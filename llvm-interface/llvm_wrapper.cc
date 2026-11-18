#include <cstdlib>
#include <memory>
#include <optional>
#include <stdio.h>
#include <string.h>

#include "llvm-c/Core.h"
#include "llvm-c/DebugInfo.h"
#include "llvm-c/Types.h"
#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/DIBuilder.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/DiagnosticInfo.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/IntrinsicsNVPTX.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/CallingConv.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/MC/TargetRegistry.h"
#include "llvm/Passes/PassBuilder.h"
#if LLVM_VERSION_MAJOR < 22
#include "llvm/Passes/PassPlugin.h"
#else
#include "llvm/Plugins/PassPlugin.h"
#endif
#include "llvm/Support/Casting.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetOptions.h"
#include "llvm/TargetParser/AArch64TargetParser.h"
#include "llvm/TargetParser/RISCVISAInfo.h"
#include "llvm/TargetParser/RISCVTargetParser.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Program.h"
#include "llvm/Transforms/IPO/AlwaysInliner.h"
#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Transforms/Instrumentation/AddressSanitizer.h"
#include "llvm/Transforms/Instrumentation/HWAddressSanitizer.h"
#include "llvm/Transforms/Instrumentation/SanitizerCoverage.h"
#include "llvm/Transforms/Scalar/LoopPassManager.h"
#include "llvm/Transforms/Scalar/LoopRotation.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/CodeExtractor.h"
#include "llvm/Frontend/Offloading/OffloadWrapper.h"
#include "llvm/Frontend/Offloading/Utility.h"
#include "llvm/Object/OffloadBinary.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Transforms/Utils/Cloning.h"

#include "clang/Basic/Diagnostic.h"
#include "clang/Basic/DiagnosticIDs.h"
#include "clang/Basic/DiagnosticOptions.h"
#include "clang/Basic/TargetInfo.h"
#include "clang/Basic/TargetOptions.h"

// Adapt to varying patches to LLVM.
#include "gnat-llvm-config.h"

using namespace llvm;
using namespace llvm::sys;

using namespace clang;

extern "C" Instruction *Get_Latest_Instruction(IRBuilder<> *bld) {
  return dyn_cast<Instruction>(&*--bld->GetInsertPoint());
}

extern "C" void Add_Debug_Flags(Module *TheModule, uint32_t version) {
  TheModule->addModuleFlag(Module::Warning, "Debug Info Version",
                           DEBUG_METADATA_VERSION);
  TheModule->addModuleFlag(Module::Warning, "Dwarf Version", version);
}

extern "C" MDBuilder *Create_MDBuilder_In_Context(LLVMContext &Ctx) {
  return new MDBuilder(Ctx);
}

extern "C" MDNode *Create_TBAA_Root(MDBuilder *MDHelper) {
  return MDHelper->createTBAARoot("Ada Root");
}

extern "C" void Add_Cold_Attribute(Function *fn) {
  fn->addFnAttr(Attribute::Cold);
}

extern "C" void Add_Asm_Element_Type(CallBase *Call, unsigned Index,
                                     Type *ElementType) {
  Call->addParamAttr(
      Index,
      Attribute::get(Call->getContext(), Attribute::ElementType, ElementType));
}

extern "C" void Set_Asm_Location(Instruction *Call, uint64_t Location) {
  auto &Ctx = Call->getContext();
  auto *Loc = ConstantAsMetadata::get(
      ConstantInt::get(Type::getInt64Ty(Ctx), Location));
  Call->setMetadata("srcloc", MDNode::get(Ctx, Loc));
}

using AsmDiagnosticCallback = void (*)(uint64_t, const char *, int);

namespace {
class AsmDiagnosticHandler : public llvm::DiagnosticHandler {
  AsmDiagnosticCallback Callback;
  std::unique_ptr<llvm::DiagnosticHandler> Previous;

public:
  AsmDiagnosticHandler(AsmDiagnosticCallback Callback,
                       std::unique_ptr<llvm::DiagnosticHandler> Previous)
      : Callback(Callback), Previous(std::move(Previous)) {}

  bool handleDiagnostics(const llvm::DiagnosticInfo &DI) override {
    if (const auto *Asm = dyn_cast<DiagnosticInfoInlineAsm>(&DI)) {
      if (Asm->getLocCookie() &&
          (DI.getSeverity() == DS_Error || DI.getSeverity() == DS_Warning)) {
        Callback(Asm->getLocCookie(), Asm->getMsgStr().str().c_str(),
                 DI.getSeverity() == DS_Warning);
        return true;
      }
    }
    return Previous && Previous->handleDiagnostics(DI);
  }
};
} // namespace

extern "C" void Install_Asm_Diagnostic_Handler(LLVMContext *Ctx,
                                               AsmDiagnosticCallback Callback) {
  Ctx->setDiagnosticHandler(std::make_unique<AsmDiagnosticHandler>(
      Callback, Ctx->getDiagnosticHandler()));
}

// ??? This function and its uses should be removed when System.Address
// change is merged.
static bool isPointerParam(Function *fn, unsigned idx) {
  return fn->getFunctionType()->getParamType(idx)->isPointerTy();
}

extern "C" void Add_Dereferenceable_Attribute(Function *fn, unsigned idx,
                                              unsigned long long Bytes) {
  if (isPointerParam(fn, idx))
    fn->addDereferenceableParamAttr(idx, Bytes);
}

extern "C" void Add_Ret_Dereferenceable_Attribute(Function *fn,
                                                  unsigned long long Bytes) {
  /* There doesn't appear to be a way to do this in LLVM 14, so skip for now.
     fn->addDereferenceableRetAttr (Bytes); */
}

extern "C" void
Add_Dereferenceable_Or_Null_Attribute(Function *fn, unsigned idx,
                                      unsigned long long Bytes) {
  if (isPointerParam(fn, idx))
    fn->addDereferenceableOrNullParamAttr(idx, Bytes);
}

extern "C" void
Add_Ret_Dereferenceable_Or_Null_Attribute(Function *fn,
                                          unsigned long long Bytes) {
  /* There doesn't appear to be a way to do this in LLVM 14, so skip for now.
     fn->addDereferenceableOrNullRetAttr (Bytes); */
}

extern "C" void Add_Inline_Always_Attribute(Function *fn) {
  fn->addFnAttr(Attribute::AlwaysInline);
}

extern "C" void Add_Inline_Hint_Attribute(Function *fn) {
  fn->addFnAttr(Attribute::InlineHint);
}

extern "C" void Add_Inline_No_Attribute(Function *fn) {
  fn->addFnAttr(Attribute::NoInline);
}

extern "C" void Add_Uwtable_Attribute(Function *fn) {
  fn->setUWTableKind(UWTableKind::Default);
}

extern "C" void Add_Fn_Readonly_Attribute(Function *fn) {
  fn->setOnlyReadsMemory();
}

extern "C" void Add_Named_Attribute(Function *fn, const char *name,
                                    const char *val, LLVMContext &Ctx) {
  fn->addFnAttr(Attribute::get(Ctx, StringRef(name, strlen(name)),
                               StringRef(val, strlen(val))));
}

extern "C" void Add_Nest_Attribute(Value *v, unsigned idx) {
  if (Function *fn = dyn_cast<Function>(v))
    fn->addParamAttr(idx, Attribute::Nest);
  else if (CallInst *ci = dyn_cast<CallInst>(v))
    ci->addParamAttr(idx, Attribute::Nest);
  else if (InvokeInst *ii = dyn_cast<InvokeInst>(v))
    ii->addParamAttr(idx, Attribute::Nest);
}

extern "C" void Add_Noalias_Attribute(Function *fn, unsigned idx) {
  if (isPointerParam(fn, idx))
    fn->addParamAttr(idx, Attribute::NoAlias);
}

extern "C" void Add_Ret_Noalias_Attribute(Function *fn) {
  fn->addRetAttr(Attribute::NoAlias);
}

extern "C" void Add_Nocapture_Attribute(LLVMContext *Context, Function *fn,
                                        unsigned idx) {
  if (!isPointerParam(fn, idx))
    return;
#if LLVM_VERSION_MAJOR < 21
  fn->addParamAttr(idx, Attribute::NoCapture);
#else
  fn->addParamAttr(
      idx, Attribute::getWithCaptureInfo(*Context, CaptureInfo::none()));
#endif
}

extern "C" void Add_Non_Null_Attribute(Function *fn, unsigned idx) {
  if (isPointerParam(fn, idx))
    fn->addParamAttr(idx, Attribute::NonNull);
}

extern "C" void Add_Ret_Non_Null_Attribute(Function *fn, unsigned idx) {
  fn->addRetAttr(Attribute::NonNull);
}

extern "C" void Add_Readonly_Attribute(Function *fn, unsigned idx) {
  if (isPointerParam(fn, idx))
    fn->addParamAttr(idx, Attribute::ReadOnly);
}

extern "C" void Add_Writeonly_Attribute(Function *fn, unsigned idx) {
  if (isPointerParam(fn, idx))
    fn->addParamAttr(idx, Attribute::WriteOnly);
}

extern "C" void Add_Opt_For_Fuzzing_Attribute(Function *fn) {
  fn->addFnAttr(Attribute::OptForFuzzing);
}

extern "C" void Add_Sanitize_Address_Attribute(Function *fn) {
  fn->addFnAttr(Attribute::SanitizeAddress);
}

extern "C" void Add_Sanitize_HW_Address_Attribute(Function *fn) {
  fn->addFnAttr(Attribute::SanitizeHWAddress);
}

extern "C" void Add_No_Implicit_Float_Attribute(Function *fn) {
  fn->addFnAttr(Attribute::NoImplicitFloat);
}

extern "C" void Add_Hardware_Shadow_Stack_Attribute(Function *fn) {
  // Clang adds the attribute only when targeting RISC-V, but there should be
  // no harm in adding it unconditionally because it's never read outside of
  // RISC-V frame lowering.
  fn->addFnAttr("hw-shadow-stack");
}

extern "C" void Add_No_Red_Zone_Attribute(Function *fn) {
  fn->addFnAttr(Attribute::NoRedZone);
}

extern "C" bool Has_Inline_Attribute(Function *fn) {
  return fn->hasFnAttribute(Attribute::InlineHint);
}

extern "C" bool Has_Inline_Always_Attribute(Function *fn) {
  return fn->hasFnAttribute(Attribute::AlwaysInline);
}

extern "C" bool Has_Nest_Attribute(Function *fn, unsigned idx) {
  return fn->hasParamAttribute(idx, Attribute::Nest);
}

extern "C" bool Call_Param_Has_Nest(CallBase *CI, unsigned idx) {
  return CI->getAttributes().hasParamAttr(idx, Attribute::Nest);
}

extern "C" MDNode *Create_TBAA_Scalar_Type_Node(LLVMContext &ctx,
                                                MDBuilder *MDHelper,
                                                const char *name, uint64_t size,
                                                MDNode *parent) {
  Type *Int64 = Type::getInt64Ty(ctx);
  auto MDname = MDHelper->createString(name);
  auto MDsize = MDHelper->createConstant(ConstantInt::get(Int64, size));
  return MDNode::get(ctx, {parent, MDsize, MDname});
}

extern "C" MDNode *
Create_TBAA_Struct_Type_Node(LLVMContext &ctx, MDBuilder *MDHelper,
                             const char *name, uint64_t size, int num_fields,
                             MDNode *parent, MDNode *fields[],
                             uint64_t offsets[], uint64_t sizes[]) {
  Type *Int64 = Type::getInt64Ty(ctx);
  SmallVector<Metadata *, 8> Ops(num_fields * 3 + 3);
  Ops[0] = parent;
  Ops[1] = MDHelper->createConstant(ConstantInt::get(Int64, size));
  Ops[2] = MDHelper->createString(name);
  for (int i = 0; i < num_fields; i++) {
    Ops[3 + i * 3] = fields[i];
    Ops[3 + i * 3 + 1] =
        MDHelper->createConstant(ConstantInt::get(Int64, offsets[i]));
    Ops[3 + i * 3 + 2] =
        MDHelper->createConstant(ConstantInt::get(Int64, sizes[i]));
  }

  return MDNode::get(ctx, Ops);
}

extern "C" MDNode *Create_TBAA_Struct_Node(LLVMContext &ctx,
                                           MDBuilder *MDHelper, int num_fields,
                                           MDNode *types[], uint64_t offsets[],
                                           uint64_t sizes[]) {
  Type *Int64 = Type::getInt64Ty(ctx);
  SmallVector<Metadata *, 8> Ops(num_fields * 3);
  for (int i = 0; i < num_fields; i++) {
    Ops[i * 3] = MDHelper->createConstant(ConstantInt::get(Int64, offsets[i]));
    Ops[i * 3 + 1] =
        MDHelper->createConstant(ConstantInt::get(Int64, sizes[i]));
    Ops[i * 3 + 2] = types[i];
  }

  return MDNode::get(ctx, Ops);
}

extern "C" MDNode *Create_TBAA_Access_Tag(MDBuilder *MDHelper, MDNode *BaseType,
                                          MDNode *AccessType, uint64_t offset,
                                          uint64_t size) {
  return MDHelper->createTBAAAccessTag(BaseType, AccessType, offset, size,
                                       false);
}

extern "C" void Set_NUW(Instruction *inst) { inst->setHasNoUnsignedWrap(); }

extern "C" void Set_NSW(Instruction *inst) { inst->setHasNoSignedWrap(); }

extern "C" bool Has_NSW(Instruction *inst) { return inst->hasNoSignedWrap(); }

extern "C" void Add_TBAA_Access(Instruction *inst, MDNode *md) {
  inst->setMetadata(LLVMContext::MD_tbaa, md);
}

extern "C" void Set_DSO_Local(GlobalObject *GV) { GV->setDSOLocal(true); }

/* Return nonnull if this value is a constant data.  */

extern "C" Value *Is_Constant_Data(Value *v) {
  return dyn_cast<ConstantData>(v);
}

/* Say whether this struct type has a name.  */

extern "C" bool Struct_Has_Name(StructType *t) { return t->hasName(); }

/*  Say whether this value has a name */

extern "C" bool Value_Has_Name(Value *v) { return v->getName().size() != 0; }

/* The LLVM C interface only provide single-index forms of extractvalue
   and insertvalue, so provide the multi-index forms here.  */

extern "C" Value *Build_Extract_Value_C(IRBuilder<> *bld, Value *aggr,
                                        unsigned *IdxList, unsigned NumIdx,
                                        char *name) {
  return bld->CreateExtractValue(aggr, {IdxList, NumIdx}, name);
}

extern "C" Value *Build_Insert_Value_C(IRBuilder<> *bld, Value *aggr,
                                       Value *elt, unsigned *IdxList,
                                       unsigned NumIdx, char *name) {
  return bld->CreateInsertValue(aggr, elt, {IdxList, NumIdx}, name);
}

/* The LLVM C interface only provides a subset of the arguments for building
   memory copy/move/set, so we provide the full interface here.  */

extern "C" Value *Build_MemCpy(IRBuilder<> *bld, Value *Dst, unsigned DstAlign,
                               Value *Src, unsigned SrcAlign, Value *Size,
                               bool isVolatile, MDNode *TBAATag,
                               MDNode *TBAAStructTag, MDNode *ScopeTag,
                               MDNode *NoAliasTag) {
#if LLVM_VERSION_MAJOR < 21
  return bld->CreateMemCpy(Dst, MaybeAlign(DstAlign), Src, MaybeAlign(SrcAlign),
                           Size, isVolatile, TBAATag, TBAAStructTag, ScopeTag,
                           NoAliasTag);
#elif LLVM_VERSION_MAJOR < 22
  return bld->CreateMemCpy(
      Dst, MaybeAlign(DstAlign), Src, MaybeAlign(SrcAlign), Size, isVolatile,
      AAMDNodes(TBAATag, TBAAStructTag, ScopeTag, NoAliasTag));
#else
  return bld->CreateMemCpy(
      Dst, MaybeAlign(DstAlign), Src, MaybeAlign(SrcAlign), Size, isVolatile,
      AAMDNodes(TBAATag, TBAAStructTag, ScopeTag, NoAliasTag, nullptr));
#endif
}

extern "C" Value *Build_MemMove(IRBuilder<> *bld, Value *Dst, unsigned DstAlign,
                                Value *Src, unsigned SrcAlign, Value *Size,
                                bool isVolatile, MDNode *TBAATag,
                                MDNode *ScopeTag, MDNode *NoAliasTag) {
#if LLVM_VERSION_MAJOR < 21
  return bld->CreateMemMove(Dst, MaybeAlign(DstAlign), Src,
                            MaybeAlign(SrcAlign), Size, isVolatile, TBAATag,
                            ScopeTag, NoAliasTag);
#elif LLVM_VERSION_MAJOR < 22
  return bld->CreateMemMove(Dst, MaybeAlign(DstAlign), Src,
                            MaybeAlign(SrcAlign), Size, isVolatile,
                            AAMDNodes(TBAATag, nullptr, ScopeTag, NoAliasTag));
#else
  return bld->CreateMemMove(
      Dst, MaybeAlign(DstAlign), Src, MaybeAlign(SrcAlign), Size, isVolatile,
      AAMDNodes(TBAATag, nullptr, ScopeTag, NoAliasTag, nullptr));
#endif
}

extern "C" Value *Build_MemSet(IRBuilder<> *bld, Value *Ptr, Value *Val,
                               Value *Size, unsigned align, bool isVolatile,
                               MDNode *TBAATag, MDNode *ScopeTag,
                               MDNode *NoAliasTag) {
#if LLVM_VERSION_MAJOR < 21
  return bld->CreateMemSet(Ptr, Val, Size, MaybeAlign(align), isVolatile,
                           TBAATag, ScopeTag, NoAliasTag);
#elif LLVM_VERSION_MAJOR < 22
  return bld->CreateMemSet(Ptr, Val, Size, MaybeAlign(align), isVolatile,
                           AAMDNodes(TBAATag, nullptr, ScopeTag, NoAliasTag));
#else
  return bld->CreateMemSet(
      Ptr, Val, Size, MaybeAlign(align), isVolatile,
      AAMDNodes(TBAATag, nullptr, ScopeTag, NoAliasTag, nullptr));
#endif
}

extern "C" CallInst *Create_Lifetime_Start(IRBuilder<> *bld, Value *Ptr,
                                           ConstantInt *Size) {
#if LLVM_VERSION_MAJOR < 22
  return bld->CreateLifetimeStart(Ptr, Size);
#else
  return bld->CreateLifetimeStart(Ptr);
#endif
}

extern "C" CallInst *Create_Lifetime_End(IRBuilder<> *bld, Value *Ptr,
                                         ConstantInt *Size) {
#if LLVM_VERSION_MAJOR < 22
  return bld->CreateLifetimeEnd(Ptr, Size);
#else
  return bld->CreateLifetimeEnd(Ptr);
#endif
}

extern "C" CallInst *Create_Invariant_Start(IRBuilder<> *bld, Value *Ptr,
                                            ConstantInt *Size) {
  return bld->CreateInvariantStart(Ptr, Size);
}

extern "C" unsigned char Does_Not_Throw(Function *fn) {
  return fn->doesNotThrow() ? 1 : 0;
}

extern "C" void Create_Fake_Use(IRBuilder<> *bld, Module *Mod, Value *Var) {
#if LLVM_VERSION_MAJOR >= 21
  llvm::Function *FakeUseDecl =
      llvm::Intrinsic::getOrInsertDeclaration(Mod, llvm::Intrinsic::fake_use);
  bld->CreateCall(FakeUseDecl, {Var});
#endif
}

extern "C" void Set_Does_Not_Throw(Function *fn) {
  return fn->setDoesNotThrow();
}

extern "C" unsigned char Does_Not_Return(Function *fn) {
  return fn->doesNotReturn() ? 1 : 0;
}

extern "C" void Set_Does_Not_Return(Function *fn) {
  return fn->setDoesNotReturn();
}

/* The LLVM C procedure Set_Volatile only works for loads and stores, not
   Atomic instructions.  */

extern "C" void Set_Volatile_For_Atomic(Instruction *inst) {
  if (AtomicRMWInst *ARW = dyn_cast<AtomicRMWInst>(inst))
    ARW->setVolatile(true);
  else
    cast<AtomicCmpXchgInst>(inst)->setVolatile(true);
}

extern "C" void Set_Weak_For_Atomic_Xchg(AtomicCmpXchgInst *inst) {
  inst->setWeak(true);
}

extern "C" void Add_Function_To_Module(Function *f, Module *m,
                                       bool allowDeduplication) {
  // Check if the function already exists in the module. We only add imported
  // functions to the module after we've processed the entire GNAT tree, and we
  // deduplicate based on GNAT node IDs. However, builtin functions such as
  // __gnat_last_chance_handler are processed separately (because there is no
  // associated node in the GNAT tree) and added eagerly to the module.
  //
  // If a module uses a builtin function implicitly and also calls it
  // explicitly, we don't want two LLVM values representing the same function.
  // In this case, we replace all uses of one with the other (unless they're
  // identical), which is safe because the LLVM value is just a declaration for
  // a function to be imported.

  auto existingFunction = m->getFunction(f->getName());
  if (existingFunction == f)
    return;

  if (existingFunction && !allowDeduplication) {
    assert(f->isDeclaration() && existingFunction->isDeclaration() &&
           f->getFunctionType() == existingFunction->getFunctionType());
    f->replaceAllUsesWith(existingFunction);
    delete f;
  } else {
    m->getFunctionList().push_back(f);
  }
}

extern "C" void Dump_Metadata(MDNode *MD) { MD->print(errs()); }

extern "C" unsigned Get_Metadata_Num_Operands(MDNode *MD) {
  return MD->getNumOperands();
}

extern "C" uint64_t Get_Metadata_Operand_Constant_Value(MDNode *MD,
                                                        unsigned i) {
  return mdconst::extract<ConstantInt>(MD->getOperand(i))->getZExtValue();
}

extern "C" MDNode *Get_Metadata_Operand(MDNode *MD, unsigned i) {
  return dyn_cast<MDNode>(MD->getOperand(i));
}

extern "C" void Initialize_LLVM(void) {
  // Initialize the target registry etc.  These functions appear to be
  // in LLVM.Target, but they reference static inline function, so they
  // can only be used from C, not Ada.

  InitializeAllTargetInfos();
  InitializeAllTargets();
  InitializeAllTargetMCs();
  InitializeAllAsmParsers();
  InitializeAllAsmPrinters();
}

// Container for Clang's target information and any data that it references.
struct ClangTargetInfo {
  // The TargetInfo gets only a reference to the options (a pointer before LLVM
  // 21), so we need to hold on to them.
  //
  // ??? When we drop support for LLVM versions before 21, we can turn this
  // field into a value instead of a pointer because recent versions of
  // TargetInfo take it by reference, not as std::shared_ptr.
  std::shared_ptr<clang::TargetOptions> Options;

  // The DiagnosticOptions are passed to the DiagnosticsEngine (below) by
  // reference, so we need to retain them.
#if LLVM_VERSION_MAJOR < 21
  IntrusiveRefCntPtr<DiagnosticOptions> DiagOpts;
#else
  DiagnosticOptions DiagOpts;
#endif

  // The DiagnosticsEngine class doesn't have a default initializer and can't
  // be moved, so we store it inside std::optional.
  std::optional<DiagnosticsEngine> Diags;

  TargetInfo *Info;
};

// The kinds of asm constraints that we're interested in. Note the matching Ada
// definition in gnatllvm-wrapper.ads.
enum Asm_Constraint_Kind {
  Invalid_Constraint = -1,
  Value_Constraint = 0,
  Memory_Constraint = 1,
  Read_Write_Constraint = 2
};

extern "C" Asm_Constraint_Kind
Classify_Asm_Constraint(ClangTargetInfo *CTI, const char *Constraint,
                        const char *OutputConstraint, bool IsOutput) {
  TargetInfo::ConstraintInfo Info(Constraint, "");
  if (IsOutput) {
    if (!CTI->Info->validateOutputConstraint(Info))
      return Invalid_Constraint;
    if (Info.isReadWrite())
      return Read_Write_Constraint;
  } else {
    SmallVector<TargetInfo::ConstraintInfo, 1> Outputs;
    if (*OutputConstraint) {
      Outputs.emplace_back(OutputConstraint, "");
      if (!CTI->Info->validateOutputConstraint(Outputs.back()))
        return Invalid_Constraint;
    }
    if (!CTI->Info->validateInputConstraint(Outputs, Info))
      return Invalid_Constraint;
  }

  return Info.allowsMemory() && !Info.allowsRegister() ? Memory_Constraint
                                                       : Value_Constraint;
}

extern "C" ClangTargetInfo *Get_Target_Info(const char *TargetTriple,
                                            const char *CPU, const char *ABI,
                                            const char *Features) {
  auto Result = std::make_unique<ClangTargetInfo>();

  Result->Options = std::make_shared<clang::TargetOptions>();
  Result->Options->Triple = TargetTriple;
  Result->Options->CPU = CPU;
  Result->Options->ABI = ABI;

  std::string FeatureString = Features;
  if (!FeatureString.empty()) {
    SmallVector<StringRef, 16> FeatureVector;
    SplitString(FeatureString, FeatureVector, ",");
    for (const auto F : FeatureVector)
      Result->Options->FeaturesAsWritten.push_back(F.str());
  }

  // The Clang API requires us to provide a handler for diagnostic messages
  // emitted during the operation. It owns the handler, and the DiagnosticIDs
  // are reference-counted, so there's no need to keep either of them alive
  // explicitly.
  //
  // ??? Use a real diagnostics consumer if we ever get an error from Clang.
  IntrusiveRefCntPtr<DiagnosticIDs> DiagID(new DiagnosticIDs());
#if LLVM_VERSION_MAJOR < 21
  Result->DiagOpts = new DiagnosticOptions();
  Result->Diags.emplace(DiagID, &*Result->DiagOpts, new IgnoringDiagConsumer());
#else
  Result->Diags.emplace(DiagID, Result->DiagOpts, new IgnoringDiagConsumer());
#endif

  // Finally, we can create the TargetInfo structure.
#if LLVM_VERSION_MAJOR < 21
  Result->Info = TargetInfo::CreateTargetInfo(*Result->Diags, Result->Options);
#else
  Result->Info = TargetInfo::CreateTargetInfo(*Result->Diags, *Result->Options);
#endif

  if (Result->Info == nullptr)
    return nullptr;

  // Leak our heap-allocated result structure to the Ada caller, which is going
  // to own it from this point on.
  return Result.release();
}

// Description of C type properties to pass to Ada. Unless otherwise noted,
// sizes are in bits.
struct Target_C_Type_Info {
  unsigned PointerSize;
  unsigned CharSize;
  unsigned WCharTSize;
  unsigned ShortSize;
  unsigned IntSize;
  unsigned LongSize;
  unsigned LongLongSize;
  unsigned LongLongAlignment;
  unsigned LongLongLongSize;
  unsigned LongLongLongAlignment;
  unsigned DoubleSize;
  unsigned DoubleAlignment;
  unsigned LongDoubleSemanticSize; // 0 if the target doesn't have long double
  unsigned LongDoubleStorageSize;  // 0 if the target doesn't have long double
  unsigned LongDoubleAlignment;    // 0 if the target doesn't have long double
  unsigned MaximumAlignmentBytes;
  unsigned RegisterSize;
  unsigned SystemAllocatorAlignment;
  unsigned StrictAlignment;
};

extern "C" void Get_Target_C_Types(ClangTargetInfo *CTI,
                                   Target_C_Type_Info *Result, int Emit_C,
                                   unsigned char *success) {
  *Result = {};
  *success = 0;

  auto Info = CTI->Info;

  Result->PointerSize = Info->getPointerWidth(LangAS::Default);
  Result->CharSize = Info->getCharWidth();
  Result->WCharTSize = Info->getWCharWidth();
  Result->ShortSize = Info->getShortWidth();
  Result->IntSize = Info->getIntWidth();
  Result->LongSize = Info->getLongWidth();
  Result->LongLongSize = Info->getLongLongWidth();
  Result->LongLongAlignment = Info->getLongLongAlign();
  if (Info->hasInt128Type() && !Emit_C) {
    Result->LongLongLongSize = 128;
    Result->LongLongLongAlignment = Info->getInt128Align();
  } else {
    Result->LongLongLongSize = Result->LongLongSize;
    Result->LongLongLongAlignment = Result->LongLongAlignment;
  }
  Result->DoubleSize = Info->getDoubleWidth();
  Result->DoubleAlignment = Info->getDoubleAlign();
  if (Info->hasLongDoubleType()) {
    Result->LongDoubleSemanticSize =
        APFloat::semanticsSizeInBits(Info->getLongDoubleFormat());
    Result->LongDoubleStorageSize = Info->getLongDoubleWidth();
    Result->LongDoubleAlignment = Info->getLongDoubleAlign();
  }
  Result->MaximumAlignmentBytes = Info->getSuitableAlign() / 8;
  Result->RegisterSize = Info->getRegisterWidth();
  Result->SystemAllocatorAlignment = Info->getNewAlign() / 8;
  Result->StrictAlignment = !Info->hasUnalignedAccess();

  *success = 1;
}

/* This is a dummy optimization "pass" that serves just to obtain loop
   information when generating C.

   For now, we don't actually do anything except collect information to look
   at in the debugger.  */

namespace llvm {
class Loop;

struct OurLoopPass : PassInfoMixin<OurLoopPass> {
public:
  PreservedAnalyses run(Loop &L, LoopAnalysisManager &AM,
                        LoopStandardAnalysisResults &AR, LPMUpdater &U);
  static bool isRequired() { return true; }
};
} // namespace llvm

PreservedAnalyses OurLoopPass::run(Loop &L, LoopAnalysisManager &LAM,
                                   LoopStandardAnalysisResults &AR,
                                   LPMUpdater &U) {

  auto pre = L.getLoopPreheader();
  auto header = L.getHeader();
  auto latch = L.getLoopLatch();
  auto cmp = L.getLatchCmpInst();
  auto issimple = L.isLoopSimplifyForm();
  return PreservedAnalyses::all();
}

extern "C" LLVMBool
LLVM_Optimize_Module(Module *M, TargetMachine *TM, int CodeOptLevel,
                     int SizeOptLevel, bool NeedLoopInfo, bool UnrollLoops,
                     bool LoopVectorization, bool SLPVectorization,
                     bool MergeFunctions, bool PrepareForThinLTO,
                     bool PrepareForLTO, bool RerollLoops, bool EnableFuzzer,
                     bool EnableAddressSanitizer, bool EnableHWAddressSanitizer,
                     const char *SanCovAllowList, const char *SanCovIgnoreList,
                     const char **PassPluginNames, char **ErrorMessage) {
  // This code is derived from EmitAssemblyWithNewPassManager in clang

  std::optional<PGOOptions> PGOOpt;
  PipelineTuningOptions PTO;
  PassInstrumentationCallbacks PIC;
  Triple TargetTriple(M->getTargetTriple());
  OptimizationLevel Level = (CodeOptLevel == 1   ? OptimizationLevel::O1
                             : CodeOptLevel == 2 ? OptimizationLevel::O2
                             : CodeOptLevel == 3 ? OptimizationLevel::O3
                                                 : OptimizationLevel::O0);
  PTO.LoopUnrolling = UnrollLoops;
  PTO.LoopInterleaving = UnrollLoops;
  PTO.LoopVectorization = LoopVectorization;
  PTO.SLPVectorization = SLPVectorization;
  PTO.MergeFunctions = MergeFunctions;

  LoopAnalysisManager LAM;
  FunctionAnalysisManager FAM;
  CGSCCAnalysisManager CGAM;
  ModuleAnalysisManager MAM;

  PassBuilder PB(TM, PTO, PGOOpt, &PIC);

  if (PassPluginNames != nullptr) {
    while (*PassPluginNames != nullptr) {
      auto Plugin = PassPlugin::Load(*PassPluginNames);

      if (auto Err = Plugin.takeError()) {
        handleAllErrors(std::move(Err), [&](const StringError &Err) {
          if (ErrorMessage != nullptr)
            *ErrorMessage = strdup(Err.getMessage().c_str());
        });

        return 1;
      }

      Plugin->registerPassBuilderCallbacks(PB);
      PassPluginNames++;
    }
  }

  FAM.registerPass([&] { return PB.buildDefaultAAPipeline(); });

  // Register the target library analysis directly and give it a customized
  // preset TLI.
  TargetLibraryInfoImpl *TLII = new TargetLibraryInfoImpl(TargetTriple);
  FAM.registerPass([&] { return TargetLibraryAnalysis(*TLII); });

  // Register all the basic analyses with the managers.

  PB.registerModuleAnalyses(MAM);
  PB.registerCGSCCAnalyses(CGAM);
  PB.registerFunctionAnalyses(FAM);
  PB.registerLoopAnalyses(LAM);
  PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

  // Register additional passes for the sanitizers if applicable. This code is
  // inspired by addSanitizers in LLVM's clang/lib/CodeGen/BackendUtil.cpp.
  PB.registerOptimizerLastEPCallback(
#if LLVM_VERSION_MAJOR < 21
      [&](ModulePassManager &MPM, OptimizationLevel Level) {
#else
      [&](ModulePassManager &MPM, OptimizationLevel Level, ThinOrFullLTOPhase) {
#endif
        if (EnableFuzzer) {
          // Configure sanitizer coverage according to what Clang does in
          // clang/lib/Driver/SanitizerArgs.cpp when the fuzzer is enabled.
          SanitizerCoverageOptions CoverageOpts;
          CoverageOpts.CoverageType = SanitizerCoverageOptions::SCK_Edge;
          CoverageOpts.Inline8bitCounters = true;
          CoverageOpts.IndirectCalls = true;
          CoverageOpts.TraceCmp = true;
          CoverageOpts.PCTable = true;
          if (TargetTriple.isOSLinux())
            CoverageOpts.StackDepth = true;

          std::vector<std::string> AllowListFiles;
          if (SanCovAllowList != nullptr)
            AllowListFiles.push_back(SanCovAllowList);

          std::vector<std::string> IgnoreListFiles;
          if (SanCovIgnoreList != nullptr)
            IgnoreListFiles.push_back(SanCovIgnoreList);

#if LLVM_VERSION_MAJOR < 22
          MPM.addPass(SanitizerCoveragePass(CoverageOpts, AllowListFiles,
                                            IgnoreListFiles));
#else
          MPM.addPass(SanitizerCoveragePass(CoverageOpts, nullptr,
                                            AllowListFiles, IgnoreListFiles));
#endif
        }

        if (EnableAddressSanitizer)
          MPM.addPass(AddressSanitizerPass(AddressSanitizerOptions()));

        if (EnableHWAddressSanitizer)
          MPM.addPass(HWAddressSanitizerPass(HWAddressSanitizerOptions()));
      });

  ModulePassManager MPM;
  if (CodeOptLevel == 0) {
#if LLVM_VERSION_MAJOR < 21
    bool LTOPhase = PrepareForLTO || PrepareForThinLTO;
#else
    ThinOrFullLTOPhase LTOPhase = ThinOrFullLTOPhase::None;
    if (PrepareForLTO) {
      LTOPhase = ThinOrFullLTOPhase::FullLTOPreLink;
    } else if (PrepareForThinLTO) {
      LTOPhase = ThinOrFullLTOPhase::ThinLTOPreLink;
    }
#endif
    MPM = PB.buildO0DefaultPipeline(Level, LTOPhase);
    if (NeedLoopInfo)
      MPM.addPass(createModuleToFunctionPassAdaptor(
          createFunctionToLoopPassAdaptor(LoopRotatePass())));
  } else if (PrepareForThinLTO)
    MPM = PB.buildThinLTOPreLinkDefaultPipeline(Level);
  else if (PrepareForLTO)
    MPM = PB.buildLTOPreLinkDefaultPipeline(Level);
  else
    MPM = PB.buildPerModuleDefaultPipeline(Level);

  if (NeedLoopInfo)
    MPM.addPass(createModuleToFunctionPassAdaptor(
        createFunctionToLoopPassAdaptor(OurLoopPass())));
  MPM.run(*M, MAM);
  return 0;
}

extern "C" Value *Get_Float_From_Words_And_Exp(LLVMContext *Context, Type *T,
                                               int Exp, unsigned NumWords,
                                               const uint64_t Words[]) {
  auto LongInt = APInt(NumWords * 64, {Words, NumWords});
  auto Initial = APFloat(T->getFltSemantics(),
                         APInt::getZero(T->getPrimitiveSizeInBits()));
  Initial.convertFromAPInt(LongInt, false, APFloat::rmTowardZero);
  auto Result = scalbn(Initial, Exp, APFloat::rmTowardZero);
  return ConstantFP::get(*Context, Result);
}

extern "C" bool Const_Int_Fits_In_LLI(Value *V) {
  // Mirror the condition under which APInt::getSExtValue is defined
  return cast<ConstantInt>(V)->getValue().getSignificantBits() <= 64;
}

extern "C" bool Const_Int_Fits_In_ULL(Value *V) {
  // Mirror the condition under which APInt::getZExtValue is defined
  return cast<ConstantInt>(V)->getValue().getActiveBits() <= 64;
}

extern "C" void Get_Const_Int_Words(Value *V, uint64_t Words[]) {
  const APInt &Val = cast<ConstantInt>(V)->getValue();
  memcpy(Words, Val.getRawData(), Val.getNumWords() * sizeof(uint64_t));
}

extern "C" Value *Pred_FP(LLVMContext *Context, Type *T, Value *Val) {
  // We want to compute the predecessor of Val, but the "next" function
  // can return unnormalized, so we have to multiply by one (adding zero
  // doesn't do it).
  auto apf = dyn_cast<ConstantFP>(Val)->getValueAPF();
  auto one = APFloat(T->getFltSemantics(), 1);
  apf.next(true);
  apf.multiply(one, APFloat::rmTowardZero);
  return ConstantFP::get(*Context, apf);
}

extern "C" int Convert_FP_To_String(Value *V, char *Buf) {
  const APFloat &APF = dyn_cast<ConstantFP>(V)->getValueAPF();

  if (&APF.getSemantics() == &APFloat::IEEEsingle() ||
      &APF.getSemantics() == &APFloat::IEEEdouble()) {
    if (!APF.isInfinity() && !APF.isNaN()) {
      SmallString<128> StrVal;
      APF.toString(StrVal, 0, 0, false);

      if (&APF.getSemantics() == &APFloat::IEEEsingle())
        StrVal += "f";

      strcpy(Buf, StrVal.c_str());
      return strlen(Buf);
    }

    // Output special values in hexadecimal format
    std::string S = ("0x" +
                     utohexstr(APF.bitcastToAPInt().getZExtValue(),
                               /*Lower=*/true) +
                     "p0");

    std::strcpy(Buf, S.c_str());
    return S.length();
  }

  return strlen(strcpy(Buf, "<unsupported floating point type>"));
}

extern "C" Value *Get_Infinity(Type *T) {
  return ConstantFP::getInfinity(T, false);
}

extern "C" bool Equals_Int(ConstantInt *v, uint64_t val) {
  return v->equalsInt(val);
}

/* Return whether V1 and V2 have the same constant values, interpreted as
   signed integers. If the sizes differ, we have to convert to the
   widest size.  */

extern "C" bool Equal_Constants(ConstantInt *v1, ConstantInt *v2) {
  APInt i1 = v1->getValue(), i2 = v2->getValue();

  if (i1.getBitWidth() > i2.getBitWidth())
    i2 = i2.sext(i1.getBitWidth());
  else if (i2.getBitWidth() > i1.getBitWidth())
    i1 = i1.sext(i2.getBitWidth());
  return i1 == i2;
}

extern "C" bool Get_GEP_Constant_Offset(Value *GEP, DataLayout &dl,
                                        uint64_t *result) {
  auto Offset =
      APInt(dl.getIndexSizeInBits(GEP->getType()->getPointerAddressSpace()), 0);
  auto GEPO = dyn_cast<GEPOperator>(GEP);

  if (!GEPO || !GEPO->accumulateConstantOffset(dl, Offset) ||
      !Offset.isIntN(64))
    return false;

  *result = Offset.getZExtValue();
  return true;
}

extern "C" int64_t Get_Element_Offset(DataLayout &DL, StructType *ST,
                                      unsigned idx) {
  const StructLayout *SL = DL.getStructLayout(ST);
  return SL->getElementOffset(idx);
}

extern "C" unsigned Get_Num_CDA_Elements(ConstantDataArray *CA) {
  return CA->getNumElements();
}

extern "C" bool Is_C_String(ConstantDataSequential *CDS) {
  return CDS->isCString();
}

/* There are two LLVM "opcodes": the real LLVM opcode, which is used
   throughout the LLVM C++ interface, and a "stable" version of the
   opcodes, that's used in the C interface.  We need to map between them,
   but the only function to do so in LLVM is static (in Core.cpp), so we
   duplicate that small function here.  */

static int map_from_llvmopcode(LLVMOpcode code) {
  switch (code) {
#define HANDLE_INST(num, opc, clas)                                            \
  case LLVM##opc:                                                              \
    return num;
#include "llvm/IR/Instruction.def"
#undef HANDLE_INST
  }

  llvm_unreachable("Unhandled Opcode.");
}

extern "C" const char *Get_Opcode_Name(LLVMOpcode opc) {
  return Instruction::getOpcodeName(map_from_llvmopcode(opc));
}

extern "C" Type *Get_Load_Store_Type(Value *I) { return getLoadStoreType(I); }

extern "C" Type *Get_Source_Element_Type(Value *I) {
  auto *GEPO = cast<GEPOperator>(I);
  return GEPO->getSourceElementType();
}

extern "C" Type *Get_Function_Type(Function *F) { return F->getFunctionType(); }

extern "C" BasicBlock *Get_Unique_Predecessor(BasicBlock *bb) {
  return bb->getUniquePredecessor();
}

extern "C" void Invert_Predicate(CmpInst *c) {
  c->setPredicate(c->getInversePredicate());
}

extern "C" void Swap_Successors(BranchInst *c) { c->swapSuccessors(); }

extern "C" void Replace_Inst_With_Inst(Instruction *from, Instruction *to) {
  ReplaceInstWithInst(from, to);
}

extern "C" BinaryOperator *Create_And(Value *Op1, Value *Op2) {
  return BinaryOperator::CreateAnd(Op1, Op2);
}

extern "C" BinaryOperator *Create_Or(Value *Op1, Value *Op2) {
  return BinaryOperator::CreateOr(Op1, Op2);
}

extern "C" CallInst *Create_Call_2(Function *Fn, Value *op1, Value *op2) {
  return CallInst::Create(Fn, {op1, op2});
}

extern "C" ReturnInst *Create_Return(LLVMContext &C, Value *retVal) {
  return ReturnInst::Create(C, retVal);
}

extern "C" BranchInst *Create_Br(BasicBlock *dest) {
  return BranchInst::Create(dest);
}

extern "C" void Insert_At_Block_End(Instruction *I, BasicBlock *BB,
                                    Instruction *From) {
  I->insertInto(BB, BB->end());
  I->setDebugLoc(From->getDebugLoc());
}

extern "C" AllocaInst *Insert_Alloca_Before(Type *Ty, Instruction *Before) {
  auto Inst = new AllocaInst(Ty, 0, "", Before->getIterator());
  Inst->setDebugLoc(Before->getDebugLoc());
  return Inst;
}

extern "C" LoadInst *Insert_Load_Before(Type *Ty, Value *Ptr,
                                        Instruction *Before) {
  auto Inst = new LoadInst(Ty, Ptr, "", Before->getIterator());
  Inst->setDebugLoc(Before->getDebugLoc());
  return Inst;
}

extern "C" void Insert_Store_Before(Value *Val, Value *Ptr,
                                    Instruction *Before) {
  auto Inst = new StoreInst(Val, Ptr, Before->getIterator());
  Inst->setDebugLoc(Before->getDebugLoc());
}

extern "C" bool All_Preds_Are_Unc_Branches(BasicBlock *BB) {
  for (auto *PBB : predecessors(BB))
    if (PBB->getTerminator()->getNumSuccessors() != 1)
      return false;

  return true;
}

extern "C" bool Is_Dead_Basic_Block(BasicBlock *BB) {
  return BB->hasNPredecessors(0);
}

extern "C" Value *Get_First_Non_Phi_Or_Dbg(BasicBlock *BB) {
#if LLVM_VERSION_MAJOR < 21
  return BB->getFirstNonPHIOrDbg();
#else
  return &*BB->getFirstNonPHIOrDbg();
#endif
}

extern "C" bool Is_Lifetime_Intrinsic(Instruction *v) {
  return v->isLifetimeStartOrEnd();
}

extern "C" void Delete_Trailing_Dbg_Records(BasicBlock *b) {
  b->deleteTrailingDbgRecords();
}

/* If we call into CCG from GNAT LLVM during the compilation process to
   record some information about a Value (for example, its signedness),
   there's a chance that that value will be deleted during the optimization
   process and that same address used for some other value. So we need to
   set a callback on that value to notify us that this happened so we can
   delete the value from our table. The below class and function is used
   for that purpose.  */

class GNATCallbackVH final : public CallbackVH {
  void (*fn)(Value *);
  void deleted() override;

public:
  GNATCallbackVH(Value *V, void (*Fn)(Value *));
};

void GNATCallbackVH::deleted() {
  (this->fn)(getValPtr());

  // This callback object is no longer needed, and we don't keep references to
  // it anywhere, so self-delete.
  delete this;
}

GNATCallbackVH::GNATCallbackVH(Value *V, void (*Fn)(Value *))
    : CallbackVH(V), fn(Fn) {}

extern "C" void Notify_On_Value_Delete(Value *V, void (*Fn)(Value *)) {
  GNATCallbackVH *CB = new GNATCallbackVH(V, Fn);
}

extern "C" void Set_Module_PIC_PIE(Module *M, int PIC, int PIE) {
  M->setPICLevel(static_cast<PICLevel::Level>(PIC));
  M->setPIELevel(static_cast<PIELevel::Level>(PIE));
}

extern "C" void Set_Unwind_Tables(Module *M) {
  M->setUwtable(UWTableKind::Default);
}

extern "C" void Enable_Frame_Pointers(Module *M) {
  M->setFramePointer(FramePointerKind::All);
}

extern "C" bool Enable_Branch_Protection(Module *M, ClangTargetInfo *CTI) {
  if (!CTI->Info->checkCFProtectionBranchSupported(*CTI->Diags))
    return false;

  M->addModuleFlag(Module::Warning, "cf-protection-branch", 1);
  return true;
}

extern "C" bool Enable_Return_Protection(Module *M, ClangTargetInfo *CTI) {
  if (!CTI->Info->checkCFProtectionReturnSupported(*CTI->Diags))
    return false;

  M->addModuleFlag(Module::Warning, "cf-protection-return", 1);
  return true;
}

extern "C" bool Has_Default_PIE(const char *Target) {
  Triple TargetTriple(Target);

  // Like Clang, we default to PIE on Linux and x86_64 Windows (out of the
  // supported targets). See the comment at the call site in GNATLLVM.Codegen
  // for details.
  return TargetTriple.isOSLinux() || (TargetTriple.isOSWindows() &&
                                      TargetTriple.getArch() == Triple::x86_64);
}

extern "C" bool Has_SEH(const char *Target) {
  Triple TargetTriple(Target);

  return TargetTriple.isOSWindows() &&
         (TargetTriple.getArch() == Triple::x86_64 ||
          TargetTriple.getArch() == Triple::aarch64);
}

extern "C" bool Has_Call_Graph_Section(const char *Target) {
  // LLVM can only emit a .llvm.callgraph section into an ELF object:
  // MCObjectFileInfo leaves CallGraphSection null for every other object
  // format and AsmPrinter::emitCallGraphSection dereferences it.
  return Triple(Target).isOSBinFormatELF();
}

extern "C" bool Has_HW_Address_Sanitizer(const char *Target) {
  Triple TargetTriple(Target);

  return (TargetTriple.getArch() == Triple::x86_64 ||
          TargetTriple.getArch() == Triple::aarch64 ||
          TargetTriple.getArch() == Triple::riscv64) &&
         (TargetTriple.isOSLinux() || TargetTriple.isOSUnknown());
}

extern "C" bool Needs_Frame_Pointers(const char *Target) {
  Triple TargetTriple(Target);

  // Like GCC, we enable frame pointers for x86 because backtrace computations
  // rely on them, except on Linux where they use DWARF.
  return !TargetTriple.isOSLinux() && (TargetTriple.getArch() == Triple::x86);
}

extern "C" bool Is_x86(const char *Target) {
  Triple TargetTriple(Target);
  return TargetTriple.getArch() == Triple::x86;
}

extern "C" bool Is_x86_Family(const char *Target) {
  return Triple(Target).isX86();
}

extern "C" bool Is_Windows(const char *Target) {
  Triple TargetTriple(Target);
  return TargetTriple.isOSWindows();
}

extern "C" const char *Get_Personality_Function_Name(const char *Target) {
  // For now, we don't support SJLJ exceptions, so we just need to decide
  // whether the target uses SEH.
  if (Has_SEH(Target))
    return "__gnat_personality_seh0";
  else
    return "__gnat_personality_v0";
}

// Add the features to the extension set.
static void ProcessAArch64Features(StringRef Features,
                                   AArch64::ExtensionSet &Extensions) {
  if (Features.empty())
    return;

  SmallVector<StringRef, 8> FeatureSplit;
  Features.split(FeatureSplit, "+", /*MaxSplit=*/-1,
                 /*KeepEmpty=*/false);

  for (auto const Feature : FeatureSplit) {
    if (Feature == "neon" || Feature == "noneon") {
      errs() << "warning: [no]neon is not accepted as modifier, please use "
                "[no]simd instead\n";
      continue;
    }

    if (!Extensions.parseModifier(Feature))
      errs() << "warning: ignoring unsupported feature " << Feature << "\n";
  }
}

static StringRef getRISCVArch(const Triple &T, StringRef Arch, StringRef CPU,
                              StringRef ABI) {
  // Inspired by riscv::getRISCVArch in
  // clang/lib/Driver/ToolChains/Arch/RISCV.cpp.

  // Use the explicitly specified arch, if any.
  if (!Arch.empty())
    return Arch;

  // If no target architecture has been specified, derive it from the CPU.
  if (StringRef ArchFromCPU = RISCV::getMArchFromMcpu(CPU);
      !ArchFromCPU.empty())
    return ArchFromCPU;

  // Next, try to get the arch from the ABI.
  if (ABI.equals_insensitive("ilp32e"))
    return "rv32e";
  if (ABI.equals_insensitive("lp64e"))
    return "rv64e";
  if (ABI.starts_with_insensitive("ilp32"))
    return "rv32imafdc";
  if (ABI.starts_with_insensitive("lp64"))
    return "rv64imafdc";

  // If we still don't have an architecture, choose a default based on the
  // triple.
  return (T.getOS() == Triple::UnknownOS) ? "rv64imac" : "rv64imafdc";
}

extern "C" char *Get_Features(const char *TargetTriple, const char *Arch,
                              const char *CPU, const char *ABI,
                              int EnableExperimentalExtensions) {
  // This is a simplified version of Clang's tools::getTargetFeatures (see
  // clang/lib/Driver/ToolChains/CommonArgs.cpp), adapted to the arguments that
  // we have available and the defaults that we set during option parsing.

  Triple T(TargetTriple);

  // ??? We may want to add code for more target architectures here; Clang
  // often puts it in clang/lib/Driver/ToolChains/Arch/.

  switch (T.getArch()) {
  default:
    return nullptr;

  case Triple::aarch64: {
    // Here we replicate relevant parts of Clang's
    // aarch64::getAArch64TargetFeatures (see
    // clang/lib/Driver/ToolChains/Arch/AArch64.cpp).

    StringRef TargetCPU = CPU;

    AArch64::ExtensionSet Extensions;
    std::vector<StringRef> Features;
    StringRef ArchFeatures, CPUFeatures;

    auto ArchLowerCase = StringRef(Arch).lower();
    if (ArchLowerCase.empty() && TargetCPU == "generic") {
      // Clang defaults to ARMv8-A if the user hasn't specified a CPU either,
      // so let's do the same.
      ArchLowerCase = "armv8-a";
    }

    if (ArchLowerCase.size()) {
      // The -march option value has the format
      // "architecture+feature1+feature2", so first split the architecture from
      // the list of features.
      auto const ArchSplit = StringRef(ArchLowerCase).split("+");
      auto const ArchInfo = AArch64::parseArch(ArchSplit.first);

      if (ArchInfo == nullptr) {
        errs() << "warning: ignoring unsupported -march value " << Arch << "\n";
        return nullptr;
      }

      Extensions.addArchDefaults(*ArchInfo);
      ProcessAArch64Features(ArchSplit.second, Extensions);
    }

    // The -mcpu option value has the format "cpu+feature1+feature2", so
    // first split the CPU from the list of features.
    auto const CPUSplit = TargetCPU.split("+");

    // Only derive features from the CPU if we don't have an arch (default or
    // user-specified).
    if (ArchLowerCase.empty()) {
      auto const CPUInfo = AArch64::parseCpu(CPUSplit.first);

      if (!CPUInfo) {
        errs() << "warning: ignoring unsupported -mcpu value " << TargetCPU
               << "\n";
        return nullptr;
      }

      Extensions.addCPUDefaults(*CPUInfo);
    }

    // Always process features appended to the CPU, if any.
    ProcessAArch64Features(CPUSplit.second, Extensions);

    // ??? In Clang, -mgeneral-regs-only disables all floating-point features
    // via Extensions.disable(AArch64::AEK_FP).

    Extensions.toLLVMFeatureList(Features);

    // ??? There is a lot more in Clang's AArch64 feature lookup code that we
    // may want to copy.

    return strdup(join(Features, ",").c_str());
  }

  case Triple::riscv64: {
    // This part is based on Clang's riscv::getRISCVTargetFeatures (see
    // clang/lib/Driver/ToolChains/Arch/RISCV.cpp).

    StringRef TargetArch = getRISCVArch(T, Arch, CPU, ABI);
    std::vector<StringRef> Features;

    auto ISAInfo =
        RISCVISAInfo::parseArchString(TargetArch, EnableExperimentalExtensions);
    if (!ISAInfo) {
      handleAllErrors(ISAInfo.takeError(), [&](StringError &ErrMsg) {
        errs() << "warning: unsupported -march value " << Arch << "\n";
      });

      return nullptr;
    }

    std::vector<std::string> ISAFeatures = (*ISAInfo)->toFeatures(true, false);
    for (const std::string &Feature : ISAFeatures)
      Features.push_back(Feature);

    if (EnableExperimentalExtensions)
      Features.push_back("+experimental");

    if (RISCV::hasFastScalarUnalignedAccess(CPU))
      Features.push_back("+unaligned-scalar-mem");
    if (RISCV::hasFastVectorUnalignedAccess(CPU))
      Features.push_back("+unaligned-vector-mem");

    // Clang sets -mrelax by default, so we do the same.
    Features.push_back("+relax");

    return strdup(join(Features, ",").c_str());
  }
  }
}

extern "C" const char *Get_Target_Default_CPU(const char *TargetTriple) {
  // Select a default CPU for a given target triple.
  //
  // If not selected explicitly, set the same default CPU as Clang does.
  // Consistency with Clang is generally useful, and on x86 in particular,
  // the choice of CPU results in selection of features.
  // In this case the use of SSE rather than x87 for floating point
  // operations improves rounding behavior.

  Triple T(TargetTriple);

  switch (T.getArch()) {
  default:
    return "generic";
  case Triple::riscv32:
    return "generic-rv32";
  case Triple::riscv64:
    return "generic-rv64";
  case Triple::x86_64:
    return "x86-64";
  case Triple::x86:
    return "pentium4";
  }
}

extern "C" const char *Get_Normalized_CPU_Name(const char *TargetTriple,
                                               const char *CPU) {
  // This function is modeled after tools::getCPUName in
  // clang/lib/Driver/ToolChains/CommonArgs.cpp.

  Triple T(TargetTriple);

  switch (T.getArch()) {
  default:
    return nullptr;
  case Triple::aarch64: {
    // Strip features appended to the CPU name, then resolve aliases.
    return strdup(
        AArch64::resolveCPUAlias(StringRef(CPU).split("+").first.lower())
            .str()
            .c_str());
  }
  }
}

extern "C" const char *Get_Target_Default_ABI(const char *TargetTriple,
                                              const char *Arch,
                                              const char *CPU) {
  Triple T(TargetTriple);

  // Collect the result in a std::string and strdup it at the end because when
  // we get a StringRef we can't guarantee that it points to null-terminated
  // memory.
  std::string Result{""};

  switch (T.getArch()) {
  default:
    break;
  case Triple::riscv32:
  case Triple::riscv64: {
    // Inspired by riscv::getRISCVABI in
    // clang/lib/Driver/ToolChains/Arch/RISCV.cpp.

    // Assuming that we wouldn't be called if the user had specified an ABI
    // explicitly, try to derive the ABI from the architecture.
    StringRef TargetArch = getRISCVArch(T, Arch, CPU, StringRef{});
    auto ParseResult = RISCVISAInfo::parseArchString(TargetArch, true);
    if (!llvm::errorToBool(ParseResult.takeError())) {
      Result = (*ParseResult)->computeDefaultABI();
      break;
    }

    // Use a default ABI based on the triple as a last resort.
    if (T.isRISCV32()) {
      if (T.getOS() == llvm::Triple::UnknownOS) {
        Result = "ilp32";
      } else {
        Result = "ilp32d";
      }
    } else {
      if (T.getOS() == llvm::Triple::UnknownOS) {
        Result = "lp64";
      } else {
        Result = "lp64d";
      }
    }

    break;
  }
  }

  return strdup(Result.c_str());
}

extern "C" unsigned Get_Default_Address_Space(const DataLayout &DL) {
  return DL.getDefaultGlobalsAddressSpace();
}

extern "C" bool Need_Enable_Execute_Stack(const char *Target) {
  // Decide whether we need to call __enable_execute_stack in order to make the
  // stack executable. The GNU linker does this automatically in ELF binaries,
  // but lld doesn't, and on Windows the helper function is also required.

  Triple TargetTriple(Target);
  return TargetTriple.isOSWindows() || TargetTriple.isOSLinux();
}

extern "C" void Print_Targets(void) {
  TargetRegistry::printRegisteredTargetsForVersion(outs());
}

extern "C" void Enable_Init_Array(TargetMachine *TM) {
  TM->Options.UseInitArray = 1;
}

extern "C" void Enable_Call_Graph_Section(TargetMachine *TM) {
#ifdef GNAT_LLVM_HAVE_EMIT_CALL_GRAPH_SECTION
  TM->Options.EmitCallGraphSection = 1;
#else
  errs() << "warning: call-graph section unsupported in this version of LLVM\n";
#endif
}

extern "C" void Enable_Stack_Size_Section(TargetMachine *TM) {
  TM->Options.EmitStackSizeSection = 1;
}

extern "C" void Enable_Function_Sections(TargetMachine *TM) {
  TM->Options.FunctionSections = 1;
}

extern "C" void Enable_Data_Sections(TargetMachine *TM) {
  TM->Options.DataSections = 1;
}

// The front-end call-graph info file. GCC's toplev opens this stream before
// invoking gnat1, and Exp_CG.Generate_CG_Output writes the dispatching-call
// edges and the tagged-type "class{}" declarations to it. gnat-llvm has no
// toplev, so the two routines below open it and read it back, and
// GNATLLVM.Codegen.Generate_Code puts the text into an object section.
//
// The variable is defined in gcc_missing.c.
extern "C" FILE *callgraph_info_file;

// Open a temporary stream as the call-graph info file and return true on
// success. Returns false, and changes nothing, if a stream is already open or
// if the file cannot be created. The caller diagnoses both the same way.
//
// tmpfile is deliberate and not one of LLVM's temporary file helpers.
// Exp_CG writes through an imported fputs, so the stream has to be a C
// FILE *, and nothing in LLVM gives one. tmpfile also has the OS remove
// the file on close and on abnormal termination.
extern "C" bool gnatllvm_open_callgraph_info_file(void) {
  if (callgraph_info_file != nullptr)
    return false;

  callgraph_info_file = tmpfile();

  return callgraph_info_file != nullptr;
}

// Return everything written to the call-graph info file so far, as a string
// allocated with strdup for the caller to free, and close the stream. An
// empty string means a unit with no descriptors, and null means that no
// stream was open or that the text could not be read.
// callgraph_info_file goes back to null either way, so the later call of
// Generate_CG_Output from gnat1drv finds no stream and does nothing.
extern "C" char *gnatllvm_take_callgraph_info_text(void) {
  FILE *F = callgraph_info_file;
  callgraph_info_file = nullptr;

  if (F == nullptr)
    return nullptr;

  char *Result = nullptr;
  SmallString<0> Text;

  // Generate_CG_Output has left f at the end, whereas readNativeFileToEOF
  // reads from the current position, so we have to rewind.

  if (fflush(F) == 0 && !ferror(F)) {
    rewind(F);

    if (Error E = sys::fs::readNativeFileToEOF(
            sys::fs::convertFDToNativeFile(fileno(F)), Text))
      consumeError(std::move(E));
    else
      Result = strdup(Text.c_str());
  }

  fclose(F);

  return Result;
}

// Metadata kind used to tag an indirect/dispatching call with its source
// location ("file:line:col").  The tag is attached at code-generation time
// (when the location is known) and survives inlining, so the post-optimization
// walk below can attribute the call to whatever function ends up containing it.
static const char *const CG_Loc_Kind = "gnat.cg.loc";

// Tag an indirect/dispatching call instruction with its source location.  A
// no-op on anything that is not an indirect call.
extern "C" void Set_Indirect_Call_Location(LLVMValueRef CallRef,
                                           const char *File, int Line,
                                           int Col) {
  CallBase *CB = dyn_cast_or_null<CallBase>(unwrap(CallRef));
  if (!CB || !CB->isIndirectCall())
    return;
  LLVMContext &Ctx = CB->getContext();
  std::string Loc = std::string(File ? File : "") + ":" + std::to_string(Line) +
                    ":" + std::to_string(Col);
  CB->setMetadata(CG_Loc_Kind, MDNode::get(Ctx, MDString::get(Ctx, Loc)));
}

// Walk the optimized module and produce one "__indirect_call" edge for every
// call that is still an indirect call there. This resolves dispatch even when
// the source-level caller was inlined. The result is the VCG text, allocated
// with strdup for the caller to free, or null when the module has no
// indirect call.
//
// An untagged indirect call is emitted without a "label:", which is what GCC
// writes for a statement with no location, and GNAT Stack then reports an
// unresolved indirect call.
extern "C" char *Get_Indirect_Call_Edges(LLVMModuleRef ModRef) {
  Module *M = unwrap(ModRef);
  unsigned KindID = M->getContext().getMDKindID(CG_Loc_Kind);
  std::string Buf;
  for (Function &Fn : *M)
    for (BasicBlock &BB : Fn)
      for (Instruction &I : BB) {
        CallBase *CB = dyn_cast<CallBase>(&I);
        if (CB == nullptr || !CB->isIndirectCall())
          continue;

        // The placeholder node for the edges' common target. This is what
        // GCC does (dump_final_node_vcg_start in gcc/toplev.cc), printed once
        // per unit that has an indirect call, "shape : ellipse" meaning
        // "referenced but not defined here". GNATStack parses the line and
        // throws it away, so we emit it for parity with GCC's output and for
        // any other reader of the format.

        if (Buf.empty())
          Buf = "node: { title: \"__indirect_call\" label: \"Indirect Call "
                "Placeholder\" shape : ellipse }\n";

        Buf += "edge: { sourcename: \"";
        Buf += Fn.getName().str();
        Buf += "\" targetname: \"__indirect_call\"";

        MDNode *MD = CB->getMetadata(KindID);
        MDString *S = MD != nullptr && MD->getNumOperands() != 0
                          ? dyn_cast<MDString>(MD->getOperand(0))
                          : nullptr;
        if (S != nullptr) {
          Buf += " label: \"";
          Buf += S->getString().str();
          Buf += "\"";
        }

        Buf += " }\n";
      }

  if (Buf.empty())
    return nullptr;

  return strdup(Buf.c_str());
}

// Append Text to the module as the whole content of the named section, using
// module-level inline assembly.  The linker then concatenates the sections of
// every object it links, so a linked binary carries the blocks of exactly the
// units it contains.
//
// Text is emitted as a .byte list rather than with .ascii: it contains quotes
// and backslashes, and a .byte list has no quoting rules to get wrong.  We use
// .pushsection/.popsection and not .section/.previous because module-level
// assembly is emitted before any function, so there is no previous section to
// return to. We give no section type: SHT_PROGBITS is what the assembler
// defaults to.
extern "C" void Append_Section_Data(LLVMModuleRef ModRef, const char *Section,
                                    const char *Text) {
  if (Section == nullptr || Text == nullptr || *Text == '\0')
    return;

  std::string Asm = "\t.pushsection\t";
  Asm += Section;
  Asm += ",\"\"\n";

  unsigned Count = 0;
  for (const char *P = Text; *P != '\0'; ++P) {
    Asm += (Count % 16 == 0 ? "\t.byte\t" : ",");
    Asm += utostr((unsigned char)*P);

    if (++Count % 16 == 0)
      Asm += "\n";
  }

  if (Count % 16 != 0)
    Asm += "\n";

  Asm += "\t.popsection\n";
  unwrap(ModRef)->appendModuleInlineAsm(Asm);
}

extern "C" void Create_And_Insert_Label(LLVMDIBuilderRef Builder,
                                        LLVMMetadataRef Scope, const char *Name,
                                        LLVMMetadataRef File, unsigned LineNo,
                                        unsigned ColmunNo,
                                        LLVMMetadataRef DebugLoc,
                                        LLVMBasicBlockRef Block) {
#if LLVM_VERSION_MAJOR < 21
  auto *L = unwrap(Builder)->createLabel(unwrap<DIScope>(Scope),
                                         StringRef(Name, strlen(Name)),
                                         unwrap<DIFile>(File), LineNo, false);
#else
  auto *L = unwrap(Builder)->createLabel(
      unwrap<DIScope>(Scope), StringRef(Name, strlen(Name)),
      unwrap<DIFile>(File), LineNo, ColmunNo, false, std::nullopt, false);
#endif
  unwrap(Builder)->insertLabel(L, unwrap<DILocation>(DebugLoc), unwrap(Block));
}

extern "C" MDNode *Create_Subrange_Type(
    LLVMDIBuilderRef Builder, LLVMMetadataRef Scope, const char *Name,
    LLVMMetadataRef File, unsigned LineNumber, uint64_t SizeInBits,
    uint32_t AlignInBits, LLVMDIFlags Flags, LLVMBool IsUnsigned,
    LLVMMetadataRef BaseType, LLVMMetadataRef LowerBound,
    LLVMMetadataRef UpperBound, LLVMMetadataRef Stride, LLVMMetadataRef Bias) {
  DINode::DIFlags DIF = static_cast<DINode::DIFlags>(Flags);
#ifdef GNAT_LLVM_HAVE_SUBRANGE_TYPE
  DIScope *DS = Scope ? unwrap<DIScope>(Scope) : nullptr;
  DIFile *DF = File ? unwrap<DIFile>(File) : nullptr;
  DIType *Ty = BaseType ? unwrap<DIType>(BaseType) : nullptr;
  return unwrap(Builder)->createSubrangeType(
      StringRef(Name, strlen(Name)), DF, LineNumber, DS, SizeInBits,
      AlignInBits, DIF, Ty, unwrap(LowerBound), unwrap(UpperBound),
      unwrap(Stride), unwrap(Bias));
#else
  return unwrap(Builder)->createBasicType(
      StringRef(Name, strlen(Name)), SizeInBits,
      IsUnsigned ? llvm::dwarf::DW_ATE_unsigned : llvm::dwarf::DW_ATE_signed,
      DIF);
#endif // GNAT_LLVM_HAVE_SUBRANGE_TYPE
}

extern "C" MDNode *Create_Array_Type_With_Name(
    LLVMDIBuilderRef Builder, LLVMMetadataRef Scope, const char *Name,
    LLVMMetadataRef File, unsigned LineNo, uint64_t Size, uint32_t AlignInBits,
    LLVMMetadataRef Ty, LLVMMetadataRef BitStride, LLVMMetadataRef *Subscripts,
    unsigned NumSubscripts) {
  auto Subs =
      unwrap(Builder)->getOrCreateArray({unwrap(Subscripts), NumSubscripts});
#ifdef GNAT_LLVM_HAVE_ARRAY_NAME
  DIScope *DS = Scope ? unwrap<DIScope>(Scope) : nullptr;
  DIFile *DF = File ? unwrap<DIFile>(File) : nullptr;
  return unwrap(Builder)->createArrayType(
      DS, StringRef(Name, strlen(Name)), DF, LineNo, Size, AlignInBits,
      unwrap<DIType>(Ty), Subs, nullptr, nullptr, nullptr, nullptr,
      unwrap(BitStride));
#else
  return unwrap(Builder)->createArrayType(Size, AlignInBits, unwrap<DIType>(Ty),
                                          Subs);
#endif // GNAT_LLVM_HAVE_ARRAY_NAME
}

extern "C" Metadata *Constant_As_Metadata(LLVMContext *Context,
                                          MDBuilder *MDHelper, bool IsNegative,
                                          unsigned NumWords,
                                          const uint64_t Words[]) {
  auto Result = APInt(NumWords * 64, {Words, NumWords});
  // We know the words represent a positive value.  So, if the sign
  // bit is set, we need some extra precision.
  if (Result.isSignBitSet())
    Result = Result.zext(Result.getBitWidth() + 1);
  if (IsNegative)
    Result.negate();
  return MDHelper->createConstant(ConstantInt::get(*Context, Result));
}

extern "C" Metadata *Create_Enumerator(LLVMDIBuilderRef Builder,
                                       const char *Name, bool IsNegative,
                                       unsigned NumWords,
                                       const uint64_t Words[]) {
  auto Value = APInt(NumWords * 64, {Words, NumWords});
  // We know the words represent a positive value.  So, if the sign
  // bit is set, we need some extra precision.
  if (Value.isSignBitSet())
    Value = Value.zext(Value.getBitWidth() + 1);
  if (IsNegative)
    Value.negate();
  return unwrap(Builder)->createEnumerator({Name, strlen(Name)},
                                           APSInt(Value, !IsNegative));
}

extern "C" MDNode *Create_Binary_Fixed_Point_Type(
    LLVMDIBuilderRef Builder, const char *Name, const char *FullName,
    LLVMMetadataRef File, unsigned LineNo, LLVMMetadataRef Scope, uint64_t Size,
    uint32_t AlignInBits, bool IsUnsigned, int Factor) {
#ifdef GNAT_LLVM_HAVE_FIXED_POINT
  DIScope *DS = Scope ? unwrap<DIScope>(Scope) : nullptr;
  DIFile *DF = File ? unwrap<DIFile>(File) : nullptr;
  return unwrap(Builder)->createBinaryFixedPointType(
#ifdef GNAT_LLVM_HAVE_BASIC_TYPE_SCOPE
      Name, DF, LineNo, DS,
#else
      FullName,
#endif // GNAT_LLVM_HAVE_BASIC_TYPE_SCOPE
      Size, AlignInBits,
      IsUnsigned ? dwarf::DW_ATE_unsigned_fixed : dwarf::DW_ATE_signed_fixed,
      DINode::FlagZero, Factor);
#else
  return unwrap(Builder)->createBasicType(
      Name, Size, IsUnsigned ? dwarf::DW_ATE_unsigned : dwarf::DW_ATE_signed,
      DINode::FlagZero);
#endif // GNAT_LLVM_HAVE_FIXED_POINT
}

extern "C" MDNode *Create_Decimal_Fixed_Point_Type(
    LLVMDIBuilderRef Builder, const char *Name, const char *FullName,
    LLVMMetadataRef File, unsigned LineNo, LLVMMetadataRef Scope, uint64_t Size,
    uint32_t AlignInBits, bool IsUnsigned, int Factor) {
#ifdef GNAT_LLVM_HAVE_FIXED_POINT
  DIScope *DS = Scope ? unwrap<DIScope>(Scope) : nullptr;
  DIFile *DF = File ? unwrap<DIFile>(File) : nullptr;
  return unwrap(Builder)->createDecimalFixedPointType(
#ifdef GNAT_LLVM_HAVE_BASIC_TYPE_SCOPE
      Name, DF, LineNo, DS,
#else
      FullName,
#endif // GNAT_LLVM_HAVE_BASIC_TYPE_SCOPE
      Size, AlignInBits,
      IsUnsigned ? dwarf::DW_ATE_unsigned_fixed : dwarf::DW_ATE_signed_fixed,
      DINode::FlagZero, Factor);
#else
  return unwrap(Builder)->createBasicType(
      Name, Size, IsUnsigned ? dwarf::DW_ATE_unsigned : dwarf::DW_ATE_signed,
      DINode::FlagZero);
#endif // GNAT_LLVM_HAVE_FIXED_POINT
}

extern "C" MDNode *Create_Rational_Fixed_Point_Type(
    LLVMDIBuilderRef Builder, const char *Name, const char *FullName,
    LLVMMetadataRef File, unsigned LineNo, LLVMMetadataRef Scope, uint64_t Size,
    uint32_t AlignInBits, bool IsUnsigned, Metadata *Num, Metadata *Denom) {
#ifdef GNAT_LLVM_HAVE_FIXED_POINT
  Constant *Num_C = dyn_cast<ConstantAsMetadata>(Num)->getValue();
  ConstantInt *Num_Int = dyn_cast<ConstantInt>(Num_C);

  Constant *Denom_C = dyn_cast<ConstantAsMetadata>(Denom)->getValue();
  ConstantInt *Denom_Int = dyn_cast<ConstantInt>(Denom_C);

  DIScope *DS = Scope ? unwrap<DIScope>(Scope) : nullptr;
  DIFile *DF = File ? unwrap<DIFile>(File) : nullptr;
  return unwrap(Builder)->createRationalFixedPointType(
#ifdef GNAT_LLVM_HAVE_BASIC_TYPE_SCOPE
      Name, DF, LineNo, DS,
#else
      FullName,
#endif // GNAT_LLVM_HAVE_BASIC_TYPE_SCOPE
      Size, AlignInBits,
      IsUnsigned ? dwarf::DW_ATE_unsigned_fixed : dwarf::DW_ATE_signed_fixed,
      DINode::FlagZero, Num_Int->getValue(), Denom_Int->getValue());
#else
  return unwrap(Builder)->createBasicType(
      Name, Size, IsUnsigned ? dwarf::DW_ATE_unsigned : dwarf::DW_ATE_signed,
      DINode::FlagZero);
#endif // GNAT_LLVM_HAVE_FIXED_POINT
}

extern "C" MDNode *Create_Basic_Type(LLVMDIBuilderRef Builder, const char *Name,
                                     const char *FullName, LLVMMetadataRef File,
                                     unsigned LineNo, LLVMMetadataRef Scope,
                                     uint64_t Size, unsigned Encoding,
                                     LLVMDIFlags Flags) {
  DINode::DIFlags DIF = static_cast<DINode::DIFlags>(Flags);
  DIScope *DS = Scope ? unwrap<DIScope>(Scope) : nullptr;
  DIFile *DF = File ? unwrap<DIFile>(File) : nullptr;
  return unwrap(Builder)->createBasicType(
#ifdef GNAT_LLVM_HAVE_BASIC_TYPE_SCOPE
      Name, DF, LineNo, DS,
#else
      FullName,
#endif // GNAT_LLVM_HAVE_BASIC_TYPE_SCOPE
      Size, Encoding, DIF);
}

extern "C" void Add_Instruction_Combining_Pass(legacy::PassManager *PM) {
  PM->add(createInstructionCombiningPass());
}

extern "C" bool Types_Can_Have_Function_Scope() {
#ifdef GNAT_LLVM_HAVE_TYPE_FN_SCOPE
  return true;
#else
  return false;
#endif
}

extern "C" bool Types_Can_Have_Dynamic_Offsets() {
#ifdef GNAT_LLVM_HAVE_DYNAMIC_OFFSETS
  return true;
#else
  return false;
#endif
}

extern "C" bool Types_Can_Have_Multiple_Variant_Members() {
#ifdef GNAT_LLVM_HAVE_MULTI_MEMBER_VARIANT
  return true;
#else
  return false;
#endif
}

extern "C" bool DI_Expression_Extensions() {
#ifdef GNAT_LLVM_HAVE_DW_EXPRESSION_EXTENSIONS
  return true;
#else
  return false;
#endif
}

extern "C" bool DI_Subrange_Allows_Member() {
#ifdef GNAT_LLVM_HAVE_SUBRANGE_TYPE_EXTENSION
  return true;
#else
  return false;
#endif
}

extern "C" bool DI_Nameless_Basic_Types() {
#ifdef GNAT_LLVM_HAVE_NAMELESS_BASIC_TYPE
  return true;
#else
  return false;
#endif
}

extern "C" bool Can_Create_Expression_With_Variable() {
#ifdef GNAT_LLVM_HAVE_DIVARIABLEEXPRESSION
  return true;
#else
  return false;
#endif
}

extern "C" uint64_t Get_DW_OP_LLVM_arg() { return llvm::dwarf::DW_OP_LLVM_arg; }

extern "C" LLVMMetadataRef Create_Global_Variable_Declaration(
    LLVMDIBuilderRef Builder, LLVMMetadataRef Scope, const char *Name,
    const char *Linkage, LLVMMetadataRef File, unsigned LineNo,
    LLVMMetadataRef Ty, LLVMBool LocalToUnit, LLVMMetadataRef Expr,
    LLVMMetadataRef Decl, uint32_t AlignInBits) {
  DIScope *DS = Scope ? unwrap<DIScope>(Scope) : nullptr;
  DIFile *DF = File ? unwrap<DIFile>(File) : nullptr;
  MDNode *MD = Decl ? unwrap<MDNode>(Decl) : nullptr;

  return wrap(unwrap(Builder)->createGlobalVariableExpression(
      DS, {Name, strlen(Name)}, {Linkage, strlen(Linkage)}, DF, LineNo,
      unwrap<DIType>(Ty), LocalToUnit, false, unwrap<DIExpression>(Expr), MD,
      nullptr, AlignInBits));
}

extern "C" LLVMMetadataRef Replace_Composite_Elements(LLVMDIBuilderRef Builder,
                                                      LLVMMetadataRef Composite,
                                                      LLVMMetadataRef *Elements,
                                                      unsigned NumElements) {
  auto Elems =
      unwrap(Builder)->getOrCreateArray({unwrap(Elements), NumElements});
  DICompositeType *T = unwrap<DICompositeType>(Composite);
  unwrap(Builder)->replaceArrays(T, Elems);
  // T might have been modified by replaceArrays.
  return wrap(T);
}

extern "C" LLVMMetadataRef Create_Variant_Part(LLVMDIBuilderRef Builder,
                                               LLVMMetadataRef Discriminator,
                                               LLVMMetadataRef *Elements,
                                               unsigned NumElements) {
  DIDerivedType *Disc =
      Discriminator ? unwrap<DIDerivedType>(Discriminator) : nullptr;
  auto Elems =
      unwrap(Builder)->getOrCreateArray({unwrap(Elements), NumElements});

  return wrap(unwrap(Builder)->createVariantPart(
      nullptr, {}, nullptr, 0, 0, 0, DINode::FlagZero, Disc, Elems));
}

extern "C" LLVMMetadataRef
Create_Variant_Member(LLVMContext *Context, LLVMDIBuilderRef Builder,
                      LLVMMetadataRef *Elements, unsigned NumElements,
                      uint64_t *Discriminants, unsigned NumDiscriminants) {
#ifdef GNAT_LLVM_HAVE_MULTI_MEMBER_VARIANT
  auto Elems =
      unwrap(Builder)->getOrCreateArray({unwrap(Elements), NumElements});
  Constant *D = nullptr;
  // Note that this small optimization is actually required: when
  // adding support for discriminant lists to LLVM, I did not realize
  // that ConstantDataArray::get will return a ConstantAggregateZero
  // when possible; and so the DWARF generation code does not handle
  // this case.  If a variant uses "when 0", this will result in a
  // discriminant array of {0, 0}, which would then be ignored by the
  // DWARF writer.  This optimization works around this oddity to
  // provide correct DWARF output.
  if (NumDiscriminants == 2 && Discriminants[0] == Discriminants[1]) {
    D = ConstantInt::get(Type::getInt64Ty(*Context), Discriminants[0]);
  } else if (NumDiscriminants > 0) {
    ArrayRef<uint64_t> Vals(Discriminants, NumDiscriminants);
    D = ConstantDataArray::get(*Context, Vals);
  }
  return wrap(
      unwrap(Builder)->createVariantMemberType(nullptr, Elems, D, nullptr));
#else
  // This should never be called in this situation.
  assert(0);
#endif
}

extern "C" LLVMMetadataRef Create_Pointer_Type(LLVMDIBuilderRef Builder,
                                               LLVMMetadataRef Pointee,
                                               uint64_t SizeInBits,
                                               uint32_t AlignInBits) {
  return wrap(unwrap(Builder)->createPointerType(unwrap<DIType>(Pointee),
                                                 SizeInBits, AlignInBits));
}

extern "C" LLVMMetadataRef
Create_Member(LLVMDIBuilderRef Builder, LLVMMetadataRef Scope, const char *Name,
              LLVMMetadataRef File, unsigned LineNo, LLVMMetadataRef SizeInBits,
              LLVMMetadataRef OffsetInBits, LLVMMetadataRef Ty,
              LLVMDIFlags Flags, LLVMBool IsBitField) {
#ifdef GNAT_LLVM_HAVE_DYNAMIC_OFFSETS
  DINode::DIFlags DIF = static_cast<DINode::DIFlags>(Flags);
  DIScope *DS = Scope ? unwrap<DIScope>(Scope) : nullptr;
  DIFile *DF = File ? unwrap<DIFile>(File) : nullptr;
  Metadata *SB = SizeInBits ? unwrap(SizeInBits) : nullptr;
  Metadata *OB = OffsetInBits ? unwrap(OffsetInBits) : nullptr;
  DIDerivedType *Result;
  if (IsBitField) {
    Result = unwrap(Builder)->createBitFieldMemberType(
        DS, Name, DF, LineNo, SB, OB, 0, DIF, unwrap<DIType>(Ty));
  } else {
    Result = unwrap(Builder)->createMemberType(DS, Name, DF, LineNo, SB, 0, OB,
                                               DIF, unwrap<DIType>(Ty));
  }
  return wrap(Result);
#else
  // This should never be called in this situation.
  assert(0);
#endif
}

extern "C" LLVMMetadataRef Create_Struct_Type_Non_Constant_Size(
    LLVMDIBuilderRef Builder, LLVMMetadataRef Scope, const char *Name,
    LLVMMetadataRef File, unsigned LineNo, LLVMMetadataRef SizeInBits,
    uint32_t AlignInBits, LLVMDIFlags Flags, LLVMMetadataRef DerivedFrom,
    LLVMMetadataRef *Elements, unsigned NumElements, unsigned RunTimeLang,
    LLVMMetadataRef VTableHolder, const char *UniqueId) {
#ifdef GNAT_LLVM_HAVE_DYNAMIC_OFFSETS
  DINode::DIFlags DIF = static_cast<DINode::DIFlags>(Flags);
  DIScope *DS = Scope ? unwrap<DIScope>(Scope) : nullptr;
  DIFile *DF = File ? unwrap<DIFile>(File) : nullptr;
  Metadata *SB = SizeInBits ? unwrap(SizeInBits) : nullptr;
  DIType *DerF = DerivedFrom ? unwrap<DIType>(DerivedFrom) : nullptr;
  DIType *VTH = VTableHolder ? unwrap<DIType>(VTableHolder) : nullptr;
  StringRef NameRef(Name);
  StringRef UniqueRef(UniqueId);
  auto Elems =
      unwrap(Builder)->getOrCreateArray({unwrap(Elements), NumElements});
  DICompositeType *Result = unwrap(Builder)->createStructType(
      DS, NameRef, DF, LineNo, SB, AlignInBits, DIF, DerF, Elems, RunTimeLang,
      VTH, UniqueRef);
  return wrap(Result);
#else
  // This should never be called in this situation.
  assert(0);
#endif
}

extern "C" LLVMMetadataRef
Create_Expression_With_Variables(LLVMDIBuilderRef Builder, uint64_t *Expr,
                                 size_t Expr_Len, LLVMMetadataRef *Vars,
                                 size_t Vars_Len) {
#ifdef GNAT_LLVM_HAVE_DIVARIABLEEXPRESSION
  return wrap(unwrap(Builder)->createExpressionWithVariables(
      {Expr, Expr_Len}, {unwrap(Vars), Vars_Len}));
#else
  // This should never be called in this situation.
  assert(0);
#endif
}

// Attach self-referential `llvm.loop` metadata to a loop latch terminator so
// the vectorizer / unroller act on the loop.  This mirrors what Clang emits for
// `#pragma omp simd` and is the first native OpenMP lowering hook used by
// GNAT-LLVM (`pragma OpenMP (Simd, ...)`).
extern "C" void Set_Loop_Metadata_For_Vectorize(LLVMValueRef Term_Ref,
                                                unsigned Enable,
                                                unsigned Width,
                                                unsigned Unroll) {
  auto *Term = dyn_cast<Instruction>(unwrap(Term_Ref));
  if (!Term)
    return;

  LLVMContext &Ctx = Term->getContext();
  SmallVector<Metadata *, 4> Loop_Ops;
  // The first operand must be a self-reference; fill it in after creating a
  // distinct node (a uniqued node cannot be made self-referential).
  Loop_Ops.push_back(nullptr);

  auto Add_Bool = [&](const char *Name) {
    Loop_Ops.push_back(MDNode::get(
        Ctx, {MDString::get(Ctx, Name),
              ConstantAsMetadata::get(
                  ConstantInt::get(Type::getInt1Ty(Ctx), 1))}));
  };

  if (Enable)
    Add_Bool("llvm.loop.vectorize.enable");
  if (Unroll)
    Add_Bool("llvm.loop.unroll.enable");

  if (Width > 1) {
    Loop_Ops.push_back(MDNode::get(
        Ctx, {MDString::get(Ctx, "llvm.loop.vectorize.width"),
              ConstantAsMetadata::get(
                  ConstantInt::get(Type::getInt32Ty(Ctx), Width))}));
  }

  MDNode *Loop_ID = MDNode::getDistinct(Ctx, Loop_Ops);
  Loop_ID->replaceOperandWith(0, Loop_ID);
  Term->setMetadata(LLVMContext::MD_loop, Loop_ID);
}

// ---------------------------------------------------------------------------
// Native OpenMP parallel-for outlining
// ---------------------------------------------------------------------------

namespace {

// Create (once per module) a helper returning the per-thread numeric lower
// (High = false) or upper (High = true) bound of [Lo, Hi] for a static split
// across the current OpenMP team.  Implemented in IR so that no extra runtime
// object has to be linked beyond libomp itself.
Function *Get_Or_Create_Range_Fn(Module *M, bool High, bool Strided) {
  const char *Name =
      Strided ? (High ? "gnat.omp.thread_high.strided"
                      : "gnat.omp.thread_low.strided")
              : (High ? "gnat.omp.thread_high" : "gnat.omp.thread_low");
  if (Function *Existing = M->getFunction(Name))
    return Existing;

  LLVMContext &Ctx = M->getContext();
  Type *I64 = Type::getInt64Ty(Ctx);
  FunctionType *FT = FunctionType::get(I64, {I64, I64}, false);
  Function *F = Function::Create(FT, GlobalValue::InternalLinkage, Name, M);
  BasicBlock *Entry = BasicBlock::Create(Ctx, "entry", F);
  IRBuilder<> B(Entry);

  Value *Lo = F->getArg(0);
  Value *Hi = F->getArg(1);
  FunctionCallee TidF =
      M->getOrInsertFunction("omp_get_thread_num", Type::getInt32Ty(Ctx));
  FunctionCallee NumF =
      M->getOrInsertFunction("omp_get_num_threads", Type::getInt32Ty(Ctx));
  Value *Tid = B.CreateSExt(B.CreateCall(TidF), I64);
  Value *Num = B.CreateSExt(B.CreateCall(NumF), I64);

  // total = Hi - Lo + 1, clamped to >= 0
  Value *Total = B.CreateAdd(B.CreateSub(Hi, Lo), B.getInt64(1));
  Value *NonEmpty = B.CreateICmpSGT(Total, B.getInt64(0));
  Value *T = B.CreateSelect(NonEmpty, Total, B.getInt64(0));
  // A team has at least one thread.
  Value *NumPos = B.CreateICmpSGT(Num, B.getInt64(0));
  Value *N = B.CreateSelect(NumPos, Num, B.getInt64(1));
  // Clamp tid into [0, N-1], then drop ids without any work.
  Value *TidInTeam =
      B.CreateSelect(B.CreateICmpSLT(Tid, N), Tid, B.CreateSub(N, B.getInt64(1)));

  // T and N are non-negative counts here; unsigned division gives the
  // floor semantics Ada uses for `mod` and avoids signed-truncation bias.
  Value *Base = B.CreateUDiv(T, N);
  Value *Rem = B.CreateURem(T, N);
  Value *HasExtra = B.CreateICmpULT(TidInTeam, Rem);
  Value *Extra =
      B.CreateSelect(HasExtra, B.getInt64(1), B.getInt64(0));

  Value *LowP, *HighP;
  if (Strided) {
    // Cyclic split: thread t runs Lo+t, Lo+t+N, ... This makes consecutive
    // CUDA lanes touch consecutive elements on every iteration (coalesced
    // global memory accesses), unlike a contiguous chunk per thread.
    Value *Start = B.CreateAdd(Lo, TidInTeam);
    Value *Count = B.CreateAdd(Base, Extra);
    // Threads whose id >= total have no work: start past the end and set the
    // upper bound below it so the empty-range guard skips the loop.
    Value *NoWork = B.CreateICmpUGE(TidInTeam, T);
    Value *RealStart = B.CreateSelect(NoWork, B.CreateAdd(Lo, T), Start);
    Value *RealCount = B.CreateSelect(NoWork, B.getInt64(0), Count);
    Value *Span =
        B.CreateMul(B.CreateSub(RealCount, B.getInt64(1)), N);
    LowP = RealStart;
    HighP = B.CreateAdd(RealStart, Span);
  } else {
    Value *Offset =
        B.CreateAdd(B.CreateMul(TidInTeam, Base),
                    B.CreateSelect(HasExtra, TidInTeam, Rem));
    LowP = B.CreateAdd(Lo, Offset);
    HighP = B.CreateSub(B.CreateAdd(LowP, B.CreateAdd(Base, Extra)),
                        B.getInt64(1));
  }

  if (!High)
    return B.CreateRet(LowP), F;
  return B.CreateRet(HighP), F;
}

// Emit a call to the range helper at At, returning a value of type Ty.
Value *Range_Call(Module *M, bool High, Value *Lo, Value *Hi, Type *Ty,
                  Instruction *At, bool Strided = false) {
  Function *F = Get_Or_Create_Range_Fn(M, High, Strided);
  IRBuilder<> B(At);
  Type *I64 = B.getInt64Ty();
  Value *L = B.CreateSExtOrTrunc(Lo, I64);
  Value *H = B.CreateSExtOrTrunc(Hi, I64);
  Value *C = B.CreateCall(F, {L, H});
  return B.CreateSExtOrTrunc(C, Ty);
}

Constant *Get_OpenMP_Target_Ident(Module *M) {
  if (GlobalVariable *G = M->getNamedGlobal("gnat.omp.target.ident"))
    return G;

  LLVMContext &Ctx = M->getContext();
  Type *I32 = Type::getInt32Ty(Ctx);
  Type *Ptr = PointerType::getUnqual(Ctx);
  StructType *IdentTy = StructType::get(I32, I32, I32, I32, Ptr);

  // OpenMP source-info format expected by libomptarget: ;file;func;line;col;;
  Constant *Src = ConstantDataArray::getString(
      Ctx, ";unknown;unknown;0;0;;", true);
  auto *SrcGV = new GlobalVariable(*M, Src->getType(), true,
                                   GlobalValue::InternalLinkage, Src,
                                   "gnat.omp.target.source");
  Constant *SrcPtr = ConstantExpr::getBitCast(SrcGV, Ptr);
  // flags = 2 marks the region as requiring an OpenMP device.
  Constant *Init = ConstantStruct::get(
      IdentTy, {ConstantInt::get(I32, 0), ConstantInt::get(I32, 2),
                ConstantInt::get(I32, 0), ConstantInt::get(I32, 0), SrcPtr});
  return new GlobalVariable(*M, IdentTy, true, GlobalValue::InternalLinkage,
                            Init, "gnat.omp.target.ident");
}

// Emit a device image for the outlined region and register it with
// libomptarget.  The current implementation builds a host (x86_64) image, so
// the runtime's host plugin executes the kernel; the same machinery can emit
// amdgcn/nvptx images once a device toolchain is available.
// Best-effort size of the object a mapped pointer refers to.
static Value *Build_Mapped_Size(IRBuilder<> &B, Value *V,
                                const DataLayout &DL, bool &Known) {
  Type *I64 = B.getInt64Ty();
  if (auto *AI = dyn_cast<AllocaInst>(V)) {
    uint64_t Elem = DL.getTypeAllocSize(AI->getAllocatedType());
    if (!AI->isArrayAllocation())
      return ConstantInt::get(I64, Elem);
    // Ada arrays sized by a runtime N are emitted as VLAs: alloca T, i64 N.
    // The element count dominates the target call, so multiply it by the
    // element size in the host IR and let libomptarget see the real byte count.
    Value *Count = B.CreateZExtOrTrunc(AI->getArraySize(), I64);
    return B.CreateMul(Count, ConstantInt::get(I64, Elem));
  }
  if (auto *GV = dyn_cast<GlobalVariable>(V))
    return ConstantInt::get(I64, DL.getTypeAllocSize(GV->getValueType()));
  if (auto *BC = dyn_cast<BitCastOperator>(V))
    return Build_Mapped_Size(B, BC->getOperand(0), DL, Known);
  if (auto *GEP = dyn_cast<GEPOperator>(V))
    return Build_Mapped_Size(B, GEP->getPointerOperand(), DL, Known);
  // The pointer's extent is not statically known here (e.g. a heap pointer
  // passed in from a call).  Do not emit a device image for this region:
  // mapping zero bytes would leave the kernel reading unmapped device memory.
  Known = false;
  return ConstantInt::get(I64, 0);
}

// Emit an NVPTX (PTX) device image for the outlined region.  The image is
// packed in the libomptarget offload-binary format with the nvptx64 triple and
// sm_89 arch, so the CUDA plugin can JIT it with ptxas.  omp_get_thread_num /
// omp_get_num_threads are defined from NVPTX special registers so the existing
// static range helpers split the loop across the launched CUDA threads.
struct OMPRegion {
  std::string EName;
  GlobalVariable *RegionId;
  std::string KernelName;
  unsigned NArgs;
};
static SmallVector<OMPRegion, 4> Pending_OMP_Regions;

extern "C" void Register_OpenMP_Target(Module *M, Function *E,
                                       GlobalVariable *RegionId,
                                       const char *KernelName,
                                       unsigned NArgs) {
  Pending_OMP_Regions.push_back({E->getName().str(), RegionId, KernelName,
                                 NArgs});
}

// Build one NVPTX cubin containing all target kernels of the translation unit.
static bool Emit_OpenMP_NVPTX_Image(Module *M, ArrayRef<OMPRegion> Regions,
                                    SmallVectorImpl<char> &Bytes) {
  if (Regions.empty())
    return false;
  LLVMContext &Ctx = M->getContext();
  Type *Ptr = PointerType::getUnqual(Ctx);
  Type *Void = Type::getVoidTy(Ctx);
  for (const OMPRegion &R : Regions) {
    Function *Source = M->getFunction(R.EName);
    if (!Source)
      continue;
    FunctionType *EFT = Source->getFunctionType();
    if (EFT->getNumParams() != R.NArgs || R.NArgs == 0)
      return false;
  }

  const char *TripleStr = "nvptx64-nvidia-cuda";
  const char *Arch = "sm_89";
  Triple TT = Triple(StringRef(TripleStr));
  std::string Err;
  const Target *T = TargetRegistry::lookupTarget(TT, Err);
  if (!T)
    return false;
  llvm::TargetOptions Opt;
  std::unique_ptr<TargetMachine> TM(T->createTargetMachine(
      TT, Arch, "", Opt, std::nullopt, std::nullopt, CodeGenOptLevel::None));
  if (!TM)
    return false;

  ValueToValueMapTy VMap;
  std::unique_ptr<Module> DM = CloneModule(*M, VMap);
  DM->setModuleIdentifier("gnat.omp.nvptx.device");
  DM->setTargetTriple(TT);
  DM->setDataLayout(TM->createDataLayout());
  for (const char *Name : {"llvm.global_ctors", "llvm.used",
                           "llvm.compiler.used"})
    if (GlobalVariable *G = DM->getNamedGlobal(Name))
      G->eraseFromParent();
  if (NamedMDNode *N = DM->getNamedMetadata("llvm.offloading.symbols"))
    DM->eraseNamedMetadata(N);
  for (GlobalVariable &G : llvm::make_early_inc_range(DM->globals()))
    if (G.getName().contains("offloading") ||
        G.getName().starts_with("gnat.omp.region.id"))
      G.eraseFromParent();

  // Define the OpenMP thread queries from NVPTX special registers.
  auto DefineTid = [&](StringRef Name, bool IsNum) {
    Function *F = DM->getFunction(Name);
    if (!F)
      return;
    F->deleteBody();
    IRBuilder<> B(BasicBlock::Create(Ctx, "entry", F));
    auto Intr = [&](Intrinsic::ID ID) {
      return Intrinsic::getOrInsertDeclaration(DM.get(), ID);
    };
    Function *Tid = Intr(static_cast<Intrinsic::ID>(
        Intrinsic::nvvm_read_ptx_sreg_tid_x));
    Function *NTid = Intr(static_cast<Intrinsic::ID>(
        Intrinsic::nvvm_read_ptx_sreg_ntid_x));
    Function *Ctaid = Intr(static_cast<Intrinsic::ID>(
        Intrinsic::nvvm_read_ptx_sreg_ctaid_x));
    Function *NCtaid = Intr(static_cast<Intrinsic::ID>(
        Intrinsic::nvvm_read_ptx_sreg_nctaid_x));
    Value *Result;
    if (IsNum)
      Result = B.CreateMul(B.CreateCall(NTid), B.CreateCall(NCtaid));
    else {
      Value *T = B.CreateCall(Tid);
      Value *NT = B.CreateCall(NTid);
      Value *CTA = B.CreateCall(Ctaid);
      Result = B.CreateAdd(T, B.CreateMul(CTA, NT));
    }
    B.CreateRet(B.CreateZExtOrTrunc(Result, F->getReturnType()));
  };
  DefineTid("omp_get_thread_num", false);
  DefineTid("omp_get_num_threads", true);

  SmallVector<Function *, 4> Kernels;
  for (const OMPRegion &R : Regions) {
    Function *Source = M->getFunction(R.EName);
    if (!Source)
      continue;
    FunctionType *EFT = Source->getFunctionType();
    Function *DE = DM->getFunction(R.EName);
    if (!DE)
      continue;
    // Generic-mode environment: without it libomptarget launches in BARE mode
    // with zero threads and cuLaunchKernel fails with INVALID_VALUE.
    Type *I8 = Type::getInt8Ty(Ctx);
    Type *I32 = Type::getInt32Ty(Ctx);
    StructType *ConfigTy =
        StructType::get(Ctx, {I8, I8, I8, I32, I32, I32, I32, I32, I32});
    StructType *EnvTy = StructType::get(Ctx, {ConfigTy, Ptr, Ptr});
    auto *Config = ConstantStruct::get(
        ConfigTy, {ConstantInt::get(I8, 2), ConstantInt::get(I8, 2),
                   ConstantInt::get(I8, 2), ConstantInt::get(I32, -1),
                   ConstantInt::get(I32, -1), ConstantInt::get(I32, -1),
                   ConstantInt::get(I32, -1), ConstantInt::get(I32, 0),
                   ConstantInt::get(I32, 0)});
    auto *Env = ConstantStruct::get(
        EnvTy, {Config, ConstantPointerNull::get(cast<PointerType>(Ptr)),
                ConstantPointerNull::get(cast<PointerType>(Ptr))});
    auto *EnvGV = new GlobalVariable(
        *DM, EnvTy, true, GlobalValue::WeakODRLinkage, Env,
        R.KernelName + "_kernel_environment", nullptr,
        GlobalValue::NotThreadLocal,
        DM->getDataLayout().getDefaultGlobalsAddressSpace());
    EnvGV->setVisibility(GlobalValue::ProtectedVisibility);

    DE->setLinkage(GlobalValue::InternalLinkage);
    SmallVector<Type *, 8> KParams(1 + EFT->getNumParams(), Ptr);
    Function *K = Function::Create(FunctionType::get(Void, KParams, false),
                                   GlobalValue::ExternalLinkage,
                                   R.KernelName, DM.get());
    K->setCallingConv(llvm::CallingConv::PTX_Kernel);
    IRBuilder<> KB(BasicBlock::Create(Ctx, "entry", K));
    SmallVector<Value *, 8> Fwd;
    for (unsigned I = 0; I < EFT->getNumParams(); ++I) {
      Type *PT = EFT->getParamType(I);
      Value *A = K->getArg(I + 1);
      Fwd.push_back(PT->isPointerTy() ? A : KB.CreateLoad(PT, A));
    }
    KB.CreateCall(DE, Fwd);
    KB.CreateRetVoid();
    Kernels.push_back(K);
  }

  SmallPtrSet<Function *, 32> Live;
  SmallVector<Function *, 32> Work(Kernels.begin(), Kernels.end());
  while (!Work.empty()) {
    Function *F = Work.pop_back_val();
    if (!Live.insert(F).second)
      continue;
    for (BasicBlock &BB : *F)
      for (Instruction &I : BB)
        if (auto *CB = dyn_cast<CallBase>(&I))
          if (Function *Callee = CB->getCalledFunction())
            Work.push_back(Callee);
  }
  for (Function &F : llvm::make_early_inc_range(*DM))
    if (!F.isDeclaration() && !Live.count(&F))
      F.eraseFromParent();
  for (GlobalVariable &G : llvm::make_early_inc_range(DM->globals()))
    if (!G.isDeclaration() && G.hasLocalLinkage() && G.use_empty())
      G.eraseFromParent();

  if (std::getenv("GNAT_LLVM_VERIFY_DEVICE_IR"))
    verifyModule(*DM, &errs());
  SmallVector<char, 0> PTX;
  raw_svector_ostream PTXOS(PTX);
  legacy::PassManager PM;
  if (TM->addPassesToEmitFile(PM, PTXOS, nullptr,
                              CodeGenFileType::AssemblyFile))
    return false;
  PM.run(*DM);

  auto PtxasOrErr = sys::findProgramByName("ptxas");
  if (!PtxasOrErr) {
    if (sys::fs::exists("/usr/local/cuda/bin/ptxas"))
      PtxasOrErr = std::string("/usr/local/cuda/bin/ptxas");
    else
      return false;
  }
  SmallString<128> PTXPath, CubinPath;
  int PTXFD = -1;
  if (sys::fs::createTemporaryFile("gnat-omp-nvptx", "ptx", PTXFD, PTXPath))
    return false;
  {
    raw_fd_ostream PTXFile(PTXFD, true);
    PTXFile.write(PTX.data(), PTX.size());
  }
  CubinPath = PTXPath;
  CubinPath += ".cubin";
  SmallVector<StringRef, 8> PtxasArgs = {
      *PtxasOrErr, "-m64", "-O3", "--gpu-name", Arch,
      "-o", CubinPath, PTXPath};
  std::string ExecErr;
  int RC = sys::ExecuteAndWait(*PtxasOrErr, PtxasArgs, std::nullopt, {}, 0, 0,
                               &ExecErr);
  if (RC != 0) {
    errs() << "gnat-omp: ptxas failed: " << ExecErr << "\n";
    sys::fs::remove(PTXPath);
    return false;
  }
  sys::fs::remove(PTXPath);
  auto CubinOrErr = MemoryBuffer::getFile(CubinPath);
  sys::fs::remove(CubinPath);
  if (!CubinOrErr)
    return false;

  object::OffloadBinary::OffloadingImage Img;
  Img.TheImageKind = object::IMG_Object;
  Img.TheOffloadKind = object::OFK_OpenMP;
  Img.Flags = 0;
  Img.StringData["triple"] = TripleStr;
  Img.StringData["arch"] = Arch;
  Img.Image = std::move(*CubinOrErr);
  SmallString<0> ImageBytes = object::OffloadBinary::write(Img);
  Bytes.append(ImageBytes.begin(), ImageBytes.end());
  return true;
}

// Build one host-plugin shared object containing all target kernels.
static bool Emit_OpenMP_Host_Image(Module *M, ArrayRef<OMPRegion> Regions,
                                   SmallVectorImpl<char> &Bytes) {
  LLVMContext &Ctx = M->getContext();
  Type *Ptr = PointerType::getUnqual(Ctx);
  Type *Void = Type::getVoidTy(Ctx);
  ValueToValueMapTy VMap;
  std::unique_ptr<Module> DM = CloneModule(*M, VMap);
  DM->setModuleIdentifier("gnat.omp.device");
  DM->setTargetTriple(Triple(StringRef("x86_64-pc-linux-gnu")));
  DM->setDataLayout(M->getDataLayout());
  for (const char *Name : {"llvm.global_ctors", "llvm.used",
                           "llvm.compiler.used"})
    if (GlobalVariable *G = DM->getNamedGlobal(Name))
      G->eraseFromParent();
  if (NamedMDNode *N = DM->getNamedMetadata("llvm.offloading.symbols"))
    DM->eraseNamedMetadata(N);

  SmallVector<Function *, 4> Kernels;
  for (const OMPRegion &R : Regions) {
    Function *DE = DM->getFunction(R.EName);
    if (!DE)
      continue;
    DE->setLinkage(GlobalValue::InternalLinkage);
    for (const char *Name : {"gnat.omp.thread_low", "gnat.omp.thread_high"}) {
      Function *F = DM->getFunction(Name);
      if (!F)
        continue;
      bool High = StringRef(Name).ends_with("high");
      F->deleteBody();
      IRBuilder<> B(BasicBlock::Create(Ctx, "entry", F));
      B.CreateRet(High ? F->getArg(1) : F->getArg(0));
    }
    Function *Source = M->getFunction(R.EName);
    if (!Source)
      continue;
    FunctionType *EFT = Source->getFunctionType();
    SmallVector<Type *, 8> KParams(1 + EFT->getNumParams(), Ptr);
    Function *K = Function::Create(FunctionType::get(Void, KParams, false),
                                   GlobalValue::ExternalLinkage,
                                   R.KernelName, DM.get());
    IRBuilder<> KB(BasicBlock::Create(Ctx, "entry", K));
    SmallVector<Value *, 8> Fwd;
    for (unsigned I = 0; I < EFT->getNumParams(); ++I) {
      Type *PT = EFT->getParamType(I);
      Value *A = K->getArg(I + 1);
      Fwd.push_back(PT->isPointerTy() ? A : KB.CreateLoad(PT, A));
    }
    KB.CreateCall(DE, Fwd);
    KB.CreateRetVoid();
    Kernels.push_back(K);
  }

  SmallPtrSet<Function *, 32> Live;
  SmallVector<Function *, 32> Work(Kernels.begin(), Kernels.end());
  while (!Work.empty()) {
    Function *F = Work.pop_back_val();
    if (!Live.insert(F).second)
      continue;
    for (BasicBlock &BB : *F)
      for (Instruction &I : BB)
        if (auto *CB = dyn_cast<CallBase>(&I))
          if (Function *Callee = CB->getCalledFunction())
            Work.push_back(Callee);
  }
  for (Function &F : llvm::make_early_inc_range(*DM))
    if (!F.isDeclaration() && !Live.count(&F))
      F.eraseFromParent();
  for (GlobalVariable &G : llvm::make_early_inc_range(DM->globals()))
    if (!G.isDeclaration() && G.hasLocalLinkage() && G.use_empty())
      G.eraseFromParent();

  Triple TT(StringRef("x86_64-pc-linux-gnu"));
  std::string Err;
  const Target *T = TargetRegistry::lookupTarget(TT, Err);
  if (!T)
    return false;
  llvm::TargetOptions Opt;
  std::optional<Reloc::Model> RM(Reloc::PIC_);
  std::unique_ptr<TargetMachine> TM(
      T->createTargetMachine(TT, "generic", "", Opt, RM));
  if (!TM)
    return false;
  SmallVector<char, 0> Obj;
  raw_svector_ostream OS(Obj);
  legacy::PassManager PM;
  if (TM->addPassesToEmitFile(PM, OS, nullptr, CodeGenFileType::ObjectFile))
    return false;
  PM.run(*DM);

  SmallString<128> ObjPath;
  int FD = -1;
  if (sys::fs::createTemporaryFile("gnat-omp-dev", "o", FD, ObjPath))
    return false;
  {
    raw_fd_ostream OF(FD, true);
    OF.write(Obj.data(), Obj.size());
  }
  SmallString<128> SoPath(ObjPath);
  SoPath += ".so";
  auto ClangOrErr = sys::findProgramByName("clang");
  if (!ClangOrErr)
    ClangOrErr = sys::findProgramByName("clang-21");
  if (!ClangOrErr) {
    sys::fs::remove(ObjPath);
    return false;
  }
  std::string ClangPath = *ClangOrErr;
  SmallVector<StringRef, 8> LinkArgs = {ClangPath, "-shared", "-nostdlib",
                                        "-o", SoPath.str(), ObjPath.str()};
  std::string ExecErr;
  int RC = sys::ExecuteAndWait(ClangPath, LinkArgs, std::nullopt, {}, 0, 0,
                               &ExecErr);
  if (RC != 0) {
    sys::fs::remove(ObjPath);
    return false;
  }
  auto SoOrErr = MemoryBuffer::getFile(SoPath.str());
  if (!SoOrErr) {
    sys::fs::remove(ObjPath);
    return false;
  }
  std::unique_ptr<MemoryBuffer> SoBuf = std::move(*SoOrErr);
  object::OffloadBinary::OffloadingImage Img;
  Img.TheImageKind = object::IMG_Object;
  Img.TheOffloadKind = object::OFK_OpenMP;
  Img.Flags = 0;
  Img.StringData["triple"] = "x86_64-pc-linux-gnu";
  Img.StringData["arch"] = "x86_64";
  Img.Image = std::move(SoBuf);
  SmallString<0> ImageBytes = object::OffloadBinary::write(Img);
  sys::fs::remove(ObjPath);
  sys::fs::remove(SoPath);
  Bytes.append(ImageBytes.begin(), ImageBytes.end());
  return true;
}

// Called once when the module is complete: one descriptor, one image per
// device, and all kernels present in every image.
extern "C" void Finalize_OpenMP_Images(Module *M) {
  if (Pending_OMP_Regions.empty())
    return;
  Type *Ptr = PointerType::getUnqual(M->getContext());
  // Only advertise kernels that will actually exist in the emitted images.
  // A missing/renamed outlined function would otherwise produce an offload
  // entry whose symbol cannot be loaded at runtime.
  SmallVector<OMPRegion, 4> Regions;
  for (const OMPRegion &R : Pending_OMP_Regions) {
    Function *F = M->getFunction(R.EName);
    if (!F || R.NArgs == 0 ||
        F->getFunctionType()->getNumParams() != R.NArgs)
      continue;
    Regions.push_back(R);
  }
  Pending_OMP_Regions.clear();
  if (Regions.empty())
    return;

  SmallString<0> HostBytes, NVPTXBytes;
  bool HaveHost = Emit_OpenMP_Host_Image(M, Regions, HostBytes);
  bool HaveNVPTX = Emit_OpenMP_NVPTX_Image(M, Regions, NVPTXBytes);
  if (!HaveHost && !HaveNVPTX)
    return;
  auto EntriesB = offloading::getOffloadEntryArray(*M, "omp_offloading_entries");
  offloading::emitOffloadingEntry(*M, object::OFK_OpenMP,
                                  ConstantPointerNull::get(cast<PointerType>(Ptr)),
                                  "", 0, 0x10, 0x008, nullptr,
                                  "omp_offloading_entries");
  for (const OMPRegion &R : Regions)
    offloading::emitOffloadingEntry(*M, object::OFK_OpenMP, R.RegionId,
                                    R.KernelName, 0, 0, 0, nullptr,
                                    "omp_offloading_entries");
  SmallVector<ArrayRef<char>, 2> Images;
  if (HaveHost)
    Images.push_back(ArrayRef<char>(HostBytes.data(), HostBytes.size()));
  if (HaveNVPTX)
    Images.push_back(ArrayRef<char>(NVPTXBytes.data(), NVPTXBytes.size()));
  if (Error E = offloading::wrapOpenMPBinaries(*M, Images, EntriesB))
    consumeError(std::move(E));
}
Constant *Get_OpenMP_Ident(Module *M) {
  if (GlobalVariable *G = M->getNamedGlobal("gnat.omp.ident"))
    return G;

  LLVMContext &Ctx = M->getContext();
  Type *I32 = Type::getInt32Ty(Ctx);
  Type *Ptr = PointerType::getUnqual(Ctx);
  StructType *IdentTy = StructType::get(I32, I32, I32, I32, Ptr);

  Constant *Src =
      ConstantDataArray::getString(Ctx, "gnat-openmp", /*AddNull=*/true);
  auto *SrcGV = new GlobalVariable(*M, Src->getType(), true,
                                   GlobalValue::InternalLinkage, Src,
                                   "gnat.omp.source");
  Constant *SrcPtr = ConstantExpr::getBitCast(SrcGV, Ptr);
  Constant *Zero = ConstantInt::get(I32, 0);
  Constant *Init =
      ConstantStruct::get(IdentTy, {Zero, Zero, Zero, Zero, SrcPtr});
  auto *GV = new GlobalVariable(*M, IdentTy, true, GlobalValue::InternalLinkage,
                                Init, "gnat.omp.ident");
  return GV;
}

// Find the block of F that is terminated by a void return.
BasicBlock *Find_Return_Block(Function *F) {
  BasicBlock *Result = nullptr;
  for (BasicBlock &BB : *F) {
    if (isa<ReturnInst>(BB.getTerminator()) && BB.getTerminator()->getNumSuccessors() == 0) {
      if (Result)
        return nullptr;
      Result = &BB;
    }
  }
  return Result;
}

} // namespace

// Outline the loop headed by Header into a libomp microtask and replace the
// loop with a call to __kmpc_fork_call.  Returns 1 on success; on failure the
// loop keeps its sequential form (or remains a plain call if extraction
// already happened, which is still correct).
extern "C" unsigned Outline_Parallel_For(LLVMValueRef Header_Ref,
                                    unsigned Num_Threads,
                                    unsigned Reversed,
                                    unsigned Is_Target) {
  auto *Header = dyn_cast<BasicBlock>(unwrap(Header_Ref));
  if (!Header)
    return 0;
  Function *F = Header->getParent();
  Module *M = F->getParent();

  DominatorTree DT(*F);
  // Use an owning pointer so the analysis can be rebuilt from scratch after
  // splitting the entry block.  Calling LoopInfo::analyze() on a live,
  // already-populated analysis leaks/duplicates Loop objects and crashes in
  // ~LoopInfo on scope exit (observed as a glibc "double free").
  std::unique_ptr<LoopInfo> LI(new LoopInfo(DT));
  Loop *L = LI->getLoopFor(Header);
  if (!L || L->getHeader() != Header)
    return 0;
  BasicBlock *Pre = L->getLoopPreheader();
  if (!Pre)
    return 0;

  // CodeExtractor cannot outline the function entry block.  When the
  // parallel loop is the first statement, its preheader *is* the entry block,
  // so split it at the loop-variable initialization and outline the tail.
  if (Pre == &F->getEntryBlock()) {
    Instruction *SplitAt = nullptr;
    for (Instruction &I : *Pre)
      if (isa<StoreInst>(&I))
        SplitAt = &I;
    if (!SplitAt)
      return 0;
    Pre->splitBasicBlock(SplitAt, "omp.preheader");
    DT.recalculate(*F);
    LI.reset(new LoopInfo(DT));
    L = LI->getLoopFor(Header);
    if (!L || L->getHeader() != Header)
      return 0;
    Pre = L->getLoopPreheader();
    if (!Pre)
      return 0;
  }

  SmallVector<BasicBlock *, 32> Blocks;
  Blocks.push_back(Pre);
  for (BasicBlock *BB : L->blocks())
    Blocks.push_back(BB);

  CodeExtractor CE(Blocks, &DT);
  if (!CE.isEligible())
    return 0;

  // Bail out before extracting if the region writes values used after it;
  // forwarding those through a parallel region would be incorrect.
  SetVector<Value *> Inputs, Outputs, Allocas;
  CE.findInputsOutputs(Inputs, Outputs, Allocas);
  if (!Outputs.empty())
    return 0;

  CodeExtractorAnalysisCache CEAC(*F);
  Function *E = CE.extractCodeRegion(CEAC, Inputs, Outputs);
  if (!E || !Outputs.empty())
    return 0;

  // Locate the call to the outlined function in the caller.
  CallInst *HostCall = nullptr;
  for (BasicBlock &BB : *F)
    for (Instruction &I : BB)
      if (auto *C = dyn_cast<CallInst>(&I))
        if (C->getCalledFunction() == E)
          HostCall = C;
  if (!HostCall)
    return 0;

  // Inspect the outlined loop.
  DominatorTree DT2(*E);
  LoopInfo LI2(DT2);
  if (LI2.empty())
    return 0;
  Loop *OL = *LI2.begin();
  BasicBlock *OPre = OL->getLoopPreheader();
  BasicBlock *OLatch = OL->getLoopLatch();
  if (!OPre || !OLatch)
    return 0;
  auto *LatchBr = dyn_cast<BranchInst>(OLatch->getTerminator());
  if (!LatchBr || !LatchBr->isConditional())
    return 0;
  auto *Cmp = dyn_cast<ICmpInst>(LatchBr->getCondition());
  if (!Cmp)
    return 0;

  // The loop start is the value stored by the last store in the preheader;
  // the loop end is the non-induction operand of the latch comparison.
  StoreInst *InitStore = nullptr;
  for (Instruction &I : *OPre)
    if (auto *SI = dyn_cast<StoreInst>(&I))
      InitStore = SI;
  if (!InitStore)
    return 0;
  Value *Start = InitStore->getValueOperand();
  Value *Last = Cmp->getOperand(1);
  if (Start->getType() != Last->getType())
    return 0;

  Instruction *Term = OPre->getTerminator();

  // Any pointer input that the extracted body stores to *directly* is a
  // thread-private variable in the OpenMP sense -- typically a loop counter
  // of a loop nested inside the parallel loop.  All invocations of the
  // microtask receive the same argument pointers, so without private copies
  // the threads race on the host's allocas (corrupted loop counters,
  // out-of-bounds accesses, STORAGE_ERROR).  Writes *through* a pointer
  // (array elements) are left alone: those identify shared storage.
  DenseMap<Argument *, Type *> StoredArgTypes;
  for (BasicBlock &BB : *E)
    for (Instruction &I : BB)
      if (auto *SI = dyn_cast<StoreInst>(&I))
        if (auto *Arg = dyn_cast<Argument>(SI->getPointerOperand()))
          if (Arg->getParent() == E)
            StoredArgTypes[Arg] = SI->getValueOperand()->getType();

  for (auto &KV : StoredArgTypes) {
    Argument *Arg = KV.first;
    IRBuilder<> AB(&*E->getEntryBlock().getFirstInsertionPt());
    AllocaInst *Private =
        AB.CreateAlloca(KV.second, nullptr, "omp.private");
    // Copy in the caller's value before rebinding the uses.  Nested loop
    // counters overwrite it in their initialization; other variables keep
    // their incoming value.  The copy-in load must keep reading the original
    // argument, so restore its operand after replaceAllUsesWith.
    LoadInst *Copy = AB.CreateLoad(KV.second, Arg);
    Arg->replaceAllUsesWith(Private);
    Copy->setOperand(0, Arg);
    AB.CreateStore(Copy, Private);
  }

  // Compute this thread's subrange before the loop-variable initialization,
  // which itself uses the lower bound.
  Value *NumericLo = Reversed ? Last : Start;
  Value *NumericHi = Reversed ? Start : Last;
  Type *Ty = Start->getType();

  // For forward target loops use a cyclic (strided) split: consecutive
  // threads then access consecutive elements, which is what makes warp lanes
  // coalesce on NVPTX.  This requires changing the loop increment from 1 to
  // the team size; find that increment first and fall back to the contiguous
  // split if the loop shape is not recognized.
  BinaryOperator *LoopStep = nullptr;
  bool UseStride = Is_Target && !Reversed && OLatch;
  if (UseStride)
    for (Instruction &I : *OLatch)
      if (auto *SI = dyn_cast<StoreInst>(&I))
        if (SI->getPointerOperand() == InitStore->getPointerOperand())
          if (auto *AI = dyn_cast<BinaryOperator>(SI->getValueOperand()))
            if (AI->getOpcode() == Instruction::Add)
              if (auto *CI = dyn_cast<ConstantInt>(AI->getOperand(1)))
              if (CI->isOne()) {
                LoopStep = AI;
                break;
              }
  if (!LoopStep)
    UseStride = false;

  Value *NumStep = nullptr;
  if (UseStride) {
    IRBuilder<> NB(InitStore);
    FunctionCallee NumF = M->getOrInsertFunction(
        "omp_get_num_threads", Type::getInt32Ty(M->getContext()));
    Value *Num32 = NB.CreateCall(NumF);
    Value *Num64 = NB.CreateSExt(Num32, Type::getInt64Ty(M->getContext()));
    Value *Positive = NB.CreateICmpSGT(
        Num64, ConstantInt::get(Type::getInt64Ty(M->getContext()), 0));
    Value *Num = NB.CreateSelect(
        Positive, Num64,
        ConstantInt::get(Type::getInt64Ty(M->getContext()), 1));
    NumStep = NB.CreateSExtOrTrunc(Num, Ty);
    LoopStep->setOperand(1, NumStep);
  }

  Value *ThreadLo =
      Range_Call(M, false, NumericLo, NumericHi, Ty, InitStore, UseStride);
  Value *ThreadHi =
      Range_Call(M, true, NumericLo, NumericHi, Ty, InitStore, UseStride);

  Value *InitVal = Reversed ? ThreadHi : ThreadLo;
  Value *LastVal = Reversed ? ThreadLo : ThreadHi;

  // Skip the loop for threads whose subrange is empty.  The loop is a
  // do-while, so this guard is required, not just an optimization.
  BasicBlock *RetBB = Find_Return_Block(E);
  auto *TermBr = dyn_cast<BranchInst>(Term);
  if (RetBB && TermBr && TermBr->isUnconditional()
      && TermBr->getSuccessor(0) == OL->getHeader()) {
    IRBuilder<> GB(Term);
    Value *NonEmpty = GB.CreateICmpSLE(ThreadLo, ThreadHi);
    GB.CreateCondBr(NonEmpty, OL->getHeader(), RetBB);
    Term->eraseFromParent();
  } else {
    // No usable guard: clamp the start so an empty thread runs at most one
    // (idempotent) iteration instead of looping forever.
    IRBuilder<> CB(Term);
    InitVal = CB.CreateSelect(CB.CreateICmpSLE(ThreadLo, ThreadHi),
                              InitVal, LastVal);
  }

  // Rebind the loop to this thread's subrange.
  InitStore->setOperand(0, InitVal);
  Cmp->setOperand(1, LastVal);

  // Build the microtask wrapper: (global_tid, bound_tid, inputs...).
  LLVMContext &Ctx = M->getContext();
  Type *I32 = Type::getInt32Ty(Ctx);
  Type *Ptr = PointerType::getUnqual(Ctx);
  Type *Void = Type::getVoidTy(Ctx);

  SmallVector<Type *, 8> WParams = {Ptr, Ptr};
  for (Value *Arg : HostCall->args())
    WParams.push_back(Arg->getType());
  FunctionType *WFT = FunctionType::get(Void, WParams, false);
  Function *W = Function::Create(WFT, GlobalValue::InternalLinkage,
                                 F->getName() + ".omp_outlined", M);
  BasicBlock *WEntry = BasicBlock::Create(Ctx, "entry", W);
  IRBuilder<> WB(WEntry);
  SmallVector<Value *, 8> Fwd;
  for (unsigned I = 0; I < HostCall->arg_size(); ++I)
    Fwd.push_back(W->getArg(I + 2));
  WB.CreateCall(E, Fwd);
  WB.CreateRetVoid();

  // __kmpc_fork_call(&ident, argc, wrapper, args...)
  FunctionCallee Fork = M->getOrInsertFunction(
      "__kmpc_fork_call", FunctionType::get(Void, {Ptr, I32, Ptr}, true));
  Constant *Ident = Get_OpenMP_Ident(M);

  SmallVector<Value *, 8> ForkArgs = {
      Ident, ConstantInt::get(I32, HostCall->arg_size()), W};
  for (Value *Arg : HostCall->args())
    ForkArgs.push_back(Arg);

  auto add_thread_push = [&](IRBuilder<> &B) {
    if (Num_Threads > 0) {
      FunctionCallee GTid = M->getOrInsertFunction(
          "__kmpc_global_thread_num", FunctionType::get(I32, {Ptr}, false));
      Value *Tid = B.CreateCall(GTid, {Ident});
      FunctionCallee Push = M->getOrInsertFunction(
          "__kmpc_push_num_threads",
          FunctionType::get(Void, {Ptr, I32, I32}, false));
      B.CreateCall(Push, {Ident, Tid, ConstantInt::get(I32, Num_Threads)});
    }
  };

  if (!Is_Target) {
    IRBuilder<> HB(HostCall);
    add_thread_push(HB);
    HB.CreateCall(Fork, ForkArgs);
    HostCall->eraseFromParent();
    return 1;
  }

  // Target region: dispatch through libomptarget's __tgt_target_kernel and
  // fall back to the host team when the runtime reports no device image.
  Constant *TgtIdent = Get_OpenMP_Target_Ident(M);
  Type *I64 = Type::getInt64Ty(Ctx);
  Type *I8 = Type::getInt8Ty(Ctx);

  static unsigned Kernel_Count = 0;
  std::string Suffix = std::to_string(Kernel_Count++);
  auto *RegionId = new GlobalVariable(
      *M, I8, true, GlobalValue::InternalLinkage,
      ConstantInt::get(I8, 0), "gnat.omp.region.id." + Suffix);
  std::string KernelName = "gnat_omp_kernel_" + Suffix;

  unsigned NArgs = HostCall->arg_size();
  BasicBlock *Orig = HostCall->getParent();
  BasicBlock *Cont = Orig->splitBasicBlock(HostCall, "omp.target.cont");
  Instruction *OldBr = Orig->getTerminator();

  IRBuilder<> B(OldBr);
  unsigned ASize = NArgs ? NArgs : 1;
  Type *PtrArr = ArrayType::get(Ptr, ASize);
  Type *I64Arr = ArrayType::get(I64, ASize);
  AllocaInst *Base = B.CreateAlloca(PtrArr, nullptr, "omp.base");
  AllocaInst *Sizes = B.CreateAlloca(I64Arr, nullptr, "omp.sizes");
  AllocaInst *MapT = B.CreateAlloca(I64Arr, nullptr, "omp.maptypes");
  Constant *Zero64 = ConstantInt::get(I64, 0);
  SmallVector<Value *, 8> MappedValues;
  SmallVector<Value *, 8> MappedSizes;
  bool SizesKnown = true;
  for (Value *Arg : HostCall->args()) {
    Value *BaseVal = Arg;
    Value *Size;
    if (Arg->getType()->isPointerTy()) {
      // Arrays and scalar addresses: map the whole object (VLAs included).
      Size = Build_Mapped_Size(B, Arg, M->getDataLayout(), SizesKnown);
    } else {
      // By-value args are firstprivate on the device: map a 4-byte slot
      // holding the value instead of treating the value as an address.
      AllocaInst *Slot = B.CreateAlloca(Arg->getType(), nullptr, "omp.scalar");
      B.CreateStore(Arg, Slot);
      BaseVal = Slot;
      Size = ConstantInt::get(
          I64, M->getDataLayout().getTypeAllocSize(Arg->getType()));
    }
    MappedValues.push_back(BaseVal);
    MappedSizes.push_back(Size);
  }

  for (unsigned Index = 0; Index < NArgs; ++Index) {
    Value *BP = B.CreateInBoundsGEP(PtrArr, Base,
                                    {B.getInt32(0), B.getInt32(Index)});
    B.CreateStore(MappedValues[Index], BP);
    Value *SP = B.CreateInBoundsGEP(I64Arr, Sizes,
                                    {B.getInt32(0), B.getInt32(Index)});
    B.CreateStore(SizesKnown ? MappedSizes[Index] : Zero64, SP);
    Value *MP = B.CreateInBoundsGEP(I64Arr, MapT,
                                    {B.getInt32(0), B.getInt32(Index)});
    B.CreateStore(ConstantInt::get(I64, SizesKnown ? 35 : 0), MP);
  }

  // Without a known extent for every mapped object there is no safe device
  // image.  Leave the region unregistered so __tgt_target_kernel reports a
  // miss and the correct host fallback below executes.
  if (SizesKnown && NArgs > 0)
    Register_OpenMP_Target(M, E, RegionId, KernelName.c_str(), NArgs);

  ArrayType *Arr3 = ArrayType::get(I32, 3);
  StructType *ArgTy =
      StructType::get(Ctx, {I32, I32, Ptr, Ptr, Ptr, Ptr, Ptr, Ptr, I64, I64,
                            Arr3, Arr3, I32});
  AllocaInst *Args = B.CreateAlloca(ArgTy, nullptr, "omp.kernel.args");
  auto field_ptr = [&](unsigned I) {
    return B.CreateStructGEP(ArgTy, Args, I);
  };
  B.CreateStore(ConstantInt::get(I32, 3), field_ptr(0));
  B.CreateStore(ConstantInt::get(I32, NArgs), field_ptr(1));
  Value *BasePtr = B.CreateBitCast(Base, Ptr);
  B.CreateStore(BasePtr, field_ptr(2));
  B.CreateStore(BasePtr, field_ptr(3));
  B.CreateStore(Sizes, field_ptr(4));
  B.CreateStore(MapT, field_ptr(5));
  Value *Null = ConstantPointerNull::get(cast<PointerType>(Ptr));
  B.CreateStore(Null, field_ptr(6));
  B.CreateStore(Null, field_ptr(7));
  B.CreateStore(Zero64, field_ptr(8));
  B.CreateStore(Zero64, field_ptr(9));
  B.CreateStore(ConstantInt::get(I32, 0), field_ptr(12));

  Value *MaxSize = nullptr;
  for (Value *Sz : MappedSizes)
    MaxSize = MaxSize ? B.CreateSelect(B.CreateICmpSGT(Sz, MaxSize), Sz, MaxSize)
                      : Sz;
  if (!MaxSize)
    MaxSize = ConstantInt::get(I64, 2048);
  Value *Elems = B.CreateUDiv(MaxSize, ConstantInt::get(I64, 8));
  Value *Teams64 = B.CreateUDiv(B.CreateAdd(Elems, ConstantInt::get(I64, 255)),
                                ConstantInt::get(I64, 256));
  Value *Teams = B.CreateTrunc(Teams64, I32);
  // Large flat arrays (the 1-D stencil) need a grid proportional to the
  // element count; smaller mapped objects are faster with a modest fixed
  // grid (the nbody particle array and 2-D stencil case).
  Value *Large = B.CreateICmpSGE(MaxSize, ConstantInt::get(I64, 4u * 1024 * 1024));
  Value *FixedTeams = ConstantInt::get(I32, 64);
  Teams = B.CreateSelect(Large, Teams, FixedTeams);
  B.CreateStore(ConstantArray::get(
                    Arr3, {ConstantInt::get(I32, 1), ConstantInt::get(I32, 1),
                           ConstantInt::get(I32, 1)}),
                field_ptr(10));
  B.CreateStore(Teams,
                B.CreateInBoundsGEP(Arr3, field_ptr(10),
                                    {B.getInt32(0), B.getInt32(0)}));
  B.CreateStore(ConstantArray::get(
                    Arr3, {ConstantInt::get(I32, 256), ConstantInt::get(I32, 1),
                           ConstantInt::get(I32, 1)}),
                field_ptr(11));
  B.CreateStore(ConstantInt::get(I32, 0), field_ptr(12));

  FunctionCallee TgtKernel = M->getOrInsertFunction(
      "__tgt_target_kernel",
      FunctionType::get(I32, {Ptr, I64, I32, I32, Ptr, Ptr}, false));
  // The runtime takes num_teams/thread_limit from these call arguments and
  // overwrites the corresponding fields of KernelArgs, so they must match the
  // grid the device kernel expects.
  Value *Ret = B.CreateCall(
      TgtKernel, {TgtIdent, ConstantInt::get(I64, -1),
                  Teams, ConstantInt::get(I32, 256),
                  ConstantExpr::getBitCast(RegionId, Ptr), Args});
  Value *Fallback = B.CreateICmpNE(Ret, ConstantInt::get(I32, 0));
  BasicBlock *FB = BasicBlock::Create(Ctx, "omp.target.fallback", F);
  B.CreateCondBr(Fallback, FB, Cont);
  OldBr->eraseFromParent();

  IRBuilder<> FBB(FB);
  add_thread_push(FBB);
  FBB.CreateCall(Fork, ForkArgs);
  FBB.CreateBr(Cont);

  HostCall->eraseFromParent();

  return 1;
}
