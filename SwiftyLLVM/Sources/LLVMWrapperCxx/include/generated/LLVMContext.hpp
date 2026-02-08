// Auto-generated wrapper for ::llvm::LLVMContext
#pragma once
#include <memory>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Type.h>
#include <llvm/IR/Verifier.h>
#include <llvm/IR/DiagnosticInfo.h>
#include <llvm/IR/DiagnosticHandler.h>
#include <llvm/IR/LLVMRemarkStreamer.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Remarks/RemarkStreamer.h>

namespace LLVM {

class LLVMContext {
private:
  std::unique_ptr<::llvm::LLVMContext> wrapped_;

public:
  // Constructor
  LLVMContext() : wrapped_(std::make_unique<::llvm::LLVMContext>()) {}
  
  // Move constructor
  LLVMContext(LLVMContext&&) = default;
  
  // Move assignment
  LLVMContext& operator=(LLVMContext&&) = default;
  
  // Destructor
  ~LLVMContext() = default;
  
  // Deleted copy operations
  LLVMContext(const LLVMContext&) = delete;
  LLVMContext& operator=(const LLVMContext&) = delete;
  
  // Access to wrapped object
  ::llvm::LLVMContext& asLLVM() { return *wrapped_; }
  const ::llvm::LLVMContext& asLLVM() const { return *wrapped_; }

  using YieldCallbackTy = ::llvm::LLVMContext::YieldCallbackTy;

  // Accessors for field 'pImpl'
  ::llvm::LLVMContextImpl *const getPImpl() const { return wrapped_->pImpl; }
  ::llvm::LLVMContextImpl *const getPImpl() { return wrapped_->pImpl; }

  // Forwarding method 'operator='
  ::llvm::LLVMContext & operator=(const ::llvm::LLVMContext & arg0) const = delete;

  /// getMDKindID - Return a unique non-zero ID for the specified metadata kind.
  /// This ID is uniqued across modules in the current LLVMContext.
  unsigned int getMDKindID(::llvm::StringRef Name) const {
    return wrapped_->getMDKindID(std::forward<::llvm::StringRef>(Name));
  }

  /// getMDKindNames - Populate client supplied SmallVector with the name for
  /// custom metadata IDs registered in this LLVMContext.
  void getMDKindNames(::llvm::SmallVectorImpl< ::llvm::StringRef> & Result) const {
    wrapped_->getMDKindNames(std::forward<::llvm::SmallVectorImpl< ::llvm::StringRef> &>(Result));
  }

  /// getOperandBundleTags - Populate client supplied SmallVector with the
  /// bundle tags registered in this LLVMContext.  The bundle tags are ordered
  /// by increasing bundle IDs.
  /// \see LLVMContext::getOperandBundleTagID
  void getOperandBundleTags(::llvm::SmallVectorImpl< ::llvm::StringRef> & Result) const {
    wrapped_->getOperandBundleTags(std::forward<::llvm::SmallVectorImpl< ::llvm::StringRef> &>(Result));
  }

  /// getOrInsertBundleTag - Returns the Tag to use for an operand bundle of
  /// name TagName.
  ::llvm::StringMapEntry< ::uint32_t> * getOrInsertBundleTag(::llvm::StringRef TagName) const {
    return wrapped_->getOrInsertBundleTag(std::forward<::llvm::StringRef>(TagName));
  }

  /// getOperandBundleTagID - Maps a bundle tag to an integer ID.  Every bundle
  /// tag registered with an LLVMContext has an unique ID.
  ::uint32_t getOperandBundleTagID(::llvm::StringRef Tag) const {
    return wrapped_->getOperandBundleTagID(std::forward<::llvm::StringRef>(Tag));
  }

  /// getOrInsertSyncScopeID - Maps synchronization scope name to
  /// synchronization scope ID.  Every synchronization scope registered with
  /// LLVMContext has unique ID except pre-defined ones.
  ::llvm::SyncScope::ID getOrInsertSyncScopeID(::llvm::StringRef SSN) {
    return wrapped_->getOrInsertSyncScopeID(std::forward<::llvm::StringRef>(SSN));
  }

  /// getSyncScopeNames - Populates client supplied SmallVector with
  /// synchronization scope names registered with LLVMContext.  Synchronization
  /// scope names are ordered by increasing synchronization scope IDs.
  void getSyncScopeNames(::llvm::SmallVectorImpl< ::llvm::StringRef> & SSNs) const {
    wrapped_->getSyncScopeNames(std::forward<::llvm::SmallVectorImpl< ::llvm::StringRef> &>(SSNs));
  }

  /// getSyncScopeName - Returns the name of a SyncScope::ID
  /// registered with LLVMContext, if any.
  ::std::optional< ::llvm::StringRef> getSyncScopeName(::llvm::SyncScope::ID Id) const {
    return wrapped_->getSyncScopeName(std::forward<::llvm::SyncScope::ID>(Id));
  }

  /// Define the GC for a function
  void setGC(const ::llvm::Function & Fn, ::std::string GCName) const {
    wrapped_->setGC(std::forward<const ::llvm::Function &>(Fn), std::forward<::std::string>(GCName));
  }

  /// Return the GC for a function
  const ::std::string & getGC(const ::llvm::Function & Fn) const {
    return wrapped_->getGC(std::forward<const ::llvm::Function &>(Fn));
  }

  /// Remove the GC for a function
  void deleteGC(const ::llvm::Function & Fn) const {
    wrapped_->deleteGC(std::forward<const ::llvm::Function &>(Fn));
  }

  /// Return true if the Context runtime configuration is set to discard all
  /// value names. When true, only GlobalValue names will be available in the
  /// IR.
  bool shouldDiscardValueNames() const {
    return wrapped_->shouldDiscardValueNames();
  }

  /// Set the Context runtime configuration to discard all value name (but
  /// GlobalValue). Clients can use this flag to save memory and runtime,
  /// especially in release mode.
  void setDiscardValueNames(bool Discard) {
    wrapped_->setDiscardValueNames(std::forward<bool>(Discard));
  }

  /// Whether there is a string map for uniquing debug info
  /// identifiers across the context.  Off by default.
  bool isODRUniquingDebugTypes() const {
    return wrapped_->isODRUniquingDebugTypes();
  }

  // Forwarding method 'enableDebugTypeODRUniquing'
  void enableDebugTypeODRUniquing() {
    wrapped_->enableDebugTypeODRUniquing();
  }

  // Forwarding method 'disableDebugTypeODRUniquing'
  void disableDebugTypeODRUniquing() {
    wrapped_->disableDebugTypeODRUniquing();
  }

  /// generateMachineFunctionNum - Get a unique number for MachineFunction
  /// that associated with the given Function.
  unsigned int generateMachineFunctionNum(::llvm::Function & arg0) {
    return wrapped_->generateMachineFunctionNum(std::forward<::llvm::Function &>(arg0));
  }

  /// setDiagnosticHandlerCallBack - This method sets a handler call back
  /// that is invoked when the backend needs to report anything to the user.
  /// The first argument is a function pointer and the second is a context pointer
  /// that gets passed into the DiagHandler.  The third argument should be set to
  /// true if the handler only expects enabled diagnostics.
  ///
  /// LLVMContext doesn't take ownership or interpret either of these
  /// pointers.
  void setDiagnosticHandlerCallBack(::llvm::DiagnosticHandler::DiagnosticHandlerTy DiagHandler, void * DiagContext, bool RespectFilters) {
    wrapped_->setDiagnosticHandlerCallBack(std::forward<::llvm::DiagnosticHandler::DiagnosticHandlerTy>(DiagHandler), std::forward<void *>(DiagContext), std::forward<bool>(RespectFilters));
  }

  /// setDiagnosticHandler - This method sets unique_ptr to object of
  /// DiagnosticHandler to provide custom diagnostic handling. The first
  /// argument is unique_ptr of object of type DiagnosticHandler or a derived
  /// of that. The second argument should be set to true if the handler only
  /// expects enabled diagnostics.
  ///
  /// Ownership of this pointer is moved to LLVMContextImpl.
  void setDiagnosticHandler(::std::unique_ptr< ::llvm::DiagnosticHandler> && DH, bool RespectFilters) {
    wrapped_->setDiagnosticHandler(std::forward<::std::unique_ptr< ::llvm::DiagnosticHandler> &&>(DH), std::forward<bool>(RespectFilters));
  }

  /// getDiagnosticHandlerCallBack - Return the diagnostic handler call back set by
  /// setDiagnosticHandlerCallBack.
  ::llvm::DiagnosticHandler::DiagnosticHandlerTy getDiagnosticHandlerCallBack() const {
    return wrapped_->getDiagnosticHandlerCallBack();
  }

  /// getDiagnosticContext - Return the diagnostic context set by
  /// setDiagnosticContext.
  void * getDiagnosticContext() const {
    return wrapped_->getDiagnosticContext();
  }

  /// getDiagHandlerPtr - Returns const raw pointer of DiagnosticHandler set by
  /// setDiagnosticHandler.
  const ::llvm::DiagnosticHandler * getDiagHandlerPtr() const {
    return wrapped_->getDiagHandlerPtr();
  }

  /// getDiagnosticHandler - transfers ownership of DiagnosticHandler unique_ptr
  /// to caller.
  ::std::unique_ptr< ::llvm::DiagnosticHandler> getDiagnosticHandler() {
    return wrapped_->getDiagnosticHandler();
  }

  /// Return if a code hotness metric should be included in optimization
  /// diagnostics.
  bool getDiagnosticsHotnessRequested() const {
    return wrapped_->getDiagnosticsHotnessRequested();
  }

  /// Set if a code hotness metric should be included in optimization
  /// diagnostics.
  void setDiagnosticsHotnessRequested(bool Requested) {
    wrapped_->setDiagnosticsHotnessRequested(std::forward<bool>(Requested));
  }

  // Forwarding method 'getMisExpectWarningRequested'
  bool getMisExpectWarningRequested() const {
    return wrapped_->getMisExpectWarningRequested();
  }

  // Forwarding method 'setMisExpectWarningRequested'
  void setMisExpectWarningRequested(bool Requested) {
    wrapped_->setMisExpectWarningRequested(std::forward<bool>(Requested));
  }

  // Forwarding method 'setDiagnosticsMisExpectTolerance'
  void setDiagnosticsMisExpectTolerance(::std::optional< ::uint32_t> Tolerance) {
    wrapped_->setDiagnosticsMisExpectTolerance(std::forward<::std::optional< ::uint32_t>>(Tolerance));
  }

  // Forwarding method 'getDiagnosticsMisExpectTolerance'
  ::uint32_t getDiagnosticsMisExpectTolerance() const {
    return wrapped_->getDiagnosticsMisExpectTolerance();
  }

  /// Return the minimum hotness value a diagnostic would need in order
  /// to be included in optimization diagnostics.
  ///
  /// Three possible return values:
  /// 0            - threshold is disabled. Everything will be printed out.
  /// positive int - threshold is set.
  /// UINT64_MAX   - threshold is not yet set, and needs to be synced from
  ///                profile summary. Note that in case of missing profile
  ///                summary, threshold will be kept at "MAX", effectively
  ///                suppresses all remarks output.
  ::uint64_t getDiagnosticsHotnessThreshold() const {
    return wrapped_->getDiagnosticsHotnessThreshold();
  }

  /// Set the minimum hotness value a diagnostic needs in order to be
  /// included in optimization diagnostics.
  void setDiagnosticsHotnessThreshold(::std::optional< ::uint64_t> Threshold) {
    wrapped_->setDiagnosticsHotnessThreshold(std::forward<::std::optional< ::uint64_t>>(Threshold));
  }

  /// Return if hotness threshold is requested from PSI.
  bool isDiagnosticsHotnessThresholdSetFromPSI() const {
    return wrapped_->isDiagnosticsHotnessThresholdSetFromPSI();
  }

  /// The "main remark streamer" used by all the specialized remark streamers.
  /// This streamer keeps generic remark metadata in memory throughout the life
  /// of the LLVMContext. This metadata may be emitted in a section in object
  /// files depending on the format requirements.
  ///
  /// All specialized remark streamers should convert remarks to
  /// llvm::remarks::Remark and emit them through this streamer.
  ::llvm::remarks::RemarkStreamer * getMainRemarkStreamer() {
    return wrapped_->getMainRemarkStreamer();
  }

  // Forwarding method 'getMainRemarkStreamer'
  const ::llvm::remarks::RemarkStreamer * getMainRemarkStreamer() const {
    return wrapped_->getMainRemarkStreamer();
  }

  // Forwarding method 'setMainRemarkStreamer'
  void setMainRemarkStreamer(::std::unique_ptr< ::llvm::remarks::RemarkStreamer> MainRemarkStreamer) {
    wrapped_->setMainRemarkStreamer(std::forward<::std::unique_ptr< ::llvm::remarks::RemarkStreamer>>(MainRemarkStreamer));
  }

  /// The "LLVM remark streamer" used by LLVM to serialize remark diagnostics
  /// comming from IR and MIR passes.
  ///
  /// If it does not exist, diagnostics are not saved in a file but only emitted
  /// via the diagnostic handler.
  ::llvm::LLVMRemarkStreamer * getLLVMRemarkStreamer() {
    return wrapped_->getLLVMRemarkStreamer();
  }

  // Forwarding method 'getLLVMRemarkStreamer'
  const ::llvm::LLVMRemarkStreamer * getLLVMRemarkStreamer() const {
    return wrapped_->getLLVMRemarkStreamer();
  }

  // Forwarding method 'setLLVMRemarkStreamer'
  void setLLVMRemarkStreamer(::std::unique_ptr< ::llvm::LLVMRemarkStreamer> RemarkStreamer) {
    wrapped_->setLLVMRemarkStreamer(std::forward<::std::unique_ptr< ::llvm::LLVMRemarkStreamer>>(RemarkStreamer));
  }

  /// Get the prefix that should be printed in front of a diagnostic of
  ///        the given \p Severity
  const char * getDiagnosticMessagePrefix(::llvm::DiagnosticSeverity Severity) const {
    return wrapped_->getDiagnosticMessagePrefix(std::forward<::llvm::DiagnosticSeverity>(Severity));
  }

  /// Report a message to the currently installed diagnostic handler.
  ///
  /// This function returns, in particular in the case of error reporting
  /// (DI.Severity == \a DS_Error), so the caller should leave the compilation
  /// process in a self-consistent state, even though the generated code
  /// need not be correct.
  ///
  /// The diagnostic message will be implicitly prefixed with a severity keyword
  /// according to \p DI.getSeverity(), i.e., "error: " for \a DS_Error,
  /// "warning: " for \a DS_Warning, and "note: " for \a DS_Note.
  void diagnose(const ::llvm::DiagnosticInfo & DI) const {
    wrapped_->diagnose(std::forward<const ::llvm::DiagnosticInfo &>(DI));
  }

  /// Registers a yield callback with the given context.
  ///
  /// The yield callback function may be called by LLVM to transfer control back
  /// to the client that invoked the LLVM compilation. This can be used to yield
  /// control of the thread, or perform periodic work needed by the client.
  /// There is no guaranteed frequency at which callbacks must occur; in fact,
  /// the client is not guaranteed to ever receive this callback. It is at the
  /// sole discretion of LLVM to do so and only if it can guarantee that
  /// suspending the thread won't block any forward progress in other LLVM
  /// contexts in the same process.
  ///
  /// At a suspend point, the state of the current LLVM context is intentionally
  /// undefined. No assumptions about it can or should be made. Only LLVM
  /// context API calls that explicitly state that they can be used during a
  /// yield callback are allowed to be used. Any other API calls into the
  /// context are not supported until the yield callback function returns
  /// control to LLVM. Other LLVM contexts are unaffected by this restriction.
  void setYieldCallback(::llvm::LLVMContext::YieldCallbackTy Callback, void * OpaqueHandle) {
    wrapped_->setYieldCallback(std::forward<::llvm::LLVMContext::YieldCallbackTy>(Callback), std::forward<void *>(OpaqueHandle));
  }

  /// Calls the yield callback (if applicable).
  ///
  /// This transfers control of the current thread back to the client, which may
  /// suspend the current thread. Only call this method when LLVM doesn't hold
  /// any global mutex or cannot block the execution in another LLVM context.
  void yield() {
    wrapped_->yield();
  }

  /// emitError - Emit an error message to the currently installed error handler
  /// with optional location information.  This function returns, so code should
  /// be prepared to drop the erroneous construct on the floor and "not crash".
  /// The generated code need not be correct.  The error message will be
  /// implicitly prefixed with "error: " and should not end with a ".".
  void emitError(const ::llvm::Instruction * I, const ::llvm::Twine & ErrorStr) const {
    wrapped_->emitError(std::forward<const ::llvm::Instruction *>(I), std::forward<const ::llvm::Twine &>(ErrorStr));
  }

  // Forwarding method 'emitError'
  void emitError(const ::llvm::Twine & ErrorStr) const {
    wrapped_->emitError(std::forward<const ::llvm::Twine &>(ErrorStr));
  }

  /// Access the object which can disable optional passes and individual
  /// optimizations at compile time.
  ::llvm::OptPassGate & getOptPassGate() const {
    return wrapped_->getOptPassGate();
  }

  /// Set the object which can disable optional passes and individual
  /// optimizations at compile time.
  ///
  /// The lifetime of the object must be guaranteed to extend as long as the
  /// LLVMContext is used by compilation.
  void setOptPassGate(::llvm::OptPassGate & arg0) {
    wrapped_->setOptPassGate(std::forward<::llvm::OptPassGate &>(arg0));
  }

  /// Get or set the current "default" target CPU (target-cpu function
  /// attribute). The intent is that compiler frontends will set this to a value
  /// that reflects the attribute that a function would get "by default" without
  /// any specific function attributes, and compiler passes will attach the
  /// attribute to newly created functions that are not associated with a
  /// particular function, such as global initializers.
  /// Function::createWithDefaultAttr() will create functions with this
  /// attribute. This function should only be called by passes that run at
  /// compile time and not by the backend or LTO passes.
  ::llvm::StringRef getDefaultTargetCPU() {
    return wrapped_->getDefaultTargetCPU();
  }

  // Forwarding method 'setDefaultTargetCPU'
  void setDefaultTargetCPU(::llvm::StringRef CPU) {
    wrapped_->setDefaultTargetCPU(std::forward<::llvm::StringRef>(CPU));
  }

  /// Similar to {get,set}DefaultTargetCPU() but for default target-features.
  ::llvm::StringRef getDefaultTargetFeatures() {
    return wrapped_->getDefaultTargetFeatures();
  }

  // Forwarding method 'setDefaultTargetFeatures'
  void setDefaultTargetFeatures(::llvm::StringRef Features) {
    wrapped_->setDefaultTargetFeatures(std::forward<::llvm::StringRef>(Features));
  }

};

} // namespace
