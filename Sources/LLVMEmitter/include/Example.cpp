#include <FrontEnd-Swift.h>
#include "Example.hpp"
#include <llvm/IR/LLVMContext.h>
#include <llvm/ADT/Twine.h>

int Example::sum() const { return a + b; }

int exampleFun(int a, int b)
{
  auto ctx = llvm::LLVMContext();

  FrontEnd::Program program = FrontEnd::Program::init();

  return a + b;
}
