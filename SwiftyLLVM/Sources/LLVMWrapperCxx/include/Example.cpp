#include "Example.hpp"
#include <llvm/IR/LLVMContext.h>
#include <llvm/ADT/Twine.h>

int Example::sum() const { return a + b; }

int exampleFun(int a, int b)
{
  auto ctx = llvm::LLVMContext();

  return a + b;
}
