# Subscript Decomposition

This document discusses subscript decomposition, which is the process `hc` uses to compile subscripts and their applications.

## Intuition

Intuitively, a subscript can be understood as a pair of functions.
The first, called *ramp*, computes a value to project.
The second, called *slide* undoes the setup made to compute that value and potentially applies changes made to the projected value back to the whole of which it is a part.
Then, applying a subscript consists of calling the ramp to obtain a value before eventually calling the slide to dispose of the projected value, after its last use.

Setting up a value to project may involve memory allocation.
One main objective of subscript decomposition is to avoid allocating such memory on the heap.
To that end, the idea is to keep the call frame ramp on the stack while the projected value is being used.
Hence, rather than returning from the ramp, one can instead pass it a closure encapsulating the uses of the value being projected.
Perhaps more simply, subscripts can be implemented as higher-order functions applying a closure to the value being projected.
This approach, however, presents two issues.
First, the lifetime of a subscript may end in different parts of the program, notwithstanding its lexical structure.
Second, projections may overlap without nesting. Both of these issues make it not obvious to determine what region of a closure covers.

One solution is to renounce keeping closures small, taking a page from continuation passing instead.
When a subscript is called, all the code dominated by that call can be wrapped into a closure passed to the subscript.
This closure, called a *plateau*, will then call the slide after the last use of the projection.
Consider the following program to illustrate:

```hylo
subscript bit(i: Int, of n: inout Int) inout -> Bool {
  let m = 1 << i
  let b = n & m != 0
  yield b
  &b = if b { b | m } else { b & ~m }
}

fun foo() {
  var x = 0b11
  inout b = &bit[1, of: &x]
  if b { &b = false ; print(x) } else { &b = true }
}
```

The lifetime of `b` in `foo` starts at the second line and ends in two different locations, making it difficult to form a closure tightly wrapped around all uses of `b`.
The following transformation could be applied instead.

```hylo
fun bit<E, F>(
  i: Int, of n: inout Int,
  plateau: [E](inout Bool, sink [F]() sink -> Void) -> Void
) {
  let m = 1 << i
  let b = n & m != 0
  plateau(&b, fun () {
    &b = if b { b | m } else { b & ~m }
  })
}

fun foo() {
  var x = 0b11
  bit(1, of: &x, fun(b, slide) {
    if b { &b = false ; slide(); print(x) } else { &b = true ; slide() }
  })
}
```

Note that this example is only meant to illustrate the core idea of subscript decomposition.
The above program is not legal in Hylo because there is an overlapping access on `b` in `bit`, as the value is simultaneously passed as an `inout` parameter and captured into a lambda.
The actual transformation is performed using unsafe constructs at a lower level of abstraction to circumvent this issue.

## Implementation

Subscript decomposition is implemented during LLVM code generation and it involves two main operations.
The first decomposes a subscript into a ramp and a slide.
The second extracts plateaus from functions applying subscripts.

When a subscript is compiled, the code generator creates a function representing its ramp and incorporates instructions preceding `yield`.
This function accepts all the parameters of the subscript (applying the Hylo passing convention) as well as two additional parameters at the end, representing the plateau that will be called with the projected value along and the environment of this plateau.
Together, these parameters as referred to as a *plateau callback* in the sources.
The return value of a ramp is a 32-bit integer denoting where control-flow should be directed after the subscript returns.
When the code generator encounters a `yield` instruction, the code generator emits a call to the plateau callback, which returns a `i32` that is eventually returned from the ramp.

For example, on an arm64 machine, the `bit` subscript discussed above will be compiled into the following ramp:

```llvm
define i32 @bit(%sTR2 %0, ptr %1, ptr %2, ptr %3) {
  ; ...
  %10 = call i32 %2(ptr %x, ptr %3, ptr @bit.slide, ptr %y)
  ret i32 %10
}

define i32 @bit.slide(ptr %0) {
  ; ...
}
```

A plateau accepts 4 pointers, namely:
- the value projected by a subscript (`%x` in the above example);
- the environment of the code extracted out of the caller to form the plateau (`%3` in the above example);
- the function implementing the subscript's slide (`@bit.slide` in the above example); and
- the environment of the subscript's slide (`%y` in the above example).

A slide is a function generated with all code reachable from the `yield` instruction that was compiled into its call.
It accepts a single pointer to its environment and returns no value.

Finally, when the code generator encounters a `project` instruction, it emits a call to the corresponding ramp and generates all code dominated by that instruction into a plateau.

### Environments

The environment of a slide or plateau is computed in two steps.
First, we gather all the definitions dominating the instruction causing the slide or plateau to be created.
Second, we filter out definitions that can be recomputed in another function.
In other words, we keep only parameters, allocations, and projections.
The values of those definitions are captured in an array of pointers.

An environment is represented by a pair whose second element is an array of pointers to captured values and whose first element is either an empty tuple or, if the environment is built in the context of a ramp, another pair representing the plateau callback of the subscript.
