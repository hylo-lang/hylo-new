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

### Slides and plateaus

The contents of a function that is compiled into a slide or plateau is determined by enumerating the basic blocks that are dominated by the start of the slide or plateau.
This approach identifies the largest possible region that cannot possibly contain a back edge to a position before the instruction at the start of the slide or plateau.
This property is most relevant in the presence of loops, as it prevents unintended (and possibly diverging) unrolling.

One exception is made for plateaus that cover a `yield` instruction.
Specifically, if a plateau is formed over a region that contains a `yield` instruction, then its contents is made of the set of blocks *reachable* from its start, which thereby includes the set of blocks dominated by the `yield` instructions that are part of the plateau.

### Environments

The environment of a slide or plateau is represented by a pair whose second element is an array of pointers to captured values and whose first element is either an empty tuple or, if the environment is built in the context of a ramp, another pair representing the plateau callback of the subscript.

The captures of an environment are identified in two steps.
First, we gather all the definitions dominating the instruction causing the slide or plateau to be created.
Second, we filter out definitions that can be recomputed in another function.
In other words, we keep only parameters, allocations, and projections.
The values of those definitions are captured in an array of pointers.

Consider the following IR subscript to illustrate:

```
fun id(_:)(inout %p0: Int32) inout <: Int32 {
%b0:
  %r0 = alloca Int, #preferred
  %r1 = subfield %r0 at 0 as word
  %r2 = access [set] %r1
  %r3 = store word 0 to %r2
  %r4 = end %r2
  %r5 = access [inout] %p0
  %r6 = yield %r5
  %r7 = end %r5
  %r8 = access [sink] %r0
  %r9 = assume_state %r8 uninitialized
  %r10 = end %r8
  %r11 = return
}
```

The `yield` statement will be compiled as a call to a slide covering `%r7` through `%r11`.
The environment of this slides captures `%p0`, `%r0`, `%r1`, `%r2`, and `%r5` (`%r3` and `%r4` do not define values) but only `%p0` and `%r0` need to be stored in the environment, since all other definitions can be recomputed in the slide.
