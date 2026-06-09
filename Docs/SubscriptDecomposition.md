# Subscript Decomposition

Intuitively, a subscript can be understood as a pair of functions.
The first, called "ramp", computes a value to project.
The second, called "slide" undoes the setup made to compute that value and potentially applies changes made to the projected value back to the whole of which it is a part.
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
This closure, called a "plateau", will then call the slide after the last use of the projection. Consider the following program to illustrate:

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
