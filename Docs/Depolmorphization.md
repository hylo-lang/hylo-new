# Deploymorphization

A function (or type) is polymorphic iff it accepts type parameters and monomorphic otherwise.
The implementation (aka definition) of a monomorphic function may feature uses of polymorphic constructs that have to be either *monomorphized* or *existentialized* before IR can be compiled to machine code.
These transformations are referred to as *depolymorphization*.

Both monomorphization and existentialization essentially consist of creating a copy of the polymorphic function.
In the former case, type arguments are simply substituted for their corresponding parameters.
In the latter case, the type parameters are transformed into term parameters accepting type witnesses at run-time.

This document describes how Hylo implements depolymorphization.

> Disclaimer:
> The syntax of Hylo IR is far from final.
> Snippets are intended as illustration rather than specification.

## Existentialization

In a nutshell, existentialization consists of replacing type parameters with term parameters while abstracting over any information that cannot be determined at compile-time.
Consider the following example to illustrate this concept:

```hylo
fun swap<T is Movable>(a: inout T, b: inout T) {
  var x = a ; a = b ; b = x
}
```

The first step to compile this function is to lower it to Hylo IR.
Recall a conformance constraint such as `T is Movable` is always compiled to term parameter accepting a conformance witness.
As a result, the signature of the lowered form of `swap(_:_:)` is as follows:

```hylo
fun swap(_:_:)<T>(
  let %p0: Movable<T>, inout %p1: T, inout %p2: T, set %p3: Void
)
```

The function is still polymorphic at this stage, taking a type parameter `T`.
`%p0` accepts a witness of `T`'s conformance to movable.
`%p1` and `%p2`, correspond to `a` and `b`, respectively.
Finally, `%p3` denotes the output register of the function, i.e., the place to which its result is written.

Existentialization will produce a copy of this function in which the type parameter `T` is replaced with a term parameters:

```hylo
fun swap(_:_:).existentialized(
  let %p0: Type, let %p1: Movable<?0>, inout %p2: ?0, inout %p3: ?0, set %p4: Void
)
```

Rather than taking a type parameter, this function accepts a *type witness* as its first parameter `%p0`.
This type witness will be used to obtain information about the layout of `T`, as we shall see later.
The following parameters are the same as those of the polymorphic version, just renamed.
Finally, occurrences of `T` have been replaced with `?0`, which denotes a *skolem* representing some type unknown at compile time.

> From a more formal perspective, existentialization relies on the observation that a term of type `∀⍺.τ`, where `⍺` is a type variable that may occur in `τ`, can be transformed into a term of type `∃⍺.ω → τ` in which the extra parameter witnesses `⍺`'s properties at runtime.
> One can then [skolemize](https://en.wikipedia.org/wiki/Skolem_normal_form) existentially quantified variable to get rid of the quantifier, resulting in a term of type `ω → τ` in which each occurrence of `⍺` has been replaced with a skolem (aka rigid variable).
>
> For example, given a function of type `∀⍺.⍺ → ⍺`, we first construct a function `∃⍺.ω → ⍺ → ⍺` before applying skolemization to replace occurrences of `⍺` by some unique skolem `κ` and end up with a term of type `ω → κ → κ`, which is a monomorphic function.
>
> Note that nothing in the type system that links `ω` to neither `⍺` nor `κ`.
> As a consequence, the compiler cannot verify the type safety of a function after it has been existentialized.
> This issue is inconvenient but does not invalidate the safety of the source language, since existentialization preserves semantics.
> Hence, a showing the well-typedness of a polymorphic function provides guarantees about the behavior of its existentialized form, at least in principle.
> No formal theorem has been proven at the time of this writing.

### Existentializing definitions

Notice that the existentialized form of `swap(_:_:)` is monomorphic, as it no longer accepts any type argument.
As a result, it can be compiled to LLVM and ultimately machine code.
Naturally, the definition of the function should also be modified to eliminate uses of the type parameter.
The details of this transformation are discussed below, using `swap(_:_:)` as a running example.

> From a formal perspective, the mechanisms discussed below describe to the transformations applied to a polymorphic term of type `∀⍺.τ` to produce an monomorphic term of type `ω → τ[⍺ ↦ κ]`.

#### Stack allocations

Storage allocated on the stack is represented by `alloca` instructions in the IR.
If the type of the allocated storage is concrete and not hidden behind a resilience boundary, the compiler can compute the size and alignment of the allocation at compile-time.
Otherwise, the size of the allocation is read from a type witness at run-time.

To illustrate, consider the allocation of `x` in the original polymorphic definition of `swap`, which is lowered to the following alloca:

```hylo
%r0 = alloca T, #preferred
```

As the function's definition gets existentialized, the compiler will conclude that `?0`'s layout is abstract and thus transform the allocation so that it uses the corresponding type witness instead.
In our running example, recall that this witness is passed to `%p0`:

```hylo
%r1 = access [let] %p0
%r0 = alloca %r1 as ?0, #preferred
```

A less trivial case arises when the allocation is for a generic type instantiated using a skolem.
For instance, assume the following instruction was existentialized under the same conditions:

```hylo
%r0 = alloca T[2], #preferred
```

Because `%p0` is a witness of `T` (i.e., `?0` in the existentialized signature) and not `T[2]`, the compiler has to first construct a type witness of the latter before it can replace the `alloca`:

```hylo
%r3 = access [let] %p0
%r2 = type_witness (<T> T[2])(%r3)
%r1 = access [let] %r2
%r0 = alloca %r1 as ?0, #preferred
```

Here, `%r2` is assigned to a type witness constructed at run-time.
The semantics of the `type_witness` are discussed later.
For now, it suffices to understand that it serves to apply a type constructor (i.e., `<T> T[2]`) to the witness of `?0` that is passed to `%p0`.
Finally, the resulting new type witness is used to transform the `alloca`, as in the previous example.

Note that the more occurrence of a type parameter in a type expression does not determine whether or not that expression denotes a type whose layout is abstract.
For example, the type `Pointer<T>` does not have an abstract layout because it contains no stored property whose layout depends on `T`.
Therefore, no change is necessary to existentialize an `alloca` creating a place for storing instances of `Pointer<T>`.

> A non-generic type may also have an abstract layout if it is defined beyond a resilience boundary.
> In this case, however, the first lowering phase will already have generated `alloca` instructions parameterized by type witnesses.

#### Function calls

Consider the following use of `swap(_:_:)`, in a monomorphic call site:

```hylo
public fun main() {
  var m = 2
  var n = 4
  swap(&n, &m)
}
```

The use elaborates to `swap<Int>` during typing and is compiled to a type application during lowering.
Specifically, the emitter produces the following IR:

```hylo
%r0 = type_apply swap(_:_:)<Int>
%r1 = apply %r0(%w, %m, %n) => %u
```

`%r0` is the result of applying the lowered form of `swap(_:_:)` to `Int`.
It occurs as the callee in the second line, which assumes that `%w` is a `let` access on the evidence that `Int` is `Movable`, that `%m` and `%n` are `inout` accesses to the places whose contents are exchanged, and that `%u` is a `set` access to a place for storing a unit value (i.e., the result of the call).

Existentializing this sequence of instructions requires three modifications to the `apply` instruction at the end.
First, we should substitute a reference to the existentialized form of `swap(_:_:)` for `%r0`.
Second, we should pass a type witness of `Int` to the additional parameter this function accepts.
Finally, we should remove the `type_apply` instruction.
The resulting IR will be as follows:

```hylo
%r2 = type_witness Int()
%r3 = access [let] %r2
%r4 = place_cast %w as let Movable<?0>
%r5 = place_cast %m as inout ?0
%r6 = place_cast %n as inout ?0
%r1 = apply swap(_:_:).existentialized(%r3, %r4, %r5, %r6) => %u
```

`%r2` is assigned to a value witnessing the properties of the type `Int`, which is used as a type constructor of arity 0.
This value is passed to the first parameter of the call in the last line, applies the existentialized form of `swap(_:_:)` rather than its type application.
The casts whose results are assigned to `%r4`, `%r5`, and `%r6` only serve to appease the type system so that the arguments' types match the parameters'.

No other change is necessary.
When the existentialized form of `swap(_:_:)` is eventually compiled to LLVM, the code generator will conclude that its parameters should be taken by reference since the size of a skolem is unknown at compile-time.

#### Accesses to stored properties

The way in which the stored properties of a type are laid out in memory depends on the sizes and alignment requirements of these properties.
If the layout of a type is concrete and not hidden behind a resilience boundary, then the address of a particular stored property can be computed at compile time.
Otherwise, this address must be computed at run-time by reading layout properties from a type witness.

Hylo IR uses a relatively abstract instruction, called `property`, to express raw accesses to these properties.
While this instruction abstracts over byte offset computation, it still distinguishes between compile-time and run-time address computation.
To illustrate, consider an overload of `swap(_:_:)` that would operate on the elements of a pair.

```hylo
struct Pair<A, B> {
  var first: A
  var second: B
}

fun swap<T is Movable>(elements_of pair: Pair<T, T>) {
  swap(&p.first, &p.second)
}
```

The lowered form of `swap(elements_of:)`'s polymorphic definition, the `first` and `second` properties of the pair are accessed as follows:

```hylo
%r0 = property "first" of %pair as T
```

Here, `%pair` denotes the pair passed as an argument and `T` is the type of the property whose address is taken.
As already discussed, `T` will be replaced by `?0` in the function's existentialized form.
Just like with `allocate` instructions, the compiler will eventually conclude that `?0` is abstract and transform the instruction accordingly.
Specifically, the property access will be modified to include a run-time witness of the type whose property is being accessed.

```hylo
%r1 = access [let] %p0
%r2 = access [let] %p0
%r3 = type_witness (<T, U> Pair<T, U>)(%r1, %r2)
%r4 = access [let] %r3
%r0 = property "first" of (%pair : %r4) as ?0
```

`%p0` and `%p1` are both accesses to the place containing the witness of `?0`, which are passed to a type constructor to form a witness of `Pair<?0, ?0>`.
At run-time, this type witness will be used to determine the byte offset of the pair's `first` property.

Accesses to members of a tuple or buffer are transformed similarly, only for another instruction.
For example, should `Pair` be defined as an alias for `{T, U}` in source code, then the above example would be lowered as follows:

```hylo
%r1 = access [let] %p0
%r2 = type_witness (<T> {T, T})(%r1)
%r3 = access [let] %r2
%r0 = subfield [0] of (%pair : %r3) as ?0
```

*The reason why the type constructor takes only one argument here is explained later, along with the discussion that examines the construction of run-time type witnesses.*

#### Witness tables

Before we delve into the details of witness table existentialization, we should first discuss how conformance declarations are lowered from source to IR.

Consider the following program:

```hylo
trait P {
  fun foo() -> Int
  fun bar() -> Int { 1 - self.foo() }
}

given wa: Bool is P {
  fun foo() -> Int { if self { 1 } else { 0 } }
  fun bar() -> Int { if self { 0 } else { 1 } }
}
```

A conformance declaration can be understood as a subscript that projects a value witnessing the conformance of a type to a trait.
In the above example, `wa` declares a conformance of `Bool` to `P`, which can be seen as a subscript projecting an instance of `P<Bool>`.
The value of this instance is a *witness table* describing how `P`'s requirements are implemented.

Unsurprisingly, then, a conformance declaration is lowered like a subscript:

```hylo
fun wa() <: let P<Bool> {
%b0:
  %r0 = witness_table {
    $implementation[P.foo for Self: Bool],
    $implementation[P.bar for Self: Bool]
  } as P<Bool>
  %r1 = access [let] %r0
  %r2 = yield %r1
  %r3 = end %r1
  %r4 = return
}

fun $implementation[P.bar for Self: Bool](
  let %p0: P<Bool>, let %p1: Bool, set %p2: Int
) {
  ...
  %r3 = apply wa.bar(%r1) => %r2
  ...
}

fun wa.bar(let %p0: Bool, set %p1: Int) { ... }
```

The instruction `witness_table` creates a witness table gathering the functions implementing the trait's requirements.
Notice that these functions, which are called *implementation interfaces*, have a signature slightly different from those statisfying the trait requirements in the original source.
Specifically, they accept an additional parameter of type `P<Bool>`, which denotes the witness itself.
The reason for this mechanism will become more obvious later.
For now, one can think of an implementation as a method of the witness that forwards calls to some other function.
For instance, the implementation interface `$implementation[P.foo for Self: Bool]` simply forwards its arguments to `wa.foo`.

At call site, using a method inherited by conformance involves two steps.
The first is to obtain a witness table, either by applying a conformance declaration or reading a parameter.
The second is to obtain the implementation contained in that table.
For example, `true.foo[]` would be lowered as follows:

```hylo
%r0 = project w[]
%r1 = property "foo" of %r0 as [Void](let P<Bool>, self: let Bool) <: let Int
%r2 = access [let] %r0
%r5 = apply %r1(%r2, %b) => %n
```

The first line assigns `%r0` to the witness table projected by the application of the conformance declaration.
The next assigns `%r1` to the implementation of `foo` in that table.
This function is finally called in the last line, assuming `%b` is a `let` access to a place storing `true` and `%n` is a set access to the storage in which the result of the call `foo` should be written.
Notice that the witness table itself is passed as the first argument.

We are now ready to examine how this mechanism interacts with existentialization.
Implementation interfaces are there to provide a uniform way to refer to an implementation, regardless of the way it is defined in sources.
To illustrate, imagine `wa` did not define `bar`, relying instead on the default implementation defined in the trait.
The implementation interface of `bar` would change accordingly:

```hylo
fun $implementation[P.bar for Self: Bool](let %p0: P<Bool>, let %p1: Bool, set %p2: Int) {
  ...
  %r4 = apply P.bar.existentialized(%r10, %r11, %r12) => %r13
  ...
}

fun P.bar<Self>(
  let %p0: P<Self>, let %p1: Self, set %p2: Int
) { ... }

fun P.bar.existentialized(
  let %p0: Type, let %p1: P<?0>, let %p2: ?0, set %p3: Int
) { ... }
```

In this scenario, the default implementation of `bar` defined along with the trait is in fact generic over the `Self` parameter of that trait.
As a result, it has to be existentialized (or monomorphized) before it can be used to construct a witness table instantiated with `Bool`.
However, since existentialization will extend the parameter list of the polymorphic function, the resulting function's signature won't match the type expected at call sites.
The implementation interface addresses this issue by supplying the extra argument.

One complication arises when the conformance declaration is itself generic.
For instance, consider the following example:

```hylo
given wb: <T> => T is P {
  fun foo() -> Int { 0 }
}
```

The implementation of `foo` in `wb` is generic over `T`.
Yet, the signature of the trait requitement did not change and neither did the type of the implementation expected at call sites.
While existentialization can produce a monomorphic version of this polymorphic function, calling it will require a type witness of the type argument instantiating the conformance.
Unlike in the previous case, however, this type witness is not constant and thus we cannot simply modify the implementation interface.

In fact, the type witness that should be passed to the existentialized form of `foo` is first passed to the existentialized form of the conformance declaration.
To illustrate, let us examine a use of `wb` lowered to IR:

```hylo
%r0 = type_witness Bool()
%r1 = access [let] %r2
%r2 = project wb.existentialized[%r1]
%r3 = property "foo" of %r2 as [Void](let P<Bool>, self: let Bool) let -> Int
%r4 = access [let] %r0
%r5 = apply %r3(%r4, %b) => %n
```

The function assigned to `%r3` is expected to have the same signature as in the previous example, meaning that its interface can't forward a type witness from its own parameters.
Instead, the type witness can be captured into the witness table projected by the application of `wb`.
Then, since a witness table is passed as the first argument of a call to an implementation interface, the latter can extract the captured witness and forward it.
The following snippet illustrates:

```hylo
fun wb.existentialized(let %p0: Type) let <: P<?0> {
%b0:
  %r5 = access [let] %p0
  %r0 = witness_table {
    $implementation[P.foo for Self: ?0].existentialized.applied_0,
    $implementation[P.bar for Self: ?0].existentialized.applied_0
  } + [%r5] as P<?0>
  %r1 = access [let] %r0
  %r2 = yield %r1
  %r3 = end %r1
  %r6 = end %r5
  %r4 = return
}

fun $implementation[P.foo for Self: ?0].existentialized.applied_0(
  let %p0: P<?0>, let %p1: ?0, set %p2: Int
) {
%b0:
  %r0 = witness_table_stash %p0 as {Type}
  ...
  %r6 = apply $implementation[P.foo for Self: ?0].existentialized(%r2, %r3, %r4) => %r5
  ...
}

fun $implementation[P.foo for Self: ?0].existentialized(
  let %p0: Type, let %p1: P<?0>, let %p2: ?0, set %p3: Int
) { ... }
```

The existentialization of `foo`'s implementation interface results in the last function, which accepts a type witness of the trait's `Self` parameter as its first argument.
The second function represents this interface partially applied to its first argument.
The value of the witness is read from the witness table using the `witness_table_stash` instruction, which projects the place containing the captures of a witness table.
Finally, the witness table is filled with the partially applied interfaces, along with a capture of the type witness passed to the conformance declaration.

Note that nothing in the type system guarantees the safety of these functions.
Instead, the sole argument justifying their correctness is that they are all the product of a mechanical transformation.
In particular, unlike the type of a lambda, the type of a witness table does not describe the shape of its captures.
Consequently, `witness_table_stash` unsafely assumes the shape of the table's captures.

The lifetimes of a table's captures are guaranteed to exceed the lifetime of the table itself because witness tables do not yet support copying or relocation.
This limitation should be lifted in the future, requiring a mechanism to ensure the liveness of a table's captures.
No design has been finalized yet, but a promising approach would be to require captures to be `Regular` and make them part of escaping tables.
