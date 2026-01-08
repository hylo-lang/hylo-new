# The state of Hylo's support for generics

This document describes the current state of Hylo's support for generic programming.
It is intended as a light introduction to the theoretical foundations of Hylo's type systems and as a basis to discuss possible developments.

Unless stated otherwise, the examples presented in this document are supposed to be already supported by the compiler.
Of course it is possible that some features are still under developement and therefore buggy or subject to changes.

## Background

This section presents some background on fundamental concepts.
Readers with a solid grasp on the topic may skip these details or come back to them later.

It's worth mentioning that all of the concepts introduced below have been discovered and extensively studied elsewhere.
Important references include:

- Wadler, P., & Blott, S. (1989, January). How to make ad-hoc polymorphism less ad hoc. (https://doi.org/10.1145/75277.7528)
- Siek, J. G., & Lumsdaine, A. (2005). Essential language support for generic programming. (https://doi.org/10.1145/1065010.1065021)
- Odersky, M. et al. (2017). Simplicitly: Foundations and applications of implicit function types. (https://doi.org/10.1145/31581)

### Implicit programming

In statically typed programming languages, an expression has meaning in a context which defines symbols, their types, and their associated operations.
This context is traditionally defined lexically.
Implicit programming is a technique that allows abstracting over this context.
Consider the following program to illustrate:

```hylo
struct Logger is Regular {
  public let terminator: String
  public memberwise init
  public fun log(item: String) {
    print(item, terminator: terminator)
  }
}

given let global_logger = Logger(terminator: ", ")

fun log<where let logger: Logger>(item: String) {
  logger.log(item)
}

fun f1<where let logger: Logger>() {
  log("Hello")
}

fun f2() {
  given let local_logger = Logger(terminator: "!\n")
  f1("World")
}

public fun main() { f1() ; f2() }
```

The function `log` takes `logger` as a contextual parameter and uses it to log a message.
The body of the function is not particularly suprising but its call sites in `f1` and `f2` are more interesting:

- `f1` takes a logger as a contextual parameter, which will be used implicitly in the call `log("Hello")`.
- `f2` introduces a new logger in the implicit context (with the keyword `given`), which will be used implicitly in the call to `log("World")`.

The main function calls both `f1` and `f2`, causing the program to print `Hello, World!\n`.
In the first call, `global_logger` is passed implicitly to `f1` whereas no implict parameter has to be provided to `f2`.

This somewhat contrived setup shows that contextual parameters can be used to modify the context in which expressions will be evaluated across function boundaries.
In particular, by introducing a logger in the implicit context, `f2` can influence the behavior of the `log`.
This influence is transitive.
For example, `main` could introduce another logger implicitly to influencethe behavior of the function `log` through its call by `f1`.

Finally, note that there's nothing special about `Logger` and its instances.
The former is just a good old type and the latter are just good old values.
The "magic" is about the way the compiler figures out how to provide arguments to contextual parameters implicitly.
We'll keep this mechanism abstract for the time being and just assume the existence of some algorithm without thinking too hard about its properties.

### Parametric polymorphism

One of the simplest ways to support generic programming is to abstract over concrete data stuctures by introducing type parameters.
For example, consider the following program, which features a non-generic algorithm:

```hylo
fun contains(x: Int, in xs: Int[], from s: Int, to e: Int) -> Bool {
  (s != e) && ((xs[s] == x) || contains(x, in: xs, from: s + 1, to: e))
}

public fun main() {
  assert(contains(1, in: [0, 1, 2], from: 0, to: 3))
}
```

*(Note: I'm not using slices on purpose. The main goal of this example is to illustrate the use of parametric polymorphism to write generic algorithms using as few concepts as possible.)*

It is easy to write a more generic version of this implementation by abstracting over the data structure on which it operates.
In order to do so, however, we must also abstract over the way in which we're able to subscript the data structure and get to the next position.

```hylo
fun contains<T, U is Regular>(
  x: Int, in xs: T, from s: U, to e: U,
  reading_elements_with read: [](T, U) -> Int,
  advancing_positions_with advance: [](T, U) -> U
) -> Bool {
  (s != e) && ((read(xs, s) == x) || contains(
    x, in: xs, from: advance(xs, s), to: e,
    reading_elements_with: read,
    advancing_positions_with: advance))
}

public fun main() {
  assert(contains(
    1, in: [0, 1, 2], from: 0, to: 3,
    reading_elements_with: fun(xs, p) { xs[p].copy() },
    advancing_positions_with: fun(xs, p) { p + 1 }))
}
```

This more generic definition is certainly cumbersome to use but it shows that support for standard parametric polymoprhism is enough to get quite far.

### Type classes

Type classes can be understood as a way to alleviate signatures like that of the generic version of `contains` we've discussed above.
The core idea is to bundle operations associated with a particular type into some data structure so that one no longer has to pass each of them individually.
To illustrate, we can simplify the previous example as follows:

```hylo
struct IntegerCollection<T, U> is Regular {
  public let read: [](T, U) -> Int
  public let advance: [](T, U) -> U
  public memberwise init
}

fun contains<T, U is Regular>(
  x: Int, in xs: T, from s: U, to e: U,
  reading_contents_with w: IntegerCollection<T, U>
) -> Bool {
  (s != e) && ((w.read(xs, s) == x) || contains(
    x, in: xs, from: w.advance(xs, s), to: e, reading_contents_with: w))
}

public fun main() {
  let w = IntegerCollection<Int[], Int>(
    read: fun(xs, p) { xs[p].copy() },
    advance: fun(xs, p) { p + 1 })
  assert(contains(1, in: [0, 1, 2], from: 0, to: 3, reading_contents_with: w))
}
```

The two generic operations we've been using to interact with the abstract collection are now bundled into a single entity that we can name and document.
As a result, the signature of `contains` gets quite simpler to read.

To go further, we'd probably like to eliminate some of the boilerplate involved in passing down argumuments to the parameter `w` of `contains`.
If you've been following from the beginning, it should be quite obvious that it's time for contextual parameters to make an entrance.

```hylo
fun contains<T, U is Regular where let w: IntegerCollection<T, U>>(
  x: Int, in xs: T, from s: U, to e: U
) -> Bool {
  (s != e) && ((w.read(xs, s) == x) || contains(x, in: xs, from: w.advance(xs, s), to: e))
}
```

For all intents and purposes, `IntegerCollection` is in fact a type class, which [I like to describe as](https://arxiv.org/pdf/2502.20546v1) "a set of requirements representing a concept in the form of operations that a type must support" and `w` is an instance of this type class.
This instance notionally acting as a witness of `Int[]`'s conformance the concept described by the type class.
Again, it is interesting to note that `IntegerCollection` is just an ordinary type.
The only thing out of the ordinary in our running example is the use of a contextual parameter to pass instances of the type class implicitly, which helps reducing boilerplate.

Programming languages like Haskell, Swift, Scala, or Rust have special syntax to introduce type classes and contextual parameters but the core principles are the same.
Swift and Rust users can substitute `T` for `Self` in the definitions to make the connection more obvious.
More generally, type classes in Haskell, protocols in Swift, and traits in Rust are mostly sugar for what we've discussed so far.
Of course the devil hides in the details and there are important additional considerations to make if we want to study these systems in more details.

#### Type members

While abstracting over arrays in our running example, we also abstracted over the type representing their positions by introducing  `U`.
Because there exist a relationship between `U` and the concept described by `IntegerCollection`, we often say that the former is an *associated type* of the latter.

So far we've been using generic type parameters to represent associated types.
That is a simple approach but it has an important cost in terms of boilerplate because type parameters typically need to appear in all generic signatures.
In our example, that means we must make `contains` generic over both `T` *and* `U` even if we probably do not care about the specific type an instance of `T` uses to represent positions.

One way to avoid this problem is to define associated types as type members.
In Scala, for example, one could declare `IntegerCollection` as follows:

```scala
trait IntegerCollection[Self]:
  type Position
  def read: (Self, Position): Int
  def advance: (Self, Position): Position

def contains[T](using w: IntegerCollection[T])(
    x: Int, xs: T, from s: w.Position, to e: s.Position
): Bool =
  (s != e) && ((w.read(xs, s) == x) || contains(x, xs, w.advance(xs, s), e))
```

As `Position` is defined as a member of `IntegerCollection`, the signature of `contains` no longer needs to explicitly abstract over the type representing positions into instances of `T`.
That's a very convenient trick but it comes with some language complexity costs.
In particular, it requires some support for dependent typing.
We can study the signature of `contains` to understand why.

Just like in Hylo, we're introducing `w` as a contextual parameter (with the keyword `using`) and using it to interact with `xs`.
The interesting difference is that we're using `w.Position` to refer to the type of a position in `xs`.
That is a dependent type!
Specifically, we're referring to a type that is a member of `w`, which is a value.

#### Instance uniqueness

Swift, Rust and Haskell's type systems are not expressive enough to manipulate type class instances explicitly but their underlying model is similar to that of Hylo or Scala nonetheless.
One subtelty, however, is all of these languages adopt a discpline often referred to as "global uniqueness of type class instances", which prescribes that there can be at most one instance of any type class application (i.e., a type class together with arguments for each of its generic parameters), and that such an instance should be defined globally.
The most important benefit of this restriction is that the mere knowledge that a constraint requiring some type `T` to be conform to a concept `P` has been satisfied is enough to assume that any witness of such a conformance will have the same value.
Further, since instances are defined globally, the value of any witness does not need to be passed down as a parameter or stored anywhere; it can simply be obtained on demand.

To illustrate, consider the following Swift snippet:

```swift
struct Negated<T: IntegerCollection> : IntegerCollection {
  let base: T
  func read(_ p: T.Position) -> Int { -base.read(p) }
  func advance(_ p: T.Position) -> T.Position { base.advance(p) }
}
```

Requiring that `T` be conform to `IntegerCollection` means that any type argument `A` allowing the creation of an instance of `Negated<A>` implies the existence of a unique instance of `IntegerCollection`, available globally.
As a result, such an instance does not need to be stored anywhere.
Further, the type expression `T.Position` can be assumed to represent the same dependent type anywhere, since the value on which it depends is globally unique.

In contrast, it is not enough in a language like Hylo to know that there exists some witness of `T`'s conformance to `IntegerCollection` to tell anything about the value of that witness in an arbitrary context.
For this reason, one cannot declare a type like `Negated` in the same way as Swift allows.

## Type classes in Hylo (aka traits, aka concepts)

Hylo's approach to generic programming relies heavily on type classes, which can be understood as a special case of the language's support for implicit programming.
A type class in Hylo is declared as a trait, which defines a set of requirements.
These requirements can represent functions, subscripts, types, or type class instances (i.e., conformance witnesses).
For example:

```hylo
trait Equatable {
  fun equal(other: Self) -> Bool
}
```

*(Note: We're shadowing `Equatable` from the standard library.)*

Just like in Swift or Rust, all traits in Hylo have at least one type parameter named `Self`, declared implicitly.
Additional type parameters are also allowed, as we'll see later.
These parameters are distinct from associated type requirements, which will also be discussed later.

It is important to note that a trait is not too different from a struct.
In fact, the background discusses how to express a type class with a generic struct in Hylo and we could do the same here:

```hylo
struct Equatable<T> {
  let equal: [](T, T) -> Bool
}
```

Using traits mostly helps the compiler (and the user) understand the intent to declare a concept rather than an ordinary generic type, which enables all sorts of sugars.
One sugar in particular relates to the way we can think of the requirements of a trait just like ordinary members.
For example, the member requirement `equal(_:)` in `Equatable` is declared like a method of `Self` when it is in fact a method of `Equatable`, just like the one declared in the generic struct.
Of course these shenanigans are mostly transparent to the user, as we'll see throughout this document.

An instance of a trait denotes a witness of some type's conformance to the concept described by that trait.
It can be declared as follows:

```hylo
struct A {
  public var m: Int
  public memberwise init
}

given A is Equatable {
  public fun equal(other: A) -> Bool { self.m == other.m }
}
```

Note that Hylo places no restriction on conformance declarations.
It is possible to define another instance of `A`'s conformance to `Equatable` for any type argument we want, in any scope we want.
Conflicts will be detected at the point of use.
It is also possible to name a conformance declaration, which may come handy to resolve these conflicts explicitly.

```hylo
given foo: A is Equatable {
  public fun equal(other: A) -> Bool { self.m == other.m }
}
```

Traits can be used as constraints in generic signatures to require that the conformance of a type to a particular concept be established at the use site.
For example:

```hylo
fun first_position<T is Equatable>(of x: T, in xs: T[]) -> Int {
  var p = 0
  while p < xs.size() {
    if xs[p].equal(x) { return .some(p) }
    &p += 1
  }
  return .none
}
```

The function is should be self-explanatory for readers familiar with type class oriented languages.
We can have a look at the desugared version, which is also expressible in surface syntax, to understand the specifics nonetheless:

```hylo
fun first_position<T where let w: Equatable<T>>(of x: T, in xs: T[]) -> Int {
  var p = 0
  while p < xs.size() {
    if w.equal(xs[p], x) { return .some(p) }
    &p += 1
  }
  return .none
}
```

Again, it is interesting to observe that all the shenanigans of the original example boil down to rather simple ideas after desugaring.
The constraint that `T` be conform to `Equatable` is expressed as a contextual parameter `w` of type `Equatable<T>`.
Moreover, the call `xs[p].equal(x)` is sugar for `w.equal(xs[p], x)`.

Looking at this form also gives us a hint about what happens at call site.
For example, consider the following call to `first_position`:

```hylo
fun test_first_position(xs: A[]) {
  assert(xs.empty() || first_position(of: xs[0], in: xs) == 0)
}
```

The compiler has to provide an instance of `Equatable<A>` to the contextual parameter of `first_position`.
Fortunately we have defined such an instance when we declared conformance of `A` to `Equatable` earlier.
Assuming it is called `foo`, the compiler will *elaborate* the call as follows:

```hylo
first_position<_ where w: foo>(of: xs[0], in: xs)
```

### Associated types and generic traits

As mentioned before, traits can be declared with additional type parameters, which are distinct from associated type requirements.
Both are used to abstract over types related to the concept being declared and, as discussed in the background, both have advantages and drawbacks.
As a rule of thumb, it is probably best to use a type parameter to declare types that should typically be constrained in generic signatures involving the trait.
For example, one typically constrains the type of a collection's elements more often than the type of its positions.

```hylo
trait Collection<Element> {
  type Position is Regular
  fun start() -> Position
  fun end() -> Position
  fun position(after p: Position) -> Position
  subscript(p: Position) -> Element
}
```

### Conditional conformances

A conditional conformance states that some type `T` conforms to a trait `P` only in places where some constraints are satisfied.
For example, we can state that arrays conform to `Equatable` only when they contain elements that also conform to `Equatable`:

```hylo
given <T is Equatable> => T[] is Equatable {
  public fun equal(other: Self) -> Bool {
    self.elements_equal(other, by: fun(a, b) { a.equal(b) })
  }
}
```

As a short aside, remark that since conformance witnesses are simply contextual parameters, Hylo gives us quite some flexibility to play with them as first-class values.
For example, we can rewrite the above conformance declaration as follows:

```hylo
given <T where let w: Equatable<T>> => T[] is Equatable {
  public fun equal(other: Self) -> Bool {
    self.elements_equal(other, by: w.equal)
  }
}
```

This observation hints at the fact that conditional conformances are in fact abstractions introduced in the implicit context.
That is, when we say that `T[]` conforms to `Equatable` only when `T` also does, we're defining an abstraction of the form `Equatable<T> => Equatable<T[]>`.
The use of the fat arrow intentionally suggests that the abstraction relates to an implication in first order logic.
And indeed, that is exactly how the compiler interprets conditional conformances.
We'll come back to this observation when we'll discuss resolution.

Constraints can also relate to associated types.
For example, we can state that collections (i.e., types conforming to `Collection`) whose elements conform to `Equatable` also conform to `Equatable`:

```hylo
given <U, T is Collection<U> where U is Equatable>
  => T is Equatable { ... }
```

We can also state (even though that's a somewhat silly example) that collections whose positions conform to `Equatable`:

```hylo
given <U, T is Collection<U> where T.Position is Equatable>
  => T is Equatable { ... }
```

Both of these declarations are hopefully understandable intuitively but the fine prints on the second one are a little sophisticated.
As mentioned in the background, type members imply some form of dependent typing and thus when we write `T.Position` we are actually expressing a dependent type.
Moreover, since Hylo does not uphold global uniqueness of type class instances, we cannot play the same trick as Swift and Rust to assume that `T.Position` represent the same dependent type anywhere.
However, we can say that, *in this specific context*, `T.Position` refers to the member of `T`'s conformance to `Position`.
Put differently, the declaration is equivalent to the following:

```hylo
given <U, T where let w0: Collection<T, U>, let w1: Eq<w0.Element>>
  => T is Equatable { ... }
```

Hylo places no restriction on the shape of a conditional conformance.
In particular, it does not attempt to prove that they can be satisfied or that they may overlap with other declarations.
Conflicts will be detected at the point of use.

### Equality constraints

Swift, Rust, and Haskell support equality constraints (aka same-type requirements) between abstract types, which are typically used in generic signatures to require that an associated type be equal to some other type.
Such constraints are also supported in Hylo.

There are two ways to encode equality constraints in Hylo.
The simplest applies to generic type parameters and it consists of just providing type arguments.
For example, we can state that arrays of Booleans conform to `Equatable` by declaring conformance of `Bool[]` to `Equatable`:

```hylo
given Bool[] is Equatable { ... }
```

Notice that no arrows occur in the declaration because the conformance is not really conditional, at least not in the same way as we have discussed earlier.
It would be conditional if we introduced a type parameter and, separately, a constraint that this parameter is equal to some other type.
For example:

```hylo
given <T where T == Bool>
  => T[] is Equatable { ... }
```

While this declaration means the same as the previous one notionally, it is much more complex when seen through the eyes of the underlying theory and thus the first approach should be preferred.
However, explicit equality constraints are necessary to constrain type members.
For example, we can state that collections whose positions represented by `Int` conform to `Equatable`:

```hylo
given <U, T is Collection<U> where T.Position == Int>
  => T is Equatable { ... }
```

An explicit equality constraint between to types `A` and `B` is represented by a contextual parameter of the built-in type `Eq` (not to be confused with `Equatable`).
Perhaps surprisingly, there is nothing particularly special about `Eq` or the way that it is used to prove equality between two types.
That is, the presence of an instance of `Eq<A, B>` in the implicit context is interpreted as evidence that `A` and `B` are equal.
The difficult part is to deduce equalities that are consequence of other constraints.

To illustrate, consider the following definition:

```hylo
fun f<T, U where T == U>() { f<U, T>() }
```

Calling `f` will certainly diverge but one can expect that the function type checks.
If `T` is equal to `U` then surely `U` is equal to `T`.
If we desugar the definition, however, we see that making such a deduction requires extra steps to figure out that an instance of `Eq<T, U>` is can be used to derive an instance of `Eq<U, T>`.
Fortunately, we can teach the compiler how to make such deductions using ordinary conditional conformances encoding the formal properties of equality.

```hylo
/// Reflexivity
given <T> => Eq<T, T>
/// Symmetry
given <T, U> => Eq<U, T>
/// Transitivity
given <T, U, V where T == U, U == V> => Eq<T, V>
```

These conformances are built-in but they otherwise contribute to the resolution algorithm in the same way as any other conformance declaration.

### Trait refinement (aka trait inheritance)

Swift, Rust, and Haskell support some notion of trait inheritance.
Intuitively, if a trait `Q` inherits from `P`, then any type that conforms to `Q` *must* also conform to `P`.
This notion is reminiscent of subtyping but it is fundamentally different.
In broad strokes, subtyping is typically thought to obey Liskov's substitution principle, stating that if `B` is subtype of `A` then one can use an instance of `B` anywhere an instance of `A` would be allowed.
This principle is not upheld by trait inheritance as implemented by Swift, Rust, Haskell, or Hylo.

To illustrate, let us consider the following program:

```hylo
trait Comparable refines Equatable {
  fun less_than(other: Self) -> Bool
}
```

*(Note: We're shadowing the standard library again.)*

This declaration states that `Comparable` is a refinement of `Equatable` and therefore holding an instance witnessing conformance to the former implies the existence of an instance witnessing conformance to the latter.
This guarantee is encoded by a conformance requirement on the `Self` parameter of the trait.
That is, the above declaration is sugar for the following:

```hylo
trait Comparable {
  given base: Equatable<Self>
  fun less_than(other: Self) -> Bool
}

given equatable_from_comparable: <T where let w: Comparable<T>>
  => T is Equatable = w.base
```

There are two key elements at play here.
First, the conformance requirement in `Comparable` ensures that any instance must also provide a conformance to `Equatable`.
Second, the given definition outside of the trait ensures that the compiler can derive an instance of `Equatable<T>` in any context where an instance of `Comparable<T>` is available.
Together, these definitions allow the following program to type check, as expected:

```hylo
fun foo<T is Comparable>(x: T) -> Bool {
  x.equal(x)
}
```

However, note that an instance of `Equatable<T>` *cannot* be susbstituted for an instance of `Comparable<T>`, neither in this example nor in general.
And indeed, the elaboration of `foo` reveals that the call to `equal` does not use the instance of `Comparable<T>` directly.
Instead, we must first resolve an instance of `Equatable<T>`:

```hylo
fun foo<T where let w0: Comparable<T>>(x: T) -> Bool {
  let w1: Equatable<T> = equatable_from_comparable<T where w: w0>[]
  return w1.equal(x, x)
}
```

### Higher-kinded type parameters

Hylo supports higher-kinded types.
That is, one can declare a generic type parameter denoting a type constructor.
Classic use cases include the obligatory functor:

```hylo
fun foo<F :: * -> *, A, B>(fa: F<A>, map: [](A) -> B) -> F<B> { ... }
```

*(Note: `* -> *` specifies the kind of the parameter.)*

As `F` is higher-kinded, we should pass a type constructor to instantiate `foo`.
For example:

```hylo
let xs: Bool[] = foo<Array, _, _>([1, 2, 3], fun(a) { a & 1 == 0 })
let ys: Bool? = foo<Optional, _, _>(.some(1), fun(a) { a & 1 == 0 })
```

Another particularly interesting use case relates to the resolution of conformance constraints involving equality constraints.
For example, consider the following function:

```hylo
fun bar<T, U is Equatable where T == U>(x: T, y: U) -> Bool {
  x.equal(y)
}
```

From the constraints in the signature we can assume the existence of two witnesses in the body of the function, namely `Equatable<U>` and `Eq<T, U>`.
Unfortunately, neither can be used to call `equal`, as we're looking for an insntance of `Equatable<T>`.
Fortunately, we can teach the compiler to find such an instance by adding the following definition:

```hylo
given <P :: * -> *, A, B, where A is P, A == B> => P<B>
```

In plain English, this conformance definition reads as "given a trait `P` and two types `A` and `B`, if `A` conforms to `P` and `A` is equal to `B` then `B` conforms to `P`".
Just like the properties of equality, this definition is built-in but otherwise contributes to the resolution algorithm in the same way as any other conformance declaration.

## Implicit resolution

This section discusses the algorithm Hylo uses to provide arguments to contextual parameters implicitly.
This algorithm is often referred to as "implicit resolution" or just "resolution" in the documentation of the compiler.

Implicit resolution can be seen as a generalization of type inference.
Compilers of languages supporting parametric polymorphism are generally expected to infer arguments to type parameters.
The following illustrates:

```hylo
fun id<T is Movable>(x: sink T) -> T { x }
public fun main() {
  _ = id(1)
}
```

The call to `id` requires the compiler to infer an argument for the function's type parameter.
In Hylo and like many modern languages, that is done by considering the type of the other parameters as well as the expected type of the call.
Here, inference easily concludes that the type argument is `Int`.

Implicit programming extends this idea to *term* parameters, allowing the compiler to infer term arguments depending on the context.
Coming back to the above example, the call to `id` also involves an additional contextual parameter witnessing the conformance of `T` to `Movable`.
Just like for `T`, the compiler is expected to figure out the argument that should be passed to this parameter by inspecting the context of the call.

We'll need a bit of math to explain formally how resolution works.
Fortunately, it is relatively easy to fit Hylo's type system into System F, or more precisely System F Omega but the former will be enough in the context of this document.

Resolution consists of finding a term to replace `e` in the formal statement below, which states that an instance of `τ` can be derived from those found in `Γ`.

```
Γ ⊩ e : τ
```

To illustrate, consider the following program:

```hylo
trait P {}
struct S<T> {}

given a: Bool is P {}
given b: <where Bool is P> => Int is P {}
given c: <T where T is P> => S<T> is P {}

fun foo<where S<Int> is P>() {}
public fun main() { foo() }
```

The call to `foo` in `main` requires the compiler to resolve an argument of type `P<S<Int>>`.
That is, it must satisfy the following formal statement:

```
a : P<Bool>, b : P<Bool> => P<Int>, c : ∀T . P<T> => P<S<T>> ⊩ e : P<S<Int>>
```

Spoiler: the statement does hold if `e` is substituted for `(c Int) (b a)`.

A complete explanation of Hylo's resolution algorithm is beyond the scope of this introductory document but we can nonetheless look at a handful of examples to get some intuition.

Resolution is a type-directed process.
Looking at the statement `Γ ⊩ e : τ`, the goal is to find in `Γ` definitions producing an instance of a type unifiable with `τ`.
Doing so will guide the construction of the term that will eventually replace `e`.

The process concludes immediately there exists `x : τ` in `Γ`, in which case `e` is simply susbtituted for `x`.
Otherwise, there are just a few situations to handle.
We'll focus on three of them:

- If `Γ` contains a term `x : τ'` such that `τ` is unifiable with `τ'`, we can construct a term `x` and use the result of unification to fix the type of free variables in `Γ`.
  For example, given `x : α, α ⊩ e : τ` where `α` is a free variable, we can conclude `x : τ, α : τ ⊩ x : τ`.

- If `Γ` contains an implication `x : τ'' => τ'` such that `τ` is unifiable with `τ'`, we can construct a term `x e''` and use resolution to infer `e''` such that `Γ ⊩ e'' : τ'`.
  For example, given `x : τ1 => τ2, y : τ1 ⊩ e : τ2`, we can conclude `x : τ1 => τ2, y : τ1 ⊩ x y : τ2`.

- If `Γ` contains a u universally quantified formula `x : ∀α . τ'` such that `τ` is unifiable with `τ'`, we can construct a term of the form `x α'` and use resolution to infer `α` such that `Γ, α ⊩ x α : τ`.
  For example, given `x : ∀α . α ⊩ e : τ`, we can conclude `x : ∀α . α, α : τ ⊩ x τ : τ`.

It's worth noting that this relatively simple declarative specification explains resolution almost entirely!
The formal definition is even more concise and fits a third of a page.
Unfortunately, this specification is also ambiguous because there may be more than one way to form a term `e` such that ``Γ ⊩ e : τ` holds.
For example, we could write the following program:

```hylo
trait P {}

given a: Bool is P {}
given b: <where Bool is P> => Int is P {}
given c: <where Int is P> => Bool is P {}
```

There are an infinite number of ways to obtain an instance of `P<Bool>` using these definitions, including:

- `a`
- `(c (b a))`
- `(c (b (c (b a))))`
- ...

That is an issue because the choice of a particular term may have an impact on the semantics of the program.
For example, there may be two different instances witnesses the conformance of a type to `Hashable` with different implementations.
To make things worse, it is not possible in general to know whether or not we have exhausted all possible ways to form an instance and thus we cannot simply construct to set of all instances and decide which one we like better.

There has been a lot of work trying to figure out sensible syntactic restrictions to eliminate this problem but all of them have pretty significant drawbacks.
At the very least, they introduce great complexity in the specification of resolution, sometimes even [opening the door to soundness issues](https://arxiv.org/pdf/2502.20546v1).

Fortunately, there is a nice and easy way to make our declaration deterministic without making any of these syntactic restrictions.
We can simply state that the resolution picks the smallest term.
In the above example, that means the first result (i.e., `a`) is preferred over all the others because it is just smaller.

In practice, another advantage of this trick is that it helps writing an algorithm that is complete with respect to the declarative specification.
In layperson's terms, that means we can devise an algorithm that is guaranteed to produce the same results as the declarative specification.
Thus it is not necessary to understand the specifics of this algorithm to understand the resolution; the far simpler declarative specification suffices.

## Known limitations

The system we have presented so far presents a some known limitations that have yet to be addressed.
This section discusses two of them.

### Constraints on parametric type definitions

Perhaps surprisingly, it is not currently possible to constrain the type parameters of a generic type definition.
For example, the following type declaration is illegal:

```hylo
struct S<T is Hashable> { ... }
```

Such constraints can be expressed in Swift because of global uniquess.
Since there the conformance of a type to a type class must be unique and global, one does not have to worry that two instances of `S<T>` might have been constructed using different witnesses of `T`'s conformance to `Hashable`.

These assumptions do not hold in Hylo.
For example, one could write the following:

```hylo
struct S<T is Hashable> is Regular { ... }

fun foo() -> S<Int> {
  given Int is Hashable {
    public fun hash(into h: inout Hasher) { &h.combine(self) }
  }
  return S()
}

public fun main() {
  let x: S<Int> = foo()
  assert(S<Int>().hash_value() == x.hash_value())
}
```

The value returned by `foo` presumably uses a witness of `Int`'s conformance to `Hashable` different from the one visible to `main`, likely causing the assertion to fire.

It may be tempting to say that a type expression `T` denote different types depending on the context in which it occurs.
Then one could conclude that the return statement of `foo` is ill-typed since it would result in an instance of `S<Int>` that is not compatible with instances of `S<Int>` formed outside of `foo`.
However, this strategy is not applicable in Hylo because one cannot enumerate the set of traits to which a type conform in a given context.

Another idea would be to somehow encode the a witness into the type expression `S<T>`.
However, this strategy is not ideal either as it would bring significant complexity to the type system.
A fundamental issue is that witnesses are values and thus any effort to bring them into type signatures requires some form of dependent typing.

Yet another idea would be to store the witness in instances of `S<T>`.
This strategy is problably the most promising but it is not expressive enough to handle some of the use cases Swift handles.
In particular, one would need an instance of `S<T>` to determine the value of the witness that was used to construct it.
As a result, one would not be able to write definitions like the following:

```hylo
trait P { type X }
struct S<T is P> {}
given <T> => S<T> is P { type X = T.X }
```

Here, the meaning of `T.X` is unclear because it depends on the value of a witness that is not available in the definition.
In Swift, it suffices to query how `T` uniquely conforms to `P` since the answer will be the same in any context.
That is not the case in Hylo.

### Specialization

Implicit resolution is biased toward simpler derivations as it picks the smallest term that it can construct to witness a specific conformance.
Consequently, if presented with two ways to derive an instance of `P<T>`, the compiler will select the one that involves the least constraints, all other things being equal.

This strategy might be counter-intuitive to users coming from languages supporting some form of specialization as in those languages, constraints typically correlate with opportunities to provide more efficient implementations.

Because resolution is relatively predictable, however, there exist many ways in which the user may be able to influence resolution.
For example, one can manually introduce a witness of a specific type into the context that will have priority over any other definition:

```hylo
trait P {}
trait Q {}
struct S<T> is Regular { ... }

given a: <T> => S<T> is P { ... }
given b: <T> => S<T> is Q { ... }
given c: <T is Q> => T is P { ... }

fun use<T is P>(x: T) { ... }

public fun main() {
  given d: P<S<Int>> = c<S<Int> where b>[]
  use(S<Int>())
}
```

In the absence of the given declaration in `main`, resolution would pick `a` rather than `c` to derive a witness if `S<Int>`'s conformance to `P`.
That is because the former would lead to a smaller derivation than the latter.
Because `d` has type `P<S<Int>>`, however, resolution will pick that definition over both `a` and `d`.
