# Application Binary Interface

## Hylo Type Layout

### Definitions
- **Size:** the number of bytes that the type takes up in memory - the offset past the last member of the type.
- **Alignment:** the required number that the address of any instance must be a multiple of. 0-sized
  types have alignment 1. Alignment is always a power of two.
- **Stride:** the number of bytes between the start of consecutive elements of the type. Can be
  derived by rounding up the size to the nearest multiple of the alignment.

### Record layout
Structs, tuples and enums are laid out using the record layout algorithm.
An enum's record representation is composed of its discriminator and payload, when applicable. Enums
with 0 or 1 cases have no discriminator.

A record's members are laid out in decreasing order of alignment, or when equal, in declaration
order. 

- The offset of each member is such that
  - `(member_byte_offset + member_size) <= record_size`.
  - the offset is a multiple of the member's alignment.
- The offset of a 0-sized member is an unspecified number `x` where `0 <= x <= record_size`.
- 0-sized objects are not guaranteed to have a unique address.

## Hylo Calling Convention

- `self` is passed as the first argument in case of member functions.
- Functions return their result indirectly except when the return type's layout is known and doesn't
  exceed the size of a pointer.
  - Directly: through an LLVM function return value.
  - Indirectly: through a new pointer parameter added at the end of the signature, which points to 
    uninitialized storage allocated by the caller.
- Parameters are passed indirectly, except `sink` and `let` parameters that don't exceed the size of
  a pointer.
- 0-sized parameters are erased.

Examples:

```cpp
fun f(p1: let Int, p2: inout Int32, let p3: LargeStruct) -> Int
// roughly translates to:
intptr_t f(intptr_t p1, int32_t* p2, LargeStruct const*);
```

```cpp
fun g(a: let Vector2, b: let Vector2) -> Vector2
// roughly translates to: 
void g(Vector2 const* a, Vector2 const* b, Vector2* result);
```

```cpp
struct Vector2 {
  var (x, t): {Float32, Float32}
  fun length() -> Float32
}
// roughly translates to:
float length(P const* self);
```

### Closure representation

TODO

### Indirect C Calling Convention

For C interoperability, we pass every parameter and the return value indirectly through the language boundary. For the detailed motivations, see 
https://github.com/orgs/hylo-lang/discussions/1122#discussioncomment-17090235.

We can declare an `@extern_c_indirect`-annotated function in Hylo, and implement it in C. In the indirect C calling convention:

- All parameters are passed indirectly, except zero-sized ones, which are ignored.
- The return value is passed as the last parameter, except if zero-sized.

Example:

```hylo
// Hylo FFI thunk declaration
@extern_c_indirect("eq_int_indirect")
fun eq(x: Int, y: Int) -> Bool
```

```c
// Indirect C function
void eq_int_indirect(intptr_t const* x, intptr_t* y, char* result) {
  *result = *x == *y;
}
```

Here the type layout of `intptr_t` is assumed to match `Int`; same for `char` and `Bool`.
