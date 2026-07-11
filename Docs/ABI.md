# Abstract Binary Interface

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

For C interoperability, we pass every parameter and the return value indirectly through the language
boundary. For the detailed motivations, see 
https://github.com/orgs/hylo-lang/discussions/1122#discussioncomment-17090235.

We can declare an `@extern_c_indirect`-annotated function in Hylo, and implement it in C. In the 
indirect C calling convention:
- All parameters are passed indirectly, except zero-sized ones, which are ignored.
- The return value is passed as the last parameter, except if zero-sized.

Example:

```hylo
// Hylo FFI thunk declaration
@c_ffi("eq_int_indirect")
fun eq(x: Int, y: Int) -> Bool
```
```c
// Indirect C function
void eq_int_indirect(intptr_t const* x, intptr_t* y, char* result) {
  *result = *x == *y;
}
```
Here the type layout of `intptr_t` is assumed to match `Int`; same for `char` and `Bool`.