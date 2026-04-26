# Current ABI specification

## Struct Layout
However LLVM lays out structs by default. It's most likely consistent with the C ABI on the target platform.

## Function Calling
 - `self` is passed as the first argument in case of member functions
 - Return values are passed as the last argument.
 - Void return value is still passed as `void*` as a last argument.
 - All arguments are passed indirectly, via pointers.
 - Name mangling is nonexistent, we just prepend `hylo_` to the function name. See WIP PR for real name mangling: https://github.com/hylo-lang/hylo-new/pull/94

Examples:

```hylo
fun f(param1: let Int, param2: inout Int32) -> Int64

// translates to:
// void hylo_f(intptr_t const* param1, int32_t* param2, intptr_t* returnValue);
```

```hylo
struct P {
  var x: Int32
  var y: Int32

  fun negated() -> P 
}

// translates to:
// void hylo_negated(P const* self, P* returnValue);
```

## Lambda / Arrow Representation

A Hylo lambda (an `Arrow` type with a non-`Void` environment) is represented at the LLVM level as a
**two-field struct**:

```
{
    /// A pointer to a thin function 
    ptr functionPointer, 

    /// The environment struct
    { capture₀, capture₁, … } environment 
}
```
### Thin function calling convention

The thin function pointed to by the arrow's `functionPointer` receives its arguments in this order:

1. **Captured environment elements**, passed individually by pointer (one `ptr` per capture). Remote captures (`RemoteType`) are *stored* inside the environment by pointer and are *loaded* (dereferenced) before being forwarded, so the thin function always receives a plain `ptr` for each capture.
2. **Explicit arguments**, each passed by pointer (same rule as ordinary functions).
3. **Return value**, passed as the last argument by pointer (same rule as ordinary functions).

The return type of the thin function is always `void`; the result is written through the last pointer argument.

So for an arrow with *k* captures and *n* explicit parameters the LLVM function type is:

```
void (ptr cap₀, …, ptr capₖ₋₁, ptr arg₀, …, ptr argₙ₋₁, ptr returnValue)
```

### Bare function references

When a callee is a bare function reference (i.e. the `Arrow` type has a `Void` environment / no captures), no environment struct is constructed and no capture arguments are prepended; the call reduces to the ordinary function-calling convention.

### Example

```hylo
fun apply(f: let [Int] -> Int, x: let Int) -> Int {
  return f(x)
}
```

At the call site `f(x)`, the code generation:
1. Loads the function pointer from `f[0]`.
2. Extracts each capture pointer from `f[1]` (dereferencing remote captures as needed).
3. Calls `fnPtr(cap₀, …, x*, returnValue*)`.

The corresponding C-level sketch:
```c
// Environment struct for a lambda capturing one `let Int`:
struct Env { intptr_t const* cap0; };
// Arrow struct:
struct F { void (*fn)(intptr_t const*, intptr_t const*, intptr_t*); struct Env env; };

// Call site emitted by the back-end:
intptr_t result_storage;
f.fn(f.env.cap0, &x, &result_storage);
```

## Tips:
For interop, you can use `@extern` to declare functions that are implemented in C. Hylo can use their declarations, while you can implement their body in C.

```hylo
@extern("hylo_print_int")
fun print(x: Int) -> Void
```

```c
void hylo_print_int(intptr_t* x, void* returnValue) {
  printf("%ld\n", *x);
}
```

You can emit an object file from a hylo module using the `--emit=object` flag of hc.