# `Number`

`Number` is an experimental arbitrary-range binary floating-point type declared
in [`prec_num.hpp`](prec_num.hpp). It uses `precz_t` for its significand and
tracks an accuracy estimate independently for each value.

Precision is measured in significant binary bits, not decimal places.
Arithmetic retains extra guard limbs internally. Text conversion first rounds
the stored value to its declared binary precision and then converts it to
decimal; for example, a value just below one can round to exactly one at low
precision.

```cpp
#include "prec_num.hpp"
```

## Representation

A `Number` stores three fields conceptually:

```text
value = significand * 2^(-64 * radix_point)
```

- `significand` is an arbitrary-precision signed integer.
- `radix_point` is measured in 64-bit limbs, not individual bits.
- `precision` is the estimated number of accurate significant binary bits.

Integral constructors create exact values. Exact precision is represented by
positive infinity and can be tested with `is_exact()`.

Finite-precision values retain two guard limbs while they are normalized.
Limbs below that working precision are discarded; this keeps temporary values
bounded during long calculations.

## Construction

```cpp
Number zero;
Number a(123);                 // exact integer
Number b(precn_t(456));        // exact unsigned integer
Number c(precz_t(-789));       // exact signed integer
Number d(0.5);                 // finite, 53-bit precision
Number e(0.5f);                // finite, 24-bit precision
```

The `float` and `double` constructors preserve the exact binary value already
stored by the source type. They do not perform another rounding step:

```text
Number(0.5)  represents exactly 1/2
Number(0.1)  represents the nearest binary64 value to decimal 0.1
```

The second case is not exact decimal `1/10`; that rounding happened earlier,
when the C++ `double` was created. The resulting `Number` is tagged with 53
bits of precision (`24` for `float`) so later arithmetic treats it as an
approximate input.

NaN and positive or negative infinity are not supported and cause `abort`.
Positive and negative floating-point zero both become canonical zero.

### Raw construction

`from_raw` constructs a value directly from the representation:

```cpp
Number half = Number::from_raw(
    precz_t(precn_t(1) << 63), // significand
    1,                         // radix point
    128                        // claimed precision in bits
);
```

This produces `0.5`. `from_raw` trusts the supplied precision; it does not
measure the accuracy of the significand. A precision must be positive or
infinite.

## Precision

```cpp
double bits = value.precision();
bool exact = value.is_exact();
value.set_precision(256);
```

`set_precision` controls retained working precision. Lowering it may discard
low limbs. Raising it does not recover information that was already discarded,
so callers must not interpret it as an accuracy-improving operation. A common
use is to assign a working precision to an exact input before division or
square root:

```cpp
Number two(2);
two.set_precision(256);
Number root = sqrt(two);
```

Arithmetic does not require equal operand precisions:

- Addition and subtraction propagate absolute input error and account for
  cancellation.
- Multiplication and division combine the operands' relative error estimates.
- Multiplication of two values with `p` accurate bits generally produces
  slightly fewer than `p` reported bits because both operands contribute
  error.
- Division of two exact integers uses 64 bits of working precision because a
  non-terminating binary quotient cannot remain exact.

The precision field is an estimate used to control storage and output. It is
not an interval bound or a proof that every reported bit is correct.

## Arithmetic

`Number` provides:

```cpp
Number z = x + y;
Number z = x - y;
Number z = x * y;
Number z = x / y;

x += y;
x -= y;
x *= y;
x /= y;

Number scaled_up = x << 17;  // multiply by 2^17
Number scaled_dn = x >> 17;  // divide by 2^17

Number magnitude = abs(x);
Number root = sqrt(x);
```

`getpi(digits)` returns pi with enough binary precision for the requested
number of decimal places:

```cpp
Number pi = getpi(100);
std::cout << pi.to_string(100) << '\n';
```

`digits` must be positive. Requests up to 1000 decimal places use a shared,
thread-safe 1000-digit cache initialized on first use. Larger requests run the
factor-aware Chudnovsky binary-splitting implementation directly.

`gete(digits)` similarly returns Euler's number and caches a 1000-digit value:

```cpp
Number e = gete(100);
```

The exponential and natural logarithm use each input's stored binary precision:

```cpp
Number x(2);
x.set_precision(512);
Number ex = exp(x);
Number lx = ln(x);
```

Exact inputs use a 64-bit default because nontrivial transcendental results are
usually inexact. Set a finite precision first when more bits are required.
`ln` requires a positive argument and calls `abort` for zero or negative input.

Shifts are exact powers-of-two scaling operations and preserve the precision
tag. Square root preserves exactness when an exact input has an exactly
representable square root; other roots use finite working precision. Division
by zero and square root of a negative value call `abort`.

All six comparisons are available. Comparisons use represented values; they do
not consider whether the precision intervals of two approximate values might
overlap.

## Conversion And Formatting

```cpp
precz_t integer = value.to_integer();
std::string fixed = value.to_string(30);
std::string automatic = (std::string)value;
```

`to_integer()` truncates toward zero.

`to_string(fractional_digits)` requests at most that many digits after the
decimal point. It currently truncates toward zero rather than rounding to
nearest, then removes trailing fractional zeroes. It never emits scientific
notation.

The explicit `std::string` conversion chooses a decimal digit count from the
stored binary precision. Exact integers are printed without a fractional part.

There is currently no decimal-string constructor for `Number`. Constructing
from `double` is unsuitable when the exact decimal input matters because the
decimal-to-binary64 conversion has already rounded it. Use `from_raw` for an
exact binary value or extend the API with a decimal parser.

## Example

```cpp
#include "prec_num.hpp"

#include <iostream>
#include <string>

int main(){
    Number x(2);
    x.set_precision(256);

    Number y = sqrt(x);
    Number check = y * y;

    std::cout << y.to_string(60) << '\n';
    std::cout << check.to_string(20) << '\n';
}
```

Build from the repository root:

```powershell
clang++ -O3 -mavx2 -std=c++17 example.cpp src\*.cpp -o example.exe
```

## Limitations

- This is not an IEEE 754 type: there are no NaNs, infinities, signed zeroes,
  status flags, or selectable rounding modes.
- Decimal formatting truncates instead of rounding to nearest.
- Precision metadata is approximate and can be overstated by `from_raw` or by
  increasing `set_precision` on an already approximate value.
- The public API is experimental and does not provide a stable ABI.
- Invalid operations use `abort` rather than exceptions or error values.
