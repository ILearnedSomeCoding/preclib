# Number Calculator

This is an interactive expression calculator built on prec-cpp's `Number`
type. It parses decimal literals directly instead of converting them through
`double`.

## Build

From the repository root:

```powershell
clang++ -O3 -mavx2 -std=c++17 calculator\number_calculator.cpp src\*.cpp -o calculator\number_calculator.exe
```

## Run

```powershell
.\calculator\number_calculator.exe
```

The default working precision is 256 requested bits plus 32 internal guard
bits. Command-line options can change the requested precision and fixed output
digits:

```powershell
.\calculator\number_calculator.exe --bits 1024 --digits 100
```

## Expressions

```text
2 + 3 * 4
(2 + 3) * 4
2^1000
1 / 3
sqrt(2)
exp(1)
expm1(1e-30)
ln(2)
log10(1000)
log2(8)
sin(1)
atan(1)
sinh(1)
9^0.5
abs(-123.5)
1.25e-40 * 8e40
ans^2
```

Supported operators are `+`, `-`, `*`, `/`, and `^`. Integer exponents use
binary exponentiation and have magnitude no greater than 1,000,000 in the
calculator. Fractional exponents use `exp(b * ln(a))` and therefore require a
positive base. `^` is right-associative, and exponentiation binds more tightly
than unary minus, so `-2^2` is `-4`.

`ans` contains the last successful result.

## Commands

```text
!precision 512   Set requested binary precision for later approximations
!digits 80       Compute and print up to 80 fractional decimal digits
!auto            Choose output digits from Number's precision estimate
!help            Show concise help
!quit            Exit
```

Fixed-digit mode automatically raises the working precision enough to cover
the requested decimal places. `!precision` remains a minimum. Changing either
setting affects later calculations; it cannot add accuracy to the existing
value in `ans`.

Integer literals and decimal values whose scale is nonnegative are represented
exactly. Other decimal fractions are evaluated by high-precision integer
division and rounded to the nearest guarded binary value, with halfway cases
rounded upward in magnitude. Using one common precision makes complementary
literals such as `0.2 + 0.3` cancel exactly against `0.5`. `Number` itself
formats by truncating, but the calculator rounds displayed results to nearest,
with halfway cases rounded away from zero. Automatic output also reserves two
decimal guard digits rather than exposing the least reliable edge of the
requested binary precision. It uses scientific notation when fixed notation
would mostly show placeholder zeroes outside the significant digits.
`!digits N` always requests fixed notation instead.
