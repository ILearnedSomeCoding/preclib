# preclib

`preclib` is an experimental C++17 arbitrary-precision integer library. It
stores magnitudes as little-endian arrays of 64-bit limbs and selects different
multiplication and division algorithms according to operand size.

It provides two number types:

- `precn_t`: an arbitrary-precision unsigned integer
- `precz_t`: an arbitrary-precision signed integer built from a private
  `precn_t` magnitude and a sign

The repository also includes a Chudnovsky/binary-splitting program that uses
the library to calculate large numbers of digits of pi.

## Features

- Construction from integral values and decimal strings
- Conversion to decimal and other bases
- Addition and unsigned subtraction
- Multiplication, division, and remainder
- Comparisons, bit shifts, and bitwise operations
- Greatest common divisor and integer square root
- Specialized multiplication implementations:
  - Schoolbook
  - Karatsuba
  - Toom-Cook
  - FFT
  - NTT
  - Schönhage-Strassen-style Fermat-ring multiplication
- Schoolbook, divide-and-conquer, and Newton reciprocal division

## Representation

The main type is `precn_t`, declared in [`prec.hpp`](prec.hpp):

```cpp
struct precn_t {
    size_t asiz; // allocated limb count
    size_t rsiz; // significant limb count
    uint64_t *a; // little-endian limbs
};
```

An integer is represented as:

```text
a[0] + a[1] * 2^64 + a[2] * 2^128 + ...
```

Zero has `rsiz == 0`. The implementation owns its limb allocation and provides
copy and move operations.

`precz_t` uses sign-and-magnitude internally. Its sign is private, and every
result is normalized so zero is always positive; `-0` cannot be produced
through its public API. Signed division truncates toward zero and the remainder
has the dividend's sign, matching C++ integer division.

### Signed division semantics

`precz_t` division and remainder follow the C++ rules for nonzero divisors:

| Expression | Result |
| --- | ---: |
| `7 / 3` | `2` |
| `-7 / 3` | `-2` |
| `7 / -3` | `-2` |
| `-7 / -3` | `2` |
| `7 % 3` | `1` |
| `-7 % 3` | `-1` |
| `7 % -3` | `1` |
| `-7 % -3` | `-1` |

For every nonzero `b`:

```text
a == (a / b) * b + (a % b)
abs(a % b) < abs(b)
```

The quotient truncates toward zero. A nonzero remainder has the dividend's
sign; an exact remainder is canonical positive zero. These rules are tested
against native signed integer division over all sign combinations.

## Example

```cpp
#include "prec.hpp"

#include <iostream>
#include <string>

int main() {
    precn_t a(std::string("123456789012345678901234567890"));
    precn_t b(std::string("98765432109876543210"));

    precn_t product = a * b;
    precn_t quotient = a / b;
    precn_t remainder = a % b;

    std::cout << static_cast<std::string>(product) << '\n';
    std::cout << static_cast<std::string>(quotient) << '\n';
    std::cout << static_cast<std::string>(remainder) << '\n';
}
```

Signed values use the same operators:

```cpp
precz_t x(std::string("-12345678901234567890"));
precz_t y(42);
precz_t z = x * y + 7;

std::cout << static_cast<std::string>(z) << '\n';
```

The signed API includes arithmetic, division and remainder, comparisons,
shifts, increment/decrement, `abs`, `gcd`, and `precz_sqrt`. Right shift acts
on the magnitude and therefore truncates negative values toward zero.

Build it from the repository root by compiling the program together with all
library source files:

```bash
clang++ -O3 -std=c++17 example.cpp src/*.cpp -o example
```

There is currently no separate library build system or installation step.

## Multiplication dispatch

`operator*` automatically chooses an implementation. The current dispatcher
uses approximately the following policy, measured in 64-bit limbs:

| Operand shape or size | Implementation |
| --- | --- |
| One-limb operand | Scalar multiplication |
| Up to 24 limbs | Schoolbook |
| 25-192 limbs | Karatsuba |
| 193-6144 limbs | FFT |
| More than 6144 limbs | NTT |
| More than 2:1 imbalance | Blocked multiplication |

Dedicated Toom-Cook and SSA entry points are available for testing and
experimentation but are not selected by the default dispatcher.

## Division dispatch

Division includes:

- A single-limb `128 / 64 -> 64` loop
- Normalized schoolbook long division
- Divide-and-conquer division starting at 256 divisor limbs
- Newton reciprocal division starting at 32768 divisor limbs when the
  divide-and-conquer path is not used

On x86-64 Clang builds, single-limb division uses the hardware `divq`
instruction. Each call maintains `high_limb < divisor`, which guarantees that
the quotient fits in one `uint64_t`.

## Building the pi example

### Portable build

```bash
clang++ -O3 -std=c++17 pi/pi_chudnovsky.cpp src/*.cpp \
  -o pi/pi_chudnovsky
```

### Intel macOS with AVX2

```bash
clang++ -O3 -mavx2 -std=c++17 pi/pi_chudnovsky.cpp src/*.cpp \
  -o pi/pi_chudnovsky
```

Only use `-mavx2` on a CPU that supports AVX2. The FFT and NTT implementations
contain explicit AVX2 paths. FMA is not required.

### Windows with Clang

```powershell
clang++ -O3 -mavx2 -std=c++17 pi\pi_chudnovsky.cpp src\*.cpp -o pi\pi_chudnovsky.exe
```

### Usage

Calculate 1,000 digits after the decimal point:

```bash
./pi/pi_chudnovsky 1000
```

Long results are abbreviated to their first and last ten digits by default.
Use `--full` to print every digit:

```bash
./pi/pi_chudnovsky 1000 --full
```

Write the full result to a file:

```bash
./pi/pi_chudnovsky 100000 --file pi100000.txt
```

Show phase timings:

```bash
./pi/pi_chudnovsky 100000 --phases
```

The phases report time spent in binary splitting, scaled square root, final
division, and decimal conversion.

## Tests

Build and run the main test suite:

```bash
clang++ -O3 -mavx2 -std=c++17 test/test_prec.cpp src/*.cpp \
  -o test/test_prec
./test/test_prec
```

The full suite includes large stress and timing cases and may take some time.
For a shorter optimized-build check:

```bash
clang++ -O3 -mavx2 -std=c++17 test/test_opt_smoke.cpp src/*.cpp \
  -o test/test_opt_smoke
./test/test_opt_smoke
```

### FFT torture test

The FFT torture test compares FFT multiplication against exact NTT
multiplication on adversarial operand patterns:

```bash
clang++ -O3 -mavx2 -std=c++17 -DCOUNT_FFTS=1 \
  test/fft_torture.cpp src/*.cpp -o test/fft_torture
./test/fft_torture
```

It also reports the distance of reconstructed FFT values from their selected
integers. That rounding statistic is a warning indicator, not an independent
proof of correctness: after an error crosses a half-integer boundary, rounding
may select the wrong integer while the measured distance becomes smaller
again. The exact FFT-versus-NTT product comparison is the correctness check.

An experimental fast-math build can be tested with:

```bash
clang++ -O3 -mavx2 -ffast-math -std=c++17 -DCOUNT_FFTS=1 \
  test/fft_torture.cpp src/*.cpp -o test/fft_torture_fastmath
```

Do not assume `-ffast-math` is safe for every FFT size merely because the
included torture cases pass.

### GMP comparison

When GMP is installed, build the comparison benchmark with the appropriate
include and library paths for the local installation. For example, with an
Intel Homebrew installation on macOS:

```bash
clang++ -O3 -mavx2 -std=c++17 test/bench_gmp.cpp src/*.cpp \
  -I/usr/local/opt/gmp/include -L/usr/local/opt/gmp/lib -lgmp \
  -o test/bench_gmp
```

Run multiplication and division comparisons through `2^N` limbs:

```bash
./test/bench_gmp 10
```

Run only the GCD comparison:

```bash
./test/bench_gmp 8 gcd
```

Each GCD result is checked against `mpz_gcd`. The reported ratio is preclib
time divided by GMP time, so smaller is better.

## API notes and limitations

- `precn_t` is unsigned; negative integers are not supported.
- Subtracting a larger value from a smaller value returns zero.
- Division or remainder by zero currently returns positive zero for both
  `precn_t` and `precz_t`. Unlike this library, division by zero in C and C++ is
  undefined behavior.
- Decimal string construction ignores non-decimal characters. For example,
  `"12a34"` is parsed as `1234`.
- The representation fields are public and memory is managed with
  `malloc`/`realloc`/`free`.
- The project currently has no stable ABI, namespace, package definition, or
  installed-library target.
- Thresholds are implementation constants tuned experimentally and may not be
  optimal on every CPU.

These properties make the project most suitable for numerical experiments,
algorithm development, and benchmarking rather than as a hardened replacement
for GMP or Boost.Multiprecision.

## Repository layout

```text
prec.hpp          Public type and function declarations
src/              Arithmetic implementations
pi/               Chudnovsky pi calculator
test/             Correctness tests, torture tests, and benchmarks
tools/            Helper scripts for generated numerical constants
```
