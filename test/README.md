# Tests

Compare VST forward radix-4 butterflies with the original radix-2 stages:

```powershell
$sources = (Get-ChildItem src -Filter *.cpp | Where-Object Name -ne 'mul_vst.cpp').FullName
clang++ -O3 -mavx2 -std=c++17 test\test_vst_forward.cpp $sources -o test\test_vst_forward.exe
.\test\test_vst_forward.exe
```

This white-box test checks double and compact buffers, maximal residues,
random residues, and zero padding. The double-buffer serial path uses radix-4
from 65536 transform points; define `VST_DOUBLE_RADIX4=0` for the old path.
The compact-buffer algorithm is unchanged. This test also compares inverse
butterflies. Double-buffer inverse radix-4 remains an opt-in experiment
(`VST_DOUBLE_INVERSE_RADIX4=1`) because full-product timings were inconsistent.

Integer square root certifies a Newton result using the division remainder
and a square of the smaller correction, avoiding another full-size square
when the bound succeeds. Use `PRECN_SQRT_RESIDUAL_CERTIFY=0` for a baseline.
`test_prec --checks-only` covers exact squares, neighboring squares, and
interior values around the recursive seed threshold and at large sizes.

Test the NTT convolution finish against an independent cyclic convolution:

```powershell
$sources = (Get-ChildItem src -Filter *.cpp | Where-Object Name -ne 'mul_ntt.cpp').FullName
clang++ -O3 -mavx2 -std=c++17 test\test_ntt_finish.cpp $sources -o test\test_ntt_finish.exe
.\test\test_ntt_finish.exe
```

This white-box test includes `mul_ntt.cpp` itself, so omit that file from the
link inputs. It covers all five moduli, one-point and small transforms, squares,
and repeated use of a transformed right operand. The normal convolution finish
fuses pointwise multiplication with the first inverse butterfly, and combines
inverse scaling with Montgomery output conversion. Ring transforms retain their
Montgomery output for untwisting. Define `NTT_FUSED_FINISH=0` for an A/B baseline.

Build and run:

```powershell
clang++ -O3 -mavx2 -std=c++17 test\test_prec.cpp src\*.cpp -o test\test_prec.exe
.\test\test_prec.exe
```

Build and run the arbitrary-precision `Number` tests:

```powershell
clang++ -O3 -mavx2 -std=c++17 test\test_number.cpp src\*.cpp -o test\test_number.exe
.\test\test_number.exe
```

Exact CAS arena and canonicalization tests:

```powershell
clang++ -O3 -mavx2 -std=c++17 cas\test\test_cas.cpp cas\src\*.cpp cas\ntheory\*.cpp src\*.cpp -o cas\test\test_cas.exe
.\cas\test\test_cas.exe
```

General symbolic expressions with `Number` floating-point leaves:

```powershell
clang++ -O3 -mavx2 -std=c++17 cas\test\test_expr.cpp cas\src\*.cpp cas\ntheory\*.cpp src\*.cpp -o cas\test\test_expr.exe
.\cas\test\test_expr.exe
```

The fixed-point precision-mismatch test is expected to abort with a nonzero
exit code:

```powershell
clang++ -O3 -mavx2 -std=c++17 test\test_precf_mismatch.cpp src\*.cpp -o test\test_precf_mismatch.exe
.\test\test_precf_mismatch.exe
```

Build and run the adversarial FFT rounding test:

```powershell
clang++ -O3 -mavx2 -std=c++17 -DCOUNT_FFTS=1 test\fft_torture.cpp src\*.cpp -o test\fft_torture.exe
.\test\fft_torture.exe
```

Build and run the experimental floating-point modular transform benchmark:

```powershell
clang++ -O3 -mavx2 -std=c++17 test\bench_vst.cpp src\*.cpp -o test\bench_vst.exe
.\test\bench_vst.exe --max 32768
```

Add `-mfma` on CPUs with FMA support to fuse the floating-point modular
remainder. Options `--serial`, `--square`, `--min LIMBS`, and `--max LIMBS`
select serial execution, squaring, and the tested size range. Add
`-DPRECN_VST_PROFILE=1` to print VST setup, transform, CRT/carry, and
verification timings. The AVX2 path packs two coefficients modulo two primes,
uses compact data plus 4 workers from a 2^15-point transform, and uses 8
workers only for the largest transforms (one threshold earlier for squares).
Define `PRECN_VST_STRICT_CHECKS=1` to validate every reconstructed coefficient
in tests. AVX2 builds select `mul_vst` wherever the normal dispatcher chooses
the large exact-transform backend. `mul_vst` handles transforms through 2^20
points and falls back to `mul_ntt` above that limit. Define
`MUL_DISPATCH_USE_VST=0` to retain the integer-NTT-only dispatcher for A/B
testing.

Compare serial VST dispatch near power-of-two transform boundaries:

```powershell
clang++ -O3 -mavx2 -std=c++17 -DMUL_DISPATCH_SPLIT_TAIL=1 test\bench_mul_boundary.cpp src\*.cpp -o test\bench_mul_boundary.exe
.\test\bench_mul_boundary.exe
```

The benchmark alternates dispatch and whole VST on identical inputs and checks
each product against NTT. The opt-in serial AVX2 path splits a short high tail
when the total limb count is just over a transform boundary. It is disabled by
default because whole-program pi timings did not consistently improve. Define
`MUL_DISPATCH_SPLIT_TAIL=0` for an otherwise identical baseline. Use the same
`=1` flag with `test_prec --checks-only` to exercise its boundary and alias tests.

Build and run the non-AVX2 smoke and dispatch tests:

```powershell
clang++ -O3 -std=c++17 test\test_opt_smoke.cpp src\*.cpp -o test\test_opt_smoke_noavx2.exe
.\test\test_opt_smoke_noavx2.exe
clang++ -O3 -std=c++17 -DCOUNT_FFTS=1 test\test_no_avx2.cpp src\*.cpp -o test\test_no_avx2.exe
.\test\test_no_avx2.exe
```

Build and run with all explicit AVX2/SSE2 kernels disabled. The vectorizer is
also disabled here so this exercises the scalar loops rather than compiler
generated SIMD:

```powershell
clang++ -O3 -std=c++17 -DPRECN_FORCE_NO_SIMD=1 -DCOUNT_FFTS=1 -fno-vectorize -fno-slp-vectorize test\test_no_simd.cpp src\*.cpp -o test\test_no_simd.exe
.\test\test_no_simd.exe
```

Run only division timing:

```powershell
.\test\test_prec.exe --division-timing
```

Build the normalized single-limb preinverse regression test and benchmark:

```powershell
clang++ -O3 -mavx2 -std=c++17 test\test_div_preinv.cpp src\*.cpp -o test\test_div_preinv.exe
.\test\test_div_preinv.exe
clang++ -O3 -mavx2 -std=c++17 test\bench_div_u64.cpp src\*.cpp -o test\bench_div_u64.exe
.\test\bench_div_u64.exe
```

Define `DIV_U64_PREINV_THRESHOLD` to tune or disable the reciprocal path. The
default starts at 16 limbs; smaller dividends use one hardware `divq` per
limb because computing a reciprocal does not yet repay its setup cost.

Build and run the GMP speed comparison:

```powershell
clang++ -O3 -mavx2 -std=c++17 test\bench_gmp.cpp src\*.cpp -IC:\ProgramData\anaconda3\Library\include C:\ProgramData\anaconda3\Library\lib\gmp.lib -o test\bench_gmp.exe
$env:PATH = "C:\ProgramData\anaconda3\Library\bin;" + $env:PATH
.\test\bench_gmp.exe
```

Pass a max power to test bigger limb sizes, for example:

```powershell
.\test\bench_gmp.exe 16
```
Comprehensive GMP comparison (wall-clock medians, balanced and unbalanced
multiplication, squaring, and several quotient/divisor ratios):

```powershell
clang++ -O3 -mavx2 -std=c++17 test\bench_gmp_full.cpp src\*.cpp -IC:\ProgramData\anaconda3\Library\include C:\ProgramData\anaconda3\Library\lib\gmp.lib -o test\bench_gmp_full.exe
.\test\bench_gmp_full.exe --quick
python test\plot_bench_gmp.py test\bench_gmp_full.csv --output test\bench_gmp_full.png
```

The default run reaches `2^18` limbs and samples both `2^n` and `1.5*2^n`
sizes. Use `--full` for `2^22`, or customize it with `--max-pow N`,
`--samples N`, and `--csv PATH`.
