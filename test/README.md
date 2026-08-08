# Tests

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
clang++ -O3 -mavx2 -std=c++17 cas\test\test_cas.cpp cas\src\*.cpp src\*.cpp -o cas\test\test_cas.exe
.\cas\test\test_cas.exe
```

General symbolic expressions with `Number` floating-point leaves:

```powershell
clang++ -O3 -mavx2 -std=c++17 cas\test\test_expr.cpp cas\src\*.cpp src\*.cpp -o cas\test\test_expr.exe
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
