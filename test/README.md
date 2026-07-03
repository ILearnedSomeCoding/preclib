# Tests

Build and run:

```powershell
clang++ -O3 -mavx2 -std=c++17 test\test_prec.cpp src\init_basic.cpp src\add.cpp src\sub.cpp src\mul_u32.cpp src\mul_basic.cpp src\mul_kara.cpp src\mul_toom.cpp src\mul_fft.cpp src\mul_ntt.cpp src\mul_ssa.cpp src\div_basic.cpp src\div_newton.cpp src\base_convert.cpp src\compare_shift.cpp -o test\test_prec.exe
.\test\test_prec.exe
```

Run only division timing:

```powershell
.\test\test_prec.exe --division-timing
```

Build and run the GMP speed comparison:

```powershell
clang++ -O3 -mavx2 -std=c++17 test\bench_gmp.cpp src\init_basic.cpp src\add.cpp src\sub.cpp src\mul_u32.cpp src\mul_basic.cpp src\mul_kara.cpp src\mul_toom.cpp src\mul_fft.cpp src\mul_ntt.cpp src\mul_ssa.cpp src\div_basic.cpp src\div_newton.cpp src\base_convert.cpp src\compare_shift.cpp -IC:\ProgramData\anaconda3\Library\include C:\ProgramData\anaconda3\Library\lib\gmp.lib -o test\bench_gmp.exe
$env:PATH = "C:\ProgramData\anaconda3\Library\bin;" + $env:PATH
.\test\bench_gmp.exe
```

Pass a max power to test bigger limb sizes, for example:

```powershell
.\test\bench_gmp.exe 16
```
