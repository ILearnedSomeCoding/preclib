# Tests

Build and run:

```powershell
clang++ -O3 -std=c++17 test\test_prec.cpp src\init_basic.cpp src\add.cpp src\sub.cpp src\mul_u32.cpp src\mul_basic.cpp src\mul_kara.cpp src\mul_toom.cpp src\mul_fft.cpp src\mul_ntt.cpp src\div_basic.cpp src\div_newton.cpp src\base_convert.cpp src\compare_shift.cpp -o test\test_prec.exe
.\test\test_prec.exe
```

Run only division timing:

```powershell
.\test\test_prec.exe --division-timing
```
