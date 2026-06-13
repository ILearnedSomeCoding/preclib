# Tests

Build and run:

```powershell
clang++ -std=c++17 test\test_prec.cpp src\init_basic.cpp src\add.cpp src\sub.cpp src\mul_u32.cpp src\mul_basic.cpp src\mul_kara.cpp src\mul_toom.cpp src\mul_fft.cpp src\mul_ntt.cpp -o test\test_prec.exe
.\test\test_prec.exe
```
