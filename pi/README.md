# Pi Chudnovsky

Build from the repository root:

```powershell
clang++ -O3 -std=c++17 pi\pi_chudnovsky.cpp src\init_basic.cpp src\add.cpp src\sub.cpp src\mul_u32.cpp src\mul_basic.cpp src\mul_kara.cpp src\mul_toom.cpp src\mul_fft.cpp src\mul_ntt.cpp src\div_basic.cpp src\div_newton.cpp src\base_convert.cpp src\compare_shift.cpp -o pi\pi_chudnovsky.exe
```

Run:

```powershell
.\pi\pi_chudnovsky.exe 1000
```

The argument is the number of digits after the decimal point. Long results print
as `first10digits...last10digits` by default.

For full output:

```powershell
.\pi\pi_chudnovsky.exe 1000 --full
```

Write the full output to a file while keeping console output short:

```powershell
.\pi\pi_chudnovsky.exe 100000 --file pi100000.txt
```

For phase timing:

```powershell
.\pi\pi_chudnovsky.exe 100000 --phases
```
