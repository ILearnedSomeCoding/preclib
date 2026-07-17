# Pi Chudnovsky

Build from the repository root:

```powershell
clang++ -O3 -mavx2 -std=c++17 pi\pi_chudnovsky.cpp src\*.cpp -o pi\pi_chudnovsky.exe
```

Build with FFT rounding-safety counters:

```powershell
clang++ -O3 -mavx2 -std=c++17 -DCOUNT_FFTS=1 pi\pi_chudnovsky.cpp src\*.cpp -o pi\pi_chudnovsky.exe
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
