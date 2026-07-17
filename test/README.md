# Tests

Build and run:

```powershell
clang++ -O3 -mavx2 -std=c++17 test\test_prec.cpp src\*.cpp -o test\test_prec.exe
.\test\test_prec.exe
```

Build and run the adversarial FFT rounding test:

```powershell
clang++ -O3 -mavx2 -std=c++17 -DCOUNT_FFTS=1 test\fft_torture.cpp src\*.cpp -o test\fft_torture.exe
.\test\fft_torture.exe
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
