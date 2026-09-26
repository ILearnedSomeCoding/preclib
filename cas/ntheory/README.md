# CAS 数论模块

- `factor_integer.hpp/.cpp`：素性测试、Pollard rho、ECM、QS、SIQS、整数分解分派及进度回调。
- `integer_properties.hpp/.cpp`：精确整数立方根、n 次根、小整数平方因子提取和最小素因子。
- `aprcl.hpp/.cpp`：APR-CL 素性证明，返回素数、合数或未完成，详见 [APRCL.md](APRCL.md)。

表达式层保留参数检查、符号结构和结果打印。大整数库共用的 `src/gcd.cpp`、乘除法和开方仍属于基础库；本模块通过 `prec.hpp` 使用它们。

编译 CAS 时需要显式加入本目录：

```powershell
clang++ -O3 -mavx2 -std=c++17 cas/calculator.cpp cas/src/*.cpp cas/ntheory/*.cpp src/*.cpp -o cas/calculator_ntheory.exe
```

`cas/html/build.ps1` 已包含本目录的源文件。整数分解的预算、进度和基准命令见 [FACTOR_INTEGER.md](../FACTOR_INTEGER.md)。

SIQS 的候选试除采用不分配临时大整数的 32 位余数检查和原地整除。Gray-code 根平移及筛起点使用有界加减归约，避免重复整数除法。CRT 保证候选分子可被 A 整除；诊断构建会另外检查这一条件和关系的平方同余。
