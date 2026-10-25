# CAS 数论模块

- `factor_integer.hpp/.cpp`：素性测试、Pollard rho、ECM、QS、SIQS、整数分解分派及进度回调。
- `integer_arithmetic.hpp/.cpp`：任意精度扩展欧几里得、模逆、模幂、广义中国剩余定理及 Jacobi/Kronecker 符号。
- `multiplicative_functions.hpp/.cpp`：基于完整整数分解计算 Euler φ、Möbius μ、Liouville λ、Carmichael λ、除数个数/和、radical、aliquot sum、素因子计数、平方自由/素数幂判定及正因数列表。
- `integer_properties.hpp/.cpp`：精确整数立方根、n 次根、小整数平方因子提取和最小素因子。
- `aprcl.hpp/.cpp`：APR-CL 素性证明，返回素数、合数或未完成，详见 [APRCL.md](APRCL.md)。

表达式层保留参数检查、符号结构和结果打印。大整数库共用的 `src/gcd.cpp`、乘除法和开方仍属于基础库；本模块通过 `prec.hpp` 使用它们。

计算器数论函数使用 snake_case。`extended_gcd(a,b)` 返回 `{g,{x,y}}`，满足
`a*x+b*y=g=gcd(a,b)`；`pow_mod` 接受负指数（模逆存在时）；`chinese_remainder`
接受两组等长列表，支持非互素模数并返回最小非负解，不一致时抛出错误。
`divisor_sigma(k,n)` 当前限制 `0 <= k <= 1000000`；`divisors(n)` 最多列出
100000 个正因数。依赖因数分解的函数在分解预算耗尽时明确报错，而不返回猜测结果。
新增函数 `divisor_count(n)`、`radical(n)`、`aliquot_sum(n)`、
`liouville_lambda(n)` 与 `carmichael_lambda(n)` 也复用完整因数分解；输入按绝对值解释，
但零没有定义，会抛出错误。约定 `lambda(1)=1`、`radical(1)=1`。

编译 CAS 时需要显式加入本目录：

```powershell
clang++ -O3 -mavx2 -std=c++17 cas/calculator.cpp cas/src/*.cpp cas/ntheory/*.cpp src/*.cpp -o cas/calculator.exe
```

`cas/html/build.ps1` 已包含本目录的源文件。整数分解的预算、进度和基准命令见 [FACTOR_INTEGER.md](../FACTOR_INTEGER.md)。

SIQS 的候选试除采用不分配临时大整数的 32 位余数检查和原地整除。Gray-code 根平移及筛起点使用有界加减归约，避免重复整数除法。CRT 保证候选分子可被 A 整除；诊断构建会另外检查这一条件和关系的平方同余。
