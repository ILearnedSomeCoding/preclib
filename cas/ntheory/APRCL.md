# APR-CL 素性证明

`aprcl.hpp/.cpp` 使用 `precn_t` 实现 Jacobi 和版 APR-CL。依据 Cohen 与
Lenstra 的公开数学算法独立编写，沿用本项目 MIT 许可证，不依赖外部大整数库。
算法参考：[Implementation of a New Primality Test (1987)](https://ir.cwi.nl/pub/1774)。

计算器中：

```text
aprcl(2^127-1)                 -> 1
isprime(1000036000099)         -> 0
!progress aprcl(2^127-1)
aprcl_progress(2^127-1)
```

返回 `1` 表示已完成素性证明，`0` 表示合数。负整数、0 和 1 返回 `0`。
只接受精确整数。参数表或辅助素数搜索预算不足会报
`APR-CL proof incomplete`，不会把概率素数当作证明结果。

## 实现步骤

1. 小数试除和 Miller-Rabin 合数筛查。Miller-Rabin 只负责提前拒绝合数。
2. 选择偶数 `t` 和不同的辅助素数 `q`，满足 `q-1 | t`，令
   `s=product(q)`，要求 `s*s > n`。
3. 用 Euler／Lucas-Lehmer 的初步条件建立二进制的 p-adic 条件。
4. 在 `(Z/nZ)[z]/Phi_(p^k)(z)` 中计算 Jacobi 和，检查相应乘积是
   `p^k` 次单位根。分别处理 `p=2` 的 `k=1`、`k=2`、`k>=3` 分支。
5. 对未满足 p-adic 条件的奇素数，寻找额外 `q` 并执行阶为 `p` 的检验。
6. 枚举 `n^i mod s`，检查其中可能的小因子；轨道闭合且未发现因子后，
   才返回已证明素数。

圆分环采用规范系数向量。先将卷积折叠到 `z^(p^k)-1`，再用圆分多项式
关系归约；系数乘积先累加，最后取模。小系数平方利用对称性。
大系数、较高阶的乘法采用 Kronecker 打包：每个系数占用至少
`2*bits(n)+ceil(log2(degree))` 位，向上对齐到整个 limb，保证卷积系数
之间不会串进位。整次卷积转化为一个大整数乘法，再拆包归约。
当前版本未实现论文中利用已分解的 `n-1`／`n+1` 缩小证明模数、将部分圆分环
检验映射到标量环等性能优化。

## C++ 接口和预算

```cpp
#include "cas/ntheory/aprcl.hpp"

auto result = cas_aprcl(precn_t("170141183460469231731687303715884105727"));
if(result.status == cas_primality_status::prime){ /* 已证明 */ }
```

`cas_primality_status` 有 `prime`、`composite`、`unknown` 三种状态。
结果保存原因、找到的因子（可能为空）、`t`、Jacobi 检验次数、额外检验次数和
最后候选因子次数。`cas_aprcl_options` 提供参数生成上界、圆分阶上界、试除界和
辅助素数搜索预算。默认 `t<=73513440`、`p^k<=64`。
小输入优先使用已有参数；大输入从 `720720` 出发，用小素因子动态扩展，
乘法经过溢出检查，且每个 prime-power 不超过配置的阶限制。
超过 512 bit 时，在预算允许的情况下额外保留约 64 位证明模数空间，
减少最后阶段的小因子试除；余量不足时退回只满足 `s*s > n` 的合法参数。
最后阶段先求整数平方根并验证两侧平方，再用比较筛选候选。
输入是否在预算内取决于实际 `s*s > n` 条件，不通过固定十进制位数猜测。

进度使用已有 `cas_factor_progress_scope`，可复用 `!progress` 和 C++ 回调。
函数不缓存输入证明，不改变 `factorint` 原有的概率素性筛查。

## 测试

```powershell
clang++ -O2 -mavx2 -std=c++17 cas/test/test_aprcl.cpp cas/ntheory/factor_integer.cpp src/*.cpp -o cas/test/test_aprcl.exe
.\cas\test\test_aprcl.exe
.\cas\test\test_aprcl.exe --large
.\cas\test\test_aprcl.exe --thousand
```

测试覆盖圆分环的单位、自动同构和单位根识别，各 prime-power 分支，
跳过前置筛查后逐个验证小整数，已知大素数、强伪素数和预算耗尽。
包含 3330 bit 最大系数打包卷积与直接卷积的对照。`--large` 额外证明
`10^100+267`，`--thousand` 完整证明 `10^999+7`，可能耗时较长。
测试文件直接包含实现以检查内部运算，
因此此命令不要再链接 `aprcl.cpp`。

一次完整验证中，`10^999+7` 已证明为素数：`t=8648640`，556 项 Jacobi
检验，最终轨道长度 8648640，总测试耗时约 1174 秒。期间同时进行了编译和
其他回归测试，这不是稳定性能基准；当前千位数证明仍较慢，主要耗时在
Jacobi 和的圆分环运算。`--thousand` 属于手动长测试，不作为常规 CI 检查。
