# VST 乘法实现

本文介绍 `preclib` 中的 VST（Vector-Scalable Transform）大整数乘法，对应实现为 [`src/mul_vst.cpp`](src/mul_vst.cpp)，公开入口为 `mul_vst(a, b)`。

## 来源与致谢

**VST 的算法思想借鉴自 Alexander Yee 的 y-cruncher。** [y-cruncher 的大整数乘法说明](https://www.numberworld.org/y-cruncher/internals/multiplication.html)将 VST 描述为利用浮点 SIMD 指令执行模变换的算法，并解释了名称 Vector-Scalable Transform 的来历。这里的“借鉴”指算法方向，并不表示本仓库直接复制了 y-cruncher 的实现或与其具有同等规模、优化程度及可靠性保证。

本仓库独立选择模数、编写 AVX2 蝶形与并行管线、CRT 重建及结果校验。项目原创代码的许可证见 [LICENSE](LICENSE)；其他第三方来源见 [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md)。

## 为什么用浮点数做模变换

普通复数 FFT 用浮点数近似卷积系数，最后四舍五入；VST 则对若干素数模数分别做数论变换，再通过中国剩余定理（CRT）恢复整数系数。这里 `double` 主要是 **SIMD 模运算的载体**，不是把最终乘积当作近似浮点数输出。

本实现选用的模数满足 `p^2 < 2^53`，因此两个模剩余的乘积在 `double` 中仍可精确表示为整数。模约减使用浮点倒数估算商，再将剩余修正到合法范围。这个性质不意味着整条实现自动获得形式化正确性证明：商估算、蝶形、CRT、进位和边界输入都必须分别验证。

## 计算流程

1. 将小端序的 64 位 limb 拆成 16 位数字，选择能容纳线性卷积的 2 的幂次变换长度 `n`。
2. 根据卷积系数上界决定是否使用 AVX2 的双模数打包路径；否则使用四模数路径。
3. 对两个输入分别进行正向模变换；平方时复用同一输入变换。
4. 逐点相乘并执行逆变换。
5. 对每个系数用 CRT 恢复整数，传播 16 位进位，重新打包为 64 位 limb。
6. 在主要的打包路径上，额外检查乘积模 `2^61-1` 是否等于输入余数之积；检查失败会中止，而不会返回可疑结果。

AVX2 路径使用模数 `70254593`、`81788929`；四模数路径使用 `7340033`、`13631489`、`26214401`、`28311553`。模数和卷积上界决定可恢复的最大系数，不应在没有重新核对界限及单位测试的情况下随意更改。

## SIMD、并行与内存

AVX2 路径把相邻数字及不同模数的剩余排布到向量中，在蝶形、逐点乘法和 CRT 阶段使用向量指令。较大的变换还会融合部分正变换、逐点乘法、逆变换和系数收集，并按长度使用多个 worker。变换计划及工作区会复用，以减少重复生成根表和临时分配。

这不是完整的 y-cruncher VST，也没有磁盘交换或任意大规模变换支持。本实现的变换长度上限为 `2^20`；超过上限时 `mul_vst()` 会交给整数 NTT。默认乘法分派只在合适的 AVX2 大乘法区间选择 VST；其他长度可能使用学校式、Karatsuba、Toom-Cook 或 FFT。具体阈值见 [`src/mul_basic.cpp`](src/mul_basic.cpp)。

`mul_high()` 会先裁掉不会影响所需高位的输入前缀，AVX2 构建再使用 VST 算剩余乘积；**它目前仍执行完整的剩余变换**，并非真正只逆变换输出窗口。

## 正确性边界

CRT 系数上界、`double` 精确整数范围和模 `2^61-1` 校验共同降低出错风险。校验是错误检测，不是无条件的正确性证明：它不能排除所有软件错误，也不能保证每个可能的错误都被发现。需要验证新优化时，应将结果逐 limb 与独立的整数 NTT 或学校式乘法比较，尤其覆盖全 `0xffff...`、稀疏数字、平方及不平衡输入。

## 构建与测试

以下命令均在仓库根目录运行，并要求 CPU 支持 AVX2：

```powershell
clang++ -O3 -mavx2 -std=c++17 test\test_prec.cpp src\*.cpp -o test\test_prec.exe
.\test\test_prec.exe --checks-only

clang++ -O3 -mavx2 -std=c++17 test\bench_vst.cpp src\*.cpp -o test\bench_vst.exe
.\test\bench_vst.exe --max 32768
```

`bench_vst` 对照 FFT、整数 NTT 与 VST，并先检查乘积一致性。编译时加入 `-DPRECN_VST_PROFILE=1` 可分阶段统计；加入 `-DPRECN_VST_STRICT_CHECKS=1` 可启用更严格的系数检查。使用 `-DMUL_DISPATCH_USE_VST=0` 可对比默认分派不使用 VST 的性能。结果受 CPU 温度、频率、输入形状和线程设置影响，应交错多次测量。
