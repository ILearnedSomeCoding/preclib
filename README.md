# preclib

`preclib` 是一个实验性的 C++17 高精度计算库。整数采用小端序的 64 位 limb；乘法和除法会根据操作数规模选择不同算法。仓库还包含 π 计算程序、交互式计算器、符号计算（CAS）以及测试和基准程序。

本项目主要用于研究、验证和比较高精度算法，API 与 ABI 尚不稳定，不建议直接替代经过长期检验的 GMP。

## 数值类型

| 类型 | 头文件 | 用途 |
| --- | --- | --- |
| `precn_t` | `prec.hpp` | 非负任意精度整数 |
| `precz_t` | `prec.hpp` | 有符号任意精度整数 |
| `precq_t` | `prec.hpp` | 自动约分的有理数 |
| `precf_t` | `prec.hpp` | 使用全局二进制精度的定点数 |
| `Number` | `prec_num.hpp` | 各对象独立记录精度的二进制浮点数 |

一般整数运算建议使用 `precz_t`，非整数近似计算建议使用 `Number`。`precn_t` 的值为 `a[0] + a[1] * 2^64 + ...`，其中 `rsiz` 是有效 limb 数，零的 `rsiz` 为 0。`precz_t` 使用符号加绝对值表示；有符号除法向零截断，余数符号跟随被除数。

`precq_t` 保存最简分数，乘除时会先交叉约分。`precf_t` 构造时会保存当前 `precf_digit` 的精度，不同精度的对象混合运算会中止。`Number` 的精度属于对象自身，混合运算不会要求全局精度相同；详细语义见 [NUMBER.md](NUMBER.md)。

## 快速开始

从仓库根目录编译自己的程序，直接链接 `src` 中的实现：

```powershell
clang++ -O3 -mavx2 -std=c++17 example.cpp src\*.cpp -o example.exe
```

仅在 CPU 支持 AVX2 时使用 `-mavx2`；不支持时去掉该参数。当前没有统一的库安装步骤。

```cpp
#include "prec.hpp"
#include <iostream>
#include <string>

int main(){
    precz_t a(std::string("123456789012345678901234567890"));
    precz_t b(-42);
    std::cout << std::string(a * b) << '\n';
}
```

`precn_t` 是无符号类型，做有符号计算请用 `precz_t`。`precn_t` 若减去比自身更大的数会得到零。当前整数除零也返回零；不要将此行为当作数学上有效的结果。构造非法有理数（例如分母为零）会中止程序。

## 算法概览

- 乘法包含单 limb、学校式、Karatsuba、Toom-Cook、FFT、浮点模变换 VST 和整数 NTT；另有实验性的 Fermat 环/SSA 接口。
- 默认乘法按操作数长度和比例分派。AVX2 构建在大乘法区间优先使用 VST，超出其变换长度限制时回退到 NTT。中间区间可由 FFT 或 Toom-Cook 处理，特别不平衡的输入会分块。
- VST 的设计思想借鉴自 y-cruncher；算法流程、来源和正确性边界见 [VST.md](VST.md)。
- 平方有单独的学校式实现。`mul_high()` 支持高位乘积计算：先裁去不会影响结果的低位输入，再提取所需高位。
- 除法包含单 limb、学校式、分治及倒数乘法路径；实际分派还取决于除数和商的长度。
- 提供比较、位移、GCD、整数平方根及进制转换。

分派阈值是实验参数，具体以 [src/mul_basic.cpp](src/mul_basic.cpp) 和 [src/div_basic.cpp](src/div_basic.cpp) 为准；不同 CPU 上的最佳阈值可能不同。

## 计算 π

[pi/pi_chudnovsky.cpp](pi/pi_chudnovsky.cpp) 使用 Chudnovsky 级数与二分拆分。Windows 下构建及运行：

```powershell
clang++ -O3 -mavx2 -std=c++17 pi\pi_chudnovsky.cpp src\*.cpp -o pi\pi_chudnovsky.exe
.\pi\pi_chudnovsky.exe 1000000 --phases --bs-threads 9 --threads 2
```

位置参数是小数点后的位数。长结果默认只显示开头和末尾；`--full` 打印完整结果，`--file PATH` 将完整结果写入文件，`--progress` 显示进度，`--phases` 显示二分拆分、开方、最终除法和十进制转换的耗时。`--bs-threads` 和 `--threads` 分别控制二分拆分 worker 与变换内部线程数。详细说明见 [pi/README.md](pi/README.md)。

## 计算器与 CAS

`calculator/` 是基于 `Number` 的近似数值计算器；`cas/` 提供精确表达式、化简、求解、求导和积分等符号计算功能，`cas/html/` 包含 WebAssembly 网页版。具体支持范围和指令见 [计算器说明](cas/CALCULATOR.md)、[CAS 文档](cas/README.md) 及 [网页版说明](cas/html/README.md)。

## 测试

```powershell
clang++ -O3 -mavx2 -std=c++17 test\test_prec.cpp src\*.cpp -o test\test_prec.exe
.\test\test_prec.exe --checks-only
```

省略 `--checks-only` 会运行包含较大规模计时的完整测试。其他测试、FFT 压力测试、VST 基准和 GMP 对比的命令见 [test/README.md](test/README.md)。性能比较应使用同一台机器、相同输入形状和构建选项，并留意 CPU 频率与温度变化。

## 目录

| 路径 | 内容 |
| --- | --- |
| `prec.hpp`、`prec_num.hpp` | 主要数值类型与 API |
| `src/` | 高精度运算实现 |
| `pi/` | π 计算程序 |
| `calculator/` | `Number` 交互式计算器 |
| `cas/` | 符号计算器及网页版 |
| `test/` | 正确性测试与基准 |

## 许可证

本项目原创部分采用 [MIT 许可证](LICENSE)。第三方来源和相关许可说明见 [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md)。
