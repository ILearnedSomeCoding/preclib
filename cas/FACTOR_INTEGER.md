# 整数分解：SIQS 与 ECM

实现位于 `src/factor_integer.cpp`，使用本库的 `precn_t`。算法独立实现。

## SIQS

使用多素数 A、多项式族、字节对数筛和单大余因子配对：

1. 每族固定 A，用 CRT 构造初始 B，并预计算 `2*gamma mod A`。
2. Gray code 每次改变一个符号，增量修改 B 和筛根。B 归约到 `[0,A)` 时，筛根同步补偿平移。
3. 对不整除 A 的素数筛两个根；对整除 A 的素数，筛 `Q(x)=A*x^2+2*B*x+C` 的线性根。
4. 根据筛根建立候选命中表，试除命中的素数及其幂。关系还包含 A 的因子、负号和配对余因子。
5. 相同余因子的两个 partial 合并为完整关系。余因子不要求为素数：相同整数配对仍然产生精确平方。
6. 收集 `factor_base_size+1+max(128,(factor_base_size+1)/32)` 条去重关系后，批量 GF(2) 消元，求零空间依赖。
7. 使用前重新检查依赖的 parity；构造平方同余，尝试差与和的 GCD。依次测试基向量及确定性随机组合。

筛分最多使用四个 worker。在线消元已移除；提交关系前先拒绝超过余因子上限的候选，缩短锁内工作。诊断构建会检查每条完整关系的平方同余。

一般分解入口依次尝试 trial division、rho、少量 ECM。剩余数不超过 260 bit 时进入 SIQS 和强 ECM；261–512 bit 的剩余数改用 128 条曲线、B1=50000、B2=1000000 的 ECM，避免自动启动规模不合适的筛。更大的数保留前述少量 ECM 预算，调用者可直接调用 ECM 接口扩大搜索。193–260 bit 的 SIQS 多项式预算为 60000，避免此前只运行 512 个多项式便退出。

预算耗尽时，计算器错误信息列出已知因子和未分解余数。余数不是已证明的素数，不能把这个状态当作完整分解。ECM 进度同时显示 B1、B2 和曲线预算。

这是有预算的因子搜索。返回零只表示本次未找到因子，不能据此判定输入是素数。尚未加入双大素数图、Block Lanczos；筛仍未利用完整的素数幂根，因此还有关系收集方面的优化空间。

## ECM

不超过八个 64-bit limb 的输入使用固定数组 Montgomery 运算。每个 worker 预计算第一阶段的素数幂，供多条曲线复用。

第二阶段使用 `p=k*210 +/- r` 的 baby-step/giant-step：

- 巨步只保存相邻两点，以微分加法向前推进。
- baby 点使用固定数组缓存，不再逐素数查哈希表。
- 同一巨步中 `+r` 与 `-r` 共用一次叉积检查。
- 按批计算 GCD；整批 GCD 等于 N 时逐项恢复因子。
- 其他 worker 找到因子后，正在执行曲线的 worker 能提前停止。

## 进度接口

原生计算器支持 `!progress factorint(2^128+1)`，也可以直接调用
`factorint_progress(2^128+1)`。普通 `factorint` 不显示进度。
`!progress` 只对本次表达式生效；计算失败后也会恢复默认状态。
目前接入整数分解，其他表达式可以执行，但没有内部阶段通知。

C++ 可用 `cas_factor_big_progress`、`cas_ecm_factor_progress`、
`cas_siqs_factor_progress`。回调签名为
`void(const char *stage, size_t completed, size_t total)`；`total==0`
表示该阶段没有确定的总量。回调在工作线程上串行执行，不能在回调中再次发起分解；
通知回调抛出的异常会被忽略。原接口和返回值保持不变。

ECM 报告曲线完成数，SIQS 报告已收集关系、多项式预算和矩阵消元进度。
这些数字不是找到因子的概率，也不是整个分解任务的完成百分比。
终端约每 150ms 更新一次，进度写入 stderr，结果仍写入 stdout。

## 验证与基准

从仓库根目录运行，测试构建不要定义 `NDEBUG`：

```powershell
clang++ -O3 -mavx2 -std=c++17 -DCAS_SIQS_DIAGNOSTICS cas/test/test_factor_backends.cpp src/*.cpp -o cas/test/test_factor_backends.exe
cas/test/test_factor_backends.exe --large
```

测试直接包含实现，以比较内部滚动巨步与独立标量乘法；编译它时不要再次链接 `cas/src/factor_integer.cpp`。覆盖零标量、小 B1、第二阶段独立找到因子，以及 SIQS 小输入与大输入。

大输入为：

```text
3275698819458552334773298987025285875460883388189256110657795199
= 12788310128365527796074501819439
* 256147902778239783113403647473841
```

本次诊断构建单次测量约 9.47 秒，6854 条关系、零条无效关系；ASan 的同一大输入测试也通过。时间不作为测试断言，并行关系收集的具体关系数和耗时可能变化。

ECM 单独基准：

```powershell
clang++ -O3 -mavx2 -std=c++17 cas/test/bench_ecm.cpp cas/src/factor_integer.cpp src/*.cpp -o cas/test/bench_ecm.exe
# 参数顺序为 N、曲线数、B1、B2；省略参数使用代码中的默认值。
cas/test/bench_ecm.exe
```

默认预算的新旧三组交替测量中位数约为 0.347 秒、0.324 秒。两者都耗尽预算而未找到因子，因此这不是该数的完整分解时间。
