# Changelog

## 2026-11-01

- `feat`: 支持符号斜率指数生成元的高次有理积分。以 `t = exp(a*x+b)` 换元后，复用精确 `Q(t)` Hermite/`LogRootSum` 积分器，并通过原变量求导恒等式验证候选；测试覆盖 `1/(1+exp(a*x)+exp(2*a*x)+exp(3*a*x))`。
- `test`: `cas/test/test_risch_rde_core.cpp` 通过，输出 `risch core RDE cases ok`。
- 已推送提交：`9a46338` (`feat: integrate higher-degree symbolic-slope exponentials`)。

### Follow-up: 2026-11-02

- `test`: 增加符号斜率高次有理分母的重复极点回归，覆盖 `exp(a*x)/(1+exp(a*x))^3`；更新 `cas/RISCH.md` 中支持范围。
- `test`: 重新构建并运行 RDE 核心回归，通过，输出 `risch core RDE cases ok`。
- 已推送提交：`47b591d` (`test: cover symbolic-slope rational poles`)。

### Follow-up: 2026-11-03

- `feat`: 混合对数塔支持识别多个 `c*D(p)/p` 项之和，并接受乘在整个和外面的精确变量无关因子；逐项及总式均经精确导数恒等式验证，保留去重后的 `p!=0` 条件。
- `test`: RDE 核心测试通过；新增负增长率 `x/e^x` 与 `x/2^x` 回归并检查预期闭式。
- 已推送提交：`1c6c8ba` (`feat: integrate sums of mixed-tower log derivatives`)。

### Follow-up: 2026-11-03

- `feat`: 精确积分扩展到显式整数幂微分项 `c*D(p)*p^m`；`m=-1` 生成 `c*ln(p)`，其他整数幂按幂积分规则处理。支持混合对数/嵌套指数塔中的多项求和，并对候选原函数执行精确求导验证。
- `test`: RDE 核心回归通过，输出 `risch core RDE cases ok`；覆盖负整数幂、正整数幂及嵌套指数链。
- 已推送提交：`53b1d5f` (`feat: integrate integer-power differentials in exact towers`)。

### Follow-up: 2026-11-03

- `feat`: 将精确链式幂识别扩展到普通复合参数；普通 `integrate()` 在严格验证时使用调用者的紧凑输入，避免旧化简器先展开而漏掉链式结构。单层指数仍走专用分派，负幂条件不会被普通入口丢弃。
- `test`: RDE 核心回归通过；新增正/负整数幂复合参数验证，并确认普通 `context.integrate()` 返回已验证的无条件原函数。
- 已推送提交：`6bb6fa3` (`feat: generalize exact chain-power integration`)。

### Follow-up: 2026-11-03

- `feat`: 增加受限的有理换元积分：匹配精确 `D(p)` 因子，对 `p -> t` 后仅依赖 `t` 的有理式调用严格积分器，回代后验证完整导数恒等式；传播子问题条件，并为对数参数与负幂补充非零条件。
- `test`: RDE 核心回归通过，覆盖 `cos(x)/(1+sin(x)^2)`、`1/(x*(1+ln(x)^2))`，以及混合塔对数和负幂的条件保留。
- 已推送提交：`ce5638b` (`feat: integrate rational functions through exact substitutions`)。

### Follow-up: 2026-11-03

- `feat`: 有理换元现在可提出精确且与积分变量无关的乘法系数；换元后的有理式允许多项式项与真分式项相加，并支持当前 R0 表达式系数域内的符号参数分子。
- `test`: RDE 核心回归通过，增加符号系数正弦换元和 `ln(x)` 参数的混合有理换元验证。
- 已推送提交：`eddabc7` (`feat: support symbolic rational chain substitutions`)。

### Follow-up: 2026-11-03

- `fix`: primitive-pole 判定现在识别精确符号常数平移，如 `ln(x)+a`，并能对 `(ln(x)+a)^(-m)` 给出经重构验证的非初等证书；外乘未知常数时保留非零条件，零倍数仍返回零原函数。
- `test`: 新增平移对数 pole 回归，覆盖数值/符号偏移、多个 pole 阶、未知符号缩放与零缩放；focused suite 和 RDE 核心回归均通过。
- 已推送提交：`ea5ae69` (`fix: certify shifted logarithmic poles with parameters`)。

### Follow-up: 2026-11-03

- `feat`: 将 primitive-pole 归约扩展到 `A*ln(x)+B` 的有限阶负幂，精确归一化斜率并保留 `A != 0` 条件。
- `test`: 覆盖符号斜率/截距及 `m=1,2,3`；shifted-log pole suite 与 RDE core suite 均通过。
- 已推送提交：`9ab5a01` (`feat: normalize affine logarithmic primitive poles`)。

### Follow-up: 2026-11-05

- `feat`: 对只依赖 `log(a*x+b)` 的精确输入执行仿射内层换元，递归积分后回代，并保留未证明非零的换元斜率条件。
- `test`: 覆盖 `x+1`、`2*x+3`、符号 `a*x+b` 的对数 pole（阶数 1 到 3）；focused pole suite 与 RDE core suite 均通过。
- 已推送提交：`02ed54f` (`feat: substitute affine logarithm arguments in Risch`)。

### Follow-up: 2026-11-05

- `feat`: 将仿射对数换元扩展到其余部分也依赖积分变量的精确被积式，并在内层变量中递归求解后严格回代。
- `test`: 覆盖 `x^k*log(x+1)`、`x*log(x+1)^n`、非单位仿射斜率和 `log(x)^n`（`n=1..64`）；仿射对数回归与 RDE 核心回归通过。
- 已推送提交：`a48d87d` (`feat: extend affine log substitution in Risch`)。

### Follow-up: 2026-11-05

- `feat`: 对 `exp(P(log(g(x))))*D(log(g(x)))` 的有理系数多项式指数（`deg(P)>=2`）增加严格非初等性证书。
- `test`: 覆盖 `exp(ln(x)^2)/x`、有理对数内层，以及线性/二次可积退化对照；RDE 核心与仿射对数回归通过。
- 已推送提交：`77fc961` (`feat: certify logarithmic polynomial exponentials`)。

### Follow-up: 2026-11-06

- `feat`: 将 `exp(P(log(g(x))))*Q(log(g(x)))*D(log(g(x)))` 扩展为精确多项式 RDE；有解返回原函数，次数界内无解时返回非初等证书。
- `test`: 覆盖兼容三次 cofactor、低次方程不相容、已有非初等与可积退化样例；RDE 核心与仿射对数回归通过。
- 已推送提交：`fd40737` (`feat: solve logarithmic hyperexponential polynomial RDEs`)。

### Follow-up: 2026-11-07

- `feat`: 将单对数超指数积分从多项式 cofactor 扩展到精确有理 cofactor，复用有理 RDE 分母界与矩阵求解。
- `test`: 新增已知有理解的重复极点案例和无有理解的简单极点案例；`test_risch_rde_core` 通过。
- 已推送提交：`7e143e1` (`feat: solve rational logarithmic hyperexponential RDEs`)。

### Follow-up: 2026-11-07

- `feat`: 对 `exp(c*exp(a*x+b))` 的精确仿射 Ei 核加入有理 RDE 无解证明；非仿射输入不套用该证书。
- `test`: 专项回归通过，覆盖两个非初等核、一个非仿射未认证核及一个可积邻例。完整测试首轮发现参数线性积分把 `a*x+b != 0` 错列为参数条件；该条件修复随后包含于 `b73453f`。
- 已推送提交：`45471d4` (`feat: certify affine nested exponential Ei kernels`)。

### Follow-up: 2026-11-07

- `feat`: 通用 `integrate()` 现可将仿射嵌套指数 Ei 核转换为 `Ei` 原函数，并支持显式链式 cofactor 下的非线性内层；候选均以精确求导验证。变量相关奇点不再混入 Risch 参数条件。
- `test`: 重新编译并通过 `test_risch_exponential_rational`，覆盖直接、缩放仿射与非线性链式 Ei 原函数，以及参数条件过滤。
- 已推送提交：`b73453f` (`feat: integrate nested exponential kernels with Ei`)。

### Follow-up: 2026-11-07

- `fix`: 保留混合超越塔原函数中显式出现的非零对数参数与极点基底条件；继续过滤普通有理变量极点，避免把 `a*x+b != 0` 误报为参数约束。
- `docs`: 说明 `risch_result::conditions` 同时可携带这类超越塔表达式的定义域限制。
- `test`: `test_risch_rde_core` 与 `test_risch_exponential_rational` 均重新编译并通过。
- 已推送提交：`f09a344` (`fix: preserve mixed tower integration conditions`)。

### Follow-up: 2026-11-07

- `feat`: 严格积分器递推求解符号常斜率指数乘精确多项式，`exp(g(x))*P(x)` 通过 `Q' + g'*Q = P` 构造原函数，并附带斜率非零条件。
- `test`: 增加 `x^2*exp(a*x+b)` 与符号系数三次 cofactor 回归；`test_risch_exponential_rational` 和 `test_risch_rde_core` 均通过。
- 已推送提交：`f0a0806` (`feat: integrate symbolic-slope exponential polynomials`)。

### Follow-up: 2026-11-07

- `feat`: 显式 `exp(g(x))` 的严格积分新增精确非恒定多项式指数率下的多项式 cofactor RDE 路径；候选必须通过原被积式的精确导数验证。
- `test`: 覆盖 `d[x*exp(k*x^2+b)]/dx`，并补充非仿射符号率的有理 cofactor 构造原函数；`test_risch_exponential_rational` 通过。
- `docs`: 记录可验证支持子集及尚未完成的一般参数特化、极点界和无解证明。
- 已推送提交：`6997dfb` (`feat: solve polynomial-rate exponential RDEs`)。

### Follow-up: 2026-11-07

- `feat`: 为符号多项式指数率下的有理 cofactor 增加平方自由简单极点局部证书；标量率参数未知时返回非零条件，不满足证书前提时不作非初等断言。
- `test`: `exp(k*x^2+b)/x`、`exp(k*x^2+b)/(x^2+1)` 与 `k*(2*x+1)` 率用例验证证明状态、参数退化和条件传播；指数有理回归与核心 RDE 测试均通过。
- `docs`: 记录此证书的充分条件及重复分母等未覆盖范围。
- 已推送提交：`0e4d4cc` (`feat: certify symbolic-rate simple-pole obstruction`)。

### Follow-up: 2026-11-09

- `feat`: 显式 `exp(g(x))` 的符号非恒定多项式率分支，在多项式 cofactor 不适用时改用有界的表达式系数有理 RDE 求解器；仍仅接受精确导数回代成功的候选，不把求解失败当作非初等证明。
- `test`: 新增 `exp(a*x^2)` 乘简单与重复有理极点 cofactor 的构造原函数回归；`test_risch_exponential_rational` 通过。
- 已推送提交：`b083a20` (`feat: solve rational RDEs for symbolic polynomial rates`)。

### Follow-up: 2026-11-09

- `feat`: 非恒定符号多项式指数率的有理 cofactor 判据使用平方自由重数分解；混合重数分母中若有简单极点层，即可在率系数非零条件下证明有理 RDE 无解。纯重复因子仍不沿用该结论。
- `test`: `exp(a*x^2)/(x*(x+1)^m)` 对 `m=2,3,5` 均得到带正确退化条件的非初等证明，完整指数有理回归通过。
- `docs`: 记录重数层的判据和参数化 RDE 的剩余限制。
- 已推送提交：`97b0d92` (`feat: certify mixed-multiplicity hyperexponential poles`)。

### Follow-up: 2026-11-13

- `fix`: 表达式系数有理 RDE 现在用逐系数精确重构作为 `R' + g'*R = f` 的证书；证书通过后不再因完整导数表达式的化简形式不同而拒绝候选。
- `fix`: 对通过证书的有理候选执行精确多项式 GCD 约分，避免返回未约分的重复因子。
- `test`: 新增带自由分子系数的参数化构造例，并通过完整 `test_risch_exponential_rational` 回归。
- `docs`: 更新参数化有理 RDE 已覆盖范围与剩余限制。
- 已推送提交：`e0e5826` (`fix: accept certified parameterized rational RDEs`)。

### Follow-up: 2026-11-13

- `fix`: 参数系数有理 RDE 候选新增多变量多项式 GCD 约分；仅当商可解析为积分变量多项式、且 numerator/denominator 均通过精确回乘系数验证时才采用。
- `test`: 覆盖三次自由参数分子、重复平方分母和二次符号指数率；检查公共 GCD、精确商、零余项及无额外参数条件。
- `docs`: 记录该约分的证书要求及参数化 GCD 的适用边界。
- 已推送提交：`a2ee65c` (`fix: reduce parameterized rational RDE candidates`)。

### Follow-up: 2026-11-13

- `feat`: 超指数有理 RDE 的重复极点界在有理系数 GCD 不适用时，回退到精确变量无关表达式系数 Euclid；每次除法要求主元有非零证明，候选约分逐系数回乘验证。非代数表达式 DAG 不再交给通用多项式因式分解器，避免崩溃。
- `test`: 增加平移重复二次分母及 `(x^2+e)^2` 精确常数系数案例；参数退化无法证明时仍拒绝泛型化。`test_risch_exponential_rational` 与 `test_risch_rde_core` 均通过。
- 已推送提交：`40884d3` (`feat: support exact constant-field hyperexponential RDE gcd`)。

### Follow-up: 2026-11-13

- `feat`: 表达式系数超指数有理 RDE 在无条件求解失败后可安全重试；只有精确重构成功时才返回候选，并将 GCD/回代主元所需的非零条件附到结果。示例 `(x^2+p)^2` 会显式排除重根退化分支。
- `test`: 参数化重复极点与符号参数极点回归通过；`test_risch_exponential_rational`、`test_risch_rde_core` 均通过。
- `docs`: 更新 `cas/RISCH.md` 的条件传播支持范围及限制。
- 已推送提交：`b243a6b` (`feat: propagate symbolic RDE nonzero conditions`)。

### Follow-up: 2026-11-14

- `feat`: 单一指数生成元有理换元在低次数 RDE 路径未覆盖时，回退到严格 R0 有理积分；只接受换元后与原变量无关的精确有理函数，并验证代回后的完整导数。
- `test`: 新增 `exp(x)/(1+exp(x)^7)` 高次分母用例；`test_risch_exponential_rational`、`test_risch_rde_core` 及 CLI 积分验证通过。
- `docs`: 记录此支持域以及含 `x` 依赖系数、多生成元与近似系数的边界。
