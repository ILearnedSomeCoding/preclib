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
