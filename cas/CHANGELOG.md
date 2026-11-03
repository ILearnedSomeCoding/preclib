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
