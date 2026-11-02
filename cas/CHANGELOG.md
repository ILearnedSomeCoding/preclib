# Changelog

## 2026-11-01

- `feat`: 支持符号斜率指数生成元的高次有理积分。以 `t = exp(a*x+b)` 换元后，复用精确 `Q(t)` Hermite/`LogRootSum` 积分器，并通过原变量求导恒等式验证候选；测试覆盖 `1/(1+exp(a*x)+exp(2*a*x)+exp(3*a*x))`。
- `test`: `cas/test/test_risch_rde_core.cpp` 通过，输出 `risch core RDE cases ok`。
- 已推送提交：`9a46338` (`feat: integrate higher-degree symbolic-slope exponentials`)。
