# 精确 CAS 计算器

在仓库根目录执行：

```powershell
clang++ -O3 -mavx2 -std=c++17 cas\calculator.cpp cas\src\*.cpp src\*.cpp -o cas\calculator.exe
```

然后启动：

```powershell
.\cas\calculator.exe
```

整数和整数构成的分数保持精确。十进制字面量和数值超越函数使用指定二进制精度的 `Number`。

内置精确常量为 `pi`（圆周率）和 `e`（自然常数）。它们与近似数混合运算时，会按当前二进制精度通过 `getpi/gete` 转换为 `Number`。

## 示例

```text
> 1/3 + 1/6
1/2

> x-x
0

> (1+sqrt(2)+sqrt(3))^123
(sqrt(3) + sqrt(2) + 1)^123

> expand((1+sqrt(2))^2)
2*sqrt(2) + 3

> simplify((1+sqrt(2)+sqrt(3))^2)
2*sqrt(2) + 2*sqrt(3) + 2*sqrt(6) + 6

> simplify((x^2-y^2)/(x-y))
x + y

> 9^0.5
3

> approx(1/3)
0.3333333333333333333333333333333333333333333333333333333333333333333333333333

> sin(pi)
0

> ln(e)
1

> ln(e^2)
2

> sin(pi/3)
1/2*sqrt(3)

> sin(pi/4)
1/2*sqrt(2)
```

## 命令

```text
!precision 512   设置近似计算的二进制精度
!nodes           显示 arena 节点数和 operand 数量
!gc              只保留当前答案可达的节点并压缩 arena
!tree [EXPR]     显示表达式树
!info [EXPR]     显示节点数、深度和根节点信息
!dump [LIMIT]    输出底层 arena 节点
!time EXPR       计算表达式并显示耗时
!clear           清空当前 context 和答案
!help            显示帮助
!quit            退出
```

`!precision` 使用二进制有效位，不是十进制小数位。`Number` 在内部保留保护位，并在最终显示时舍入到声明的二进制精度。

## 函数

```text
exp, expm1
ln
log, log10
log2
sin, cos, tan
asin, acos, atan
sinh, cosh, tanh
asinh, acosh, atanh
Si, Ci, Ei, erf, partial_gamma
diff, differentiate, integrate, int, D, dsolve
sqrt
expand, simplify, approx
```

`ln(x)` 是自然对数，`log(x)` 是 `log10(x)` 的别名，`log2(x)` 是以 2 为底的对数。符号参数会保留为函数节点；十进制近似参数会立即使用 `Number` 计算。

`D(y,x)` 构造形式导数；`dsolve(D(y,x)+y=x,y,x)` 使用积分因子法求一阶线性
常微分方程。方程两边可以用 `=`，返回值为 `{y -> ...}`。

## 测试

CAS 测试与数值核心分开编译：

```powershell
clang++ -O3 -mavx2 -std=c++17 cas\test\test_cas.cpp cas\src\*.cpp src\*.cpp -o cas\test\test_cas.exe
clang++ -O3 -mavx2 -std=c++17 cas\test\test_expr.cpp cas\src\*.cpp src\*.cpp -o cas\test\test_expr.exe
```

运行：

```powershell
.\cas\test\test_cas.exe
.\cas\test\test_expr.exe
```

正确输出应为：

```text
cas ok
expr ok
```
