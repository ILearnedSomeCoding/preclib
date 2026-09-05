# 精确 CAS 核心

`prec_cas.hpp` 提供 prec-cpp 的符号计算接口。精确数、近似数和符号表达式共用同一套不可变 DAG，但仍保留各自的数值语义。

主要类型：

- `exact_value`：整数、最简有理数或近似 `Number`。
- `exact_expr`：指向不可变表达式 DAG 节点的轻量句柄。
- `exact_context`：拥有共享节点 arena，并负责构造、合并和化简节点。
- `exact_add_builder`：构造大型加法时先合并数值项，减少临时节点。
- `expr`：可包含任意精度近似值的通用表达式。
- `expr_context`：为 `expr` 保存默认二进制精度和底层 `exact_context`。

`exact_expr` 和 `expr` 的声明现在都位于 `prec_cas.hpp`。

## 基本示例

```cpp
#include"prec_cas.hpp"

exact_context cas;
exact_expr x = cas.symbol("x");
exact_expr expression = pow(cas.integer(1) + sqrt(cas.integer(2)) + x,
                            cas.integer(123));
```

这里的幂会保留为一个紧凑的 power 节点，不会在普通构造过程中展开成巨大的多项式。

纯整数和有理数运算保持精确。混合近似运算会将精确操作数转换到近似操作数的精度。近似值的驻留比较使用实际保存的二进制值与精度，不使用模糊相等。

## DAG 共享与规范化

节点不可变，并使用 hash-consing 共享。重复执行：

```cpp
cas.integer(2)
```

会得到相同的节点 ID，而不会反复分配相同常量。

加法和乘法使用 n 元节点，并会执行：

- 展平嵌套的相同运算；
- 合并常量和同类项；
- 按规范顺序排序；
- 合并完全相同的节点；
- 合并乘方指数和有理式因子。

因此：

```text
x-x       -> 0
x/x       -> 1
x^2/x^3   -> x^-1
```

arena 使用固定大小的节点数组和连续的 32-bit operand ID 数组。operand 指向共享节点，不拥有连续子树。

## Arena 压缩与内存回收

hash-consing arena 在构造表达式时只会增长。要回收不可达节点，需要把所有仍需使用的根传给 `compact`：

```cpp
std::vector<exact_expr> roots = cas.compact({x, expression});
x = std::move(roots[0]);
expression = std::move(roots[1]);
```

`compact` 会从这些根出发追踪可达 DAG，并把可达节点复制到新的 `exact_storage`。遍历使用迭代后序算法，不会因表达式过深而耗尽 C++ 调用栈。

旧的 `exact_expr` 句柄仍然有效，因为它们会继续持有旧 arena。只有释放所有旧句柄后，旧 arena 的内存才会真正释放。计算器会在 arena 很大且绝大部分节点已不可达时自动执行压缩，也可以使用 `!gc` 手动触发。

## 多项式化简与 GCD

有理式约分使用混合多项式 GCD：

1. 尝试直接整除。
2. 快速提取公共单项式，例如 `x^a*y^b`。
3. 一元多项式在 `Q[x]` 上使用 monic Euclid。
4. 多变量多项式根据次数和稀疏度选择主变量。
5. 其余情况使用递归 primitive pseudo-remainder sequence。
6. 最后验证公因式能精确整除分子和分母。

例如：

```text
simplify((x^2-y^2)/(x-y))
-> x + y
```

当前实现适合中小型稀疏多项式。大型多变量输入以后可以增加 modular GCD、CRT 和插值恢复。

## 大型数值求和

解析很长的加法时，应使用临时 builder：

```cpp
exact_add_builder sum = cas.make_add_builder();
for(uint64_t i = 1; i <= 10000000; ++i) sum.add_integer(i);
exact_expr result = sum.finish();
```

小的正负整数先在 64-bit 累加器中合并，仅在溢出时转入大整数。因此这个循环会生成一个最终整数节点，而不是一千万个临时大整数节点。

规则化求和可以使用 `bounded_sum`。当前实现能够识别：

```text
sum(i, i=lower..upper)
```

并使用等差数列公式直接计算。

## 方程与方程组

单变量一至四次多项式继续使用原来的根式公式：

```text
exact_solve(x^2-1, {x})
-> {-1, 1}
```

是否返回映射由第一个参数的语法决定：裸表达式返回传统根列表；即使只有一个方程，只要写成 `{equation}`，也返回规则映射。例如 `exact_solve({x^2+y^2-1}, {x})` 的每个解都会写成 `{x -> root}`。

方程组把每个表达式视为“等于零”，方程和变量都使用花括号：

```text
exact_solve({x+y-3, x-y-1}, {x,y})
-> {{x -> 2, y -> 1}}

exact_solve({x+y-3, x*y-2}, {x,y})
-> {{x -> 2, y -> 1}, {x -> 1, y -> 2}}
```

外层列表表示所有解，内层列表是一组 `变量 -> 值` 规则，并保持变量参数的顺序。线性系统使用有理数域上的精确 Gauss-Jordan 消元；欠定系统生成不会捕获输入符号的自由参数，例如 `exact_solve({x+y}, {x,y})` 返回 `{{x -> -_solve_t1, y -> _solve_t1}}`。

非线性系统先把输入转换成有理系数稀疏多项式，再使用词典序 Buchberger 算法构造 Groebner 基，并按消元顺序回代。当前求解器面向零维系统，三角化后每个单变量方程的次数最多为四次。正维非线性系统、更高次数和超过内部项数预算的系统会明确报错，不会返回不完整的有限解集。

## 当前能力

目前包括：

- 精确整数、有理数和任意精度近似值；
- 精确特殊常量 `pi` 和 `e`，并支持按需近似求值；
- 符号、规范加法、乘法、幂和根式；
- 展开、因式约分和多项式 GCD；
- 部分平方根与立方根分母有理化；
- 指数、自然对数、二进制/十进制对数节点；
- 三角、反三角、双曲和反双曲函数节点；
- `ln(e^x)` 与常见有理倍 `pi` 的精确三角函数化简；
- 有界求和；
- 形式导数 `D(y,x)` 与一阶线性常微分方程 `dsolve`；
- 单变量一至四次方程、精确线性方程组和基于 Groebner 基的零维多项式方程组；
- DAG 调试输出和 arena 压缩。

积分器已实现有理函数归约、对数导数、超指数有理 Hermite 归约，以及常量表达式
系数域上的指数、线性三角和双曲 Risch 微分方程；平方自由的三次、四次不可约
分母可通过代数根留数生成精确对数项。当前尚未实现完整代数扩张上的通用 Risch
算法、一般高次
代数方程根表示和 modular 多项式算法。

`dsolve` 当前使用积分因子法求解 `a(x)y'+b(x)y=c(x)`，并生成不与输入符号冲突
的积分常数。它暂不支持一般非线性、高阶或常微分方程组。

对于常见周期零点，`solve` 和 `exact_solve` 使用整数参数表示完整解集：

```text
solve(sin(x), {x}) -> {{x -> n*pi}}
solve(cos(x), {x}) -> {{x -> (2*n + 1)*pi/2}}
```

这里的 `n` 表示任意整数；如果 `n` 已被用户占用，程序会自动使用 `n1`、`n2` 等名称。普通非线性方程仍使用数值 Newton 迭代并返回找到的实数解。
