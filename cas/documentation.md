# prec-cpp CAS 文档

## 1. 启动计算器

原生版本：

```powershell
cas\calculator.exe
```

WASM 版本：直接打开 `cas/html/calculator_single.html`。如果浏览器阻止本地脚本，可以在 `cas/html` 启动一个静态 HTTP 服务器。

计算器使用 `>` 作为提示符。输入表达式后按回车执行。

## 2. 数值和表达式

整数和分数默认保持精确：

```text
1/3 + 1/6
-> 1/2

10^100
-> 100000...
```

小数会创建任意精度近似值：

```text
0.1 + 0.2
```

符号直接写名称：

```text
x^2 + 2*x + 1
```

支持的运算符：

```text
+  -  *  /  ^
```

等式可以直接写成 `左边=右边`。内部会转换成 `左边-右边=0`，主要用于求解：

```text
solve(x*a+y=b, {x})
```

常量：

```text
pi  e  i
```

## 3. 精确和近似计算

`exact_expr` 适合整数、有理数、符号和精确根式。`expr` 可以包含 `Number` 近似值。

常用函数：

```text
sqrt(x)       abs(x)
exp(x)        expm1(x)
ln(x)         log(x)       log10(x)       log2(x)
sin(x) cos(x) tan(x)
asin(x) acos(x) atan(x)
sinh(x) cosh(x) tanh(x)
asinh(x) acosh(x) atanh(x)
Si(x) Ci(x) Ei(x) erf(x)
partial_gamma(a,x)
```

小数输入会触发近似计算。显式使用小数也可以强制近似路径：

```text
sin(1.)
```

## 4. 化简、展开和因式分解

```text
simplify((x^2-y^2)/(x-y))
-> x + y

expand((x+1)^3)
-> x^3 + 3*x^2 + 3*x + 1

factor(x^6+2*x^5+3*x^4+4*x^3+3*x^2+2*x+1)
-> (x + 1)^2*(x^2 + 1)^2

gcd(x^2-1, x^2-2*x+1)
-> x - 1
```

三角变换：

```text
trigexpand(sin(3*x))
trigreduce(sin(x)^2)
```

## 5. Groebner 基

`groebner` 使用 Buchberger 算法计算多项式组的 Groebner 基。系数可以是整数、有理数或符号表达式：

```text
groebner({x+y-a,x-y+b},{x,y})
```

结果是一个多项式列表，例如：

```text
{-a + x + y, b + x - y, -a - b + 2*y}
```

变量列表决定单项式顺序。当前实现适合中小型稀疏系统；指数过高、项数过多或正维系统可能超过预算。

## 6. 求解方程

单变量传统根列表：

```text
exact_solve(x^2-1, {x})
-> {-1, 1}
```

方程组返回规则映射：

```text
exact_solve({x+y=3,x-y=1},{x,y})
-> {{x -> 2, y -> 1}}
```

符号系数也支持：

```text
exact_solve({x+y-a,x-y+b},{x,y})
-> {{x -> (a-b)/2, y -> (a+b)/2}}
```

符号非线性系统会先计算符号 Groebner 基，再寻找单变量消元多项式并回代：

```text
exact_solve({x^2-a,x-y},{x,y})
```

`solve` 返回近似数值解，并会使用多个 Newton 初值。相同根会按照当前精度合并：

```text
solve({x^2+x-1-y,x^2+y^2-5},{x,y})
```

周期函数返回参数化解：

```text
solve(sin(x), {x})
-> {{x -> n*pi}}
```

## 7. 微积分和代换

```text
diff(x^3+sin(x), x)
int(2*x, x)
subs(x^2+y, x, 3)
```

`int`/`integrate` 当前覆盖部分规则积分和特殊函数节点；一般 Risch 积分仍有限制。

## 8. 假设和调试

变量假设：

```text
assume(x, positive)
sqrt(x^2)

assume(x, none)
```

计算器命令：

```text
!precision BITS   设置近似精度
!nodes            查看 arena 节点数
!gc               回收不可达节点
!dump [LIMIT]     输出节点信息
!tree [EXPR]      输出表达式 DAG
!info [EXPR]      输出节点统计
!time EXPR        测量表达式计算时间
!full             禁止简略显示，输出完整结果
!clear            清空上下文
!help             显示帮助
!quit             退出
```

## 9. C++ API

```cpp
#include "cas/prec_cas.hpp"

exact_context context;
exact_expr x = context.symbol("x");
exact_expr y = context.symbol("y");

exact_expr basis = context.groebner(
    {x + y - context.integer(3), x - y - context.integer(1)},
    {x, y});

exact_expr answer = context.exact_solve(
    {x + y - context.integer(3), x - y - context.integer(1)},
    {x, y});
```

`exact_expr` 是共享 arena 中节点的轻量句柄，不直接拥有独立的表达式树。保存长期结果时，应保留对应的 `exact_expr` 根；需要回收内存时使用 `context.compact(...)`。

## 10. 局限

- Groebner 基和符号求解受项数、次数和内存预算限制。
- 一般高次方程不保证输出根式表达式。
- 数值求解只返回找到并收敛的有限根，不表示完整的无穷解集。
- 近似计算的最后几位取决于设定精度和表达式的条件数。
