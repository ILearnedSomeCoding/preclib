# Exact CAS Calculator

Build from the repository root:

```powershell
clang++ -O3 -mavx2 -std=c++17 cas\calculator.cpp cas\src\*.cpp src\*.cpp -o cas\calculator.exe
```

Integer literals and integer fractions remain exact. Decimal literals and
numeric transcendental functions use `Number` at the selected precision.

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
> 9^0.5
3
> approx(1/3)
0.3333333333333333333333333333333333333333333333333333333333333333333333333333
```

Commands:

```text
!precision 512
!nodes
!clear
!help
!quit
```

CAS tests are built separately from the numeric core:

```powershell
clang++ -O3 -mavx2 -std=c++17 cas\test\test_cas.cpp cas\src\*.cpp src\*.cpp -o cas\test\test_cas.exe
clang++ -O3 -mavx2 -std=c++17 cas\test\test_expr.cpp cas\src\*.cpp src\*.cpp -o cas\test\test_expr.exe
```
