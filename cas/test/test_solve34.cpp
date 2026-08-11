#include"../prec_cas.hpp"

#include<cassert>
#include<iostream>

int main(){
    exact_context context;
    exact_expr x = context.symbol("x");
    exact_expr one = context.integer(1);
    exact_expr quadratic = context.exact_solve(pow(x, context.integer(2)) + one, {x});
    exact_expr cubic = context.exact_solve(pow(x, context.integer(3)) - one, {x});
    exact_expr repeated_cubic = context.exact_solve(pow(x, context.integer(3)), {x});
    exact_expr quartic = context.exact_solve(pow(x, context.integer(4)) - one, {x});
    exact_expr approximate_cubic = context.solve(pow(x, context.integer(3)) - one,
                                                  {x}, 128);
    exact_expr distinct_cubic = context.solve(
        pow(x, context.integer(3)) - context.integer(6) * pow(x, context.integer(2)) +
        context.integer(11) * x - context.integer(6), {x}, 128);
    exact_expr distinct_quartic = context.solve(
        pow(x, context.integer(4)) - context.integer(10) * pow(x, context.integer(3)) +
        context.integer(35) * pow(x, context.integer(2)) -
        context.integer(50) * x + context.integer(24), {x}, 128);
    std::cout << "quadratic " << quadratic.to_string() << '\n';
    std::cout << "cubic " << cubic.to_string() << '\n';
    std::cout << "repeated_cubic " << repeated_cubic.to_string() << '\n';
    std::cout << "quartic " << quartic.to_string() << '\n';
    std::cout << "approximate_cubic " << approximate_cubic.to_string() << '\n';
    std::cout << "distinct_cubic " << distinct_cubic.to_string() << '\n';
    std::cout << "distinct_quartic " << distinct_quartic.to_string() << '\n';
    assert(quadratic.operand_count() == 2);
    assert(cubic.operand_count() == 3);
    assert(repeated_cubic.to_string() == "{0}");
    assert(quartic.operand_count() == 4);
    std::cout << "solve34 ok\n";
    return 0;
}
