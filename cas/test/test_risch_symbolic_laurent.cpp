#include "../prec_cas.hpp"

#include <cassert>
#include <iostream>

int main(){
    exact_context context;
    exact_expr x = context.symbol("x");
    exact_expr a = context.symbol("a");
    exact_expr b = context.symbol("b");
    exact_expr log_x = context.natural_logarithm(x);
    exact_expr one_third = context.rational(
        precq_t(precn_t(1), precn_t(3)));

    exact_expr input = a * context.power(x, one_third) *
        context.power(log_x, context.integer(2)) + b * log_x / x;
    exact_expr expected = a * context.power(x,
        context.rational(precq_t(precn_t(4), precn_t(3)))) *
        (context.rational(precq_t(precn_t(3), precn_t(4))) *
             context.power(log_x, context.integer(2)) -
         context.rational(precq_t(precn_t(9), precn_t(8))) * log_x +
         context.rational(precq_t(precn_t(27), precn_t(32)))) +
        b * context.power(log_x, context.integer(2)) / context.integer(2);

    risch_result result = context.integrate_elementary(input, x);
    assert(result.status == risch_status::elementary);
    assert(result.remainder == context.integer(0));
    assert(result.conditions.empty());
    assert(context.simplify(result.elementary_part - expected) ==
           context.integer(0));
    assert(context.simplify(context.expand(
        context.differentiate(result.elementary_part, x) - input, 100000)) ==
        context.integer(0));

    std::cout << "symbolic Laurent-log RDE ok\n";
}
