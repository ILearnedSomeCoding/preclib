#include "../prec_cas.hpp"

#include <algorithm>
#include <cassert>
#include <iostream>

int main(){
    exact_context context;
    exact_expr x = context.symbol("x");
    exact_expr a = context.symbol("a");
    exact_expr b = context.symbol("b");
    exact_expr t = context.natural_logarithm(x);
    exact_expr exponent = context.power(t, context.integer(3));
    exact_expr forcing = context.integer(3) * a * context.power(t,
        context.integer(3)) + context.integer(3) * b *
        context.power(t, context.integer(2)) + a;
    exact_expr input = context.exponential(exponent) * forcing / x;
    exact_expr expected = context.exponential(exponent) * (a * t + b);

    risch_result result = context.integrate_elementary(input, x);
    assert(result.status == risch_status::elementary);
    assert(result.remainder == context.integer(0));
    assert(result.conditions.empty());
    assert(context.simplify(result.elementary_part - expected) ==
           context.integer(0));
    assert(context.simplify(context.expand(
        context.differentiate(result.elementary_part, x) - input, 100000)) ==
        context.integer(0));

    exact_expr underdetermined_input = context.exponential(exponent) * a * t / x;
    risch_result underdetermined = context.integrate_elementary(
        underdetermined_input, x);
    if(underdetermined.status == risch_status::proven_nonelementary)
        assert(std::find(underdetermined.conditions.begin(),
                         underdetermined.conditions.end(), a) !=
               underdetermined.conditions.end());

    exact_expr c = context.symbol("c");
    exact_expr u = context.symbol("u");
    exact_expr v = context.symbol("v");
    exact_expr parameterized_exponent = a * context.power(t,
        context.integer(3)) + c * context.power(t, context.integer(2));
    exact_expr parameterized_cofactor =
        context.integer(3) * a * u * context.power(t, context.integer(3)) +
        (context.integer(3) * a * v + context.integer(2) * c * u) *
            context.power(t, context.integer(2)) +
        context.integer(2) * c * v * t + u;
    exact_expr parameterized_input =
        context.exponential(parameterized_exponent) *
        parameterized_cofactor / x;
    exact_expr parameterized_expected = context.exponential(
        parameterized_exponent) * (u * t + v);
    risch_result parameterized = context.integrate_elementary(
        parameterized_input, x);
    assert(parameterized.status == risch_status::elementary);
    assert(context.simplify(parameterized.elementary_part -
                            parameterized_expected) == context.integer(0));
    assert(std::find(parameterized.conditions.begin(),
                      parameterized.conditions.end(), a) !=
           parameterized.conditions.end());
    assert(context.simplify(context.expand(
        context.differentiate(parameterized.elementary_part, x) -
        parameterized_input, 100000)) == context.integer(0));
    context.assume(a, "positive");
    risch_result assumed_parameterized = context.integrate_elementary(
        parameterized_input, x);
    assert(assumed_parameterized.status == risch_status::elementary);
    assert(assumed_parameterized.conditions.empty());

    std::cout << "symbolic logarithmic hyperexponential RDE ok\n";
}
