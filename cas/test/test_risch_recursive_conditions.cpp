#include"../src/prec_cas.cpp"

#include<cassert>
#include<cstdio>

int main(){
    exact_context context;
    exact_expr x = context.symbol("x");
    exact_expr slope = context.symbol("_risch_recursive_condition_slope");
    exact_expr lower_log = context.natural_logarithm(x);
    exact_expr affine_log = context.natural_logarithm(
        context.integer(1) + slope * x);
    exact_expr original = lower_log * affine_log / slope;
    exact_expr input = context.differentiate(original, x);

    std::puts("checking recursive coefficient integration");
    std::fflush(stdout);
    std::vector<exact_expr> conditions;
    exact_expr candidate = integration_recursive_primitive_polynomial(
        context, input, x, risch_options(), &conditions);
    assert(candidate.valid());
    assert(std::find(conditions.begin(), conditions.end(), slope) !=
           conditions.end());
    exact_expr error = context.simplify(context.expand(
        context.differentiate(candidate, x) - input, 100000));
    assert(error == context.integer(0));

    std::puts("checking public strict Risch result");
    std::fflush(stdout);
    risch_result strict = context.integrate_elementary(input, x);
    assert(strict.status == risch_status::elementary);
    assert(strict.remainder == context.integer(0));
    assert(std::find(strict.conditions.begin(), strict.conditions.end(), slope) !=
           strict.conditions.end());
    std::puts("recursive Risch conditions preserved");
}
