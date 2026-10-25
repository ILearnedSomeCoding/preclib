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

    std::puts("checking legacy integrate condition handling");
    std::fflush(stdout);
    exact_expr ordinary = context.integrate(input, x);
    assert(ordinary.operation() == exact_opcode::integral);

    std::puts("checking symbolic leading coefficient in exponential RDE");
    std::fflush(stdout);
    exact_expr exponential = context.exponential(x);
    exact_expr leading = context.symbol("_risch_rational_leading");
    exact_expr rational_primitive = exponential / (leading * x);
    exact_expr rational_input = context.differentiate(rational_primitive, x);
    risch_result rational_result = context.integrate_elementary(
        rational_input, x);
    if(rational_result.status != risch_status::elementary)
        std::fprintf(stderr, "symbolic-leading RDE status %d: %s\n",
            (int)rational_result.status, rational_result.diagnostic.c_str());
    assert(rational_result.status == risch_status::elementary);
    assert(rational_result.remainder == context.integer(0));
    assert(std::find(rational_result.conditions.begin(),
                     rational_result.conditions.end(), leading) !=
           rational_result.conditions.end());
    exact_expr rational_error = context.simplify(context.expand(
        context.differentiate(rational_result.elementary_part, x) -
        rational_input, 100000));
    assert(rational_error == context.integer(0));

    exact_expr regular_primitive = exponential /
        (leading * x + context.integer(1));
    exact_expr regular_input = context.differentiate(regular_primitive, x);
    risch_result regular_result = context.integrate_elementary(regular_input, x);
    assert(regular_result.status == risch_status::elementary);
    assert(std::find(regular_result.conditions.begin(),
                     regular_result.conditions.end(), leading) ==
           regular_result.conditions.end());
    assert(context.simplify(context.expand(
        context.differentiate(regular_result.elementary_part, x) -
        regular_input, 100000)) == context.integer(0));

    std::puts("checking symbolic exponential rate in rational RDE");
    std::fflush(stdout);
    exact_expr rate = context.symbol("_risch_rational_rate");
    exact_expr rate_exponential = context.exponential(rate * x);
    exact_expr rate_pole_primitive = rate_exponential / (rate * x);
    exact_expr rate_pole_input = context.differentiate(rate_pole_primitive, x);
    risch_result rate_pole_result = context.integrate_elementary(
        rate_pole_input, x);
    if(rate_pole_result.status != risch_status::elementary)
        std::fprintf(stderr, "symbolic-rate RDE status %d: %s\n",
            (int)rate_pole_result.status, rate_pole_result.diagnostic.c_str());
    assert(rate_pole_result.status == risch_status::elementary);
    assert(std::find(rate_pole_result.conditions.begin(),
                     rate_pole_result.conditions.end(), rate) !=
           rate_pole_result.conditions.end());
    assert(context.simplify(context.expand(
        context.differentiate(rate_pole_result.elementary_part, x) -
        rate_pole_input, 100000)) == context.integer(0));

    exact_expr rate_regular_primitive = rate_exponential /
        (rate * x + context.integer(1));
    exact_expr rate_regular_input = context.differentiate(
        rate_regular_primitive, x);
    risch_result rate_regular_result = context.integrate_elementary(
        rate_regular_input, x);
    assert(rate_regular_result.status == risch_status::elementary);
    assert(std::find(rate_regular_result.conditions.begin(),
                     rate_regular_result.conditions.end(), rate) ==
           rate_regular_result.conditions.end());
    assert(context.simplify(context.expand(
        context.differentiate(rate_regular_result.elementary_part, x) -
        rate_regular_input, 100000)) == context.integer(0));
    std::puts("recursive Risch conditions preserved");
}
