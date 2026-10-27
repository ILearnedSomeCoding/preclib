#include"../prec_cas.hpp"

#include<cassert>
#include<cstdio>

static void check_ei_reduction(exact_context &context,
        const exact_expr &variable, const exact_expr &inner,
        const exact_expr &scale){
    exact_expr integrand = scale * context.exponential(inner) *
        context.natural_logarithm(inner);
    exact_expr primitive = context.integrate(integrand, variable);
    assert(primitive.valid());
    assert(primitive.operation() != exact_opcode::integral);
    assert(context.simplify(context.expand(
        context.differentiate(primitive, variable) - integrand,
        100000)) == context.integer(0));

    risch_result strict = context.integrate_elementary(integrand, variable);
    if(strict.status != risch_status::proven_nonelementary)
        std::fprintf(stderr, "strict status %d: %s\n", (int)strict.status,
            strict.diagnostic.c_str());
    assert(strict.status == risch_status::proven_nonelementary);
}

static void check_logarithmic_rde_obstruction(exact_context &context,
        const exact_expr &variable, const exact_expr &inner,
        const exact_expr &cofactor){
    exact_expr integrand = context.exponential(inner) * cofactor;
    risch_result strict = context.integrate_elementary(integrand, variable);
    if(strict.status != risch_status::proven_nonelementary)
        std::fprintf(stderr, "logarithmic RDE status %d: %s\n",
            (int)strict.status, strict.diagnostic.c_str());
    assert(strict.status == risch_status::proven_nonelementary);
    assert(strict.remainder != context.integer(0));
    assert(context.simplify(context.expand(
        context.differentiate(strict.elementary_part, variable) +
        strict.remainder - integrand, 100000)) == context.integer(0));
}

static void check_elementary_primitive(exact_context &context,
        const exact_expr &variable, const exact_expr &integrand){
    exact_expr ordinary = context.integrate(integrand, variable);
    assert(ordinary.valid());
    assert(ordinary.operation() != exact_opcode::integral);
    assert(context.simplify(context.expand(
        context.differentiate(ordinary, variable) - integrand,
        100000)) == context.integer(0));
    risch_result strict = context.integrate_elementary(integrand, variable);
    if(strict.status != risch_status::elementary)
        std::fprintf(stderr, "elementary status %d: %s\n", (int)strict.status,
            strict.diagnostic.c_str());
    assert(strict.status == risch_status::elementary);
    assert(strict.remainder == context.integer(0));
    assert(context.simplify(context.expand(
        context.differentiate(strict.elementary_part, variable) - integrand,
        100000)) == context.integer(0));
}

int main(){
    exact_context context;
    exact_expr x = context.symbol("x");
    check_elementary_primitive(context, x,
        x * context.exponential(-x));
    check_elementary_primitive(context, x,
        x * context.power(context.integer(2), -x));
    check_ei_reduction(context, x, x, context.integer(1));
    check_ei_reduction(context, x,
        context.integer(2) * x + context.integer(1), context.integer(1));
    check_ei_reduction(context, x,
        context.integer(3) * x - context.integer(2), context.integer(7));
    exact_expr log_x = context.natural_logarithm(x);
    check_logarithmic_rde_obstruction(context, x, x,
        context.power(log_x, context.integer(2)));
    check_logarithmic_rde_obstruction(context, x,
        context.integer(2) * x + context.integer(1),
        context.power(log_x, context.integer(3)) +
            context.integer(3) * log_x + context.integer(2));
    exact_expr affine_inner = context.integer(2) * x + context.integer(1);
    exact_expr affine_log_polynomial = context.power(log_x, context.integer(3)) +
        context.integer(3) * log_x + context.integer(2);
    risch_result split_constant = context.integrate_elementary(
        context.exponential(affine_inner) * affine_log_polynomial, x);
    assert(split_constant.status == risch_status::proven_nonelementary);
    assert(split_constant.elementary_part == context.exponential(affine_inner));
    exact_expr rate = context.symbol("risch_rate");
    exact_expr parameter_inner = rate * x + context.integer(1);
    exact_expr parameter_cofactor = context.power(log_x, context.integer(2)) +
        context.integer(2) * log_x + context.integer(3);
    exact_expr parameter_integrand = context.exponential(parameter_inner) *
        parameter_cofactor;
    risch_result parameter_result = context.integrate_elementary(
        parameter_integrand, x);
    assert(parameter_result.status == risch_status::proven_nonelementary);
    assert(parameter_result.conditions.size() == 1);
    assert(parameter_result.conditions[0] == rate);
    assert(context.simplify(parameter_result.elementary_part -
        context.integer(3) / rate * context.exponential(parameter_inner)) ==
        context.integer(0));
    assert(context.simplify(context.expand(
        context.differentiate(parameter_result.elementary_part, x) +
        parameter_result.remainder - parameter_integrand, 100000)) ==
        context.integer(0));

    exact_expr leading_coefficient = context.symbol("log_poly_lead");
    exact_expr parameter_lead_integrand = context.exponential(x) *
        (leading_coefficient * log_x + context.integer(1));
    risch_result parameter_lead_result = context.integrate_elementary(
        parameter_lead_integrand, x);
    assert(parameter_lead_result.status == risch_status::proven_nonelementary);
    assert(parameter_lead_result.conditions.size() == 1);
    assert(parameter_lead_result.conditions[0] == leading_coefficient);
    assert(parameter_lead_result.elementary_part == context.exponential(x));

    exact_expr positive_rate = context.symbol("risch_positive_rate");
    context.assume(positive_rate, "positive");
    risch_result assumed_rate_result = context.integrate_elementary(
        context.exponential(positive_rate * x) * context.power(log_x,
            context.integer(2)), x);
    assert(assumed_rate_result.status == risch_status::proven_nonelementary);
    assert(assumed_rate_result.conditions.empty());

    exact_expr shifted_log = context.natural_logarithm(x + context.integer(1));
    check_logarithmic_rde_obstruction(context, x, x,
        context.power(shifted_log, context.integer(2)));
    exact_expr rational_log_argument =
        (context.power(x, context.integer(2)) + context.integer(1)) /
        (x + context.integer(2));
    exact_expr rational_log = context.natural_logarithm(rational_log_argument);
    check_logarithmic_rde_obstruction(context, x,
        context.integer(2) * x + context.integer(1),
        context.power(rational_log, context.integer(3)) +
            context.integer(3) * rational_log + context.integer(2));
    std::puts("logarithmic hyperexponential Risch reductions ok");
}
