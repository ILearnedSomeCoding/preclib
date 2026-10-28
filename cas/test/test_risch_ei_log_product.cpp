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
        const exact_expr &variable, const exact_expr &integrand,
        const exact_expr &normalized_integrand){
    exact_expr ordinary = context.integrate(integrand, variable);
    assert(ordinary.valid());
    assert(ordinary.operation() != exact_opcode::integral);
    exact_expr ordinary_error = context.simplify(context.expand(
        context.differentiate(ordinary, variable) - normalized_integrand,
        100000));
    if(ordinary_error != context.integer(0))
        std::fprintf(stderr, "ordinary primitive failed: %s -> %s; error %s\n",
            integrand.to_string().c_str(), ordinary.to_string().c_str(),
            ordinary_error.to_string().c_str());
    assert(ordinary_error == context.integer(0));
    risch_result strict = context.integrate_elementary(integrand, variable);
    if(strict.status != risch_status::elementary)
        std::fprintf(stderr, "elementary status %d: %s\n", (int)strict.status,
            strict.diagnostic.c_str());
    assert(strict.status == risch_status::elementary);
    assert(strict.remainder == context.integer(0));
    assert(context.simplify(context.expand(
        context.differentiate(strict.elementary_part, variable) -
            normalized_integrand, 100000)) == context.integer(0));
}

int main(){
    exact_context context;
    exact_expr x = context.symbol("x");
    check_elementary_primitive(context, x,
        x * context.exponential(-x), x * context.exponential(-x));
    exact_expr e_to_x = context.power(context.e(), x);
    check_elementary_primitive(context, x, x / e_to_x,
        x / context.exponential(x));
    check_elementary_primitive(context, x,
        x / context.power(context.e(), context.integer(2) * x),
        x / context.exponential(context.integer(2) * x));
    check_elementary_primitive(context, x,
        x * context.power(context.integer(2), -x),
        x * context.power(context.integer(2), -x));
    exact_expr exp_x = context.exponential(x);
    exact_expr mixed_exp_log = exp_x *
        (context.natural_logarithm(x) + context.integer(1) / x);
    check_elementary_primitive(context, x, mixed_exp_log, mixed_exp_log);
    exact_expr mixed_rational_exp_log = exp_x *
        (context.natural_logarithm(x) + context.integer(1) /
            context.power(x, context.integer(2)));
    check_elementary_primitive(context, x, mixed_rational_exp_log,
                                mixed_rational_exp_log);
    exact_expr log_x_plus_one = context.natural_logarithm(
        x + context.integer(1));
    exact_expr mixed_two_log_exp = exp_x *
        (context.natural_logarithm(x) * log_x_plus_one +
         log_x_plus_one / x + context.natural_logarithm(x) /
             (x + context.integer(1)));
    check_elementary_primitive(context, x, mixed_two_log_exp,
        mixed_two_log_exp);
    exact_expr rational_two_log_primitive = exp_x *
        context.natural_logarithm(x) * log_x_plus_one /
        (x + context.integer(2));
    exact_expr rational_two_log_integrand = context.differentiate(
        rational_two_log_primitive, x);
    check_elementary_primitive(context, x, rational_two_log_integrand,
                               rational_two_log_integrand);
    check_ei_reduction(context, x, x, context.integer(1));
    check_ei_reduction(context, x,
        context.integer(2) * x + context.integer(1), context.integer(1));
    check_ei_reduction(context, x,
        context.integer(3) * x - context.integer(2), context.integer(7));
    exact_expr nonlinear_ei_inner = context.power(x, context.integer(2)) +
                                    context.integer(1);
    exact_expr nonlinear_ei_rate = context.differentiate(
        nonlinear_ei_inner, x);
    exact_expr nonlinear_ei_integrand = nonlinear_ei_rate *
        context.exponential(nonlinear_ei_inner) *
        context.natural_logarithm(nonlinear_ei_inner);
    risch_result nonlinear_ei_result = context.integrate_elementary(
        nonlinear_ei_integrand, x);
    if(nonlinear_ei_result.status != risch_status::proven_nonelementary)
        std::fprintf(stderr, "nonlinear Ei status %d: %s\n",
            (int)nonlinear_ei_result.status,
            nonlinear_ei_result.diagnostic.c_str());
    assert(nonlinear_ei_result.status == risch_status::proven_nonelementary);
    assert(context.simplify(nonlinear_ei_result.elementary_part -
        context.exponential(nonlinear_ei_inner) *
            context.natural_logarithm(nonlinear_ei_inner)) == context.integer(0));
    assert(context.simplify(context.expand(
        context.differentiate(nonlinear_ei_result.elementary_part, x) +
        nonlinear_ei_result.remainder - nonlinear_ei_integrand, 100000)) ==
        context.integer(0));
    exact_expr rational_ei_inner =
        (context.power(x, context.integer(2)) + context.integer(1)) /
        (x + context.integer(1));
    exact_expr rational_ei_rate = context.differentiate(rational_ei_inner, x);
    exact_expr rational_ei_integrand = rational_ei_rate *
        context.exponential(rational_ei_inner) *
        context.natural_logarithm(rational_ei_inner);
    exact_expr rational_ei_primitive = context.integrate(
        rational_ei_integrand, x);
    assert(rational_ei_primitive.operation() != exact_opcode::integral);
    assert(context.simplify(context.expand(
        context.differentiate(rational_ei_primitive, x) -
        rational_ei_integrand, 100000)) == context.integer(0));
    exact_expr scaled_rational_ei_integrand =
        context.integer(7) / context.integer(3) * rational_ei_integrand;
    exact_expr scaled_rational_ei_primitive = context.integrate(
        scaled_rational_ei_integrand, x);
    assert(scaled_rational_ei_primitive.operation() != exact_opcode::integral);
    assert(context.simplify(context.expand(
        context.differentiate(scaled_rational_ei_primitive, x) -
        scaled_rational_ei_integrand, 100000)) == context.integer(0));
    risch_result rational_ei_result = context.integrate_elementary(
        rational_ei_integrand, x);
    if(rational_ei_result.status != risch_status::proven_nonelementary)
        std::fprintf(stderr, "rational Ei status %d: %s\n",
            (int)rational_ei_result.status,
            rational_ei_result.diagnostic.c_str());
    assert(rational_ei_result.status == risch_status::proven_nonelementary);
    assert(context.simplify(context.expand(
        context.differentiate(rational_ei_result.elementary_part, x) +
        rational_ei_result.remainder - rational_ei_integrand, 100000)) ==
        context.integer(0));
    risch_result scaled_rational_ei_result = context.integrate_elementary(
        scaled_rational_ei_integrand, x);
    assert(scaled_rational_ei_result.status ==
           risch_status::proven_nonelementary);
    assert(scaled_rational_ei_result.conditions.empty());
    assert(context.simplify(context.expand(
        context.differentiate(scaled_rational_ei_result.elementary_part, x) +
        scaled_rational_ei_result.remainder - scaled_rational_ei_integrand,
        100000)) == context.integer(0));
    exact_expr symbolic_ei_scale = context.symbol("risch_ei_chain_scale");
    exact_expr symbolic_ei_integrand = symbolic_ei_scale *
        rational_ei_integrand;
    exact_expr symbolic_ei_primitive = context.integrate(
        symbolic_ei_integrand, x);
    assert(symbolic_ei_primitive.operation() != exact_opcode::integral);
    assert(context.simplify(context.expand(
        context.differentiate(symbolic_ei_primitive, x) -
        symbolic_ei_integrand, 100000)) == context.integer(0));
    risch_result symbolic_ei_result = context.integrate_elementary(
        symbolic_ei_integrand, x);
    assert(symbolic_ei_result.status == risch_status::proven_nonelementary);
    assert(std::find(symbolic_ei_result.conditions.begin(),
        symbolic_ei_result.conditions.end(), symbolic_ei_scale) !=
        symbolic_ei_result.conditions.end());
    context.assume(symbolic_ei_scale, "positive");
    risch_result positive_symbolic_ei_result = context.integrate_elementary(
        symbolic_ei_integrand, x);
    assert(positive_symbolic_ei_result.status ==
           risch_status::proven_nonelementary);
    assert(positive_symbolic_ei_result.conditions.empty());
    exact_expr trigonometric_ei_inner = context.sine(x);
    exact_expr trigonometric_ei_integrand = context.cosine(x) *
        context.exponential(trigonometric_ei_inner) *
        context.natural_logarithm(trigonometric_ei_inner);
    exact_expr trigonometric_ei_primitive = context.integrate(
        trigonometric_ei_integrand, x);
    assert(trigonometric_ei_primitive.operation() != exact_opcode::integral);
    assert(context.simplify(context.expand(
        context.differentiate(trigonometric_ei_primitive, x) -
        trigonometric_ei_integrand, 100000)) == context.integer(0));
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
