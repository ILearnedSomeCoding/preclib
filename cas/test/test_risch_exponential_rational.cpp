#include"../prec_cas.hpp"

#include<algorithm>
#include<cassert>
#include<cstdio>

int main(){
    exact_context context;
    exact_expr x = context.symbol("x");
    exact_expr a = context.symbol("a");
    exact_expr b = context.symbol("b");
    exact_expr q = context.symbol("q");
    exact_expr r = context.symbol("r");
    context.assume(q, "positive");
    context.assume(r, "positive");
    exact_expr t = context.exponential(x);
    risch_options options;
    options.maximum_recursion_depth = 1;

    exact_expr inputs[] = {
        context.integer(1) / (context.integer(1) + t +
            context.exponential(context.integer(2) * x)),
        context.integer(1) / (context.integer(1) + t +
            context.exponential(-x)),
        context.integer(1) / (context.integer(1) +
            context.exponential(x / context.integer(2)) + t)
    };
    for(const exact_expr &input : inputs){
        risch_result result = context.integrate_elementary(input, x, options);
        assert(result.status == risch_status::elementary);
        assert(result.remainder == context.integer(0));
    }
    exact_expr two_to_x = context.power(context.integer(2), x);
    risch_result two_to_x_result = context.integrate_elementary(two_to_x, x);
    assert(two_to_x_result.status == risch_status::elementary);
    assert(context.simplify(context.differentiate(
        two_to_x_result.elementary_part, x) - two_to_x) == context.integer(0));
    exact_expr two_to_x_legacy = context.integrate(two_to_x, x);
    assert(two_to_x_legacy.operation() != exact_opcode::integral);
    assert(context.simplify(context.differentiate(two_to_x_legacy, x) -
        two_to_x) == context.integer(0));
    exact_expr two_to_minus_x = context.power(context.integer(2), -x);
    exact_expr x_over_two_power = x * two_to_minus_x;
    risch_result x_over_two_power_result = context.integrate_elementary(
        x_over_two_power, x);
    assert(x_over_two_power_result.status == risch_status::elementary);
    exact_expr ln_two_for_negative_power =
        context.natural_logarithm(context.integer(2));
    exact_expr x_over_two_power_expected =
        (-x / ln_two_for_negative_power - context.integer(1) /
            context.power(ln_two_for_negative_power, context.integer(2))) *
        two_to_minus_x;
    assert(context.simplify(x_over_two_power_result.elementary_part -
        x_over_two_power_expected) == context.integer(0));
    assert(context.simplify(context.expand(context.differentiate(
        x_over_two_power_result.elementary_part, x) - x_over_two_power,
        100000)) == context.integer(0));
    assert(context.integrate(x_over_two_power, x).operation() !=
        exact_opcode::integral);
    exact_expr q_to_minus_x = context.power(q, -x);
    exact_expr x_over_q_power = x * q_to_minus_x;
    risch_result x_over_q_power_result = context.integrate_elementary(
        x_over_q_power, x);
    assert(x_over_q_power_result.status == risch_status::elementary);
    assert(x_over_q_power_result.conditions.size() == 1);
    exact_expr minus_ln_q = -context.natural_logarithm(q);
    exact_expr ln_q_for_negative_power = context.natural_logarithm(q);
    exact_expr rate_condition_error = context.simplify(
        x_over_q_power_result.conditions[0] - minus_ln_q);
    exact_expr opposite_rate_condition_error = context.simplify(
        x_over_q_power_result.conditions[0] - ln_q_for_negative_power);
    assert(rate_condition_error == context.integer(0) ||
           opposite_rate_condition_error == context.integer(0));
    exact_expr x_over_q_power_expected =
        (-x / ln_q_for_negative_power - context.integer(1) /
            context.power(ln_q_for_negative_power, context.integer(2))) *
        q_to_minus_x;
    assert(context.simplify(x_over_q_power_result.elementary_part -
        x_over_q_power_expected) == context.integer(0));
    assert(context.simplify(context.expand(context.differentiate(
        x_over_q_power_result.elementary_part, x) - x_over_q_power,
        100000)) == context.integer(0));
    exact_expr x_over_q_power_legacy = context.integrate(x_over_q_power, x);
    assert(context.simplify(context.expand(context.differentiate(
        x_over_q_power_legacy, x) - x_over_q_power, 100000)) ==
        context.integer(0));
    exact_expr polynomial_times_two_to_x = x * two_to_x;
    risch_result polynomial_power_result = context.integrate_elementary(
        polynomial_times_two_to_x, x);
    assert(polynomial_power_result.status == risch_status::elementary);
    exact_expr polynomial_power_error = context.simplify(context.expand(
        context.differentiate(polynomial_power_result.elementary_part, x) -
        polynomial_times_two_to_x, 100000));
    assert(polynomial_power_error == context.integer(0));
    exact_expr polynomial_power_legacy = context.integrate(
        polynomial_times_two_to_x, x);
    assert(polynomial_power_legacy.operation() != exact_opcode::integral);
    assert(context.simplify(context.expand(
        context.differentiate(polynomial_power_legacy, x) -
        polynomial_times_two_to_x, 100000)) == context.integer(0));
    exact_expr polynomial_over_two_to_x = x / two_to_x;
    risch_result reciprocal_polynomial_power = context.integrate_elementary(
        polynomial_over_two_to_x, x);
    assert(reciprocal_polynomial_power.status == risch_status::elementary);
    assert(reciprocal_polynomial_power.remainder == context.integer(0));
    exact_expr normalized_reciprocal_input = x * context.power(
        context.integer(2), -x);
    exact_expr reciprocal_power_error = context.simplify(context.expand(
        context.differentiate(reciprocal_polynomial_power.elementary_part, x) -
        normalized_reciprocal_input, 100000));
    assert(reciprocal_power_error == context.integer(0));
    exact_expr reciprocal_polynomial_power_legacy = context.integrate(
        polynomial_over_two_to_x, x);
    assert(reciprocal_polynomial_power_legacy.operation() !=
        exact_opcode::integral);
    exact_expr legacy_reciprocal_error = context.simplify(context.expand(
        context.differentiate(reciprocal_polynomial_power_legacy, x) -
        polynomial_over_two_to_x, 100000));
    assert(legacy_reciprocal_error == context.integer(0));
    exact_expr shifted_parameter_pole = x + a;
    exact_expr parameter_pole_input = context.exponential(x) *
        (context.integer(1) / shifted_parameter_pole -
         context.integer(1) /
             context.power(shifted_parameter_pole, context.integer(2)));
    risch_result parameter_pole_result = context.integrate_elementary(
        parameter_pole_input, x);
    assert(parameter_pole_result.status == risch_status::elementary);
    assert(parameter_pole_result.remainder == context.integer(0));
    assert(context.simplify(parameter_pole_result.elementary_part -
        context.exponential(x) / shifted_parameter_pole) == context.integer(0));
    assert(context.simplify(context.expand(context.differentiate(
        parameter_pole_result.elementary_part, x) - parameter_pole_input,
        100000)) == context.integer(0));
    exact_expr quadratic_reciprocal_input = x /
        context.power(context.integer(2), context.power(x, context.integer(2)));
    exact_expr normalized_quadratic_reciprocal = x * context.power(
        context.integer(2), -context.power(x, context.integer(2)));
    risch_result quadratic_reciprocal_result = context.integrate_elementary(
        quadratic_reciprocal_input, x);
    assert(quadratic_reciprocal_result.status == risch_status::elementary);
    assert(quadratic_reciprocal_result.remainder == context.integer(0));
    assert(context.simplify(context.expand(
        context.differentiate(quadratic_reciprocal_result.elementary_part, x) -
        normalized_quadratic_reciprocal, 100000)) == context.integer(0));
    exact_expr quadratic_power_input = x * context.power(
        context.integer(2), context.power(x, context.integer(2)));
    risch_result quadratic_power_result = context.integrate_elementary(
        quadratic_power_input, x);
    assert(quadratic_power_result.status == risch_status::elementary);
    assert(context.simplify(context.expand(
        context.differentiate(quadratic_power_result.elementary_part, x) -
        quadratic_power_input, 100000)) == context.integer(0));
    exact_expr x_squared = context.power(x, context.integer(2));
    exact_expr two_to_x_squared = context.power(context.integer(2), x_squared);
    exact_expr quadratic_ln_two = context.natural_logarithm(context.integer(2));
    exact_expr quadratic_rational_rde_input =
        (context.integer(2) * quadratic_ln_two - context.integer(1) /
            context.power(x, context.integer(2))) * two_to_x_squared;
    risch_result quadratic_rational_rde_result = context.integrate_elementary(
        quadratic_rational_rde_input, x);
    assert(quadratic_rational_rde_result.status == risch_status::elementary);
    assert(quadratic_rational_rde_result.remainder == context.integer(0));
    assert(context.simplify(context.expand(context.differentiate(
        quadratic_rational_rde_result.elementary_part, x) -
        quadratic_rational_rde_input, 100000)) == context.integer(0));
    exact_expr x_squared_plus_one = x_squared + context.integer(1);
    exact_expr quadratic_repeated_pole_rde_input =
        (context.integer(2) * x * quadratic_ln_two / x_squared_plus_one -
         context.integer(2) * x /
             context.power(x_squared_plus_one, context.integer(2))) *
        two_to_x_squared;
    risch_result quadratic_repeated_pole_rde_result = context.integrate_elementary(
        quadratic_repeated_pole_rde_input, x);
    assert(quadratic_repeated_pole_rde_result.status == risch_status::elementary);
    assert(context.simplify(context.expand(context.differentiate(
        quadratic_repeated_pole_rde_result.elementary_part, x) -
        quadratic_repeated_pole_rde_input, 100000)) == context.integer(0));
    exact_expr quadratic_reciprocal_legacy = context.integrate(
        quadratic_reciprocal_input, x);
    assert(quadratic_reciprocal_legacy.operation() != exact_opcode::integral);
    assert(context.simplify(context.expand(
        context.differentiate(quadratic_reciprocal_legacy, x) -
        quadratic_reciprocal_input, 100000)) == context.integer(0));
    exact_expr cubic_power_coefficient = (a + context.integer(1)) *
        context.power(x, context.integer(3)) -
        context.integer(2) * x + context.integer(5);
    exact_expr cubic_power_input = cubic_power_coefficient * two_to_x;
    risch_result cubic_power_result = context.integrate_elementary(
        cubic_power_input, x);
    assert(cubic_power_result.status == risch_status::elementary);
    assert(context.simplify(context.expand(
        context.differentiate(cubic_power_result.elementary_part, x) -
        cubic_power_input, 100000)) == context.integer(0));
    risch_options constant_rate_tiny_budget;
    constant_rate_tiny_budget.maximum_matrix_entries = 1;
    assert(context.integrate_elementary(cubic_power_input, x,
        constant_rate_tiny_budget).status == risch_status::resource_limit);
    exact_expr shifted_power = context.power(context.integer(2),
        context.integer(3) * x + context.integer(1));
    risch_result shifted_power_result = context.integrate_elementary(
        shifted_power, x);
    assert(shifted_power_result.status == risch_status::elementary);
    assert(context.simplify(context.differentiate(
        shifted_power_result.elementary_part, x) - shifted_power) ==
        context.integer(0));
    exact_expr e_to_x = context.power(context.e(), x);
    risch_result e_to_x_result = context.integrate_elementary(e_to_x, x);
    assert(e_to_x_result.status == risch_status::elementary);
    assert(context.simplify(context.differentiate(
        e_to_x_result.elementary_part, x) - context.exponential(x)) ==
        context.integer(0));
    exact_expr e_power_logistic = context.integer(1) /
        (context.power(context.e(), x) + context.integer(1));
    risch_result e_power_logistic_result = context.integrate_elementary(
        e_power_logistic, x);
    assert(e_power_logistic_result.status == risch_status::elementary);
    assert(e_power_logistic_result.remainder == context.integer(0));
    assert(e_power_logistic_result.elementary_part == x -
        context.natural_logarithm(context.exponential(x) +
                                  context.integer(1)));
    exact_expr scaled_rational_exponential = context.e() *
        context.exponential(x) * x /
        context.power(x + context.integer(1), context.integer(2));
    risch_result scaled_rational_exponential_result =
        context.integrate_elementary(scaled_rational_exponential, x);
    assert(scaled_rational_exponential_result.status ==
        risch_status::elementary);
    exact_expr scaled_rational_exponential_expected = context.e() *
        context.exponential(x) / (x + context.integer(1));
    assert(context.simplify(scaled_rational_exponential_result.elementary_part -
        scaled_rational_exponential_expected) == context.integer(0));
    exact_expr scaled_rational_exponential_derivative = context.differentiate(
        scaled_rational_exponential_result.elementary_part, x);
    exact_expr scaled_rational_exponential_derivative_form = context.e() *
        context.exponential(x) / (x + context.integer(1)) -
        context.e() * context.exponential(x) /
            context.power(x + context.integer(1), context.integer(2));
    assert(context.simplify(scaled_rational_exponential_derivative -
        scaled_rational_exponential_derivative_form) == context.integer(0));
    assert(context.simplify((x + context.integer(1)) - context.integer(1) - x) ==
        context.integer(0));
    exact_expr symbolic_scalar_exponential = a * context.exponential(x) * x /
        context.power(x + context.integer(1), context.integer(2));
    risch_result symbolic_scalar_exponential_result =
        context.integrate_elementary(symbolic_scalar_exponential, x);
    assert(symbolic_scalar_exponential_result.status ==
        risch_status::elementary);
    assert(symbolic_scalar_exponential_result.conditions.empty());
    exact_expr symbolic_scalar_exponential_expected = a *
        context.exponential(x) / (x + context.integer(1));
    assert(context.simplify(symbolic_scalar_exponential_result.elementary_part -
        symbolic_scalar_exponential_expected) == context.integer(0));
    exact_expr algebraic_scalar = context.square_root(context.integer(2));
    exact_expr algebraic_scalar_exponential = algebraic_scalar *
        context.exponential(x) * x /
        context.power(x + context.integer(1), context.integer(2));
    risch_result algebraic_scalar_exponential_result =
        context.integrate_elementary(algebraic_scalar_exponential, x);
    assert(algebraic_scalar_exponential_result.status ==
        risch_status::elementary);
    assert(algebraic_scalar_exponential_result.conditions.empty());
    exact_expr algebraic_scalar_exponential_expected = algebraic_scalar *
        context.exponential(x) / (x + context.integer(1));
    assert(context.simplify(
        algebraic_scalar_exponential_result.elementary_part -
        algebraic_scalar_exponential_expected) == context.integer(0));
    exact_expr algebraic_multi_coefficient_exponential = algebraic_scalar *
        context.exponential(x) *
        (context.power(x, context.integer(2)) +
         context.integer(3) * x + context.integer(1)) /
        context.power(x + context.integer(1), context.integer(2));
    risch_result algebraic_multi_coefficient_result =
        context.integrate_elementary(algebraic_multi_coefficient_exponential,
                                     x);
    assert(algebraic_multi_coefficient_result.status ==
        risch_status::elementary);
    assert(algebraic_multi_coefficient_result.conditions.empty());
    exact_expr algebraic_multi_coefficient_expected = algebraic_scalar *
        context.exponential(x) * (x + context.integer(2)) /
        (x + context.integer(1));
    assert(context.simplify(
        algebraic_multi_coefficient_result.elementary_part -
        algebraic_multi_coefficient_expected) == context.integer(0));
    exact_expr x_plus_one = x + context.integer(1);
    exact_expr scaled_multi_coefficient_exponential = a *
        context.exponential(x) *
        (context.power(x, context.integer(2)) +
         context.integer(3) * x + context.integer(1)) /
        context.power(x_plus_one, context.integer(2));
    risch_result scaled_multi_coefficient_result = context.integrate_elementary(
        scaled_multi_coefficient_exponential, x);
    assert(scaled_multi_coefficient_result.status == risch_status::elementary);
    assert(scaled_multi_coefficient_result.conditions.empty());
    exact_expr scaled_multi_coefficient_expected = a * context.exponential(x) *
        (x + context.integer(2)) / x_plus_one;
    assert(context.simplify(scaled_multi_coefficient_result.elementary_part -
        scaled_multi_coefficient_expected) == context.integer(0));
    assert(context.simplify(context.substitute(
        scaled_multi_coefficient_result.elementary_part, a,
        context.integer(0))) == context.integer(0));
    exact_expr symbolic_logarithmic_integrand =
        (a * x + b) * context.natural_logarithm(x);
    risch_result symbolic_logarithmic_result = context.integrate_elementary(
        symbolic_logarithmic_integrand, x);
    assert(symbolic_logarithmic_result.status == risch_status::elementary);
    assert(symbolic_logarithmic_result.remainder == context.integer(0));
    exact_expr symbolic_logarithmic_expected =
        (a * context.power(x, context.integer(2)) / context.integer(2) +
         b * x) * context.natural_logarithm(x) -
        a * context.power(x, context.integer(2)) / context.integer(4) - b * x;
    assert(context.simplify(context.expand(
        symbolic_logarithmic_result.elementary_part -
        symbolic_logarithmic_expected, 100000)) == context.integer(0));
    assert(context.simplify(context.expand(
        context.differentiate(symbolic_logarithmic_result.elementary_part, x) -
        symbolic_logarithmic_integrand, 100000)) == context.integer(0));
    exact_expr symbolic_exponential_polynomial = context.exponential(x) *
        (a * x + b);
    risch_result symbolic_exponential_polynomial_result =
        context.integrate_elementary(symbolic_exponential_polynomial, x);
    assert(symbolic_exponential_polynomial_result.status ==
        risch_status::elementary);
    assert(symbolic_exponential_polynomial_result.conditions.empty());
    exact_expr symbolic_exponential_polynomial_expected = context.exponential(x) *
        (a * x + b - a);
    assert(context.simplify(
        symbolic_exponential_polynomial_result.elementary_part -
        symbolic_exponential_polynomial_expected) == context.integer(0));
    exact_expr x_over_e_power = x / context.power(context.e(), x);
    risch_result x_over_e_power_result = context.integrate_elementary(
        x_over_e_power, x);
    assert(x_over_e_power_result.status == risch_status::elementary);
    assert(x_over_e_power_result.remainder == context.integer(0));
    assert(x_over_e_power_result.elementary_part ==
        (-x - context.integer(1)) / context.exponential(x));
    exact_expr x_over_e_power_legacy = context.integrate(x_over_e_power, x);
    assert(x_over_e_power_legacy.operation() != exact_opcode::integral);
    exact_expr normalized_e_reciprocal = x / context.exponential(x);
    assert(context.simplify(context.expand(context.differentiate(
        x_over_e_power_legacy, x) - normalized_e_reciprocal,
        100000)) == context.integer(0));
    exact_expr nested_e_power = context.power(context.e(),
        context.power(context.e(), x));
    exact_expr nested_e_power_input = nested_e_power *
        context.power(context.e(), x);
    risch_result nested_e_power_result = context.integrate_elementary(
        nested_e_power_input, x);
    assert(nested_e_power_result.status == risch_status::elementary);
    assert(nested_e_power_result.remainder == context.integer(0));
    assert(nested_e_power_result.elementary_part ==
        context.exponential(context.exponential(x)));
    exact_expr mixed_exponential_log_input = context.exponential(x) *
        (context.natural_logarithm(x) + context.integer(1) / x);
    risch_result mixed_exponential_log_result = context.integrate_elementary(
        mixed_exponential_log_input, x);
    assert(mixed_exponential_log_result.status == risch_status::elementary);
    assert(mixed_exponential_log_result.remainder == context.integer(0));
    assert(mixed_exponential_log_result.elementary_part ==
        context.exponential(x) * context.natural_logarithm(x));
    exact_expr e_over_x = context.power(context.e(), x) / x;
    risch_result e_over_x_result = context.integrate_elementary(e_over_x, x);
    assert(e_over_x_result.status == risch_status::proven_nonelementary);
    exact_expr three_to_x = context.power(context.integer(3), x);
    exact_expr mixed_base_exponential = x * two_to_x * three_to_x;
    risch_result mixed_base_result = context.integrate_elementary(
        mixed_base_exponential, x);
    assert(mixed_base_result.status == risch_status::elementary);
    exact_expr mixed_base_rate = context.natural_logarithm(
        context.integer(2)) + context.natural_logarithm(context.integer(3));
    exact_expr mixed_base_expected =
        (x / mixed_base_rate - context.integer(1) /
            context.power(mixed_base_rate, context.integer(2))) *
        two_to_x * three_to_x;
    assert(context.simplify(mixed_base_result.elementary_part -
        mixed_base_expected) == context.integer(0));
    assert(mixed_base_result.conditions.empty());
    exact_expr three_to_x_squared = context.power(
        context.integer(3), x_squared);
    exact_expr aligned_base_input = x * two_to_x_squared *
        three_to_x_squared;
    risch_result aligned_base_result = context.integrate_elementary(
        aligned_base_input, x);
    assert(aligned_base_result.status == risch_status::elementary);
    assert(aligned_base_result.remainder == context.integer(0));
    exact_expr aligned_base_log_sum = context.natural_logarithm(
        context.integer(2)) + context.natural_logarithm(context.integer(3));
    exact_expr aligned_base_expected = two_to_x_squared *
        three_to_x_squared / (context.integer(2) * aligned_base_log_sum);
    assert(aligned_base_result.elementary_part == aligned_base_expected);
    exact_expr aligned_base_legacy = context.integrate(aligned_base_input, x);
    assert(aligned_base_legacy.operation() != exact_opcode::integral);
    assert(aligned_base_legacy == aligned_base_expected);
    exact_expr polynomial_aligned_input = context.integer(2) *
        context.power(x, context.integer(3)) * two_to_x_squared *
        three_to_x_squared;
    risch_result polynomial_aligned_result = context.integrate_elementary(
        polynomial_aligned_input, x);
    assert(polynomial_aligned_result.status == risch_status::elementary);
    exact_expr polynomial_aligned_expected =
        (x_squared / aligned_base_log_sum - context.integer(1) /
            context.power(aligned_base_log_sum, context.integer(2))) *
        two_to_x_squared * three_to_x_squared;
    assert(polynomial_aligned_result.elementary_part ==
        polynomial_aligned_expected);
    exact_expr shifted_aligned_input = context.integer(2) *
        context.power(x, context.integer(3)) *
        context.power(context.integer(2), x_squared + context.integer(1)) *
        three_to_x_squared;
    risch_result shifted_aligned_result = context.integrate_elementary(
        shifted_aligned_input, x);
    assert(shifted_aligned_result.status == risch_status::elementary);
    exact_expr shifted_aligned_expected =
        (x_squared / aligned_base_log_sum - context.integer(1) /
            context.power(aligned_base_log_sum, context.integer(2))) *
        context.power(context.integer(2), x_squared + context.integer(1)) *
        three_to_x_squared;
    assert(shifted_aligned_result.elementary_part ==
        shifted_aligned_expected);
    exact_expr aligned_rational_denominator = x_squared + context.integer(1);
    exact_expr aligned_rational_cofactor =
        aligned_base_log_sum / aligned_rational_denominator -
        context.integer(1) /
            context.power(aligned_rational_denominator, context.integer(2));
    exact_expr aligned_rational_input = context.integer(2) * x *
        aligned_rational_cofactor * two_to_x_squared * three_to_x_squared;
    risch_result aligned_rational_result = context.integrate_elementary(
        aligned_rational_input, x);
    assert(aligned_rational_result.status == risch_status::elementary);
    exact_expr aligned_rational_expected = two_to_x_squared *
        three_to_x_squared / aligned_rational_denominator;
    exact_expr aligned_rational_product = two_to_x_squared *
        three_to_x_squared;
    exact_expr aligned_rational_denominator_expanded =
        context.power(x, context.integer(4)) +
        context.integer(2) * x_squared + context.integer(1);
    assert(context.simplify(context.expand(
        aligned_rational_result.elementary_part *
            aligned_rational_denominator_expanded -
        aligned_rational_product * aligned_rational_denominator,
        100000)) == context.integer(0));
    assert(context.simplify(context.expand(
        aligned_rational_expected * aligned_rational_denominator -
        aligned_rational_product, 100000)) == context.integer(0));
    assert(context.simplify(context.expand(context.differentiate(
        aligned_rational_expected, x) - aligned_rational_input,
        100000)) == context.integer(0));
    exact_expr aligned_rational_legacy = context.integrate(
        aligned_rational_input, x);
    assert(aligned_rational_legacy.operation() != exact_opcode::integral);
    exact_expr q_to_x_squared = context.power(q, x_squared);
    exact_expr r_to_x_squared = context.power(r, x_squared);
    exact_expr symbolic_aligned_input = x * q_to_x_squared * r_to_x_squared;
    exact_expr symbolic_aligned_rate = context.natural_logarithm(q) +
        context.natural_logarithm(r);
    risch_result symbolic_aligned_result = context.integrate_elementary(
        symbolic_aligned_input, x);
    assert(symbolic_aligned_result.status == risch_status::elementary);
    assert(symbolic_aligned_result.remainder == context.integer(0));
    assert(symbolic_aligned_result.conditions.size() == 1);
    assert(context.simplify(symbolic_aligned_result.conditions[0] -
        symbolic_aligned_rate) == context.integer(0));
    exact_expr symbolic_aligned_expected = q_to_x_squared * r_to_x_squared /
        (context.integer(2) * symbolic_aligned_rate);
    assert(context.simplify(symbolic_aligned_result.elementary_part -
        symbolic_aligned_expected) == context.integer(0));
    exact_expr symbolic_aligned_legacy = context.integrate(
        symbolic_aligned_input, x);
    assert(symbolic_aligned_legacy.operation() == exact_opcode::integral);
    exact_expr q_squared_base = context.power(q, context.integer(2));
    exact_expr q_squared_exponential = context.power(q_squared_base, x_squared);
    exact_expr compound_base_input = x * q_squared_exponential * r_to_x_squared;
    exact_expr compound_base_rate = context.natural_logarithm(q_squared_base) +
        context.natural_logarithm(r);
    risch_result compound_base_result = context.integrate_elementary(
        compound_base_input, x);
    assert(compound_base_result.status == risch_status::elementary);
    assert(compound_base_result.remainder == context.integer(0));
    assert(compound_base_result.conditions.size() == 1);
    assert(context.simplify(compound_base_result.conditions[0] -
        compound_base_rate) == context.integer(0));
    exact_expr compound_base_expected = q_squared_exponential * r_to_x_squared /
        (context.integer(2) * compound_base_rate);
    assert(context.simplify(compound_base_result.elementary_part -
        compound_base_expected) == context.integer(0));
    exact_expr symbolic_aligned_denominator = x_squared + context.integer(1);
    exact_expr symbolic_aligned_cofactor = symbolic_aligned_rate /
        symbolic_aligned_denominator - context.integer(1) /
        context.power(symbolic_aligned_denominator, context.integer(2));
    exact_expr symbolic_aligned_rational_input = context.integer(2) * x *
        symbolic_aligned_cofactor * q_to_x_squared * r_to_x_squared;
    risch_result symbolic_aligned_rational_result = context.integrate_elementary(
        symbolic_aligned_rational_input, x);
    assert(symbolic_aligned_rational_result.status == risch_status::elementary);
    assert(symbolic_aligned_rational_result.remainder == context.integer(0));
    assert(symbolic_aligned_rational_result.conditions.size() == 1);
    assert(context.simplify(
        symbolic_aligned_rational_result.conditions[0] -
        symbolic_aligned_rate) == context.integer(0));
    exact_expr symbolic_aligned_rational_expected =
        q_to_x_squared * r_to_x_squared / symbolic_aligned_denominator;
    exact_expr symbolic_aligned_denominator_expanded =
        context.power(x, context.integer(4)) + context.integer(2) * x_squared +
        context.integer(1);
    exact_expr symbolic_aligned_rational_identity = context.simplify(
        symbolic_aligned_rational_result.elementary_part *
            symbolic_aligned_denominator_expanded -
        q_to_x_squared * r_to_x_squared * symbolic_aligned_denominator);
    assert(symbolic_aligned_rational_identity ==
        context.integer(0));
    assert(context.simplify(context.expand(context.differentiate(
        symbolic_aligned_rational_expected, x) -
        symbolic_aligned_rational_input, 100000)) == context.integer(0));
    exact_expr symbolic_aligned_rational_legacy = context.integrate(
        symbolic_aligned_rational_input, x);
    assert(symbolic_aligned_rational_legacy.operation() == exact_opcode::integral);
    exact_expr ln_two = context.natural_logarithm(context.integer(2));
    exact_expr rational_rde_input =
        (ln_two / x - context.integer(1) / context.power(x, context.integer(2))) *
        two_to_x;
    risch_result rational_rde_result = context.integrate_elementary(
        rational_rde_input, x);
    assert(rational_rde_result.status == risch_status::elementary);
    assert(context.simplify(rational_rde_result.elementary_part -
        two_to_x / x) == context.integer(0));
    exact_expr q_to_x = context.power(q, x);
    exact_expr ln_q = context.natural_logarithm(q);
    exact_expr symbolic_exponential_simple_pole = q_to_x / x;
    risch_result symbolic_simple_pole_result = context.integrate_elementary(
        symbolic_exponential_simple_pole, x);
    assert(symbolic_simple_pole_result.status ==
        risch_status::proven_nonelementary);
    assert(symbolic_simple_pole_result.remainder ==
        symbolic_exponential_simple_pole);
    assert(symbolic_simple_pole_result.conditions.size() == 1);
    assert(context.simplify(symbolic_simple_pole_result.conditions[0] - ln_q) ==
        context.integer(0));
    exact_expr symbolic_exponential_squarefree_poles = q_to_x /
        (x_squared + context.integer(1));
    risch_result symbolic_squarefree_poles_result = context.integrate_elementary(
        symbolic_exponential_squarefree_poles, x);
    assert(symbolic_squarefree_poles_result.status ==
        risch_status::proven_nonelementary);
    assert(symbolic_squarefree_poles_result.conditions.size() == 1);
    assert(context.simplify(symbolic_squarefree_poles_result.conditions[0] -
        ln_q) == context.integer(0));
    assert(context.integrate_elementary(q_to_x /
        (x + context.integer(1)), x).status ==
        risch_status::proven_nonelementary);
    exact_expr shared_exponential_poles = q_to_x / x +
        q_to_x / (x + context.integer(1));
    risch_result shared_exponential_poles_result = context.integrate_elementary(
        shared_exponential_poles, x);
    assert(shared_exponential_poles_result.status ==
        risch_status::proven_nonelementary);
    assert(shared_exponential_poles_result.conditions.size() == 1);
    assert(context.simplify(
        shared_exponential_poles_result.conditions[0] - ln_q) ==
        context.integer(0));
    exact_expr mixed_shared_exponential_poles = shared_exponential_poles +
        q_to_x;
    risch_result mixed_shared_poles_result = context.integrate_elementary(
        mixed_shared_exponential_poles, x);
    assert(mixed_shared_poles_result.status ==
        risch_status::proven_nonelementary);
    assert(mixed_shared_poles_result.remainder != context.integer(0));
    assert(mixed_shared_poles_result.conditions.size() == 1);
    assert(context.simplify(
        mixed_shared_poles_result.conditions[0] - ln_q) == context.integer(0));
    assert(context.simplify(context.expand(
        context.differentiate(mixed_shared_poles_result.elementary_part, x) +
        mixed_shared_poles_result.remainder - mixed_shared_exponential_poles,
        100000)) == context.integer(0));
    exact_expr mixed_exp_representations = t / x +
        e_to_x / (x + context.integer(1));
    risch_result mixed_exp_representations_result = context.integrate_elementary(
        mixed_exp_representations, x);
    assert(mixed_exp_representations_result.status ==
        risch_status::proven_nonelementary);
    assert(mixed_exp_representations_result.remainder != context.integer(0));
    exact_expr offset_exp_poles = t / x +
        context.exponential(x + context.integer(1)) /
            (x + context.integer(1));
    risch_result offset_exp_poles_result = context.integrate_elementary(
        offset_exp_poles, x);
    assert(offset_exp_poles_result.status ==
        risch_status::proven_nonelementary);
    assert(offset_exp_poles_result.remainder != context.integer(0));
    exact_expr symbolic_scaled_squarefree_poles = ln_q * q_to_x /
        (x_squared + context.integer(1));
    risch_result symbolic_scaled_squarefree_result = context.integrate_elementary(
        symbolic_scaled_squarefree_poles, x);
    assert(symbolic_scaled_squarefree_result.status ==
        risch_status::proven_nonelementary);
    assert(symbolic_scaled_squarefree_result.conditions.size() == 1);
    assert(context.simplify(
        symbolic_scaled_squarefree_result.conditions[0] - ln_q) ==
        context.integer(0));
    risch_options tiny_squarefree_rde_budget;
    tiny_squarefree_rde_budget.maximum_matrix_entries = 1;
    assert(context.integrate_elementary(symbolic_exponential_squarefree_poles,
        x, tiny_squarefree_rde_budget).status ==
        risch_status::proven_nonelementary);
    exact_expr symbolic_exponential_repeated_pole = q_to_x /
        context.power(x_squared + context.integer(1), context.integer(2));
    assert(context.integrate_elementary(symbolic_exponential_repeated_pole, x).status !=
        risch_status::proven_nonelementary);
    context.assume(q, "none");
    assert(context.integrate_elementary(symbolic_exponential_simple_pole, x).status !=
        risch_status::proven_nonelementary);
    context.assume(q, "positive");
    exact_expr symbolic_rate_rde_input =
        (ln_q / x - context.integer(1) / context.power(x, context.integer(2))) *
        q_to_x;
    risch_result symbolic_rate_rde_result = context.integrate_elementary(
        symbolic_rate_rde_input, x);
    assert(symbolic_rate_rde_result.status == risch_status::elementary);
    assert(context.simplify(symbolic_rate_rde_result.elementary_part -
        q_to_x / x) == context.integer(0));
    exact_expr symbolic_rate_parameter_input =
        (context.integer(1) + ln_q / x -
         context.integer(1) / context.power(x, context.integer(2))) * q_to_x;
    risch_result symbolic_rate_parameter_result = context.integrate_elementary(
        symbolic_rate_parameter_input, x);
    assert(symbolic_rate_parameter_result.status == risch_status::elementary);
    exact_expr symbolic_rate_rational_candidate = context.simplify(
        symbolic_rate_parameter_result.elementary_part / q_to_x);
    exact_expr symbolic_rate_rational_identity = context.expand(
        symbolic_rate_rational_candidate * context.power(x, context.integer(2)) *
            ln_q - x * ln_q - context.power(x, context.integer(2)), 100000);
    assert(context.simplify(symbolic_rate_rational_identity) == context.integer(0));
    assert(std::find(symbolic_rate_parameter_result.conditions.begin(),
        symbolic_rate_parameter_result.conditions.end(), ln_q) !=
        symbolic_rate_parameter_result.conditions.end());
    risch_result symbolic_exponential_pole = context.integrate_elementary(
        q_to_x / x, x);
    assert(symbolic_exponential_pole.status ==
        risch_status::proven_nonelementary);
    assert(symbolic_exponential_pole.conditions.size() == 1);
    risch_options rational_rde_tiny_budget;
    rational_rde_tiny_budget.maximum_matrix_entries = 1;
    risch_result rational_rde_limited = context.integrate_elementary(
        rational_rde_input, x, rational_rde_tiny_budget);
    assert(rational_rde_limited.status == risch_status::resource_limit);
    exact_expr mixed_rate_rde_input =
        (mixed_base_rate / x - context.integer(1) /
            context.power(x, context.integer(2))) * two_to_x * three_to_x;
    risch_result mixed_rate_rde_result = context.integrate_elementary(
        mixed_rate_rde_input, x);
    assert(mixed_rate_rde_result.status == risch_status::elementary);
    assert(context.simplify(mixed_rate_rde_result.elementary_part -
        two_to_x * three_to_x / x) == context.integer(0));
    exact_expr shifted_x = x + context.integer(1);
    exact_expr repeated_pole_rde_input =
        (ln_two / context.power(shifted_x, context.integer(2)) -
         context.integer(2) / context.power(shifted_x, context.integer(3))) *
        two_to_x;
    risch_result repeated_pole_rde_result = context.integrate_elementary(
        repeated_pole_rde_input, x);
    assert(repeated_pole_rde_result.status == risch_status::elementary);
    exact_expr repeated_numerator = context.expand(
        context.power(shifted_x, context.integer(2)));
    exact_expr repeated_denominator = context.expand(
        context.power(shifted_x, context.integer(4)));
    assert(context.simplify(repeated_pole_rde_result.elementary_part -
        two_to_x * repeated_numerator / repeated_denominator) ==
        context.integer(0));
    risch_result exponential_over_x = context.integrate_elementary(
        two_to_x / x, x);
    assert(exponential_over_x.status == risch_status::proven_nonelementary);
    assert(exponential_over_x.remainder == two_to_x / x);
    exact_expr exponential_over_quadratic = two_to_x /
        (context.power(x, context.integer(2)) + context.integer(1));
    assert(context.integrate_elementary(exponential_over_quadratic, x).status ==
        risch_status::proven_nonelementary);
    exact_expr cancelling_base_exponential = x * two_to_x *
        context.power(context.rational(precq_t(precn_t(1), precn_t(2))), x);
    risch_result cancelling_base_result = context.integrate_elementary(
        cancelling_base_exponential, x);
    assert(cancelling_base_result.status == risch_status::elementary);
    assert(context.simplify(cancelling_base_result.elementary_part -
        context.power(x, context.integer(2)) / context.integer(2)) ==
        context.integer(0));
    exact_expr negative_slope_cancellation = x * two_to_x *
        context.power(context.integer(4), -x / context.integer(2));
    risch_result negative_slope_result = context.integrate_elementary(
        negative_slope_cancellation, x);
    assert(negative_slope_result.status == risch_status::elementary);
    assert(context.simplify(negative_slope_result.elementary_part -
        context.power(x, context.integer(2)) / context.integer(2)) ==
        context.integer(0));
    risch_result scaled_power = context.integrate_elementary(a * two_to_x, x);
    assert(scaled_power.status == risch_status::elementary);
    assert(context.simplify(context.differentiate(
        scaled_power.elementary_part, x) - a * two_to_x) == context.integer(0));
    exact_expr symbolic_base_power = context.power(q, b * x);
    risch_result symbolic_base_result = context.integrate_elementary(
        symbolic_base_power, x);
    assert(symbolic_base_result.status == risch_status::elementary);
    assert(std::find(symbolic_base_result.conditions.begin(),
        symbolic_base_result.conditions.end(), b) !=
        symbolic_base_result.conditions.end());
    assert(std::find(symbolic_base_result.conditions.begin(),
        symbolic_base_result.conditions.end(), context.natural_logarithm(q)) !=
        symbolic_base_result.conditions.end());
    assert(context.simplify(context.differentiate(
        symbolic_base_result.elementary_part, x) - symbolic_base_power) ==
        context.integer(0));
    exact_expr symbolic_variable_rate_input = x *
        context.power(q, context.power(x, context.integer(2)));
    risch_result symbolic_variable_rate = context.integrate_elementary(
        symbolic_variable_rate_input, x);
    assert(symbolic_variable_rate.status == risch_status::elementary);
    assert(std::find(symbolic_variable_rate.conditions.begin(),
        symbolic_variable_rate.conditions.end(), context.natural_logarithm(q)) !=
        symbolic_variable_rate.conditions.end());
    assert(context.simplify(context.expand(
        context.differentiate(symbolic_variable_rate.elementary_part, x) -
        symbolic_variable_rate_input, 100000)) == context.integer(0));
    exact_expr symbolic_quadratic_power = context.power(q,
        context.power(x, context.integer(2)));
    exact_expr symbolic_rational_primitive = symbolic_quadratic_power /
        (x + context.integer(1));
    exact_expr symbolic_rational_input = context.differentiate(
        symbolic_rational_primitive, x);
    risch_result symbolic_rational_result = context.integrate_elementary(
        symbolic_rational_input, x);
    assert(symbolic_rational_result.status == risch_status::elementary);
    assert(symbolic_rational_result.remainder == context.integer(0));
    assert(context.simplify(context.expand(context.differentiate(
        symbolic_rational_result.elementary_part, x) -
        symbolic_rational_input, 100000)) == context.integer(0));
    risch_result symbolic_quadratic = context.integrate_elementary(
        context.integer(1) /
            (context.integer(1) + t +
             a * context.exponential(context.integer(2) * x)),
        x, options);
    assert(symbolic_quadratic.status == risch_status::elementary);
    assert(symbolic_quadratic.remainder == context.integer(0));
    assert(std::find(symbolic_quadratic.conditions.begin(),
        symbolic_quadratic.conditions.end(), a) !=
        symbolic_quadratic.conditions.end());
    exact_expr discriminant = context.integer(1)-context.integer(4)*a;
    assert(std::find(symbolic_quadratic.conditions.begin(),
        symbolic_quadratic.conditions.end(), discriminant) !=
        symbolic_quadratic.conditions.end());
    exact_expr quadratic = context.integer(1)+t+
        a*context.power(t, context.integer(2));
    risch_result same_generator = context.integrate_elementary(
        context.integer(1)/quadratic, x, options);
    assert(same_generator.status == risch_status::elementary);
    risch_result long_numerator = context.integrate_elementary(
        (context.integer(1)+context.power(t, context.integer(4)))/quadratic,
        x, options);
    assert(long_numerator.status == risch_status::elementary);
    exact_expr c = context.symbol("c");
    risch_result general_quadratic = context.integrate_elementary(
        context.integer(1)/(a+b*t+c*context.power(t, context.integer(2))),
        x, options);
    assert(general_quadratic.status == risch_status::elementary);
    assert(general_quadratic.remainder == context.integer(0));
    assert(std::find(general_quadratic.conditions.begin(),
        general_quadratic.conditions.end(), a) !=
        general_quadratic.conditions.end());
    assert(std::find(general_quadratic.conditions.begin(),
        general_quadratic.conditions.end(), c) !=
        general_quadratic.conditions.end());
    risch_result sparse_quadratic = context.integrate_elementary(
        context.integer(1)/(context.integer(1)+
            a*context.power(t, context.integer(2))), x, options);
    assert(sparse_quadratic.status == risch_status::elementary);
    risch_result shifted_quadratic = context.integrate_elementary(
        context.integer(1)/(context.integer(1)+t+
            a*context.exponential(context.integer(2)*x+context.integer(1))),
        x, options);
    assert(shifted_quadratic.status == risch_status::elementary);
    assert(shifted_quadratic.remainder == context.integer(0));
    exact_expr reciprocal_x = context.integer(1) / x;
    exact_expr shifted_reciprocal = context.exponential(reciprocal_x +
        context.integer(1));
    exact_expr twice_shifted_reciprocal = context.exponential(
        context.integer(2) * reciprocal_x + context.integer(3));
    exact_expr shifted_reciprocal_denominator = context.integer(1) +
        shifted_reciprocal + twice_shifted_reciprocal;
    exact_expr shifted_reciprocal_derivative = -(
        shifted_reciprocal + context.integer(2) * twice_shifted_reciprocal) /
        (context.power(x, context.integer(2)) *
         shifted_reciprocal_denominator);
    risch_result related_rational_shifts = context.integrate_elementary(
        shifted_reciprocal_derivative, x, options);
    assert(related_rational_shifts.status == risch_status::elementary);
    assert(related_rational_shifts.remainder == context.integer(0));
    assert(related_rational_shifts.elementary_part.reachable_node_count() > 0);
    exact_expr shifted_exp = context.exponential(x + context.integer(1));
    exact_expr shifted_exp_input = shifted_exp /
        context.power(context.integer(1) + context.exponential(x),
                      context.integer(2));
    risch_result shifted_exp_result = context.integrate_elementary(
        shifted_exp_input, x, options);
    assert(shifted_exp_result.status == risch_status::elementary);
    assert(context.simplify(context.differentiate(
        shifted_exp_result.elementary_part, x) -
        context.e() * context.exponential(x) /
            context.power(context.integer(1) + context.exponential(x),
                          context.integer(2))) == context.integer(0));
    risch_result shifted_exp_default = context.integrate_elementary(
        shifted_exp_input, x);
    assert(shifted_exp_default.status == risch_status::elementary);
    assert(context.simplify(shifted_exp_default.elementary_part -
        shifted_exp / (context.integer(1) + context.exponential(x))) ==
        context.integer(0));
    exact_expr inner_exponential = context.exponential(x);
    exact_expr outer_exponential = context.exponential(inner_exponential);
    exact_expr nested_polynomial_input = outer_exponential *
        (inner_exponential + context.integer(2) *
         context.power(inner_exponential, context.integer(2)));
    risch_result nested_polynomial = context.integrate_elementary(
        nested_polynomial_input, x, options);
    assert(nested_polynomial.status == risch_status::elementary);
    assert(nested_polynomial.remainder == context.integer(0));
    exact_expr nested_expected = outer_exponential *
        (context.integer(2) * inner_exponential - context.integer(1));
    assert(context.simplify(nested_polynomial.elementary_part -
        nested_expected) == context.integer(0));
    assert(context.simplify(context.differentiate(
        nested_polynomial.elementary_part, x) - nested_polynomial_input) ==
        context.integer(0));
    exact_expr nested_rational_input = outer_exponential *
        context.power(inner_exponential, context.integer(2)) /
        context.power(context.integer(1) + inner_exponential,
                      context.integer(2));
    risch_result nested_rational = context.integrate_elementary(
        nested_rational_input, x, options);
    assert(nested_rational.status == risch_status::elementary);
    assert(nested_rational.remainder == context.integer(0));
    exact_expr nested_rational_expected = outer_exponential /
        (context.integer(1) + inner_exponential);
    assert(context.simplify(nested_rational.elementary_part -
        nested_rational_expected) == context.integer(0));
    exact_expr nested_chain_inner = context.exponential(inner_exponential);
    exact_expr nested_chain_outer = context.exponential(nested_chain_inner);
    exact_expr nested_chain_derivative =
        nested_chain_inner * inner_exponential;
    exact_expr nested_chain_input = nested_chain_outer *
        nested_chain_derivative * nested_chain_inner /
        context.power(context.integer(1) + nested_chain_inner,
                      context.integer(2));
    risch_result nested_chain = context.integrate_elementary(
        nested_chain_input, x, options);
    assert(nested_chain.status == risch_status::elementary);
    assert(nested_chain.remainder == context.integer(0));
    exact_expr nested_chain_expected = nested_chain_outer /
        (context.integer(1) + nested_chain_inner);
    assert(context.simplify(nested_chain.elementary_part -
        nested_chain_expected) == context.integer(0));
    exact_expr nonlinear_chain_inner = context.exponential(
        context.power(x, context.integer(2)));
    exact_expr nonlinear_chain_outer = context.exponential(
        nonlinear_chain_inner);
    exact_expr nonlinear_chain_input = nonlinear_chain_outer *
        (context.integer(2) * x * nonlinear_chain_inner) *
        nonlinear_chain_inner /
        context.power(context.integer(1) + nonlinear_chain_inner,
                      context.integer(2));
    risch_result nonlinear_chain = context.integrate_elementary(
        nonlinear_chain_input, x, options);
    assert(nonlinear_chain.status == risch_status::elementary);
    assert(nonlinear_chain.remainder == context.integer(0));
    assert(context.simplify(nonlinear_chain.elementary_part -
        nonlinear_chain_outer /
            (context.integer(1) + nonlinear_chain_inner)) ==
        context.integer(0));
    exact_expr tower_inner = context.exponential(nested_chain_inner);
    exact_expr tower_outer = context.exponential(tower_inner);
    exact_expr tower_inner_derivative =
        tower_inner * nested_chain_inner * inner_exponential;
    exact_expr tower_input = tower_outer * tower_inner_derivative * tower_inner /
        context.power(context.integer(1) + tower_inner, context.integer(2));
    risch_result tower_result = context.integrate_elementary(
        tower_input, x, options);
    assert(tower_result.status == risch_status::elementary);
    assert(tower_result.remainder == context.integer(0));
    assert(context.simplify(tower_result.elementary_part - tower_outer /
        (context.integer(1) + tower_inner)) == context.integer(0));

    exact_expr offset_chain_outer = context.exponential(
        nested_chain_inner + context.integer(3));
    exact_expr offset_chain_input = offset_chain_outer *
        nested_chain_derivative * nested_chain_inner /
        context.power(context.integer(1) + nested_chain_inner,
                      context.integer(2));
    risch_result offset_chain = context.integrate_elementary(
        offset_chain_input, x, options);
    assert(offset_chain.status == risch_status::elementary);
    assert(offset_chain.remainder == context.integer(0));
    assert(context.simplify(offset_chain.elementary_part - offset_chain_outer /
        (context.integer(1) + nested_chain_inner)) == context.integer(0));

    exact_expr scaled_chain_outer = context.exponential(
        context.integer(2) * nested_chain_inner + context.integer(3));
    exact_expr scaled_chain_input = scaled_chain_outer *
        nested_chain_derivative *
        (context.integer(1) + context.integer(2) * nested_chain_inner) /
        context.power(context.integer(1) + nested_chain_inner,
                      context.integer(2));
    risch_result scaled_chain = context.integrate_elementary(
        scaled_chain_input, x, options);
    assert(scaled_chain.status == risch_status::elementary);
    assert(scaled_chain.remainder == context.integer(0));
    assert(context.simplify(scaled_chain.elementary_part - scaled_chain_outer /
        (context.integer(1) + nested_chain_inner)) == context.integer(0));
    exact_expr negative_three_halves = -context.rational(
        precq_t(precn_t(3), precn_t(2)));
    exact_expr five_sevenths = context.rational(
        precq_t(precn_t(5), precn_t(7)));
    exact_expr rational_offset_outer = context.exponential(
        negative_three_halves * nested_chain_inner + five_sevenths);
    exact_expr rational_offset_rhs = (
        -context.rational(precq_t(precn_t(5), precn_t(2))) +
        negative_three_halves * nested_chain_inner) /
        context.power(context.integer(1) + nested_chain_inner,
                      context.integer(2));
    exact_expr rational_offset_input = rational_offset_outer *
        nested_chain_derivative * rational_offset_rhs;
    risch_result rational_offset_chain = context.integrate_elementary(
        rational_offset_input, x, options);
    assert(rational_offset_chain.status == risch_status::elementary);
    assert(rational_offset_chain.remainder == context.integer(0));
    assert(context.simplify(rational_offset_chain.elementary_part -
        rational_offset_outer /
            (context.integer(1) + nested_chain_inner)) == context.integer(0));

    exact_expr affine_chain_inner = context.exponential(
        context.integer(2) * x + context.integer(1));
    exact_expr affine_chain_outer = context.exponential(
        context.integer(3) * affine_chain_inner + five_sevenths);
    exact_expr expanded_chain_cofactor =
        context.integer(4) * affine_chain_inner +
        context.integer(6) * context.power(affine_chain_inner,
                                           context.integer(2));
    exact_expr expanded_chain_input = affine_chain_outer *
        expanded_chain_cofactor /
        context.power(context.integer(1) + affine_chain_inner,
                      context.integer(2));
    risch_result expanded_chain = context.integrate_elementary(
        expanded_chain_input, x, options);
    assert(expanded_chain.status == risch_status::elementary);
    assert(expanded_chain.remainder == context.integer(0));
    assert(context.simplify(expanded_chain.elementary_part -
        affine_chain_outer /
            (context.integer(1) + affine_chain_inner)) == context.integer(0));
    exact_expr affine_chain_nonfactor_input = affine_chain_outer *
        (context.integer(6) - context.integer(2) / affine_chain_inner);
    risch_result affine_chain_nonfactor = context.integrate_elementary(
        affine_chain_nonfactor_input, x, options);
    assert(affine_chain_nonfactor.status == risch_status::elementary);
    assert(affine_chain_nonfactor.remainder == context.integer(0));
    assert(context.simplify(affine_chain_nonfactor.elementary_part -
        affine_chain_outer / affine_chain_inner) == context.integer(0));

    exact_expr nonlinear_chain_scaled_outer = context.exponential(
        context.integer(3) * nonlinear_chain_inner + five_sevenths);
    exact_expr nonlinear_chain_expanded_input = nonlinear_chain_scaled_outer *
        (context.integer(6) * x -
         context.integer(2) * x / nonlinear_chain_inner);
    risch_result nonlinear_chain_expanded = context.integrate_elementary(
        nonlinear_chain_expanded_input, x, options);
    assert(nonlinear_chain_expanded.status == risch_status::elementary);
    assert(nonlinear_chain_expanded.remainder == context.integer(0));
    assert(context.simplify(nonlinear_chain_expanded.elementary_part -
        nonlinear_chain_scaled_outer / nonlinear_chain_inner) ==
        context.integer(0));

    exact_expr constant_exponential = context.exponential(context.integer(3));
    exact_expr constant_exponential_input = constant_exponential *
        nested_chain_derivative /
        (context.integer(1) + nested_chain_inner);
    risch_options constant_chain_options;
    risch_result constant_exponential_chain = context.integrate_elementary(
        constant_exponential_input, x, constant_chain_options);
    if(constant_exponential_chain.status != risch_status::elementary)
        std::fprintf(stderr, "constant exponential chain: status=%d, %s\n",
            (int)constant_exponential_chain.status,
            constant_exponential_chain.diagnostic.c_str());
    assert(constant_exponential_chain.status == risch_status::elementary);
    assert(constant_exponential_chain.remainder == context.integer(0));
    exact_expr constant_exponential_expected = constant_exponential *
        context.natural_logarithm(context.integer(1) + nested_chain_inner);
    exact_expr constant_chain_difference = context.simplify(
        constant_exponential_chain.elementary_part -
        constant_exponential_expected);
    if(constant_chain_difference != context.integer(0))
        std::fprintf(stderr, "constant exponential primitive: %s\n",
            constant_exponential_chain.elementary_part.to_string().c_str());
    assert(constant_chain_difference == context.integer(0));
    exact_expr constant_affine_chain_input = constant_exponential *
        (context.integer(6) - context.integer(2) / affine_chain_inner);
    risch_result constant_affine_chain = context.integrate_elementary(
        constant_affine_chain_input, x, constant_chain_options);
    assert(constant_affine_chain.status == risch_status::elementary);
    assert(constant_affine_chain.remainder == context.integer(0));
    assert(context.simplify(context.differentiate(
        constant_affine_chain.elementary_part, x) -
        constant_affine_chain_input) == context.integer(0));
    exact_expr constant_nonlinear_chain_input = constant_exponential *
        (context.integer(6) * x -
         context.integer(2) * x / nonlinear_chain_inner);
    risch_result constant_nonlinear_chain = context.integrate_elementary(
        constant_nonlinear_chain_input, x, constant_chain_options);
    assert(constant_nonlinear_chain.status == risch_status::elementary);
    assert(constant_nonlinear_chain.remainder == context.integer(0));
    assert(context.simplify(context.differentiate(
        constant_nonlinear_chain.elementary_part, x) -
        constant_nonlinear_chain_input) == context.integer(0));
    exact_expr constant_exponential_normal_input = constant_exponential *
        nested_chain_derivative /
        (context.power(nested_chain_inner, context.integer(5)) -
         nested_chain_inner + context.integer(1));
    risch_result constant_exponential_normal = context.integrate_elementary(
        constant_exponential_normal_input, x, constant_chain_options);
    assert(constant_exponential_normal.status == risch_status::elementary);
    assert(constant_exponential_normal.remainder == context.integer(0));
    assert(constant_exponential_normal.elementary_part.valid());
    exact_expr constant_exponential_polynomial_input = constant_exponential *
        nested_chain_derivative *
        (context.integer(1) +
         context.power(nested_chain_inner, context.integer(2)));
    risch_result constant_exponential_polynomial = context.integrate_elementary(
        constant_exponential_polynomial_input, x, constant_chain_options);
    assert(constant_exponential_polynomial.status == risch_status::elementary);
    assert(constant_exponential_polynomial.remainder == context.integer(0));
    exact_expr constant_exponential_polynomial_expected = constant_exponential *
        (nested_chain_inner +
         context.power(nested_chain_inner, context.integer(3)) /
             context.integer(3));
    assert(context.simplify(constant_exponential_polynomial.elementary_part -
        constant_exponential_polynomial_expected) == context.integer(0));

    exact_expr no_rational_primitive = nested_chain_outer *
        nested_chain_derivative /
        context.power(context.integer(1) + nested_chain_inner,
                      context.integer(2));
    assert(context.integrate_elementary(no_rational_primitive, x, options).status !=
        risch_status::proven_nonelementary);
    risch_options nested_rational_tiny_budget;
    nested_rational_tiny_budget.maximum_matrix_entries = 1;
    assert(context.integrate_elementary(nested_rational_input, x,
        nested_rational_tiny_budget).status == risch_status::resource_limit);
    exact_expr three_halves = context.rational(
        precq_t(precn_t(3), precn_t(2)));
    exact_expr shifted_inner = context.exponential(
        three_halves * x + context.integer(1));
    exact_expr shifted_outer = context.exponential(shifted_inner);
    exact_expr shifted_nested_input = shifted_outer *
        (shifted_inner + context.integer(2) *
         context.power(shifted_inner, context.integer(2)));
    risch_result shifted_nested = context.integrate_elementary(
        shifted_nested_input, x, options);
    assert(shifted_nested.status == risch_status::elementary);
    assert(shifted_nested.remainder == context.integer(0));
    exact_expr shifted_nested_expected = shifted_outer *
        (context.rational(precq_t(precn_t(4), precn_t(3))) * shifted_inner -
         context.rational(precq_t(precn_t(2), precn_t(3))));
    assert(context.simplify(shifted_nested.elementary_part -
        shifted_nested_expected) == context.integer(0));
    assert(context.simplify(context.differentiate(
        shifted_nested.elementary_part, x) - shifted_nested_input) ==
        context.integer(0));
    exact_expr repeated_quadratic = a*a + context.integer(2)*a*b*t +
        b*b*context.power(t, context.integer(2));
    risch_result repeated_root = context.integrate_elementary(
        (context.integer(1)+context.power(t, context.integer(4)))/
            repeated_quadratic, x, options);
    assert(repeated_root.status == risch_status::elementary);
    assert(repeated_root.remainder == context.integer(0));
    assert(std::find(repeated_root.conditions.begin(),
        repeated_root.conditions.end(), a*a) != repeated_root.conditions.end());
    assert(std::find(repeated_root.conditions.begin(),
        repeated_root.conditions.end(), b*b) != repeated_root.conditions.end());
    risch_result zero_constant_quadratic = context.integrate_elementary(
        (context.integer(1)+context.power(t, context.integer(4)))/
            (b*t+c*context.power(t, context.integer(2))), x, options);
    assert(zero_constant_quadratic.status == risch_status::elementary);
    assert(zero_constant_quadratic.remainder == context.integer(0));
    assert(std::find(zero_constant_quadratic.conditions.begin(),
        zero_constant_quadratic.conditions.end(), b) !=
        zero_constant_quadratic.conditions.end());
    assert(std::find(zero_constant_quadratic.conditions.begin(),
        zero_constant_quadratic.conditions.end(), c) !=
        zero_constant_quadratic.conditions.end());
    exact_expr nonlinear_t = context.exponential(context.power(x,
        context.integer(2)));
    exact_expr nonlinear_denominator = a+b*nonlinear_t+
        c*context.power(nonlinear_t, context.integer(2));
    risch_result nonlinear_quadratic = context.integrate_elementary(
        context.integer(2)*x/nonlinear_denominator, x, options);
    assert(nonlinear_quadratic.status == risch_status::elementary);
    assert(nonlinear_quadratic.remainder == context.integer(0));
    assert(std::find(nonlinear_quadratic.conditions.begin(),
        nonlinear_quadratic.conditions.end(), a) !=
        nonlinear_quadratic.conditions.end());
    exact_expr related_nonlinear_denominator = a+b*nonlinear_t+
        c*context.exponential(context.integer(2)*context.power(x,
            context.integer(2)));
    risch_result related_nonlinear = context.integrate_elementary(
        context.integer(2)*x/related_nonlinear_denominator, x, options);
    assert(related_nonlinear.status == risch_status::elementary);
    assert(related_nonlinear.remainder == context.integer(0));
    assert(std::find(related_nonlinear.conditions.begin(),
        related_nonlinear.conditions.end(), c) !=
        related_nonlinear.conditions.end());
    risch_result nonlinear_repeated = context.integrate_elementary(
        context.integer(2)*x*(context.integer(1)+
            context.power(nonlinear_t, context.integer(4))) /
            (a*a+context.integer(2)*a*b*nonlinear_t+
             b*b*context.power(nonlinear_t, context.integer(2))),
        x, options);
    assert(nonlinear_repeated.status == risch_status::elementary);
    risch_result nonlinear_zero_constant = context.integrate_elementary(
        context.integer(2)*x /
            (b*nonlinear_t+c*context.power(nonlinear_t,
                context.integer(2))), x, options);
    assert(nonlinear_zero_constant.status == risch_status::elementary);
    risch_result symbolic_shift = context.integrate_elementary(
        context.integer(1)/(context.integer(1)+t+
            context.exponential(x+a)), x, options);
    assert(symbolic_shift.status == risch_status::elementary);
    assert(symbolic_shift.remainder == context.integer(0));
    exact_expr shifted_linear_coefficient = context.integer(1)+
        context.exponential(a);
    assert(std::find(symbolic_shift.conditions.begin(),
        symbolic_shift.conditions.end(), shifted_linear_coefficient) !=
        symbolic_shift.conditions.end());
    risch_result two_symbolic_shifts = context.integrate_elementary(
        context.integer(1)/(context.integer(1)+
            context.exponential(x+a)+
            context.exponential(context.integer(2)*x+b)), x, options);
    assert(two_symbolic_shifts.status == risch_status::elementary);
    risch_result nonlinear_symbolic_shifts = context.integrate_elementary(
        context.integer(2)*x/(context.integer(1)+
            context.exponential(context.power(x, context.integer(2))+a)+
            context.exponential(context.integer(2)*
                context.power(x, context.integer(2))+b)), x, options);
    assert(nonlinear_symbolic_shifts.status == risch_status::elementary);
    exact_expr symbolic_slope_t = context.exponential(a*x);
    risch_result symbolic_slope_linear = context.integrate_elementary(
        context.integer(1)/(context.integer(1)+symbolic_slope_t), x, options);
    assert(symbolic_slope_linear.status == risch_status::elementary);
    assert(std::find(symbolic_slope_linear.conditions.begin(),
        symbolic_slope_linear.conditions.end(), a) !=
        symbolic_slope_linear.conditions.end());
    risch_result symbolic_slope_quadratic = context.integrate_elementary(
        context.integer(1)/(b+symbolic_slope_t+
            c*context.power(symbolic_slope_t, context.integer(2))),
        x, options);
    assert(symbolic_slope_quadratic.status == risch_status::elementary);
    assert(std::find(symbolic_slope_quadratic.conditions.begin(),
        symbolic_slope_quadratic.conditions.end(), a) !=
        symbolic_slope_quadratic.conditions.end());
    exact_expr shifted_symbolic_slope_t = context.exponential(a*x+b);
    risch_result shifted_symbolic_slope = context.integrate_elementary(
        (context.integer(1)+context.power(shifted_symbolic_slope_t,
            context.integer(4))) /
            (context.integer(1)+shifted_symbolic_slope_t+
             c*context.power(shifted_symbolic_slope_t,
                 context.integer(2))), x, options);
    assert(shifted_symbolic_slope.status == risch_status::elementary);
    assert(std::find(shifted_symbolic_slope.conditions.begin(),
        shifted_symbolic_slope.conditions.end(), a) !=
        shifted_symbolic_slope.conditions.end());
    risch_result related_symbolic_slopes = context.integrate_elementary(
        context.integer(1)/(context.integer(1)+symbolic_slope_t+
            context.exponential(context.integer(2)*a*x+b)), x, options);
    assert(related_symbolic_slopes.status == risch_status::elementary);
    assert(std::find(related_symbolic_slopes.conditions.begin(),
        related_symbolic_slopes.conditions.end(), a) !=
        related_symbolic_slopes.conditions.end());
    risch_result fractional_symbolic_slopes = context.integrate_elementary(
        context.integer(1)/(context.integer(1)+
            context.exponential(a*x/context.integer(2))+
            symbolic_slope_t), x, options);
    assert(fractional_symbolic_slopes.status == risch_status::elementary);
    assert(!fractional_symbolic_slopes.conditions.empty());
    risch_result opposite_symbolic_slopes = context.integrate_elementary(
        context.integer(1)/(context.integer(1)+symbolic_slope_t+
            context.exponential(-a*x)), x, options);
    assert(opposite_symbolic_slopes.status == risch_status::elementary);
    exact_expr related_numeric_denominator = context.integer(1)+
        symbolic_slope_t+context.exponential(context.integer(2)*a*x);
    risch_result repeated_related_numeric = context.integrate_elementary(
        context.integer(1)/context.power(related_numeric_denominator,
            context.integer(2)), x, options);
    assert(repeated_related_numeric.status == risch_status::elementary);
    assert(!repeated_related_numeric.conditions.empty());
    risch_result independent_symbolic_slopes = context.integrate_elementary(
        context.integer(1)/(context.integer(1)+symbolic_slope_t+
            context.exponential(b*x)), x, options);
    assert(independent_symbolic_slopes.status != risch_status::elementary);
    risch_result shared_parameter_condition = context.integrate_elementary(
        context.integer(1)/(a+symbolic_slope_t+
            context.exponential(context.integer(2)*a*x)), x, options);
    assert(shared_parameter_condition.status == risch_status::elementary);
    assert(std::count(shared_parameter_condition.conditions.begin(),
        shared_parameter_condition.conditions.end(), a) == 1);
    risch_options tower_options;
    tower_options.maximum_recursion_depth = 4;
    exact_expr exp_x_squared = context.exponential(
        context.power(x, context.integer(2)));
    exact_expr related_rde_input = context.integer(2)*x*exp_x_squared +
        (context.integer(1)+context.integer(2)*
            context.power(x, context.integer(2))) *
        context.exponential(context.power(x, context.integer(2))+
            context.integer(1));
    risch_result related_rde = context.integrate_elementary(related_rde_input,
        x, tower_options);
    assert(related_rde.status == risch_status::elementary);
    assert(related_rde.remainder == context.integer(0));
    risch_result cancelled_nonelementary = context.integrate_elementary(
        context.exponential(context.power(x, context.integer(2))+
            context.integer(1)) - context.e()*exp_x_squared,
        x, tower_options);
    assert(cancelled_nonelementary.status == risch_status::elementary);
    assert(cancelled_nonelementary.remainder == context.integer(0));
    exact_expr log_x = context.natural_logarithm(x);
    risch_result mixed_exponential_primitive = context.integrate_elementary(
        exp_x_squared*(context.integer(2)*x*log_x +
            context.integer(1)/x), x, tower_options);
    assert(mixed_exponential_primitive.status == risch_status::elementary);
    assert(mixed_exponential_primitive.remainder == context.integer(0));
    assert(context.simplify(context.differentiate(
        mixed_exponential_primitive.elementary_part, x) -
        exp_x_squared*(context.integer(2)*x*log_x +
            context.integer(1)/x)) == context.integer(0));
    exact_expr mixed_pole_primitive = exp_x_squared*log_x/(x+context.integer(1));
    exact_expr mixed_pole_integrand = exp_x_squared *
        ((context.integer(2)*x/(x+context.integer(1)) -
          context.integer(1)/context.power(x+context.integer(1), context.integer(2))) *
            log_x + context.integer(1)/(x*(x+context.integer(1))));
    risch_result mixed_pole = context.integrate_elementary(
        mixed_pole_integrand, x, tower_options);
    assert(mixed_pole.status == risch_status::elementary);
    assert(mixed_pole.remainder == context.integer(0));
    assert(context.simplify(context.expand(
        context.differentiate(mixed_pole.elementary_part, x) -
        mixed_pole_integrand, 100000)) == context.integer(0));
    exact_expr mixed_denominator = context.integer(1) +
        context.exponential(x)*log_x;
    exact_expr mixed_denominator_derivative = context.exponential(x)*
        (log_x + context.integer(1)/x);
    risch_result mixed_repeated_pole = context.integrate_elementary(
        mixed_denominator_derivative /
            context.power(mixed_denominator, context.integer(2)),
        x, tower_options);
    assert(mixed_repeated_pole.status == risch_status::elementary);
    assert(mixed_repeated_pole.remainder == context.integer(0));
    assert(context.simplify(context.expand(
        context.differentiate(mixed_repeated_pole.elementary_part, x) -
        mixed_denominator_derivative /
            context.power(mixed_denominator, context.integer(2)),
        100000)) == context.integer(0));
    risch_result mixed_cubic_pole = context.integrate_elementary(
        context.integer(7)*mixed_denominator_derivative /
            context.power(mixed_denominator, context.integer(3)),
        x, tower_options);
    assert(mixed_cubic_pole.status == risch_status::elementary);
    assert(mixed_cubic_pole.remainder == context.integer(0));
    assert(context.simplify(context.expand(
        context.differentiate(mixed_cubic_pole.elementary_part, x) -
        context.integer(7)*mixed_denominator_derivative /
            context.power(mixed_denominator, context.integer(3)),
        100000)) == context.integer(0));
    risch_result unmatched_mixed_pole = context.integrate_elementary(
        context.exponential(x) /
            context.power(mixed_denominator, context.integer(2)),
        x, tower_options);
    assert(unmatched_mixed_pole.status != risch_status::elementary);
    risch_result missing_chain = context.integrate_elementary(
        context.integer(1)/nonlinear_denominator, x, options);
    assert(missing_chain.status != risch_status::elementary);
    std::puts("risch exponential rational ok");
}
