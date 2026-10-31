#include "../prec_cas.hpp"

#include <iostream>
#include <tuple>

static bool verified_primitive(exact_context &context,
                               const exact_expr &integrand,
                               const exact_expr &variable){
    risch_result result = context.integrate_elementary(integrand, variable);
    if(result.status != risch_status::elementary ||
       result.remainder != context.integer(0)){
        std::cerr << "strict integration status " << (int)result.status
                  << ": " << result.diagnostic << '\n';
        return false;
    }
    exact_expr error = context.simplify(context.substitute(
        context.differentiate(result.elementary_part, variable) - integrand,
        variable, context.integer(0)));
    if(error != context.integer(0))
        std::cerr << "strict derivative verification returned "
                  << error.to_string() << " for " << integrand.to_string() << '\n';
    return error == context.integer(0);
}

int main(){
    exact_context context;
    exact_expr x = context.symbol("x");
    exact_expr exp_x = context.exponential(x);
    exact_expr exp_x2 = context.exponential(context.power(x,
        context.integer(2)));
    exact_expr b = context.symbol("b");
    exact_expr log_x = context.natural_logarithm(x);
    exact_expr log_square = context.power(log_x, context.integer(2));
    exact_expr logarithmic_exponential = context.exponential(log_square);

    exact_expr polynomial_rhs = x * exp_x;
    exact_expr rational_rhs = exp_x * x /
        context.power(x + context.integer(1), context.integer(2));
    exact_expr polynomial_rate_rhs = context.integer(2) * x * exp_x2;
    if(!verified_primitive(context, polynomial_rhs, x) ||
       !verified_primitive(context, rational_rhs, x) ||
       !verified_primitive(context, polynomial_rate_rhs, x)){
        std::cerr << "a constructive polynomial RDE case failed\n";
        return 1;
    }
    exact_expr shifted_laurent_rhs = context.integer(1) /
        (context.exponential(context.integer(3) * x) +
         context.exponential(context.integer(2) * x + context.integer(1)));
    risch_result shifted_laurent_result = context.integrate_elementary(
        shifted_laurent_rhs, x);
    if(shifted_laurent_result.status != risch_status::elementary ||
       shifted_laurent_result.remainder != context.integer(0)){
        std::cerr << "shifted exponential Laurent RDE failed: "
                  << shifted_laurent_result.elementary_part.to_string()
                  << " status=" << (int)shifted_laurent_result.status
                  << " remainder=" << shifted_laurent_result.remainder.to_string()
                  << " diagnostic=" << shifted_laurent_result.diagnostic << '\n';
        return 1;
    }
    exact_expr shifted_laurent_numerator = exp_x /
        (context.exponential(context.integer(3) * x) +
         context.exponential(context.integer(2) * x + context.integer(1)));
    risch_result shifted_laurent_numerator_result = context.integrate_elementary(
        shifted_laurent_numerator, x);
    if(shifted_laurent_numerator_result.status != risch_status::elementary ||
       shifted_laurent_numerator_result.remainder != context.integer(0)){
        std::cerr << "shifted exponential numerator RDE failed: "
                  << shifted_laurent_numerator_result.elementary_part.to_string()
                  << " status=" << (int)shifted_laurent_numerator_result.status
                  << " diagnostic=" << shifted_laurent_numerator_result.diagnostic << '\n';
        return 1;
    }
    exact_expr negative_shifted_laurent = context.integer(1) /
        (context.exponential(-context.integer(3) * x) +
         context.exponential(-context.integer(2) * x + context.integer(1)));
    risch_result negative_shifted_result = context.integrate_elementary(
        negative_shifted_laurent, x);
    if(negative_shifted_result.status != risch_status::elementary ||
       negative_shifted_result.remainder != context.integer(0)){
        std::cerr << "negative shifted exponential Laurent RDE failed: "
                  << negative_shifted_result.elementary_part.to_string()
                  << " status=" << (int)negative_shifted_result.status
                  << " diagnostic=" << negative_shifted_result.diagnostic << '\n';
        return 1;
    }
    exact_expr mixed_laurent = context.integer(1) /
        (context.exponential(x) + context.exponential(-x));
    risch_result mixed_laurent_result = context.integrate_elementary(
        mixed_laurent, x);
    if(mixed_laurent_result.status != risch_status::elementary ||
       mixed_laurent_result.remainder != context.integer(0)){
        std::cerr << "mixed-sign exponential Laurent RDE failed: "
                  << mixed_laurent_result.elementary_part.to_string()
                  << " status=" << (int)mixed_laurent_result.status
                  << " diagnostic=" << mixed_laurent_result.diagnostic << '\n';
        return 1;
    }
    exact_expr shifted_mixed_laurent = context.integer(1) /
        (context.exponential(x) +
         context.exponential(-x + context.integer(1)));
    risch_result shifted_mixed_result = context.integrate_elementary(
        shifted_mixed_laurent, x);
    if(shifted_mixed_result.status != risch_status::elementary ||
       shifted_mixed_result.remainder != context.integer(0)){
        std::cerr << "shifted mixed-sign exponential Laurent RDE failed: "
                  << shifted_mixed_result.elementary_part.to_string()
                  << " status=" << (int)shifted_mixed_result.status
                  << " diagnostic=" << shifted_mixed_result.diagnostic << '\n';
        return 1;
    }
    exact_expr a = context.symbol("a");
    exact_expr symbolic_shifted_mixed = context.integer(1) /
        (context.exponential(x + a) + context.exponential(-x));
    risch_result symbolic_shifted_result = context.integrate_elementary(
        symbolic_shifted_mixed, x);
    if(symbolic_shifted_result.status != risch_status::elementary ||
       symbolic_shifted_result.remainder != context.integer(0)){
        std::cerr << "symbolic shifted exponential Laurent RDE failed: "
                  << symbolic_shifted_result.elementary_part.to_string()
                  << " status=" << (int)symbolic_shifted_result.status
                  << " diagnostic=" << symbolic_shifted_result.diagnostic << '\n';
        return 1;
    }
    exact_expr cubic_laurent = context.integer(1) /
        (context.integer(1) + context.exponential(x) +
         context.exponential(context.integer(2) * x));
    risch_result cubic_laurent_result = context.integrate_elementary(
        cubic_laurent, x);
    if(cubic_laurent_result.status != risch_status::elementary ||
       cubic_laurent_result.remainder != context.integer(0)){
        std::cerr << "cubic exponential Laurent RDE failed: "
                  << cubic_laurent_result.elementary_part.to_string()
                  << " status=" << (int)cubic_laurent_result.status
                  << " diagnostic=" << cubic_laurent_result.diagnostic << '\n';
        return 1;
    }
    exact_expr mixed_cubic_laurent = context.integer(1) /
        (context.integer(1) + context.exponential(x) +
         context.exponential(-x));
    risch_result mixed_cubic_result = context.integrate_elementary(
        mixed_cubic_laurent, x);
    if(mixed_cubic_result.status != risch_status::elementary ||
       mixed_cubic_result.remainder != context.integer(0)){
        std::cerr << "mixed cubic exponential Laurent RDE failed: "
                  << mixed_cubic_result.elementary_part.to_string()
                  << " status=" << (int)mixed_cubic_result.status
                  << " diagnostic=" << mixed_cubic_result.diagnostic << '\n';
        return 1;
    }
    exact_expr mixed_cubic_legacy = context.integrate(mixed_cubic_laurent, x);
    if(mixed_cubic_legacy.operation() == exact_opcode::integral){
        std::cerr << "public mixed cubic exponential integration failed: "
                  << mixed_cubic_legacy.to_string() << '\n';
        return 1;
    }
    exact_expr symbolic_mixed_cubic = context.integer(1) /
        (context.integer(1) + context.exponential(x + a) +
         context.exponential(-x));
    risch_result symbolic_mixed_cubic_result = context.integrate_elementary(
        symbolic_mixed_cubic, x);
    if(symbolic_mixed_cubic_result.status != risch_status::elementary ||
       symbolic_mixed_cubic_result.remainder != context.integer(0)){
        std::cerr << "symbolic mixed cubic exponential RDE failed: "
                  << symbolic_mixed_cubic_result.elementary_part.to_string()
                  << " status=" << (int)symbolic_mixed_cubic_result.status
                  << " diagnostic=" << symbolic_mixed_cubic_result.diagnostic << '\n';
        return 1;
    }
    exact_expr logarithmic_exponential_rhs = logarithmic_exponential *
        (context.integer(1) + context.integer(2) * log_x);
    risch_result logarithmic_result = context.integrate_elementary(
        logarithmic_exponential_rhs, x);
    exact_expr logarithmic_error = context.simplify(
        context.differentiate(logarithmic_result.elementary_part, x) -
        logarithmic_exponential_rhs);
    if(logarithmic_result.status != risch_status::elementary ||
       logarithmic_result.remainder != context.integer(0) ||
       logarithmic_error != context.integer(0)){
        std::cerr << "logarithmic strict integration status "
                  << (int)logarithmic_result.status << ": "
                  << logarithmic_result.diagnostic << " primitive="
                  << logarithmic_result.elementary_part.to_string()
                  << " remainder=" << logarithmic_result.remainder.to_string()
                  << " error=" << logarithmic_error.to_string() << '\n';
        std::cerr << "logarithmic exponential chain RDE failed\n";
        return 1;
    }
    exact_expr symbolic_logarithmic_rhs = a * logarithmic_exponential *
        (context.integer(1) + context.integer(2) * log_x);
    risch_result symbolic_logarithmic_result = context.integrate_elementary(
        symbolic_logarithmic_rhs, x);
    exact_expr symbolic_logarithmic_expected = a * x * logarithmic_exponential;
    if(symbolic_logarithmic_result.status != risch_status::elementary ||
       symbolic_logarithmic_result.remainder != context.integer(0) ||
       context.simplify(symbolic_logarithmic_result.elementary_part -
                        symbolic_logarithmic_expected) != context.integer(0)){
        std::cerr << "symbolic logarithmic exponential RDE failed: "
                  << symbolic_logarithmic_result.elementary_part.to_string()
                  << " diagnostic=" << symbolic_logarithmic_result.diagnostic << '\n';
        return 1;
    }
    exact_expr ordinary_logarithmic_exponential = context.integrate(
        logarithmic_exponential_rhs, x);
    exact_expr ordinary_logarithmic_error = context.simplify(
        context.differentiate(ordinary_logarithmic_exponential, x) -
        logarithmic_exponential_rhs);
    if(ordinary_logarithmic_error != context.integer(0)){
        std::cerr << "ordinary integration missed logarithmic exponential "
                     "chain: "
                  << ordinary_logarithmic_exponential.to_string() << '\n';
        return 1;
    }

    exact_expr logarithmic_polynomial_rhs = logarithmic_exponential *
        (context.integer(1) + log_x + context.integer(2) *
         context.power(log_x, context.integer(2)));
    risch_result logarithmic_polynomial_result = context.integrate_elementary(
        logarithmic_polynomial_rhs, x);
    exact_expr logarithmic_polynomial_error = context.simplify(
        context.differentiate(logarithmic_polynomial_result.elementary_part, x) -
        logarithmic_polynomial_rhs);
    if(logarithmic_polynomial_result.status != risch_status::elementary ||
       logarithmic_polynomial_result.remainder != context.integer(0) ||
       logarithmic_polynomial_error != context.integer(0)){
        std::cerr << "logarithmic polynomial RDE failed: "
                  << logarithmic_polynomial_result.elementary_part.to_string()
                  << '\n';
        return 1;
    }

    exact_expr log_power_input = context.power(log_x, context.integer(2));
    risch_result log_power_result = context.integrate_elementary(
        log_power_input, x);
    exact_expr log_power_expected = x *
        (context.power(log_x, context.integer(2)) - context.integer(2) * log_x +
         context.integer(2));
    exact_expr log_power_error = context.simplify(context.expand(
        context.differentiate(log_power_result.elementary_part, x) -
        log_power_input, 100000));
    if(log_power_result.status != risch_status::elementary ||
       log_power_result.remainder != context.integer(0) ||
       log_power_error != context.integer(0) ||
       context.simplify(log_power_result.elementary_part -
                        log_power_expected) != context.integer(0)){
        std::cerr << "logarithm power RDE failed: "
                  << log_power_result.elementary_part.to_string()
                  << " error=" << log_power_error.to_string() << '\n';
        return 1;
    }

    exact_expr shifted_log_square = context.power(
        context.natural_logarithm(x + context.integer(1)), context.integer(2));
    exact_expr symbolic_log_sum = a * log_power_input + b * shifted_log_square;
    risch_result symbolic_log_left = context.integrate_elementary(
        a * log_power_input, x);
    risch_result symbolic_log_right = context.integrate_elementary(
        b * shifted_log_square, x);
    risch_result symbolic_log_sum_result = context.integrate_elementary(
        symbolic_log_sum, x);
    exact_expr shifted_log_primitive = (x + context.integer(1)) *
        (shifted_log_square - context.integer(2) *
         context.natural_logarithm(x + context.integer(1)) + context.integer(2));
    exact_expr symbolic_log_sum_expected = a * log_power_expected +
        b * shifted_log_primitive;
    if(symbolic_log_sum_result.status != risch_status::elementary ||
       symbolic_log_sum_result.remainder != context.integer(0) ||
       context.simplify(symbolic_log_sum_result.elementary_part -
                        symbolic_log_sum_expected) != context.integer(0)){
        std::cerr << "additive symbolic logarithm RDE failed: "
                  << symbolic_log_sum_result.elementary_part.to_string()
                  << " diagnostic=" << symbolic_log_sum_result.diagnostic
                  << " left=" << (int)symbolic_log_left.status << ":"
                  << symbolic_log_left.diagnostic << " right="
                  << (int)symbolic_log_right.status << ":"
                  << symbolic_log_right.diagnostic << '\n';
        return 1;
    }
    exact_expr symbolic_constant_sum = a + b * log_x;
    risch_result symbolic_constant_sum_result = context.integrate_elementary(
        symbolic_constant_sum, x);
    exact_expr symbolic_constant_sum_error = context.differentiate(
        symbolic_constant_sum_result.elementary_part, x) - symbolic_constant_sum;
    bool symbolic_constant_sum_verified = true;
    for(const auto &values : {std::tuple<int, int, int>{2, 3, 1},
                              std::tuple<int, int, int>{-1, 4, 2}}){
        exact_expr specialized_error = context.substitute(
            symbolic_constant_sum_error, a, context.integer(std::get<0>(values)));
        specialized_error = context.substitute(
            specialized_error, b, context.integer(std::get<1>(values)));
        specialized_error = context.simplify(context.substitute(
            specialized_error, x, context.integer(std::get<2>(values))));
        if(specialized_error != context.integer(0)){
            symbolic_constant_sum_error = specialized_error;
            symbolic_constant_sum_verified = false;
            break;
        }
    }
    if(symbolic_constant_sum_result.status != risch_status::elementary ||
       symbolic_constant_sum_result.remainder != context.integer(0) ||
       !symbolic_constant_sum_verified){
        std::cerr << "symbolic constant term integration failed: "
                  << symbolic_constant_sum_result.elementary_part.to_string()
                  << " status=" << (int)symbolic_constant_sum_result.status
                  << " diagnostic=" << symbolic_constant_sum_result.diagnostic
                  << " error=" << symbolic_constant_sum_error.to_string() << '\n';
        return 1;
    }
    exact_expr public_symbolic_constant_sum = context.integrate(
        symbolic_constant_sum, x);
    if(public_symbolic_constant_sum.operation() == exact_opcode::integral){
        std::cerr << "public integration rejected a certified symbolic constant "
                     "sum: " << public_symbolic_constant_sum.to_string() << '\n';
        return 1;
    }

    exact_expr half = context.rational(
        precq_t(precn_t(1), precn_t(2)));
    exact_expr sqrt_x = context.power(x, half);
    exact_expr log_over_sqrt_input = log_x / sqrt_x;
    risch_result log_over_sqrt_result = context.integrate_elementary(
        log_over_sqrt_input, x);
    exact_expr log_over_sqrt_expected = sqrt_x *
        (context.integer(2) * log_x - context.integer(4));
    exact_expr log_over_sqrt_error = context.simplify(context.expand(
        context.differentiate(log_over_sqrt_result.elementary_part, x) -
        log_over_sqrt_input, 100000));
    if(log_over_sqrt_result.status != risch_status::elementary ||
       log_over_sqrt_result.remainder != context.integer(0) ||
       context.simplify(log_over_sqrt_result.elementary_part -
                        log_over_sqrt_expected) != context.integer(0)){
        std::cerr << "logarithm over square-root RDE failed: "
                  << log_over_sqrt_result.elementary_part.to_string()
                  << " error=" << log_over_sqrt_error.to_string() << '\n';
        return 1;
    }

    exact_expr third = context.rational(
        precq_t(precn_t(1), precn_t(3)));
    exact_expr cube_root_x = context.power(x, third);
    exact_expr cube_root_log_input = cube_root_x *
        (context.integer(1) + log_x);
    risch_result cube_root_log_result = context.integrate_elementary(
        cube_root_log_input, x);
    exact_expr cube_root_log_expected = context.power(x,
        context.rational(precq_t(precn_t(4), precn_t(3)))) *
        (context.rational(precq_t(precn_t(3), precn_t(4))) * log_x -
         context.rational(precq_t(precn_t(9), precn_t(16))) +
         context.rational(precq_t(precn_t(3), precn_t(4))));
    if(cube_root_log_result.status != risch_status::elementary ||
       cube_root_log_result.remainder != context.integer(0) ||
       context.simplify(cube_root_log_result.elementary_part -
                        cube_root_log_expected) != context.integer(0)){
        std::cerr << "fractional logarithm RDE failed: "
                  << cube_root_log_result.elementary_part.to_string() << '\n';
        return 1;
    }

    exact_expr reciprocal_log_input = context.integer(1) / log_x;
    risch_result reciprocal_log_result = context.integrate_elementary(
        reciprocal_log_input, x);
    if(reciprocal_log_result.status != risch_status::proven_nonelementary ||
       reciprocal_log_result.remainder != reciprocal_log_input){
        std::cerr << "reciprocal logarithm Risch decision failed: "
                  << "status=" << (int)reciprocal_log_result.status
                  << " part=" << reciprocal_log_result.elementary_part.to_string()
                  << " remainder=" << reciprocal_log_result.remainder.to_string()
                  << " diagnostic=" << reciprocal_log_result.diagnostic << '\n';
        return 1;
    }

    exact_expr shifted_log = context.natural_logarithm(x + context.integer(1));
    exact_expr mixed_log_product = log_x * shifted_log;
    exact_expr mixed_log_product_input = context.differentiate(
        mixed_log_product, x);
    exact_expr symbolic_multiple_input = a * mixed_log_product_input;
    risch_result symbolic_multiple_result = context.integrate_elementary(
        symbolic_multiple_input, x);
    if(symbolic_multiple_result.status != risch_status::elementary ||
       symbolic_multiple_result.remainder != context.integer(0) ||
       context.simplify(symbolic_multiple_result.elementary_part -
                        a * mixed_log_product) != context.integer(0)){
        std::cerr << "constant multiple primitive RDE failed: "
                  << symbolic_multiple_result.elementary_part.to_string()
                  << " diagnostic=" << symbolic_multiple_result.diagnostic << '\n';
        return 1;
    }

    exact_expr nested_log = context.natural_logarithm(log_x);
    exact_expr nested_exponential = context.exponential(
        context.power(nested_log, context.integer(2)));
    exact_expr nested_rhs = nested_exponential *
        (context.integer(1) + log_x + context.integer(2) * nested_log);
    risch_result nested_result = context.integrate_elementary(nested_rhs, x);
    exact_expr nested_error = context.simplify(
        context.differentiate(nested_result.elementary_part, x) - nested_rhs);
    if(nested_result.status != risch_status::elementary ||
       nested_result.remainder != context.integer(0) ||
       nested_error != context.integer(0)){
        std::cerr << "nested logarithmic RDE failed: "
                  << nested_result.elementary_part.to_string() << '\n';
        return 1;
    }

    exact_expr nested_product_inner = log_x * nested_log;
    exact_expr nested_product_exponential = context.exponential(
        nested_product_inner);
    exact_expr nested_product_rhs = nested_product_exponential *
        (context.integer(2) + nested_log);
    risch_result nested_product_result = context.integrate_elementary(
        nested_product_rhs, x);
    exact_expr nested_product_error = context.simplify(context.expand(
        context.differentiate(nested_product_result.elementary_part, x) -
        nested_product_rhs, 100000));
    if(nested_product_result.status != risch_status::elementary ||
       nested_product_result.remainder != context.integer(0) ||
       nested_product_error != context.integer(0)){
        std::cerr << "nested product RDE failed: "
                  << nested_product_result.elementary_part.to_string()
                  << " status=" << (int)nested_product_result.status
                  << " error=" << nested_product_error.to_string() << '\n';
        return 1;
    }

    exact_expr cubic_denominator = context.power(x, context.integer(3)) +
        context.integer(1);
    exact_expr symbolic_rational_input = (a * x + b) / cubic_denominator;
    risch_result symbolic_rational_result = context.integrate_elementary(
        symbolic_rational_input, x);
    exact_expr symbolic_rational_error = context.integer(0);
    exact_expr symbolic_rational_derivative = context.differentiate(
        symbolic_rational_result.elementary_part, x) - symbolic_rational_input;
    for(const auto &values : {std::tuple<int, int, int>{2, 3, 0},
                              std::tuple<int, int, int>{2, 3, 1},
                              std::tuple<int, int, int>{-1, 4, 2}}){
        exact_expr specialized_error = context.substitute(
            symbolic_rational_derivative, a, context.integer(std::get<0>(values)));
        specialized_error = context.substitute(
            specialized_error, b, context.integer(std::get<1>(values)));
        specialized_error = context.simplify(context.substitute(
            specialized_error, x, context.integer(std::get<2>(values))));
        if(specialized_error != context.integer(0)){
            symbolic_rational_error = specialized_error;
            break;
        }
    }
    if(symbolic_rational_result.status != risch_status::elementary ||
       symbolic_rational_result.remainder != context.integer(0) ||
       symbolic_rational_error != context.integer(0)){
        std::cerr << "symbolic rational numerator distribution failed: "
                  << symbolic_rational_result.elementary_part.to_string()
                  << " status=" << (int)symbolic_rational_result.status
                  << " diagnostic=" << symbolic_rational_result.diagnostic
                  << " error=" << symbolic_rational_error.to_string() << '\n';
        return 1;
    }

    risch_result no_rational_solution =
        context.integrate_elementary(exp_x2, x);
    if(no_rational_solution.status != risch_status::proven_nonelementary){
        std::cerr << "expected the complete RDE bound to prove exp(x^2) "
                     "non-elementary, got: "
                  << no_rational_solution.diagnostic << '\n';
        return 1;
    }

    risch_options constrained;
    constrained.maximum_nodes = 64;
    constrained.maximum_degree = 64;
    risch_result bounded_result = context.integrate_elementary(
        context.power(x + context.integer(1), context.integer(100)),
        x, constrained);
    if(bounded_result.status == risch_status::elementary){
        std::cerr << "strict integration accepted a high-degree candidate "
                     "outside the configured budget\n";
        return 1;
    }
    std::cout << "risch core RDE cases ok\n";
}
