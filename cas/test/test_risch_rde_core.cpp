#include "../prec_cas.hpp"

#include <iostream>

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
                  << error.to_string() << '\n';
    return error == context.integer(0);
}

int main(){
    exact_context context;
    exact_expr x = context.symbol("x");
    exact_expr exp_x = context.exponential(x);
    exact_expr exp_x2 = context.exponential(context.power(x,
        context.integer(2)));
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
