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
