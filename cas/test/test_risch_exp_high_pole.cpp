#include "../prec_cas.hpp"

#include <iostream>

int main(){
    exact_context context;
    exact_expr x = context.symbol("x");
    exact_expr a = context.integer(2);
    exact_expr b = context.integer(3);
    exact_expr t = context.exponential(x);
    exact_expr integrand = t *
        context.power(t + a, context.integer(-5)) *
        context.power(t + b, context.integer(-4));

    risch_options options;
    options.maximum_degree = 16;
    options.maximum_nodes = 10000;
    risch_result result = context.integrate_elementary(integrand, x, options);
    if(result.status != risch_status::elementary ||
       result.remainder != context.integer(0)){
        std::cerr << "expected a verified primitive for total pole order 9, got: "
                  << result.diagnostic << '\n';
        return 1;
    }
    exact_expr error = context.simplify(context.substitute(
        context.differentiate(result.elementary_part, x) - integrand,
        x, context.integer(0)));
    if(error != context.integer(0)){
        std::cerr << "primitive derivative mismatch: " << error.to_string()
                  << '\n';
        return 1;
    }
    std::cout << "risch exponential high-pole reduction ok\n";
}
