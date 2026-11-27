#include "../prec_cas.hpp"

#include <iostream>

int main(){
    exact_context context;
    exact_expr x = context.symbol("x");
    exact_expr a = context.symbol("a");
    exact_expr t = context.natural_logarithm(x);
    exact_expr first_pole = t + a;
    exact_expr second_pole = t + a + context.integer(1);
    risch_options options;
    options.maximum_degree = 12;
    options.maximum_matrix_entries = 65536;
    options.maximum_nodes = 20000;
    exact_expr input = context.exponential(context.power(t,
        context.integer(3))) /
        (x * context.power(first_pole, context.integer(2)) *
         context.power(second_pole, context.integer(2)));

    risch_result result = context.integrate_elementary(input, x, options);
    if(result.status != risch_status::proven_nonelementary ||
       result.elementary_part == context.integer(0) ||
       result.remainder == context.integer(0)){
        std::cerr << "status=" << (int)result.status << " diagnostic="
                  << result.diagnostic << " part="
                  << result.elementary_part.to_string() << " remainder="
                  << result.remainder.to_string() << '\n';
        return 1;
    }

    std::cout << "logarithmic multi-pole partial Hermite ok\n";
}
