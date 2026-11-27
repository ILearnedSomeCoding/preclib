#include "../prec_cas.hpp"

#include <iostream>

int main(){
    exact_context context;
    exact_expr x = context.symbol("x");
    exact_expr s = context.symbol("_risch_log_multi_pole_t");
    exact_expr t = context.natural_logarithm(x);
    exact_expr a = context.symbol("a");
    exact_expr b = context.symbol("b");
    exact_expr exponential = context.exponential(
        context.power(t, context.integer(3)));
    exact_expr candidate = context.integer(1) /
        (s * (s + context.integer(1)));
    exact_expr forcing = context.substitute(
        context.differentiate(candidate, s) + context.integer(3) *
            context.power(s, context.integer(2)) * candidate,
        s, t);
    exact_expr input = exponential * forcing / x;

    risch_options options;
    options.maximum_degree = 12;
    options.maximum_matrix_entries = 65536;
    options.maximum_nodes = 20000;
    risch_result result = context.integrate_elementary(input, x, options);
    if(result.status != risch_status::elementary ||
       result.remainder != context.integer(0)){
        std::cerr << "status=" << (int)result.status << " diagnostic="
                  << result.diagnostic << " part="
                  << result.elementary_part.to_string() << " remainder="
                  << result.remainder.to_string() << '\n';
        return 1;
    }

    exact_expr parameter_candidate = context.integer(1) /
        (context.power(s + a, context.integer(2)) *
         context.power(s + b, context.integer(2)));
    exact_expr parameter_forcing_s =
        (context.integer(-2) * (s + b) + context.integer(-2) * (s + a) +
         context.integer(3) * context.power(s, context.integer(2)) *
             (s + a) * (s + b)) /
        (context.power(s + a, context.integer(3)) *
         context.power(s + b, context.integer(3)));
    exact_expr parameter_forcing = context.substitute(parameter_forcing_s,
        s, t);
    exact_expr parameter_input = exponential * parameter_forcing / x;
    risch_result parameter_result = context.integrate_elementary(
        parameter_input, x, options);
    if(parameter_result.status != risch_status::elementary ||
       parameter_result.remainder != context.integer(0)){
        std::cerr << "parameterized logarithmic poles: status="
                  << (int)parameter_result.status << " diagnostic="
                  << parameter_result.diagnostic << " part="
                  << parameter_result.elementary_part.to_string()
                  << " remainder=" << parameter_result.remainder.to_string()
                  << '\n';
        return 1;
    }
    std::cout << "logarithmic multi-pole RDE ok\n";
}
