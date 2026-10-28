#include "../prec_cas.hpp"

#include <cassert>
#include <iostream>

int main(){
    exact_context context;
    exact_expr x = context.symbol("x");
    exact_expr denominator = context.power(x, context.integer(5)) - x +
        context.integer(1);
    exact_expr integrand = context.integer(1) / denominator;
    exact_expr primitive = context.integrate(integrand, x);
    if(primitive.operation() == exact_opcode::integral){
        std::cerr << "Rothstein-Trager path returned an unevaluated integral\n";
        return 1;
    }
    const std::string text = primitive.to_string();
    if(text.find("AlgebraicLogSum(") == std::string::npos){
        std::cerr << "expected grouped algebraic residues, got: " << text << '\n';
        return 1;
    }
    exact_expr error = context.simplify(
        context.differentiate(primitive, x) - integrand);
    if(error != context.integer(0)){
        std::cerr << "derivative did not simplify to zero: " << error.to_string() << '\n';
        return 1;
    }
    risch_options high_degree_options;
    high_degree_options.maximum_rothstein_degree = 10;
    for(size_t degree : {7u, 8u, 9u, 10u}){
        exact_expr high_denominator = context.power(x,
            context.integer((int64_t)degree)) + context.integer(1);
        if(degree < 9) high_denominator = high_denominator + x;
        exact_expr high_integrand = context.integer(1) / high_denominator;
        exact_expr default_primitive = context.integrate(high_integrand, x);
        if(default_primitive.operation() != exact_opcode::log_root_sum ||
           context.differentiate(default_primitive, x) != high_integrand){
            std::cerr << "default RT dispatch should keep an exact compact "
                         "LogRootSum at degree " << degree << ", got: "
                      << default_primitive.to_string() << '\n';
            return 1;
        }
        risch_result high_result = context.integrate_elementary(
            high_integrand, x, high_degree_options);
        exact_expr high_primitive = high_result.elementary_part;
        if(high_result.status != risch_status::elementary ||
           high_primitive.operation() != exact_opcode::algebraic_log_sum){
            std::cerr << "expected RT grouping at degree " << degree << ", got: "
                      << high_primitive.to_string() << '\n';
            return 1;
        }
        if(context.differentiate(high_primitive, x) != high_integrand){
            std::cerr << "high-degree RT derivative mismatch at degree "
                      << degree << '\n';
            return 1;
        }
    }
    std::cout << "risch rothstein-trager ok\n";
}
