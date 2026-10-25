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
    std::cout << "risch rothstein-trager ok\n";
}
