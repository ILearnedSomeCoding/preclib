#include"../prec_cas.hpp"

#include<cassert>
#include<iostream>

static void check_rational_root_sum(size_t power, int constant){
    exact_context context;
    exact_expr x = context.symbol("x");
    exact_expr denominator = context.power(x, context.integer((int64_t)power)) +
        context.integer(constant);
    exact_expr integrand = context.integer(1) / denominator;

    risch_options options;
    options.maximum_degree = 16;
    options.maximum_rothstein_degree = 8;
    risch_result result = context.integrate_elementary(
        integrand, x, options);
    assert(result.status == risch_status::elementary);
    assert(result.remainder == context.integer(0));
    assert(result.elementary_part.reachable_node_count() <=
           options.maximum_nodes);
    assert(context.simplify(context.expand(
        context.differentiate(result.elementary_part, x) - integrand,
        100000)) == context.integer(0));
}

int main(){
    check_rational_root_sum(7, -1);
    check_rational_root_sum(8, 1);
    std::cout << "risch higher-degree Rothstein-Trager ok\n";
    return 0;
}
