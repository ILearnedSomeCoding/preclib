#include "../prec_cas.hpp"

#include <algorithm>
#include <iostream>

int main(){
    exact_context context;
    exact_expr x = context.symbol("x");
    exact_expr a = context.symbol("a");
    exact_expr b = context.symbol("b");
    exact_expr scale = context.symbol("scale");
    exact_expr input = context.exponential(context.power(x,
        context.integer(3))) /
        (context.power(x + a, context.integer(2)) *
         context.power(x + b, context.integer(2)));

    risch_options options;
    options.maximum_degree = 8;
    options.maximum_matrix_entries = 4096;
    options.maximum_nodes = 6000;
    risch_result result = context.integrate_elementary(input, x, options);
    auto has_separation_condition = [&](const std::vector<exact_expr> &conditions){
        for(const exact_expr &condition : conditions)
            if(context.simplify(condition - (b - a)) == context.integer(0) ||
               context.simplify(condition - (a - b)) == context.integer(0))
                return true;
        return false;
    };
    if(result.status != risch_status::unsupported ||
       result.elementary_part == context.integer(0) ||
       result.remainder == context.integer(0) ||
       !has_separation_condition(result.conditions)){
        std::cerr << "status=" << (int)result.status << " diagnostic="
                  << result.diagnostic << " part="
                  << result.elementary_part.to_string() << " remainder="
                  << result.remainder.to_string() << '\n';
        return 1;
    }
    exact_expr specialized_error = context.differentiate(
        result.elementary_part, x) + result.remainder - input;
    specialized_error = context.substitute(specialized_error, a,
        context.integer(1));
    specialized_error = context.substitute(specialized_error, b,
        context.integer(3));
    for(int64_t sample : {-2, 0, 1, 4}){
        exact_expr at_sample = context.simplify(context.substitute(
            specialized_error, x, context.integer(sample)));
        if(at_sample != context.integer(0)){
            std::cerr << "specialized decomposition failed at " << sample
                      << ": " << at_sample.to_string() << '\n';
            return 1;
        }
    }

    exact_expr expanded_a = context.integer(2) * x * x +
        context.integer(4) * a * x + context.integer(2) * a * a;
    exact_expr expanded_b = scale * x * x +
        context.integer(2) * scale * b * x + scale * b * b;
    if(expanded_a.operation() != exact_opcode::add ||
       expanded_b.operation() != exact_opcode::add){
        std::cerr << "expanded affine-power test did not build an expanded DAG\n";
        return 1;
    }
    exact_expr expanded_input = context.exponential(context.power(x,
        context.integer(3))) / (expanded_a * expanded_b);
    risch_result expanded_result = context.integrate_elementary(expanded_input,
        x, options);
    if(expanded_result.status != risch_status::unsupported ||
       expanded_result.elementary_part == context.integer(0) ||
       expanded_result.remainder == context.integer(0) ||
       !has_separation_condition(expanded_result.conditions) ||
       std::find(expanded_result.conditions.begin(),
           expanded_result.conditions.end(), scale) ==
           expanded_result.conditions.end()){
        std::cerr << "expanded affine powers: status="
                  << (int)expanded_result.status << " diagnostic="
                  << expanded_result.diagnostic << " part="
                  << expanded_result.elementary_part.to_string()
                  << " remainder=" << expanded_result.remainder.to_string()
                  << '\n';
        return 1;
    }
    exact_expr expanded_error = context.differentiate(
        expanded_result.elementary_part, x) + expanded_result.remainder -
        expanded_input;
    expanded_error = context.substitute(expanded_error, a,
        context.integer(1));
    expanded_error = context.substitute(expanded_error, b,
        context.integer(3));
    expanded_error = context.substitute(expanded_error, scale,
        context.integer(3));
    for(int64_t sample : {-2, 0, 1, 4})
        if(context.simplify(context.substitute(expanded_error, x,
                context.integer(sample))) != context.integer(0)){
            std::cerr << "expanded affine decomposition failed at "
                      << sample << '\n';
            return 1;
        }
    context.assume(scale, "positive");
    risch_result assumed_scale_result = context.integrate_elementary(
        expanded_input, x, options);
    if(assumed_scale_result.status != risch_status::unsupported ||
       !has_separation_condition(assumed_scale_result.conditions) ||
       std::find(assumed_scale_result.conditions.begin(),
           assumed_scale_result.conditions.end(), scale) !=
           assumed_scale_result.conditions.end()){
        std::cerr << "positive leading-coefficient assumption was not used\n";
        return 1;
    }
    context.assume(scale, "none");

    exact_expr logarithm = context.natural_logarithm(x);
    exact_expr logarithmic_input = context.exponential(context.power(logarithm,
        context.integer(3))) /
        (x * context.power(logarithm + a, context.integer(2)) *
         context.power(logarithm + b, context.integer(2)));
    risch_result logarithmic_result = context.integrate_elementary(
        logarithmic_input, x, options);
    if(logarithmic_result.status != risch_status::unsupported ||
       logarithmic_result.elementary_part == context.integer(0) ||
       logarithmic_result.remainder == context.integer(0) ||
       !has_separation_condition(logarithmic_result.conditions)){
        std::cerr << "logarithmic substitution: status="
                  << (int)logarithmic_result.status << " diagnostic="
                  << logarithmic_result.diagnostic << " part="
                  << logarithmic_result.elementary_part.to_string()
                  << " remainder=" << logarithmic_result.remainder.to_string()
                  << '\n';
        return 1;
    }
    std::cout << "independent affine pole partial Hermite ok\n";
}
