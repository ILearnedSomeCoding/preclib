#include "../prec_cas.hpp"

#include <iostream>
#include <vector>

int main(){
    exact_context context;
    exact_expr x = context.symbol("x");
    exact_expr log_x = context.natural_logarithm(x);
    std::vector<exact_expr> offsets{
        context.integer(0), context.integer(1), context.symbol("a")};
    for(const exact_expr &offset : offsets){
        exact_expr generator = log_x + offset;
        for(int order : {1, 2, 3}){
            exact_expr input = context.power(generator,
                context.integer(-order));
            risch_result result = context.integrate_elementary(input, x);
            exact_expr reconstruction_error = context.simplify(
                context.expand(context.differentiate(
                    result.elementary_part, x) + result.remainder - input));

            if(result.status != risch_status::proven_nonelementary ||
               reconstruction_error != context.integer(0)){
                std::cerr << "shifted logarithmic pole should have a Risch "
                             "non-elementarity certificate; generator="
                          << generator.to_string() << " order=" << order
                          << " status=" << static_cast<int>(result.status)
                          << " diagnostic=" << result.diagnostic
                          << " reconstruction error="
                          << reconstruction_error.to_string() << '\n';
                return 1;
            }
        }
    }
    exact_expr scale = context.symbol("scale");
    exact_expr scaled_input = scale * context.power(log_x,
        context.integer(-2));
    risch_result scaled_result = context.integrate_elementary(scaled_input, x);
    exact_expr scaled_reconstruction_error = context.simplify(context.expand(
        context.differentiate(scaled_result.elementary_part, x) +
        scaled_result.remainder - scaled_input));
    bool has_scale_condition = false;
    for(const exact_expr &condition : scaled_result.conditions)
        if(condition == scale) has_scale_condition = true;
    if(scaled_result.status != risch_status::proven_nonelementary ||
       !has_scale_condition ||
       scaled_reconstruction_error != context.integer(0)){
        std::cerr << "parameterized logarithmic-pole proof lost its "
                     "nonzero condition: status="
                  << static_cast<int>(scaled_result.status)
                  << " diagnostic=" << scaled_result.diagnostic
                  << " conditions=" << scaled_result.conditions.size()
                  << " reconstruction error="
                  << scaled_reconstruction_error.to_string() << '\n';
        return 1;
    }
    exact_expr zero_input = context.integer(0) *
        context.power(log_x, context.integer(-2));
    risch_result zero_result = context.integrate_elementary(zero_input, x);
    if(zero_result.status != risch_status::elementary ||
       zero_result.remainder != context.integer(0) ||
       zero_result.elementary_part != context.integer(0)){
        std::cerr << "zero scaling must not inherit a non-elementarity proof\n";
        return 1;
    }
    std::cout << "risch shifted logarithmic pole cases ok\n";
}
