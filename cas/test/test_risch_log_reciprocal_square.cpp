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
    exact_expr slope = context.symbol("slope");
    exact_expr intercept = context.symbol("intercept");
    for(int order : {1, 2, 3}){
        exact_expr affine_log = slope * log_x + intercept;
        exact_expr affine_input = context.power(affine_log,
            context.integer(-order));
        risch_result affine_result = context.integrate_elementary(
            affine_input, x);
        exact_expr affine_reconstruction_error = context.simplify(
            context.expand(context.differentiate(
                affine_result.elementary_part, x) +
                affine_result.remainder - affine_input));
        risch_result normalized_result = context.integrate_elementary(
            context.power(log_x + intercept / slope,
                context.integer(-order)), x);
        exact_expr expected_affine_remainder = context.simplify(
            context.power(slope, context.integer(-order)) *
            normalized_result.remainder);
        exact_expr expected_affine_elementary = context.simplify(
            context.power(slope, context.integer(-order)) *
            normalized_result.elementary_part);
        bool has_slope_condition = false;
        for(const exact_expr &condition : affine_result.conditions)
            if(condition == slope) has_slope_condition = true;
        if(affine_result.status != risch_status::proven_nonelementary ||
           !has_slope_condition || affine_result.remainder !=
               expected_affine_remainder || affine_result.elementary_part !=
               expected_affine_elementary){
            std::cerr << "affine logarithmic pole proof failed; order="
                      << order << " status="
                      << static_cast<int>(affine_result.status)
                      << " normalized status="
                      << static_cast<int>(normalized_result.status)
                      << " diagnostic=" << affine_result.diagnostic
                      << " conditions=" << affine_result.conditions.size()
                      << " remainder=" << affine_result.remainder.to_string()
                      << " expected=" << expected_affine_remainder.to_string()
                      << " reconstruction error="
                      << affine_reconstruction_error.to_string() << '\n';
            return 1;
        }
    }
    exact_expr inner_variable = context.symbol("_risch_affine_log_0");
    std::vector<exact_expr> affine_arguments{
        x + context.integer(1), context.integer(2) * x + context.integer(3)};
    for(const exact_expr &argument : affine_arguments){
        exact_expr inner_log = context.natural_logarithm(inner_variable);
        exact_expr outer_log = context.natural_logarithm(argument);
        for(int order : {1, 2, 3}){
            exact_expr inner_input = context.power(
                slope * inner_log + intercept, context.integer(-order));
            exact_expr input = context.power(
                slope * outer_log + intercept, context.integer(-order));
            risch_result inner_result = context.integrate_elementary(
                inner_input, inner_variable);
            risch_result result = context.integrate_elementary(input, x);
            exact_expr expected_scale = argument == x + context.integer(1)
                ? context.integer(1)
                : context.integer(1) / context.integer(2);
            exact_expr expected_elementary = context.simplify(
                context.substitute(inner_result.elementary_part, inner_variable,
                    argument) * expected_scale);
            exact_expr expected_remainder = context.simplify(
                context.substitute(inner_result.remainder, inner_variable,
                    argument) * expected_scale);
            bool has_log_slope_condition = false;
            for(const exact_expr &condition : result.conditions)
                if(condition == slope) has_log_slope_condition = true;
            if(result.status != risch_status::proven_nonelementary ||
               !has_log_slope_condition ||
               result.elementary_part != expected_elementary ||
               result.remainder != expected_remainder){
                std::cerr << "affine-inner logarithm pole failed; argument="
                          << argument.to_string() << " order=" << order
                          << " status=" << static_cast<int>(result.status)
                          << " diagnostic=" << result.diagnostic << '\n';
                return 1;
            }
        }
    }
    exact_expr argument_slope = context.symbol("argument_slope");
    exact_expr argument_intercept = context.symbol("argument_intercept");
    exact_expr symbolic_argument = argument_slope * x + argument_intercept;
    for(int order : {1, 2, 3}){
        exact_expr inner_input = context.power(
            slope * context.natural_logarithm(inner_variable) + intercept,
            context.integer(-order));
        exact_expr input = context.power(
            slope * context.natural_logarithm(symbolic_argument) + intercept,
            context.integer(-order));
        risch_result inner_result = context.integrate_elementary(
            inner_input, inner_variable);
        risch_result result = context.integrate_elementary(input, x);
        exact_expr expected_scale = context.integer(1) / argument_slope;
        exact_expr expected_elementary = context.simplify(
            context.substitute(inner_result.elementary_part, inner_variable,
                symbolic_argument) * expected_scale);
        exact_expr expected_remainder = context.simplify(
            context.substitute(inner_result.remainder, inner_variable,
                symbolic_argument) * expected_scale);
        bool has_log_slope_condition = false;
        bool has_argument_slope_condition = false;
        for(const exact_expr &condition : result.conditions){
            if(condition == slope) has_log_slope_condition = true;
            if(condition == argument_slope) has_argument_slope_condition = true;
        }
        if(result.status != risch_status::proven_nonelementary ||
           !has_log_slope_condition || !has_argument_slope_condition ||
           result.elementary_part != expected_elementary ||
           result.remainder != expected_remainder){
            std::cerr << "symbolic affine-log substitution failed; order="
                      << order << " status=" << static_cast<int>(result.status)
                      << " diagnostic=" << result.diagnostic << '\n';
            return 1;
        }
    }
    for(int degree = 1; degree <= 3; ++degree){
        exact_expr mixed_inner = context.power(
            inner_variable - context.integer(1), context.integer(degree)) *
            context.natural_logarithm(inner_variable);
        exact_expr mixed_outer = context.power(x, context.integer(degree)) *
            context.natural_logarithm(x + context.integer(1));
        risch_result mixed_inner_result = context.integrate_elementary(
            mixed_inner, inner_variable);
        risch_result mixed_result = context.integrate_elementary(mixed_outer, x);
        exact_expr mixed_expected = context.simplify(context.substitute(
            mixed_inner_result.elementary_part, inner_variable,
            x + context.integer(1)));
        if(mixed_inner_result.status != risch_status::elementary ||
           mixed_result.status != risch_status::elementary ||
           mixed_result.elementary_part != mixed_expected ||
           mixed_result.remainder != context.integer(0)){
            std::cerr << "affine-log substitution failed with x^"
                      << degree << " cofactor; status="
                      << static_cast<int>(mixed_result.status)
                      << " diagnostic=" << mixed_result.diagnostic << '\n';
            return 1;
        }
    }
    for(int logarithm_power = 1; logarithm_power <= 4;
        ++logarithm_power){
        exact_expr inner_log_power = context.power(
            context.natural_logarithm(inner_variable),
            context.integer(logarithm_power));
        exact_expr outer_log_power = context.power(
            context.natural_logarithm(x + context.integer(1)),
            context.integer(logarithm_power));
        exact_expr mixed_inner = (inner_variable - context.integer(1)) *
            inner_log_power;
        exact_expr mixed_outer = x * outer_log_power;
        risch_result mixed_inner_result = context.integrate_elementary(
            mixed_inner, inner_variable);
        risch_result mixed_result = context.integrate_elementary(mixed_outer, x);
        exact_expr mixed_expected = context.simplify(context.substitute(
            mixed_inner_result.elementary_part, inner_variable,
            x + context.integer(1)));
        if(mixed_inner_result.status != risch_status::elementary ||
           mixed_result.status != risch_status::elementary ||
           mixed_result.elementary_part != mixed_expected ||
           mixed_result.remainder != context.integer(0)){
            std::cerr << "affine-log mixed power failed; log power="
                      << logarithm_power << " status="
                      << static_cast<int>(mixed_result.status)
                      << " diagnostic=" << mixed_result.diagnostic << '\n';
            return 1;
        }
    }
    exact_expr scaled_mixed_inner =
        (inner_variable - context.integer(3)) / context.integer(2) *
        context.natural_logarithm(inner_variable);
    exact_expr scaled_mixed_outer = x * context.natural_logarithm(
        context.integer(2) * x + context.integer(3));
    risch_result scaled_mixed_inner_result = context.integrate_elementary(
        scaled_mixed_inner, inner_variable);
    risch_result scaled_mixed_result = context.integrate_elementary(
        scaled_mixed_outer, x);
    exact_expr scaled_mixed_expected = context.simplify(
        context.substitute(scaled_mixed_inner_result.elementary_part,
            inner_variable, context.integer(2) * x + context.integer(3)) /
        context.integer(2));
    if(scaled_mixed_inner_result.status != risch_status::elementary ||
       scaled_mixed_result.status != risch_status::elementary ||
       scaled_mixed_result.elementary_part != scaled_mixed_expected ||
       scaled_mixed_result.remainder != context.integer(0)){
        std::cerr << "scaled affine-log substitution failed with x cofactor; status="
                  << static_cast<int>(scaled_mixed_result.status)
                  << " diagnostic=" << scaled_mixed_result.diagnostic << '\n';
        return 1;
    }
    exact_expr logarithm = context.natural_logarithm(x);
    exact_expr expected_log_primitive = x;
    for(int exponent = 1; exponent <= 64; ++exponent){
        expected_log_primitive = x * context.power(logarithm,
            context.integer(exponent)) - context.integer(exponent) *
            expected_log_primitive;
        exact_expr input = context.power(logarithm,
            context.integer(exponent));
        risch_result result = context.integrate_elementary(input, x);
        exact_expr error = context.simplify(context.expand(
            context.differentiate(result.elementary_part, x) +
            result.remainder - input));
        exact_expr recurrence_error = context.simplify(context.expand(
            context.differentiate(expected_log_primitive, x) - input));
        if(result.status != risch_status::elementary ||
           result.remainder != context.integer(0) ||
           error != context.integer(0) ||
           recurrence_error != context.integer(0)){
            std::cerr << "logarithm power RDE failed; exponent=" << exponent
                      << " status=" << static_cast<int>(result.status)
                      << " diagnostic=" << result.diagnostic
                      << " verification error=" << error.to_string() << '\n';
            return 1;
        }
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
