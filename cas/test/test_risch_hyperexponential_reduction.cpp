#include "../prec_cas.hpp"

#include <algorithm>
#include <iostream>

static bool is_zero(exact_context &context, const exact_expr &value){
    return context.simplify(context.expand(value, 100000)) == context.integer(0);
}

int main(){
    exact_context context;
    exact_expr x = context.symbol("x");
    exact_expr exponential = context.exponential(context.power(x,
        context.integer(2)));

    exact_expr cubic = context.power(x, context.integer(3)) * exponential;
    risch_result cubic_result = context.integrate_elementary(cubic, x);
    exact_expr cubic_expected =
        (context.power(x, context.integer(2)) / context.integer(2) -
         context.integer(1) / context.integer(2)) * exponential;
    if(cubic_result.status != risch_status::elementary ||
       cubic_result.remainder != context.integer(0) ||
       !is_zero(context, cubic_result.elementary_part - cubic_expected) ||
       !is_zero(context, context.differentiate(cubic_result.elementary_part, x) -
                         cubic)){
        std::cerr << "cubic hyperexponential reduction failed: "
                  << cubic_result.diagnostic << " primitive="
                  << cubic_result.elementary_part.to_string() << '\n';
        return 1;
    }

    exact_expr quartic = context.power(x, context.integer(4)) * exponential;
    risch_result quartic_result = context.integrate_elementary(quartic, x);
    exact_expr quartic_expected_primitive =
        (context.power(x, context.integer(3)) / context.integer(2) -
         context.integer(3) * x / context.integer(4)) * exponential;
    exact_expr quartic_expected_remainder =
        context.integer(3) * exponential / context.integer(4);
    if(quartic_result.status != risch_status::proven_nonelementary ||
       !is_zero(context, quartic_result.elementary_part -
                         quartic_expected_primitive) ||
       !is_zero(context, quartic_result.remainder -
                         quartic_expected_remainder) ||
       !is_zero(context,
           context.differentiate(quartic_result.elementary_part, x) +
               quartic_result.remainder - quartic)){
        std::cerr << "quartic partial hyperexponential reduction failed: "
                  << quartic_result.diagnostic << " elementary="
                  << quartic_result.elementary_part.to_string() << " remainder="
                  << quartic_result.remainder.to_string() << '\n';
        return 1;
    }

    exact_expr square = context.power(x, context.integer(2)) * exponential;
    risch_result square_result = context.integrate_elementary(square, x);
    exact_expr square_expected_primitive = x * exponential / context.integer(2);
    exact_expr square_expected_remainder = -exponential / context.integer(2);
    if(square_result.status != risch_status::proven_nonelementary ||
       !is_zero(context, square_result.elementary_part -
                         square_expected_primitive) ||
       !is_zero(context, square_result.remainder -
                         square_expected_remainder) ||
       !is_zero(context,
           context.differentiate(square_result.elementary_part, x) +
               square_result.remainder - square)){
        std::cerr << "quadratic partial hyperexponential reduction failed: "
                  << square_result.diagnostic << " elementary="
                  << square_result.elementary_part.to_string() << " remainder="
                  << square_result.remainder.to_string() << '\n';
        return 1;
    }

    exact_expr negative_exponential = context.exponential(
        -context.power(x, context.integer(2)));
    exact_expr negative_quartic =
        context.power(x, context.integer(4)) * negative_exponential;
    risch_result negative_result = context.integrate_elementary(
        negative_quartic, x);
    exact_expr negative_expected_primitive =
        (-context.power(x, context.integer(3)) / context.integer(2) -
         context.integer(3) * x / context.integer(4)) * negative_exponential;
    exact_expr negative_expected_remainder =
        context.integer(3) * negative_exponential / context.integer(4);
    if(negative_result.status != risch_status::proven_nonelementary ||
       !is_zero(context, negative_result.elementary_part -
                         negative_expected_primitive) ||
       !is_zero(context, negative_result.remainder -
                         negative_expected_remainder) ||
       !is_zero(context,
           context.differentiate(negative_result.elementary_part, x) +
               negative_result.remainder - negative_quartic)){
        std::cerr << "negative-rate hyperexponential reduction failed: "
                  << negative_result.diagnostic << " elementary="
                  << negative_result.elementary_part.to_string()
                  << " remainder=" << negative_result.remainder.to_string()
                  << '\n';
        return 1;
    }

    for(int degree = 0; degree <= 12; ++degree){
        exact_expr integrand = context.power(x, context.integer(degree)) *
                               exponential;
        risch_result result = context.integrate_elementary(integrand, x);
        risch_status expected_status = degree & 1
            ? risch_status::elementary : risch_status::proven_nonelementary;
        if(result.status != expected_status ||
           !is_zero(context,
               context.differentiate(result.elementary_part, x) +
                   result.remainder - integrand)){
            std::cerr << "polynomial degree sweep failed at degree "
                      << degree << ": " << result.diagnostic << '\n';
            return 1;
        }
    }

    exact_expr repeated_pole = exponential /
        context.power(x, context.integer(2));
    risch_result repeated_pole_result = context.integrate_elementary(
        repeated_pole, x);
    exact_expr repeated_pole_primitive = -exponential / x;
    exact_expr repeated_pole_remainder = context.integer(2) * exponential;
    if(repeated_pole_result.status != risch_status::proven_nonelementary ||
       !is_zero(context, repeated_pole_result.elementary_part -
                         repeated_pole_primitive) ||
       !is_zero(context, repeated_pole_result.remainder -
                         repeated_pole_remainder) ||
       !is_zero(context,
           context.differentiate(repeated_pole_result.elementary_part, x) +
               repeated_pole_result.remainder - repeated_pole)){
        std::cerr << "rational repeated-pole hyperexponential reduction failed: "
                  << repeated_pole_result.diagnostic << " elementary="
                  << repeated_pole_result.elementary_part.to_string()
                  << " remainder=" << repeated_pole_result.remainder.to_string()
                  << '\n';
        return 1;
    }

    exact_expr shifted_pole = exponential /
        context.power(x - context.integer(1), context.integer(2));
    risch_result shifted_pole_result = context.integrate_elementary(
        shifted_pole, x);
    exact_expr shifted_pole_primitive = -exponential /
        (x - context.integer(1));
    exact_expr shifted_pole_remainder = context.integer(2) * x * exponential /
        (x - context.integer(1));
    if(shifted_pole_result.status != risch_status::proven_nonelementary ||
       !is_zero(context, shifted_pole_result.elementary_part -
                         shifted_pole_primitive) ||
       !is_zero(context, shifted_pole_result.remainder -
                         shifted_pole_remainder) ||
       !is_zero(context,
           context.differentiate(shifted_pole_result.elementary_part, x) +
               shifted_pole_result.remainder - shifted_pole)){
        std::cerr << "shifted repeated-pole hyperexponential reduction failed: "
                  << shifted_pole_result.diagnostic << " elementary="
                  << shifted_pole_result.elementary_part.to_string()
                  << " remainder=" << shifted_pole_result.remainder.to_string()
                  << '\n';
        return 1;
    }

    exact_expr scale = context.symbol("scale");
    exact_expr scaled_repeated_pole = scale * repeated_pole;
    risch_result scaled_repeated_pole_result = context.integrate_elementary(
        scaled_repeated_pole, x);
    if(scaled_repeated_pole_result.status !=
           risch_status::proven_nonelementary ||
       !is_zero(context, scaled_repeated_pole_result.elementary_part -
                         scale * repeated_pole_primitive) ||
       !is_zero(context, scaled_repeated_pole_result.remainder -
                         scale * repeated_pole_remainder) ||
       std::find(scaled_repeated_pole_result.conditions.begin(),
                 scaled_repeated_pole_result.conditions.end(), scale) ==
           scaled_repeated_pole_result.conditions.end()){
        std::cerr << "symbolic-scale repeated-pole reduction failed: "
                  << scaled_repeated_pole_result.diagnostic << " elementary="
                  << scaled_repeated_pole_result.elementary_part.to_string()
                  << " remainder=" << scaled_repeated_pole_result.remainder.to_string()
                  << '\n';
        return 1;
    }

    exact_expr positive_scale = context.symbol("positive_scale");
    context.assume(positive_scale, "positive");
    risch_result positive_scaled_repeated_pole_result =
        context.integrate_elementary(positive_scale * repeated_pole, x);
    if(positive_scaled_repeated_pole_result.status !=
           risch_status::proven_nonelementary ||
       !is_zero(context,
           positive_scaled_repeated_pole_result.elementary_part -
               positive_scale * repeated_pole_primitive) ||
       !is_zero(context, positive_scaled_repeated_pole_result.remainder -
               positive_scale * repeated_pole_remainder) ||
       !positive_scaled_repeated_pole_result.conditions.empty()){
        std::cerr << "assumed-positive repeated-pole reduction failed: "
                  << positive_scaled_repeated_pole_result.diagnostic << '\n';
        return 1;
    }

    exact_expr a = context.symbol("a");
    exact_expr b = context.symbol("b");
    exact_expr symbolic_rational_cofactor =
        (a * (-x + context.integer(2) * context.power(x, context.integer(3))) +
         b * (context.integer(2) * context.power(x, context.integer(2)) -
              context.integer(2))) /
        context.power(x, context.integer(3));
    exact_expr symbolic_rational_input =
        symbolic_rational_cofactor * exponential;
    exact_expr symbolic_rational_expected =
        (a / x + b / context.power(x, context.integer(2))) * exponential;
    risch_result symbolic_rational_result = context.integrate_elementary(
        symbolic_rational_input, x);
    if(symbolic_rational_result.status != risch_status::elementary ||
       symbolic_rational_result.remainder != context.integer(0) ||
       !symbolic_rational_result.conditions.empty() ||
       !is_zero(context, symbolic_rational_result.elementary_part -
                         symbolic_rational_expected) ||
       !is_zero(context, context.differentiate(
           symbolic_rational_result.elementary_part, x) -
           symbolic_rational_input)){
        std::cerr << "symbolic numerator Hermite reduction failed: "
                  << symbolic_rational_result.diagnostic << " elementary="
                  << symbolic_rational_result.elementary_part.to_string()
                  << " remainder="
                  << symbolic_rational_result.remainder.to_string() << '\n';
        return 1;
    }

    exact_expr simple_pole = exponential / x;
    risch_result simple_pole_result = context.integrate_elementary(
        simple_pole, x);
    if(simple_pole_result.status != risch_status::proven_nonelementary ||
       simple_pole_result.elementary_part != context.integer(0) ||
       !is_zero(context, simple_pole_result.remainder - simple_pole)){
        std::cerr << "simple-pole hyperexponential classification regressed: "
                  << simple_pole_result.diagnostic << '\n';
        return 1;
    }

    std::cout << "risch hyperexponential polynomial reduction ok\n";
    return 0;
}
