#include "../prec_cas.hpp"

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

    std::cout << "risch hyperexponential polynomial reduction ok\n";
    return 0;
}
