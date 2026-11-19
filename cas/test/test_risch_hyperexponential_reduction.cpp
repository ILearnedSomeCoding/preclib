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

    exact_expr two_repeated_poles = exponential /
        (context.power(x, context.integer(2)) *
         context.power(x + context.integer(1), context.integer(2)));
    risch_result two_repeated_poles_result = context.integrate_elementary(
        two_repeated_poles, x);
    exact_expr two_repeated_poles_primitive =
        (-context.integer(2) * x - context.integer(1)) * exponential /
        (x * (x + context.integer(1)));
    exact_expr two_repeated_poles_remainder =
        context.integer(2) * (context.integer(2) * x - context.integer(1)) *
        exponential / x;
    if(two_repeated_poles_result.status !=
           risch_status::proven_nonelementary ||
       two_repeated_poles_result.elementary_part.to_string() !=
           two_repeated_poles_primitive.to_string() ||
       two_repeated_poles_result.remainder.to_string() !=
           two_repeated_poles_remainder.to_string()){
        std::cerr << "multiple repeated-pole hyperexponential reduction failed: "
                  << "status=" << (int)two_repeated_poles_result.status << ' '
                  << two_repeated_poles_result.diagnostic << " elementary="
                  << two_repeated_poles_result.elementary_part.to_string()
                  << " remainder="
                  << two_repeated_poles_result.remainder.to_string() << '\n';
        return 1;
    }

    exact_expr pole_shift = context.symbol("pole_shift");
    exact_expr symbolic_two_repeated_poles = exponential /
        (context.power(x, context.integer(2)) *
         context.power(x + pole_shift, context.integer(2)));
    risch_result symbolic_two_repeated_poles_result =
        context.integrate_elementary(symbolic_two_repeated_poles, x);
    if(symbolic_two_repeated_poles_result.status !=
           risch_status::proven_nonelementary ||
       symbolic_two_repeated_poles_result.elementary_part ==
           context.integer(0) ||
       symbolic_two_repeated_poles_result.remainder == context.integer(0) ||
       std::find(symbolic_two_repeated_poles_result.conditions.begin(),
                 symbolic_two_repeated_poles_result.conditions.end(),
                 pole_shift) ==
           symbolic_two_repeated_poles_result.conditions.end()){
        std::cerr << "parameterized multiple-pole Hermite reduction failed: "
                  << "status="
                  << (int)symbolic_two_repeated_poles_result.status << ' '
                  << symbolic_two_repeated_poles_result.diagnostic
                  << " elementary="
                  << symbolic_two_repeated_poles_result.elementary_part.to_string()
                  << " remainder="
                  << symbolic_two_repeated_poles_result.remainder.to_string()
                  << " conditions=";
        for(const exact_expr &condition :
                symbolic_two_repeated_poles_result.conditions)
            std::cerr << condition.to_string() << ',';
        std::cerr << '\n';
        return 1;
    }

    exact_context assumed_pole_context;
    exact_expr assumed_x = assumed_pole_context.symbol("x");
    exact_expr assumed_pole_shift = assumed_pole_context.symbol("pole_shift");
    assumed_pole_context.assume(assumed_pole_shift, "positive");
    exact_expr assumed_two_pole_integrand =
        assumed_pole_context.exponential(
            assumed_pole_context.power(assumed_x,
                                      assumed_pole_context.integer(2))) /
        (assumed_pole_context.power(assumed_x,
                                    assumed_pole_context.integer(2)) *
         assumed_pole_context.power(
             assumed_x + assumed_pole_shift,
             assumed_pole_context.integer(2)));
    if(assumed_pole_context.integrate_elementary(
           assumed_two_pole_integrand, assumed_x).status !=
       risch_status::proven_nonelementary){
        std::cerr << "positive pole-shift multi-pole reduction failed\n";
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

    exact_expr denominator_scale = context.symbol("denominator_scale");
    exact_expr scaled_denominator_cofactor =
        (-x + context.integer(2) * context.power(x, context.integer(3))) /
        (denominator_scale * context.power(x, context.integer(3)));
    exact_expr scaled_denominator_input = scaled_denominator_cofactor *
        exponential;
    exact_expr scaled_denominator_expected = exponential /
        (denominator_scale * x);
    risch_result scaled_denominator_result = context.integrate_elementary(
        scaled_denominator_input, x);
    if(scaled_denominator_result.status != risch_status::elementary ||
       scaled_denominator_result.remainder != context.integer(0) ||
       std::find(scaled_denominator_result.conditions.begin(),
                 scaled_denominator_result.conditions.end(), denominator_scale) ==
           scaled_denominator_result.conditions.end() ||
       !is_zero(context, scaled_denominator_result.elementary_part -
                         scaled_denominator_expected) ||
       !is_zero(context, context.differentiate(
           scaled_denominator_result.elementary_part, x) -
           scaled_denominator_input)){
        std::cerr << "scaled symbolic denominator Hermite reduction failed: "
                  << scaled_denominator_result.diagnostic << " elementary="
                  << scaled_denominator_result.elementary_part.to_string()
                  << " remainder="
                  << scaled_denominator_result.remainder.to_string() << '\n';
        return 1;
    }

    exact_expr shift = context.symbol("shift");
    exact_expr shifted_linear = x + shift;
    exact_expr symbolic_denominator_cofactor =
        (context.integer(2) * context.power(x, context.integer(3)) +
         context.integer(2) * shift * context.power(x, context.integer(2)) -
         x + shift) /
        context.power(shifted_linear, context.integer(3));
    exact_expr symbolic_denominator_input =
        symbolic_denominator_cofactor * exponential;
    exact_expr symbolic_denominator_expected = x * exponential /
        (context.power(shift, context.integer(2)) +
         context.integer(2) * shift * x + context.power(x, context.integer(2)));
    risch_result symbolic_denominator_result = context.integrate_elementary(
        symbolic_denominator_input, x);
    // The RDE solver certifies the coefficient identity exactly. The generic
    // differentiator currently does not canonicalize this symbolic quotient.
    if(symbolic_denominator_result.status != risch_status::elementary ||
       symbolic_denominator_result.remainder != context.integer(0) ||
       !symbolic_denominator_result.conditions.empty() ||
       !is_zero(context, symbolic_denominator_result.elementary_part -
                         symbolic_denominator_expected)){
        std::cerr << "general symbolic denominator RDE failed: "
                  << symbolic_denominator_result.diagnostic << " elementary="
                  << symbolic_denominator_result.elementary_part.to_string()
                  << " remainder="
                  << symbolic_denominator_result.remainder.to_string()
                  << " status=" << (int)symbolic_denominator_result.status
                  << " conditions=" << symbolic_denominator_result.conditions.size()
                  << " primitive_match=" << is_zero(context,
                      symbolic_denominator_result.elementary_part -
                          symbolic_denominator_expected) << '\n';
        return 1;
    }

    exact_expr linear_exponential = context.exponential(x);
    exact_expr shifted_parameter = context.symbol("pole_shift");
    exact_expr shifted_repeated_pole = linear_exponential /
        context.power(x + shifted_parameter, context.integer(2));
    risch_result shifted_repeated_pole_result = context.integrate_elementary(
        shifted_repeated_pole, x);
    exact_expr shifted_repeated_pole_elementary = -linear_exponential /
        (x + shifted_parameter);
    exact_expr shifted_repeated_pole_remainder = linear_exponential /
        (x + shifted_parameter);
    if(shifted_repeated_pole_result.status !=
           risch_status::proven_nonelementary ||
       !is_zero(context, shifted_repeated_pole_result.elementary_part -
                         shifted_repeated_pole_elementary) ||
       !is_zero(context, shifted_repeated_pole_result.remainder -
                         shifted_repeated_pole_remainder) ||
       !is_zero(context,
           context.differentiate(
               shifted_repeated_pole_result.elementary_part, x) +
               shifted_repeated_pole_result.remainder -
               shifted_repeated_pole)){
        std::cerr << "symbolic-parameter partial Hermite reduction failed: "
                  << shifted_repeated_pole_result.diagnostic << " elementary="
                  << shifted_repeated_pole_result.elementary_part.to_string()
                  << " remainder="
                  << shifted_repeated_pole_result.remainder.to_string()
                  << " status=" << (int)shifted_repeated_pole_result.status
                  << '\n';
        return 1;
    }

    exact_expr quadratic_shifted_pole = exponential /
        context.power(x + shifted_parameter, context.integer(2));
    risch_result quadratic_shifted_pole_result = context.integrate_elementary(
        quadratic_shifted_pole, x);
    exact_expr quadratic_shifted_elementary = -exponential /
        (x + shifted_parameter);
    exact_expr quadratic_shifted_remainder = context.integer(2) * x *
        exponential / (x + shifted_parameter);
    bool excludes_degenerate_pole = false;
    for(const exact_expr &condition : quadratic_shifted_pole_result.conditions){
        exact_expr ratio = context.simplify(condition / shifted_parameter);
        if(ratio.is_value() && !ratio.value().is_approximate() &&
           !ratio.value().is_zero()) excludes_degenerate_pole = true;
    }
    bool partial_primitive_matches = is_zero(context,
        quadratic_shifted_pole_result.elementary_part -
            quadratic_shifted_elementary);
    bool partial_remainder_matches = is_zero(context,
        quadratic_shifted_pole_result.remainder -
            quadratic_shifted_remainder);
    // The RDE matrix in the integrator verifies this coefficient identity;
    // this CAS differentiator does not yet fully cancel symbolic denominators.
    if(quadratic_shifted_pole_result.status !=
           risch_status::proven_nonelementary ||
       !partial_primitive_matches || !partial_remainder_matches ||
       !excludes_degenerate_pole){
        std::cerr << "specialized-pole condition was not retained: "
                  << quadratic_shifted_pole_result.diagnostic
                  << " elementary="
                  << quadratic_shifted_pole_result.elementary_part.to_string()
                  << " remainder="
                  << quadratic_shifted_pole_result.remainder.to_string()
                  << " conditions="
                  << quadratic_shifted_pole_result.conditions.size()
                  << " checks=" << partial_primitive_matches << ','
                  << partial_remainder_matches << ','
                  << excludes_degenerate_pole << '\n';
        return 1;
    }

    exact_expr rate_parameter = context.symbol("rate_parameter");
    exact_expr parameter_rate_exponential = context.exponential(
        rate_parameter * context.power(x, context.integer(2)));
    exact_expr parameter_rate_pole = parameter_rate_exponential /
        context.power(x + shifted_parameter, context.integer(2));
    risch_result parameter_rate_pole_result = context.integrate_elementary(
        parameter_rate_pole, x);
    exact_expr parameter_rate_elementary = -parameter_rate_exponential /
        (x + shifted_parameter);
    exact_expr parameter_rate_remainder = context.integer(2) *
        rate_parameter * x * parameter_rate_exponential /
            (x + shifted_parameter);
    auto conditions_exclude = [&](const exact_expr &degenerate_parameter){
        for(const exact_expr &condition : parameter_rate_pole_result.conditions)
            if(is_zero(context, context.substitute(condition,
                    degenerate_parameter, context.integer(0)))) return true;
        return false;
    };
    bool rate_and_pole_degeneracy_excluded =
        conditions_exclude(rate_parameter) &&
        conditions_exclude(shifted_parameter);
    if(parameter_rate_pole_result.status !=
           risch_status::proven_nonelementary ||
       !is_zero(context, parameter_rate_pole_result.elementary_part -
                         parameter_rate_elementary) ||
       !is_zero(context, parameter_rate_pole_result.remainder -
                         parameter_rate_remainder) ||
       !rate_and_pole_degeneracy_excluded){
        std::cerr << "conditional symbolic-rate Hermite reduction failed: "
                  << parameter_rate_pole_result.diagnostic
                  << " elementary="
                  << parameter_rate_pole_result.elementary_part.to_string()
                  << " remainder="
                  << parameter_rate_pole_result.remainder.to_string()
                  << " conditions=";
        for(const exact_expr &condition : parameter_rate_pole_result.conditions)
            std::cerr << condition.to_string() << ';';
        std::cerr << '\n';
        return 1;
    }

    exact_expr parameter_rate_triple_pole = parameter_rate_exponential /
        context.power(x + shifted_parameter, context.integer(3));
    risch_result parameter_rate_triple_result = context.integrate_elementary(
        parameter_rate_triple_pole, x);
    exact_expr parameter_rate_triple_elementary =
        -parameter_rate_exponential /
            (context.integer(2) * context.power(
                x + shifted_parameter, context.integer(2))) +
        rate_parameter * shifted_parameter * parameter_rate_exponential /
            (x + shifted_parameter);
    exact_expr parameter_rate_triple_remainder =
        (rate_parameter - context.integer(2) * rate_parameter *
            rate_parameter * shifted_parameter * x) *
            parameter_rate_exponential /
            (x + shifted_parameter);
    if(parameter_rate_triple_result.status !=
           risch_status::proven_nonelementary ||
       !is_zero(context, parameter_rate_triple_result.elementary_part -
                         parameter_rate_triple_elementary) ||
       !is_zero(context, parameter_rate_triple_result.remainder -
                         parameter_rate_triple_remainder) ||
       !conditions_exclude(rate_parameter) ||
       !conditions_exclude(shifted_parameter)){
        std::cerr << "conditional triple-pole Hermite reduction failed: "
                  << parameter_rate_triple_result.diagnostic
                  << " elementary="
                  << parameter_rate_triple_result.elementary_part.to_string()
                  << " remainder="
                  << parameter_rate_triple_result.remainder.to_string()
                  << " conditions=";
        for(const exact_expr &condition : parameter_rate_triple_result.conditions)
            std::cerr << condition.to_string() << ';';
        std::cerr << '\n';
        return 1;
    }

    exact_expr parameter_rate_linear_numerator = x *
        parameter_rate_exponential /
            context.power(x + shifted_parameter, context.integer(2));
    risch_result parameter_rate_linear_numerator_result =
        context.integrate_elementary(parameter_rate_linear_numerator, x);
    exact_expr parameter_rate_linear_numerator_elementary =
        shifted_parameter * parameter_rate_exponential /
            (x + shifted_parameter);
    exact_expr parameter_rate_linear_numerator_remainder =
        (context.integer(1) - context.integer(2) * shifted_parameter *
            rate_parameter * x) * parameter_rate_exponential /
            (x + shifted_parameter);
    if(parameter_rate_linear_numerator_result.status !=
           risch_status::proven_nonelementary ||
       !is_zero(context,
           parameter_rate_linear_numerator_result.elementary_part -
               parameter_rate_linear_numerator_elementary) ||
       !is_zero(context,
           parameter_rate_linear_numerator_result.remainder -
               parameter_rate_linear_numerator_remainder)){
        std::cerr << "symbolic affine-pole polynomial numerator reduction "
                     "failed: "
                  << parameter_rate_linear_numerator_result.diagnostic
                  << " elementary="
                  << parameter_rate_linear_numerator_result.elementary_part.to_string()
                  << " remainder="
                  << parameter_rate_linear_numerator_result.remainder.to_string()
                  << '\n';
        return 1;
    }

    exact_expr scaled_linear_pole = context.integer(2) * x +
        context.integer(1);
    exact_expr swept_numerator = context.power(x, context.integer(2)) +
        context.integer(3) * x + context.integer(2);
    for(int64_t order = 2; order <= 8; ++order){
        exact_expr swept_integrand = swept_numerator * exponential /
            context.power(scaled_linear_pole, context.integer(order));
        risch_result swept_result = context.integrate_elementary(
            swept_integrand, x);
        bool supported_status = swept_result.status == risch_status::elementary ||
            swept_result.status == risch_status::proven_nonelementary;
        if(!supported_status ||
           is_zero(context, swept_result.elementary_part)){
            std::cerr << "affine repeated-pole order sweep failed at order "
                      << order << " status=" << (int)swept_result.status
                      << ": " << swept_result.diagnostic
                      << " elementary="
                      << swept_result.elementary_part.to_string()
                      << " remainder=" << swept_result.remainder.to_string()
                      << '\n';
            return 1;
        }
    }
    risch_options tiny_rde_budget;
    tiny_rde_budget.maximum_matrix_entries = 1;
    risch_result limited_symbolic_denominator_result =
        context.integrate_elementary(symbolic_denominator_input, x,
                                     tiny_rde_budget);
    if(limited_symbolic_denominator_result.status !=
       risch_status::resource_limit){
        std::cerr << "symbolic denominator RDE budget status failed: "
                  << (int)limited_symbolic_denominator_result.status << ' '
                  << limited_symbolic_denominator_result.diagnostic
                  << " elementary="
                  << limited_symbolic_denominator_result.elementary_part.to_string()
                  << " remainder="
                  << limited_symbolic_denominator_result.remainder.to_string()
                  << '\n';
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
