#include "../prec_cas.hpp"

#include <iostream>

static bool check_derivative(exact_context &context,
                             const exact_expr &primitive,
                             const exact_expr &integrand,
                             const exact_expr &variable){
    exact_expr x = variable;
    exact_expr x2 = context.power(x, context.integer(2));
    exact_expr exp_x = context.exponential(x);
    exact_expr exp_plus = context.exponential(x + context.i() * x2);
    exact_expr exp_minus = context.exponential(x - context.i() * x2);
    exact_expr rewritten = context.substitute(primitive, exp_plus,
        exp_x * (context.cosine(x2) + context.i() * context.sine(x2)));
    rewritten = context.substitute(rewritten, exp_minus,
        exp_x * (context.cosine(x2) - context.i() * context.sine(x2)));
    exact_expr error = context.differentiate(rewritten, variable) - integrand;
    return context.simplify(context.expand(error, 100000)) ==
           context.integer(0);
}

static bool check_trigonometric_derivative(exact_context &context,
                                           const exact_expr &primitive,
                                           const exact_expr &integrand,
                                           const exact_expr &variable){
    exact_expr x2 = context.power(variable, context.integer(2));
    exact_expr exp_plus = context.exponential(context.i() * x2);
    exact_expr exp_minus = context.exponential(-context.i() * x2);
    exact_expr error = context.differentiate(primitive, variable) - integrand;
    error = context.substitute(error, exp_plus,
        context.cosine(x2) + context.i() * context.sine(x2));
    error = context.substitute(error, exp_minus,
        context.cosine(x2) - context.i() * context.sine(x2));
    return context.simplify(context.expand(error, 100000)) ==
           context.integer(0);
}

static bool check_hyperbolic_derivative(exact_context &context,
                                         const exact_expr &primitive,
                                         const exact_expr &integrand,
                                         const exact_expr &variable){
    exact_expr x2 = context.power(variable, context.integer(2));
    exact_expr exp_plus = context.exponential(variable + x2);
    exact_expr exp_minus = context.exponential(variable - x2);
    exact_expr exp_x = context.exponential(variable);
    exact_expr rewritten = context.substitute(primitive, exp_plus,
        exp_x * (context.hyperbolic_cosine(x2) +
                 context.hyperbolic_sine(x2)));
    rewritten = context.substitute(rewritten, exp_minus,
        exp_x * (context.hyperbolic_cosine(x2) -
                 context.hyperbolic_sine(x2)));
    exact_expr error = context.differentiate(rewritten, variable) - integrand;
    return context.simplify(context.expand(error, 100000)) ==
           context.integer(0);
}

int main(){
    exact_context context;
    exact_expr x = context.symbol("x");
    exact_expr x2 = context.power(x, context.integer(2));
    exact_expr exp_x = context.exponential(x);
    exact_expr cosine = context.cosine(x2);
    exact_expr sine = context.sine(x2);

    // This cofactor is generated from Q = 1 + i*(2 - 2*x) in the
    // exp(x +/- i*x^2) modes; its mode rates are nonconstant polynomials.
    exact_expr polynomial = context.integer(4) * x2 -
        context.integer(4) * x + context.integer(1);
    exact_expr integrand = polynomial * exp_x * cosine;
    risch_result result = context.integrate_elementary(integrand, x);
    exact_expr expected = exp_x * (cosine +
        (context.integer(2) * x - context.integer(2)) * sine);
    if(result.status != risch_status::elementary ||
       result.remainder != context.integer(0) ||
       !check_derivative(context, result.elementary_part, integrand, x) ||
       !check_derivative(context, expected, integrand, x)){
        std::cerr << "polynomial-angle exponential mode failed: "
                  << result.diagnostic << "; got "
                  << result.elementary_part.to_string() << '\n';
        return 1;
    }
    exact_expr public_result = context.integrate(integrand, x);
    if(public_result.operation() == exact_opcode::integral ||
       !check_derivative(context, public_result, integrand, x)){
        std::cerr << "public integration did not accept the verified mode\n";
        return 1;
    }

    exact_expr hyperbolic_cosine = context.hyperbolic_cosine(x2);
    exact_expr hyperbolic_sine = context.hyperbolic_sine(x2);
    exact_expr rational_cofactor = context.integer(1) / x -
        context.integer(1) / x2 - context.integer(4) * x;
    exact_expr rational_integrand = rational_cofactor * exp_x *
        hyperbolic_cosine;
    exact_expr rational_expected = exp_x * (hyperbolic_cosine / x -
        context.integer(2) * hyperbolic_sine);
    risch_result rational_result = context.integrate_elementary(
        rational_integrand, x);
    if(rational_result.status != risch_status::elementary ||
       rational_result.remainder != context.integer(0) ||
       !check_hyperbolic_derivative(context, rational_result.elementary_part,
                                   rational_integrand, x) ||
       !check_hyperbolic_derivative(context, rational_expected,
                                   rational_integrand, x)){
        std::cerr << "rational-cofactor polynomial-angle RDE failed: "
                  << rational_result.diagnostic << "; got "
                  << rational_result.elementary_part.to_string() << '\n';
        return 1;
    }
    exact_expr circular_rational_cofactor = context.integer(4) * x +
        context.integer(1) / x - context.integer(1) / x2;
    exact_expr circular_rational_integrand = circular_rational_cofactor *
        exp_x * cosine;
    exact_expr circular_rational_expected = exp_x * (cosine / x +
        context.integer(2) * sine);
    risch_result circular_rational_result = context.integrate_elementary(
        circular_rational_integrand, x);
    if(circular_rational_result.status != risch_status::elementary ||
       circular_rational_result.remainder != context.integer(0) ||
       !circular_rational_result.conditions.empty() ||
       !check_derivative(context, circular_rational_result.elementary_part,
                         circular_rational_integrand, x) ||
       !check_derivative(context, circular_rational_expected,
                         circular_rational_integrand, x)){
        std::cerr << "complex-coefficient circular RDE failed: "
                  << circular_rational_result.diagnostic << "; got "
                  << circular_rational_result.elementary_part.to_string()
                  << '\n';
        return 1;
    }
    risch_options tiny_matrix;
    tiny_matrix.maximum_matrix_entries = 1;
    risch_result budget_result = context.integrate_elementary(
        rational_integrand, x, tiny_matrix);
    if(budget_result.status != risch_status::resource_limit){
        std::cerr << "rational modal RDE budget was not reported: "
                  << (int)budget_result.status << " "
                  << budget_result.diagnostic << '\n';
        return 1;
    }

    exact_expr chain_integrand = x * cosine;
    risch_result chain = context.integrate_elementary(chain_integrand, x);
    if(chain.status != risch_status::elementary ||
       chain.remainder != context.integer(0) ||
       !check_trigonometric_derivative(context, chain.elementary_part,
                                       chain_integrand, x)){
        std::cerr << "polynomial-angle trigonometric mode failed: "
                  << chain.diagnostic << '\n';
        return 1;
    }

    risch_result sine_non_elementary = context.integrate_elementary(sine, x);
    if(sine_non_elementary.status != risch_status::proven_nonelementary ||
       sine_non_elementary.elementary_part != context.integer(0) ||
       sine_non_elementary.remainder != sine){
        std::cerr << "sin(x^2) polynomial-phase obstruction was not certified: "
                  << sine_non_elementary.diagnostic << '\n';
        return 1;
    }
    exact_expr amplitude_parameter = context.symbol("amplitude");
    risch_result conditional_sine = context.integrate_elementary(
        amplitude_parameter * sine, x);
    if(conditional_sine.status != risch_status::proven_nonelementary ||
       conditional_sine.remainder != amplitude_parameter * sine ||
       conditional_sine.conditions.size() != 1 ||
       conditional_sine.conditions[0] != amplitude_parameter){
        std::cerr << "symbolic amplitude nonzero condition was lost: "
                  << conditional_sine.diagnostic << '\n';
        return 1;
    }
    if(context.integrate_elementary(context.integer(0) * sine, x).status !=
       risch_status::elementary){
        std::cerr << "zero amplitude was not treated as elementary zero\n";
        return 1;
    }
    exact_expr phase_parameter = context.symbol("phase_scale");
    risch_result symbolic_phase = context.integrate_elementary(
        context.sine(phase_parameter * x2), x);
    if(symbolic_phase.status == risch_status::proven_nonelementary){
        std::cerr << "symbolic phase degeneration was misclassified\n";
        return 1;
    }
    exact_expr x3 = context.power(x, context.integer(3));
    exact_expr cosine_x3 = context.cosine(x3);
    risch_result cosine_non_elementary = context.integrate_elementary(
        cosine_x3, x);
    if(cosine_non_elementary.status != risch_status::proven_nonelementary ||
       cosine_non_elementary.elementary_part != context.integer(0) ||
       cosine_non_elementary.remainder != cosine_x3){
        std::cerr << "cos(x^3) polynomial-phase obstruction was not certified: "
                  << cosine_non_elementary.diagnostic << '\n';
        return 1;
    }
    exact_expr polynomial_amplitude = x + context.integer(1);
    exact_expr weighted_sine_x3 = polynomial_amplitude * context.sine(x3);
    risch_result weighted_non_elementary = context.integrate_elementary(
        weighted_sine_x3, x);
    if(weighted_non_elementary.status != risch_status::proven_nonelementary ||
       weighted_non_elementary.remainder != weighted_sine_x3){
        std::cerr << "low-degree polynomial amplitude obstruction failed: "
                  << weighted_non_elementary.diagnostic << '\n';
        return 1;
    }
    exact_expr x2_sine_x2 = x2 * sine;
    risch_result x2_sine_x2_result = context.integrate_elementary(
        x2_sine_x2, x);
    if(x2_sine_x2_result.status != risch_status::proven_nonelementary ||
       x2_sine_x2_result.remainder != x2_sine_x2){
        std::cerr << "downward polynomial RDE obstruction failed: "
                  << x2_sine_x2_result.diagnostic << '\n';
        return 1;
    }
    exact_expr sine_over_x = sine / x;
    risch_result sine_over_x_result = context.integrate_elementary(
        sine_over_x, x);
    if(sine_over_x_result.status != risch_status::proven_nonelementary ||
       sine_over_x_result.remainder != sine_over_x){
        std::cerr << "simple-pole mode obstruction failed: "
                  << sine_over_x_result.diagnostic << '\n';
        return 1;
    }
    exact_expr sine_over_quadratic = sine / (x2 + context.integer(1));
    risch_result sine_over_quadratic_result = context.integrate_elementary(
        sine_over_quadratic, x);
    if(sine_over_quadratic_result.status !=
           risch_status::proven_nonelementary ||
       sine_over_quadratic_result.remainder != sine_over_quadratic){
        std::cerr << "complex simple-pole mode obstruction failed: "
                  << sine_over_quadratic_result.diagnostic << '\n';
        return 1;
    }
    for(const exact_expr &repeated_pole_input : {
            sine / x2,
            sine / context.power(x2 + context.integer(1),
                                context.integer(2)),
            sine / context.power(x2 + context.integer(1),
                                context.integer(3))}){
        risch_result repeated_pole_result = context.integrate_elementary(
            repeated_pole_input, x);
        if(repeated_pole_result.status != risch_status::proven_nonelementary ||
           repeated_pole_result.elementary_part != context.integer(0) ||
           repeated_pole_result.remainder != repeated_pole_input ||
           repeated_pole_result.diagnostic.find(
               "exact bounded rational RDE is inconsistent") ==
               std::string::npos){
            std::cerr << "repeated-pole mode RDE obstruction failed: "
                      << repeated_pole_result.diagnostic << "; got "
                      << repeated_pole_result.elementary_part.to_string()
                      << '\n';
            return 1;
        }
    }
    exact_expr repeated_pole_elementary_input =
        (context.integer(-4) - context.integer(3) /
            context.power(x, context.integer(4))) * sine;
    exact_expr repeated_pole_elementary_expected =
        context.integer(2) * cosine / x + sine /
            context.power(x, context.integer(3));
    risch_result repeated_pole_elementary_result = context.integrate_elementary(
        repeated_pole_elementary_input, x);
    if(repeated_pole_elementary_result.status != risch_status::elementary ||
       repeated_pole_elementary_result.remainder != context.integer(0) ||
       !check_trigonometric_derivative(context,
           repeated_pole_elementary_result.elementary_part,
           repeated_pole_elementary_input, x) ||
       !check_trigonometric_derivative(context,
           repeated_pole_elementary_expected,
           repeated_pole_elementary_input, x)){
        std::cerr << "elementary repeated-pole RDE was misclassified: "
                  << repeated_pole_elementary_result.diagnostic << '\n';
        return 1;
    }
    exact_expr symbolic_amplitude = context.symbol("amplitude");
    exact_expr symbolic_repeated_pole = symbolic_amplitude * sine / x2;
    risch_result symbolic_repeated_pole_result = context.integrate_elementary(
        symbolic_repeated_pole, x);
    if(symbolic_repeated_pole_result.status ==
           risch_status::proven_nonelementary &&
       (symbolic_repeated_pole_result.conditions.size() != 1 ||
        symbolic_repeated_pole_result.conditions[0] != symbolic_amplitude ||
        symbolic_repeated_pole_result.remainder != symbolic_repeated_pole)){
        std::cerr << "symbolic amplitude condition was not preserved\n";
        std::cerr << "  status=" << (int)symbolic_repeated_pole_result.status
                  << " diagnostic=" << symbolic_repeated_pole_result.diagnostic
                  << " remainder=" << symbolic_repeated_pole_result.remainder.to_string()
                  << " conditions=";
        for(const exact_expr &condition : symbolic_repeated_pole_result.conditions)
            std::cerr << condition.to_string() << ";";
        std::cerr << '\n';
        return 1;
    }
    exact_expr x_sine_x2 = x * sine;
    exact_expr x_sine_x2_primitive = -context.cosine(x2) /
        context.integer(2);
    risch_result x_sine_x2_result = context.integrate_elementary(x_sine_x2, x);
    if(x_sine_x2_result.status != risch_status::elementary ||
       x_sine_x2_result.remainder != context.integer(0) ||
       !check_trigonometric_derivative(context,
           x_sine_x2_result.elementary_part, x_sine_x2, x) ||
       !check_trigonometric_derivative(context, x_sine_x2_primitive,
           x_sine_x2, x)){
        std::cerr << "degree-bound neighboring elementary case failed: "
                  << x_sine_x2_result.diagnostic << '\n';
        return 1;
    }
    exact_expr nonpolynomial_angle = context.sine(context.exponential(x));
    risch_result unclassified = context.integrate_elementary(
        nonpolynomial_angle, x);
    if(unclassified.status == risch_status::proven_nonelementary){
        std::cerr << "unsupported nonpolynomial angle was misreported as a proof\n";
        return 1;
    }

    std::cout << "risch polynomial-angle rate cases ok\n";
}
