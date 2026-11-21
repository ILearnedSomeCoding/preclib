#include "../prec_cas.hpp"

#include <iostream>

static bool check_derivative(exact_context &context,
                             const exact_expr &primitive,
                             const exact_expr &integrand,
                             const exact_expr &variable){
    exact_expr error = context.differentiate(primitive, variable) - integrand;
    exact_expr x = variable;
    exact_expr x2 = context.power(x, context.integer(2));
    exact_expr exp_x = context.exponential(x);
    exact_expr exp_plus = context.exponential(x + context.i() * x2);
    exact_expr exp_minus = context.exponential(x - context.i() * x2);
    error = context.substitute(error, exp_plus,
        exp_x * (context.cosine(x2) + context.i() * context.sine(x2)));
    error = context.substitute(error, exp_minus,
        exp_x * (context.cosine(x2) - context.i() * context.sine(x2)));
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

    // The degree bound must not turn a failed polynomial RDE search into a
    // proof of non-elementarity.
    risch_result unsupported = context.integrate_elementary(sine, x);
    if(unsupported.status == risch_status::proven_nonelementary){
        std::cerr << "failed polynomial-angle RDE was misreported as a proof\n";
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
