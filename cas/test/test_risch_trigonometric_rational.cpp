#include"../prec_cas.hpp"

#include<cassert>
#include<cstdio>

int main(){
    exact_context context;
    exact_expr x = context.symbol("x");

    for(int degree : {4, 6, 8}){
        exact_expr denominator = context.power(x, context.integer(degree)) +
            context.integer(1);
        if(degree == 4)
            denominator = context.power(x, context.integer(4)) +
                context.power(x, context.integer(2)) + context.integer(1);
        exact_expr integrand = context.integer(1) / denominator;
        risch_result rational_result = context.integrate_elementary(
            integrand, x);
        assert(rational_result.status == risch_status::elementary);
        exact_expr expanded_primitive = context.expand(
            rational_result.elementary_part);
        exact_expr derivative_error = context.simplify(
            context.differentiate(expanded_primitive, x) - integrand);
        if(derivative_error != context.integer(0))
            std::fprintf(stderr, "degree %d derivative error: %s\n", degree,
                         derivative_error.to_string().c_str());
        assert(derivative_error == context.integer(0));
    }

    exact_expr irreducible_quartic = context.power(x, context.integer(4)) +
        context.power(x, context.integer(2)) + x + context.integer(1);
    exact_expr quartic_integrand = context.integer(1) / irreducible_quartic;
    risch_result quartic_result = context.integrate_elementary(
        quartic_integrand, x);
    assert(quartic_result.status == risch_status::elementary);
    exact_expr expanded_quartic = context.expand(
        quartic_result.elementary_part);
    assert(expanded_quartic.operation() == exact_opcode::log_root_sum);
    assert(context.simplify(context.differentiate(expanded_quartic, x) -
        quartic_integrand) == context.integer(0));

    exact_expr sine_x = context.sine(x);
    risch_result sine_result = context.integrate_elementary(sine_x, x);
    assert(sine_result.status == risch_status::elementary);
    assert(sine_result.remainder == context.integer(0));
    assert(sine_result.elementary_part.valid());

    exact_expr rational_trig = sine_x /
        (context.integer(2) + context.cosine(x));
    risch_result rational_trig_result = context.integrate_elementary(
        rational_trig, x);
    assert(rational_trig_result.status == risch_status::elementary);
    assert(rational_trig_result.remainder == context.integer(0));

    exact_expr tangent_result_input = context.tangent(x);
    risch_result tangent_result = context.integrate_elementary(
        tangent_result_input, x);
    assert(tangent_result.status == risch_status::elementary);
    assert(tangent_result.remainder == context.integer(0));

    exact_expr hyperbolic_rational = context.hyperbolic_sine(x) /
        (context.integer(2) + context.hyperbolic_cosine(x));
    risch_result hyperbolic_result = context.integrate_elementary(
        hyperbolic_rational, x);
    assert(hyperbolic_result.status == risch_status::elementary);
    assert(hyperbolic_result.remainder == context.integer(0));

    exact_expr hyperbolic_tangent = context.hyperbolic_tangent(x);
    risch_result hyperbolic_tangent_result = context.integrate_elementary(
        hyperbolic_tangent, x);
    assert(hyperbolic_tangent_result.status == risch_status::elementary);
    assert(hyperbolic_tangent_result.remainder == context.integer(0));

    exact_expr affine_angle = context.integer(2) * x + context.integer(1);
    exact_expr affine_integrand = context.integer(2) *
        context.cosine(affine_angle);
    risch_result affine_result = context.integrate_elementary(
        affine_integrand, x);
    if(affine_result.status != risch_status::elementary)
        std::fprintf(stderr, "affine status=%d diagnostic=%s remainder=%s\n",
            (int)affine_result.status, affine_result.diagnostic.c_str(),
            affine_result.remainder.valid()
                ? affine_result.remainder.to_string().c_str() : "<invalid>");
    assert(affine_result.status == risch_status::elementary);
    assert(affine_result.remainder == context.integer(0));

    exact_expr rational_slope_angle = x / context.integer(2) +
        context.rational(precq_t(precn_t(1), precn_t(3)));
    exact_expr rational_slope_integrand =
        context.cosine(rational_slope_angle) / context.integer(2);
    risch_result rational_slope_result = context.integrate_elementary(
        rational_slope_integrand, x);
    assert(rational_slope_result.status == risch_status::elementary);
    assert(rational_slope_result.remainder == context.integer(0));

    exact_expr phase = context.symbol("phase");
    for(const exact_expr &offset : {phase, context.pi() / context.integer(3)}){
        exact_expr shifted_angle = x + offset;
        exact_expr shifted_rational_trig = context.integer(1) /
            (context.integer(2) + context.cosine(shifted_angle));
        risch_result shifted_rational_trig_result =
            context.integrate_elementary(shifted_rational_trig, x);
        assert(shifted_rational_trig_result.status == risch_status::elementary);
        assert(shifted_rational_trig_result.remainder == context.integer(0));
    }

    exact_expr exponential_factor = context.exponential(context.integer(2) * x);
    exact_expr affine_trig_angle = context.integer(3) * x + context.integer(1);
    exact_expr exponential_sine = exponential_factor *
        context.sine(affine_trig_angle);
    risch_result exponential_sine_result = context.integrate_elementary(
        exponential_sine, x);
    assert(exponential_sine_result.status == risch_status::elementary);
    assert(exponential_sine_result.remainder == context.integer(0));
    assert(context.simplify(context.differentiate(
        exponential_sine_result.elementary_part, x) - exponential_sine) ==
        context.integer(0));

    exact_expr exponential_cosine = context.exponential(x) *
        context.cosine(context.integer(2) * x);
    risch_result exponential_cosine_result = context.integrate_elementary(
        exponential_cosine, x);
    assert(exponential_cosine_result.status == risch_status::elementary);
    assert(exponential_cosine_result.remainder == context.integer(0));
    assert(context.simplify(context.differentiate(
        exponential_cosine_result.elementary_part, x) -
        exponential_cosine) == context.integer(0));

    exact_expr a = context.symbol("a");
    exact_expr b = context.symbol("b");
    exact_expr symbolic_exponential_sine = context.exponential(a * x) *
        context.sine(b * x);
    risch_result symbolic_exponential_sine_result =
        context.integrate_elementary(symbolic_exponential_sine, x);
    assert(symbolic_exponential_sine_result.status == risch_status::elementary);
    assert(!symbolic_exponential_sine_result.conditions.empty());

    exact_expr exponential_hyperbolic_sine =
        context.exponential(context.integer(2) * x) *
        context.hyperbolic_sine(context.integer(3) * x + context.integer(1));
    risch_result exponential_hyperbolic_sine_result =
        context.integrate_elementary(exponential_hyperbolic_sine, x);
    assert(exponential_hyperbolic_sine_result.status ==
        risch_status::elementary);
    exact_expr hyperbolic_plus = context.exponential(
        context.integer(5) * x + context.integer(1));
    exact_expr hyperbolic_minus = context.exponential(-x - context.integer(1));
    assert(context.simplify(context.differentiate(
        exponential_hyperbolic_sine_result.elementary_part, x) -
        (hyperbolic_plus - hyperbolic_minus) / context.integer(2)) ==
        context.integer(0));

    exact_expr exponential_hyperbolic_cosine =
        context.exponential(context.integer(2) * x) *
        context.hyperbolic_cosine(context.integer(3) * x + context.integer(1));
    risch_result exponential_hyperbolic_cosine_result =
        context.integrate_elementary(exponential_hyperbolic_cosine, x);
    assert(exponential_hyperbolic_cosine_result.status ==
        risch_status::elementary);
    assert(context.simplify(context.differentiate(
        exponential_hyperbolic_cosine_result.elementary_part, x) -
        (hyperbolic_plus + hyperbolic_minus) / context.integer(2)) ==
        context.integer(0));

    exact_expr circular_angle = context.i() * x;
    exact_expr exponential_circular_hyperbolic = context.exponential(x) *
        context.sine(x) * context.hyperbolic_sine(context.integer(2) * x);
    risch_result exponential_circular_hyperbolic_result =
        context.integrate_elementary(exponential_circular_hyperbolic, x);
    assert(exponential_circular_hyperbolic_result.status ==
        risch_status::elementary);
    exact_expr quarter_i = context.i() / context.integer(4);
    exact_expr expanded_circular_hyperbolic =
        -quarter_i * context.exponential(context.integer(3) * x + circular_angle) +
         quarter_i * context.exponential(-x + circular_angle) +
         quarter_i * context.exponential(context.integer(3) * x - circular_angle) -
         quarter_i * context.exponential(-x - circular_angle);
    assert(context.simplify(context.differentiate(
        exponential_circular_hyperbolic_result.elementary_part, x) -
        expanded_circular_hyperbolic) ==
        context.integer(0));

    exact_expr exponential_sine_square = context.exponential(x) *
        context.power(context.sine(x), context.integer(2));
    risch_result exponential_sine_square_result = context.integrate_elementary(
        exponential_sine_square, x);
    assert(exponential_sine_square_result.status == risch_status::elementary);
    exact_expr expanded_exponential_sine_square =
        -context.exponential(x + context.integer(2) * circular_angle) /
            context.integer(4) +
         context.exponential(x) / context.integer(2) -
         context.exponential(x - context.integer(2) * circular_angle) /
            context.integer(4);
    assert(context.simplify(context.differentiate(
        exponential_sine_square_result.elementary_part, x) -
        expanded_exponential_sine_square) == context.integer(0));

    exact_expr resonant_hyperbolic = context.exponential(x) *
        context.hyperbolic_sine(x);
    risch_result resonant_hyperbolic_result = context.integrate_elementary(
        resonant_hyperbolic, x);
    assert(resonant_hyperbolic_result.status == risch_status::elementary);
    assert(context.simplify(context.differentiate(
        resonant_hyperbolic_result.elementary_part, x) -
        (context.exponential(context.integer(2) * x) - context.integer(1)) /
            context.integer(2)) == context.integer(0));

    exact_expr resonant_hyperbolic_cosine = context.exponential(x) *
        context.hyperbolic_cosine(x);
    risch_result resonant_hyperbolic_cosine_result =
        context.integrate_elementary(resonant_hyperbolic_cosine, x);
    assert(resonant_hyperbolic_cosine_result.status ==
        risch_status::elementary);
    assert(context.simplify(context.differentiate(
        resonant_hyperbolic_cosine_result.elementary_part, x) -
        (context.exponential(context.integer(2) * x) + context.integer(1)) /
            context.integer(2)) == context.integer(0));

    exact_expr symbolic_exponential_cosh = context.exponential(a * x) *
        context.hyperbolic_cosine(b * x);
    risch_result symbolic_exponential_cosh_result =
        context.integrate_elementary(symbolic_exponential_cosh, x);
    assert(symbolic_exponential_cosh_result.status == risch_status::elementary);
    assert(symbolic_exponential_cosh_result.conditions.size() == 2);

    exact_expr symbolic_exponential_sinh = context.exponential(a * x) *
        context.hyperbolic_sine(b * x);
    risch_result symbolic_exponential_sinh_result =
        context.integrate_elementary(symbolic_exponential_sinh, x);
    assert(symbolic_exponential_sinh_result.status == risch_status::elementary);
    assert(symbolic_exponential_sinh_result.conditions.size() == 2);

    exact_expr c = context.symbol("c");
    exact_expr symbolic_multiangle_hyperbolic = context.exponential(a * x) *
        context.hyperbolic_sine(b * x) * context.hyperbolic_cosine(c * x);
    risch_result symbolic_multiangle_result = context.integrate_elementary(
        symbolic_multiangle_hyperbolic, x);
    assert(symbolic_multiangle_result.status == risch_status::elementary);
    assert(symbolic_multiangle_result.conditions.size() == 4);
    exact_expr expanded_symbolic_multiangle =
        (context.exponential((a + b + c) * x) +
         context.exponential((a + b - c) * x) -
         context.exponential((a - b + c) * x) -
         context.exponential((a - b - c) * x)) / context.integer(4);
    assert(context.simplify(context.differentiate(
        symbolic_multiangle_result.elementary_part, x) -
        expanded_symbolic_multiangle) == context.integer(0));

    exact_expr affine_hyperbolic_angle = context.integer(2) * x +
        context.integer(1);
    exact_expr affine_hyperbolic_integrand = context.integer(2) *
        context.hyperbolic_cosine(affine_hyperbolic_angle);
    risch_result affine_hyperbolic_result = context.integrate_elementary(
        affine_hyperbolic_integrand, x);
    assert(affine_hyperbolic_result.status == risch_status::elementary);
    assert(affine_hyperbolic_result.remainder == context.integer(0));

    exact_expr exponential_sinh_square = context.exponential(x) *
        context.power(context.hyperbolic_sine(x), context.integer(2));
    risch_result exponential_sinh_square_result = context.integrate_elementary(
        exponential_sinh_square, x);
    assert(exponential_sinh_square_result.status == risch_status::elementary);
    exact_expr expanded_sinh_square =
        (context.exponential(context.integer(3) * x) -
         context.integer(2) * context.exponential(x) +
         context.exponential(-x)) / context.integer(4);
    assert(context.simplify(context.differentiate(
        exponential_sinh_square_result.elementary_part, x) -
        expanded_sinh_square) == context.integer(0));

    exact_expr exponential_sinh_cosh = context.exponential(x) *
        context.hyperbolic_sine(x) * context.hyperbolic_cosine(x);
    risch_result exponential_sinh_cosh_result = context.integrate_elementary(
        exponential_sinh_cosh, x);
    assert(exponential_sinh_cosh_result.status == risch_status::elementary);
    exact_expr expanded_sinh_cosh =
        (context.exponential(context.integer(3) * x) -
         context.exponential(-x)) / context.integer(4);
    assert(context.simplify(context.differentiate(
        exponential_sinh_cosh_result.elementary_part, x) -
        expanded_sinh_cosh) == context.integer(0));

    exact_expr mixed_hyperbolic_angles = context.exponential(x) *
        context.hyperbolic_sine(x) *
        context.hyperbolic_cosine(context.integer(2) * x);
    risch_result mixed_hyperbolic_angles_result = context.integrate_elementary(
        mixed_hyperbolic_angles, x);
    assert(mixed_hyperbolic_angles_result.status == risch_status::elementary);
    exact_expr expanded_mixed_hyperbolic =
        (context.exponential(context.integer(4) * x) + context.integer(1) -
         context.exponential(context.integer(2) * x) -
         context.exponential(-context.integer(2) * x)) / context.integer(4);
    assert(context.simplify(context.differentiate(
        mixed_hyperbolic_angles_result.elementary_part, x) -
        expanded_mixed_hyperbolic) == context.integer(0));

    exact_expr resonant_cosh_square = context.exponential(-context.integer(4) * x) *
        context.power(context.hyperbolic_cosine(context.integer(2) * x),
                      context.integer(2));
    risch_result resonant_cosh_square_result = context.integrate_elementary(
        resonant_cosh_square, x);
    assert(resonant_cosh_square_result.status == risch_status::elementary);
    exact_expr expanded_cosh_square = (context.integer(1) +
        context.integer(2) * context.exponential(-context.integer(4) * x) +
        context.exponential(-context.integer(8) * x)) / context.integer(4);
    assert(context.simplify(context.differentiate(
        resonant_cosh_square_result.elementary_part, x) -
        expanded_cosh_square) == context.integer(0));

    std::puts("risch trigonometric rational ok");
    return 0;
}
