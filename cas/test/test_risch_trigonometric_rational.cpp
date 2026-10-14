#include"../prec_cas.hpp"

#include<cassert>
#include<cstdio>

int main(){
    exact_context context;
    exact_expr x = context.symbol("x");

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

    exact_expr affine_hyperbolic_angle = context.integer(2) * x +
        context.integer(1);
    exact_expr affine_hyperbolic_integrand = context.integer(2) *
        context.hyperbolic_cosine(affine_hyperbolic_angle);
    risch_result affine_hyperbolic_result = context.integrate_elementary(
        affine_hyperbolic_integrand, x);
    assert(affine_hyperbolic_result.status == risch_status::elementary);
    assert(affine_hyperbolic_result.remainder == context.integer(0));

    std::puts("risch trigonometric rational ok");
    return 0;
}
