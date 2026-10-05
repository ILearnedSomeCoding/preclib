#include"../src/prec_cas.cpp"
#include<cassert>
#include<cstdio>

int main(){
    exact_context context;
    exact_expr x = context.symbol("x");
    exact_expr t = context.exponential(x);
    exact_expr l = context.natural_logarithm(x);
    exact_expr u = t*l;
    exact_expr du = t*(l+context.integer(1)/x);
    exact_expr p = context.integer(1)+u;
    exact_expr q = context.integer(2)+u;
    exact_expr r = context.integer(3)+u;
    exact_expr p2 = context.power(p, context.integer(2));
    exact_expr q2 = context.power(q, context.integer(2));
    exact_expr r2 = context.power(r, context.integer(2));
    exact_expr numerator = t*(p-du)*q2*r2 +
        t*(q-du)*p2*r2 + t*(r-du)*p2*q2;
    exact_expr input = numerator/(p2*q2*r2);
    exact_expr known = t/p+t/q+t/r;
    exact_expr candidate = integration_mixed_linear_poles_primitive(
        context, input, x, risch_options());
    assert(candidate.valid());
    assert(integration_tower_rational_zero(context,
        context.differentiate(known, x)-input, x, 64, 100000));
    assert(integration_tower_rational_zero(context,
        candidate-known, x, 64, 100000));
    risch_result strict = context.integrate_elementary(input, x);
    assert(strict.status == risch_status::elementary);
    assert(strict.remainder == context.integer(0));

    exact_expr s = context.integer(3)+context.integer(2)*u;
    exact_expr ds = context.integer(2)*du;
    exact_expr s2 = context.power(s, context.integer(2));
    exact_expr q3 = context.power(q, context.integer(3));
    exact_expr mixed_input =
        (t*(p-du)*q3*s2 + t*(q-context.integer(2)*du)*p2*s2 +
         t*(s-ds)*p2*q3)/(p2*q3*s2);
    exact_expr mixed_known = t/p+t/q2+t/s;
    exact_expr mixed_candidate = integration_mixed_linear_poles_primitive(
        context, mixed_input, x, risch_options());
    assert(mixed_candidate.valid());
    assert(integration_tower_rational_zero(context,
        context.differentiate(mixed_known, x)-mixed_input,
        x, 64, 100000));
    assert(integration_tower_rational_zero(context,
        mixed_candidate-mixed_known, x, 64, 100000));
    assert(context.integrate_elementary(mixed_input, x).status ==
        risch_status::elementary);

    exact_expr fourth = context.integer(4)+u;
    exact_expr fourth2 = context.power(fourth, context.integer(2));
    exact_expr four_input =
        (numerator*fourth2 + t*(fourth-du)*p2*q2*r2)/
        (p2*q2*r2*fourth2);
    exact_expr four_known = known+t/fourth;
    exact_expr four_candidate = integration_mixed_linear_poles_primitive(
        context, four_input, x, risch_options());
    assert(four_candidate.valid());
    assert(integration_tower_rational_zero(context,
        context.differentiate(four_known, x)-four_input,
        x, 64, 100000));
    assert(integration_tower_rational_zero(context,
        four_candidate-four_known, x, 64, 100000));

    risch_options small_degree;
    small_degree.maximum_degree = 5;
    assert(!integration_mixed_linear_poles_primitive(context,
        input, x, small_degree).valid());
    exact_expr repeated = numerator/(p2*q2*context.power(
        context.integer(2)*p, context.integer(2)));
    assert(!integration_mixed_linear_poles_primitive(context,
        repeated, x, risch_options()).valid());
    std::puts("risch mixed linear poles ok");
}
