#include"../src/prec_cas.cpp"
#include<cassert>
#include<cstdio>

int main(){
    exact_context context;
    exact_expr x = context.symbol("x");
    exact_expr t = context.exponential(x);
    exact_expr l = context.natural_logarithm(x);
    exact_expr p = context.integer(1) + t*l;
    exact_expr q = context.integer(2) + t*l;
    exact_expr derivative = t*(l + context.integer(1)/x);
    exact_expr p2 = context.power(p, context.integer(2));
    exact_expr q2 = context.power(q, context.integer(2));

    exact_expr numerator = t*(p-derivative)*q2 + t*(q-derivative)*p2;
    exact_expr input = numerator/(p2*q2);
    exact_expr primitive = integration_mixed_linear_two_pole_primitive(
        context, input, x, risch_options());
    assert(primitive.valid());
    assert(integration_tower_rational_zero(context,
        context.differentiate(primitive, x)-input, x, 64, 100000));
    risch_result strict = context.integrate_elementary(input, x);
    assert(strict.status == risch_status::elementary);
    assert(strict.remainder == context.integer(0));

    assert(integration_tower_nonzero_witness(context,
        context.integer(1)-context.integer(1)/l, x, 64));
    exact_expr different = context.integer(3)+context.integer(2)*t*l;
    exact_expr different_derivative = context.integer(2)*derivative;
    exact_expr different2 = context.power(different, context.integer(2));
    exact_expr different_input =
        (t*(p-derivative)*different2 +
         t*(different-different_derivative)*p2)/(p2*different2);
    exact_expr different_primitive = integration_mixed_linear_two_pole_primitive(
        context, different_input, x, risch_options());
    assert(different_primitive.valid());
    assert(integration_tower_rational_zero(context,
        context.differentiate(different_primitive, x)-different_input,
        x, 64, 100000));

    exact_expr q3 = context.power(q, context.integer(3));
    exact_expr unequal_input =
        (t*(p-derivative)*q3 +
         t*(q-context.integer(2)*derivative)*p2)/(p2*q3);
    exact_expr unequal_primitive = integration_mixed_linear_two_pole_primitive(
        context, unequal_input, x, risch_options());
    assert(unequal_primitive.valid());
    exact_expr known = t/p + t/q2;
    assert(integration_tower_rational_zero(context,
        context.differentiate(known, x)-unequal_input,
        x, 64, 100000));
    assert(integration_tower_rational_zero(context,
        unequal_primitive-known, x, 64, 100000));
    assert(context.integrate_elementary(unequal_input, x).status ==
        risch_status::elementary);

    risch_options small_degree;
    small_degree.maximum_degree = 4;
    assert(!integration_mixed_linear_two_pole_primitive(context,
        unequal_input, x, small_degree).valid());
    exact_expr proportional = context.integer(2)*p;
    exact_expr noncoprime_input = t/(p2*context.power(proportional,
        context.integer(2)));
    assert(!integration_mixed_linear_two_pole_primitive(context,
        noncoprime_input, x, risch_options()).valid());
    std::puts("risch mixed two poles ok");
}
