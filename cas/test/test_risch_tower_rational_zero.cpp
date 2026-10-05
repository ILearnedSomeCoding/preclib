#include"../src/prec_cas.cpp"
#include<cassert>
#include<cstdio>

int main(){
    exact_context context;
    exact_expr x = context.symbol("x");
    exact_expr t = context.exponential(x);
    exact_expr l = context.natural_logarithm(x);
    exact_expr p = context.integer(1) + t*l;
    exact_expr derivative = t*(l + context.integer(1)/x);
    exact_expr identity = context.differentiate(context.integer(1)/p, x) +
        derivative/context.power(p, context.integer(2));
    assert(integration_tower_rational_zero(context, identity, x, 64, 100000));
    assert(!integration_tower_rational_zero(context, identity +
        context.integer(1)/p, x, 64, 100000));
    exact_expr mixed_integrand = t*(context.integer(1)-t/x) /
        context.power(p, context.integer(2));
    exact_expr complicated_coefficient =
        (-context.integer(1)/(x*context.power(l, context.integer(2))) -
         context.integer(1)/l)*l/(l+context.integer(1)/x);
    assert(integration_reduce_in_primitive_field(context,
        complicated_coefficient, x, 64, 100000) == -context.integer(1)/l);
    risch_result mixed = context.integrate_elementary(mixed_integrand, x);
    assert(mixed.status == risch_status::elementary);
    assert(mixed.remainder == context.integer(0));
    assert(integration_tower_rational_zero(context,
        context.differentiate(mixed.elementary_part, x) - mixed_integrand,
        x, 64, 100000));
    exact_expr public_primitive = context.integrate(mixed_integrand, x);
    assert(public_primitive.operation() != exact_opcode::integral);
    assert(integration_tower_rational_zero(context,
        context.differentiate(public_primitive, x) - mixed_integrand,
        x, 64, 100000));
    exact_expr shifted_p = context.integer(2) + t*l;
    exact_expr shifted_input = t*(context.integer(2)-t/x) /
        context.power(shifted_p, context.integer(2));
    risch_result shifted = context.integrate_elementary(shifted_input, x);
    assert(shifted.status == risch_status::elementary);
    assert(shifted.remainder == context.integer(0));
    assert(integration_tower_rational_zero(context,
        context.differentiate(shifted.elementary_part, x) - shifted_input,
        x, 64, 100000));
    std::vector<exact_expr> stress_terms;
    for(int i = 1; i <= 512; ++i)
        stress_terms.push_back(context.power(x + context.integer(i),
            context.integer(2)));
    exact_expr substituted = context.substitute(context.add(stress_terms),
        x, x + context.integer(1));
    assert(substituted.valid());
    assert(!integration_depends_on(context.substitute(substituted, x,
        context.integer(1)), x));
    risch_options quick_rejection;
    quick_rejection.maximum_recursion_depth = 1;
    quick_rejection.maximum_matrix_entries = 128;
    risch_result wrong_numerator = context.integrate_elementary(
        t/context.power(p, context.integer(2)), x, quick_rejection);
    assert(wrong_numerator.status != risch_status::elementary);
    std::puts("risch tower rational zero ok");
}
