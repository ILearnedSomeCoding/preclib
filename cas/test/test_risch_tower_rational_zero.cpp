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
    for(int order : {3, 4}){
        exact_expr pole = context.power(p, context.integer(order));
        exact_expr higher_input = t*(p-context.integer(order-1)*derivative)/pole;
        risch_result higher = context.integrate_elementary(higher_input, x);
        assert(higher.status == risch_status::elementary);
        assert(higher.remainder == context.integer(0));
        assert(integration_tower_rational_zero(context,
            context.differentiate(higher.elementary_part, x)-higher_input,
            x, 64, 100000));
    }
    exact_expr p2 = context.power(p, context.integer(2));
    exact_expr p3 = context.power(p, context.integer(3));
    exact_expr p4 = context.power(p, context.integer(4));
    exact_expr two_step_numerator =
        t*(p-context.integer(3)*derivative) +
        t*p*(p-context.integer(2)*derivative);
    exact_expr two_step_input = two_step_numerator/p4;
    risch_result two_step = context.integrate_elementary(two_step_input, x);
    assert(two_step.status == risch_status::elementary);
    assert(integration_tower_rational_zero(context,
        context.differentiate(two_step.elementary_part, x)-two_step_input,
        x, 64, 100000));
    assert(integration_tower_rational_zero(context,
        two_step_input-context.differentiate(t/p3+t/p2, x),
        x, 64, 100000));
    exact_expr vanishing = context.integer(1);
    for(int root : {1, 2, 3})
        vanishing = vanishing*context.power(x-context.integer(root),
            context.integer(2));
    exact_expr coefficient = context.integer(0), derivative_term = vanishing;
    for(int i = 0; i <= 6; ++i){
        coefficient = coefficient + (i % 2 ? -derivative_term : derivative_term);
        derivative_term = context.differentiate(derivative_term, x);
    }
    exact_expr sampled_w = -context.differentiate(coefficient, x)-coefficient;
    for(int root : {1, 2, 3}){
        assert(context.simplify(context.substitute(sampled_w, x,
            context.integer(root))) == context.integer(0));
        assert(context.simplify(context.substitute(
            context.differentiate(sampled_w, x), x,
            context.integer(root))) == context.integer(0));
    }
    assert(integration_tower_nonzero_witness(context, sampled_w, x, 64));
    assert(integration_rational_tower_polynomial_nonzero(t,
        {context.integer(1), coefficient}, x, 64));
    assert(!integration_rational_tower_polynomial_nonzero(t,
        {context.natural_logarithm(x)}, x, 64));
    exact_expr sampled_p = context.integer(1) + t*coefficient;
    exact_expr sampled_input = -context.differentiate(sampled_p, x)/
        context.power(sampled_p, context.integer(2));
    exact_expr sampled_primitive = integration_mixed_linear_hermite_primitive(
        context, sampled_input, x, risch_options());
    assert(sampled_primitive.valid());
    assert(integration_tower_rational_zero(context,
        context.differentiate(sampled_primitive, x)-sampled_input,
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
