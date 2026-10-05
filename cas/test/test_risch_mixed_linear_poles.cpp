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

    // For p=x*exp(x), D(p)/p=1+1/x.  The lower-field RDE
    // y'-(1+1/x)y = 1/x-(1+1/x)log(x) has y=log(x).
    exact_expr special_pole = x*t;
    exact_expr lambda = context.integer(1)+context.integer(1)/x;
    exact_expr lower_solution = l;
    exact_expr special_rhs = context.differentiate(lower_solution, x) -
        lambda*lower_solution;
    exact_expr special_input = special_rhs/special_pole;
    exact_expr special_candidate = integration_mixed_linear_special_pole_primitive(
        context, special_input, special_pole, {special_rhs}, 1,
        context.integer(0), x, context.integer(1), context.integer(0), x,
        risch_options());
    assert(special_candidate.valid());
    assert(integration_tower_rational_zero(context,
        context.differentiate(special_candidate, x)-special_input,
        x, 64, 100000));
    risch_result special_result = context.integrate_elementary(special_input, x);
    assert(special_result.status == risch_status::elementary);
    assert(special_result.remainder == context.integer(0));
    assert(integration_tower_rational_zero(context,
        context.differentiate(special_result.elementary_part, x)-special_input,
        x, 64, 100000));

    exact_expr special_rhs_2 = context.integer(1)/x -
        context.integer(2)*lambda*lower_solution;
    exact_expr special_rhs_1 = context.integer(1) -
        (x+context.integer(1))*lower_solution;
    exact_expr repeated_special_numerator = special_rhs_2 +
        special_rhs_1*t;
    exact_expr repeated_special_input = repeated_special_numerator/
        context.power(special_pole, context.integer(2));
    exact_expr repeated_special_candidate =
        integration_mixed_linear_special_pole_primitive(context,
            repeated_special_input, special_pole,
            {special_rhs_2, special_rhs_1}, 2,
            context.integer(0), x, context.integer(1), context.integer(0), x,
            risch_options());
    assert(repeated_special_candidate.valid());
    assert(integration_tower_rational_zero(context,
        context.differentiate(repeated_special_candidate, x)-
            repeated_special_input, x, 64, 100000));

    exact_expr log_x1 = context.natural_logarithm(x+context.integer(1));
    exact_expr product_solution = lower_solution*log_x1;
    exact_expr product_rhs = context.differentiate(product_solution, x) -
        lambda*product_solution;
    exact_expr product_input = product_rhs/special_pole;
    exact_expr product_candidate = integration_mixed_linear_special_pole_primitive(
        context, product_input, special_pole, {product_rhs}, 1,
        context.integer(0), x, context.integer(1), context.integer(0), x,
        risch_options());
    assert(product_candidate.valid());
    assert(integration_tower_rational_zero(context,
        context.differentiate(product_candidate, x)-product_input,
        x, 64, 100000));
    risch_result product_result = context.integrate_elementary(product_input, x);
    assert(product_result.status == risch_status::elementary);
    assert(product_result.remainder == context.integer(0));
    assert(integration_tower_rational_zero(context,
        context.differentiate(product_result.elementary_part, x)-product_input,
        x, 64, 100000));

    exact_expr approximate = context.value(numeric_value(Number(0.5)));
    exact_expr approximate_rhs = approximate*lower_solution;
    assert(!integration_mixed_linear_special_pole_primitive(context,
        approximate_rhs/special_pole, special_pole, {approximate_rhs}, 1,
        context.integer(0), x, context.integer(1), context.integer(0), x,
        risch_options()).valid());
    std::puts("risch mixed linear poles ok");
}
