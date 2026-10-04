#include"../prec_cas.hpp"

#include<algorithm>
#include<cassert>
#include<cstdio>

int main(){
    exact_context context;
    exact_expr x = context.symbol("x");
    exact_expr t = context.exponential(x);
    risch_options options;
    options.maximum_recursion_depth = 1;

    exact_expr inputs[] = {
        context.integer(1) / (context.integer(1) + t +
            context.exponential(context.integer(2) * x)),
        context.integer(1) / (context.integer(1) + t +
            context.exponential(-x)),
        context.integer(1) / (context.integer(1) +
            context.exponential(x / context.integer(2)) + t)
    };
    for(const exact_expr &input : inputs){
        risch_result result = context.integrate_elementary(input, x, options);
        assert(result.status == risch_status::elementary);
        assert(result.remainder == context.integer(0));
    }
    exact_expr a = context.symbol("a");
    risch_result symbolic_quadratic = context.integrate_elementary(
        context.integer(1) /
            (context.integer(1) + t +
             a * context.exponential(context.integer(2) * x)),
        x, options);
    assert(symbolic_quadratic.status == risch_status::elementary);
    assert(symbolic_quadratic.remainder == context.integer(0));
    assert(std::find(symbolic_quadratic.conditions.begin(),
        symbolic_quadratic.conditions.end(), a) !=
        symbolic_quadratic.conditions.end());
    exact_expr discriminant = context.integer(1)-context.integer(4)*a;
    assert(std::find(symbolic_quadratic.conditions.begin(),
        symbolic_quadratic.conditions.end(), discriminant) !=
        symbolic_quadratic.conditions.end());
    exact_expr quadratic = context.integer(1)+t+
        a*context.power(t, context.integer(2));
    risch_result same_generator = context.integrate_elementary(
        context.integer(1)/quadratic, x, options);
    assert(same_generator.status == risch_status::elementary);
    risch_result long_numerator = context.integrate_elementary(
        (context.integer(1)+context.power(t, context.integer(4)))/quadratic,
        x, options);
    assert(long_numerator.status == risch_status::elementary);
    exact_expr b = context.symbol("b"), c = context.symbol("c");
    risch_result general_quadratic = context.integrate_elementary(
        context.integer(1)/(a+b*t+c*context.power(t, context.integer(2))),
        x, options);
    assert(general_quadratic.status == risch_status::elementary);
    assert(general_quadratic.remainder == context.integer(0));
    assert(std::find(general_quadratic.conditions.begin(),
        general_quadratic.conditions.end(), a) !=
        general_quadratic.conditions.end());
    assert(std::find(general_quadratic.conditions.begin(),
        general_quadratic.conditions.end(), c) !=
        general_quadratic.conditions.end());
    risch_result sparse_quadratic = context.integrate_elementary(
        context.integer(1)/(context.integer(1)+
            a*context.power(t, context.integer(2))), x, options);
    assert(sparse_quadratic.status == risch_status::elementary);
    risch_result shifted_quadratic = context.integrate_elementary(
        context.integer(1)/(context.integer(1)+t+
            a*context.exponential(context.integer(2)*x+context.integer(1))),
        x, options);
    assert(shifted_quadratic.status == risch_status::elementary);
    assert(shifted_quadratic.remainder == context.integer(0));
    exact_expr repeated_quadratic = a*a + context.integer(2)*a*b*t +
        b*b*context.power(t, context.integer(2));
    risch_result repeated_root = context.integrate_elementary(
        (context.integer(1)+context.power(t, context.integer(4)))/
            repeated_quadratic, x, options);
    assert(repeated_root.status == risch_status::elementary);
    assert(repeated_root.remainder == context.integer(0));
    assert(std::find(repeated_root.conditions.begin(),
        repeated_root.conditions.end(), a*a) != repeated_root.conditions.end());
    assert(std::find(repeated_root.conditions.begin(),
        repeated_root.conditions.end(), b*b) != repeated_root.conditions.end());
    risch_result zero_constant_quadratic = context.integrate_elementary(
        (context.integer(1)+context.power(t, context.integer(4)))/
            (b*t+c*context.power(t, context.integer(2))), x, options);
    assert(zero_constant_quadratic.status == risch_status::elementary);
    assert(zero_constant_quadratic.remainder == context.integer(0));
    assert(std::find(zero_constant_quadratic.conditions.begin(),
        zero_constant_quadratic.conditions.end(), b) !=
        zero_constant_quadratic.conditions.end());
    assert(std::find(zero_constant_quadratic.conditions.begin(),
        zero_constant_quadratic.conditions.end(), c) !=
        zero_constant_quadratic.conditions.end());
    exact_expr nonlinear_t = context.exponential(context.power(x,
        context.integer(2)));
    exact_expr nonlinear_denominator = a+b*nonlinear_t+
        c*context.power(nonlinear_t, context.integer(2));
    risch_result nonlinear_quadratic = context.integrate_elementary(
        context.integer(2)*x/nonlinear_denominator, x, options);
    assert(nonlinear_quadratic.status == risch_status::elementary);
    assert(nonlinear_quadratic.remainder == context.integer(0));
    assert(std::find(nonlinear_quadratic.conditions.begin(),
        nonlinear_quadratic.conditions.end(), a) !=
        nonlinear_quadratic.conditions.end());
    exact_expr related_nonlinear_denominator = a+b*nonlinear_t+
        c*context.exponential(context.integer(2)*context.power(x,
            context.integer(2)));
    risch_result related_nonlinear = context.integrate_elementary(
        context.integer(2)*x/related_nonlinear_denominator, x, options);
    assert(related_nonlinear.status == risch_status::elementary);
    assert(related_nonlinear.remainder == context.integer(0));
    assert(std::find(related_nonlinear.conditions.begin(),
        related_nonlinear.conditions.end(), c) !=
        related_nonlinear.conditions.end());
    risch_result nonlinear_repeated = context.integrate_elementary(
        context.integer(2)*x*(context.integer(1)+
            context.power(nonlinear_t, context.integer(4))) /
            (a*a+context.integer(2)*a*b*nonlinear_t+
             b*b*context.power(nonlinear_t, context.integer(2))),
        x, options);
    assert(nonlinear_repeated.status == risch_status::elementary);
    risch_result nonlinear_zero_constant = context.integrate_elementary(
        context.integer(2)*x /
            (b*nonlinear_t+c*context.power(nonlinear_t,
                context.integer(2))), x, options);
    assert(nonlinear_zero_constant.status == risch_status::elementary);
    risch_result symbolic_shift = context.integrate_elementary(
        context.integer(1)/(context.integer(1)+t+
            context.exponential(x+a)), x, options);
    assert(symbolic_shift.status == risch_status::elementary);
    assert(symbolic_shift.remainder == context.integer(0));
    exact_expr shifted_linear_coefficient = context.integer(1)+
        context.exponential(a);
    assert(std::find(symbolic_shift.conditions.begin(),
        symbolic_shift.conditions.end(), shifted_linear_coefficient) !=
        symbolic_shift.conditions.end());
    risch_result two_symbolic_shifts = context.integrate_elementary(
        context.integer(1)/(context.integer(1)+
            context.exponential(x+a)+
            context.exponential(context.integer(2)*x+b)), x, options);
    assert(two_symbolic_shifts.status == risch_status::elementary);
    risch_result nonlinear_symbolic_shifts = context.integrate_elementary(
        context.integer(2)*x/(context.integer(1)+
            context.exponential(context.power(x, context.integer(2))+a)+
            context.exponential(context.integer(2)*
                context.power(x, context.integer(2))+b)), x, options);
    assert(nonlinear_symbolic_shifts.status == risch_status::elementary);
    exact_expr symbolic_slope_t = context.exponential(a*x);
    risch_result symbolic_slope_linear = context.integrate_elementary(
        context.integer(1)/(context.integer(1)+symbolic_slope_t), x, options);
    assert(symbolic_slope_linear.status == risch_status::elementary);
    assert(std::find(symbolic_slope_linear.conditions.begin(),
        symbolic_slope_linear.conditions.end(), a) !=
        symbolic_slope_linear.conditions.end());
    risch_result symbolic_slope_quadratic = context.integrate_elementary(
        context.integer(1)/(b+symbolic_slope_t+
            c*context.power(symbolic_slope_t, context.integer(2))),
        x, options);
    assert(symbolic_slope_quadratic.status == risch_status::elementary);
    assert(std::find(symbolic_slope_quadratic.conditions.begin(),
        symbolic_slope_quadratic.conditions.end(), a) !=
        symbolic_slope_quadratic.conditions.end());
    exact_expr shifted_symbolic_slope_t = context.exponential(a*x+b);
    risch_result shifted_symbolic_slope = context.integrate_elementary(
        (context.integer(1)+context.power(shifted_symbolic_slope_t,
            context.integer(4))) /
            (context.integer(1)+shifted_symbolic_slope_t+
             c*context.power(shifted_symbolic_slope_t,
                 context.integer(2))), x, options);
    assert(shifted_symbolic_slope.status == risch_status::elementary);
    assert(std::find(shifted_symbolic_slope.conditions.begin(),
        shifted_symbolic_slope.conditions.end(), a) !=
        shifted_symbolic_slope.conditions.end());
    risch_result related_symbolic_slopes = context.integrate_elementary(
        context.integer(1)/(context.integer(1)+symbolic_slope_t+
            context.exponential(context.integer(2)*a*x+b)), x, options);
    assert(related_symbolic_slopes.status == risch_status::elementary);
    assert(std::find(related_symbolic_slopes.conditions.begin(),
        related_symbolic_slopes.conditions.end(), a) !=
        related_symbolic_slopes.conditions.end());
    risch_result fractional_symbolic_slopes = context.integrate_elementary(
        context.integer(1)/(context.integer(1)+
            context.exponential(a*x/context.integer(2))+
            symbolic_slope_t), x, options);
    assert(fractional_symbolic_slopes.status == risch_status::elementary);
    assert(!fractional_symbolic_slopes.conditions.empty());
    risch_result opposite_symbolic_slopes = context.integrate_elementary(
        context.integer(1)/(context.integer(1)+symbolic_slope_t+
            context.exponential(-a*x)), x, options);
    assert(opposite_symbolic_slopes.status == risch_status::elementary);
    exact_expr related_numeric_denominator = context.integer(1)+
        symbolic_slope_t+context.exponential(context.integer(2)*a*x);
    risch_result repeated_related_numeric = context.integrate_elementary(
        context.integer(1)/context.power(related_numeric_denominator,
            context.integer(2)), x, options);
    assert(repeated_related_numeric.status == risch_status::elementary);
    assert(!repeated_related_numeric.conditions.empty());
    risch_result independent_symbolic_slopes = context.integrate_elementary(
        context.integer(1)/(context.integer(1)+symbolic_slope_t+
            context.exponential(b*x)), x, options);
    assert(independent_symbolic_slopes.status != risch_status::elementary);
    risch_result shared_parameter_condition = context.integrate_elementary(
        context.integer(1)/(a+symbolic_slope_t+
            context.exponential(context.integer(2)*a*x)), x, options);
    assert(shared_parameter_condition.status == risch_status::elementary);
    assert(std::count(shared_parameter_condition.conditions.begin(),
        shared_parameter_condition.conditions.end(), a) == 1);
    risch_options tower_options;
    tower_options.maximum_recursion_depth = 4;
    exact_expr exp_x_squared = context.exponential(
        context.power(x, context.integer(2)));
    exact_expr related_rde_input = context.integer(2)*x*exp_x_squared +
        (context.integer(1)+context.integer(2)*
            context.power(x, context.integer(2))) *
        context.exponential(context.power(x, context.integer(2))+
            context.integer(1));
    risch_result related_rde = context.integrate_elementary(related_rde_input,
        x, tower_options);
    assert(related_rde.status == risch_status::elementary);
    assert(related_rde.remainder == context.integer(0));
    risch_result cancelled_nonelementary = context.integrate_elementary(
        context.exponential(context.power(x, context.integer(2))+
            context.integer(1)) - context.e()*exp_x_squared,
        x, tower_options);
    assert(cancelled_nonelementary.status == risch_status::elementary);
    assert(cancelled_nonelementary.remainder == context.integer(0));
    exact_expr log_x = context.natural_logarithm(x);
    risch_result mixed_exponential_primitive = context.integrate_elementary(
        exp_x_squared*(context.integer(2)*x*log_x +
            context.integer(1)/x), x, tower_options);
    assert(mixed_exponential_primitive.status == risch_status::elementary);
    assert(mixed_exponential_primitive.remainder == context.integer(0));
    assert(context.simplify(context.differentiate(
        mixed_exponential_primitive.elementary_part, x) -
        exp_x_squared*(context.integer(2)*x*log_x +
            context.integer(1)/x)) == context.integer(0));
    exact_expr mixed_pole_primitive = exp_x_squared*log_x/(x+context.integer(1));
    exact_expr mixed_pole_integrand = exp_x_squared *
        ((context.integer(2)*x/(x+context.integer(1)) -
          context.integer(1)/context.power(x+context.integer(1), context.integer(2))) *
            log_x + context.integer(1)/(x*(x+context.integer(1))));
    risch_result mixed_pole = context.integrate_elementary(
        mixed_pole_integrand, x, tower_options);
    assert(mixed_pole.status == risch_status::elementary);
    assert(mixed_pole.remainder == context.integer(0));
    assert(context.simplify(context.expand(
        context.differentiate(mixed_pole.elementary_part, x) -
        mixed_pole_integrand, 100000)) == context.integer(0));
    exact_expr mixed_denominator = context.integer(1) +
        context.exponential(x)*log_x;
    exact_expr mixed_denominator_derivative = context.exponential(x)*
        (log_x + context.integer(1)/x);
    risch_result mixed_repeated_pole = context.integrate_elementary(
        mixed_denominator_derivative /
            context.power(mixed_denominator, context.integer(2)),
        x, tower_options);
    assert(mixed_repeated_pole.status == risch_status::elementary);
    assert(mixed_repeated_pole.remainder == context.integer(0));
    assert(context.simplify(context.expand(
        context.differentiate(mixed_repeated_pole.elementary_part, x) -
        mixed_denominator_derivative /
            context.power(mixed_denominator, context.integer(2)),
        100000)) == context.integer(0));
    risch_result mixed_cubic_pole = context.integrate_elementary(
        context.integer(7)*mixed_denominator_derivative /
            context.power(mixed_denominator, context.integer(3)),
        x, tower_options);
    assert(mixed_cubic_pole.status == risch_status::elementary);
    assert(mixed_cubic_pole.remainder == context.integer(0));
    assert(context.simplify(context.expand(
        context.differentiate(mixed_cubic_pole.elementary_part, x) -
        context.integer(7)*mixed_denominator_derivative /
            context.power(mixed_denominator, context.integer(3)),
        100000)) == context.integer(0));
    risch_result unmatched_mixed_pole = context.integrate_elementary(
        context.exponential(x) /
            context.power(mixed_denominator, context.integer(2)),
        x, tower_options);
    assert(unmatched_mixed_pole.status != risch_status::elementary);
    risch_result missing_chain = context.integrate_elementary(
        context.integer(1)/nonlinear_denominator, x, options);
    assert(missing_chain.status != risch_status::elementary);
    std::puts("risch exponential rational ok");
}
