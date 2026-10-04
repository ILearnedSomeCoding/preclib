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
    std::puts("risch exponential rational ok");
}
