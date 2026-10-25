#include"../src/prec_cas.cpp"

#include<cassert>
#include<cstdio>

int main(){
    exact_context context;
    exact_expr x = context.symbol("x");
    exact_expr parameter = context.symbol("_quadratic_curve_parameter");

    auto verify_derivative = [&](const exact_expr &result,
                                 const exact_expr &input,
                                 const exact_expr &radicand){
        exact_expr root = context.square_root(radicand);
        exact_expr derivative_error = context.substitute(
            context.differentiate(result,x)-input,root,parameter);
        integration_expr_poly reduced;
        assert(integration_parse_algebraic_quotient(context,derivative_error,
            parameter,{-radicand,context.integer(0),context.integer(1)},x,
            risch_options(),reduced));
        for(const exact_expr &coefficient : reduced)
            assert(coefficient == context.integer(0));
    };

    const exact_expr radicands[] = {
        x*x+context.integer(1),
        context.integer(4)*x*x+context.integer(4)*x+context.integer(5)
    };
    for(const exact_expr &radicand : radicands){
        exact_expr input = context.integer(1)/context.square_root(radicand);
        risch_result result = context.integrate_elementary(input,x);
        assert(result.status == risch_status::elementary);
        assert(result.remainder == context.integer(0));
        verify_derivative(result.elementary_part,input,radicand);
    }

    exact_expr radicand = x*x+context.integer(1);
    exact_expr root = context.square_root(radicand);
    for(const exact_expr &input : {
            context.integer(1)/(x*x*root), x/root,
            x*x/root, context.integer(1)/(x+root)}){
        risch_result result = context.integrate_elementary(input,x);
        assert(result.status == risch_status::elementary);
        assert(result.remainder == context.integer(0));
        verify_derivative(result.elementary_part,input,radicand);
    }

    std::puts("risch genus-0 quadratic curve ok");
    return 0;
}
