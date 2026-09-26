#include"../src/prec_cas.cpp"
#include<cassert>
#include<cstdio>

int main(){
    using status = integration_parametric_rde_status;
    std::vector<std::vector<numeric_value>> matrix{
        {numeric_value(1), numeric_value(1), numeric_value(2)},
        {numeric_value(2), numeric_value(2), numeric_value(4)}};
    std::vector<numeric_value> particular;
    std::vector<std::vector<numeric_value>> kernel;
    assert(integration_solve_linear(matrix, 2, particular, &kernel));
    assert(particular[0] + particular[1] == numeric_value(2));
    assert(kernel.size() == 1 && kernel[0][0] + kernel[0][1] == numeric_value(0));
    matrix = {{numeric_value(0), numeric_value(1)}};
    assert(!integration_solve_linear(matrix, 1, particular, &kernel));
    assert(kernel.empty());
    std::vector<integration_parametric_rde_basis> basis;
    assert(integration_parametric_rde_polynomial({numeric_value(0)},
        {{numeric_value(1)}, {numeric_value(0), numeric_value(1)}}, basis) == status::solved);
    assert(basis.size() == 3); // Constant, integral of 1, integral of x.
    assert(basis[0].solution == integration_poly{numeric_value(1)});
    assert(basis[0].constants == std::vector<numeric_value>(2, numeric_value(0)));
    assert(integration_parametric_rde_polynomial({numeric_value(1)},
        {{numeric_value(0), numeric_value(1)}}, basis) == status::solved);
    assert(basis.size() == 1);
    assert((basis[0].solution == integration_poly{numeric_value(-1), numeric_value(1)}));
    assert(basis[0].constants[0] == numeric_value(1));
    assert(integration_parametric_rde_polynomial({numeric_value(0), numeric_value(2)},
        {{numeric_value(1)}}, basis) == status::solved);
    assert(basis.empty()); // y'+2xy=1 has no polynomial solution.
    assert(integration_parametric_rde_polynomial({numeric_value(0), numeric_value(2)},
        {{numeric_value(1)}, {numeric_value(1)}}, basis) == status::solved);
    assert(basis.size() == 1 && integration_zero_poly(basis[0].solution));
    assert(basis[0].constants[0] + basis[0].constants[1] == numeric_value(0));
    assert(integration_parametric_rde_polynomial({numeric_value(1)}, {}, basis) == status::solved);
    assert(basis.empty());
    assert(integration_parametric_rde_polynomial({numeric_value(0)}, {}, basis) == status::solved);
    assert(basis.size() == 1);
    assert(integration_parametric_rde_polynomial({numeric_value(1)},
        {{numeric_value(1)}}, basis, 1) == status::resource_limit);
    assert(basis.empty());
    for(int k = -3; k <= 3; ++k){
        integration_poly a{numeric_value(k), numeric_value(2)};
        integration_poly y{numeric_value(k + 1), numeric_value(-2), numeric_value(3)};
        integration_poly b = integration_add(integration_derivative_poly(y), integration_mul(a, y));
        assert(integration_parametric_rde_polynomial(a, {b}, basis) == status::solved);
        assert(basis.size() == 1 && basis[0].solution == y);
    }
    exact_context context;
    exact_expr x = context.symbol("x");
    for(const auto &argument : {x + context.integer(1),
            context.power(x, context.integer(2)) + context.integer(1),
            x / (x + context.integer(1))}){
        exact_expr t = context.natural_logarithm(argument);
        for(int degree : {2, 3}){
            exact_expr original = context.power(x + t, context.integer(degree));
            exact_expr f = context.simplify(context.expand(
                context.differentiate(original, x), 100000));
            integration_expr_poly coefficients;
            assert(integration_parse_expr_poly(context, f, t, coefficients));
            exact_expr candidate = integration_joint_primitive_polynomial(
                context, coefficients, t, x, risch_options());
            assert(candidate.valid());
            // The polynomial primitive is unique modulo a constant.
            exact_expr difference = context.simplify(context.expand(
                candidate - original, 100000));
            assert(!integration_depends_on(difference, x));
            assert(context.integrate_elementary(f, x).status == risch_status::elementary);
            risch_options tiny;
            tiny.maximum_matrix_entries = 1;
            assert(!integration_joint_primitive_polynomial(context, coefficients,
                t, x, tiny).valid());
        }
    }
    puts("parametric RDE and coupled primitive ok");
}
