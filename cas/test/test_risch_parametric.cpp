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
    puts("parametric RDE ok");
}
