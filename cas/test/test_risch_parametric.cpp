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
    std::vector<integration_parametric_rational_basis> rational_basis;
    assert(integration_parametric_rde_rational({numeric_value(1)},
        {{{numeric_value(0), numeric_value(1)},
          {numeric_value(1), numeric_value(2), numeric_value(1)}}},
        rational_basis) == status::solved);
    assert(rational_basis.size() == 1);
    assert((rational_basis[0].numerator == integration_poly{numeric_value(1)}));
    assert((rational_basis[0].denominator == integration_poly{numeric_value(1), numeric_value(1)}));
    assert(rational_basis[0].constants[0] == numeric_value(1));
    assert(integration_parametric_rde_rational({numeric_value(1)},
        {{{numeric_value(1)}, {numeric_value(0), numeric_value(1)}},
         {{numeric_value(-1), numeric_value(1)}, {numeric_value(0), numeric_value(1)}}},
        rational_basis) == status::solved);
    assert(rational_basis.size() == 1);
    assert(rational_basis[0].constants[0] == rational_basis[0].constants[1]);
    assert(integration_parametric_rde_rational({numeric_value(0)},
        {{{numeric_value(1)}, {numeric_value(0), numeric_value(1)}}},
        rational_basis) == status::solved);
    assert(rational_basis.size() == 1 && rational_basis[0].constants[0].is_zero());
    assert(integration_parametric_rde_rational({numeric_value(1)},
        {{{numeric_value(1)}, {numeric_value(0), numeric_value(1)}}},
        rational_basis) == status::solved);
    assert(rational_basis.empty());
    assert(integration_parametric_rde_rational({numeric_value(1)},
        {{{numeric_value(1)}, {numeric_value(1)}}}, rational_basis, 1) == status::resource_limit);
    assert(rational_basis.empty());
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
    for(const auto &h : {x, context.power(x, context.integer(2)) + context.integer(1)}){
        for(int power : {-2, 1, 3}){
            exact_expr u = context.power(h, context.integer(power));
            exact_expr a = context.differentiate(u, x) / u;
            integration_poly an, ad;
            assert(integration_parse_rational(a, x, an, ad));
            assert(integration_parametric_rde_gauged(context, an, ad, {}, x,
                rational_basis, risch_options()) == status::solved);
            assert(rational_basis.size() == 1);
            exact_expr y = (x + context.integer(3)) / (x + context.integer(2));
            a = a + context.integer(1);
            exact_expr b = context.differentiate(y, x) + a * y;
            integration_poly bn, bd, yn, yd;
            assert(integration_parse_rational(a, x, an, ad));
            assert(integration_parse_rational(b, x, bn, bd));
            assert(integration_parse_rational(y, x, yn, yd));
            assert(integration_parametric_rde_gauged(context, an, ad, {{bn, bd}},
                x, rational_basis, risch_options()) == status::solved);
            assert(rational_basis.size() == 1);
            integration_poly lhs = integration_mul(rational_basis[0].numerator, yd);
            integration_poly rhs = integration_mul(yn, rational_basis[0].denominator);
            for(auto &v : rhs) v = v * rational_basis[0].constants[0];
            assert(lhs == rhs);
            exact_expr inner = x + context.integer(power) * context.natural_logarithm(h);
            exact_expr candidate = integration_hyperexponential_rational(context, b,
                inner, x);
            assert(candidate.valid());
            assert(context.integrate_elementary(b * context.exponential(inner), x).status ==
                risch_status::elementary);
        }
    }
    assert(integration_parametric_rde_gauged(context, {numeric_value(1)},
        {numeric_value(0), numeric_value(2)}, {}, x, rational_basis,
        risch_options()) == status::solved);
    assert(rational_basis.empty());
    for(int residue : {3, -4}){
        assert(integration_parametric_rde_rational({numeric_value(residue)}, {},
            rational_basis, 65536, {numeric_value(-2), numeric_value(1)}) == status::solved);
        assert(rational_basis.size() == 1);
        if(residue > 0) assert(rational_basis[0].denominator.size() == 4);
        else assert(rational_basis[0].numerator.size() == 5);
    }
    for(int sign : {-1, 1}){
        exact_expr a = context.integer(sign) / (context.integer(2) * (x - context.integer(2)));
        exact_expr y = context.power(x, context.integer(3)) / (x + context.integer(1));
        exact_expr b = context.differentiate(y, x) + a * y;
        integration_poly an, ad, bn, bd, yn, yd;
        assert(integration_parse_rational(a, x, an, ad));
        assert(integration_parse_rational(b, x, bn, bd));
        assert(integration_parse_rational(y, x, yn, yd));
        assert(integration_parametric_rde_rational(an, {{bn, bd}}, rational_basis,
            65536, ad) == status::solved);
        assert(rational_basis.size() == 1);
        integration_poly lhs = integration_mul(rational_basis[0].numerator, yd);
        integration_poly rhs = integration_mul(yn, rational_basis[0].denominator);
        for(auto &v : rhs) v = v * rational_basis[0].constants[0];
        assert(lhs == rhs);
    }
    for(const auto &a : {
            context.integer(3) / x + context.integer(1) /
                (context.integer(2) * (x - context.integer(1))),
            -context.integer(1) / (context.integer(2) * x) -
                context.integer(1) / (context.integer(2) * (x - context.integer(1)))}){
        exact_expr y = (context.power(x, context.integer(2)) + context.integer(1)) /
            context.power(x, context.integer(3));
        exact_expr b = context.differentiate(y, x) + a * y;
        integration_poly an, ad, bn, bd, yn, yd;
        assert(integration_parse_rational(a, x, an, ad));
        assert(integration_parse_rational(b, x, bn, bd));
        assert(integration_parse_rational(y, x, yn, yd));
        assert(integration_parametric_rde_gauged(context, an, ad, {{bn, bd}}, x,
            rational_basis, risch_options()) == status::solved);
        assert(rational_basis.size() == 1);
        integration_poly lhs = integration_mul(rational_basis[0].numerator, yd);
        integration_poly rhs = integration_mul(yn, rational_basis[0].denominator);
        for(auto &v : rhs) v = v * rational_basis[0].constants[0];
        assert(lhs == rhs);
    }
    exact_expr multi_a = context.integer(3) / x -
        context.integer(4) / (x - context.integer(1));
    integration_poly multi_an, multi_ad;
    assert(integration_parse_rational(multi_a, x, multi_an, multi_ad));
    assert(integration_parametric_rde_gauged(context, multi_an, multi_ad, {}, x,
        rational_basis, risch_options()) == status::solved);
    assert(rational_basis.size() == 1 && rational_basis[0].numerator.size() == 5 &&
        rational_basis[0].denominator.size() == 4);
    assert(integration_parametric_rde_gauged(context, {numeric_value(1)},
        {numeric_value(0), numeric_value(0), numeric_value(1)}, {}, x,
        rational_basis, risch_options()) == status::solved);
    assert(rational_basis.empty());
    for(const auto &a : {
            context.integer(1) / context.power(x, context.integer(2)),
            context.integer(2) / context.power(x, context.integer(3)),
            context.integer(3) / (x - context.integer(1)) +
                context.integer(1) / context.power(x + context.integer(1), context.integer(2))}){
        for(const auto &y : {context.power(x, context.integer(3)),
                (x + context.integer(2)) / context.power(x, context.integer(3))}){
            exact_expr b = context.differentiate(y, x) + a * y;
            integration_poly an, ad, bn, bd, yn, yd;
            assert(integration_parse_rational(a, x, an, ad));
            assert(integration_parse_rational(b, x, bn, bd));
            assert(integration_parse_rational(y, x, yn, yd));
            assert(integration_parametric_rde_gauged(context, an, ad, {{bn, bd}}, x,
                rational_basis, risch_options()) == status::solved);
            assert(rational_basis.size() == 1);
            integration_poly lhs = integration_mul(rational_basis[0].numerator, yd);
            integration_poly rhs = integration_mul(yn, rational_basis[0].denominator);
            for(auto &v : rhs) v = v * rational_basis[0].constants[0];
            assert(lhs == rhs);
        }
    }
    exact_expr high_inner = -context.integer(1) / x;
    exact_expr quadratic = context.power(x, context.integer(2)) + context.integer(1);
    for(int k : {-4, -1, 1, 3}){
        exact_expr a = context.integer(k) * context.differentiate(quadratic, x) / quadratic;
        integration_poly an, ad;
        assert(integration_parse_rational(a, x, an, ad));
        assert(integration_parametric_rde_rational(an, {}, rational_basis,
            65536, ad) == status::solved);
        assert(rational_basis.size() == 1);
        exact_expr expected = context.power(quadratic, context.integer(-k));
        integration_poly en, ed;
        assert(integration_parse_rational(expected, x, en, ed));
        assert(integration_mul(rational_basis[0].numerator, ed) ==
            integration_mul(en, rational_basis[0].denominator));
    }
    for(int k : {-1, 1}){
        exact_expr a = context.integer(k) * context.differentiate(quadratic, x) /
            (context.integer(2) * quadratic);
        exact_expr y = (x + context.integer(2)) / quadratic;
        exact_expr b = context.differentiate(y, x) + a * y;
        integration_poly an, ad, bn, bd, yn, yd;
        assert(integration_parse_rational(a, x, an, ad));
        assert(integration_parse_rational(b, x, bn, bd));
        assert(integration_parse_rational(y, x, yn, yd));
        assert(integration_parametric_rde_rational(an, {{bn, bd}}, rational_basis,
            65536, ad) == status::solved);
        assert(rational_basis.size() == 1);
        integration_poly rhs = integration_mul(yn, rational_basis[0].denominator);
        for(auto &v : rhs) v = v * rational_basis[0].constants[0];
        assert(integration_mul(rational_basis[0].numerator, yd) == rhs);
        assert(integration_parametric_rde_rational(an, {}, rational_basis,
            65536, ad) == status::solved);
        assert(rational_basis.empty());
    }
    for(const auto &a : {
            context.integer(1) / context.power(quadratic, context.integer(2)),
            context.integer(1) / (context.power(quadratic, context.integer(3)) *
                context.power(x, context.integer(2))),
            context.integer(3) / (x - context.integer(1)) +
                context.integer(1) / context.power(quadratic, context.integer(2))}){
        exact_expr y = (context.power(x, context.integer(3)) + context.integer(2)) /
            context.power(quadratic, context.integer(2));
        exact_expr b = context.differentiate(y, x) + a * y;
        integration_poly an, ad, bn, bd, yn, yd;
        assert(integration_parse_rational(a, x, an, ad));
        assert(integration_parse_rational(b, x, bn, bd));
        assert(integration_parse_rational(y, x, yn, yd));
        assert(integration_parametric_rde_gauged(context, an, ad, {{bn, bd}}, x,
            rational_basis, risch_options()) == status::solved);
        assert(rational_basis.size() == 1);
        integration_poly lhs = integration_mul(rational_basis[0].numerator, yd);
        integration_poly rhs = integration_mul(yn, rational_basis[0].denominator);
        for(auto &v : rhs) v = v * rational_basis[0].constants[0];
        assert(lhs == rhs);
        assert(integration_parametric_rde_gauged(context, an, ad, {}, x,
            rational_basis, risch_options()) == status::solved);
        assert(rational_basis.empty());
    }
    assert(integration_parametric_rde_rational({numeric_value(1)}, {}, rational_basis,
        65536, {numeric_value(1), numeric_value(0), numeric_value(1)}) == status::solved);
    assert(rational_basis.empty());
    std::vector<std::pair<integration_poly, int64_t>> resonances;
    assert(integration_integer_residue_factors(
        {numeric_value(0), numeric_value(-1), numeric_value(1)},
        {numeric_value(-3), numeric_value(5)},
        {numeric_value(-1), numeric_value(2)}, resonances, 65536) == status::solved);
    assert(resonances.size() == 2);
    assert(resonances[0].second == 2 && resonances[1].second == 3);
    assert(resonances[0].first == integration_poly({numeric_value(-1), numeric_value(1)}));
    assert(resonances[1].first == integration_poly({numeric_value(0), numeric_value(1)}));
    assert(integration_parametric_rde_rational({numeric_value(-3), numeric_value(5)}, {},
        rational_basis, 65536, {numeric_value(0), numeric_value(-1), numeric_value(1)}) ==
        status::solved);
    assert(rational_basis.size() == 1 && rational_basis[0].denominator.size() == 6);
    resonances.clear();
    assert(integration_integer_residue_factors(
        {numeric_value(1), numeric_value(0), numeric_value(1)},
        {numeric_value(1)}, {numeric_value(0), numeric_value(2)}, resonances, 4) ==
        status::resource_limit);
    assert(resonances.empty());
    exact_expr algebraic_a = context.integer(1) / quadratic;
    exact_expr algebraic_y = x / context.power(quadratic, context.integer(2));
    integration_poly algebraic_an, algebraic_ad, algebraic_bn, algebraic_bd;
    assert(integration_parse_rational(algebraic_a, x, algebraic_an, algebraic_ad));
    assert(integration_parse_rational(context.differentiate(algebraic_y, x) +
        algebraic_a * algebraic_y, x, algebraic_bn, algebraic_bd));
    assert(integration_parametric_rde_rational(algebraic_an,
        {{algebraic_bn, algebraic_bd}}, rational_basis, 65536, algebraic_ad) == status::solved);
    assert(rational_basis.size() == 1 && !rational_basis[0].constants[0].is_zero());
    exact_expr quadratic_inner = context.integer(1) / quadratic;
    exact_expr quadratic_y = x / quadratic;
    exact_expr quadratic_b = context.differentiate(quadratic_y, x) +
        context.differentiate(quadratic_inner, x) * quadratic_y;
    assert(context.integrate_elementary(quadratic_b *
        context.exponential(quadratic_inner), x).status == risch_status::elementary);
    for(const auto &inner : {context.integer(1) / x, quadratic_inner}){
        assert(context.integrate_elementary(context.exponential(inner), x).status ==
            risch_status::proven_nonelementary);
        exact_expr integrable = context.differentiate(inner, x) * context.exponential(inner);
        assert(context.integrate_elementary(integrable, x).status == risch_status::elementary);
        risch_options tiny_rde;
        tiny_rde.maximum_matrix_entries = 1;
        assert(context.integrate_elementary(context.exponential(inner), x, tiny_rde).status ==
            risch_status::resource_limit);
        exact_expr positive = context.exponential(inner);
        exact_expr negative = context.exponential(-context.integer(2) * inner);
        exact_expr laurent_input = context.differentiate(inner, x) *
            (positive + negative);
        auto laurent_result = context.integrate_elementary(laurent_input, x);
        assert(laurent_result.status == risch_status::elementary);
        assert(laurent_result.remainder == context.integer(0));
        exact_expr expected = positive - negative / context.integer(2);
        exact_expr error = context.simplify(context.expand(
            context.differentiate(laurent_result.elementary_part - expected, x), 100000));
        error = context.simplify(context.substitute(error, negative,
            context.power(positive, context.integer(-2))));
        error = context.simplify(context.substitute(error, context.exponential(-inner),
            context.power(positive, context.integer(-1))));
        if(error != context.integer(0)){
            fprintf(stderr, "Laurent primitive: %s\nexpected: %s\nerror: %s\n",
                laurent_result.elementary_part.to_string().c_str(),
                expected.to_string().c_str(), error.to_string().c_str());
        }
        assert(error == context.integer(0));
    }
    exact_expr rational_exp = context.exponential(context.integer(1) / x);
    exact_expr twice_rational_exp = context.exponential(context.integer(2) / x);
    exact_expr mixed_laurent = (rational_exp + context.power(x, context.integer(2)) *
        twice_rational_exp) / context.power(x, context.integer(2));
    auto mixed_result = context.integrate_elementary(mixed_laurent, x);
    if(mixed_result.status != risch_status::proven_nonelementary)
        fprintf(stderr, "Mixed Laurent status %d: %s; input %s\n",
            (int)mixed_result.status, mixed_result.diagnostic.c_str(),
            mixed_laurent.to_string().c_str());
    assert(mixed_result.status == risch_status::proven_nonelementary);
    assert(mixed_result.elementary_part != context.integer(0));
    assert(mixed_result.remainder != context.integer(0));
    for(const auto &g : {context.integer(1) / x, quadratic_inner}){
        exact_expr first = context.exponential(g / context.integer(2));
        exact_expr second = context.exponential(-g / context.integer(3));
        exact_expr input = context.differentiate(g, x) * (first + second);
        auto fractional = context.integrate_elementary(input, x);
        assert(fractional.status == risch_status::elementary);
        assert(fractional.remainder == context.integer(0));
        // Compare in one exponential generator using exact integer powers.
        exact_expr base = context.exponential(g / context.integer(6));
        exact_expr error = context.differentiate(fractional.elementary_part, x) - input;
        error = context.substitute(error, first, context.power(base, context.integer(3)));
        error = context.substitute(error, second, context.power(base, context.integer(-2)));
        error = context.substitute(error, context.exponential(-g / context.integer(6)),
            context.power(base, context.integer(-1)));
        error = context.simplify(context.expand(error, 100000));
        assert(error == context.integer(0));
    }
    for(const auto &g : {context.power(x, context.integer(2)),
            context.integer(1) / x, quadratic_inner}){
        exact_expr t = context.exponential(g);
        exact_expr dt = context.differentiate(g, x) * t;
        for(const auto &input : {
                dt / (context.integer(1) + t),
                dt / context.power(context.integer(1) + t, context.integer(2)),
                dt / (context.integer(1) + context.power(t, context.integer(2)))}){
            auto substituted = context.integrate_elementary(input, x);
            if(substituted.status != risch_status::elementary)
                fprintf(stderr, "Exponential substitution status %d: %s; input %s\n",
                    (int)substituted.status, substituted.diagnostic.c_str(),
                    input.to_string().c_str());
            assert(substituted.status == risch_status::elementary);
            assert(substituted.remainder == context.integer(0));
            exact_expr error = context.simplify(context.expand(
                context.differentiate(substituted.elementary_part, x) - input, 100000));
            assert(error == context.integer(0));
        }
    }
    // The -7/x term cancels D(x^7), leaving an RHS of degree five.
    assert(integration_parametric_rde_gauged(context,
        {numeric_value(1), numeric_value(-7)},
        {numeric_value(0), numeric_value(0), numeric_value(1)},
        {{{numeric_value(0), numeric_value(0), numeric_value(0), numeric_value(0),
           numeric_value(0), numeric_value(1)}, {numeric_value(1)}}}, x,
        rational_basis, risch_options()) == status::solved);
    assert(rational_basis.size() == 1 && rational_basis[0].numerator.size() == 8);
    assert(rational_basis[0].numerator.back() == rational_basis[0].constants[0]);
    for(size_t i = 0; i < 7; ++i)
        assert(rational_basis[0].numerator[i] == numeric_value(0));
    exact_expr high_y = (x + context.integer(2)) / context.power(x, context.integer(3));
    exact_expr high_b = context.differentiate(high_y, x) +
        context.differentiate(high_inner, x) * high_y;
    assert(integration_hyperexponential_rational(context, high_b, high_inner, x).valid());
    assert(context.integrate_elementary(high_b * context.exponential(high_inner), x).status ==
        risch_status::elementary);
    assert(integration_parametric_rde_rational({numeric_value(1)}, {}, rational_basis,
        65536, {numeric_value(0), numeric_value(0), numeric_value(1)},
        {{numeric_value(0), numeric_value(1)}}) == status::unsupported);
    risch_options gauge_budget;
    gauge_budget.maximum_degree = 0;
    assert(integration_parametric_rde_gauged(context, {numeric_value(1)},
        {numeric_value(0), numeric_value(1)}, {}, x, rational_basis,
        gauge_budget) == status::resource_limit);
    assert(rational_basis.empty());
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
    for(const auto &denominator : {x + context.integer(2),
            context.power(x, context.integer(2)) + context.integer(2)}){
        exact_expr t = context.natural_logarithm(x / (x + context.integer(1)));
        for(int multiplicity : {1, 2, 3}){
            exact_expr original = context.power(x + t, context.integer(3)) /
                context.power(denominator, context.integer(multiplicity));
            exact_expr f = context.simplify(context.expand(
                context.differentiate(original, x), 100000));
            integration_expr_poly input;
            assert(integration_parse_expr_poly(context, f, t, input));
            exact_expr candidate = integration_joint_primitive_polynomial(
                context, input, t, x, risch_options());
            assert(candidate.valid());
            integration_expr_poly difference;
            assert(integration_parse_expr_poly(context, context.expand(
                candidate - original, 100000), t, difference));
            for(size_t i = 0; i < difference.size(); ++i){
                integration_poly n, d;
                assert(integration_parse_rational(difference[i], x, n, d));
                assert(integration_normalize_rational(n, d));
                if(i) assert(integration_zero_poly(n));
                else assert(integration_zero_poly(integration_sub(
                    integration_mul(integration_derivative_poly(n), d),
                    integration_mul(n, integration_derivative_poly(d)))));
            }
            assert(context.integrate_elementary(f, x).status == risch_status::elementary);
        }
    }
    exact_expr lower_log = context.natural_logarithm(x);
    exact_expr shifted_log = context.natural_logarithm(x + context.integer(1));
    exact_expr second_shifted_log = context.natural_logarithm(x + context.integer(2));
    for(const auto &original : {
            context.power(x + lower_log + shifted_log, context.integer(2)) /
                (x + context.integer(2)),
            x * (lower_log + context.integer(1)) * (shifted_log + context.integer(1)) *
                (second_shifted_log + context.integer(1))}){
        exact_expr f = context.simplify(context.expand(context.differentiate(original, x), 100000));
        exact_expr candidate = integration_joint_primitives(context, f, x, risch_options());
        assert(candidate.valid());
        assert(context.integrate_elementary(f, x).status == risch_status::elementary);
        exact_expr error = context.simplify(context.expand(
            context.differentiate(candidate - original, x), 100000));
        std::vector<exact_expr> logs{lower_log, shifted_log, second_shifted_log};
        auto verify_coefficients = [&](auto &&self, const exact_expr &part, size_t axis) -> bool{
            if(axis == logs.size()){
                integration_poly n, d;
                return integration_parse_rational(part, x, n, d) &&
                    integration_normalize_rational(n, d) && integration_zero_poly(n);
            }
            integration_expr_poly coefficients;
            if(!integration_parse_expr_poly(context, part, logs[axis], coefficients)) return false;
            for(const auto &coefficient : coefficients)
                if(!self(self, coefficient, axis + 1)) return false;
            return true;
        };
        assert(verify_coefficients(verify_coefficients, error, 0));
        exact_expr ordinary = context.integrate(f, x);
        assert(ordinary.operation() != exact_opcode::integral);
        exact_expr ordinary_error = context.simplify(context.expand(
            context.differentiate(ordinary - original, x), 100000));
        assert(verify_coefficients(verify_coefficients, ordinary_error, 0));
        risch_options small_grid;
        small_grid.maximum_matrix_entries = 1;
        assert(!integration_joint_primitives(context, f, x, small_grid).valid());
    }
    exact_expr multilog_y = context.power(x + lower_log + shifted_log, context.integer(2)) /
        (x + context.integer(2));
    exact_expr multilog_b = context.simplify(context.expand(
        context.differentiate(multilog_y, x) + multilog_y, 100000));
    assert(integration_mixed_primitive_exponential(context,
        multilog_b * context.exponential(x), x, risch_options()).valid());
    assert(context.integrate_elementary(multilog_b * context.exponential(x), x).status ==
        risch_status::elementary);
    for(const auto &g : {x, context.power(x, context.integer(2)), context.integer(1) / x}){
        for(const auto &h : {x, x / (x + context.integer(1))}){
            exact_expr t = context.natural_logarithm(h);
            exact_expr y = context.power(x + t, context.integer(3)) /
                context.power(x + context.integer(2), context.integer(2));
            exact_expr b = context.simplify(context.expand(context.differentiate(y, x) +
                context.differentiate(g, x) * y, 100000));
            exact_expr candidate = integration_mixed_primitive_exponential(context,
                b * context.exponential(g), x, risch_options());
            assert(candidate.valid());
            auto mixed = context.integrate_elementary(b * context.exponential(g), x);
            assert(mixed.status == risch_status::elementary);
            exact_expr ordinary = context.integrate(b * context.exponential(g), x);
            assert(ordinary.operation() != exact_opcode::integral);
            risch_options tiny_mixed;
            tiny_mixed.maximum_matrix_entries = 1;
            assert(!integration_mixed_primitive_exponential(context,
                b * context.exponential(g), x, tiny_mixed).valid());
            integration_expr_poly errors;
            exact_expr error = context.simplify(context.expand(
                context.differentiate(candidate / context.exponential(g) - y, x), 100000));
            assert(integration_parse_expr_poly(context, error, t, errors));
            for(const auto &coefficient : errors){
                integration_poly n, d;
                assert(integration_parse_rational(coefficient, x, n, d));
                assert(integration_normalize_rational(n, d));
                assert(integration_zero_poly(n));
            }
            exact_expr ordinary_y = ordinary / context.exponential(g);
            exact_expr ordinary_error = context.simplify(context.expand(
                context.differentiate(ordinary_y, x) +
                context.differentiate(g, x) * ordinary_y - b, 100000));
            assert(integration_parse_expr_poly(context, ordinary_error, t, errors));
            for(const auto &coefficient : errors){
                integration_poly n, d;
                assert(integration_parse_rational(coefficient, x, n, d));
                assert(integration_normalize_rational(n, d));
                assert(integration_zero_poly(n));
            }
        }
    }
    exact_expr nested_log = context.natural_logarithm(lower_log);
    for(const auto &original : {
            context.power(lower_log + nested_log, context.integer(2)),
            context.power(lower_log + nested_log, context.integer(3)) /
                (lower_log + context.integer(2)),
            context.power(nested_log, context.integer(2)) * lower_log}){
        exact_expr f = context.differentiate(original, x);
        auto nested = context.integrate_elementary(f, x);
        if(nested.status != risch_status::elementary)
            fprintf(stderr, "Nested primitive status %d: %s; input %s\n",
                (int)nested.status, nested.diagnostic.c_str(), f.to_string().c_str());
        assert(nested.status == risch_status::elementary);
        assert(nested.remainder == context.integer(0));
        exact_expr error = context.simplify(context.expand(
            context.differentiate(nested.elementary_part - original, x), 100000));
        assert(error == context.integer(0));
    }
    risch_options no_recursion;
    no_recursion.maximum_recursion_depth = 0;
    assert(context.integrate_elementary(x, x, no_recursion).status == risch_status::resource_limit);
    assert(context.integrate_elementary(x, x).status == risch_status::elementary);
    puts("parametric RDE and coupled primitive ok");
}
