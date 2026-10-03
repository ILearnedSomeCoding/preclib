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
            auto checked = context.integrate_elementary(f, x);
            if(checked.status != risch_status::elementary)
                fprintf(stderr, "primitive regression status %d: %s\ninput: %s\n",
                    (int)checked.status, checked.diagnostic.c_str(), f.to_string().c_str());
            assert(checked.status == risch_status::elementary);
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
            auto checked = context.integrate_elementary(f, x);
            if(checked.status != risch_status::elementary){
                auto parametric = integration_parametric_primitive_polynomial(
                    context, input, t, x, risch_options(), context.integer(0));
                fprintf(stderr, "rational primitive regression status %d: %s\ninput: %s\nparametric: %s\n",
                    (int)checked.status, checked.diagnostic.c_str(), f.to_string().c_str(),
                    parametric.valid() ? parametric.to_string().c_str() : "invalid");
            }
            assert(checked.status == risch_status::elementary);
        }
    }
    exact_expr lower_log = context.natural_logarithm(x);
    {
        integration_expr_poly normalized;
        exact_expr scale,r = x*x*(x+context.integer(1));
        assert(integration_binomial_normalize_generator(context,
            {-r,context.integer(0),context.integer(1)},x,risch_options(),normalized,scale) == status::solved);
        exact_expr error = scale-x;
        assert(integration_normalize_expr_coefficient(context,error,x,64));
        assert(error == context.integer(0));
        error = normalized[0]+x+context.integer(1);
        assert(integration_normalize_expr_coefficient(context,error,x,64));
        assert(error == context.integer(0));
        assert(integration_binomial_irreducible_certificate(normalized,x,64));
        assert(integration_binomial_normalize_generator(context,
            {-context.integer(1)/x,context.integer(0),context.integer(1)},x,risch_options(),normalized,scale) == status::solved);
        error = scale-context.integer(1)/x;
        assert(integration_normalize_expr_coefficient(context,error,x,64));
        assert(error == context.integer(0));
        assert(normalized[0] == -x);
        assert(integration_binomial_irreducible_certificate(normalized,x,64));
        assert(integration_binomial_irreducible_certificate(
            {-x,context.integer(0),context.integer(0),context.integer(0),context.integer(1)},x,64));
        integration_expr_poly sixth(7,context.integer(0));
        sixth[0] = -x*x*(x+context.integer(1))*(x+context.integer(1))*(x+context.integer(1));
        sixth[6] = context.integer(1);
        assert(integration_binomial_irreducible_certificate(sixth,x,64));
        assert(integration_binomial_irreducible_certificate(
            {-context.integer(2)*x*x,context.integer(0),context.integer(0),
             context.integer(0),context.integer(1)},x,64));
        assert(!integration_binomial_irreducible_certificate(
            {-x*x,context.integer(0),context.integer(0),context.integer(0),context.integer(1)},x,64));
        assert(!integration_binomial_irreducible_certificate(
            {-context.integer(9)*x*x/context.integer(4),context.integer(0),
             context.integer(0),context.integer(0),context.integer(1)},x,64));
        assert(integration_binomial_irreducible_certificate(
            {context.integer(9)*x*x/context.integer(4),context.integer(0),
             context.integer(0),context.integer(0),context.integer(1)},x,64));
        assert(!integration_binomial_irreducible_certificate(
            {context.integer(8)*context.power(x,context.integer(3)),context.integer(0),
             context.integer(0),context.integer(1)},x,64));
        assert(!integration_binomial_irreducible_certificate(
            {context.integer(4)*context.power(x,context.integer(4)),context.integer(0),
             context.integer(0),context.integer(0),context.integer(1)},x,64));
        assert(!integration_binomial_irreducible_certificate(
            {-context.integer(1),context.integer(0),context.integer(1)},x,64));
        bool square = false;
        assert(integration_rational_square_status(x*x/(x+context.integer(1)),x,64,square) && !square);
        assert(integration_rational_square_status(context.integer(9)*x*x/
            (context.integer(4)*(x+context.integer(1))*(x+context.integer(1))),x,64,square) && square);
        assert(integration_rational_square_status(-x*x,x,64,square) && !square);
        exact_expr root = context.square_root(r);
        auto solved = context.integrate_elementary(root/(context.integer(2)*x*(x+context.integer(1))),x);
        assert(solved.status == risch_status::elementary && solved.remainder == context.integer(0));
        integration_expr_poly difference;
        assert(integration_parse_algebraic_quotient(context,solved.elementary_part-root/x,
            root,{-r,context.integer(0),context.integer(1)},x,risch_options(),difference));
        for(const auto &v : difference) assert(v == context.integer(0));
    }
    {
        exact_expr u = context.square_root(x);
        exact_expr v = context.square_root(x+context.integer(1));
        exact_expr t = context.symbol("_risch_test_biquadratic_t");
        integration_expr_poly modulus;
        exact_expr formal_u,formal_v;
        assert(integration_biquadratic_field(context,x,x+context.integer(1),t,x,
            risch_options(),modulus,formal_u,formal_v));
        assert(!integration_biquadratic_field(context,x,x*x,t,x,
            risch_options(),modulus,formal_u,formal_v));
        assert(!integration_biquadratic_field(context,x,context.integer(1)/x,t,x,
            risch_options(),modulus,formal_u,formal_v));
        exact_expr target = context.integer(1)/(u+v);
        exact_expr integrand = -(context.integer(1)/(context.integer(2)*u)+
            context.integer(1)/(context.integer(2)*v))/((u+v)*(u+v));
        auto solved = context.integrate_elementary(integrand,x);
        assert(solved.status == risch_status::elementary);
        assert(solved.remainder == context.integer(0));
        integration_expr_poly difference;
        assert(integration_biquadratic_field(context,x,x+context.integer(1),t,x,
            risch_options(),modulus,formal_u,formal_v));
        exact_expr error = context.substitute(context.substitute(
            solved.elementary_part-target,u,formal_u),v,formal_v);
        assert(integration_parse_algebraic_quotient(context,error,t,modulus,x,
            risch_options(),difference));
        assert(difference.size() == 1 && difference[0] == context.integer(0));
    }
    {
        integration_expr_poly modulus{-x,context.integer(0),context.integer(1)},exact,residual;
        assert(integration_algebraic_infinity_reduce(context,{context.integer(0),context.integer(1)},
            modulus,x,risch_options(),exact,residual) == status::solved);
        exact_expr error = exact[1]-context.integer(2)*x/context.integer(3);
        assert(integration_normalize_expr_coefficient(context,error,x,64));
        assert(error == context.integer(0));
        for(const auto &v : residual) assert(v == context.integer(0));
        modulus[0] = -x*x*x+x;
        assert(integration_algebraic_infinity_reduce(context,{context.integer(0),context.integer(1)},
            modulus,x,risch_options(),exact,residual) == status::solved);
        error = exact[1]-context.integer(2)*x/context.integer(5);
        assert(integration_normalize_expr_coefficient(context,error,x,64));
        assert(error == context.integer(0));
        error = residual[1]+context.integer(2)/(context.integer(5)*(x*x-context.integer(1)));
        assert(integration_normalize_expr_coefficient(context,error,x,64));
        assert(error == context.integer(0));
        risch_options tiny; tiny.maximum_matrix_entries = 1;
        assert(integration_algebraic_infinity_reduce(context,{context.integer(0),context.integer(1)},
            modulus,x,tiny,exact,residual) == status::resource_limit);
    }
    {
        integration_residue_algebra algebra{{numeric_value(0),numeric_value(-1),numeric_value(1)}};
        std::vector<std::vector<integration_poly>> matrix{
            {{numeric_value(0),numeric_value(1)},{numeric_value(1),numeric_value(-1)},{numeric_value(3),numeric_value(-1)}},
            {{numeric_value(1),numeric_value(-1)},{numeric_value(0),numeric_value(1)},{numeric_value(2),numeric_value(1)}}};
        std::vector<integration_poly> solution;
        assert(integration_residue_linear_solve(algebra,matrix,65536,solution) == status::solved);
        assert(solution == std::vector<integration_poly>({{numeric_value(2)},{numeric_value(3)}}));
        assert(integration_residue_linear_solve(algebra,matrix,5,solution) == status::resource_limit);
        matrix[1] = matrix[0];
        assert(integration_residue_linear_solve(algebra,matrix,65536,solution) == status::unsupported);
        algebra.modulus = {numeric_value(0),numeric_value(2),numeric_value(-3),numeric_value(1)};
        numeric_value half = numeric_value(1)/numeric_value(2);
        integration_poly e0{numeric_value(1),-numeric_value(3)*half,half};
        integration_poly e1{numeric_value(0),numeric_value(2),numeric_value(-1)};
        integration_poly e2{numeric_value(0),-half,half};
        matrix = {{e0,e1,e2},{e2,e0,e1},{e1,e2,e0}};
        for(auto &row : matrix){
            integration_poly rhs{numeric_value(0)};
            for(size_t column = 0; column < 3; ++column)
                rhs = algebra.reduce(integration_add(rhs,algebra.multiply(row[column],{numeric_value(column+2)})));
            row.push_back(rhs);
        }
        assert(integration_residue_linear_solve(algebra,matrix,65536,solution) == status::solved);
        assert(solution == std::vector<integration_poly>({{numeric_value(2)},{numeric_value(3)},{numeric_value(4)}}));
        algebra.modulus = {numeric_value(0),numeric_value(-1),numeric_value(1)};
        matrix = {{{numeric_value(0),numeric_value(1)},{numeric_value(0)},{numeric_value(0)}},
                  {{numeric_value(0)},{numeric_value(1)},{numeric_value(0)}}};
        integration_poly obstruction;
        assert(integration_residue_linear_solve(algebra,matrix,65536,solution,&obstruction) == status::unsupported);
        assert(obstruction == integration_poly({numeric_value(0),numeric_value(1)}));
    }
    {
        exact_expr r = x*x*x-x;
        integration_expr_poly modulus{-r,context.integer(0),context.integer(1)},exact,residual;
        exact_expr coefficient = context.differentiate(r,x)/(context.integer(2)*r*x) -
            context.integer(1)/(x*x)+context.integer(1)/r;
        assert(integration_algebraic_finite_reduce(context,{context.integer(0),coefficient},
            modulus,x,risch_options(),exact,residual) == status::solved);
        exact_expr error = exact[1]-context.integer(1)/x;
        assert(integration_normalize_expr_coefficient(context,error,x,64));
        assert(error == context.integer(0));
        error = residual[1]-context.integer(1)/r;
        assert(integration_normalize_expr_coefficient(context,error,x,64));
        assert(error == context.integer(0));
        modulus[0] = -x*x;
        assert(integration_algebraic_finite_reduce(context,
            {context.integer(0),context.integer(1)/(x*x)},modulus,x,risch_options(),exact,residual) == status::solved);
        for(const auto &v : exact) assert(v == context.integer(0));
        error = residual[1]-context.integer(1)/(x*x);
        assert(integration_normalize_expr_coefficient(context,error,x,64));
        assert(error == context.integer(0));
        modulus = integration_expr_poly(5,context.integer(0));
        modulus[0] = -x*x*(x-context.integer(2));
        modulus[4] = context.integer(1);
        exact_expr poles = x*x*(x-context.integer(1))*(x-context.integer(1));
        assert(integration_algebraic_finite_reduce(context,
            {context.integer(0),context.integer(0),context.integer(1)/poles},
            modulus,x,risch_options(),exact,residual) == status::solved);
        assert(exact.size() > 2 && exact[2] != context.integer(0));
        integration_poly n,d;
        assert(integration_parse_rational(residual[2]*(x-context.integer(1)),x,n,d,64,64));
        assert(integration_normalize_rational(n,d));
        assert(integration_gcd_poly(d,{numeric_value(-1),numeric_value(1)}).size() == 1);
    }
    {
        integration_expr_poly modulus{-x,context.integer(1),context.integer(1)},exact,residual;
        exact_expr p = context.integer(4)*x+context.integer(1);
        assert(integration_algebraic_regular_singular_pole_step(context,
            {context.integer(0),context.integer(1)/(p*p)},modulus,
            {numeric_value(1),numeric_value(4)},2,x,risch_options(),exact,residual) == status::solved);
        exact_expr error = exact[0]+context.integer(1)/(context.integer(8)*p);
        assert(integration_normalize_expr_coefficient(context,error,x,64));
        assert(error == context.integer(0));
        error = exact[1]+context.integer(1)/(context.integer(2)*p);
        assert(integration_normalize_expr_coefficient(context,error,x,64));
        assert(error == context.integer(0));
        integration_expr_poly radical{-x,context.integer(0),context.integer(1)};
        assert(integration_algebraic_regular_singular_pole_step(context,
            {context.integer(0),context.integer(1)/(x*x)},radical,
            {numeric_value(0),numeric_value(1)},2,x,risch_options(),exact,residual) == status::solved);
        error = exact[1]+context.integer(2)/x;
        assert(integration_normalize_expr_coefficient(context,error,x,64));
        assert(error == context.integer(0));
        for(const auto &v : residual) assert(v == context.integer(0));
        radical[0] = -x*x;
        assert(integration_algebraic_regular_singular_pole_step(context,
            {context.integer(0),context.integer(1)/(x*x)},radical,
            {numeric_value(0),numeric_value(1)},2,x,risch_options(),exact,residual) == status::unsupported);
    }
    {
        integration_expr_poly modulus{-x,context.integer(1),context.integer(1)},exact,residual;
        exact_expr coefficient = context.integer(1)/context.power(x-context.integer(2),context.integer(3)) +
            context.integer(1)/context.power(x-context.integer(3),context.integer(2));
        assert(integration_algebraic_finite_reduce(context,{context.integer(0),coefficient},
            modulus,x,risch_options(),exact,residual) == status::solved);
        assert(exact[1] != context.integer(0));
        integration_expr_poly scalar_exact,scalar_rest;
        assert(integration_algebraic_finite_reduce(context,{coefficient},modulus,x,
            risch_options(),scalar_exact,scalar_rest) == status::solved);
        assert(scalar_exact.size() == 2 && scalar_exact[1] == context.integer(0));
        integration_poly normal_poles{numeric_value(6),numeric_value(-5),numeric_value(1)};
        for(const auto &v : residual){
            integration_poly n,d;
            assert(integration_parse_rational(v,x,n,d));
            assert(integration_normalize_rational(n,d));
            assert(integration_gcd_poly(normal_poles,
                integration_gcd_poly(d,integration_derivative_poly(d))).size() == 1);
        }
        exact_expr r = x*x*x-x,root = context.square_root(r);
        exact_expr original = root/(x+context.integer(2));
        auto solved = context.integrate_elementary(context.differentiate(original,x)+context.integer(1)/root,x);
        assert(solved.status == risch_status::unsupported);
        assert(solved.elementary_part != context.integer(0));
        assert(solved.remainder != context.integer(0));
    }
    {
        integration_expr_poly modulus{-x,context.integer(1),context.integer(1)};
        integration_expr_poly input{context.integer(0),context.integer(1)/context.power(x-context.integer(2),context.integer(3))};
        integration_expr_poly exact,residual,dz,derivative;
        assert(integration_algebraic_normal_pole_step(context,input,modulus,
            {numeric_value(-2),numeric_value(1)},3,x,risch_options(),exact,residual) == status::solved);
        exact_expr error = exact[1]+context.integer(1)/(context.integer(2)*context.power(x-context.integer(2),context.integer(2)));
        assert(integration_normalize_expr_coefficient(context,error,x,64));
        assert(error == context.integer(0));
        assert(integration_algebraic_implicit_derivation(context,modulus,x,risch_options(),dz));
        assert(integration_algebraic_quotient_derivative(context,exact,modulus,dz,x,risch_options(),derivative));
        for(size_t i = 0; i < input.size(); ++i){
            error = input[i]-derivative[i]-residual[i];
            assert(integration_normalize_expr_coefficient(context,error,x,64));
            assert(error == context.integer(0));
        }
        integration_expr_poly second,rest;
        assert(integration_algebraic_normal_pole_step(context,residual,modulus,
            {numeric_value(-2),numeric_value(1)},2,x,risch_options(),second,rest) == status::solved);
        assert(integration_algebraic_normal_pole_step(context,input,modulus,
            {numeric_value(1),numeric_value(4)},3,x,risch_options(),exact,residual) == status::unsupported);
        assert(integration_algebraic_normal_pole_step(context,input,modulus,
            {numeric_value(4),numeric_value(-4),numeric_value(1)},3,x,risch_options(),exact,residual) == status::unsupported);
        risch_options tiny; tiny.maximum_degree = 2;
        assert(integration_algebraic_normal_pole_step(context,input,modulus,
            {numeric_value(-2),numeric_value(1)},3,x,tiny,exact,residual) == status::resource_limit);
    }
    {
        integration_expr_poly modulus{-x*x*x+x, context.integer(0), context.integer(1)}, dz, first, second;
        assert(integration_algebraic_implicit_derivation(context, modulus, x, risch_options(), dz));
        std::vector<integration_expr_poly> arguments{
            {context.integer(1), context.integer(1)}, {context.integer(2), context.integer(1)}};
        assert(integration_algebraic_log_derivative(context, arguments[0], modulus, dz, x, risch_options(), first));
        assert(integration_algebraic_log_derivative(context, arguments[1], modulus, dz, x, risch_options(), second));
        for(auto &v : second) v = context.integer(2)*v;
        auto input = integration_expr_add(context, first, second);
        std::vector<numeric_value> constants;
        integration_expr_poly residual;
        assert(integration_algebraic_log_combination(context, input, arguments, modulus, dz,
            x, risch_options(), constants, residual) == status::solved);
        assert(constants.size() == 2 && constants[0] == numeric_value(1) && constants[1] == numeric_value(2));
        for(const auto &v : residual) assert(v == context.integer(0));
        arguments.push_back(arguments[0]);
        assert(integration_algebraic_log_combination(context, input, arguments, modulus, dz,
            x, risch_options(), constants, residual) == status::solved);
        risch_options tiny; tiny.maximum_matrix_entries = 1;
        assert(integration_algebraic_log_combination(context, input, arguments, modulus, dz,
            x, tiny, constants, residual) == status::resource_limit);
        exact_expr r = x*x*x-x, root = context.square_root(r);
        exact_expr f = context.differentiate(r,x)/(context.integer(2)*root)*
            (context.integer(1)/(context.integer(1)+root)+context.integer(2)/(context.integer(2)+root));
        auto solved = context.integrate_elementary(f,x);
        assert(solved.status == risch_status::elementary && solved.remainder == context.integer(0));
    }
    {
        exact_expr r = x*x*x-x, root = context.square_root(r);
        exact_expr f = context.differentiate(r, x)/(context.integer(2)*root*(context.integer(1)+root));
        auto solved = context.integrate_elementary(f, x);
        assert(solved.status == risch_status::elementary);
        assert(solved.remainder == context.integer(0));
        integration_expr_poly modulus{-r, context.integer(0), context.integer(1)}, error;
        exact_expr z = context.symbol("_test_algebraic_log_verify");
        exact_expr differential = context.differentiate(solved.elementary_part, x)-f;
        std::vector<exact_expr> roots;
        std::unordered_set<uint32_t> seen;
        auto collect = [&](auto &&self, const exact_expr &part) -> void{
            if(!seen.insert(part.id()).second) return;
            if(part.operation() == exact_opcode::square_root) roots.push_back(part);
            for(size_t i = 0; i < part.operand_count(); ++i) self(self, part.operand(i));
        };
        collect(collect, differential);
        for(const auto &part : roots){
            exact_expr relation_error = part.operand(0)-r;
            assert(integration_normalize_expr_coefficient(context, relation_error, x, 64));
            assert(relation_error == context.integer(0));
            differential = context.substitute(differential, part, z);
        }
        assert(integration_parse_algebraic_quotient(context,
            differential, z, modulus,
            x, risch_options(), error));
        for(const auto &v : error) assert(v == context.integer(0));
        integration_expr_poly dz, logarithmic, remainder;
        assert(integration_algebraic_implicit_derivation(context, modulus, x, risch_options(), dz));
        assert(integration_algebraic_log_derivative(context,
            {context.integer(1), context.integer(1)}, modulus, dz, x, risch_options(), logarithmic));
        for(auto &v : logarithmic) v = x*v;
        exact_expr constant;
        assert(!integration_algebraic_log_candidate(context, logarithmic,
            {context.integer(1), context.integer(1)}, modulus, dz, x,
            risch_options(), constant, remainder));
    }
    {
        exact_expr r = x*x*x-x;
        exact_expr square = context.square_root(r);
        exact_expr cube = context.power(r, context.value(numeric_value(1)/numeric_value(3)));
        exact_expr expected = context.integer(1)/(square+cube);
        exact_expr f = context.differentiate(expected, x);
        auto solved = context.integrate_elementary(f, x);
        assert(solved.status == risch_status::elementary);
        assert(solved.remainder == context.integer(0));
        exact_expr ordinary = context.integrate(f, x);
        std::unordered_set<uint32_t> seen;
        auto has_integral = [&](auto &&self, const exact_expr &part) -> bool{
            if(!seen.insert(part.id()).second) return false;
            if(part.operation() == exact_opcode::integral) return true;
            for(size_t i = 0; i < part.operand_count(); ++i)
                if(self(self, part.operand(i))) return true;
            return false;
        };
        assert(!has_integral(has_integral, ordinary));
    }
    {
        exact_expr r = x*x*x-x;
        for(size_t degree : {2u, 3u}){
            exact_expr root = degree == 2 ? context.square_root(r) :
                context.power(r, context.value(numeric_value(1)/numeric_value(degree)));
            exact_expr expected = root/(x+context.integer(2));
            exact_expr f = expected*(context.differentiate(r, x)/(context.integer(degree)*r) -
                context.integer(1)/(x+context.integer(2)));
            auto solved = context.integrate_elementary(f, x);
            assert(solved.status == risch_status::elementary);
            assert(solved.remainder == context.integer(0));
            integration_expr_poly modulus(degree+1, context.integer(0)), difference;
            modulus[0] = -r; modulus.back() = context.integer(1);
            assert(integration_parse_algebraic_quotient(context, solved.elementary_part-expected,
                root, modulus, x, risch_options(), difference));
            for(const auto &v : difference) assert(v == context.integer(0));
            exact_expr ordinary = context.integrate(f, x);
            assert(ordinary.operation() != exact_opcode::integral);
            exact_expr normalized_root = context.simplify(root);
            modulus[0] = -context.simplify(r);
            assert(integration_parse_algebraic_quotient(context,
                ordinary-context.simplify(expected), normalized_root, modulus,
                x, risch_options(), difference));
            for(const auto &v : difference) assert(v == context.integer(0));
        }
    }
    {
        using status = integration_parametric_rde_status;
        for(size_t degree : {2u, 3u}){
            integration_expr_poly modulus(degree+1, context.integer(0));
            modulus[0] = -(x*x*x-x); modulus.back() = context.integer(1);
            integration_expr_poly known(degree, context.integer(0)), dz, derivative, exact, residual;
            known[1] = context.integer(1)/(x+context.integer(2));
            assert(integration_algebraic_implicit_derivation(context, modulus, x, risch_options(), dz));
            assert(integration_algebraic_quotient_derivative(context, known, modulus, dz,
                x, risch_options(), derivative));
            assert(integration_binomial_exact_reduce(context, derivative, modulus,
                x, risch_options(), exact, residual) == status::solved);
            for(const auto &v : residual) assert(v == context.integer(0));
            exact_expr error = exact[1]-known[1];
            assert(integration_normalize_expr_coefficient(context, error, x, 64));
            assert(error == context.integer(0));
        }
        integration_expr_poly modulus{-x, context.integer(0), context.integer(1)}, exact, residual;
        assert(integration_binomial_exact_reduce(context, {context.integer(0), context.integer(1)/x},
            modulus, x, risch_options(), exact, residual) == status::solved);
        assert(exact[1] == context.integer(2));
        assert(residual[0] == context.integer(0) && residual[1] == context.integer(0));
        assert(integration_binomial_exact_reduce(context, {context.integer(1)/x},
            modulus, x, risch_options(), exact, residual) == status::solved);
        assert(residual[0] == context.integer(1)/x);
        modulus[1] = context.integer(1);
        assert(integration_binomial_exact_reduce(context, {context.integer(1)},
            modulus, x, risch_options(), exact, residual) == status::unsupported);
    }
    {
        using status = integration_parametric_rde_status;
        integration_expr_poly modulus{-x, context.integer(1), context.integer(1)}, dz;
        assert(integration_algebraic_implicit_derivation(context, modulus, x, risch_options(), dz));
        integration_expr_poly known{x/(x-context.integer(1)), context.integer(1)/(x-context.integer(1))};
        integration_expr_poly a{context.integer(1), context.integer(1)}, derivative, q, right, solution;
        assert(integration_algebraic_quotient_derivative(context, known, modulus, dz,
            x, risch_options(), derivative));
        assert(integration_expr_divmod_rational_coefficients(context,
            integration_expr_add(context, derivative, integration_expr_mul(context, a, known)),
            modulus, x, 64, q, right));
        std::vector<integration_expr_poly> homogeneous;
        assert(integration_algebraic_rde_ansatz(context, modulus, a, right,
            {numeric_value(-1), numeric_value(1)}, 1, x, risch_options(), solution, homogeneous) == status::solved);
        for(size_t i = 0; i < known.size(); ++i){
            exact_expr error = solution[i]-known[i];
            assert(integration_normalize_expr_coefficient(context, error, x, 64));
            assert(error == context.integer(0));
        }
        assert(homogeneous.empty());
        assert(integration_algebraic_rde_ansatz(context, modulus, {context.integer(0)},
            {context.integer(1)}, {numeric_value(1)}, 1, x, risch_options(), solution, homogeneous) == status::solved);
        assert(homogeneous.size() == 1);
        assert(integration_algebraic_rde_ansatz(context, modulus, {context.integer(0)},
            {context.integer(1)/x}, {numeric_value(1)}, 2, x, risch_options(), solution, homogeneous) == status::unsupported);
        risch_options tiny; tiny.maximum_matrix_entries = 1;
        assert(integration_algebraic_rde_ansatz(context, modulus, a, right,
            {numeric_value(1)}, 1, x, tiny, solution, homogeneous) == status::resource_limit);
    }
    {
        for(size_t degree : {2u, 3u, 4u}){
            integration_expr_poly modulus(degree + 1, context.integer(0));
            modulus[0] = -x-context.integer(1); modulus.back() = context.integer(1);
            std::vector<integration_expr_poly> matrix;
            assert(integration_algebraic_connection_matrix(context, modulus, x, risch_options(), matrix));
            integration_expr_poly input, dz, derivative;
            for(size_t i = 0; i < degree; ++i) input.push_back(context.integer(i+1)/(x+context.integer(i+2)));
            assert(integration_algebraic_implicit_derivation(context, modulus, x, risch_options(), dz));
            assert(integration_algebraic_quotient_derivative(context, input, modulus, dz,
                x, risch_options(), derivative));
            for(size_t row = 0; row < degree; ++row){
                exact_expr expected = context.differentiate(input[row], x);
                for(size_t column = 0; column < degree; ++column)
                    expected = expected + matrix[row][column]*input[column];
                exact_expr error = expected - (row < derivative.size() ? derivative[row] : context.integer(0));
                assert(integration_normalize_expr_coefficient(context, error, x, 64));
                assert(error == context.integer(0));
            }
            risch_options tiny; tiny.maximum_matrix_entries = degree*degree-1;
            assert(!integration_algebraic_connection_matrix(context, modulus, x, tiny, matrix));
            modulus.push_back(context.integer(0));
            assert(!integration_algebraic_connection_matrix(context, modulus, x, risch_options(), matrix));
        }
    }
    {
        integration_expr_poly modulus{-x, context.integer(0), context.integer(1)}, dz, value;
        assert(integration_algebraic_implicit_derivation(context, modulus, x, risch_options(), dz));
        assert(integration_algebraic_log_derivative(context,
            {context.integer(0), context.integer(1)}, modulus, dz, x, risch_options(), value));
        assert(value.size() == 1);
        exact_expr error = value[0] - context.integer(1)/(context.integer(2)*x);
        assert(integration_normalize_expr_coefficient(context, error, x, 64));
        assert(error == context.integer(0));
        assert(integration_algebraic_log_derivative(context,
            {context.integer(1), context.integer(1)}, modulus, dz, x, risch_options(), value));
        assert(value.size() == 2);
        error = value[0] - context.integer(1)/(context.integer(2)*(x-context.integer(1)));
        assert(integration_normalize_expr_coefficient(context, error, x, 64));
        assert(error == context.integer(0));
        error = value[1] - context.integer(1)/(context.integer(2)*x*(context.integer(1)-x));
        assert(integration_normalize_expr_coefficient(context, error, x, 64));
        assert(error == context.integer(0));
        integration_expr_poly reducible{-x*x, context.integer(0), context.integer(1)};
        assert(integration_algebraic_implicit_derivation(context, reducible, x, risch_options(), dz));
        assert(!integration_algebraic_log_derivative(context,
            {-x, context.integer(1)}, reducible, dz, x, risch_options(), value));
        assert(!integration_algebraic_log_derivative(context,
            {context.integer(0)}, modulus, dz, x, risch_options(), value));
    }
    {
        exact_expr z = context.symbol("_test_algebraic_trace_root");
        for(size_t degree : {2u, 3u}){
            integration_expr_poly modulus(degree + 1, context.integer(0));
            modulus[0] = -x; modulus.back() = context.integer(1);
            integration_expr_poly value, dz, derivative, remainder;
            assert(integration_parse_algebraic_quotient(context,
                context.integer(1) / (context.integer(1) + z), z, modulus,
                x, risch_options(), value));
            exact_expr trace, base, derivative_trace;
            assert(integration_algebraic_quotient_trace(context, value, modulus, x, risch_options(), trace));
            exact_expr expected = context.integer(degree) /
                (context.integer(1) + context.integer(degree == 2 ? -1 : 1)*x);
            exact_expr error = trace - expected;
            assert(integration_normalize_expr_coefficient(context, error, x, 64));
            assert(error == context.integer(0));
            assert(integration_algebraic_implicit_derivation(context, modulus, x, risch_options(), dz));
            assert(integration_algebraic_quotient_derivative(context, value, modulus, dz,
                x, risch_options(), derivative));
            assert(integration_algebraic_quotient_trace(context, derivative, modulus,
                x, risch_options(), derivative_trace));
            error = context.differentiate(trace, x) - derivative_trace;
            assert(integration_normalize_expr_coefficient(context, error, x, 64));
            assert(error == context.integer(0));
            assert(integration_algebraic_trace_split(context, value, modulus, x, risch_options(), base, remainder));
            remainder[0] = remainder[0] + base;
            for(size_t i = 0; i < value.size(); ++i){
                error = remainder[i] - value[i];
                assert(integration_normalize_expr_coefficient(context, error, x, 64));
                assert(error == context.integer(0));
            }
            risch_options tiny;
            tiny.maximum_matrix_entries = 1;
            assert(!integration_algebraic_quotient_trace(context, value, modulus, x, tiny, trace));
            integration_expr_poly noncanonical = modulus;
            noncanonical.push_back(context.integer(0));
            assert(!integration_algebraic_quotient_trace(context, value, noncanonical,
                x, risch_options(), trace));
            assert(!integration_algebraic_trace_split(context, value, noncanonical,
                x, risch_options(), base, remainder));
            tiny = risch_options();
            tiny.maximum_degree = degree - 1;
            assert(!integration_algebraic_quotient_trace(context, value, modulus, x, tiny, trace));
        }
    }
    {
        exact_expr root = context.square_root(x);
        integration_expr_poly modulus{-x, context.integer(0), context.integer(1)}, value, dz, derivative;
        exact_expr expression = context.integer(1) / (context.integer(1) + root);
        assert(integration_parse_algebraic_quotient(context, expression, root, modulus,
            x, risch_options(), value));
        assert(value.size() == 2);
        for(size_t i = 0; i < 2; ++i){
            exact_expr error = value[i] - context.integer(i ? -1 : 1) / (context.integer(1) - x);
            assert(integration_normalize_expr_coefficient(context, error, x, 64));
            assert(error == context.integer(0));
        }
        assert(integration_algebraic_implicit_derivation(context, modulus, x, risch_options(), dz));
        assert(integration_algebraic_quotient_derivative(context, value, modulus, dz,
            x, risch_options(), derivative));
        integration_expr_poly expected;
        assert(integration_parse_algebraic_quotient(context,
            -context.integer(1) / (context.integer(2) * root *
             context.power(context.integer(1) + root, context.integer(2))), root,
            modulus, x, risch_options(), expected));
        assert(derivative == expected);
        assert(!integration_parse_algebraic_quotient(context,
            context.integer(1) / (root - x), root,
            {-context.power(x, context.integer(2)), context.integer(0), context.integer(1)},
            x, risch_options(), value));
        risch_options tiny;
        tiny.maximum_nodes = 1;
        assert(!integration_parse_algebraic_quotient(context, expression, root, modulus,
            x, tiny, value));
    }
    {
        for(const auto &radicand : {x, x + context.integer(1),
                context.power(x, context.integer(3)) - x}){
            integration_expr_poly modulus{-radicand, context.integer(0), context.integer(1)}, dz, derivative;
            assert(integration_algebraic_implicit_derivation(context, modulus, x, risch_options(), dz));
            assert(dz.size() == 2 && dz[0] == context.integer(0));
            exact_expr error = dz[1] - context.differentiate(radicand, x) /
                (context.integer(2) * radicand);
            assert(integration_normalize_expr_coefficient(context, error, x, 64));
            assert(error == context.integer(0));
            assert(integration_algebraic_quotient_derivative(context,
                {context.integer(0), context.integer(0), context.integer(1)}, modulus, dz,
                x, risch_options(), derivative));
            assert(derivative.size() == 1);
            error = derivative[0] - context.differentiate(radicand, x);
            assert(integration_normalize_expr_coefficient(context, error, x, 64));
            assert(error == context.integer(0));
            integration_expr_poly inverse;
            assert(integration_expr_inverse_mod_rational_coefficients(context,
                {context.integer(0), context.integer(1)}, modulus, x, 64, inverse));
            assert(integration_algebraic_quotient_derivative(context, inverse, modulus, dz,
                x, risch_options(), derivative));
            assert(derivative.size() == 2);
            error = derivative[1] + context.differentiate(radicand, x) /
                (context.integer(2) * context.power(radicand, context.integer(2)));
            assert(integration_normalize_expr_coefficient(context, error, x, 64));
            assert(error == context.integer(0));
        }
        integration_expr_poly modulus{-x - context.integer(1), context.integer(0),
            context.integer(0), context.integer(1)}, dz, derivative;
        assert(integration_algebraic_implicit_derivation(context, modulus, x, risch_options(), dz));
        assert(integration_algebraic_quotient_derivative(context,
            {context.integer(0), context.integer(0), context.integer(0), context.integer(1)},
            modulus, dz, x, risch_options(), derivative));
        assert(derivative.size() == 1 && derivative[0] == context.integer(1));
        assert(!integration_algebraic_implicit_derivation(context,
            {context.power(x, context.integer(2)), -context.integer(2)*x, context.integer(1)},
            x, risch_options(), dz));
        risch_options tiny;
        tiny.maximum_degree = 1;
        assert(!integration_algebraic_implicit_derivation(context, modulus, x, tiny, dz));
    }
    {
        for(const auto &residual : {
                context.integer(1) / (x + context.integer(1)),
                context.integer(1) / (context.power(x, context.integer(5)) - x + context.integer(1))}){
            integration_expr_poly input{residual, context.integer(1)};
            exact_expr solved = integration_parametric_primitive_polynomial(context,
                input, lower_log, x, risch_options(), context.integer(0));
            assert(solved.valid());
            integration_expr_poly error, denominator;
            assert(integration_parse_expr_rational(context,
                context.differentiate(solved, x) - lower_log - residual,
                lower_log, error, denominator, 64, &x));
            for(auto &v : error){
                assert(integration_normalize_expr_coefficient(context, v, x, 64));
                assert(v == context.integer(0));
            }
        }
    }
    {
        exact_expr next_log = context.natural_logarithm(x + context.integer(1));
        exact_expr ratio_log = context.natural_logarithm(x / (x + context.integer(1)));
        std::vector<integration_primitive_derivative_relation> relations;
        assert(integration_primitive_derivative_relations(context, {lower_log, next_log},
            x, risch_options(), relations) == status::solved);
        assert(relations.empty());
        std::vector<exact_expr> generators{lower_log, next_log, ratio_log};
        assert(integration_primitive_derivative_relations(context, generators, x,
            risch_options(), relations) == status::solved);
        assert(relations.size() == 1);
        for(const auto &relation : relations){
            assert(relation.constants.size() == generators.size());
            exact_expr error = -context.differentiate(
                integration_poly_expr(context, relation.numerator, x) /
                integration_poly_expr(context, relation.denominator, x), x);
            for(size_t i = 0; i < generators.size(); ++i)
                error = error + context.value(relation.constants[i]) *
                    context.differentiate(generators[i], x);
            assert(integration_normalize_expr_coefficient(context, error, x, 64));
            assert(error == context.integer(0));
        }
        risch_options tiny;
        tiny.maximum_matrix_entries = 1;
        assert(integration_primitive_derivative_relations(context, generators, x,
            tiny, relations) == status::resource_limit);
        assert(relations.empty());
        assert(integration_primitive_derivative_relations(context,
            {lower_log, context.natural_logarithm(lower_log)}, x, risch_options(), relations) ==
            status::unsupported);
        assert(relations.empty());
    }
    {
        exact_expr second_log = context.natural_logarithm(x + context.integer(1));
        exact_expr original = context.power(x, context.integer(2)) * lower_log * second_log +
            context.power(lower_log, context.integer(2)) / (x + context.integer(1)) +
            context.power(second_log, context.integer(2)) / x;
        for(const auto &a : {context.integer(0), -context.integer(2) / x}){
            exact_expr rhs = context.differentiate(original, x) + a * original;
            integration_expr_poly first;
            assert(integration_parse_expr_poly(context, context.expand(rhs, 100000), lower_log, first));
            integration_expr_poly input(9, context.integer(0));
            for(size_t i = 0; i < first.size(); ++i){
                integration_expr_poly second;
                assert(integration_parse_expr_poly(context, first[i], second_log, second));
                assert(i < 3 && second.size() <= 3);
                for(size_t j = 0; j < second.size(); ++j) input[i + 3*j] = second[j];
            }
            exact_expr solved = integration_parametric_primitive_grid(context, input,
                {lower_log, second_log}, {3,3}, x, risch_options(), a);
            assert(solved.valid());
            integration_expr_poly error;
            assert(integration_parse_expr_poly(context, context.expand(
                context.differentiate(solved, x) + a * solved - rhs, 100000), lower_log, error));
            for(const auto &v : error){
                integration_expr_poly second;
                assert(integration_parse_expr_poly(context, v, second_log, second));
                for(auto &coefficient : second){
                    assert(integration_normalize_expr_coefficient(context, coefficient, x, 64));
                    assert(coefficient == context.integer(0));
                }
            }
        }
    }
    {
        exact_expr original = context.power(x, context.integer(2)) *
            context.power(lower_log, context.integer(2)) +
            lower_log / (x + context.integer(1)) + context.integer(1) / x;
        for(const auto &a : {context.integer(0), -context.integer(2) / x,
                context.integer(2) * x}){
            exact_expr rhs = context.differentiate(original, x) + a * original;
            integration_expr_poly input, error;
            assert(integration_parse_expr_poly(context, context.expand(rhs, 100000), lower_log, input));
            exact_expr solved = integration_parametric_primitive_polynomial(
                context, input, lower_log, x, risch_options(), a);
            assert(solved.valid());
            assert(integration_parse_expr_poly(context, context.expand(
                context.differentiate(solved, x) + a * solved - rhs, 100000), lower_log, error));
            for(auto &v : error){
                assert(integration_normalize_expr_coefficient(context, v, x, 64));
                assert(v == context.integer(0));
            }
            risch_options tiny;
            tiny.maximum_matrix_entries = 1;
            assert(!integration_parametric_primitive_polynomial(
                context, input, lower_log, x, tiny, a).valid());
        }
    }
    {
        exact_expr u = lower_log + x;
        exact_expr input = context.integer(6) * context.differentiate(u, x) /
            (context.power(u, context.integer(3)) - context.integer(2));
        exact_expr logs, polynomial;
        assert(integration_algebraic_residue_logs(context, input, lower_log, x,
            risch_options(), logs, polynomial));
        assert(polynomial == context.integer(0));
        assert(logs.operation() == exact_opcode::algebraic_log_sum);
        integration_expr_poly error, denominator;
        assert(integration_parse_expr_rational(context, context.differentiate(logs, x) - input,
            lower_log, error, denominator, 64, &x));
        for(auto &v : error){
            assert(integration_normalize_expr_coefficient(context, v, x, 64));
            assert(v == context.integer(0));
        }
        assert(context.integrate_elementary(input, x).status == risch_status::elementary);
    }
    {
        exact_expr z = context.symbol("_test_logsum_root");
        exact_expr minimal = context.power(z, context.integer(3)) - context.integer(2);
        exact_expr node = context.algebraic_log_sum(minimal, z, lower_log - z, lower_log, x);
        assert(node.operation() == exact_opcode::algebraic_log_sum);
        assert(node.to_string().find("AlgebraicLogSum(") == 0);
        exact_expr expected = context.integer(6) /
            (x * (context.power(lower_log, context.integer(3)) - context.integer(2)));
        integration_expr_poly error, denominator;
        for(const auto &value : {node, context.simplify(node), context.expand(node, 1000)}){
            assert(value.operation() == exact_opcode::algebraic_log_sum);
            assert(integration_parse_expr_rational(context, context.differentiate(value, x) - expected,
                lower_log, error, denominator, 64, &x));
            for(auto &v : error){
                assert(integration_normalize_expr_coefficient(context, v, x, 64));
                assert(v == context.integer(0));
            }
        }
        assert(context.substitute(node, z, context.integer(7)) == node);
        bool capture = false;
        try{ (void)context.substitute(node, x, x + z); }
        catch(const std::invalid_argument &){ capture = true; }
        assert(capture);
        assert(context.differentiate(node, z) == context.integer(0));
        assert(!integration_depends_on(node, z));
        assert(integration_depends_on(node, x));
        auto bound_integral = context.integrate_elementary(node, z);
        assert(bound_integral.status == risch_status::elementary);
        assert(context.differentiate(bound_integral.elementary_part, z) == node);
        assert(context.differentiate(context.integrate(node, z), z) == node);
    }
    {
        exact_context compact_context;
        exact_expr cx = compact_context.symbol("x"), cz = compact_context.symbol("z");
        exact_expr ct = compact_context.natural_logarithm(cx);
        exact_expr node = compact_context.algebraic_log_sum(
            compact_context.power(cz, compact_context.integer(3)) - compact_context.integer(2),
            cz, ct - cz, ct, cx);
        std::string before = node.to_string();
        node = compact_context.compact(node);
        cx = compact_context.symbol("x"); cz = compact_context.symbol("z");
        ct = compact_context.natural_logarithm(cx);
        assert(node.to_string() == before);
        assert(!integration_depends_on(node, cz));
        integration_expr_poly error, denominator;
        exact_expr expected = compact_context.integer(6) /
            (cx * (compact_context.power(ct, compact_context.integer(3)) - compact_context.integer(2)));
        assert(integration_parse_expr_rational(compact_context,
            compact_context.differentiate(node, cx) - expected, ct, error, denominator, 64, &cx));
        for(auto &v : error){
            assert(integration_normalize_expr_coefficient(compact_context, v, cx, 64));
            assert(v == compact_context.integer(0));
        }
    }
    {
        exact_expr z = context.symbol("_test_residue_parameter");
        exact_expr u = lower_log + x, trace;
        integration_poly minimal{numeric_value(1) / numeric_value(4), numeric_value(0), numeric_value(1)};
        exact_expr expression = z * (context.integer(1) + context.integer(1) / x) /
            (u + context.integer(2) * z);
        assert(integration_algebraic_expression_trace(context, expression, minimal, z,
            lower_log, x, risch_options(), trace));
        exact_expr expected = (context.integer(1) + context.integer(1) / x) /
            (context.power(u, context.integer(2)) + context.integer(1));
        integration_expr_poly error, denominator;
        assert(integration_parse_expr_rational(context, trace - expected, lower_log,
            error, denominator, 64, &x));
        for(auto &v : error){
            assert(integration_normalize_expr_coefficient(context, v, x, 64));
            assert(v == context.integer(0));
        }
        assert(integration_algebraic_expression_trace(context,
            context.integer(1) / (lower_log - z),
            {numeric_value(-2), numeric_value(0), numeric_value(0), numeric_value(1)},
            z, lower_log, x, risch_options(), trace));
        expected = context.integer(3) * context.power(lower_log, context.integer(2)) /
            (context.power(lower_log, context.integer(3)) - context.integer(2));
        assert(integration_parse_expr_rational(context, trace - expected, lower_log,
            error, denominator, 64, &x));
        for(auto &v : error){
            assert(integration_normalize_expr_coefficient(context, v, x, 64));
            assert(v == context.integer(0));
        }
        assert(!integration_algebraic_expression_trace(context, expression, minimal, x,
            lower_log, x, risch_options(), trace));
    }
    {
        integration_residue_algebra algebra{{numeric_value(1) / numeric_value(4),
            numeric_value(0), numeric_value(1)}};
        integration_algebraic_fraction ratio{
            {{numeric_value(0), numeric_value(1)}, {numeric_value(1)}},
            {{numeric_value(0), numeric_value(-1)}, {numeric_value(1)}}};
        integration_algebraic_fraction z{{{numeric_value(0), numeric_value(1)}}, {{numeric_value(1)}}};
        integration_algebraic_function_poly polynomial{integration_algebraic_fraction(), z, ratio};
        for(const auto &generator : {lower_log, context.exponential(x)}){
            integration_algebraic_function_poly dt;
            if(generator == lower_log)
                dt.push_back({{{numeric_value(1)}}, {{numeric_value(0)}, {numeric_value(1)}}});
            else dt = {integration_algebraic_fraction(),
                {{{numeric_value(1)}}, {{numeric_value(1)}}}};
            integration_algebraic_function_poly derived;
            assert(integration_algebraic_function_poly_derivative(algebra, polynomial, dt, 64, derived));
            exact_expr trace, derivative_trace;
            integration_algebraic_function_poly one{{{{numeric_value(1)}}, {{numeric_value(1)}}}};
            assert(integration_algebraic_function_trace(context, algebra, polynomial, one,
                generator, x, risch_options(), trace));
            assert(integration_algebraic_function_trace(context, algebra, derived, one,
                generator, x, risch_options(), derivative_trace));
            integration_expr_poly error, divisor;
            assert(integration_parse_expr_rational(context,
                context.differentiate(trace, x) - derivative_trace, generator, error, divisor, 64, &x));
            for(auto &coefficient : error){
                assert(integration_normalize_expr_coefficient(context, coefficient, x, 64));
                assert(coefficient == context.integer(0));
            }
            assert(!integration_algebraic_function_poly_derivative(algebra, polynomial, dt, 1, derived));
        }
        integration_algebraic_function_poly derived;
        assert(!integration_algebraic_function_poly_derivative(algebra, polynomial, {}, 64, derived));
    }
    {
        integration_residue_algebra algebra{{numeric_value(1) / numeric_value(4),
            numeric_value(0), numeric_value(1)}};
        integration_algebraic_function_poly denominator{
            {{{numeric_value(0), numeric_value(2)}, {numeric_value(1)}}, {{numeric_value(1)}}},
            {{{numeric_value(1)}}, {{numeric_value(1)}}}};
        integration_algebraic_function_poly numerator{
            {{{numeric_value(0), numeric_value(1)}, {numeric_value(0), numeric_value(1)}},
                {{numeric_value(0)}, {numeric_value(1)}}}};
        exact_expr trace;
        assert(integration_algebraic_function_trace(context, algebra, numerator, denominator,
            lower_log, x, risch_options(), trace));
        exact_expr u = lower_log + x;
        exact_expr expected = (context.integer(1) + context.integer(1) / x) /
            (context.power(u, context.integer(2)) + context.integer(1));
        integration_expr_poly error, divisor;
        assert(integration_parse_expr_rational(context, trace - expected, lower_log,
            error, divisor, 64, &x));
        for(auto &v : error){
            assert(integration_normalize_expr_coefficient(context, v, x, 64));
            assert(v == context.integer(0));
        }
        assert(!integration_algebraic_function_trace(context, algebra, numerator,
            {integration_algebraic_fraction()}, lower_log, x, risch_options(), trace));
        integration_residue_algebra cubic{{numeric_value(-2), numeric_value(0),
            numeric_value(0), numeric_value(1)}};
        integration_algebraic_function_poly cubic_denominator{
            {{{numeric_value(0), numeric_value(-1)}}, {{numeric_value(1)}}},
            {{{numeric_value(1)}}, {{numeric_value(1)}}}};
        assert(integration_algebraic_function_trace(context, cubic,
            {{{{numeric_value(1)}}, {{numeric_value(1)}}}}, cubic_denominator,
            lower_log, x, risch_options(), trace));
        expected = context.integer(3) * context.power(lower_log, context.integer(2)) /
            (context.power(lower_log, context.integer(3)) - context.integer(2));
        assert(integration_parse_expr_rational(context, trace - expected, lower_log,
            error, divisor, 64, &x));
        for(auto &v : error){
            assert(integration_normalize_expr_coefficient(context, v, x, 64));
            assert(v == context.integer(0));
        }
    }
    for(int constant : {1, -2}){
        exact_expr u = x + lower_log;
        exact_expr input = context.differentiate(u, x) /
            (context.power(u, context.integer(2)) + context.integer(constant));
        exact_expr candidate = integration_quadratic_residue_logs(context, input,
            lower_log, x, risch_options());
        assert(candidate.valid());
        assert(context.integrate_elementary(input, x).status == risch_status::elementary);
    }
    {
        exact_expr u = x + lower_log;
        exact_expr input = context.differentiate(u, x) /
            (context.power(u, context.integer(2)) + context.integer(1));
        integration_poly minimal{numeric_value(1) / numeric_value(4), numeric_value(0), numeric_value(1)};
        integration_algebraic_function_poly factor;
        assert(integration_algebraic_residue_factor(context, input, lower_log, x,
            minimal, risch_options(), factor));
        assert(factor.size() == 2);
        assert(factor[0].numerator == integration_residue_poly({{numeric_value(0), numeric_value(2)},
            {numeric_value(1)}}));
        assert(factor[0].denominator == integration_residue_poly({{numeric_value(1)}}));
        assert(!integration_algebraic_residue_factor(context, input, lower_log, x,
            {numeric_value(1), numeric_value(0), numeric_value(1)}, risch_options(), factor));
        assert(!integration_algebraic_residue_factor(context, x * input, lower_log, x,
            minimal, risch_options(), factor));
    }
    {
        integration_residue_algebra algebra{{numeric_value(1) / numeric_value(4),
            numeric_value(0), numeric_value(1)}};
        auto coefficient = [](integration_residue_poly n){
            return integration_algebraic_fraction{std::move(n), {{numeric_value(1)}}};
        };
        integration_algebraic_function_poly d{
            coefficient({{numeric_value(1)}, {numeric_value(0)}, {numeric_value(1)}}),
            coefficient({{numeric_value(0)}, {numeric_value(2)}}), coefficient({{numeric_value(1)}})};
        integration_algebraic_function_poly difference{
            coefficient({{numeric_value(1)}, {numeric_value(0), numeric_value(-2)}}),
            coefficient({{numeric_value(0), numeric_value(-2)}})};
        for(auto &v : d) v.denominator = {{numeric_value(1)}, {numeric_value(1)}};
        integration_algebraic_function_poly gcd;
        assert(integration_algebraic_function_poly_gcd(algebra, d, difference, 64, gcd));
        assert(gcd.size() == 2);
        assert(gcd[0].numerator == integration_residue_poly({{numeric_value(0), numeric_value(2)},
            {numeric_value(1)}}));
        assert(gcd[0].denominator == integration_residue_poly({{numeric_value(1)}}));
        assert(gcd[1].numerator == integration_residue_poly({{numeric_value(1)}}));
        assert(!integration_algebraic_function_poly_gcd(algebra, d, difference, 0, gcd));
    }
    {
        integration_residue_algebra algebra{{numeric_value(1), numeric_value(0), numeric_value(1)}};
        integration_algebraic_fraction f{
            {{numeric_value(0), numeric_value(1)}, {numeric_value(1)}},
            {{numeric_value(0), numeric_value(-1)}, {numeric_value(1)}}};
        integration_algebraic_fraction inverse, product, derivative;
        assert(integration_algebraic_fraction_normalize(algebra, f, 64));
        exact_expr trace;
        assert(integration_algebraic_fraction_trace(context, algebra, f, x, risch_options(), trace));
        exact_expr error = trace - context.integer(2) *
            (context.power(x, context.integer(2)) - context.integer(1)) /
            (context.power(x, context.integer(2)) + context.integer(1));
        assert(integration_normalize_expr_coefficient(context, error, x, 64));
        assert(error == context.integer(0));
        risch_options tiny_trace;
        tiny_trace.maximum_matrix_entries = 1;
        assert(!integration_algebraic_fraction_trace(context, algebra, f, x, tiny_trace, trace));
        integration_residue_algebra cubic{{numeric_value(-2), numeric_value(0),
            numeric_value(0), numeric_value(1)}};
        integration_algebraic_fraction z{{{numeric_value(0), numeric_value(1)}}, {{numeric_value(1)}}};
        assert(integration_algebraic_fraction_trace(context, cubic, z, x, risch_options(), trace));
        assert(trace == context.integer(0));
        integration_algebraic_fraction cube{{{numeric_value(0), numeric_value(0),
            numeric_value(0), numeric_value(1)}}, {{numeric_value(1)}}};
        assert(integration_algebraic_fraction_trace(context, cubic, cube, x, risch_options(), trace));
        assert(trace == context.integer(6));
        assert(integration_algebraic_fraction_inverse(algebra, f, 64, inverse));
        assert(integration_algebraic_fraction_combine(algebra, f, inverse, true, 64, product));
        assert(product.numerator == integration_residue_poly({{numeric_value(1)}}));
        assert(product.denominator == integration_residue_poly({{numeric_value(1)}}));
        assert(integration_algebraic_fraction_derivative(algebra, f, 64, derivative));
        assert(derivative.numerator == integration_residue_poly({{numeric_value(0), numeric_value(-2)}}));
        assert(derivative.denominator == integration_residue_poly({{numeric_value(-1)},
            {numeric_value(0), numeric_value(-2)}, {numeric_value(1)}}));
        integration_algebraic_fraction minus_f = f;
        for(auto &coefficient : minus_f.numerator) for(auto &v : coefficient) v = -v;
        assert(integration_algebraic_fraction_combine(algebra, f, minus_f, false, 64, product));
        assert(product.numerator == integration_residue_poly({{numeric_value(0)}}));
        assert(product.denominator == integration_residue_poly({{numeric_value(1)}}));
        assert(!integration_algebraic_fraction_inverse(algebra, product, 64, inverse));
        assert(!integration_algebraic_fraction_derivative(algebra, f, 1, derivative));
    }
    {
        integration_residue_algebra algebra{{numeric_value(1) / numeric_value(4),
            numeric_value(0), numeric_value(1)}};
        integration_poly inverse;
        assert(algebra.inverse({numeric_value(0), numeric_value(1)}, inverse));
        assert(inverse == integration_poly({numeric_value(0), numeric_value(-4)}));
        integration_residue_poly gcd;
        assert(integration_residue_poly_gcd(algebra,
            {{numeric_value(1)}, {numeric_value(0)}, {numeric_value(1)}},
            {{numeric_value(1)}, {numeric_value(0), numeric_value(-2)}}, 64, gcd));
        assert(gcd == integration_residue_poly({{numeric_value(0), numeric_value(2)},
            {numeric_value(1)}}));
        integration_residue_algebra reducible{{numeric_value(-1), numeric_value(0), numeric_value(1)}};
        assert(!reducible.inverse({numeric_value(-1), numeric_value(1)}, inverse));
        assert(!algebra.inverse({numeric_value(0)}, inverse));
        assert(!integration_residue_poly_gcd(algebra,
            {{numeric_value(1)}, {numeric_value(1)}}, {{numeric_value(1)}}, 0, gcd));
    }
    {
        exact_expr p = lower_log + x, q = lower_log + context.integer(2) * x;
        exact_expr original = context.natural_logarithm(p) -
            context.natural_logarithm(q) / context.integer(2);
        exact_expr f = context.differentiate(original, x), logs, polynomial;
        assert(integration_rational_residue_logs(context, f, lower_log, x,
            risch_options(), logs, polynomial));
        assert(polynomial == context.integer(0));
        assert(context.integrate_elementary(f, x).status == risch_status::elementary);
        integration_expr_poly error, denominator;
        assert(integration_parse_expr_rational(context, context.differentiate(logs - original, x),
            lower_log, error, denominator, 64, &x));
        for(auto &v : error){
            assert(integration_normalize_expr_coefficient(context, v, x, 64));
            assert(v == context.integer(0));
        }
        assert(!integration_rational_residue_logs(context, x * f, lower_log, x,
            risch_options(), logs, polynomial));
    }
    {
        // Two distinct rational residues, represented without factoring the denominator.
        integration_expr_poly d{context.integer(2) * context.power(x, context.integer(2)),
            context.integer(3) * x, context.integer(1)};
        integration_expr_poly r{context.integer(0), -context.integer(1) / x};
        integration_expr_poly characteristic;
        assert(integration_residue_characteristic_polynomial(context, r, d, x,
            risch_options(), characteristic));
        assert(characteristic.size() == 3 && characteristic[0] == context.integer(2) &&
            characteristic[1] == context.integer(-3) && characteristic[2] == context.integer(1));
        risch_options tiny;
        tiny.maximum_matrix_entries = 1;
        assert(!integration_residue_characteristic_polynomial(context, r, d, x,
            tiny, characteristic));
        assert(integration_residue_characteristic_polynomial(context, {x}, d, x,
            risch_options(), characteristic));
        assert(characteristic[0] == context.power(x, context.integer(2)) &&
            characteristic[1] == -context.integer(2) * x);
    }
    {
        exact_expr p = x + lower_log + context.integer(1);
        exact_expr original = x / context.power(p, context.integer(2)) +
            context.natural_logarithm(p);
        exact_expr f = context.differentiate(original, x);
        exact_expr candidate = integration_normal_hermite_primitive(context, f, x, risch_options());
        assert(candidate.valid());
        auto strict = context.integrate_elementary(f, x);
        assert(strict.status == risch_status::elementary);
        assert(context.integrate(f, x).operation() != exact_opcode::integral);
        integration_expr_poly error, denominator;
        assert(integration_parse_expr_rational(context,
            context.differentiate(candidate - original, x), lower_log,
            error, denominator, 64, &x));
        for(auto &v : error){
            assert(integration_normalize_expr_coefficient(context, v, x, 64));
            assert(v == context.integer(0));
        }
    }
    {
        exact_expr t = lower_log, p = x + t + context.integer(1);
        exact_expr q = t + context.integer(2);
        exact_expr input = (x + t) / (context.power(p, context.integer(3)) *
            context.power(q, context.integer(2)));
        exact_expr primitive, remainder;
        assert(integration_normal_hermite_reduce(context, input, t, x,
            risch_options(), primitive, remainder));
        integration_expr_poly error, denominator;
        assert(integration_parse_expr_rational(context,
            input - context.differentiate(primitive, x) - remainder, t, error, denominator, 64, &x));
        for(auto &v : error){
            assert(integration_normalize_expr_coefficient(context, v, x, 64));
            assert(v == context.integer(0));
        }
        assert(integration_parse_expr_rational(context, remainder, t, error, denominator, 64));
        integration_expr_poly partial(denominator.size() - 1, context.integer(0)), gcd;
        for(size_t i = 1; i < denominator.size(); ++i)
            partial[i - 1] = context.integer(i) * denominator[i];
        assert(integration_expr_gcd_rational_coefficients(context, denominator, partial, x, 64, gcd));
        assert(gcd.size() == 1 && gcd[0] == context.integer(1));
        assert(integration_normal_hermite_reduce(context,
            context.integer(1) / context.exponential(x), context.exponential(x), x,
            risch_options(), primitive, remainder));
        assert(primitive == context.integer(0));
        assert(remainder == context.integer(1) / context.exponential(x));
    }
    {
        exact_expr t = context.exponential(x), p = t + context.integer(1);
        for(size_t special_order : {2u, 3u}){
            exact_expr input = context.integer(1) /
                (context.power(t, context.integer(special_order)) *
                 context.power(p, context.integer(2)));
            exact_expr primitive, remainder;
            assert(integration_normal_hermite_reduce(context, input, t, x,
                risch_options(), primitive, remainder));
            assert(primitive != context.integer(0));
            integration_expr_poly error, denominator;
            assert(integration_parse_expr_rational(context,
                input - context.differentiate(primitive, x) - remainder,
                t, error, denominator, 64, &x));
            for(auto &v : error){
                assert(integration_normalize_expr_coefficient(context, v, x, 64));
                assert(v == context.integer(0));
            }
            assert(integration_parse_expr_rational(context, remainder, t,
                error, denominator, 64, &x));
            integration_expr_poly normal, special;
            assert(integration_differential_denominator_parts(context, denominator,
                t, x, risch_options(), normal, special));
            assert(special.size() == 2);
            auto solved = context.integrate_elementary(input, x);
            assert(solved.status == risch_status::elementary);
            assert(solved.remainder == context.integer(0));
            assert(integration_parse_expr_rational(context,
                context.differentiate(solved.elementary_part, x) - input,
                t, error, denominator, 64, &x));
            for(auto &v : error){
                assert(integration_normalize_expr_coefficient(context, v, x, 64));
                assert(v == context.integer(0));
            }
        }
    }
    {
        exact_expr t = context.exponential(context.power(x, context.integer(2)));
        exact_expr original = context.integer(1) /
            context.power(t + context.integer(1), context.integer(2));
        exact_expr input = context.differentiate(original, x) + t;
        auto solved = context.integrate_elementary(input, x);
        assert(solved.status == risch_status::proven_nonelementary);
        assert(solved.elementary_part != context.integer(0));
        assert(solved.remainder != context.integer(0));
        integration_expr_poly error, denominator;
        assert(integration_parse_expr_rational(context,
            input - context.differentiate(solved.elementary_part, x) - solved.remainder,
            t, error, denominator, 64, &x));
        for(auto &v : error){
            assert(integration_normalize_expr_coefficient(context, v, x, 64));
            assert(v == context.integer(0));
        }
        assert(context.integrate_elementary(solved.remainder, x).status ==
            risch_status::proven_nonelementary);
    }
    for(const auto &t : {lower_log, context.exponential(x)}){
        integration_expr_poly pole{x, context.integer(1)};
        for(size_t m : {2u, 3u, 5u}){
            integration_expr_poly n{context.integer(1), x}, b, r;
            assert(integration_normal_pole_reduce_step(context, n, pole, m, t, x,
                risch_options(), b, r));
            exact_expr p = integration_expr_poly_expr(context, pole, t);
            exact_expr f = integration_expr_poly_expr(context, n, t) /
                context.power(p, context.integer(m));
            exact_expr primitive = integration_expr_poly_expr(context, b, t) /
                context.power(p, context.integer(m - 1));
            exact_expr rest = integration_expr_poly_expr(context, r, t) /
                context.power(p, context.integer(m - 1));
            integration_expr_poly error, denominator;
            assert(integration_parse_expr_rational(context,
                f - context.differentiate(primitive, x) - rest, t, error, denominator, 64));
            for(auto &v : error){
                assert(integration_normalize_expr_coefficient(context, v, x, 64));
                assert(v == context.integer(0));
            }
        }
        integration_expr_poly b, r;
        assert(!integration_normal_pole_reduce_step(context,
            {context.integer(1)}, pole, 1, t, x, risch_options(), b, r));
    }
    {
        integration_expr_poly b, r;
        assert(!integration_normal_pole_reduce_step(context, {context.integer(1)},
            {context.integer(0), context.integer(1)}, 2, context.exponential(x), x,
            risch_options(), b, r));
    }
    {
        integration_expr_poly normal, special, polynomial, quotient, remainder;
        exact_expr t = context.exponential(x);
        assert(integration_parse_expr_poly(context, context.expand(
            context.power(t, context.integer(3)) *
            context.power(t + context.integer(1), context.integer(2)), 100000), t, polynomial));
        assert(integration_differential_denominator_parts(context, polynomial, t, x,
            risch_options(), normal, special));
        assert(normal.size() == 2 && normal[0] == context.integer(1) &&
            normal[1] == context.integer(1));
        assert(special.size() == 2 && special[0] == context.integer(0) &&
            special[1] == context.integer(1));
        assert(integration_parse_expr_poly(context, context.expand(
            context.power(lower_log + x, context.integer(3)), 100000), lower_log, polynomial));
        assert(integration_differential_denominator_parts(context, polynomial, lower_log, x,
            risch_options(), normal, special));
        assert(normal.size() == 2 && normal[0] == x && normal[1] == context.integer(1));
        assert(special.size() == 1 && special[0] == context.integer(1));
        assert(integration_expr_divmod_rational_coefficients(context,
            {context.integer(1)}, {x, context.integer(1)}, x, 64, quotient, remainder));
        assert(quotient.size() == 1 && quotient[0] == context.integer(0));
        assert(remainder.size() == 1 && remainder[0] == context.integer(1));
        integration_expr_poly inverse;
        assert(integration_expr_inverse_mod_rational_coefficients(context,
            {context.integer(0), context.integer(1)},
            {context.integer(1), context.integer(0), context.integer(1)}, x, 64, inverse));
        assert(inverse.size() == 2 && inverse[0] == context.integer(0) &&
            inverse[1] == context.integer(-1));
        assert(integration_expr_inverse_mod_rational_coefficients(context,
            {context.integer(1) / x}, {x, context.integer(1)}, x, 64, inverse));
        assert(inverse.size() == 1 && inverse[0] == x);
        assert(!integration_expr_inverse_mod_rational_coefficients(context,
            {x, context.integer(1)}, {x, context.integer(1)}, x, 64, inverse));
        assert(!integration_differential_denominator_parts(context,
            {context.integer(0)}, lower_log, x, risch_options(), normal, special));
    }
    for(const auto &t : {lower_log,
            context.natural_logarithm(x / (x + context.integer(1)))}){
        exact_expr q = x + t + context.integer(1);
        for(const auto &original : {
                x / q,
                context.power(x + t, context.integer(2)) / context.power(q, context.integer(2)),
                x / ((x + context.integer(2)) * q)}){
            exact_expr f = context.differentiate(original, x);
            exact_expr candidate = integration_primitive_rational_derivative(
                context, f, x, risch_options());
            if(!candidate.valid())
                fprintf(stderr, "Primitive rational ansatz failed: %s\n", f.to_string().c_str());
            assert(candidate.valid());
            assert(context.integrate_elementary(f, x).status == risch_status::elementary);
            exact_expr ordinary = context.integrate(f, x);
            assert(ordinary.operation() != exact_opcode::integral);
            for(const auto &primitive : {candidate, ordinary}){
                exact_expr error = context.differentiate(primitive - original, x);
                integration_expr_poly coefficients, denominator;
                assert(integration_parse_expr_rational(context, error, t, coefficients, denominator, 64));
                for(const auto &coefficient : coefficients){
                    integration_poly n, d;
                    assert(integration_parse_rational(coefficient, x, n, d));
                    assert(integration_normalize_rational(n, d));
                    assert(integration_zero_poly(n));
                }
            }
            risch_options tiny;
            tiny.maximum_matrix_entries = 1;
            assert(!integration_primitive_rational_derivative(context, f, x, tiny).valid());
        }
    }
    integration_expr_poly divided;
    assert(integration_expr_divide_rational_coefficients(context,
        {context.power(x, context.integer(2)) - context.integer(1),
            context.integer(2) * x, context.integer(1)},
        {x - context.integer(1), context.integer(1)}, x, 64, divided));
    assert(divided.size() == 2 && divided[0] == x + context.integer(1) &&
        divided[1] == context.integer(1));
    assert(!integration_expr_divide_rational_coefficients(context,
        {context.integer(1)}, {x, context.integer(1)}, x, 64, divided));
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
        if(error != context.integer(0)){
            integration_expr_poly numerator, denominator;
            assert(integration_parse_expr_rational(context, error, lower_log,
                numerator, denominator, 64, &x));
            for(auto &coefficient : numerator){
                assert(integration_normalize_expr_coefficient(context, coefficient, x, 64));
                assert(coefficient == context.integer(0));
            }
            error = context.integer(0);
        }
        if(error != context.integer(0))
            fprintf(stderr, "nested candidate: %s\noriginal: %s\nerror: %s\n",
                nested.elementary_part.to_string().c_str(), original.to_string().c_str(),
                error.to_string().c_str());
        assert(error == context.integer(0));
    }
    risch_options no_recursion;
    no_recursion.maximum_recursion_depth = 0;
    assert(context.integrate_elementary(x, x, no_recursion).status == risch_status::resource_limit);
    assert(context.integrate_elementary(x, x).status == risch_status::elementary);
    puts("parametric RDE and coupled primitive ok");
}
