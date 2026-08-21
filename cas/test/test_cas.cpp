#include"../prec_cas.hpp"
#include"../src/factor_integer.hpp"

#include<cassert>
#include<cstdio>
#include<stdexcept>
#include<string>
#include<vector>

int main(){
    exact_context context;

    exact_value exact_third(precq_t(precn_t(1), precn_t(3)));
    exact_value approximate_third(exact_third.to_number(256));
    assert(approximate_third.is_approximate());
    assert(!exact_third.is_approximate());
    exact_value mixed = approximate_third + exact_value(2);
    assert(mixed.is_approximate());
    Number expected_mixed =
        exact_value(precq_t(precn_t(7), precn_t(3))).to_number(256);
    Number mixed_error = mixed.number() - expected_mixed;
    Number mixed_tolerance = Number::from_raw(precz_t(1), 2, 256);
    assert(abs(mixed_error) < mixed_tolerance);

    exact_expr approximate_node_a = context.value(approximate_third);
    exact_expr approximate_node_b = context.value(approximate_third);
    assert(approximate_node_a == approximate_node_b);
    assert(approximate_node_a != context.value(exact_third));

    Number approximate_one(1.0);
    Number approximate_zero(0.0);
    approximate_one.set_precision(256);
    approximate_zero.set_precision(256);
    exact_expr approximate_one_node =
        context.value(exact_value(std::move(approximate_one)));
    exact_expr approximate_zero_node =
        context.value(exact_value(std::move(approximate_zero)));
    exact_expr approximate_pi = context.multiply({approximate_one_node,
                                                   context.pi()});
    assert(approximate_pi.is_value());
    assert(approximate_pi.value().is_approximate());
    exact_expr approximate_zero_plus_pi = context.add({approximate_zero_node,
                                                        context.pi()});
    assert(approximate_zero_plus_pi.is_value());
    assert(approximate_zero_plus_pi.value().is_approximate());
    exact_expr approximate_e = exp(approximate_one_node);
    assert(approximate_e.is_value());
    assert(approximate_e.value().is_approximate());
    exact_expr approximate_cos_zero = cos(approximate_zero_node);
    assert(approximate_cos_zero.is_value());
    assert(approximate_cos_zero.value().is_approximate());

    bool exact_division_by_zero = false;
    try{
        context.divide(context.integer(0), context.integer(0));
    }catch(const std::domain_error &error){
        exact_division_by_zero =
            std::string(error.what()) == "division by zero";
    }
    assert(exact_division_by_zero);
    bool approximate_division_by_zero = false;
    try{
        context.divide(approximate_zero_node, approximate_zero_node);
    }catch(const std::domain_error &error){
        approximate_division_by_zero =
            std::string(error.what()) == "division by zero";
    }
    assert(approximate_division_by_zero);

    Number approximate_nine(9);
    approximate_nine.set_precision(256);
    exact_expr approximate_root = sqrt(context.value(exact_value(approximate_nine)));
    assert(approximate_root.is_value());
    assert(approximate_root.value().is_approximate());
    assert(approximate_root.value().number() == Number(3));
    Number approximate_minus_one(-1.0);
    approximate_minus_one.set_precision(256);
    bool approximate_negative_sqrt = false;
    try{
        (void)sqrt(context.value(exact_value(
            std::move(approximate_minus_one))));
    }catch(const std::domain_error &error){
        approximate_negative_sqrt =
            std::string(error.what()) == "square root of a negative number";
    }
    assert(approximate_negative_sqrt);
    Number approximate_half =
        exact_value(precq_t(precn_t(1), precn_t(2))).to_number(256);
    exact_expr approximate_power = context.power(
        context.integer(9), context.value(exact_value(approximate_half)));
    assert(approximate_power.is_value());
    assert(approximate_power.value().is_approximate());
    assert(abs(approximate_power.value().number() - Number(3)) < mixed_tolerance);

    size_t before_two = context.node_count();
    exact_expr two_a = context.integer(2);
    exact_expr two_b = context.integer(2);
    assert(two_a == two_b);
    assert(context.node_count() == before_two + 1);

    Number approximate_ten(10.0);
    Number approximate_fifty_half(50.5);
    approximate_ten.set_precision(1000);
    approximate_fifty_half.set_precision(1000);
    exact_expr delayed_power = context.power(
        context.value(exact_value(std::move(approximate_ten))),
        context.value(exact_value(std::move(approximate_fifty_half))));
    assert(delayed_power.operation() == exact_opcode::power);
    exact_expr squared_delayed_power = context.power(delayed_power, two_a);
    assert(squared_delayed_power.is_value());
    std::string ten_to_101 = "1" + std::string(101, '0');
    assert(squared_delayed_power.value().number() == Number(precn_t(ten_to_101)));

    exact_expr one = context.integer(1);
    exact_expr three = context.integer(3);
    exact_expr folded = context.add({one, two_a, three});
    assert(folded.is_value());
    assert(folded.value() == exact_value(6));

    exact_expr pi_constant = context.pi();
    exact_expr e_constant = context.e();
    assert(pi_constant == context.pi());
    assert(e_constant == context.e());
    assert(pi_constant.to_string() == "pi");
    assert(e_constant.to_string() == "e");
    assert(exp(one) == e_constant);
    assert(ln(e_constant) == one);
    assert(ln(context.power(e_constant, two_a)) == two_a);
    assert(sin(pi_constant) == context.integer(0));
    assert(cos(pi_constant) == context.integer(-1));
    assert(tan(pi_constant) == context.integer(0));
    exact_expr half_pi = context.multiply({
        context.rational(precq_t(precn_t(1), precn_t(2))), pi_constant});
    exact_expr third_pi = context.multiply({
        context.rational(precq_t(precn_t(1), precn_t(3))), pi_constant});
    exact_expr quarter_pi = context.multiply({
        context.rational(precq_t(precn_t(1), precn_t(4))), pi_constant});
    assert(sin(half_pi) == one);
    assert(sin(third_pi) == context.multiply({
        context.rational(precq_t(precn_t(1), precn_t(2))), sqrt(three)}));
    assert(sin(quarter_pi) == context.multiply({
        context.rational(precq_t(precn_t(1), precn_t(2))), sqrt(two_a)}));
    assert(cos(third_pi) ==
           context.rational(precq_t(precn_t(1), precn_t(2))));
    assert(tan(quarter_pi) == one);
    bool exact_tan_pole = false;
    try{
        (void)tan(half_pi);
    }catch(const std::domain_error &){
        exact_tan_pole = true;
    }
    assert(exact_tan_pole);
    Number approximate_two(2.0);
    approximate_two.set_precision(256);
    exact_expr approximate_half_pi = context.divide(
        pi_constant, context.value(exact_value(std::move(approximate_two))));
    bool approximate_tan_pole = false;
    try{
        (void)tan(approximate_half_pi);
    }catch(const std::domain_error &){
        approximate_tan_pole = true;
    }
    assert(approximate_tan_pole);
    exact_expr approximate_pi_sum = context.add({pi_constant, approximate_node_a});
    assert(approximate_pi_sum.is_value());
    Number expected_pi_sum = getpi(90) + approximate_third.number();
    assert(abs(approximate_pi_sum.value().number() - expected_pi_sum) <
           mixed_tolerance);

    exact_expr x = context.symbol("x");
    exact_expr y = context.symbol("y");
    exact_expr polynomial_xy = context.power(x, context.integer(2)) +
        context.integer(2) * x * y + context.power(y, context.integer(2));
    assert(context.substitute(polynomial_xy, x, y) ==
           context.integer(4) * context.power(y, context.integer(2)));
    exact_expr x_plus_y = x + y;
    assert(context.substitute(context.power(x_plus_y, context.integer(2)),
                              x_plus_y, context.integer(3)) ==
           context.integer(9));
    assert(context.substitute(sin(x), x, half_pi) == one);
    assert(context.substitute(polynomial_xy, context.symbol("z"), one) ==
           polynomial_xy);
    assert(context.is_polynomial(polynomial_xy));
    exact_expr factored_difference = context.factor(
        context.power(x, context.integer(2)) -
        context.power(y, context.integer(2)));
    assert(context.expand(factored_difference) ==
           context.power(x, context.integer(2)) -
           context.power(y, context.integer(2)));
    assert(factored_difference.operation() == exact_opcode::multiply);
    exact_expr factored_common = context.factor(
        context.integer(2) * x + context.integer(2) * y);
    assert(factored_common.operation() == exact_opcode::multiply);
    assert(context.expand(factored_common) ==
           context.integer(2) * x + context.integer(2) * y);
    assert(context.gcd(context.integer(48), context.integer(-18)) ==
           context.integer(6));
    assert(context.factor_integer(context.integer(360)).to_string() ==
           "{2^3, 3^2, 5}");
    assert(context.factor_integer(context.integer(-12)).to_string() ==
           "{-1, 2^2, 3}");
    assert(context.factor_integer(context.integer(1)).to_string() == "{}");
    assert(context.factor_integer(context.integer(UINT64_C(1000036000099)))
               .to_string() == "{1000003, 1000033}");
    assert(context.factor_integer(context.value(exact_value(
               precz_t("18446799413941772685654671")))).to_string() ==
           "{1000003, 18446744073709551557}");
    precn_t fermat_eight = (precn_t(1) << 256) + 1;
    assert(context.factor_integer(context.value(exact_value(
               precz_t(fermat_eight)))).to_string() ==
           "{1238926361552897, "
           "93461639715357977769163558199606896584051237541638188580280321}");
    precn_t mersenne_256 = (precn_t(1) << 256) - 1;
    exact_expr parsed_style_mersenne =
        context.power(context.integer(2), context.integer(256)) -
        context.integer(1);
    assert(parsed_style_mersenne.is_value() &&
           parsed_style_mersenne.value().is_integer() &&
           parsed_style_mersenne.value().integer().magnitude() == mersenne_256);
    assert(context.factor_integer(parsed_style_mersenne).to_string() ==
           "{3, 5, 17, 257, 641, 65537, 274177, 6700417, 67280421310721, "
           "59649589127497217, 5704689200685129054721}");
    precn_t qs_input("1000036000099");
    precn_t rho_factor = cas_pollard_rho_factor(qs_input);
    assert(rho_factor > precn_t(1) && rho_factor < qs_input &&
           (qs_input % rho_factor).rsiz == 0);
    precn_t siqs_factor = cas_siqs_factor(qs_input, 64, 256);
    assert(siqs_factor > precn_t(1) && siqs_factor < qs_input &&
           (qs_input % siqs_factor).rsiz == 0);
    precn_t qs_factor = cas_qs_factor(qs_input);
    assert(qs_factor > precn_t(1) && qs_factor < qs_input &&
           (qs_input % qs_factor).rsiz == 0);
    assert(context.gcd(context.power(x, context.integer(2)) -
                           context.integer(1),
                       context.power(x, context.integer(2)) -
                           context.integer(2) * x + context.integer(1)) ==
           x - context.integer(1));
    exact_expr multivariate_gcd_left =
        context.power(x + y, context.integer(2));
    exact_expr multivariate_gcd_right =
        (x + y) * (x - y);
    assert(context.gcd(multivariate_gcd_left, multivariate_gcd_right) == x + y);
    assert(context.factor(context.power(x, context.integer(3)) -
                          context.integer(1)).to_string() ==
           "(x - 1)*(x^2 + x + 1)");
    exact_expr power_105_difference =
        context.power(x, context.integer(105)) - context.integer(1);
    exact_expr factored_105 = context.factor(power_105_difference);
    assert(factored_105.operation() == exact_opcode::multiply);
    assert(factored_105.operand_count() == 8);
    assert(context.expand(factored_105) == power_105_difference);
    std::string factored_105_text = factored_105.to_string();
    assert(factored_105_text.find("(x^2 + x + 1)") <
           factored_105_text.find("(x^4 + x^3 + x^2 + x + 1)"));
    assert(context.factor(context.power(x, context.integer(2)) +
                          context.integer(2) * x + context.integer(1))
               .to_string() == "(x + 1)^2");
    exact_expr symbolic_groebner = context.groebner(
        {x + y - context.symbol("a"), x - y + context.symbol("b")}, {x, y});
    assert(symbolic_groebner.operation() == exact_opcode::expression_list);
    assert(symbolic_groebner.operand_count() == 3);
    exact_expr symbolic_system = context.exact_solve(
        {context.power(x, context.integer(2)) - context.symbol("a"), x - y},
        {x, y});
    assert(symbolic_system.operation() == exact_opcode::expression_list);
    exact_expr nested_repeated = context.power(x, context.integer(6)) +
        context.integer(2) * context.power(x, context.integer(5)) +
        context.integer(3) * context.power(x, context.integer(4)) +
        context.integer(4) * context.power(x, context.integer(3)) +
        context.integer(3) * context.power(x, context.integer(2)) +
        context.integer(2) * x + one;
    assert(context.factor(nested_repeated).to_string() ==
           "(x + 1)^2*(x^2 + 1)^2");
    exact_expr general_quartic = context.power(x, context.integer(4)) -
        context.integer(5) * context.power(x, context.integer(2)) +
        context.integer(4);
    exact_expr factored_general_quartic = context.factor(general_quartic);
    assert(factored_general_quartic.to_string() ==
           "(x + 1)*(x + 2)*(x - 1)*(x - 2)");
    assert(context.expand(factored_general_quartic) == general_quartic);
    exact_expr repeated_root_polynomial =
        context.power(x, context.integer(5)) -
        context.integer(5) * context.power(x, context.integer(4)) +
        context.integer(10) * context.power(x, context.integer(3)) -
        context.integer(10) * context.power(x, context.integer(2)) +
        context.integer(5) * x - context.integer(1);
    assert(context.factor(repeated_root_polynomial).to_string() == "(x - 1)^5");
    exact_expr repeated_irreducible = context.power(x, context.integer(6)) +
        context.integer(3) * context.power(x, context.integer(4)) +
        context.integer(3) * context.power(x, context.integer(2)) +
        context.integer(1);
    exact_expr factored_repeated_irreducible = context.factor(repeated_irreducible);
    assert(factored_repeated_irreducible.to_string() == "(x^2 + 1)^3");
    assert(context.expand(factored_repeated_irreducible) == repeated_irreducible);
    exact_expr quartic_without_rational_roots =
        context.power(x, context.integer(4)) +
        context.integer(5) * context.power(x, context.integer(2)) +
        context.integer(4);
    exact_expr factored_without_rational_roots =
        context.factor(quartic_without_rational_roots);
    assert(factored_without_rational_roots.to_string() ==
           "(x^2 + 1)*(x^2 + 4)");
    assert(context.expand(factored_without_rational_roots) ==
           quartic_without_rational_roots);
    exact_expr asymmetric_quartic = context.power(x, context.integer(4)) +
        context.integer(3) * context.power(x, context.integer(3)) +
        context.integer(5) * context.power(x, context.integer(2)) +
        context.integer(4) * x + context.integer(2);
    assert(context.factor(asymmetric_quartic).to_string() ==
           "(x^2 + 2*x + 2)*(x^2 + x + 1)");
    exact_expr modular_sextic = context.power(x, context.integer(6)) +
        context.integer(3) * context.power(x, context.integer(4)) +
        context.integer(3) * context.power(x, context.integer(3)) +
        context.integer(2) * context.power(x, context.integer(2)) +
        context.integer(4) * x + context.integer(2);
    exact_expr factored_modular_sextic = context.factor(modular_sextic);
    assert(factored_modular_sextic.to_string() ==
           "(x^3 + 2*x + 2)*(x^3 + x + 1)");
    assert(context.expand(factored_modular_sextic) == modular_sextic);
    exact_expr lifted_modular_sextic = context.power(x, context.integer(6)) +
        context.integer(24) * context.power(x, context.integer(3)) -
        context.integer(100) * context.power(x, context.integer(2)) -
        context.integer(20) * x + context.integer(143);
    exact_expr factored_lifted_sextic = context.factor(lifted_modular_sextic);
    assert(factored_lifted_sextic.operation() == exact_opcode::multiply);
    assert(context.expand(factored_lifted_sextic) == lifted_modular_sextic);
    exact_expr three_quadratic_factors = context.power(x, context.integer(6)) +
        context.integer(6) * context.power(x, context.integer(4)) +
        context.integer(11) * context.power(x, context.integer(2)) +
        context.integer(6);
    exact_expr recursively_factored = context.factor(three_quadratic_factors);
    assert(recursively_factored.to_string() ==
           "(x^2 + 1)*(x^2 + 2)*(x^2 + 3)");
    assert(context.expand(recursively_factored) == three_quadratic_factors);
    assert(!context.is_polynomial(one / x));
    assert(!context.is_polynomial(sin(y) * x));
    assert(context.is_polynomial(sin(y) * x, {x}));
    assert(context.is_polynomial(x / y, {x}));
    assert(!context.is_polynomial(context.power(x, y), {x}));
    assert(context.is_polynomial(sqrt(context.integer(2))));
    assert(context.exact_solve(x - context.integer(2), {x}).to_string() == "{2}");
    assert(context.exact_solve(context.power(x, context.integer(2)) -
                               context.integer(4), {x}).to_string() == "{-2, 2}");
    assert(context.exact_solve(context.power(x, context.integer(2)) +
                               context.integer(2) * x + one,
                               {x}).to_string() == "{-1}");
    assert(context.exact_solve(context.power(x, context.integer(2)) + one,
                               {x}).to_string() == "{-i, i}");
    exact_expr imaginary = context.i();
    assert(context.power(imaginary, context.integer(2)).to_string() == "-1");
    assert(context.power(imaginary, context.integer(-1)).to_string() == "-i");
    assert(context.simplify(context.power(
        context.square_root(imaginary * imaginary), context.integer(2)))
        .to_string() == "-1");
    exact_expr exact_log_i = context.natural_logarithm(imaginary);
    assert(exact_log_i.to_string() == "1/2*i*pi");
    assert(context.exponential(exact_log_i + exact_log_i).to_string() == "-1");
    assert(context.exponential(exact_log_i + context.natural_logarithm(
        context.power(imaginary, context.integer(4)))).to_string() == "i");
    assert(context.exponential(context.rational(
        precq_t(precn_t(1), precn_t(2))) * imaginary * context.pi())
        .to_string() == "i");
    Number approximate_complex_one(1);
    approximate_complex_one.set_precision(256);
    exact_expr approximate_i = context.multiply({imaginary,
        context.value(exact_value(std::move(approximate_complex_one)))});
    exact_expr log_i = context.natural_logarithm(approximate_i);
    assert(log_i.to_string().find("ln") == std::string::npos);
    assert(log_i.to_string().find("i") != std::string::npos);
    exact_complex exact_z(context.integer(2), context.integer(3));
    assert(imaginary.to_string() == "i");
    assert(exact_z.expression().to_string() == "3*i + 2");
    assert((exact_z * conjugate(exact_z)).expression().to_string() == "13");
    exact_expr cubic_roots = context.exact_solve(
        context.power(x, context.integer(3)) - one, {x});
    assert(cubic_roots.operand_count() == 3);
    assert(cubic_roots.operand(0).to_string() == "1");
    assert(context.exact_solve(context.power(x, context.integer(3)), {x})
               .to_string() == "{0}");
    exact_expr quartic_roots = context.exact_solve(
        context.power(x, context.integer(4)) - one, {x});
    assert(quartic_roots.operand_count() == 4);
    assert(quartic_roots.to_string() == "{1, -1, -i, i}");
    exact_expr rounded_quartic_roots = context.solve(
        context.power(x, context.integer(4)) + x + context.integer(1), {x});
    assert(rounded_quartic_roots.operand_count() == 4);
    for(size_t root = 0; root < rounded_quartic_roots.operand_count(); ++root)
        assert(rounded_quartic_roots.operand(root).to_string().find("x") ==
               std::string::npos);
    exact_expr exact_irrational_roots = context.exact_solve(
        context.power(x, context.integer(2)) - context.integer(2), {x});
    assert(exact_irrational_roots.to_string() == "{-sqrt(2), sqrt(2)}");
    exact_expr approximate_roots = context.solve(
        context.power(x, context.integer(2)) - context.integer(2), {x}, 256);
    assert(approximate_roots.to_string().find("sqrt") == std::string::npos);
    exact_expr coefficient_a = context.symbol("a");
    exact_expr coefficient_b = context.symbol("b");
    assert(context.solve(coefficient_a * x + coefficient_b, {x}).to_string() ==
           "{-b/a}");
    assert(context.exact_solve(coefficient_a * x + coefficient_b, {x}).to_string() ==
           "{-b/a}");
    assert(context.exact_solve(polynomial_xy, {x}).to_string() == "{-y}");
    assert(context.exact_solve(x / context.integer(2) - one, {x}).to_string() ==
           "{2}");
    assert(context.exact_solve(
        {context.power(x, context.integer(2)) +
         context.power(y, context.integer(2)) - one}, {x}).to_string() ==
        "{{x -> -sqrt(-y^2 + 1)}, {x -> sqrt(-y^2 + 1)}}");

    exact_expr system_y = context.symbol("system_y");
    assert(context.exact_solve(
        {x + system_y - context.integer(3),
         x - system_y - context.integer(1)}, {x, system_y}).to_string() ==
        "{{x -> 2, system_y -> 1}}");
    assert(context.exact_solve(
        {x + system_y - context.integer(3),
         x * system_y - context.integer(2)}, {x, system_y}).to_string() ==
        "{{x -> 1, system_y -> 2}, {x -> 2, system_y -> 1}}");
    assert(context.exact_solve(
        {x + system_y, x + system_y - context.integer(1)},
        {x, system_y}).to_string() == "{}");
    exact_expr system_z = context.symbol("system_z");
    assert(context.exact_solve(
        {x + system_y + system_z - context.integer(6),
         x - system_y, system_y - system_z},
        {x, system_y, system_z}).to_string() ==
        "{{x -> 2, system_y -> 2, system_z -> 2}}");
    assert(context.exact_solve(
        {context.power(x, context.integer(2)) - context.integer(1),
         system_y - x}, {x, system_y}).to_string() ==
        "{{x -> -1, system_y -> -1}, {x -> 1, system_y -> 1}}");
    exact_expr reducible_system = context.exact_solve(
        {context.power(x, context.integer(2)) +
             context.power(system_y, context.integer(2)) - context.integer(5),
         context.power(x, context.integer(2)) + x - context.integer(1) - system_y},
        {x, system_y});
    assert(reducible_system.to_string().find(
        "{x -> 2^(1/3), system_y -> 2^(1/3) + 2^(2/3) - 1}") !=
        std::string::npos);

    exact_expr parametric = context.exact_solve({x + system_y}, {x, system_y});
    assert(parametric.to_string() ==
           "{{x -> _solve_t1, system_y -> -_solve_t1}}");
    assert(context.simplify(parametric).to_string() == parametric.to_string());
    exact_expr parameter = context.symbol("_solve_t1");
    assert(context.substitute(parametric, parameter, context.integer(3)).to_string() ==
           "{{x -> 3, system_y -> -3}}");
    assert(context.substitute(parametric, x, context.integer(9)).to_string() ==
           parametric.to_string());
    assert(context.debug_dump().find("rule") != std::string::npos);

    exact_expr occupied_parameter = context.symbol("_solve_t1");
    exact_expr collision_safe = context.exact_solve(
        {x + occupied_parameter}, {x, occupied_parameter});
    assert(collision_safe.to_string().find("_solve_t2") != std::string::npos);
    Number approximate_system_constant(2.0);
    approximate_system_constant.set_precision(256);
    exact_expr approximate_system = context.solve(
        {x + system_y - context.value(exact_value(approximate_system_constant)),
         x - system_y}, {x, system_y}, 256);
    assert(approximate_system.to_string() ==
           "{{x -> 1, system_y -> 1}}");
    exact_expr numeric_trig = context.solve(
        {context.sine(x), system_y - x}, {x, system_y}, 128);
    assert(numeric_trig.to_string().find("x -> 0") != std::string::npos);
    for(size_t i = 0; i < numeric_trig.operand_count(); ++i)
        assert(numeric_trig.operand(i).to_string().find("sqrt") ==
               std::string::npos);
    exact_context compact_context;
    exact_expr compact_x = compact_context.symbol("x");
    exact_expr compact_y = compact_context.symbol("y");
    exact_expr compact_solution = compact_context.exact_solve(
        {compact_x + compact_y}, {compact_x, compact_y});
    std::string compact_text = compact_solution.to_string();
    assert(compact_context.compact(compact_solution).to_string() == compact_text);
    Number approximate_coefficient(0.5);
    approximate_coefficient.set_precision(256);
    bool approximate_exact_solve = false;
    try{
        (void)context.exact_solve(
            context.value(exact_value(std::move(approximate_coefficient))) * x - one,
            {x});
    }catch(const std::invalid_argument &){ approximate_exact_solve = true; }
    assert(approximate_exact_solve);
    exact_expr symbolic_solution = context.solve(
        coefficient_a * x + coefficient_b, {x});
    assert(context.substitute(symbolic_solution, coefficient_a, one).to_string() ==
           "{-b}");
    bool infinite_solutions = false;
    try{
        (void)context.solve(context.integer(0), {x});
    }catch(const std::domain_error &){ infinite_solutions = true; }
    assert(infinite_solutions);
    exact_expr numeric_sine = context.solve(sin(x), {x}, 128);
    assert(numeric_sine.operand_count() > 0);
    assert(numeric_sine.to_string().find("sqrt") == std::string::npos);
    assert(exp(x).to_string() == "exp(x)");
    assert(ln(exp(x)) == x);
    assert(exp(ln(x)) == x);
    assert(exp(ln(x) + ln(y)) == x * y);
    exact_expr logarithm_remainder = context.symbol("z");
    assert(exp(ln(x) + ln(y) + logarithm_remainder) ==
           x * y * exp(logarithm_remainder));
    assert(sin(x + y).to_string() == "sin(x + y)");
    exact_expr sine_x = sin(x);
    exact_expr cosine_x = cos(x);
    exact_expr sine_square = context.power(sine_x, context.integer(2));
    exact_expr cosine_square = context.power(cosine_x, context.integer(2));
    assert(context.simplify(sine_square + cosine_square) == one);
    assert(context.simplify(
        context.power(sine_x, context.integer(4)) -
        context.power(cosine_x, context.integer(4))) ==
        sine_square - cosine_square);
    assert(context.simplify(context.integer(3) * sine_square +
                            context.integer(3) * cosine_square) == three);
    exact_expr double_x = context.integer(2) * x;
    assert(context.simplify(context.integer(2) * sine_x * cosine_x) ==
           sin(double_x));
    assert(context.simplify(sine_x * cosine_x) == sine_x * cosine_x);
    assert(context.trig_expand(sin(double_x)) ==
           context.integer(2) * sine_x * cosine_x);
    exact_expr triple_x = context.integer(3) * x;
    assert(context.trig_expand(sin(triple_x)) ==
           context.integer(3) * sine_x -
           context.integer(4) * context.power(sine_x, context.integer(3)));
    assert(context.trig_expand(cos(triple_x)) ==
           context.integer(4) * context.power(cosine_x, context.integer(3)) -
           context.integer(3) * cosine_x);
    assert(context.trig_expand(sin(x + y)) ==
           sin(x) * cos(y) + cos(x) * sin(y));
    exact_expr half = context.rational(
        precq_t(precn_t(1), precn_t(2)));
    assert(context.trig_reduce(sine_x * cosine_x) == half * sin(double_x));
    assert(context.trig_reduce(sine_square) ==
           half - half * cos(double_x));
    assert(context.trig_reduce(cosine_square) ==
           half + half * cos(double_x));
    assert(context.trig_reduce(sine_square + cosine_square) == one);
    assert(cos(context.integer(0)) == context.integer(1));
    assert(tan(context.integer(0)) == context.integer(0));
    assert(sinh(x).to_string() == "sinh(x)");
    assert(cosh(x).to_string() == "cosh(x)");
    assert(tanh(x).to_string() == "tanh(x)");
    assert(asin(x).to_string() == "asin(x)");
    assert(acos(x).to_string() == "acos(x)");
    assert(atan(x).to_string() == "atan(x)");
    assert(asinh(x).to_string() == "asinh(x)");
    assert(acosh(x).to_string() == "acosh(x)");
    assert(atanh(x).to_string() == "atanh(x)");
    assert(Si(x).to_string() == "Si(x)");
    assert(Ci(x).to_string() == "Ci(x)");
    assert(Ei(x).to_string() == "Ei(x)");
    assert(erf(x).to_string() == "erf(x)");
    assert(erfi(x).to_string() == "erfi(x)");
    assert(partial_gamma(x, y).to_string() == "partial_gamma(x, y)");
    exact_expr polynomial_for_diff = context.power(x, context.integer(3)) +
                                     context.integer(2) * x;
    assert(context.differentiate(polynomial_for_diff, x) ==
           context.integer(3) * context.power(x, context.integer(2)) +
           context.integer(2));
    exact_expr elementary_integrand = context.exponential(context.integer(3) * x) +
                                       context.sine(context.integer(2) * x) +
                                       context.power(x, context.integer(4));
    exact_expr elementary_antiderivative =
        context.integrate(elementary_integrand, x);
    assert(context.simplify(context.differentiate(
               elementary_antiderivative, x) - elementary_integrand) ==
           context.integer(0));
    exact_expr special_integrand = context.sine_integral(x) +
                                   context.cosine_integral(x) +
                                   context.exponential_integral(x) +
                                   context.error_function(x);
    exact_expr special_antiderivative = context.integrate(special_integrand, x);
    assert(context.simplify(context.differentiate(
               special_antiderivative, x) - special_integrand) ==
           context.integer(0));
    assert(context.integrate(context.sine(context.power(x, context.integer(2))), x)
               .operation() == exact_opcode::integral);
    assert(context.integrate(context.exponential(
               context.power(x, context.integer(2))), x) ==
           context.square_root(context.pi()) * erfi(x) / context.integer(2));
    assert(context.integrate(context.exponential(
               -context.power(x, context.integer(2))), x) ==
           context.square_root(context.pi()) * erf(x) / context.integer(2));
    exact_expr positive_quadratic = context.power(x, context.integer(2)) *
        context.exponential(context.power(x, context.integer(2)));
    exact_expr negative_quadratic = context.power(x, context.integer(4)) *
        context.exponential(-context.power(x, context.integer(2)));
    exact_expr shifted_positive_quadratic = context.power(x, context.integer(2)) *
        context.exponential(context.integer(3) * context.power(x, context.integer(2)) +
                            context.integer(2) * x + context.integer(5));
    exact_expr shifted_negative_quadratic = context.power(x, context.integer(3)) *
        context.exponential(-context.integer(2) * context.power(x, context.integer(2)) +
                            context.integer(3) * x - context.integer(4));
    assert(context.simplify(context.differentiate(
               context.integrate(positive_quadratic, x), x) -
               positive_quadratic) == context.integer(0));
    assert(context.simplify(context.differentiate(
               context.integrate(negative_quadratic, x), x) -
               negative_quadratic) == context.integer(0));
    exact_expr shifted_positive_result = context.integrate(
        shifted_positive_quadratic, x);
    exact_expr shifted_positive_expected =
        (x / context.integer(6) - context.integer(1) / context.integer(18)) *
            context.exponential(context.integer(3) * context.power(x, context.integer(2)) +
                                context.integer(2) * x + context.integer(5)) -
        context.exponential(context.integer(14) / context.integer(3)) *
            context.square_root(context.pi()) *
            erfi(context.square_root(context.integer(3)) *
                 (x + context.integer(1) / context.integer(3))) /
            (context.integer(36) * context.square_root(context.integer(3)));
    assert(shifted_positive_result == shifted_positive_expected);
    assert(context.integrate(shifted_negative_quadratic, x).operation() !=
           exact_opcode::integral);
    exact_expr trig_inner = context.integer(3) * x + context.integer(2);
    exact_expr sine_polynomial = context.power(x, context.integer(5)) *
        context.sine(trig_inner);
    exact_expr cosine_polynomial = context.power(x, context.integer(4)) *
        context.cosine(trig_inner);
    exact_expr sinh_polynomial = context.power(x, context.integer(3)) *
        context.hyperbolic_sine(trig_inner);
    exact_expr cosh_polynomial = context.power(x, context.integer(2)) *
        context.hyperbolic_cosine(trig_inner);
    assert(context.simplify(context.differentiate(
               context.integrate(sine_polynomial, x), x) -
               sine_polynomial) == context.integer(0));
    assert(context.simplify(context.differentiate(
               context.integrate(cosine_polynomial, x), x) -
               cosine_polynomial) == context.integer(0));
    assert(context.simplify(context.differentiate(
               context.integrate(sinh_polynomial, x), x) -
               sinh_polynomial) == context.integer(0));
    assert(context.simplify(context.differentiate(
               context.integrate(cosh_polynomial, x), x) -
               cosh_polynomial) == context.integer(0));
    assert(context.integrate(context.sine(x) / x, x) ==
           context.sine_integral(x));
    assert(context.integrate(context.cosine(x) / x, x) ==
           context.cosine_integral(x));
    assert(context.integrate(context.exponential(x) / x, x) ==
           context.exponential_integral(x));
    exact_expr shifted_ei_integrand = context.exponential(x) /
        (x + context.integer(1));
    assert(context.integrate(shifted_ei_integrand, x) ==
           context.exponential(context.integer(-1)) *
           context.exponential_integral(x + context.integer(1)));
    exact_expr shifted_si_integrand = context.sine(x) /
        (x + context.integer(1));
    exact_expr shifted_si_expected =
        context.cosine(context.integer(-1)) *
            context.sine_integral(x + context.integer(1)) +
        context.sine(context.integer(-1)) *
            context.cosine_integral(x + context.integer(1));
    assert(context.integrate(shifted_si_integrand, x) == shifted_si_expected);
    exact_expr quadratic_inner = context.power(x, context.integer(2));
    exact_expr sine_log_kernel = context.integer(2) * x *
        context.sine(quadratic_inner) / quadratic_inner;
    exact_expr cosine_log_kernel = context.integer(2) * x *
        context.cosine(quadratic_inner) / quadratic_inner;
    exact_expr exponential_log_kernel = context.integer(2) * x *
        context.exponential(quadratic_inner) / quadratic_inner;
    assert(context.integrate(sine_log_kernel, x) ==
           context.sine_integral(quadratic_inner));
    assert(context.integrate(cosine_log_kernel, x) ==
           context.cosine_integral(quadratic_inner));
    assert(context.integrate(exponential_log_kernel, x) ==
           context.exponential_integral(quadratic_inner));
    exact_expr exponential_generator = context.exponential(
        context.integer(2) * x + context.integer(1));
    exact_expr exponential_rational = context.integer(2) *
        exponential_generator / (context.integer(1) + exponential_generator);
    assert(context.integrate(exponential_rational, x) ==
           context.natural_logarithm(context.absolute_value(
               context.integer(1) + exponential_generator)));
    exact_expr pi_exponential_generator = context.exponential(context.pi() * x);
    exact_expr pi_exponential_rational = pi_exponential_generator /
        (context.integer(1) + pi_exponential_generator);
    assert(context.integrate(pi_exponential_rational, x) ==
           context.natural_logarithm(context.absolute_value(
               context.integer(1) + pi_exponential_generator)) / context.pi());
    exact_expr tangent_generator = context.tangent(
        context.integer(2) * x + context.integer(1));
    exact_expr tangent_rational = context.integer(2) /
        (context.integer(1) + tangent_generator);
    exact_expr hyperbolic_tangent_generator = context.hyperbolic_tangent(
        context.integer(3) * x - context.integer(1));
    exact_expr hyperbolic_tangent_rational = context.integer(3) /
        (context.integer(2) + hyperbolic_tangent_generator);
    assert(context.integrate(tangent_rational, x).operation() !=
           exact_opcode::integral);
    assert(context.integrate(hyperbolic_tangent_rational, x).operation() !=
           exact_opcode::integral);
    exact_expr circular_inner = context.integer(2) * x;
    exact_expr weierstrass_rational = context.integer(1) /
        (context.integer(1) + context.sine(circular_inner));
    exact_expr weierstrass_mixed = context.cosine(circular_inner) /
        (context.integer(2) + context.sine(circular_inner));
    assert(context.integrate(weierstrass_rational, x).operation() !=
           exact_opcode::integral);
    assert(context.integrate(weierstrass_mixed, x).operation() !=
           exact_opcode::integral);
    exact_expr hyperbolic_inner = context.integer(2) * x;
    exact_expr hyperbolic_weierstrass_rational = context.integer(1) /
        (context.integer(1) + context.hyperbolic_sine(hyperbolic_inner));
    exact_expr hyperbolic_weierstrass_mixed =
        context.hyperbolic_cosine(hyperbolic_inner) /
        (context.integer(2) + context.hyperbolic_sine(hyperbolic_inner));
    assert(context.integrate(hyperbolic_weierstrass_rational, x).operation() !=
           exact_opcode::integral);
    assert(context.integrate(hyperbolic_weierstrass_mixed, x).operation() !=
           exact_opcode::integral);
    exact_expr chain_sine = context.integer(2) * x *
        context.sine(quadratic_inner);
    exact_expr chain_logarithm = context.integer(2) * x *
        context.natural_logarithm(quadratic_inner);
    exact_expr chain_erfi = context.integer(2) * x * erfi(quadratic_inner);
    assert(context.simplify(context.differentiate(
               context.integrate(chain_sine, x), x) - chain_sine) ==
           context.integer(0));
    assert(context.simplify(context.differentiate(
               context.integrate(chain_logarithm, x), x) - chain_logarithm) ==
           context.integer(0));
    assert(context.simplify(context.differentiate(
               context.integrate(chain_erfi, x), x) - chain_erfi) ==
           context.integer(0));
    exact_expr logarithmic_integral = context.integrate(context.integer(1) /
        context.natural_logarithm(x), x);
    assert(logarithmic_integral ==
           context.exponential_integral(context.natural_logarithm(x)));
    assert(logarithmic_integral.to_string() == "Ei(ln(x))");
    exact_expr rational_integrand = context.integer(1) /
        (context.integer(1) + context.power(x, context.integer(2)));
    assert(context.integrate(rational_integrand, x) == context.arc_tangent(x));
    exact_expr inverse_sqrt_positive = context.integer(1) /
        context.square_root(context.power(x, context.integer(2)) + context.integer(1));
    exact_expr inverse_sqrt_negative = context.integer(1) /
        context.square_root(context.integer(1) - context.power(x, context.integer(2)));
    assert(context.integrate(inverse_sqrt_positive, x) ==
           context.inverse_hyperbolic_sine(x));
    assert(context.integrate(inverse_sqrt_negative, x) == context.arc_sine(x));
    exact_expr root_polynomial_linear = x /
        context.square_root(context.power(x, context.integer(2)) + context.integer(1));
    exact_expr root_polynomial_quadratic = context.power(x, context.integer(2)) /
        context.square_root(context.power(x, context.integer(2)) + context.integer(1));
    assert(context.integrate(root_polynomial_linear, x) ==
           context.square_root(context.power(x, context.integer(2)) + context.integer(1)));
    assert(context.integrate(root_polynomial_quadratic, x).operation() !=
           exact_opcode::integral);
    exact_expr cubic_rational_integrand = context.integer(1) /
        (context.power(x, context.integer(3)) + context.integer(1));
    exact_expr cubic_rational_antiderivative =
        context.integrate(cubic_rational_integrand, x);
    exact_expr integration_root_three = context.square_root(context.integer(3));
    exact_expr expected_cubic_antiderivative =
        context.natural_logarithm(context.absolute_value(x + context.integer(1))) /
            context.integer(3) -
        context.natural_logarithm(context.absolute_value(
            context.power(x, context.integer(2)) - x + context.integer(1))) /
            context.integer(6) +
        context.arc_tangent((context.integer(2) * x - context.integer(1)) /
                            integration_root_three) /
            integration_root_three;
    assert(cubic_rational_antiderivative == expected_cubic_antiderivative);
    exact_expr quartic_rational = context.integer(1) /
        (context.power(x, context.integer(4)) - context.integer(1));
    assert(context.integrate(quartic_rational, x).operation() !=
           exact_opcode::integral);
    exact_expr mixed_rational = context.integer(1) /
        (context.power(x, context.integer(3)) + x);
    assert(context.integrate(mixed_rational, x).operation() !=
           exact_opcode::integral);
    exact_expr general_quadratic = context.integer(1) /
        (context.power(x, context.integer(2)) + context.integer(2) * x +
         context.integer(2));
    assert(context.integrate(general_quadratic, x).operation() !=
           exact_opcode::integral);
    exact_expr rational_numerator = (context.integer(2) * x +
        context.integer(3)) /
        (context.power(x, context.integer(2)) + x + context.integer(1));
    assert(context.integrate(rational_numerator, x).operation() !=
           exact_opcode::integral);
    exact_expr improper_rational =
        (context.power(x, context.integer(4)) + context.integer(2) * x +
         context.integer(1)) /
        (context.power(x, context.integer(2)) + context.integer(1));
    assert(context.integrate(improper_rational, x).operation() !=
           exact_opcode::integral);
    exact_expr repeated_linear = context.integer(1) /
        context.power(x + context.integer(1), context.integer(3));
    assert(context.integrate(repeated_linear, x) ==
           -context.integer(1) /
           (context.integer(2) *
            context.power(x + context.integer(1), context.integer(2))));
    exact_expr repeated_quadratic = (context.integer(3) * x +
        context.integer(2)) /
        context.power(context.power(x, context.integer(2)) + context.integer(1),
                      context.integer(2));
    assert(context.integrate(repeated_quadratic, x).operation() !=
           exact_opcode::integral);
    exact_expr exponential_kernel = context.integer(2) * x *
        context.exponential(context.power(x, context.integer(2)));
    assert(context.integrate(exponential_kernel, x) ==
           context.exponential(context.power(x, context.integer(2))));
    assert(context.integrate(x * context.exponential(x), x) ==
           x * context.exponential(x) - context.exponential(x));
    assert(context.integrate(context.power(x, context.integer(2)) *
                             context.exponential(x), x) ==
           context.power(x, context.integer(2)) * context.exponential(x) -
           context.integer(2) * x * context.exponential(x) +
           context.integer(2) * context.exponential(x));
    exact_expr e_power = context.power(context.e(), x);
    exact_expr e_polynomial = context.power(x, context.integer(5)) +
        context.integer(3) * context.power(x, context.integer(2)) -
        context.integer(7);
    exact_expr e_integrand = e_polynomial * e_power;
    exact_expr e_antiderivative = context.integrate(e_integrand, x);
    assert(e_antiderivative.operation() != exact_opcode::integral);
    assert(context.simplify(context.differentiate(e_antiderivative, x) -
                           e_integrand) == context.integer(0));
    exact_expr logarithmic_derivative = context.cosine(x) / context.sine(x);
    assert(context.integrate(logarithmic_derivative, x) ==
           context.natural_logarithm(
               context.absolute_value(context.sine(x))));
    exact_expr logarithm_power = context.power(
        context.natural_logarithm(x), context.integer(3)) / x;
    assert(context.integrate(logarithm_power, x) ==
           context.power(context.natural_logarithm(x), context.integer(4)) /
           context.integer(4));
    exact_expr logarithmic_tower = x * context.power(
        context.natural_logarithm(x), context.integer(3));
    exact_expr logarithmic_quadratic_tower = x * context.power(
        context.natural_logarithm(context.power(x, context.integer(2)) +
                                  context.integer(1)), context.integer(2));
    assert(context.simplify(context.differentiate(
               context.integrate(logarithmic_tower, x), x) -
               logarithmic_tower) == context.integer(0));
    assert(context.integrate(logarithmic_quadratic_tower, x).operation() !=
           exact_opcode::integral);
    exact_expr atan_polynomial = x * context.arc_tangent(x);
    exact_expr si_polynomial = x * context.sine_integral(x);
    exact_expr erfi_polynomial = x * erfi(x);
    assert(context.integrate(atan_polynomial, x).operation() !=
           exact_opcode::integral);
    assert(context.integrate(si_polynomial, x).operation() !=
           exact_opcode::integral);
    assert(context.integrate(erfi_polynomial, x).operation() !=
           exact_opcode::integral);
    exact_expr log_quadratic = context.natural_logarithm(
        context.power(x, context.integer(2)) + context.integer(1));
    exact_expr expected_log_quadratic = x * log_quadratic -
        context.integer(2) * x + context.integer(2) * context.arc_tangent(x);
    assert(context.integrate(log_quadratic, x) ==
           context.simplify(expected_log_quadratic));
    exact_expr x_log_x = x * context.natural_logarithm(x);
    exact_expr expected_x_log_x =
        context.power(x, context.integer(2)) * context.natural_logarithm(x) /
            context.integer(2) -
        context.power(x, context.integer(2)) / context.integer(4);
    assert(context.integrate(x_log_x, x) == context.simplify(expected_x_log_x));
    exact_expr polynomial_logarithm = x * log_quadratic;
    assert(context.integrate(polynomial_logarithm, x).operation() !=
           exact_opcode::integral);
    assert(context.integrate(
               context.natural_logarithm(context.sine(x)), x).operation() ==
           exact_opcode::integral);
    exact_expr constant_base_power = context.power(context.integer(2), x);
    exact_expr constant_base_antiderivative =
        context.integrate(constant_base_power, x);
    assert(context.simplify(context.differentiate(
               constant_base_antiderivative, x) - constant_base_power) ==
           context.integer(0));
    exact_expr linear_exponent_power = context.power(
        context.integer(2), context.integer(3) * x + context.integer(1));
    exact_expr linear_exponent_antiderivative =
        context.integrate(linear_exponent_power, x);
    assert(context.simplify(context.differentiate(
               linear_exponent_antiderivative, x) - linear_exponent_power) ==
           context.integer(0));
    assert(context.integrate(context.power(x, x), x).operation() ==
           exact_opcode::integral);
    exact_expr logarithm_antiderivative =
        context.integrate(context.natural_logarithm(x), x);
    assert(context.simplify(context.differentiate(logarithm_antiderivative, x) -
                            context.natural_logarithm(x)) == context.integer(0));
    assert(sin(asin(x)) == x);
    assert(cos(acos(x)) == x);
    assert(tan(atan(x)) == x);
    assert(cos(asin(x)) == sqrt(one - context.power(x, context.integer(2))));
    assert(sin(atan(x)) == x /
           sqrt(one + context.power(x, context.integer(2))));
    assert(cosh(asinh(x)) ==
           sqrt(one + context.power(x, context.integer(2))));
    assert(tanh(atanh(x)) == x);
    assert(ln(x).to_string() == "ln(x)");
    assert(log2(x).to_string() == "log2(x)");
    assert(log10(x).to_string() == "log10(x)");
    assert(asin(context.integer(0)) == context.integer(0));
    assert(atanh(context.integer(0)) == context.integer(0));
    assert(ln(one) == context.integer(0));
    assert(log2(one) == context.integer(0));
    assert(log10(one) == context.integer(0));
    assert(acosh(one) == context.integer(0));
    assert(context.add({x, y}) == context.add({y, x}));
    assert(context.multiply({x, y}) == context.multiply({y, x}));
    exact_expr shared_debug = context.add({context.multiply({x, y}),
                                           context.power(x, two_a)});
    assert(shared_debug.reachable_node_count() == 6);
    assert(shared_debug.depth() == 3);
    assert(shared_debug.operand(0).valid());
    assert(shared_debug.debug_tree().find("#" + std::to_string(x.id())) !=
           std::string::npos);
    assert(std::string(exact_opcode_name(shared_debug.operation())) == "add");
    std::string arena_dump = context.debug_dump();
    assert(arena_dump.find("arena:") == 0);
    assert(arena_dump.find("children={") != std::string::npos);
    assert(context.debug_dump(1).find("nodes omitted") != std::string::npos);
    assert(context.add({x, x}) == context.multiply({context.integer(2), x}));
    assert(context.multiply({x, x, x}) == context.power(x, context.integer(3)));
    assert(x - x == context.integer(0));
    assert(x - context.multiply({context.integer(2), x}) == -x);
    assert(x / x == context.integer(1));
    assert(context.divide(context.multiply({context.integer(2), x}),
                          context.multiply({context.integer(4), x})) ==
           context.rational(precq_t(precn_t(1), precn_t(2))));
    assert(context.power(x, context.integer(2)) /
           context.power(x, context.integer(3)) ==
           context.power(x, context.integer(-1)));
    exact_expr cancellable = context.divide(
        context.add({context.power(x, context.integer(2)), x}),
        context.add({x, one}));
    assert(context.simplify(cancellable) == x);
    exact_expr common_symbol = context.divide(
        context.add({context.multiply({x, y}), context.multiply({x, three})}),
        context.add({y, three}));
    assert(context.simplify(common_symbol) == x);
    exact_expr y_squared = context.power(y, context.integer(2));
    exact_expr difference_of_squares_fraction = context.divide(
        context.subtract(context.power(x, context.integer(2)), y_squared),
        context.subtract(x, y));
    assert(context.simplify(difference_of_squares_fraction) ==
           context.add({x, y}));
    assert(context.simplify(difference_of_squares_fraction).to_string() ==
           "x + y");
    exact_expr multivariate_division = context.divide(
        context.add({context.power(x, context.integer(2)),
                     context.multiply({x, y}), x, y}),
        context.add({x, y}));
    assert(context.simplify(multivariate_division) == context.add({x, one}));
    exact_expr z = context.symbol("z");
    exact_expr hidden_left = context.add({
        context.power(x, context.integer(2)), context.multiply({x, y}),
        context.multiply({x, z}), context.multiply({y, z})});
    exact_expr hidden_right = context.add({
        context.multiply({x, y}), context.multiply({x, z}),
        context.power(y, context.integer(2)), context.multiply({y, z})});
    assert(context.simplify(context.divide(hidden_left, hidden_right)) ==
           context.divide(context.add({x, z}), context.add({y, z})));
    exact_expr univariate_gcd_numerator = context.add({
        context.power(x, context.integer(4)),
        context.power(x, context.integer(3)),
        context.multiply({context.integer(3), context.power(x, context.integer(2))}),
        context.multiply({context.integer(2), x}), context.integer(2)});
    exact_expr univariate_gcd_denominator = context.add({
        context.power(x, context.integer(3)),
        context.multiply({context.integer(4), context.power(x, context.integer(2))}),
        context.multiply({context.integer(4), x}), context.integer(3)});
    assert(context.simplify(context.divide(univariate_gcd_numerator,
                                           univariate_gcd_denominator)) ==
           context.divide(context.add({context.power(x, context.integer(2)),
                                       context.integer(2)}),
                          context.add({x, context.integer(3)})));
    exact_expr square_sum = context.add({
        context.power(x, context.integer(2)),
        context.multiply({context.integer(2), x, y}),
        context.power(y, context.integer(2))});
    assert(context.simplify(context.divide(
        square_sum, context.subtract(context.power(x, context.integer(2)),
                                     context.power(y, context.integer(2))))) ==
        context.divide(context.add({x, y}), context.subtract(x, y)));
    exact_expr difference_of_cubes = context.divide(
        context.subtract(context.power(x, context.integer(3)), one),
        context.subtract(x, one));
    assert(context.simplify(difference_of_cubes) == context.add({
        context.power(x, context.integer(2)), x, one}));
    assert(context.simplify(difference_of_cubes).to_string() == "x^2 + x + 1");
    exact_expr uncancelled_rational = context.divide(
        context.add({context.power(x, context.integer(1145)), x, one}),
        context.multiply({x, y}));
    assert(context.simplify(uncancelled_rational) == uncancelled_rational);
    assert(context.simplify(uncancelled_rational).to_string() ==
           "(x^1145 + x + 1)/(x*y)");
    assert(context.divide(x, y).to_string() == "x/y");
    assert(context.power(y, context.integer(-1)).to_string() == "1/y");
    exact_expr rational_root_two = sqrt(two_a);
    exact_expr root_three = sqrt(three);
    exact_expr rationalized_radicals = context.simplify(context.divide(
        one, context.add({rational_root_two, root_three})));
    assert(rationalized_radicals ==
           context.subtract(root_three, rational_root_two));
    exact_expr rationalized_one = context.simplify(context.divide(
        one, context.add({one, rational_root_two})));
    assert(rationalized_one == context.subtract(rational_root_two, one));
    exact_expr root_five = sqrt(context.integer(5));
    exact_expr rationalized_three = context.simplify(context.divide(
        one, context.add({rational_root_two, root_three, root_five})));
    exact_expr check_three = context.expand(context.multiply({
        rationalized_three,
        context.add({rational_root_two, root_three, root_five})}));
    assert(check_three == one);
    exact_expr root_seven = sqrt(context.integer(7));
    exact_expr four_root_denominator = context.add({
        rational_root_two, root_three, root_five, root_seven});
    exact_expr rationalized_four = context.simplify(
        context.divide(one, four_root_denominator));
    assert(context.expand(context.multiply({
        rationalized_four, four_root_denominator})) == one);
    Number approximate_eleven(11.0);
    exact_expr approximate_root_eleven = context.square_root(
        context.value(exact_value(std::move(approximate_eleven))));
    exact_expr approximate_denominator = context.add({
        rational_root_two, root_three, approximate_root_eleven});
    assert(approximate_denominator.is_value());
    assert(approximate_denominator.value().is_approximate());
    exact_expr approximate_reciprocal = context.divide(one,
                                                        approximate_denominator);
    assert(approximate_reciprocal.is_value());
    assert(approximate_reciprocal.value().is_approximate());
    exact_expr approximate_result = context.simplify(approximate_reciprocal);
    assert(approximate_result.is_value());
    assert(approximate_result.value().is_approximate());
    exact_expr signed_polynomial = context.add({
        context.power(x, context.integer(5)),
        context.multiply({context.integer(-1),
                          context.power(x, context.integer(3))}),
        one});
    assert(signed_polynomial.to_string() == "x^5 - x^3 + 1");
    assert(exact_value(7) - exact_value(10) == exact_value(-3));
    assert(exact_value(3) / exact_value(4) ==
           exact_value(precq_t(precn_t(3), precn_t(4))));
    assert(sqrt(context.integer(144)) == context.integer(12));
    assert(sqrt(context.rational(precq_t(precn_t(1), precn_t(6)))) ==
           context.rational(precq_t(precn_t(1), precn_t(6))) *
               sqrt(context.integer(6)));
    assert(abs(context.integer(-144)) == context.integer(144));
    assert(abs(context.i()) == context.integer(1));
    assert(abs(context.integer(3) + context.integer(4) * context.i()) ==
           context.integer(5));
    assert(abs(x).to_string() == "abs(x)");
    assert(abs(-x).to_string() == "abs(x)");
    assert(abs(abs(x)) == abs(x));
    exact_expr real_symbol = context.symbol("real_symbol");
    context.assume(real_symbol, "real");
    assert(sqrt(context.power(real_symbol, context.integer(2))).to_string() ==
           "abs(real_symbol)");
    exact_expr nonnegative_symbol = context.symbol("nonnegative_symbol");
    context.assume(nonnegative_symbol, "nonnegative");
    assert(sqrt(context.power(nonnegative_symbol, context.integer(2))) ==
           nonnegative_symbol);
    assert(abs(nonnegative_symbol) == nonnegative_symbol);
    exact_expr positive_solution_variable = context.symbol("positive_solution_x");
    context.assume(positive_solution_variable, "positive");
    assert(context.solve(context.power(positive_solution_variable,
                                      context.integer(2)) + context.integer(1),
                         {positive_solution_variable}).to_string() == "{}");
    assert(context.solve(context.power(positive_solution_variable,
                                      context.integer(2)) - context.integer(1),
                         {positive_solution_variable}).to_string() == "{1}");
    context.assume(positive_solution_variable, "none");
    assert(sqrt(context.power(positive_solution_variable,
                              context.integer(2))).to_string() ==
           "sqrt(positive_solution_x^2)");
    assert(context.solve(context.power(positive_solution_variable,
                                      context.integer(2)) - context.integer(1),
                         {positive_solution_variable}).to_string() == "{-1, 1}");

    exact_expr compact = context.power(
        context.add({one, sqrt(two_a), sqrt(three)}), context.integer(123));
    assert(compact.operation() == exact_opcode::power);
    assert(compact.operand_count() == 2);
    assert(compact.to_string().find("^123") != std::string::npos);

    exact_expr root_two = sqrt(two_a);
    exact_expr one_half = context.rational(
        precq_t(precn_t(1), precn_t(2)));
    assert(context.power(two_a, one_half) == root_two);
    assert(context.power(two_a, context.rational(
        precq_t(precn_t(1), precn_t(2), true))) ==
        context.divide(one, root_two));
    assert(context.power(x, context.rational(
        precq_t(precn_t(1), precn_t(3)))).to_string() == "x^(1/3)");
    exact_expr two_thirds = context.rational(
        precq_t(precn_t(2), precn_t(3)));
    exact_expr three_halves = context.rational(
        precq_t(precn_t(3), precn_t(2)));
    exact_expr branch_sensitive_power = context.power(
        context.power(x, two_thirds), three_halves);
    assert(branch_sensitive_power.operation() == exact_opcode::power);
    assert(branch_sensitive_power.operand(0).operation() == exact_opcode::power);
    assert(context.power(context.power(x, two_thirds), context.integer(3)) ==
           context.power(x, context.integer(2)));
    exact_expr cube_root_two = context.power(two_a, context.rational(
        precq_t(precn_t(1), precn_t(3))));
    assert(context.divide(one, cube_root_two).to_string() == "2^(-1/3)");
    exact_expr rationalized_cube_root = context.simplify(context.divide(
        one, context.add({one, cube_root_two})));
    assert(context.expand(context.multiply({
        rationalized_cube_root, context.add({one, cube_root_two})})) == one);
    exact_expr cube_root_three = context.power(three, context.rational(
        precq_t(precn_t(1), precn_t(3))));
    exact_expr two_cube_root_denominator = context.add({
        one, cube_root_two, cube_root_three});
    exact_expr rationalized_two_cube_roots = context.simplify(
        context.divide(one, two_cube_root_denominator));
    assert(context.expand(context.multiply({
        rationalized_two_cube_roots, two_cube_root_denominator})) == one);
    exact_expr mixed_root_denominator = context.add({
        one, rational_root_two, cube_root_three});
    exact_expr rationalized_mixed_roots = context.simplify(
        context.divide(one, mixed_root_denominator));
    assert(context.expand(context.multiply({
        rationalized_mixed_roots, mixed_root_denominator})) == one);
    exact_expr expanded_square = context.expand(
        context.power(context.add({one, root_two}), context.integer(2)));
    exact_expr expected_square = context.add({
        context.integer(3), context.multiply({context.integer(2), root_two})});
    assert(expanded_square == expected_square);
    exact_expr expanded_monomial = context.expand(context.power(
        context.multiply({context.integer(9), x}), context.integer(10)));
    assert(expanded_monomial == context.multiply({
        context.integer(UINT64_C(3486784401)),
        context.power(x, context.integer(10))}));
    assert(context.power(context.divide(context.integer(9), x),
                         context.integer(10)).to_string() ==
           "3486784401/x^10");
    exact_expr a_symbol = context.symbol("a");
    exact_expr b_symbol = context.symbol("b");
    exact_expr scaled_difference = context.subtract(
        context.multiply({context.integer(25), context.power(
            a_symbol, context.integer(2))}),
        context.power(context.multiply({context.integer(4), b_symbol}),
                      context.integer(2)));
    exact_expr five_a = context.multiply({context.integer(5), a_symbol});
    exact_expr four_b = context.multiply({context.integer(4), b_symbol});
    assert(context.factor(scaled_difference) == context.multiply({
        context.subtract(five_a, four_b), context.add({five_a, four_b})}));
    exact_expr three_a = context.multiply({context.integer(3), a_symbol});
    exact_expr two_times_b = context.multiply({context.integer(2), b_symbol});
    exact_expr scaled_cube_difference = context.subtract(
        context.multiply({context.integer(27), context.power(
            a_symbol, context.integer(3))}),
        context.multiply({context.integer(8), context.power(
            b_symbol, context.integer(3))}));
    exact_expr cube_quotient = context.add({
        context.power(three_a, context.integer(2)),
        context.multiply({three_a, two_times_b}),
        context.power(two_times_b, context.integer(2))});
    assert(context.factor(scaled_cube_difference) == context.multiply({
        context.subtract(three_a, two_times_b), cube_quotient}));
    exact_expr scaled_fifth_difference = context.subtract(
        context.multiply({context.integer(243), context.power(
            a_symbol, context.integer(5))}),
        context.multiply({context.integer(32), context.power(
            b_symbol, context.integer(5))}));
    exact_expr factored_fifth = context.factor(scaled_fifth_difference);
    assert(factored_fifth.operation() == exact_opcode::multiply);
    assert(context.expand(factored_fifth) == scaled_fifth_difference);
    exact_expr simplified_radicals = context.simplify(context.power(
        context.add({one, root_two, sqrt(three)}), context.integer(2)));
    exact_expr expected_radicals = context.add({
        context.integer(6),
        context.multiply({context.integer(2), root_two}),
        context.multiply({context.integer(2), sqrt(three)}),
        context.multiply({context.integer(2), sqrt(context.integer(6))})});
    assert(simplified_radicals == expected_radicals);
    assert(context.multiply({root_two, root_two, root_two}) ==
           context.multiply({context.integer(2), root_two}));
    assert(sqrt(context.integer(72)) ==
           context.multiply({context.integer(6), root_two}));
    exact_expr simplified_tenth = context.simplify(context.power(
        context.add({one, root_two, sqrt(three)}), context.integer(10)));
    exact_expr expected_tenth = context.add({
        context.integer(375936),
        context.multiply({context.integer(265088), root_two}),
        context.multiply({context.integer(216448), sqrt(three)}),
        context.multiply({context.integer(153472), sqrt(context.integer(6))})});
    assert(simplified_tenth == expected_tenth);
    size_t before_large_simplify = context.node_count();
    exact_expr simplified_compact = context.simplify(compact);
    assert(simplified_compact.operation() == exact_opcode::add);
    assert(simplified_compact.operand_count() == 4);
    assert(context.node_count() - before_large_simplify < 1000);

    std::vector<exact_expr> eight_radicals = {
        one, sqrt(two_a), sqrt(three), sqrt(context.integer(5)),
        sqrt(context.integer(6)), sqrt(context.integer(7)),
        sqrt(context.integer(10)), sqrt(context.integer(11))};
    exact_expr eighth_base_power = context.power(
        context.add(eight_radicals), context.integer(12));
    exact_expr expanded_eighth = context.expand(eighth_base_power);
    exact_expr simplified_eighth = context.simplify(eighth_base_power);
    assert(simplified_eighth == expanded_eighth);
    assert(simplified_eighth.operation() == exact_opcode::add);
    assert(simplified_eighth.operand_count() == 32);
    exact_expr difference_of_squares = context.expand(
        context.multiply({context.add({x, one}), context.subtract(x, one)}));
    assert(difference_of_squares == context.subtract(
        context.power(x, context.integer(2)), one));
    bool expansion_limited = false;
    try{
        context.expand(context.power(context.add({x, y, one}),
                                     context.integer(20)), 10);
    }catch(const std::length_error &){
        expansion_limited = true;
    }
    assert(expansion_limited);

    size_t before_radicals = context.node_count();
    std::vector<exact_expr> radicals;
    radicals.reserve(1000);
    for(uint64_t i = 1; i <= 1000; ++i)
        radicals.push_back(sqrt(context.integer(i)));
    exact_expr radical_square = context.power(context.add(radicals), context.integer(2));
    assert(radical_square.operation() == exact_opcode::power);
    assert(context.node_count() - before_radicals < 3000);

    exact_context bulk_context;
    exact_add_builder builder = bulk_context.make_add_builder();
    for(uint64_t i = 1; i <= 10000000; ++i) builder.add_integer(i);
    exact_expr bulk_total = builder.finish();
    assert(bulk_total.value() == exact_value(UINT64_C(50000005000000)));
    assert(bulk_context.node_count() == 1);
    assert(bulk_context.operand_id_count() == 0);

    exact_context sum_context;
    exact_expr i = sum_context.symbol("i");
    exact_expr ten_million_sum = sum_context.bounded_sum(
        i, sum_context.integer(1), sum_context.integer(10000000), i);
    assert(ten_million_sum.is_value());
    assert(ten_million_sum.value() == exact_value(UINT64_C(50000005000000)));
    assert(sum_context.node_count() == 4);

    exact_expr symbolic_sum = sum_context.bounded_sum(
        i, sum_context.integer(1), sum_context.symbol("n"),
        sum_context.power(i, sum_context.integer(2)));
    assert(symbolic_sum.operation() == exact_opcode::bounded_sum);
    assert(symbolic_sum.operand_count() == 4);

    exact_context gc_context;
    exact_expr gc_x = gc_context.symbol("x");
    exact_expr gc_kept = gc_context.add({gc_x, gc_context.integer(1)});
    for(uint64_t value = 2; value < 5000; ++value){
        exact_expr discarded = gc_context.add({gc_x, gc_context.integer(value)});
        assert(discarded.valid());
    }
    size_t nodes_before_gc = gc_context.node_count();
    std::string kept_before_gc = gc_kept.to_string();
    exact_expr old_kept = gc_kept;
    std::vector<exact_expr> compacted = gc_context.compact({gc_x, gc_kept});
    gc_x = std::move(compacted[0]);
    gc_kept = std::move(compacted[1]);
    assert(gc_context.node_count() < nodes_before_gc / 100);
    assert(gc_kept.to_string() == kept_before_gc);
    assert(old_kept.to_string() == kept_before_gc);
    assert(gc_context.add({gc_kept, gc_x}).valid());

    puts("cas ok");
    return 0;
}
