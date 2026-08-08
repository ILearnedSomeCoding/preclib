#include"../prec_cas.hpp"

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

    Number approximate_nine(9);
    approximate_nine.set_precision(256);
    exact_expr approximate_root = sqrt(context.value(exact_value(approximate_nine)));
    assert(approximate_root.is_value());
    assert(approximate_root.value().is_approximate());
    assert(approximate_root.value().number() == Number(3));
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

    exact_expr x = context.symbol("x");
    exact_expr y = context.symbol("y");
    assert(exp(x).to_string() == "exp(x)");
    assert(sin(x + y).to_string() == "sin(x + y)");
    assert(cos(context.integer(0)) == context.integer(1));
    assert(tan(context.integer(0)) == context.integer(0));
    assert(sinh(x).to_string() == "sinh(x)");
    assert(cosh(x).to_string() == "cosh(x)");
    assert(tanh(x).to_string() == "tanh(x)");
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

    puts("cas ok");
    return 0;
}
