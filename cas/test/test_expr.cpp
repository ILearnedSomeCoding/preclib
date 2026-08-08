#include"../prec_cas.hpp"

#include<cassert>
#include<cstdio>
#include<string>

int main(){
    expr_context context(256);
    expr half = context.floating(0.5);
    expr quarter = context.floating(0.25);
    assert((half + quarter).is_approximate());
    assert((half + quarter).number() == Number(0.75));

    expr x = context.symbol("x");
    expr y = context.symbol("y");
    expr mixed = x + half;
    assert(!mixed.is_number());
    assert(mixed.to_string().find("x") != std::string::npos);

    expr two = context.integer(2);
    expr fraction = (pow(x, two) - pow(y, two)) / (x - y);
    assert(context.simplify(fraction) == x + y);

    Number two_number(2);
    two_number.set_precision(256);
    expr root = sqrt(context.number(std::move(two_number)));
    assert(root.is_approximate());
    Number tolerance = Number::from_raw(precz_t(1), 2, 240);
    assert(abs(root.number() * root.number() - Number(2)) < tolerance);

    expr exponential = exp(context.floating(1.0));
    assert(exponential.is_approximate());
    assert(sin(x).to_string() == "sin(x)");
    assert(cosh(x + y).to_string() == "cosh(x + y)");

    puts("expr ok");
    return 0;
}
