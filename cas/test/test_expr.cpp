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

    expr pi_constant = context.pi();
    expr e_constant = context.e();
    assert(pi_constant.is_approximate());
    assert(e_constant.is_approximate());
    assert(abs(sin(pi_constant).number()) <
           Number::from_raw(precz_t(1), 2, 220));
    assert(abs(ln(e_constant).number() - Number(1)) <
           Number::from_raw(precz_t(1), 2, 220));

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
    assert(partial_gamma(x, y).to_string() == "partial_gamma(x, y)");
    Number precise_one(1);
    precise_one.set_precision(256);
    expr approximate_one = context.number(std::move(precise_one));
    assert(Si(approximate_one).is_approximate());
    assert(erf(approximate_one).is_approximate());
    Number negative_one(-1);
    negative_one.set_precision(256);
    assert(abs(partial_gamma(approximate_one, approximate_one).number() -
               exp(negative_one)) < tolerance);
    assert(diff(pow(x, context.integer(3)), x).to_string() == "3*x^2");
    expr expr_integrand = exp(context.integer(2) * x) + cos(x);
    expr expr_antiderivative = integrate(expr_integrand, x);
    assert(context.simplify(diff(expr_antiderivative, x) - expr_integrand) ==
           context.integer(0));
    assert(ln(x).to_string() == "ln(x)");
    assert(log2(x).to_string() == "log2(x)");
    assert(log10(x).to_string() == "log10(x)");

    expr half_angle = asin(half);
    assert(half_angle.is_approximate());
    assert(abs(sin(half_angle).number() - Number(0.5)) < tolerance);
    assert(abs(tanh(atanh(half)).number() - Number(0.5)) < tolerance);
    expr two_log = context.number(Number(2));
    assert(abs(log2(two_log).number() - Number(1)) < tolerance);

    puts("expr ok");
    return 0;
}
