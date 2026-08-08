#include"../prec_num.hpp"

#include<cassert>
#include<cmath>
#include<cstdio>
#include<string>

static void expect(const Number &a, size_t digits, const char *value){
    assert(a.to_string(digits) == std::string(value));
}

int main(){
    expect(Number(3) + Number(2), 0, "5");
    expect(Number(3) - Number(5), 0, "-2");
    expect(Number(-7) * Number(-6), 0, "42");
    expect(Number(3) / Number(2), 12, "1.5");

    Number half = Number::from_raw(precz_t(precn_t(1) << 63), 1, 128);
    expect(half, 12, "0.5");
    assert(half == Number(1) / Number(2));
    assert((half << 1) == Number(1));
    assert((Number(8) >> 2) == Number(2));

    Number from_double(0.5);
    expect(from_double, 12, "0.5");
    assert(!from_double.is_exact());
    assert(from_double.precision() == 53);

    Number low = Number::from_raw(precz_t(3), 0, 80);
    Number high = Number::from_raw(precz_t(5), 0, 200);
    Number product = low * high;
    assert(product.precision() <= 80 && product.precision() > 79);

    Number two(2);
    two.set_precision(256);
    Number root = sqrt(two);
    std::string root_text = root.to_string(60);
    assert(root_text.substr(0, 52) ==
           "1.41421356237309504880168872420969807856967187537694");
    assert(root.precision() == 256);
    assert(root > Number(1) && root < Number(2));

    Number eleven = sqrt(Number(121));
    assert(eleven.is_exact());
    assert(eleven == Number(11));

    Number quarter = Number::from_raw(precz_t(precn_t(1) << 62), 1,
                                      Number::exact_precision());
    Number exact_half = sqrt(quarter);
    assert(exact_half.is_exact());
    assert(exact_half == half);

    Number pi50 = getpi(50);
    assert(pi50.to_string(50) ==
           "3.1415926535897932384626433832795028841971693993751");
    assert(getpi(50) == pi50);
    std::string pi1000 = getpi(1000).to_string(1000);
    assert(pi1000.size() == 1002);
    assert(pi1000.compare(0, 52,
           "3.14159265358979323846264338327950288419716939937510") == 0);
    assert(pi1000.compare(pi1000.size() - 32, 32,
                         "66130019278766111959092164201989") == 0);

    Number e50 = gete(50);
    assert(e50.to_string(50) ==
           "2.71828182845904523536028747135266249775724709369995");
    assert(gete(50) == e50);

    Number one(1);
    one.set_precision(256);
    assert(exp(one).to_string(60) ==
           "2.718281828459045235360287471352662497757247093699959574966967");
    Number tiny = Number(1) >> 200;
    tiny.set_precision(256);
    Number tolerance = Number::from_raw(precz_t(1), 2, 256);
    assert(abs(expm1(tiny) / tiny - Number(1)) < tolerance);

    Number two_for_log(2);
    two_for_log.set_precision(256);
    assert(ln(two_for_log).to_string(60) ==
           "0.69314718055994530941723212145817656807550013436025525412068");
    Number round_trip = ln(exp(two_for_log));
    assert(abs(round_trip - two_for_log) < tolerance);
    Number inverse_check = exp(one) * exp(-one);
    assert(abs(inverse_check - Number(1)) < tolerance);
    Number half_for_log = half;
    half_for_log.set_precision(128);
    Number log_tolerance = Number::from_raw(precz_t(1), 1, 128);
    assert(abs(ln(half_for_log) + ln(two_for_log)) < log_tolerance);

    Number eight(8);
    eight.set_precision(256);
    assert(abs(log2(eight) - Number(3)) < tolerance);
    Number thousand(1000);
    thousand.set_precision(256);
    assert(abs(log10(thousand) - Number(3)) < tolerance);
    assert(pow(Number(2), Number(10)) == Number(1024));
    assert(pow(Number(-2), Number(31)) == Number(-2147483648LL));
    expect(pow(Number(2), Number(-3)), 12, "0.125");
    Number one_third_numerator(1), one_third_denominator(3);
    one_third_numerator.set_precision(256);
    one_third_denominator.set_precision(256);
    Number fractional_power = pow(eight,
                                  one_third_numerator / one_third_denominator);
    assert(abs(fractional_power - Number(2)) < tolerance);
    assert(pow(Number(0), half).is_zero());

    Number pi_for_trig = getpi(90);
    pi_for_trig.set_precision(256);
    Number six(6), three(3), four(4);
    six.set_precision(256);
    three.set_precision(256);
    four.set_precision(256);
    Number angle_sixth = pi_for_trig / six;
    Number angle_third = pi_for_trig / three;
    Number angle_quarter = pi_for_trig / four;
    assert(abs(sin(angle_sixth) - half) < tolerance);
    assert(abs(cos(angle_third) - half) < tolerance);
    assert(abs(tan(angle_quarter) - Number(1)) < tolerance);
    assert(abs(sin(-angle_sixth) + half) < tolerance);
    Number arbitrary_angle = Number(7) / three;
    Number identity = sin(arbitrary_angle) * sin(arbitrary_angle) +
                      cos(arbitrary_angle) * cos(arbitrary_angle);
    assert(abs(identity - Number(1)) < tolerance);
    assert(abs(asin(half) - angle_sixth) < tolerance);
    assert(abs(acos(half) - angle_third) < tolerance);
    assert(abs(atan(Number(1)) - angle_quarter) < tolerance);
    Number quarter_value = Number(1) / four;
    assert(abs(sin(asin(quarter_value)) - quarter_value) < tolerance);
    assert(abs(cos(acos(quarter_value)) - quarter_value) < tolerance);
    assert(abs(tan(atan(arbitrary_angle)) - arbitrary_angle) < tolerance);
    assert(asin(Number(0)).is_zero());
    assert(acos(Number(1)).is_zero());

    Number log_two = ln(two_for_log);
    assert(abs(expm1(log_two) - Number(1)) < tolerance);
    assert(abs(ln(Number(1) + expm1(tiny)) - tiny) < tolerance);
    Number three_quarters = Number(3) / four;
    Number five_quarters = Number(5) / four;
    Number three_value(3), five_value(5);
    three_value.set_precision(256);
    five_value.set_precision(256);
    Number three_fifths = three_value / five_value;
    assert(abs(sinh(log_two) - three_quarters) < tolerance);
    assert(abs(cosh(log_two) - five_quarters) < tolerance);
    assert(abs(tanh(log_two) - three_fifths) < tolerance);
    Number hyperbolic_identity = cosh(one) * cosh(one) - sinh(one) * sinh(one);
    assert(abs(hyperbolic_identity - Number(1)) < tolerance);
    assert(abs(asinh(sinh(one)) - one) < tolerance);
    assert(abs(acosh(cosh(one)) - one) < tolerance);
    Number precise_half = one / two_for_log;
    assert(abs(atanh(tanh(precise_half)) - precise_half) < tolerance);
    Number large_hyperbolic(100);
    large_hyperbolic.set_precision(256);
    assert(tanh(large_hyperbolic) > Number(0));
    assert(tanh(large_hyperbolic) < Number(1));
    assert(sinh(Number(0)).is_zero());
    assert(cosh(Number(0)) == Number(1));
    assert(tanh(Number(0)).is_zero());

    assert(Number(-3) < Number(-2));
    assert(Number(-1).to_integer() == precz_t(-1));
    assert((Number::from_raw(precz_t(3), 1, 128) << 64).to_integer() == precz_t(3));

    Number binary_round_numerator(99999123), binary_round_denominator(100000000);
    binary_round_numerator.set_precision(256);
    binary_round_denominator.set_precision(256);
    Number binary_round = binary_round_numerator / binary_round_denominator;
    binary_round.set_precision(4);
    assert((std::string)binary_round == "1");
    assert((std::string)(-binary_round) == "-1");

    puts("number ok");
    return 0;
}
