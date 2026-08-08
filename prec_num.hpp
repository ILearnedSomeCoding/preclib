#pragma once

#include"prec.hpp"

#include<cstddef>
#include<cstdint>
#include<string>
#include<type_traits>

class PRECLIB_API Number{
    // value = significand_ * 2^(-64 * dotp_). precision_ counts reliable
    // significant binary bits; infinity marks an exact value.
    precz_t significand_;
    int64_t dotp_;
    double precision_;

    struct raw_tag_t{};
    Number(precz_t significand, int64_t dotp, double precision, raw_tag_t);

    void normalize();
    static double combine_precision(double a, double b);

public:
    Number();
    template<class T, typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
    Number(T val) : significand_(val), dotp_(0), precision_(exact_precision()){}
    Number(const precn_t &val);
    Number(precn_t &&val);
    Number(const precz_t &val);
    Number(precz_t &&val);
    explicit Number(float val);
    explicit Number(double val);

    static double exact_precision();
    // Low-level constructor for algorithms that already have a scaled integer.
    static Number from_raw(precz_t significand, int64_t dotp,
                           double precision_bits);

    bool is_exact() const;
    bool is_zero() const;
    bool is_negative() const;
    double precision() const;
    int64_t radix_point() const;
    const precz_t &significand() const;

    void set_precision(double bits);
    precz_t to_integer() const;
    std::string to_string(size_t fractional_digits) const;
    explicit operator std::string() const;

    Number &operator+=(const Number &o);
    Number &operator-=(const Number &o);
    Number &operator*=(const Number &o);
    Number &operator/=(const Number &o);
    Number &operator<<=(int64_t bits);
    Number &operator>>=(int64_t bits);

    friend PRECLIB_API Number operator+(const Number &a, const Number &b);
    friend PRECLIB_API Number operator-(const Number &a, const Number &b);
    friend PRECLIB_API Number operator-(const Number &a);
    friend PRECLIB_API Number operator+(const Number &a);
    friend PRECLIB_API Number operator*(const Number &a, const Number &b);
    friend PRECLIB_API Number operator/(const Number &a, const Number &b);
    friend PRECLIB_API Number operator<<(const Number &a, int64_t bits);
    friend PRECLIB_API Number operator>>(const Number &a, int64_t bits);
    friend PRECLIB_API bool operator==(const Number &a, const Number &b);
    friend PRECLIB_API bool operator<(const Number &a, const Number &b);
    friend PRECLIB_API Number abs(const Number &a);
    friend PRECLIB_API Number sqrt(const Number &a);
};

PRECLIB_API Number operator+(const Number &a, const Number &b);
PRECLIB_API Number operator-(const Number &a, const Number &b);
PRECLIB_API Number operator-(const Number &a);
PRECLIB_API Number operator+(const Number &a);
PRECLIB_API Number operator*(const Number &a, const Number &b);
PRECLIB_API Number operator/(const Number &a, const Number &b);
PRECLIB_API Number operator<<(const Number &a, int64_t bits);
PRECLIB_API Number operator>>(const Number &a, int64_t bits);

PRECLIB_API bool operator==(const Number &a, const Number &b);
PRECLIB_API bool operator!=(const Number &a, const Number &b);
PRECLIB_API bool operator<(const Number &a, const Number &b);
PRECLIB_API bool operator>(const Number &a, const Number &b);
PRECLIB_API bool operator<=(const Number &a, const Number &b);
PRECLIB_API bool operator>=(const Number &a, const Number &b);

PRECLIB_API Number abs(const Number &a);
PRECLIB_API Number sqrt(const Number &a);

// Decimal-precision constants. Values up to 1000 digits use lazy caches.
PRECLIB_API Number getpi(int digits);
PRECLIB_API Number gete(int digits);

// Transcendentals use the input's stored precision. Exact nontrivial inputs
// default to 64 bits, so set_precision() first when more accuracy is needed.
PRECLIB_API Number exp(const Number &a);
// Accurate near zero, where exp(a) - 1 would lose significant bits.
PRECLIB_API Number expm1(const Number &a);
PRECLIB_API Number ln(const Number &a);
// Logarithms require positive arguments. pow supports negative bases only
// when the exponent is an integer; unsupported real-domain cases abort.
PRECLIB_API Number log10(const Number &a);
PRECLIB_API Number log2(const Number &a);
PRECLIB_API Number pow(const Number &a, const Number &b);

PRECLIB_API Number sin(const Number &a);
PRECLIB_API Number cos(const Number &a);
PRECLIB_API Number tan(const Number &a);
PRECLIB_API Number asin(const Number &a);
PRECLIB_API Number acos(const Number &a);
PRECLIB_API Number atan(const Number &a);

PRECLIB_API Number sinh(const Number &a);
PRECLIB_API Number cosh(const Number &a);
PRECLIB_API Number tanh(const Number &a);
PRECLIB_API Number asinh(const Number &a);
PRECLIB_API Number acosh(const Number &a);
PRECLIB_API Number atanh(const Number &a);
