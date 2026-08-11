#include"../../prec_num.hpp"

#include<stdexcept>
#include<utility>

Complex::Complex() : real_(0), imag_(0){}
Complex::Complex(const Number &real) : real_(real), imag_(0){}
Complex::Complex(Number &&real) : real_(std::move(real)), imag_(0){}
Complex::Complex(const Number &real, const Number &imag)
    : real_(real), imag_(imag){}
Complex::Complex(Number &&real, Number &&imag)
    : real_(std::move(real)), imag_(std::move(imag)){}

const Number &Complex::real() const{ return real_; }
const Number &Complex::imag() const{ return imag_; }
bool Complex::is_real() const{ return imag_.is_zero(); }
bool Complex::is_zero() const{ return real_.is_zero() && imag_.is_zero(); }

void Complex::set_precision(double bits){
    real_.set_precision(bits);
    imag_.set_precision(bits);
}

std::string Complex::to_string(size_t fractional_digits) const{
    if(imag_.is_zero()) return real_.to_string(fractional_digits);
    Number magnitude = ::abs(imag_);
    std::string imaginary = magnitude.to_string(fractional_digits);
    if(real_.is_zero())
        return std::string(imag_.is_negative() ? "-" : "") + imaginary + "*i";
    return real_.to_string(fractional_digits) +
           (imag_.is_negative() ? " - " : " + ") + imaginary + "*i";
}

Complex::operator std::string() const{
    if(imag_.is_zero()) return (std::string)real_;
    Number magnitude = ::abs(imag_);
    if(real_.is_zero())
        return std::string(imag_.is_negative() ? "-" : "") +
               (std::string)magnitude + "*i";
    return (std::string)real_ + (imag_.is_negative() ? " - " : " + ") +
           (std::string)magnitude + "*i";
}

Complex operator+(const Complex &a, const Complex &b){
    return Complex(a.real_ + b.real_, a.imag_ + b.imag_);
}

Complex operator-(const Complex &a, const Complex &b){
    return Complex(a.real_ - b.real_, a.imag_ - b.imag_);
}

Complex operator-(const Complex &a){ return Complex(-a.real_, -a.imag_); }

Complex operator*(const Complex &a, const Complex &b){
    return Complex(a.real_ * b.real_ - a.imag_ * b.imag_,
                   a.real_ * b.imag_ + a.imag_ * b.real_);
}

Complex operator/(const Complex &a, const Complex &b){
    Number denominator = b.real_ * b.real_ + b.imag_ * b.imag_;
    if(denominator.is_zero()) throw std::domain_error("complex division by zero");
    return Complex((a.real_ * b.real_ + a.imag_ * b.imag_) / denominator,
                   (a.imag_ * b.real_ - a.real_ * b.imag_) / denominator);
}

bool operator==(const Complex &a, const Complex &b){
    return a.real_ == b.real_ && a.imag_ == b.imag_;
}
bool operator!=(const Complex &a, const Complex &b){ return !(a == b); }

Complex conjugate(const Complex &a){ return Complex(a.real_, -a.imag_); }
Number norm(const Complex &a){ return a.real_ * a.real_ + a.imag_ * a.imag_; }
Number abs(const Complex &a){ return ::sqrt(norm(a)); }

Complex sqrt(const Complex &a){
    if(a.imag_.is_zero()){
        if(!a.real_.is_negative()) return Complex(::sqrt(a.real_), Number(0));
        return Complex(Number(0), ::sqrt(-a.real_));
    }
    Number radius = abs(a);
    Number real_square = (radius + a.real_) / Number(2);
    Number imag_square = (radius - a.real_) / Number(2);
    // Both values are nonnegative mathematically.  Roundoff in abs(a) can
    // place one a few ulps below zero near the real axis.
    if(real_square.is_negative()) real_square = Number(0);
    if(imag_square.is_negative()) imag_square = Number(0);
    Number real = ::sqrt(real_square);
    Number imag = ::sqrt(imag_square);
    if(a.imag_.is_negative()) imag = -imag;
    return Complex(std::move(real), std::move(imag));
}

Complex pow(const Complex &a, int64_t exponent){
    if(exponent == 0) return Complex(Number(1));
    bool negative = exponent < 0;
    uint64_t power = negative ? (uint64_t)0 - (uint64_t)exponent :
                                (uint64_t)exponent;
    Complex result(Number(1));
    Complex base(a);
    while(power){
        if(power & 1) result *= base;
        power >>= 1;
        if(power) base *= base;
    }
    return negative ? Complex(Number(1)) / result : result;
}

Complex exp(const Complex &a){
    Number scale = ::exp(a.real());
    return Complex(scale * ::cos(a.imag()), scale * ::sin(a.imag()));
}

Complex ln(const Complex &a){
    if(a.is_zero()) throw std::domain_error("complex logarithm of zero");
    Number angle;
    double precision = 256.0;
    if(!a.real().is_exact()) precision = std::max(precision, a.real().precision());
    if(!a.imag().is_exact()) precision = std::max(precision, a.imag().precision());
    int digits = (int)std::ceil(precision * 0.30102999566398119521) + 10;
    if(a.real().is_zero()){
        Number pi = getpi(digits);
        angle = a.imag().is_negative() ? -(pi / Number(2)) : pi / Number(2);
    }else{
        angle = ::atan(a.imag() / a.real());
        if(a.real().is_negative()){
            Number pi = getpi(digits);
            angle += a.imag().is_negative() ? -pi : pi;
        }
    }
    Number squared_radius = norm(a);
    Number real = squared_radius == Number(1)
        ? Number(0) : (::ln(squared_radius) / Number(2));
    return Complex(std::move(real), std::move(angle));
}

Complex pow(const Complex &a, const Complex &b){
    if(b.imag().is_zero()){
        precz_t integer = b.real().to_integer();
        if(Number(integer) == b.real() && integer.magnitude().rsiz <= 1){
            uint64_t magnitude = integer.magnitude().rsiz
                ? integer.magnitude().a[0] : 0;
            if(magnitude <= (uint64_t)INT64_MAX){
                int64_t exponent = (int64_t)magnitude;
                if(integer.is_negative()) exponent = -exponent;
                return ::pow(a, exponent);
            }
        }
    }
    return ::exp(b * ::ln(a));
}

Complex &Complex::operator+=(const Complex &other){ return *this = *this + other; }
Complex &Complex::operator-=(const Complex &other){ return *this = *this - other; }
Complex &Complex::operator*=(const Complex &other){ return *this = *this * other; }
Complex &Complex::operator/=(const Complex &other){ return *this = *this / other; }
