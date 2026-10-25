#include "integer_arithmetic.hpp"

#include <stdexcept>

namespace cas_ntheory{
namespace{
precz_t positive_mod(precz_t value, const precz_t &modulus){
    value %= modulus;
    if(value.is_negative()) value += modulus;
    return value;
}

unsigned low_bits(const precz_t &value, unsigned bits){
    if(value.is_zero()) return 0;
    return (unsigned)(value.magnitude().a[0] & ((1u << bits) - 1));
}
}

extended_gcd_result extended_gcd(const precz_t &a, const precz_t &b){
    precz_t old_r = abs(a), r = abs(b);
    precz_t old_s(1), s(0), old_t(0), t(1);
    while(!r.is_zero()){
        precz_t q = old_r / r;
        precz_t next_r = old_r - q * r;
        old_r = std::move(r);
        r = std::move(next_r);
        precz_t next_s = old_s - q * s;
        old_s = std::move(s);
        s = std::move(next_s);
        precz_t next_t = old_t - q * t;
        old_t = std::move(t);
        t = std::move(next_t);
    }
    if(a.is_negative()) old_s = -old_s;
    if(b.is_negative()) old_t = -old_t;
    return {std::move(old_r), std::move(old_s), std::move(old_t)};
}

precz_t modular_inverse(const precz_t &a, const precz_t &modulus){
    if(modulus <= precz_t(0))
        throw std::domain_error("modular_inverse requires a positive modulus");
    extended_gcd_result eg = extended_gcd(a, modulus);
    if(eg.gcd != precz_t(1))
        throw std::domain_error("modular inverse does not exist");
    return positive_mod(std::move(eg.x), modulus);
}

precz_t power_mod(precz_t base, precz_t exponent, const precz_t &modulus){
    if(modulus <= precz_t(0))
        throw std::domain_error("pow_mod requires a positive modulus");
    if(modulus == precz_t(1)) return precz_t(0);
    if(exponent.is_negative()){
        base = modular_inverse(base, modulus);
        exponent = abs(exponent);
    }
    base = positive_mod(std::move(base), modulus);
    precz_t result = positive_mod(precz_t(1), modulus);
    while(!exponent.is_zero()){
        if(exponent.magnitude().a[0] & 1) result = (result * base) % modulus;
        exponent >>= 1;
        if(!exponent.is_zero()) base = (base * base) % modulus;
    }
    return result;
}

precz_t chinese_remainder(const std::vector<precz_t> &residues,
                          const std::vector<precz_t> &moduli){
    if(residues.size() != moduli.size())
        throw std::invalid_argument("chinese_remainder list sizes must match");
    precz_t value(0), combined_modulus(1);
    for(size_t i = 0; i < residues.size(); ++i){
        if(moduli[i] <= precz_t(0))
            throw std::domain_error("chinese_remainder moduli must be positive");
        precz_t next_modulus = moduli[i];
        precz_t next_residue = positive_mod(residues[i], next_modulus);
        extended_gcd_result eg = extended_gcd(combined_modulus, next_modulus);
        precz_t difference = next_residue - value;
        if(!(difference % eg.gcd).is_zero())
            throw std::domain_error("chinese_remainder system is inconsistent");
        precz_t reduced_modulus = next_modulus / eg.gcd;
        precz_t step = reduced_modulus == precz_t(1) ? precz_t(0) :
            positive_mod((difference / eg.gcd) * eg.x, reduced_modulus);
        value += combined_modulus * step;
        combined_modulus *= reduced_modulus;
        value = positive_mod(std::move(value), combined_modulus);
    }
    return value;
}

int jacobi_symbol(precz_t numerator, precz_t odd_denominator){
    if(odd_denominator <= precz_t(0) ||
       !(odd_denominator.magnitude().a[0] & 1))
        throw std::domain_error("jacobi_symbol requires a positive odd denominator");
    numerator = positive_mod(std::move(numerator), odd_denominator);
    int sign = 1;
    while(!numerator.is_zero()){
        while(!(numerator.magnitude().a[0] & 1)){
            numerator >>= 1;
            unsigned residue = low_bits(odd_denominator, 3);
            if(residue == 3 || residue == 5) sign = -sign;
        }
        std::swap(numerator, odd_denominator);
        if(low_bits(numerator, 2) == 3 && low_bits(odd_denominator, 2) == 3)
            sign = -sign;
        numerator %= odd_denominator;
    }
    return odd_denominator == precz_t(1) ? sign : 0;
}

int kronecker_symbol(precz_t numerator, precz_t denominator){
    if(denominator.is_zero())
        return abs(numerator) == precz_t(1) ? 1 : 0;
    int sign = 1;
    if(denominator.is_negative()){
        denominator = abs(denominator);
        if(numerator.is_negative()) sign = -sign;
    }
    unsigned twos = 0;
    while(!denominator.is_zero() &&
          !(denominator.magnitude().a[0] & 1)){
        denominator >>= 1;
        ++twos;
    }
    if(twos){
        if(numerator.is_zero()) return 0;
        if(!(numerator.magnitude().a[0] & 1)) return 0;
        unsigned residue = low_bits(numerator, 3);
        int symbol_two = (residue == 1 || residue == 7) ? 1 : -1;
        if((twos & 1) && symbol_two < 0) sign = -sign;
    }
    if(denominator != precz_t(1))
        sign *= jacobi_symbol(std::move(numerator), std::move(denominator));
    return sign;
}
}
