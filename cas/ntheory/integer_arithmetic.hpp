#ifndef PREC_CAS_INTEGER_ARITHMETIC_HPP
#define PREC_CAS_INTEGER_ARITHMETIC_HPP

#include "../../prec.hpp"

#include <vector>

namespace cas_ntheory{
struct extended_gcd_result{
    precz_t gcd;
    precz_t x;
    precz_t y;
};

extended_gcd_result extended_gcd(const precz_t &a, const precz_t &b);
precz_t modular_inverse(const precz_t &a, const precz_t &modulus);
precz_t power_mod(precz_t base, precz_t exponent, const precz_t &modulus);
precz_t chinese_remainder(const std::vector<precz_t> &residues,
                          const std::vector<precz_t> &moduli);
int jacobi_symbol(precz_t numerator, precz_t odd_denominator);
int kronecker_symbol(precz_t numerator, precz_t denominator);
}

#endif
