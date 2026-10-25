#ifndef PREC_CAS_MULTIPLICATIVE_FUNCTIONS_HPP
#define PREC_CAS_MULTIPLICATIVE_FUNCTIONS_HPP

#include "../../prec.hpp"

#include <cstddef>
#include <vector>

namespace cas_ntheory{
precz_t euler_phi(const precz_t &value);
int mobius_mu(const precz_t &value);
precz_t divisor_sigma(uint64_t power, const precz_t &value);
size_t prime_nu(const precz_t &value);
size_t prime_omega(const precz_t &value);
bool square_free_q(const precz_t &value);
bool prime_power_q(const precz_t &value);
std::vector<precz_t> divisors(const precz_t &value,
                              size_t maximum_count = 100000);
}

#endif
