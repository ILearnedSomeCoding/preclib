#ifndef PREC_CAS_INTEGER_PROPERTIES_HPP
#define PREC_CAS_INTEGER_PROPERTIES_HPP

#include "../../prec.hpp"

namespace cas_ntheory{
// Bounded small-integer helpers return false/zero outside their trial budget.
bool split_small_square_factor_u64(uint64_t value, uint64_t &outside, uint64_t &inside);
uint64_t smallest_prime_factor(uint64_t value);
bool perfect_cube_root(const precn_t &value, precn_t &root);
bool perfect_nth_root(const precn_t &value, uint64_t degree, precn_t &root);
}

#endif
