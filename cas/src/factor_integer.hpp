#ifndef PREC_CAS_FACTOR_INTEGER_HPP
#define PREC_CAS_FACTOR_INTEGER_HPP

#include"../../prec.hpp"

#include<vector>

bool cas_probable_prime(const precn_t &value);
precn_t cas_pollard_rho_factor(const precn_t &value,
                               size_t iteration_limit = 1000000);
precn_t cas_ecm_factor(const precn_t &value, unsigned curves = 64,
                       uint32_t stage1_bound = 10000,
                       uint32_t stage2_bound = 50000);
precn_t cas_siqs_factor(const precn_t &value, size_t polynomials = 96,
                        size_t interval = 384);
precn_t cas_qs_factor(const precn_t &value, size_t maximum_relations = 4096);
bool cas_factor_big(const precn_t &value, std::vector<precn_t> &factors);

#endif
