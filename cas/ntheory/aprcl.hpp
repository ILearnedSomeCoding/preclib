#ifndef PREC_CAS_APRCL_HPP
#define PREC_CAS_APRCL_HPP

#include"../../prec.hpp"
#include<string>

enum class cas_primality_status{ composite, prime, unknown };

struct cas_aprcl_options{
    uint32_t maximum_t = 73513440;
    uint32_t maximum_prime_power = 64;
    uint32_t trial_division_bound = 1000;
    uint32_t additional_prime_limit = 100000;
    unsigned additional_trials = 50;
    bool probable_prime_filter = true;
};

struct cas_aprcl_result{
    cas_primality_status status = cas_primality_status::unknown;
    precn_t factor;
    std::string reason;
    uint32_t t = 0;
    size_t jacobi_tests = 0;
    size_t additional_tests = 0;
    size_t final_divisors = 0;
};

// A prime result requires the complete proof, including final trial division.
// Exhausting a table or witness-search budget returns unknown, never prime.
cas_aprcl_result cas_aprcl(const precn_t &n,
    const cas_aprcl_options &options = cas_aprcl_options());

#endif
