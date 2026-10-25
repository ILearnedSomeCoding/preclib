#include "../ntheory/multiplicative_functions.hpp"

#include <cassert>
#include <stdexcept>

using namespace cas_ntheory;

int main(){
    assert(euler_phi(precz_t(36)) == precz_t(12));
    assert(euler_phi(precz_t(-1)) == precz_t(1));
    assert(euler_phi(precz_t(1)) == precz_t(1));

    assert(mobius_mu(precz_t(1)) == 1);
    assert(mobius_mu(precz_t(30)) == -1);
    assert(mobius_mu(precz_t(-30)) == -1);
    assert(mobius_mu(precz_t(12)) == 0);
    assert(mobius_mu(precz_t(0)) == 0);

    assert(divisor_sigma(0, precz_t(12)) == precz_t(6));
    assert(divisor_sigma(1, precz_t(12)) == precz_t(28));
    assert(divisor_sigma(2, precz_t(12)) == precz_t(210));
    assert(divisor_count(precz_t(360)) == precz_t(24));
    assert(radical(precz_t(360)) == precz_t(30));
    assert(radical(precz_t(-1)) == precz_t(1));
    assert(aliquot_sum(precz_t(12)) == precz_t(16));
    assert(liouville_lambda(precz_t(8)) == -1);
    assert(liouville_lambda(precz_t(12)) == -1);
    assert(carmichael_lambda(precz_t(1)) == precz_t(1));
    assert(carmichael_lambda(precz_t(8)) == precz_t(2));
    assert(carmichael_lambda(precz_t(15)) == precz_t(4));
    assert(carmichael_lambda(precz_t(360)) == precz_t(12));
    bool sigma_limit_failed = false;
    try{ (void)divisor_sigma(1000001, precz_t(12)); }
    catch(const std::out_of_range &){ sigma_limit_failed = true; }
    assert(sigma_limit_failed);
    assert(prime_nu(precz_t(12)) == 2);
    assert(prime_omega(precz_t(12)) == 3);

    assert(square_free_q(precz_t(30)));
    assert(!square_free_q(precz_t(12)));
    assert(!square_free_q(precz_t(0)));
    assert(prime_power_q(precz_t(8)));
    assert(!prime_power_q(precz_t(12)));
    assert(!prime_power_q(precz_t(-8)));

    std::vector<precz_t> expected = {
        precz_t(1), precz_t(2), precz_t(3),
        precz_t(4), precz_t(6), precz_t(12)};
    assert(divisors(precz_t(12)) == expected);
    assert(divisors(precz_t(-1)) == std::vector<precz_t>{precz_t(1)});
    bool limit_failed = false;
    try{ (void)divisors(precz_t(360), 4); }
    catch(const std::length_error &){ limit_failed = true; }
    assert(limit_failed);
    return 0;
}
