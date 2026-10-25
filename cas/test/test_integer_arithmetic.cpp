#include "../ntheory/integer_arithmetic.hpp"

#include <cassert>
#include <stdexcept>

using cas_ntheory::chinese_remainder;
using cas_ntheory::extended_gcd;
using cas_ntheory::jacobi_symbol;
using cas_ntheory::kronecker_symbol;
using cas_ntheory::modular_inverse;
using cas_ntheory::power_mod;

int main(){
    auto eg = extended_gcd(precz_t(-30), precz_t(21));
    assert(eg.gcd == precz_t(3));
    assert(precz_t(-30) * eg.x + precz_t(21) * eg.y == eg.gcd);
    auto eg_zero = extended_gcd(precz_t(0), precz_t(0));
    assert(eg_zero.gcd.is_zero());

    assert(modular_inverse(precz_t(-3), precz_t(11)) == precz_t(7));
    assert(power_mod(precz_t(2), precz_t(10), precz_t(1000)) == precz_t(24));
    assert(power_mod(precz_t(3), precz_t(-1), precz_t(11)) == precz_t(4));
    bool inverse_failed = false;
    try{ (void)modular_inverse(precz_t(6), precz_t(15)); }
    catch(const std::domain_error &){ inverse_failed = true; }
    assert(inverse_failed);

    assert(chinese_remainder({precz_t(2), precz_t(5)},
                             {precz_t(6), precz_t(9)}) == precz_t(14));
    assert(chinese_remainder({}, {}) == precz_t(0));
    bool crt_failed = false;
    try{ (void)chinese_remainder({precz_t(1), precz_t(2)},
                                {precz_t(4), precz_t(6)}); }
    catch(const std::domain_error &){ crt_failed = true; }
    assert(crt_failed);

    assert(jacobi_symbol(precz_t(2), precz_t(7)) == 1);
    assert(jacobi_symbol(precz_t(3), precz_t(7)) == -1);
    assert(jacobi_symbol(precz_t(-1), precz_t(7)) == -1);
    assert(jacobi_symbol(precz_t(0), precz_t(1)) == 1);
    assert(kronecker_symbol(precz_t(-1), precz_t(8)) == 1);
    assert(kronecker_symbol(precz_t(3), precz_t(8)) == -1);
    assert(kronecker_symbol(precz_t(3), precz_t(4)) == 1);
    assert(kronecker_symbol(precz_t(-1), precz_t(0)) == 1);
    assert(kronecker_symbol(precz_t(3), precz_t(0)) == 0);
    bool jacobi_failed = false;
    try{ (void)jacobi_symbol(precz_t(2), precz_t(8)); }
    catch(const std::domain_error &){ jacobi_failed = true; }
    assert(jacobi_failed);
    return 0;
}
