#include "../ntheory/integer_arithmetic.hpp"
#include "../ntheory/integer_sequences.hpp"

#include <cassert>
#include <stdexcept>

using cas_ntheory::fibonacci;
using cas_ntheory::legendre_symbol;
using cas_ntheory::lucas_number;
using cas_ntheory::multiplicative_order;

int main(){
    assert(fibonacci(precz_t(0)) == precz_t(0));
    assert(fibonacci(precz_t(1)) == precz_t(1));
    assert(fibonacci(precz_t(100)) == precz_t("354224848179261915075"));
    assert(fibonacci(precz_t(-8)) == precz_t(-21));
    assert(lucas_number(precz_t(0)) == precz_t(2));
    assert(lucas_number(precz_t(10)) == precz_t(123));
    assert(lucas_number(precz_t(-5)) == precz_t(-11));

    assert(legendre_symbol(precz_t(2), precz_t(7)) == 1);
    assert(legendre_symbol(precz_t(3), precz_t(7)) == -1);
    assert(legendre_symbol(precz_t(14), precz_t(7)) == 0);
    bool rejected_composite = false;
    try{ (void)legendre_symbol(precz_t(2), precz_t(9)); }
    catch(const std::domain_error &){ rejected_composite = true; }
    assert(rejected_composite);

    assert(multiplicative_order(precz_t(2), precz_t(7)) == precz_t(3));
    assert(multiplicative_order(precz_t(3), precz_t(10)) == precz_t(4));
    assert(multiplicative_order(precz_t(2), precz_t(9)) == precz_t(6));
    bool rejected_nonunit = false;
    try{ (void)multiplicative_order(precz_t(6), precz_t(15)); }
    catch(const std::domain_error &){ rejected_nonunit = true; }
    assert(rejected_nonunit);
    return 0;
}
