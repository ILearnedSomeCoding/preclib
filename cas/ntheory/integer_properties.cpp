#include "integer_properties.hpp"

namespace cas_ntheory{

static size_t natural_bit_length(const precn_t &value){
    if(!value.rsiz) return 0;
    uint64_t top = value.a[value.rsiz - 1];
    size_t bits = (value.rsiz - 1) * 64;
    while(top){ ++bits; top >>= 1; }
    return bits;
}

bool split_small_square_factor_u64(uint64_t remaining,
                                          uint64_t &outside,
                                          uint64_t &inside){
    // Trial division is excellent for the small radicands produced by normal
    // symbolic expansion, but must not turn sqrt(huge_prime) into a long job.
    if(remaining > UINT64_C(1000000000000)) return false;
    if(!remaining){ outside = 0; inside = 1; return true; }
    outside = 1;
    inside = 1;
    for(uint64_t prime = 2; prime <= remaining / prime;
        prime = prime == 2 ? 3 : prime + 2){
        if(remaining % prime) continue;
        unsigned count = 0;
        do{
            remaining /= prime;
            ++count;
        }while(remaining % prime == 0);
        for(unsigned i = 0; i < count / 2; ++i) outside *= prime;
        if(count & 1) inside *= prime;
    }
    if(remaining > 1) inside *= remaining;
    return true;
}

bool perfect_cube_root(const precn_t &value, precn_t &root){
    if(value.rsiz == 0){ root = precn_t(); return true; }
    size_t bits = natural_bit_length(value);
    precn_t x = precn_t(1) << ((bits + 2) / 3);
    for(;;){
        precn_t square = x * x;
        precn_t y = div_u64(mul_u64(x, 2) + value / square, 3);
        if(y >= x) break;
        x = std::move(y);
    }
    if(x * x * x != value) return false;
    root = std::move(x);
    return true;
}

static int compare_power(const precn_t &base, uint64_t exponent,
                         const precn_t &limit){
    precn_t result(1), factor(base);
    while(exponent){
        if(exponent & 1){
            result = result * factor;
            if(result > limit) return 1;
        }
        exponent >>= 1;
        if(exponent){
            factor = factor * factor;
            if(factor > limit) factor = limit + precn_t(1);
        }
    }
    if(result < limit) return -1;
    return result == limit ? 0 : 1;
}

bool perfect_nth_root(const precn_t &value, uint64_t degree,
                             precn_t &root){
    if(degree < 2) return false;
    if(value.rsiz == 0){ root = precn_t(); return true; }
    size_t bits = natural_bit_length(value);
    if(degree >= bits){
        if(value == precn_t(1)){ root = precn_t(1); return true; }
        return false;
    }
    size_t root_bits = (bits + (size_t)degree - 1) / (size_t)degree;
    precn_t low(1), high = precn_t(1) << root_bits;
    while(low <= high){
        precn_t middle = (low + high) >> 1;
        int comparison = compare_power(middle, degree, value);
        if(comparison == 0){ root = std::move(middle); return true; }
        if(comparison < 0) low = middle + precn_t(1);
        else{
            if(middle.rsiz == 0) break;
            high = middle - precn_t(1);
        }
    }
    return false;
}

uint64_t smallest_prime_factor(uint64_t value){
    if(value < 2 || value > UINT64_C(1000000000000)) return 0;
    if((value & 1) == 0) return 2;
    for(uint64_t divisor = 3; divisor <= value / divisor; divisor += 2)
        if(value % divisor == 0) return divisor;
    return value;
}

} // namespace cas_ntheory
