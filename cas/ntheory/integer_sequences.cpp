#include "integer_sequences.hpp"

#include <stdexcept>

namespace cas_ntheory{
namespace{
constexpr uint64_t maximum_index = UINT64_C(10000000);

uint64_t checked_index(const precz_t &index){
    const precn_t &magnitude = index.magnitude();
    if(magnitude.rsiz > 1 ||
       (magnitude.rsiz && magnitude.a[0] > maximum_index))
        throw std::out_of_range("integer sequence index exceeds 10000000");
    return magnitude.rsiz ? magnitude.a[0] : 0;
}

std::pair<precn_t, precn_t> fibonacci_pair(uint64_t index){
    size_t bits = 0;
    for(uint64_t n = index; n; n >>= 1) ++bits;
    precn_t f(0), next(1);
    for(size_t bit = bits; bit-- > 0;){
        precn_t twice_next = next + next;
        precn_t even = f * (twice_next - f);
        precn_t odd = f * f + next * next;
        if((index >> bit) & 1){
            f = std::move(odd);
            next = even + f;
        }else{
            f = std::move(even);
            next = std::move(odd);
        }
    }
    return {std::move(f), std::move(next)};
}
}

precz_t fibonacci(const precz_t &index){
    uint64_t n = checked_index(index);
    precn_t value = fibonacci_pair(n).first;
    if(index.is_negative() && !(n & 1))
        return precz_t::from_magnitude(std::move(value), true);
    return precz_t(std::move(value));
}

precz_t lucas_number(const precz_t &index){
    uint64_t n = checked_index(index);
    auto pair = fibonacci_pair(n);
    precn_t value = (pair.second + pair.second) - pair.first;
    if(index.is_negative() && (n & 1))
        return precz_t::from_magnitude(std::move(value), true);
    return precz_t(std::move(value));
}
}
