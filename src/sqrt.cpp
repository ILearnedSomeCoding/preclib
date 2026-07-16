#include"../prec.hpp"

static size_t sqrt_bit_length(const precn_t &a){
    if(a.rsiz == 0) return 0;
    uint64_t top = a.a[a.rsiz - 1];
#if defined(__clang__) || defined(__GNUC__)
    return (a.rsiz - 1) * 64 + 64 - (size_t)__builtin_clzll(top);
#else
    size_t bits = (a.rsiz - 1) * 64;
    while(top){
        ++bits;
        top >>= 1;
    }
    return bits;
#endif
}

static uint64_t sqrt_top_bits(const precn_t &a, size_t bits, size_t take){
    size_t shift = bits - take;
    size_t limb = shift / 64;
    unsigned offset = (unsigned)(shift % 64);
    uint64_t top = a.a[limb] >> offset;
    if(offset && limb + 1 < a.rsiz) top |= a.a[limb + 1] << (64 - offset);
    return top;
}

static precn_t sqrt_top_seed(const precn_t &a){
    size_t bits = sqrt_bit_length(a);
    size_t take = std::min<size_t>(bits, 53);
    size_t shift = bits - take;
    uint64_t top = sqrt_top_bits(a, bits, take);
    double estimate = std::sqrt((double)top);
    if(shift & 1) estimate *= 1.4142135623730950488;

    // The extra units make the truncated leading-bit estimate an upper
    // bound.  Newton can then stay monotone and only needs a tiny correction.
    uint64_t seed = (uint64_t)estimate + 4;
    return precn_t(seed) << (shift / 2);
}

static precn_t sqrt_refine_upper(const precn_t &a, precn_t x){
    for(;;){
        precn_t y = (x + a / x) >> 1;
        if(y >= x) break;
        x = y;
    }

    precn_t square = x * x;
    while(square > a){
        x = x - 1;
        square = x * x;
    }
    for(;;){
        precn_t next = x + 1;
        precn_t next_square = next * next;
        if(next_square > a) break;
        x = next;
    }
    return x;
}

static precn_t sqrt_high_part(const precn_t &a, size_t drop){
    precn_t high;
    high.rsiz = a.rsiz - drop;
    high.asiz = high.rsiz;
    high.a = (uint64_t*) realloc(high.a, high.asiz * sizeof(uint64_t));
    memcpy(high.a, a.a + drop, high.rsiz * sizeof(uint64_t));
    return high;
}

precn_t precn_sqrt(const precn_t &a){
    if(a.rsiz == 0) return precn_t();

    // This follows the divide-and-refine shape of ilmp_sqrt_divide_: solve a
    // high-half approximation first, scale it to a guaranteed upper bound,
    // then refine.  The final Newton loop therefore has only a couple of
    // full-size divisions rather than starting every iteration at one bit.
    if(a.rsiz <= 4) return sqrt_refine_upper(a, sqrt_top_seed(a));

    size_t drop = (a.rsiz / 2) & ~(size_t)1;
    if(drop == 0) return sqrt_refine_upper(a, sqrt_top_seed(a));

    precn_t high_root = precn_sqrt(sqrt_high_part(a, drop));
    precn_t upper = (high_root + 1) << (drop * 32);
    return sqrt_refine_upper(a, upper);
}
