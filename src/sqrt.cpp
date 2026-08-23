#include"../prec.hpp"

#ifndef PRECN_SQRT_USE_MULINV_DIV
#define PRECN_SQRT_USE_MULINV_DIV 0
#endif

#ifndef PRECN_SQRT_TRACE
#define PRECN_SQRT_TRACE 0
#endif

#ifndef PRECN_SQRT_HIGH_DIVISOR
#define PRECN_SQRT_HIGH_DIVISOR 2
#endif

#ifndef PRECN_SQRT_RESIDUAL_STEP
#define PRECN_SQRT_RESIDUAL_STEP 1
#endif

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

static void sqrt_add_inplace(precn_t &a, const precn_t &b){
    size_t n = std::max(a.rsiz, b.rsiz);
    if(a.asiz < n + 1){
        a.a = (uint64_t*)realloc(a.a, (n + 1) * sizeof(uint64_t));
        a.asiz = n + 1;
    }
    uint64_t carry = 0;
    for(size_t i = 0; i < n; ++i){
        uint64_t av = i < a.rsiz ? a.a[i] : 0;
        uint64_t bv = i < b.rsiz ? b.a[i] : 0;
        uint64_t out;
        carry = precn_add_carry(av, bv, carry, out);
        a.a[i] = out;
    }
    a.rsiz = n;
    if(carry) a.a[a.rsiz++] = carry;
}

static void sqrt_shift_right_1_inplace(precn_t &a){
    uint64_t carry = 0;
    for(size_t i = a.rsiz; i > 0; --i){
        uint64_t cur = a.a[i - 1];
        a.a[i - 1] = (cur >> 1) | carry;
        carry = cur << 63;
    }
    while(a.rsiz && a.a[a.rsiz - 1] == 0) --a.rsiz;
    if(a.rsiz == 0) a.a[0] = 0;
}

static precn_t sqrt_refine_upper(const precn_t &a, precn_t x){
    precn_t y;
    for(;;){
#if PRECN_SQRT_TRACE
        fprintf(stderr, "sqrt division: %zu / %zu limbs\n", a.rsiz, x.rsiz);
#endif
        if(PRECN_SQRT_RESIDUAL_STEP){
            // x is an upper bound.  e has substantially fewer leading limbs
            // than a once the recursive seed is reasonably close.
            precn_t e = precn_sqr(x) - a;
            // Unsigned subtraction is zero exactly when x*x <= a.  The
            // iteration never drops below floor(sqrt(a)), so x is final.
            if(e.rsiz == 0) return x;
            precn_t den = x << 1;
            precn_t remainder;
            divmod_into(y, remainder, e, den);
            if(remainder.rsiz) y = y + precn_t(1);
            y = x - y;
        }else{
            if(PRECN_SQRT_USE_MULINV_DIV && x.rsiz >= 128) y = div_mulinv(a, x);
            else div_into(y, a, x);
            sqrt_add_inplace(y, x);
            sqrt_shift_right_1_inplace(y);
        }
        // Starting from an upper bound, integer Newton decreases until x is
        // exactly floor(sqrt(a)).  At that point floor(a/x) >= x and the
        // iteration can no longer decrease.  No full-size x*x correction is
        // needed after this condition.
        if(y >= x) return x;
        std::swap(x, y);
    }
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

    size_t drop = (a.rsiz - a.rsiz / PRECN_SQRT_HIGH_DIVISOR) & ~(size_t)1;
    if(drop == 0) return sqrt_refine_upper(a, sqrt_top_seed(a));

    precn_t high_root = precn_sqrt(sqrt_high_part(a, drop));
    precn_t upper = (high_root + 1) << (drop * 32);
    return sqrt_refine_upper(a, upper);
}
