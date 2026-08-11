#include"../prec.hpp"

static const size_t DIVEXACT_INVERSE_THRESHOLD = 96;

static unsigned divexact_ctz64(uint64_t x){
#if defined(__clang__) || defined(__GNUC__)
    return (unsigned)__builtin_ctzll(x);
#else
    unsigned n = 0;
    while((x & 1) == 0){ x >>= 1; ++n; }
    return n;
#endif
}

static size_t divexact_trailing_bits(const precn_t &a){
    size_t limbs = 0;
    while(limbs < a.rsiz && a.a[limbs] == 0) ++limbs;
    return limbs * 64 + divexact_ctz64(a.a[limbs]);
}

static precn_t divexact_low(const precn_t &a, size_t limbs){
    precn_t r;
    size_t n = std::min(a.rsiz, limbs);
    if(n == 0) return r;
    r.asiz = std::max<size_t>(n, 1);
    r.a = (uint64_t*)realloc(r.a, r.asiz * sizeof(uint64_t));
    memcpy(r.a, a.a, n * sizeof(uint64_t));
    r.rsiz = n;
    while(r.rsiz && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}

static precn_t divexact_mul_low(const precn_t &a, const precn_t &b,
                                size_t limbs){
    return divexact_low(a * b, limbs);
}

// Return 2-a modulo B^limbs, where B=2^64.  Building the complement limb by
// limb avoids allocating the explicit B^limbs modulus at every Newton step.
static precn_t divexact_two_minus(const precn_t &a, size_t limbs){
    precn_t r;
    r.asiz = std::max<size_t>(limbs, 1);
    r.a = (uint64_t*)realloc(r.a, r.asiz * sizeof(uint64_t));
    r.rsiz = limbs;

    uint64_t borrow = 0;
    for(size_t i = 0; i < limbs; ++i){
        uint64_t av = i < a.rsiz ? a.a[i] : 0;
        borrow = precn_sub_borrow(0, av, borrow, r.a[i]);
    }
    uint64_t carry = 2;
    for(size_t i = 0; i < limbs && carry; ++i){
        uint64_t out;
        carry = precn_add_carry(r.a[i], carry, 0, out);
        r.a[i] = out;
    }
    while(r.rsiz && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}

static uint64_t divexact_inverse_limb(uint64_t odd){
    uint64_t x = 1;
    for(unsigned i = 0; i < 6; ++i) x *= 2 - odd * x;
    return x;
}

static precn_t divexact_inverse_mod(const precn_t &odd, size_t limbs){
    precn_t x(divexact_inverse_limb(odd.a[0]));
    size_t known = 1;
    while(known < limbs){
        size_t next = std::min(limbs, known * 2);
        precn_t bpart = divexact_low(odd, next);
        precn_t bx = divexact_mul_low(bpart, x, next);
        precn_t correction = divexact_two_minus(bx, next);
        x = divexact_mul_low(x, correction, next);
        known = next;
    }
    return x;
}

precn_t precn_divexact(const precn_t &a, const precn_t &b){
    if(a.rsiz == 0) return precn_t();
    if(b.rsiz == 0) std::abort();
    if(a < b) std::abort();

    size_t raw_quotient_limbs = a.rsiz - b.rsiz + 1;
    if(raw_quotient_limbs < DIVEXACT_INVERSE_THRESHOLD ||
       raw_quotient_limbs < b.rsiz * 2)
        return a / b;

    size_t trailing = divexact_trailing_bits(b);
    precn_t numerator = trailing ? a >> trailing : a;
    precn_t odd = trailing ? b >> trailing : b;
    if(odd.rsiz == 1 && odd.a[0] == 1) return numerator;

    size_t quotient_limbs = numerator.rsiz - odd.rsiz + 1;
    // Full products followed by truncation are not competitive for balanced
    // operands.  Until mul_low has a native FFT/NTT kernel, use the inverse
    // path only when ordinary division would scan a much longer quotient.
    // For odd b, q = a*b^-1 (mod B^k).  The exact quotient occupies at most
    // k limbs, so this residue is the ordinary integer quotient itself.
    precn_t inverse = divexact_inverse_mod(odd, quotient_limbs);
    return divexact_mul_low(numerator, inverse, quotient_limbs);
}

precz_t precz_divexact(const precz_t &a, const precz_t &b){
    if(b.is_zero()) std::abort();
    precz_t q(precn_divexact(a.magnitude(), b.magnitude()));
    return a.is_negative() != b.is_negative() ? -q : q;
}
