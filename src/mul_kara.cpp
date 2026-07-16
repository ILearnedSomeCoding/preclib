#include"../prec.hpp"

#define KARATSUBA_BASECASE_LIMBS 32

static precn_t kara_slice(const precn_t &a, size_t start, size_t n){
    if(start >= a.rsiz || n == 0) return precn_t();
    n = std::min(n, a.rsiz - start);

    precn_t r;
    r.asiz = std::max<size_t>(n, 1);
    r.a = (uint64_t*) realloc(r.a, r.asiz * sizeof(uint64_t));
    memcpy(r.a, a.a + start, n * sizeof(uint64_t));
    r.rsiz = n;
    while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}

static precn_t kara_shift_limbs(const precn_t &a, size_t limbs){
    if(a.rsiz == 0) return precn_t();

    precn_t r;
    r.asiz = a.rsiz + limbs;
    r.a = (uint64_t*) realloc(r.a, r.asiz * sizeof(uint64_t));
    memset(r.a, 0, limbs * sizeof(uint64_t));
    memcpy(r.a + limbs, a.a, a.rsiz * sizeof(uint64_t));
    r.rsiz = a.rsiz + limbs;
    return r;
}

static precn_t kara_mul(const precn_t &a, const precn_t &b){
    if(a.rsiz == 0 || b.rsiz == 0) return precn_t();

    size_t lo = std::min(a.rsiz, b.rsiz);
    size_t hi = std::max(a.rsiz, b.rsiz);
    if(lo <= KARATSUBA_BASECASE_LIMBS || hi > lo * 2) return mul_basic(a, b);

    size_t split = hi / 2;
    precn_t a0 = kara_slice(a, 0, split);
    precn_t a1 = kara_slice(a, split, a.rsiz - std::min(a.rsiz, split));
    precn_t b0 = kara_slice(b, 0, split);
    precn_t b1 = kara_slice(b, split, b.rsiz - std::min(b.rsiz, split));

    precn_t z0 = kara_mul(a0, b0);
    precn_t z2 = kara_mul(a1, b1);
    precn_t z1 = kara_mul(a0 + a1, b0 + b1) - z0 - z2;

    return z0 + kara_shift_limbs(z1, split) + kara_shift_limbs(z2, split * 2);
}

precn_t mul_karatsuba(const precn_t &a, const precn_t &b){
    return kara_mul(a, b);
}
