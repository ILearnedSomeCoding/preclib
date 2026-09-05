#include"../prec.hpp"

#include<vector>

#define KARATSUBA_BASECASE_LIMBS 32

static size_t kara_trim(const uint64_t *a, size_t n){
    while(n && a[n - 1] == 0) --n;
    return n;
}

static void kara_schoolbook(uint64_t *r, size_t rn,
                            const uint64_t *a, size_t an,
                            const uint64_t *b, size_t bn){
    memset(r, 0, rn * sizeof(uint64_t));
    an = kara_trim(a, an);
    bn = kara_trim(b, bn);
    if(an == 0 || bn == 0) return;

    const uint64_t *x = a;
    const uint64_t *y = b;
    size_t xn = an;
    size_t yn = bn;
    if(xn < yn){
        std::swap(x, y);
        std::swap(xn, yn);
    }
    for(size_t i = 0; i < yn; ++i){
        uint64_t carry = 0;
        uint64_t av = y[i];
        for(size_t j = 0; j < xn; ++j){
            size_t k = i + j;
            uint64_t hi, lo, out;
            precn_mul_wide(av, x[j], hi, lo);
            uint64_t c1 = precn_add_carry(r[k], lo, 0, out);
            uint64_t c2 = precn_add_carry(out, carry, 0, out);
            r[k] = out;
            carry = hi + c1 + c2;
        }
        size_t k = i + xn;
        while(carry && k < rn){
            uint64_t out;
            carry = precn_add_carry(r[k], 0, carry, out);
            r[k++] = out;
        }
        if(carry) std::abort();
    }
}

static size_t kara_add(uint64_t *r, const uint64_t *a, size_t an,
                       const uint64_t *b, size_t bn){
    size_t n = std::max(an, bn);
    uint64_t carry = 0;
    for(size_t i = 0; i < n; ++i){
        uint64_t av = i < an ? a[i] : 0;
        uint64_t bv = i < bn ? b[i] : 0;
        carry = precn_add_carry(av, bv, carry, r[i]);
    }
    if(carry) r[n++] = carry;
    return kara_trim(r, n);
}

static void kara_sub_inplace(uint64_t *a, size_t an,
                             const uint64_t *b, size_t bn){
    uint64_t borrow = 0;
    for(size_t i = 0; i < an; ++i){
        uint64_t bv = i < bn ? b[i] : 0;
        borrow = precn_sub_borrow(a[i], bv, borrow, a[i]);
    }
    if(borrow) std::abort();
}

static void kara_add_shift(uint64_t *r, size_t rn,
                           const uint64_t *a, size_t an, size_t shift){
    uint64_t carry = 0;
    size_t i = 0;
    for(; i < an && i + shift < rn; ++i)
        carry = precn_add_carry(r[i + shift], a[i], carry,
                                r[i + shift]);
    size_t k = i + shift;
    while(carry && k < rn){
        carry = precn_add_carry(r[k], 0, carry, r[k]);
        ++k;
    }
    if(i != an || carry) std::abort();
}

static size_t kara_scratch_size(size_t an, size_t bn){
    size_t lo = std::min(an, bn);
    size_t hi = std::max(an, bn);
    if(lo <= KARATSUBA_BASECASE_LIMBS || hi > lo * 2) return 0;

    size_t split = hi / 2;
    size_t a0n = std::min(an, split), a1n = an - a0n;
    size_t b0n = std::min(bn, split), b1n = bn - b0n;
    size_t san = std::max(a0n, a1n) + 1;
    size_t sbn = std::max(b0n, b1n) + 1;
    size_t z1n = san + sbn;
    size_t child = std::max({
        kara_scratch_size(a0n, b0n),
        kara_scratch_size(a1n, b1n),
        kara_scratch_size(san, sbn)
    });
    return san + sbn + z1n + child;
}

static void kara_mul_raw(uint64_t *r, const uint64_t *a, size_t an,
                         const uint64_t *b, size_t bn, uint64_t *scratch){
    size_t rn = an + bn;
    memset(r, 0, rn * sizeof(uint64_t));
    an = kara_trim(a, an);
    bn = kara_trim(b, bn);
    if(an == 0 || bn == 0) return;

    size_t lo = std::min(an, bn);
    size_t hi = std::max(an, bn);
    if(lo <= KARATSUBA_BASECASE_LIMBS || hi > lo * 2){
        kara_schoolbook(r, rn, a, an, b, bn);
        return;
    }

    size_t split = hi / 2;
    size_t a0n = std::min(an, split), a1n = an - a0n;
    size_t b0n = std::min(bn, split), b1n = bn - b0n;
    size_t sa_capacity = std::max(a0n, a1n) + 1;
    size_t sb_capacity = std::max(b0n, b1n) + 1;
    size_t z1_capacity = sa_capacity + sb_capacity;
    uint64_t *sa = scratch;
    uint64_t *sb = sa + sa_capacity;
    uint64_t *z1 = sb + sb_capacity;
    uint64_t *child_scratch = z1 + z1_capacity;

    kara_mul_raw(r, a, a0n, b, b0n, child_scratch);
    kara_mul_raw(r + split * 2, a + a0n, a1n,
                 b + b0n, b1n, child_scratch);

    size_t san = kara_add(sa, a, a0n, a + a0n, a1n);
    size_t sbn = kara_add(sb, b, b0n, b + b0n, b1n);
    size_t z1n = san + sbn;
    kara_mul_raw(z1, sa, san, sb, sbn, child_scratch);
    kara_sub_inplace(z1, z1n, r, a0n + b0n);
    kara_sub_inplace(z1, z1n, r + split * 2, a1n + b1n);
    z1n = kara_trim(z1, z1n);
    kara_add_shift(r, rn, z1, z1n, split);
}

void precn_mul_karatsuba_into_internal(precn_t &r, const precn_t &a,
                                       const precn_t &b){
    if(&r == &a || &r == &b){
        precn_t temporary;
        precn_mul_karatsuba_into_internal(temporary, a, b);
        r = std::move(temporary);
        return;
    }
    if(a.rsiz == 0 || b.rsiz == 0){
        r.rsiz = 0;
        r.a[0] = 0;
        return;
    }

    size_t result_size = a.rsiz + b.rsiz;
    if(r.asiz < result_size){
        r.a = (uint64_t*)realloc(r.a, result_size * sizeof(uint64_t));
        r.asiz = result_size;
    }
    r.rsiz = result_size;
    size_t scratch_size = kara_scratch_size(a.rsiz, b.rsiz);
    static thread_local std::vector<uint64_t> scratch;
    if(scratch.size() < std::max<size_t>(scratch_size, 1))
        scratch.resize(std::max<size_t>(scratch_size, 1));
    kara_mul_raw(r.a, a.a, a.rsiz, b.a, b.rsiz, scratch.data());
    while(r.rsiz && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
}

precn_t mul_karatsuba(const precn_t &a, const precn_t &b){
    precn_t r;
    precn_mul_karatsuba_into_internal(r, a, b);
    return r;
}
