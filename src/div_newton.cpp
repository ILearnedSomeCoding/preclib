#include"../prec.hpp"

#ifndef NEWTON_INPLACE_SHIFT
#define NEWTON_INPLACE_SHIFT 1
#endif


static size_t newton64_bits(const precn_t &a){
    if(a.rsiz == 0) return 0;
    uint64_t top = a.a[a.rsiz - 1];
    size_t bits = (a.rsiz - 1) * 64;
    while(top){
        ++bits;
        top >>= 1;
    }
    return bits;
}

static precn_t newton64_pow2(size_t bits){
    return precn_t(1) << bits;
}

static void newton64_shift_left_inplace(precn_t &a, size_t bits){
    if(a.rsiz == 0 || bits == 0) return;
    size_t limb_shift = bits >> 6;
    unsigned bit_shift = (unsigned)(bits & 63);
    size_t old_size = a.rsiz;
    size_t need = old_size + limb_shift + (bit_shift != 0);
    if(a.asiz < need){
        a.a = (uint64_t*)realloc(a.a, need * sizeof(uint64_t));
        a.asiz = need;
    }
    if(limb_shift){
        memmove(a.a + limb_shift, a.a, old_size * sizeof(uint64_t));
        memset(a.a, 0, limb_shift * sizeof(uint64_t));
    }
    if(bit_shift){
        uint64_t carry = 0;
        for(size_t i = limb_shift; i < limb_shift + old_size; ++i){
            uint64_t cur = a.a[i];
            a.a[i] = (cur << bit_shift) | carry;
            carry = cur >> (64 - bit_shift);
        }
        if(carry) a.a[limb_shift + old_size++] = carry;
    }
    a.rsiz = old_size + limb_shift;
}

static precn_t newton64_pow2_minus(const precn_t &a, size_t bit){
    size_t limb = bit / 64;
    unsigned offset = (unsigned)(bit % 64);
    precn_t r;
    r.asiz = limb + 1;
    r.a = (uint64_t*)realloc(r.a, r.asiz * sizeof(uint64_t));
    memset(r.a, 0, r.asiz * sizeof(uint64_t));
    r.a[limb] = 1ULL << offset;
    r.rsiz = limb + 1;

    uint64_t borrow = 0;
    for(size_t i = 0; i < r.rsiz; ++i){
        uint64_t out;
        borrow = precn_sub_borrow(r.a[i], i < a.rsiz ? a.a[i] : 0,
                                  borrow, out);
        r.a[i] = out;
    }
    if(borrow) std::abort();
    while(r.rsiz && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}

static precn_t newton64_mul_shift_right(const precn_t &a, const precn_t &b,
                                        size_t shift){
    size_t drop = shift / 64;
    if(drop && std::max(a.rsiz, b.rsiz) >= 2048)
        return mul_high(a, b, drop) >> (shift % 64);
    return (a * b) >> shift;
}

static precn_t newton64_top_ceil(const precn_t &b, size_t divisor_bits,
                                 size_t keep_bits){
    if(keep_bits >= divisor_bits) return b;
    size_t drop = divisor_bits - keep_bits;
    // Rounding the discarded tail upward keeps the reciprocal estimate on
    // the low side.  An exact power-of-two cut may add one unnecessarily,
    // which only costs a guard bit and is corrected by the final quotient.
    precn_t r = b >> drop;
    size_t i = 0;
    while(i < r.rsiz && ++r.a[i] == 0) ++i;
    if(i == r.rsiz){
        if(r.asiz == r.rsiz){
            ++r.asiz;
            r.a = (uint64_t*)realloc(r.a, r.asiz * sizeof(uint64_t));
        }
        r.a[r.rsiz++] = 1;
    }
    return r;
}

static precn_t newton64_reciprocal_approx(const precn_t &b, size_t bits){
    if(b.rsiz == 0 || bits < newton64_bits(b)) return precn_t();

    // x represents floor(2^precision / b).  Each step doubles the number
    // of correct reciprocal bits while preserving the fixed-point scale.
    size_t divisor_bits = newton64_bits(b);
    size_t target_known = bits - divisor_bits;
    size_t known = std::min<size_t>(target_known, 64);
    size_t keep = std::min(divisor_bits, known + 128);
    precn_t bt = newton64_top_ceil(b, divisor_bits, keep);
    size_t precision = keep + known;
    precn_t x = div_schoolbook(newton64_pow2(precision), bt);

    while(known < target_known){
        size_t next_known = std::min(target_known, known * 2);
        size_t next_keep = std::min(divisor_bits, next_known + 128);
        precn_t next_b = newton64_top_ceil(b, divisor_bits, next_keep);
        size_t next = next_keep + next_known;
#if NEWTON_INPLACE_SHIFT
        newton64_shift_left_inplace(x, next_known - known);
        precn_t &scaled_x = x;
#else
        precn_t scaled_x = x << (next_known - known);
#endif
        precn_t bx = next_b * scaled_x;
        if(newton64_bits(bx) > next + 1){
            // This only protects against a rounding overshoot; it is not the
            // normal path for a floor reciprocal.
            scaled_x = scaled_x >> 1;
            bx = next_b * scaled_x;
        }
        precn_t correction = newton64_pow2_minus(bx, next + 1);
        x = newton64_mul_shift_right(scaled_x, correction, next);
        known = next_known;
    }

    return x;
}

precn_t precn_reciprocal_newton_approx(const precn_t &b, size_t bits){
    return newton64_reciprocal_approx(b, bits);
}

precn_t precn_reciprocal_newton(const precn_t &b, size_t bits){
    precn_t x = newton64_reciprocal_approx(b, bits);
    if(x.rsiz == 0 || b.rsiz == 0) return x;

    // Public reciprocal callers expect the exact floor value.  Division uses
    // the approximation directly and corrects its quotient instead.
    precn_t scale = newton64_pow2(bits);
    precn_t product = b * x;
    while(product > scale){
        x = x - precn_t(1);
        product = product - b;
    }
    while(product + b <= scale){
        x = x + precn_t(1);
        product = product + b;
    }
    return x;
}


static precn_t div_mulinv_apply(const precn_t &a, const precn_t &b,
                               const precn_t &inverse, size_t scale,
                               precn_t *remainder){
    precn_t q = newton64_mul_shift_right(a, inverse, scale);
    precn_t product = b * q;

    while(product > a){
        precn_t delta = div_schoolbook(product - a, b);
        if(delta.rsiz == 0) delta = precn_t(1);
        q = q - delta;
        product = product - b * delta;
    }
    while(product + b <= a){
        precn_t delta = div_schoolbook(a - product, b);
        if(delta.rsiz == 0) delta = precn_t(1);
        q = q + delta;
        product = product + b * delta;
    }

    if(remainder) *remainder = a - product;
    return q;
}

static precn_t div_mulinv_impl(const precn_t &a, const precn_t &b, precn_t *remainder){
    if(a.rsiz == 0 || b.rsiz == 0){
        if(remainder) *remainder = precn_t();
        return precn_t();
    }
    if(a < b){
        if(remainder) *remainder = a;
        return precn_t();
    }
    if(b.rsiz == 1){
        if(remainder) *remainder = mod_u64(a, b.a[0]);
        return div_u64(a, b.a[0]);
    }

    size_t scale = newton64_bits(a) + 128;
    precn_t inverse = newton64_reciprocal_approx(b, scale);
    return div_mulinv_apply(a, b, inverse, scale, remainder);
}

precn_t div_mulinv(const precn_t &a, const precn_t &b){
    return div_mulinv_impl(a, b, nullptr);
}

void div_mulinv_pair_into(precn_t &qa, precn_t &qc,
                          const precn_t &a, const precn_t &c,
                          const precn_t &b){
    if(b.rsiz == 0) std::abort();
    if(b.rsiz == 1){
        qa = div_u64(a, b.a[0]);
        qc = div_u64(c, b.a[0]);
        return;
    }
    size_t scale = std::max(newton64_bits(a), newton64_bits(c)) + 128;
    precn_t inverse = newton64_reciprocal_approx(b, scale);
    qa = div_mulinv_apply(a, b, inverse, scale, nullptr);
    qc = div_mulinv_apply(c, b, inverse, scale, nullptr);
}

void divmod_mulinv_into(precn_t &q, precn_t &r, const precn_t &a,
                        const precn_t &b){
    q = div_mulinv_impl(a, b, &r);
}
void divmod_mulinv_precomputed_into(
    precn_t &q, precn_t &r, const precn_t &a, const precn_t &b,
    const precn_t &inverse, size_t scale){
    if(b.rsiz == 0 || inverse.rsiz == 0) std::abort();
    q = div_mulinv_apply(a, b, inverse, scale, &r);
}

precn_t mod_mulinv(const precn_t &a, const precn_t &b){
    precn_t r;
    div_mulinv_impl(a, b, &r);
    return r;
}
