#include"../prec.hpp"

static int newton64_cmp(const precn_t &a, const precn_t &b){
    if(a.rsiz != b.rsiz) return a.rsiz < b.rsiz ? -1 : 1;
    for(size_t i = a.rsiz; i > 0; --i){
        if(a.a[i - 1] != b.a[i - 1]) return a.a[i - 1] < b.a[i - 1] ? -1 : 1;
    }
    return 0;
}

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

static precn_t newton64_top_ceil(const precn_t &b, size_t divisor_bits,
                                 size_t keep_bits){
    if(keep_bits >= divisor_bits) return b;
    size_t drop = divisor_bits - keep_bits;
    // Rounding the discarded tail upward keeps the reciprocal estimate on
    // the low side.  An exact power-of-two cut may add one unnecessarily,
    // which only costs a guard bit and is corrected by the final quotient.
    return (b >> drop) + 1;
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
        precn_t scaled_x = x << (next_known - known);
        precn_t two_scale = newton64_pow2(next + 1);
        precn_t bx = next_b * scaled_x;
        if(bx >= two_scale){
            // This only protects against a rounding overshoot; it is not the
            // normal path for a floor reciprocal.
            scaled_x = scaled_x >> 1;
            bx = next_b * scaled_x;
        }
        x = (scaled_x * (two_scale - bx)) >> next;
        known = next_known;
    }

    return x;
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

    // Keep two full guard limbs.  The reciprocal is truncated after every
    // Newton step, so two bits are not enough to reliably keep the quotient
    // correction to one unit at large sizes.
    size_t scale = newton64_bits(a) + 128;
    precn_t inverse = newton64_reciprocal_approx(b, scale);
    precn_t q = (a * inverse) >> scale;
    precn_t product = b * q;

    // A good reciprocal reaches one of the two short loops below immediately.
    // If it does not, correct the whole quotient error at once.  The previous
    // q = q +/- 1 loop made a large reciprocal error effectively unbounded.
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

precn_t div_mulinv(const precn_t &a, const precn_t &b){
    return div_mulinv_impl(a, b, nullptr);
}

precn_t mod_mulinv(const precn_t &a, const precn_t &b){
    precn_t r;
    div_mulinv_impl(a, b, &r);
    return r;
}
