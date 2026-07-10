#include"../prec.hpp"

// This file implements reciprocal-based division.  The public reciprocal is
// floor(2^n / b); internally division uses blocks so it does not build one
// enormous reciprocal for the whole dividend.

static int newton_cmp(const precn_t &a, const precn_t &b){
    if(a.rsiz != b.rsiz) return a.rsiz < b.rsiz ? -1 : 1;
    for(size_t i = a.rsiz; i > 0; --i){
        if(a.a[i - 1] != b.a[i - 1]) return a.a[i - 1] < b.a[i - 1] ? -1 : 1;
    }
    return 0;
}

static void newton_reserve(precn_t &a, size_t n){
    if(a.asiz >= n) return;
    a.a = (uint32_t*) realloc(a.a, n * 4);
    a.asiz = n;
}

static void newton_norm(precn_t &a){
    while(a.rsiz > 0 && a.a[a.rsiz - 1] == 0) --a.rsiz;
    if(a.rsiz == 0) a.a[0] = 0;
}

static void newton_inc(precn_t &a){
    newton_reserve(a, std::max<size_t>(a.rsiz + 1, 1));
    uint64_t carry = 1;
    size_t i = 0;
    for(; i < a.rsiz && carry; ++i){
        uint64_t s = (uint64_t)a.a[i] + carry;
        a.a[i] = (uint32_t)s;
        carry = s >> 32;
    }
    if(carry) a.a[a.rsiz++] = (uint32_t)carry;
    if(a.rsiz == 0) a.rsiz = 1;
    newton_norm(a);
}

static void newton_dec(precn_t &a){
    size_t i = 0;
    while(i < a.rsiz){
        if(a.a[i]){
            --a.a[i];
            break;
        }
        a.a[i++] = 0xFFFFFFFFu;
    }
    newton_norm(a);
}

static void newton_add_inplace(precn_t &a, const precn_t &b){
    size_t n = std::max(a.rsiz, b.rsiz);
    newton_reserve(a, n + 1);
    if(a.rsiz < n) memset(a.a + a.rsiz, 0, (n - a.rsiz) * 4);

    uint64_t carry = 0;
    for(size_t i = 0; i < n; ++i){
        uint64_t s = (uint64_t)a.a[i] + (i < b.rsiz ? b.a[i] : 0) + carry;
        a.a[i] = (uint32_t)s;
        carry = s >> 32;
    }
    a.rsiz = n;
    if(carry) a.a[a.rsiz++] = (uint32_t)carry;
    newton_norm(a);
}

static void newton_sub_inplace_ge(precn_t &a, const precn_t &b){
    uint64_t borrow = 0;
    for(size_t i = 0; i < a.rsiz; ++i){
        uint64_t av = a.a[i];
        uint64_t sub = (i < b.rsiz ? b.a[i] : 0) + borrow;
        if(av < sub){
            a.a[i] = (uint32_t)((1ULL << 32) + av - sub);
            borrow = 1;
        }else{
            a.a[i] = (uint32_t)(av - sub);
            borrow = 0;
        }
    }
    newton_norm(a);
}

static int newton_diff_ge(const precn_t &a, const precn_t &b, const precn_t &c){
    // Return whether a - b >= c, without allocating a-b.  Caller guarantees a >= b.
    size_t n = std::max(std::max(a.rsiz, b.rsiz), c.rsiz);
    uint64_t borrow = 0;
    int cmp = 0;
    for(size_t i = 0; i < n; ++i){
        uint64_t av = i < a.rsiz ? a.a[i] : 0;
        uint64_t bv = i < b.rsiz ? b.a[i] : 0;
        uint64_t cv = i < c.rsiz ? c.a[i] : 0;
        uint64_t sub = bv + borrow;
        uint64_t dv;
        if(av < sub){
            dv = (1ULL << 32) + av - sub;
            borrow = 1;
        }else{
            dv = av - sub;
            borrow = 0;
        }
        if(dv != cv) cmp = dv > cv ? 1 : -1;
    }
    return borrow == 0 && cmp >= 0;
}

static unsigned newton_limb_bits(uint32_t x){
    unsigned n = 0;
    while(x){
        ++n;
        x >>= 1;
    }
    return n;
}

static size_t newton_bit_length(const precn_t &a){
    if(a.rsiz == 0) return 0;
    return (a.rsiz - 1) * 32 + newton_limb_bits(a.a[a.rsiz - 1]);
}

static precn_t newton_pow2(size_t bit){
    size_t limb = bit / 32;
    unsigned shift = (unsigned)(bit % 32);
    precn_t r;
    r.asiz = limb + 1;
    r.a = (uint32_t*) realloc(r.a, r.asiz * 4);
    memset(r.a, 0, r.asiz * 4);
    r.a[limb] = (uint32_t)1u << shift;
    r.rsiz = limb + 1;
    return r;
}

// Shift helpers are bit shifts, not limb-only shifts.  They are local because
// the public shift operators are not implemented elsewhere yet.
static precn_t newton_shl(const precn_t &a, size_t bits){
    if(a.rsiz == 0) return precn_t();
    size_t limbs = bits / 32;
    unsigned shift = (unsigned)(bits % 32);
    size_t extra = shift != 0 ? 1 : 0;

    precn_t r;
    r.asiz = a.rsiz + limbs + extra;
    r.a = (uint32_t*) realloc(r.a, r.asiz * 4);
    memset(r.a, 0, r.asiz * 4);

    uint32_t carry = 0;
    for(size_t i = 0; i < a.rsiz; ++i){
        uint64_t cur = ((uint64_t)a.a[i] << shift) | carry;
        r.a[i + limbs] = (uint32_t)cur;
        carry = (uint32_t)(cur >> 32);
    }
    r.rsiz = a.rsiz + limbs;
    if(shift != 0 && carry != 0) r.a[r.rsiz++] = carry;
    return r;
}

static precn_t newton_shr(const precn_t &a, size_t bits){
    size_t limbs = bits / 32;
    unsigned shift = (unsigned)(bits % 32);
    if(a.rsiz <= limbs) return precn_t();

    precn_t r;
    r.asiz = a.rsiz - limbs;
    r.a = (uint32_t*) realloc(r.a, r.asiz * 4);
    r.rsiz = r.asiz;

    uint32_t carry = 0;
    for(size_t i = a.rsiz; i > limbs; --i){
        uint32_t cur = a.a[i - 1];
        if(shift == 0){
            r.a[i - 1 - limbs] = cur;
        }else{
            r.a[i - 1 - limbs] = (cur >> shift) | carry;
            carry = cur << (32 - shift);
        }
    }

    while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}

static double newton_normalized_double(const precn_t &a, size_t bits){
    // Return the leading bits of a as a double in [0.5, 1).  This gives the
    // Newton reciprocal a ~52-bit starting estimate instead of a 1-limb guess.
    unsigned top_bits = (unsigned)((bits - 1) % 32 + 1);
    double r = std::ldexp((double)a.a[a.rsiz - 1], -(int)top_bits);
    if(a.rsiz > 1) r += std::ldexp((double)a.a[a.rsiz - 2], -(int)(top_bits + 32));
    if(a.rsiz > 2) r += std::ldexp((double)a.a[a.rsiz - 3], -(int)(top_bits + 64));
    return r;
}

static precn_t newton_step(const precn_t &b, const precn_t &x, size_t precision){
    // Fixed-point Newton step:
    // x' = floor(x * (2*2^precision - b*x) / 2^precision).
    // If x is scaled as 2^precision / b, each step roughly doubles accuracy.
    precn_t two_scale = newton_pow2(precision + 1);
    precn_t bx = b * x;
    if(newton_cmp(bx, two_scale) >= 0) return newton_shr(x, 1);
    return newton_shr(x * (two_scale - bx), precision);
}

static precn_t newton_correct_reciprocal(const precn_t &b, precn_t x, size_t precision){
    // Newton gives a very close reciprocal; adjust to the exact
    // floor(2^precision / b) promised by precn_reciprocal_newton.
    precn_t scale = newton_pow2(precision);
    precn_t product = b * x;

    while(newton_cmp(product, scale) > 0){
        x = x - precn_t(1);
        product = product - b;
    }

    while(newton_cmp(product + b, scale) <= 0){
        x = x + precn_t(1);
        product = product + b;
    }
    return x;
}

static precn_t newton_slice(const precn_t &a, size_t start, size_t n){
    // Copy n limbs starting at limb "start".  Limbs are little-endian, so this
    // is a base-2^32 block extraction.
    if(n == 0 || start >= a.rsiz) return precn_t();
    n = std::min(n, a.rsiz - start);

    precn_t r;
    r.asiz = std::max<size_t>(n, 1);
    r.a = (uint32_t*) realloc(r.a, r.asiz * 4);
    memcpy(r.a, a.a + start, n * 4);
    r.rsiz = n;
    while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}

static precn_t newton_concat_limbs(const precn_t &high, const precn_t &low, size_t low_limbs){
    // Return high * B^low_limbs + low.  This is the limb-block version of
    // newton_shl(high, low_limbs * 32) + low, but without two extra temporaries.
    if(high.rsiz == 0) return low;
    if(low.rsiz > low_limbs) return newton_shl(high, low_limbs * 32) + low;

    precn_t r;
    r.asiz = high.rsiz + low_limbs;
    r.a = (uint32_t*) realloc(r.a, r.asiz * 4);
    memset(r.a, 0, r.asiz * 4);
    memcpy(r.a, low.a, low.rsiz * 4);
    memcpy(r.a + low_limbs, high.a, high.rsiz * 4);
    r.rsiz = r.asiz;
    while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}

static size_t mulinv_size(size_t nq, size_t nb){
    // Choose quotient-block size like ILMP's div_mulinv:
    // - many quotient limbs: split into blocks no larger than divisor size
    // - quotient a little smaller than divisor: use two blocks
    // - very small quotient: one block, schoolbook is usually better anyway
    if(nq > nb){
        size_t blocks = (nq - 1) / nb + 1;
        return (nq - 1) / blocks + 1;
    }
    if(nq * 3 > nb) return (nq - 1) / 2 + 1;
    return nq;
}

precn_t precn_reciprocal_newton(const precn_t &b, size_t n){
    if(b.rsiz == 0) return precn_t();

    size_t bbits = newton_bit_length(b);
    if(n < bbits) return precn_t();

    size_t target_bits = n - bbits;
    size_t known_bits = std::min<size_t>(target_bits, 52);
    size_t precision = bbits + known_bits;

    // Seed x at scale 2^precision.  The double estimate approximates
    // 1 / (b / 2^bbits), then seed_shift moves it to floor(2^precision / b).
    double normalized = newton_normalized_double(b, bbits);
    uint64_t seed = (uint64_t)std::ldexp(1.0 / normalized, 52);
    long long seed_shift = (long long)precision - (long long)bbits - 52;
    precn_t x(seed);
    if(seed_shift >= 0) x = newton_shl(x, (size_t)seed_shift);
    else x = newton_shr(x, (size_t)(-seed_shift));

    x = newton_step(b, x, precision);

    while(precision < n){
        // Re-scale x to the next precision before each Newton step.  Each
        // iteration doubles the number of known quotient/reciprocal bits.
        known_bits = precision - bbits;
        size_t next_known = std::min(target_bits, known_bits * 2);
        if(next_known == known_bits) next_known = target_bits;
        size_t next_precision = bbits + next_known;
        x = newton_shl(x, next_precision - precision);
        x = newton_step(b, x, next_precision);
        precision = next_precision;
    }

    return newton_correct_reciprocal(b, x, n);
}

static precn_t mulinv_preinverse(const precn_t &divisor, size_t ni){
    // ILMP does not invert the whole divisor for every block.  It uses the
    // most significant ni+1 limbs, which are enough for an estimate that the
    // correction loop can fix.  The returned value is:
    //     floor(B^(top_limbs+ni) / top(divisor)) - B^ni
    // scaled so the block loop can compute q ~= high + high*preinverse/B^ni.
    size_t top_limbs = std::min(divisor.rsiz, ni + 1);
    precn_t top = newton_slice(divisor, divisor.rsiz - top_limbs, top_limbs);
    precn_t reciprocal = precn_reciprocal_newton(top, (top_limbs + ni) * 32);
    return reciprocal - newton_pow2(ni * 32);
}

static precn_t div_mulinv_impl(const precn_t &a, const precn_t &b,
                               precn_t *remainder_out, int want_quotient){
    if(a.rsiz == 0 || b.rsiz == 0){
        if(remainder_out) *remainder_out = precn_t();
        return precn_t();
    }
    if(newton_cmp(a, b) < 0){
        if(remainder_out) *remainder_out = a;
        return precn_t();
    }
    if(b.rsiz == 1){
        if(remainder_out) *remainder_out = mod_u32(a, b.a[0]);
        return want_quotient ? div_u32(a, b.a[0]) : precn_t();
    }

    // Normalize b so its top bit is set.  That keeps quotient-block estimates
    // tight; the final remainder is shifted back down before returning.
    unsigned shift = 32 - newton_limb_bits(b.a[b.rsiz - 1]);
    precn_t divisor = shift == 0 ? b : newton_shl(b, shift);
    precn_t dividend = shift == 0 ? a : newton_shl(a, shift);

    // nq is the maximum quotient limb count in the normalized division.
    size_t nq = dividend.rsiz - divisor.rsiz + 1;
    if(nq * 3 <= divisor.rsiz){
        if(remainder_out) *remainder_out = mod_schoolbook(a, b);
        return want_quotient ? div_schoolbook(a, b) : precn_t();
    }

    // ni is the number of quotient limbs produced per block.  The reciprocal
    // has divisor.rsiz + ni limbs of fixed-point precision, enough to estimate
    // one block from the high divisor.rsiz+ni limbs of the current partial
    // dividend.
    size_t ni = mulinv_size(nq, divisor.rsiz);
    precn_t preinverse_full = mulinv_preinverse(divisor, ni);
    precn_t quotient;

    // The top divisor.rsiz-1 limbs are the initial partial remainder.  The
    // loop appends quotient blocks below it, just like long division.
    precn_t remainder = newton_slice(dividend, nq, divisor.rsiz - 1);

    size_t pos = nq;
    size_t first = nq % ni;
    if(first == 0) first = ni;

    while(pos > 0){
        // Pull down the next block of dividend limbs.  "current" has the old
        // remainder in high limbs and the new block in low limbs.
        size_t block = pos == nq ? first : ni;
        pos -= block;

        precn_t chunk = newton_slice(dividend, pos, block);
        precn_t current = newton_concat_limbs(remainder, chunk, block);

        // Convert reciprocal to ILMP-style preinverse:
        // preinverse ~= B^block * (B^divisor_limbs / divisor - 1).
        // Multiplying only the high part of "current" by this is cheaper than
        // multiplying the whole current block by the full reciprocal.
        precn_t preinverse = block == ni
            ? preinverse_full
            : newton_shr(preinverse_full, (ni - block) * 32);
        precn_t high = newton_shr(current, divisor.rsiz * 32);
        precn_t estimate = high + newton_shr(high * preinverse, block * 32);
        precn_t product = divisor * estimate;

        // The estimate can be a little high or low because the reciprocal and
        // high-product estimate are truncated.  Correct until:
        //     product <= current < product + divisor
        while(newton_cmp(product, current) > 0){
            newton_dec(estimate);
            newton_sub_inplace_ge(product, divisor);
        }
        while(newton_diff_ge(current, product, divisor)){
            newton_inc(estimate);
            newton_add_inplace(product, divisor);
        }

        // current = divisor * estimate + remainder for this block.
        remainder = current - product;
        if(want_quotient) quotient = newton_concat_limbs(quotient, estimate, block);
    }

    if(remainder_out){
        // Undo normalization.  Quotient is unchanged by the common shift.
        *remainder_out = shift == 0 ? remainder : newton_shr(remainder, shift);
    }
    return want_quotient ? quotient : precn_t();
}

precn_t div_mulinv(const precn_t &a, const precn_t &b){
    return div_mulinv_impl(a, b, nullptr, 1);
}

precn_t mod_mulinv(const precn_t &a, const precn_t &b){
    precn_t remainder;
    div_mulinv_impl(a, b, &remainder, 0);
    return remainder;
}

precn_t div_newton(const precn_t &a, const precn_t &b){
    return div_mulinv(a, b);
}
