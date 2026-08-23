#include"../prec.hpp"

#include<vector>

#define SSA_MAX_TRANSFORM 128

static precn_t ssa_from_limbs(const uint64_t *p, size_t n){
    while(n > 0 && p[n - 1] == 0) --n;

    precn_t r;
    r.asiz = std::max<size_t>(n, 1);
    r.a = (uint64_t*) realloc(r.a, r.asiz * sizeof(uint64_t));
    r.rsiz = n;
    if(n) memcpy(r.a, p, n * sizeof(uint64_t));
    else r.a[0] = 0;
    return r;
}

static precn_t ssa_low_limbs(const precn_t &a, size_t n){
    return ssa_from_limbs(a.a, std::min(a.rsiz, n));
}

static precn_t ssa_high_limbs(const precn_t &a, size_t n){
    if(a.rsiz <= n) return precn_t();
    return ssa_from_limbs(a.a + n, a.rsiz - n);
}

static precn_t ssa_fermat_modulus(size_t ring_bits){
    return (precn_t(1) << ring_bits) + 1;
}

static precn_t ssa_fermat_reduce(const precn_t &x, size_t ring_bits, const precn_t &mod){
    // ring_bits is deliberately a multiple of 64.  In Z/(2^m + 1), split
    // x = lo + 2^m hi and replace it by lo - hi because 2^m == -1.
    size_t limbs = ring_bits / 64;
    precn_t r = x;

    while(r.rsiz > limbs){
        precn_t lo = ssa_low_limbs(r, limbs);
        precn_t hi = ssa_high_limbs(r, limbs);
        if(lo >= hi) r = lo - hi;
        else r = mod - (hi - lo);
    }
    if(r >= mod) r = r - mod;
    return r;
}

static precn_t ssa_fermat_neg(const precn_t &a, const precn_t &mod){
    if(a.rsiz == 0) return precn_t();
    return mod - a;
}

static precn_t ssa_fermat_add(const precn_t &a, const precn_t &b, const precn_t &mod){
    precn_t r = a + b;
    if(r >= mod) r = r - mod;
    if(r >= mod) r = r - mod;
    return r;
}

static precn_t ssa_fermat_sub(const precn_t &a, const precn_t &b, const precn_t &mod){
    if(a >= b) return a - b;
    precn_t d = b - a;
    return d.rsiz ? mod - d : precn_t();
}

static precn_t ssa_fermat_shift(const precn_t &a, size_t shift,
                                size_t ring_bits, const precn_t &mod){
    if(a.rsiz == 0) return precn_t();

    size_t period = ring_bits * 2;
    shift %= period;
    int neg = 0;
    if(shift >= ring_bits){
        shift -= ring_bits;
        neg = 1;
    }

    precn_t r = ssa_fermat_reduce(a << shift, ring_bits, mod);
    return neg ? ssa_fermat_neg(r, mod) : r;
}

static precn_t ssa_fermat_mul(const precn_t &a, const precn_t &b,
                              size_t ring_bits, const precn_t &mod){
    if(a.rsiz == 0 || b.rsiz == 0) return precn_t();
    precn_t product = std::max(a.rsiz, b.rsiz) <= 64 ? mul_basic(a, b) : mul_fft(a, b);
    return ssa_fermat_reduce(product, ring_bits, mod);
}

static void ssa_bit_reverse(std::vector<precn_t> &a){
    size_t n = a.size();
    for(size_t i = 1, j = 0; i < n; ++i){
        size_t bit = n >> 1;
        for(; j & bit; bit >>= 1) j ^= bit;
        j ^= bit;
        if(i < j) std::swap(a[i], a[j]);
    }
}

static void ssa_fft(std::vector<precn_t> &a, int inv,
                    size_t ring_bits, const precn_t &mod){
    size_t n = a.size();
    ssa_bit_reverse(a);

    for(size_t len = 2; len <= n; len <<= 1){
        size_t half = len >> 1;
        size_t root_step = (ring_bits * 2) / len;
        if(inv) root_step = ring_bits * 2 - root_step;

        for(size_t i = 0; i < n; i += len){
            for(size_t j = 0; j < half; ++j){
                precn_t u = a[i + j];
                precn_t v = ssa_fermat_shift(a[i + j + half],
                                             root_step * j,
                                             ring_bits, mod);
                a[i + j] = ssa_fermat_add(u, v, mod);
                a[i + j + half] = ssa_fermat_sub(u, v, mod);
            }
        }
    }

    if(inv){
        size_t lg = 0;
        while(((size_t)1 << lg) < n) ++lg;

        size_t inv_shift = ring_bits - lg;
        for(size_t i = 0; i < n; ++i){
            precn_t t = ssa_fermat_shift(a[i], inv_shift, ring_bits, mod);
            a[i] = ssa_fermat_neg(t, mod);
        }
    }
}

precn_t mul_ssa(const precn_t &a, const precn_t &b){
    if(a.rsiz == 0 || b.rsiz == 0) return precn_t();
    if(a.rsiz + b.rsiz <= 4) return mul_basic(a, b);

    // Split our base-2^64 limbs into base-2^32 coefficients.  With n a power
    // of two and m = 32n, every convolution coefficient is strictly below
    // 2^m, so recovering it from Z/(2^m + 1) is unambiguous.
    std::vector<uint32_t> da, db;
    da.reserve(a.rsiz * 2);
    db.reserve(b.rsiz * 2);
    for(size_t i = 0; i < a.rsiz; ++i){
        da.push_back((uint32_t)a.a[i]);
        da.push_back((uint32_t)(a.a[i] >> 32));
    }
    for(size_t i = 0; i < b.rsiz; ++i){
        db.push_back((uint32_t)b.a[i]);
        db.push_back((uint32_t)(b.a[i] >> 32));
    }
    while(!da.empty() && da.back() == 0) da.pop_back();
    while(!db.empty() && db.back() == 0) db.pop_back();
    if(da.empty() || db.empty()) return precn_t();

    size_t n = 1;
    while(n < da.size() + db.size()) n <<= 1;
    if(n > SSA_MAX_TRANSFORM) return mul_ntt(a, b);

    size_t ring_bits = n * 32;
    precn_t mod = ssa_fermat_modulus(ring_bits);

    std::vector<precn_t> fa(n), fb(n);
    for(size_t i = 0; i < da.size(); ++i) fa[i] = precn_t(da[i]);
    for(size_t i = 0; i < db.size(); ++i) fb[i] = precn_t(db[i]);

    ssa_fft(fa, 0, ring_bits, mod);
    ssa_fft(fb, 0, ring_bits, mod);

    for(size_t i = 0; i < n; ++i){
        fa[i] = ssa_fermat_mul(fa[i], fb[i], ring_bits, mod);
    }

    ssa_fft(fa, 1, ring_bits, mod);

    precn_t r;
    size_t out = da.size() + db.size() - 1;
    r.asiz = out / 2 + 3;
    r.a = (uint64_t*) realloc(r.a, r.asiz * sizeof(uint64_t));
    memset(r.a, 0, r.asiz * sizeof(uint64_t));
    r.rsiz = 0;

    // The inverse produces ordinary base-2^32 convolution coefficients.
    // Normalize them once from low to high instead of building shifted
    // temporary big integers for every coefficient.
    precn_t carry;
    size_t digit = 0;
    for(size_t i = 0; i < out; ++i){
        precn_t coefficient = fa[i] + carry;
        uint32_t low = coefficient.rsiz ? (uint32_t)coefficient.a[0] : 0;
        size_t limb = digit >> 1;
        if(limb >= r.asiz){
            size_t old = r.asiz;
            r.asiz *= 2;
            r.a = (uint64_t*) realloc(r.a, r.asiz * sizeof(uint64_t));
            memset(r.a + old, 0, (r.asiz - old) * sizeof(uint64_t));
        }
        r.a[limb] |= (uint64_t)low << ((digit & 1) * 32);
        if(r.rsiz < limb + 1) r.rsiz = limb + 1;
        carry = coefficient >> 32;
        ++digit;
    }
    while(carry.rsiz){
        uint32_t low = (uint32_t)carry.a[0];
        size_t limb = digit >> 1;
        if(limb >= r.asiz){
            size_t old = r.asiz;
            r.asiz *= 2;
            r.a = (uint64_t*) realloc(r.a, r.asiz * sizeof(uint64_t));
            memset(r.a + old, 0, (r.asiz - old) * sizeof(uint64_t));
        }
        r.a[limb] |= (uint64_t)low << ((digit & 1) * 32);
        if(r.rsiz < limb + 1) r.rsiz = limb + 1;
        carry = carry >> 32;
        ++digit;
    }
    while(r.rsiz && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}
