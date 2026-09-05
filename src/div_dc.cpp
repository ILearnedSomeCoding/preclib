#include"../prec.hpp"


#ifndef DIV_DC_BASECASE
#define DIV_DC_BASECASE 64
#endif

static precn_t dc_slice(const precn_t &a, size_t off, size_t n){
    precn_t r;
    if(off >= a.rsiz || n == 0) return r;
    n = std::min(n, a.rsiz - off);
    r.asiz = std::max<size_t>(n, 1);
    r.a = (uint64_t*) realloc(r.a, r.asiz * sizeof(uint64_t));
    memcpy(r.a, a.a + off, n * sizeof(uint64_t));
    r.rsiz = n;
    while(r.rsiz && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}

static precn_t dc_join(const precn_t &high, const precn_t &low, size_t low_limbs){
    if(high.rsiz == 0) return low;
    // The two inputs occupy disjoint limb ranges.  Building a shifted copy
    // and then adding it to low used two temporary big integers at every
    // divide-and-conquer level; concatenate the ranges directly instead.
    precn_t r;
    r.rsiz = low_limbs + high.rsiz;
    r.asiz = std::max<size_t>(r.rsiz, 1);
    r.a = (uint64_t*)realloc(r.a, r.asiz * sizeof(uint64_t));
    if(low.rsiz) memcpy(r.a, low.a, low.rsiz * sizeof(uint64_t));
    if(low.rsiz < low_limbs)
        memset(r.a + low.rsiz, 0, (low_limbs - low.rsiz) * sizeof(uint64_t));
    memcpy(r.a + low_limbs, high.a, high.rsiz * sizeof(uint64_t));
    return r;
}

static precn_t dc_join_low_words(const precn_t &high, const uint64_t *low,
                                 size_t low_siz, size_t low_limbs){
    if(high.rsiz == 0){
        precn_t r;
        r.rsiz = low_siz;
        r.asiz = std::max<size_t>(low_siz, 1);
        r.a = (uint64_t*)realloc(r.a, r.asiz * sizeof(uint64_t));
        if(low_siz) memcpy(r.a, low, low_siz * sizeof(uint64_t));
        else r.a[0] = 0;
        return r;
    }

    precn_t r;
    r.rsiz = low_limbs + high.rsiz;
    r.asiz = r.rsiz;
    r.a = (uint64_t*)realloc(r.a, r.asiz * sizeof(uint64_t));
    if(low_siz) memcpy(r.a, low, low_siz * sizeof(uint64_t));
    if(low_siz < low_limbs)
        memset(r.a + low_siz, 0, (low_limbs - low_siz) * sizeof(uint64_t));
    memcpy(r.a + low_limbs, high.a, high.rsiz * sizeof(uint64_t));
    return r;
}

static precn_t dc_limb_mask(size_t n){
    precn_t r;
    r.asiz = std::max<size_t>(n, 1);
    r.a = (uint64_t*) realloc(r.a, r.asiz * sizeof(uint64_t));
    r.rsiz = n;
    for(size_t i = 0; i < n; ++i) r.a[i] = UINT64_MAX;
    if(n == 0) r.a[0] = 0;
    return r;
}

static void dc_div_2n1n(const precn_t &a, const precn_t &b, size_t n,
                        precn_t &q, precn_t &r);

// Divide a three-half window by a two-half divisor.  The trial quotient comes
// from the high halves; multiplying it by the low half needs at most two
// corrections when the divisor is normalized.
static void dc_div_3n2n(const precn_t &a, const precn_t &b, size_t n,
                        precn_t &q, precn_t &r){
    size_t k = n / 2;
    precn_t b0 = dc_slice(b, 0, k);
    precn_t b1 = dc_slice(b, k, k);
    precn_t a2 = dc_slice(a, k * 2, k);
    precn_t upper = dc_slice(a, k, k * 2);
    precn_t rhat;

    if(a2 < b1){
        dc_div_2n1n(upper, b1, k, q, rhat);
    }else{
        q = dc_limb_mask(k);
        rhat = upper - q * b1;
    }

    size_t low_siz = std::min(k, a.rsiz);
    precn_t t = dc_join_low_words(rhat, a.a, low_siz, k);
    precn_t d = q * b0;
    while(t < d){
        q = q - precn_t(1);
        t = t + b;
    }
    r = t - d;
}

static void dc_div_2n1n(const precn_t &a, const precn_t &b, size_t n,
                        precn_t &q, precn_t &r){
    if(n <= DIV_DC_BASECASE || (n & 1)){
        divmod_schoolbook_into(q, r, a, b);
        return;
    }

    size_t k = n / 2;
    precn_t upper = dc_slice(a, k, n + k);
    precn_t q1, r1, q0;
    dc_div_3n2n(upper, b, n, q1, r1);
    precn_t lower = dc_join_low_words(r1, a.a, std::min(k, a.rsiz), k);
    dc_div_3n2n(lower, b, n, q0, r);
    q = dc_join(q1, q0, k);
}
static unsigned dc_clz64(uint64_t x){
#if defined(__clang__) || defined(__GNUC__)
    return (unsigned)__builtin_clzll(x);
#else
    unsigned n = 0;
    while((x & 0x8000000000000000ULL) == 0){ x <<= 1; ++n; }
    return n;
#endif
}

bool div_dc_into(precn_t &q, precn_t &r, const precn_t &a, const precn_t &b){
    if(b.rsiz < DIV_DC_BASECASE || a < b) return false;
    if(a.rsiz > b.rsiz * 2) return false;

    // Low zero padding makes the divisor length recursively splittable
    // without changing the quotient.  A 64-limb block is enough because the
    // recursion stops there; requiring a power-of-two input length would
    // unnecessarily exclude most real operand sizes.
    size_t n = (b.rsiz + DIV_DC_BASECASE - 1) / DIV_DC_BASECASE * DIV_DC_BASECASE;
    size_t limb_pad = n - b.rsiz;

    unsigned shift = dc_clz64(b.a[b.rsiz - 1]);
    size_t total_shift = limb_pad * 64 + shift;
    precn_t bn = total_shift ? b << total_shift : b;
    precn_t an = total_shift ? a << total_shift : a;
    precn_t high = dc_slice(an, n, an.rsiz);
    precn_t qhigh, rhigh;

    // Normalization can expose a short leading quotient above the n-limb
    // recursive window.  Remove it once with the basecase routine.
    if(high >= bn){
        divmod_schoolbook_into(qhigh, rhigh, high, bn);
    }else{
        rhigh = high;
    }

    precn_t qlow, rn;
    precn_t lower = dc_join_low_words(rhigh, an.a, std::min(n, an.rsiz), n);
    dc_div_2n1n(lower, bn, n, qlow, rn);
    q = dc_join(qhigh, qlow, n);
    r = total_shift ? rn >> total_shift : rn;
    return true;
}
bool div_dc_blocked_into(precn_t &q, precn_t &r,
                         const precn_t &a, const precn_t &b){
    if(b.rsiz < DIV_DC_BASECASE || a < b || a.rsiz <= b.rsiz * 2)
        return false;

    size_t n = (b.rsiz + DIV_DC_BASECASE - 1) / DIV_DC_BASECASE * DIV_DC_BASECASE;
    size_t limb_pad = n - b.rsiz;
    unsigned shift = dc_clz64(b.a[b.rsiz - 1]);
    size_t total_shift = limb_pad * 64 + shift;
    precn_t bn = total_shift ? b << total_shift : b;
    precn_t an = total_shift ? a << total_shift : a;
    size_t blocks = (an.rsiz + n - 1) / n;

    q.asiz = std::max<size_t>(blocks * n, 1);
    q.a = (uint64_t*)realloc(q.a, q.asiz * sizeof(uint64_t));
    memset(q.a, 0, q.asiz * sizeof(uint64_t));
    q.rsiz = blocks * n;

    precn_t rn, current, qblock, next_r;
    for(size_t block = blocks; block > 0; --block){
        size_t index = block - 1;
        size_t offset = index * n;
        size_t chunk_size = std::min(n, an.rsiz - offset);
        size_t current_size = n + rn.rsiz;
        size_t need = std::max(current_size, chunk_size);
        if(current.asiz < need){
            current.asiz = need;
            current.a = (uint64_t*)realloc(current.a,
                                            need * sizeof(uint64_t));
        }
        memcpy(current.a, an.a + offset, chunk_size * sizeof(uint64_t));
        if(chunk_size < n)
            memset(current.a + chunk_size, 0,
                   (n - chunk_size) * sizeof(uint64_t));
        if(rn.rsiz) memcpy(current.a + n, rn.a,
                           rn.rsiz * sizeof(uint64_t));
        current.rsiz = std::max(chunk_size, current_size);
        while(current.rsiz && current.a[current.rsiz - 1] == 0)
            --current.rsiz;

        if(current < bn){
            qblock.rsiz = 0;
            next_r = current;
        }else{
            dc_div_2n1n(current, bn, n, qblock, next_r);
        }
        if(qblock.rsiz > n) std::abort();
        if(qblock.rsiz)
            memcpy(q.a + offset, qblock.a,
                   qblock.rsiz * sizeof(uint64_t));
        rn = std::move(next_r);
    }

    while(q.rsiz && q.a[q.rsiz - 1] == 0) --q.rsiz;
    if(q.rsiz == 0) q.a[0] = 0;
    r = total_shift ? rn >> total_shift : rn;
    return true;
}
