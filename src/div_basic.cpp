#include"../prec.hpp"

#include<utility>
#include<vector>

#if defined(_MSC_VER) && defined(_M_X64) && !defined(__clang__)
#include<intrin.h>
#endif

#define DIV_DC_THRESHOLD 256
#define DIV_MULINV_THRESHOLD 32768
#define DIV_LONG_MULINV_THRESHOLD 16384
#ifndef DIV_U64_PREINV_THRESHOLD
#define DIV_U64_PREINV_THRESHOLD 16
#endif

static int div_cmp(const precn_t &a, const precn_t &b){
    if(a.rsiz != b.rsiz) return a.rsiz < b.rsiz ? -1 : 1;
    for(size_t i = a.rsiz; i > 0; --i){
        if(a.a[i - 1] != b.a[i - 1]) return a.a[i - 1] < b.a[i - 1] ? -1 : 1;
    }
    return 0;
}

static unsigned div_clz64(uint64_t x){
#if defined(__clang__) || defined(__GNUC__)
    return (unsigned)__builtin_clzll(x);
#else
    unsigned n = 0;
    while((x & 0x8000000000000000ULL) == 0){
        x <<= 1;
        ++n;
    }
    return n;
#endif
}

static uint64_t div_submul_1(uint64_t *up, const uint64_t *vp, size_t n, uint64_t q){
    if(q == 0) return 0;

    uint64_t borrow = 0;
    for(size_t i = 0; i < n; ++i){
        uint64_t hi, lo;
        precn_mul_wide(vp[i], q, hi, lo);
        uint64_t prod_low;
        uint64_t c = precn_add_carry(lo, borrow, 0, prod_low);
        uint64_t prod_high = hi + c;

        uint64_t old = up[i];
        up[i] = old - prod_low;
        borrow = prod_high + (old < prod_low);
    }
    return borrow;
}

static uint64_t div_2by1(uint64_t hi, uint64_t lo, uint64_t d, uint64_t &rem){
#if defined(_MSC_VER) && defined(_M_X64) && !defined(__clang__)
    // Every caller maintains hi < d, so the quotient fits in one limb.
    // Clang/MSVC lower this intrinsic to one hardware divq instruction.
    return _udiv128(hi, lo, d, &rem);
#elif defined(__clang__) && defined(__x86_64__)
    // clang++ in this Windows setup exposes neither _udiv128 nor a public
    // equivalent.  divq is exactly the operation wanted here: RDX:RAX / d.
    __asm__ volatile("divq %2" : "+a"(lo), "+d"(hi) : "r"(d) : "cc");
    rem = hi;
    return lo;
#else
    if(d <= UINT32_MAX){
        // Here hi is a remainder, hence it already fits below d.  Splitting
        // the numerator directly avoids normalization and its correction
        // loops for the common uint32_t divisor case.
        uint64_t top = (hi << 32) | (lo >> 32);
        uint64_t q1 = top / d;
        rem = top - q1 * d;
        uint64_t bottom = (rem << 32) | (uint32_t)lo;
        uint64_t q0 = bottom / d;
        rem = bottom - q0 * d;
        return (q1 << 32) | q0;
    }

    const uint64_t base = 1ULL << 32;
    unsigned shift = div_clz64(d);
    uint64_t vn = d << shift;
    uint64_t vn1 = vn >> 32;
    uint64_t vn0 = (uint32_t)vn;
    uint64_t un64 = shift == 0 ? hi : (hi << shift) | (lo >> (64 - shift));
    uint64_t un10 = lo << shift;
    uint64_t un1 = un10 >> 32;
    uint64_t un0 = (uint32_t)un10;

    uint64_t q1 = un64 / vn1;
    uint64_t rhat = un64 - q1 * vn1;
    while(q1 >= base || q1 * vn0 > (rhat << 32) + un1){
        --q1;
        rhat += vn1;
        if(rhat >= base) break;
    }

    uint64_t un21 = un64 * base + un1 - q1 * vn;
    uint64_t q0 = un21 / vn1;
    rhat = un21 - q0 * vn1;
    while(q0 >= base || q0 * vn0 > (rhat << 32) + un0){
        --q0;
        rhat += vn1;
        if(rhat >= base) break;
    }

    uint64_t normalized_rem = un21 * base + un0 - q0 * vn;
    rem = shift == 0 ? normalized_rem : normalized_rem >> shift;
    return q1 * base + q0;
#endif
}

// For normalized d, inverse is floor((2^128 - 1) / d) - 2^64. One divq
// computes it once; each following quotient limb only needs multiplications
// and carry corrections.
static uint64_t div_inverse_normalized(uint64_t d){
    uint64_t ignored;
    return div_2by1(~d, UINT64_MAX, d, ignored);
}

static uint64_t div_2by1_preinv(uint64_t hi, uint64_t lo, uint64_t d,
                                uint64_t inverse, uint64_t &rem){
    uint64_t qh, ql;
    precn_mul_wide(hi, inverse, qh, ql);

    uint64_t estimate_low;
    uint64_t carry = precn_add_carry(ql, lo, 0, estimate_low);
    uint64_t estimate;
    precn_add_carry(qh, hi + 1, carry, estimate);

    uint64_t r = lo - estimate * d;
    if(r > estimate_low){
        --estimate;
        r += d;
    }
    if(r >= d){
        ++estimate;
        r -= d;
    }
    rem = r;
    return estimate;
}

static uint64_t div_u64_preinv_limbs_plan(uint64_t *quotient,
                                          const precn_t &a,
                                          unsigned shift, uint64_t d,
                                          uint64_t inverse){
    uint64_t rem = shift ? a.a[a.rsiz - 1] >> (64 - shift) : 0;

    for(size_t i = a.rsiz; i > 0; --i){
        size_t limb = i - 1;
        uint64_t low = a.a[limb] << shift;
        if(shift && limb) low |= a.a[limb - 1] >> (64 - shift);
        uint64_t q = div_2by1_preinv(rem, low, d, inverse, rem);
        if(quotient) quotient[limb] = q;
    }
    return shift ? rem >> shift : rem;
}

static uint64_t div_u64_preinv_limbs(uint64_t *quotient,
                                     const precn_t &a, uint64_t b){
    unsigned shift = div_clz64(b);
    uint64_t d = b << shift;
    return div_u64_preinv_limbs_plan(quotient, a, shift, d,
                                     div_inverse_normalized(d));
}

static uint64_t div_add_n(uint64_t *up, const uint64_t *vp, size_t n){
    uint64_t carry = 0;
    for(size_t i = 0; i < n; ++i){
        uint64_t out;
        carry = precn_add_carry(up[i], vp[i], carry, out);
        up[i] = out;
    }
    return carry;
}

static void div_reserve(precn_t &a, size_t n){
    if(a.asiz >= n) return;
    a.a = (uint64_t*) realloc(a.a, n * sizeof(uint64_t));
    a.asiz = n;
}

static void div_zero(precn_t &a){
    a.rsiz = 0;
    if(a.asiz == 0){
        a.asiz = 1;
        a.a = (uint64_t*) malloc(sizeof(uint64_t));
    }
    a.a[0] = 0;
}

static void div_norm(precn_t &a){
    while(a.rsiz > 0 && a.a[a.rsiz - 1] == 0) --a.rsiz;
    if(a.rsiz == 0) a.a[0] = 0;
}

void precn_div_1e10_into(precn_t &q, const precn_t &a){
    if(a.rsiz == 0){
        div_zero(q);
        return;
    }
    div_reserve(q, a.rsiz);
    q.rsiz = a.rsiz;
    div_u64_preinv_limbs_plan(q.a, a, 30, 10737418240000000000ULL,
                              13244520931996183421ULL);
    div_norm(q);
}

static uint64_t div_u64_into_impl(precn_t &q, const precn_t &a, uint64_t b){
    if(a.rsiz == 0 || b == 0){
        div_zero(q);
        return 0;
    }
    div_reserve(q, std::max<size_t>(a.rsiz, 1));
    q.rsiz = a.rsiz;

    if(b == 1){
        if(&q != &a) memcpy(q.a, a.a, a.rsiz * sizeof(uint64_t));
        return 0;
    }
    if((b & (b - 1)) == 0){
        unsigned shift = 63 - div_clz64(b);
        uint64_t rem = a.a[0] & (b - 1);
        for(size_t i = 0; i < a.rsiz; ++i){
            uint64_t high = i + 1 < a.rsiz ? a.a[i + 1] : 0;
            q.a[i] = (a.a[i] >> shift) | (high << (64 - shift));
        }
        div_norm(q);
        return rem;
    }

    uint64_t rem;
    if(a.rsiz >= DIV_U64_PREINV_THRESHOLD){
        rem = div_u64_preinv_limbs(q.a, a, b);
    }else{
        rem = 0;
        for(size_t i = a.rsiz; i > 0; --i)
            q.a[i - 1] = div_2by1(rem, a.a[i - 1], b, rem);
    }

    div_norm(q);
    return rem;
}

static void mod_u64_into_impl(precn_t &r, const precn_t &a, uint64_t b){
    if(a.rsiz == 0 || b == 0){
        div_zero(r);
        return;
    }

    uint64_t rem;
    if((b & (b - 1)) == 0){
        rem = a.a[0] & (b - 1);
    }else if(a.rsiz >= DIV_U64_PREINV_THRESHOLD){
        rem = div_u64_preinv_limbs(nullptr, a, b);
    }else{
        rem = 0;
        for(size_t i = a.rsiz; i > 0; --i){
            uint64_t ignored = div_2by1(rem, a.a[i - 1], b, rem);
            (void)ignored;
        }
    }

    div_reserve(r, 1);
    r.a[0] = rem;
    r.rsiz = rem ? 1 : 0;
}

precn_t div_u32(const precn_t &a, uint32_t b){
    return div_u64(a, b);
}

precn_t div_u64(const precn_t &a, uint64_t b){
    precn_t q = precn_t::with_capacity(a.rsiz);
    div_u64_into_impl(q, a, b);
    return q;
}

precn_t mod_u32(const precn_t &a, uint32_t b){
    return mod_u64(a, b);
}

precn_t mod_u64(const precn_t &a, uint64_t b){
    precn_t r;
    mod_u64_into_impl(r, a, b);
    return r;
}

static precn_t div_schoolbook_impl(const precn_t &a, const precn_t &b,
                                   precn_t *remainder, int want_quotient){
    if(a.rsiz == 0 || b.rsiz == 0){
        if(remainder) *remainder = precn_t();
        return precn_t();
    }
    if(div_cmp(a, b) < 0){
        if(remainder) *remainder = a;
        return precn_t();
    }
    if(b.rsiz == 1){
        if(remainder) *remainder = mod_u64(a, b.a[0]);
        return want_quotient ? div_u64(a, b.a[0]) : precn_t();
    }

    size_t n = b.rsiz;
    size_t m = a.rsiz - n;
    unsigned shift = div_clz64(b.a[n - 1]);

    uint64_t vn_stack[32];
    uint64_t un_stack[65];
    std::vector<uint64_t> vn_heap;
    std::vector<uint64_t> un_heap;
    uint64_t *vn;
    uint64_t *un;
    if(n <= 32 && a.rsiz <= 64){
        vn = vn_stack;
        un = un_stack;
        memset(un, 0, (a.rsiz + 1) * sizeof(uint64_t));
    }else{
        vn_heap.resize(n);
        un_heap.assign(a.rsiz + 1, 0);
        vn = vn_heap.data();
        un = un_heap.data();
    }

    if(shift == 0){
        memcpy(vn, b.a, n * sizeof(uint64_t));
        memcpy(un, a.a, a.rsiz * sizeof(uint64_t));
    }else{
        uint64_t carry = 0;
        for(size_t i = 0; i < n; ++i){
            uint64_t cur = (b.a[i] << shift) | carry;
            vn[i] = cur;
            carry = shift ? (b.a[i] >> (64 - shift)) : 0;
        }

        carry = 0;
        for(size_t i = 0; i < a.rsiz; ++i){
            uint64_t cur = (a.a[i] << shift) | carry;
            un[i] = cur;
            carry = shift ? (a.a[i] >> (64 - shift)) : 0;
        }
        un[a.rsiz] = carry;
    }

    precn_t q = want_quotient ? precn_t::with_capacity(m + 1) : precn_t();
    if(want_quotient){
        q.rsiz = m + 1;
    }

    for(size_t jj = m + 1; jj > 0; --jj){
        size_t j = jj - 1;
        uint64_t qhat;
        uint64_t rhat;
        bool rhat_overflow = false;
        if(un[j + n] >= vn[n - 1]){
            qhat = UINT64_MAX;
            rhat = un[j + n - 1] + vn[n - 1];
            rhat_overflow = rhat < un[j + n - 1];
        }else{
            qhat = div_2by1(un[j + n], un[j + n - 1], vn[n - 1], rhat);
        }

        uint64_t ph, pl;
        precn_mul_wide(qhat, vn[n - 2], ph, pl);
        while(!rhat_overflow && (ph > rhat || (ph == rhat && pl > un[j + n - 2]))){
            --qhat;
            uint64_t old = rhat;
            rhat += vn[n - 1];
            rhat_overflow = rhat < old;
            precn_mul_wide(qhat, vn[n - 2], ph, pl);
        }

        uint64_t borrow = div_submul_1(un + j, vn, n, qhat);

        uint64_t old_top = un[j + n];
        un[j + n] = old_top - borrow;
        if(old_top < borrow){
            --qhat;
            un[j + n] += div_add_n(un + j, vn, n);
        }

        if(want_quotient) q.a[j] = qhat;
    }

    if(want_quotient){
        while(q.rsiz > 0 && q.a[q.rsiz - 1] == 0) --q.rsiz;
        if(q.rsiz == 0) q.a[0] = 0;
    }

    if(remainder){
        precn_t r = precn_t::with_capacity(n);
        r.rsiz = n;
        if(shift == 0){
            memcpy(r.a, un, n * sizeof(uint64_t));
        }else{
            for(size_t i = 0; i < n; ++i){
                r.a[i] = (un[i] >> shift) | (un[i + 1] << (64 - shift));
            }
        }
        while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
        if(r.rsiz == 0) r.a[0] = 0;
        *remainder = r;
    }
    return want_quotient ? q : precn_t();
}

precn_t div_schoolbook(const precn_t &a, const precn_t &b){
    return div_schoolbook_impl(a, b, nullptr, 1);
}

precn_t mod_schoolbook(const precn_t &a, const precn_t &b){
    precn_t remainder;
    div_schoolbook_impl(a, b, &remainder, 0);
    return remainder;
}

precn_t operator/(const precn_t &a, const precn_t &b){
    if(b.rsiz == 1) return div_u64(a, b.a[0]);
    precn_t q;
    div_into(q, a, b);
    return q;
}

precn_t operator%(const precn_t &a, const precn_t &b){
    if(b.rsiz == 1) return mod_u64(a, b.a[0]);
    precn_t r;
    mod_into(r, a, b);
    return r;
}

void divmod_schoolbook_into(precn_t &q, precn_t &r, const precn_t &a, const precn_t &b){
    q = div_schoolbook_impl(a, b, &r, 1);
}

void divmod_into(precn_t &q, precn_t &r, const precn_t &a, const precn_t &b){
    if(&q == &r) return;
    if(&q == &a || &q == &b || &r == &a || &r == &b){
        precn_t tq, tr;
        divmod_into(tq, tr, a, b);
        q = std::move(tq);
        r = std::move(tr);
        return;
    }
    if(a.rsiz == 0 || b.rsiz == 0){
        div_zero(q);
        div_zero(r);
        return;
    }
    if(b.rsiz == 1){
        uint64_t rem = div_u64_into_impl(q, a, b.a[0]);
        div_reserve(r, 1);
        r.a[0] = rem;
        r.rsiz = rem ? 1 : 0;
        return;
    }
    if(b.rsiz >= DIV_LONG_MULINV_THRESHOLD && a.rsiz > b.rsiz * 3){
        divmod_mulinv_into(q, r, a, b);
        return;
    }
    if(b.rsiz >= DIV_DC_THRESHOLD && a.rsiz > b.rsiz * 2){
        div_dc_blocked_into(q, r, a, b);
        return;
    }
    if(b.rsiz >= DIV_DC_THRESHOLD && div_dc_into(q, r, a, b)) return;
    if(b.rsiz < DIV_MULINV_THRESHOLD){
        q = div_schoolbook_impl(a, b, &r, 1);
        return;
    }

    divmod_mulinv_into(q, r, a, b);
}

void div_into(precn_t &q, const precn_t &a, const precn_t &b){
    if(&q == &a || &q == &b){
        precn_t t;
        div_into(t, a, b);
        q = std::move(t);
        return;
    }
    if(a.rsiz == 0 || b.rsiz == 0){
        div_zero(q);
        return;
    }
    if(b.rsiz == 1){
        div_u64_into_impl(q, a, b.a[0]);
        return;
    }
    if(b.rsiz >= DIV_LONG_MULINV_THRESHOLD && a.rsiz > b.rsiz * 3){
        q = div_mulinv(a, b);
        return;
    }
    if(b.rsiz >= DIV_DC_THRESHOLD && a.rsiz > b.rsiz * 2){
        precn_t r;
        div_dc_blocked_into(q, r, a, b);
        return;
    }
    if(b.rsiz >= DIV_DC_THRESHOLD){
        precn_t r;
        if(div_dc_into(q, r, a, b)) return;
    }
    q = b.rsiz >= DIV_MULINV_THRESHOLD ? div_mulinv(a, b) : div_schoolbook(a, b);
}

void mod_into(precn_t &r, const precn_t &a, const precn_t &b){
    if(&r == &a || &r == &b){
        precn_t t;
        mod_into(t, a, b);
        r = std::move(t);
        return;
    }
    if(a.rsiz == 0 || b.rsiz == 0){
        div_zero(r);
        return;
    }
    if(b.rsiz == 1){
        mod_u64_into_impl(r, a, b.a[0]);
        return;
    }
    if(b.rsiz >= DIV_LONG_MULINV_THRESHOLD && a.rsiz > b.rsiz * 3){
        r = mod_mulinv(a, b);
        return;
    }
    if(b.rsiz >= DIV_DC_THRESHOLD && a.rsiz > b.rsiz * 2){
        precn_t q;
        div_dc_blocked_into(q, r, a, b);
        return;
    }
    if(b.rsiz >= DIV_DC_THRESHOLD){
        precn_t q;
        if(div_dc_into(q, r, a, b)) return;
    }
    r = b.rsiz >= DIV_MULINV_THRESHOLD ? mod_mulinv(a, b) : mod_schoolbook(a, b);
}
