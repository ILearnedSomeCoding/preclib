#include"../prec.hpp"
#include"toom_cook_ptr.hpp"

#define MUL_TOOM22_THRESHOLD 64
#define MUL_TOOMX2_THRESHOLD 64
#define MUL_TOOM33_THRESHOLD 256
#define MUL_FFT_THRESHOLD 1736

struct sprecn_t{
    int neg;
    precn_t v;
};

static size_t toom_trim(ptr_len x){
    while(x.siz > 0 && x.a[x.siz - 1] == 0) --x.siz;
    return x.siz;
}

static int toom_cmp(const precn_t &a, const precn_t &b){
    if(a.rsiz != b.rsiz) return a.rsiz < b.rsiz ? -1 : 1;
    for(size_t i = a.rsiz; i > 0; --i){
        if(a.a[i - 1] != b.a[i - 1]) return a.a[i - 1] < b.a[i - 1] ? -1 : 1;
    }
    return 0;
}

static precn_t toom_from_ptr(ptr_len x){
    x.siz = toom_trim(x);
    precn_t r;
    r.asiz = std::max<size_t>(x.siz, 1);
    r.a = (uint64_t*) realloc(r.a, r.asiz * sizeof(uint64_t));
    r.rsiz = x.siz;
    if(x.siz) memcpy(r.a, x.a, x.siz * sizeof(uint64_t));
    else r.a[0] = 0;
    return r;
}

precn_t precn_divexact_2(const precn_t &a){
    precn_t r;
    r.asiz = std::max<size_t>(a.rsiz, 1);
    r.a = (uint64_t*) realloc(r.a, r.asiz * sizeof(uint64_t));
    r.rsiz = a.rsiz;

    uint64_t carry = 0;
    for(size_t i = a.rsiz; i > 0; --i){
        r.a[i - 1] = (a.a[i - 1] >> 1) | (carry << 63);
        carry = a.a[i - 1] & 1;
    }

    while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}

precn_t precn_divexact_3(const precn_t &a){
    if(a.rsiz == 0) return precn_t();

    // 3^-1 modulo 2^64.  The carry is only 0, 1, or 2, so this replaces a
    // full long division with one multiply and a few carries per limb.
    const uint64_t inverse_3 = 0xAAAAAAAAAAAAAAABULL;
    precn_t r;
    r.asiz = a.rsiz;
    r.a = (uint64_t*) realloc(r.a, r.asiz * sizeof(uint64_t));
    r.rsiz = a.rsiz;

    uint64_t carry = 0;
    for(size_t i = 0; i < a.rsiz; ++i){
        uint64_t x = a.a[i] - carry;
        carry = x > a.a[i];
        uint64_t q = x * inverse_3;
        r.a[i] = q;

        uint64_t twice = q + q;
        carry += twice < q;
        uint64_t thrice = twice + q;
        carry += thrice < twice;
    }

    while(r.rsiz && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}

static precn_t toom_basic(ptr_len a, ptr_len b){
    a.siz = toom_trim(a);
    b.siz = toom_trim(b);
    if(a.siz == 0 || b.siz == 0) return precn_t();

    precn_t r;
    r.asiz = a.siz + b.siz + 1;
    r.a = (uint64_t*) realloc(r.a, r.asiz * sizeof(uint64_t));
    memset(r.a, 0, r.asiz * sizeof(uint64_t));
    r.rsiz = a.siz + b.siz;

    for(size_t i = 0; i < a.siz; ++i){
        uint64_t carry = 0;
        for(size_t j = 0; j < b.siz; ++j){
            size_t k = i + j;
            uint64_t prod = (uint64_t)a.a[i] * b.a[j] + r.a[k] + carry;
            r.a[k] = (uint32_t)(prod & 0xFFFFFFFFu);
            carry = prod >> 32;
        }

        size_t k = i + b.siz;
        while(carry){
            uint64_t sum = (uint64_t)r.a[k] + carry;
            r.a[k] = (uint32_t)(sum & 0xFFFFFFFFu);
            carry = sum >> 32;
            ++k;
        }
    }

    while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}

static sprecn_t sp_make(precn_t v, int neg = 0){
    int sign = v.rsiz == 0 ? 0 : neg;
    return sprecn_t{sign, std::move(v)};
}

static sprecn_t sp_add(const sprecn_t &a, const sprecn_t &b){
    if(a.neg == b.neg) return sp_make(a.v + b.v, a.neg);

    int c = toom_cmp(a.v, b.v);
    if(c == 0) return sp_make(precn_t());
    if(c > 0) return sp_make(a.v - b.v, a.neg);
    return sp_make(b.v - a.v, b.neg);
}

static sprecn_t sp_sub(const sprecn_t &a, const sprecn_t &b){
    if(a.neg != b.neg) return sp_make(a.v + b.v, a.neg);

    int c = toom_cmp(a.v, b.v);
    if(c == 0) return sp_make(precn_t());
    if(c > 0) return sp_make(a.v - b.v, a.neg);
    return sp_make(b.v - a.v, !a.neg);
}

static sprecn_t sp_mul_u32(const sprecn_t &a, uint32_t b){
    return sp_make(mul_u32(a.v, b), a.neg);
}

static sprecn_t sp_divexact_2(const sprecn_t &a){
    return sp_make(precn_divexact_2(a.v), a.neg);
}

static sprecn_t sp_divexact_3(const sprecn_t &a){
    return sp_make(precn_divexact_3(a.v), a.neg);
}

static sprecn_t sp_divexact_den(sprecn_t a, long long d){
    while(d % 2 == 0){
        a = sp_divexact_2(a);
        d /= 2;
    }
    while(d % 3 == 0){
        a = sp_divexact_3(a);
        d /= 3;
    }
    return a;
}

static void toom_norm(precn_t &a){
    while(a.rsiz > 0 && a.a[a.rsiz - 1] == 0) --a.rsiz;
    if(a.rsiz == 0 && a.asiz) a.a[0] = 0;
}

static void toom_reserve(precn_t &a, size_t n){
    if(a.asiz >= n) return;
    a.a = (uint64_t*) realloc(a.a, n * sizeof(uint64_t));
    memset(a.a + a.asiz, 0, (n - a.asiz) * 4);
    a.asiz = n;
}

static int toom_cmp_shift(const precn_t &a, const precn_t &b, size_t shift){
    size_t as = a.rsiz;
    size_t bs = b.rsiz ? b.rsiz + shift : 0;
    if(as != bs) return as < bs ? -1 : 1;
    for(size_t i = as; i > 0; --i){
        uint32_t av = a.a[i - 1];
        uint32_t bv = (i - 1 >= shift && i - 1 - shift < b.rsiz) ? b.a[i - 1 - shift] : 0;
        if(av != bv) return av < bv ? -1 : 1;
    }
    return 0;
}

static void toom_add_shift(precn_t &a, const precn_t &b, size_t shift){
    if(b.rsiz == 0) return;
    size_t need = std::max(a.rsiz, b.rsiz + shift) + 1;
    toom_reserve(a, need);
    if(a.rsiz < need) memset(a.a + a.rsiz, 0, (need - a.rsiz) * 4);

    uint64_t carry = 0;
    size_t i = 0;
    for(; i < b.rsiz; ++i){
        uint64_t sum = (uint64_t)a.a[i + shift] + b.a[i] + carry;
        a.a[i + shift] = (uint32_t)(sum & 0xFFFFFFFFu);
        carry = sum >> 32;
    }
    i += shift;
    while(carry){
        uint64_t sum = (uint64_t)a.a[i] + carry;
        a.a[i] = (uint32_t)(sum & 0xFFFFFFFFu);
        carry = sum >> 32;
        ++i;
    }
    a.rsiz = need;
    toom_norm(a);
}

static void toom_sub_shift_ge(precn_t &a, const precn_t &b, size_t shift){
    uint64_t borrow = 0;
    size_t i = 0;
    for(; i < b.rsiz; ++i){
        uint64_t av = a.a[i + shift];
        uint64_t sub = (uint64_t)b.a[i] + borrow;
        if(av < sub){
            a.a[i + shift] = (uint32_t)((1ULL << 32) + av - sub);
            borrow = 1;
        }else{
            a.a[i + shift] = (uint32_t)(av - sub);
            borrow = 0;
        }
    }
    i += shift;
    while(borrow){
        if(a.a[i]){
            --a.a[i];
            borrow = 0;
        }else{
            a.a[i] = 0xFFFFFFFFu;
            ++i;
        }
    }
    toom_norm(a);
}

static precn_t toom_shift(const precn_t &a, size_t limbs){
    precn_t r;
    if(a.rsiz == 0) return r;
    r.asiz = a.rsiz + limbs;
    r.a = (uint64_t*) realloc(r.a, r.asiz * sizeof(uint64_t));
    memset(r.a, 0, limbs * sizeof(uint64_t));
    memcpy(r.a + limbs, a.a, a.rsiz * sizeof(uint64_t));
    r.rsiz = a.rsiz + limbs;
    return r;
}

static sprecn_t sp_add_shift(sprecn_t a, const sprecn_t &b, size_t shift){
    if(b.v.rsiz == 0) return a;
    if(a.v.rsiz == 0) return sp_make(toom_shift(b.v, shift), b.neg);

    if(a.neg == b.neg){
        toom_add_shift(a.v, b.v, shift);
        return sp_make(std::move(a.v), a.neg);
    }

    int c = toom_cmp_shift(a.v, b.v, shift);
    if(c == 0) return sp_make(precn_t());
    if(c > 0){
        toom_sub_shift_ge(a.v, b.v, shift);
        return sp_make(std::move(a.v), a.neg);
    }

    precn_t r = toom_shift(b.v, shift);
    toom_sub_shift_ge(r, a.v, 0);
    return sp_make(std::move(r), b.neg);
}

static precn_t toom_mul(ptr_len a, ptr_len b);

static sprecn_t sp_mul(const sprecn_t &a, const sprecn_t &b){
    if(a.v.rsiz == 0 || b.v.rsiz == 0) return sp_make(precn_t());
    ptr_len ap = {a.v.rsiz, a.v.a};
    ptr_len bp = {b.v.rsiz, b.v.a};
    return sp_make(toom_mul(ap, bp), a.neg != b.neg);
}

static ptr_len toom_part(ptr_len a, size_t id, size_t k){
    size_t off = id * k;
    if(off >= a.siz) return ptr_len{0, a.a + a.siz};
    return ptr_len{std::min(k, a.siz - off), a.a + off};
}

static sprecn_t toom_eval_p1(precn_t *p, size_t n){
    precn_t r;
    for(size_t i = 0; i < n; ++i) r = r + p[i];
    return sp_make(r);
}

static sprecn_t toom_eval_m1(precn_t *p, size_t n){
    sprecn_t r = sp_make(precn_t());
    for(size_t i = 0; i < n; ++i){
        sprecn_t term = sp_make(p[i]);
        if(i & 1) term.neg = !term.neg;
        r = sp_add(r, term);
    }
    return r;
}

static sprecn_t toom_eval_p2(precn_t *p, size_t n){
    precn_t r;
    uint32_t c = 1;
    for(size_t i = 0; i < n; ++i){
        r = r + mul_u32(p[i], c);
        c <<= 1;
    }
    return sp_make(r);
}

static precn_t toom_interpolate(sprecn_t *y, size_t n, size_t k){
    sprecn_t coef[5];
    for(size_t i = 0; i < n; ++i) coef[i] = sp_make(precn_t());

    coef[0] = y[0];
    if(n == 4){
        coef[3] = y[3];
        sprecn_t a = sp_sub(sp_sub(y[1], y[0]), coef[3]);
        sprecn_t b = sp_add(sp_sub(y[2], y[0]), coef[3]);

        coef[2] = sp_divexact_2(sp_add(a, b));
        coef[1] = sp_sub(a, coef[2]);
    }else{
        coef[4] = y[4];
        sprecn_t a = sp_sub(sp_sub(y[1], y[0]), coef[4]);
        sprecn_t b = sp_sub(sp_sub(y[2], y[0]), coef[4]);
        sprecn_t c = sp_sub(sp_sub(y[3], y[0]), sp_mul_u32(coef[4], 16));
        sprecn_t s = sp_divexact_2(sp_add(a, b));
        sprecn_t t = sp_divexact_2(sp_sub(a, b));

        coef[2] = s;
        coef[3] = sp_divexact_3(sp_sub(sp_sub(sp_divexact_2(c), t), sp_mul_u32(s, 2)));
        coef[1] = sp_sub(t, coef[3]);
    }

    sprecn_t ans = sp_make(precn_t());
    for(size_t i = 0; i < n; ++i){
        ans = sp_add_shift(std::move(ans), coef[i], i * k);
    }
    return ans.neg ? precn_t() : ans.v;
}

static precn_t toom_pq(ptr_len a, ptr_len b, size_t pa, size_t pb){
    a.siz = toom_trim(a);
    b.siz = toom_trim(b);
    if(a.siz == 0 || b.siz == 0) return precn_t();
    if(std::min(a.siz, b.siz) < MUL_TOOM22_THRESHOLD) return toom_basic(a, b);

    size_t k = std::max((a.siz + pa - 1) / pa, (b.siz + pb - 1) / pb);
    ptr_len ap[4], bp[4];
    for(size_t i = 0; i < pa; ++i) ap[i] = toom_part(a, i, k);
    for(size_t i = 0; i < pb; ++i) bp[i] = toom_part(b, i, k);

    precn_t av[4], bv[4];
    for(size_t i = 0; i < pa; ++i) av[i] = toom_from_ptr(ap[i]);
    for(size_t i = 0; i < pb; ++i) bv[i] = toom_from_ptr(bp[i]);

    size_t n = pa + pb - 1;
    sprecn_t y[5];

    y[0] = sp_mul(sp_make(av[0]), sp_make(bv[0]));
    y[1] = sp_mul(toom_eval_p1(av, pa), toom_eval_p1(bv, pb));
    y[2] = sp_mul(toom_eval_m1(av, pa), toom_eval_m1(bv, pb));
    if(n == 5) y[3] = sp_mul(toom_eval_p2(av, pa), toom_eval_p2(bv, pb));
    y[n - 1] = sp_mul(sp_make(av[pa - 1]), sp_make(bv[pb - 1]));

    return toom_interpolate(y, n, k);
}

static precn_t toom_mul(ptr_len a, ptr_len b){
    a.siz = toom_trim(a);
    b.siz = toom_trim(b);
    if(a.siz == 0 || b.siz == 0) return precn_t();

    size_t lo = std::min(a.siz, b.siz);
    size_t hi = std::max(a.siz, b.siz);
    if(lo < MUL_TOOM22_THRESHOLD || (lo < MUL_TOOMX2_THRESHOLD && hi * 4 < lo * 5)){
        return toom_basic(a, b);
    }

    if(hi * 4 < lo * 5){
        if(lo < MUL_TOOM33_THRESHOLD) return mul_karatsuba(toom_from_ptr(a), toom_from_ptr(b));
        return toom_pq(a, b, 3, 3);
    }

    if(lo < MUL_TOOMX2_THRESHOLD) return toom_basic(a, b);
    if(hi * 5 < lo * 9) return a.siz <= b.siz ? toom_pq(a, b, 2, 3) : toom_pq(b, a, 2, 3);
    return a.siz <= b.siz ? toom_pq(a, b, 2, 4) : toom_pq(b, a, 2, 4);
}

static precn_t toom64_slice(const precn_t &a, size_t start, size_t n){
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

static sprecn_t toom64_mul(const sprecn_t &a, const sprecn_t &b){
    return sp_make(a.v * b.v, a.neg != b.neg);
}

static sprecn_t toom64_shift(const sprecn_t &a, size_t limbs){
    return sp_make(a.v << (limbs * 64), a.neg);
}

static precn_t toom64_33(const precn_t &a, const precn_t &b){
    if(a.rsiz == 0 || b.rsiz == 0) return precn_t();
    size_t lo = std::min(a.rsiz, b.rsiz);
    size_t hi = std::max(a.rsiz, b.rsiz);
    if(lo < 64 || hi > lo * 2) return mul_karatsuba(a, b);

    size_t k = (hi + 2) / 3;
    precn_t ap[3] = {
        toom64_slice(a, 0, k), toom64_slice(a, k, k), toom64_slice(a, 2 * k, k)
    };
    precn_t bp[3] = {
        toom64_slice(b, 0, k), toom64_slice(b, k, k), toom64_slice(b, 2 * k, k)
    };

    sprecn_t am1 = sp_add(sp_sub(sp_make(ap[0]), sp_make(ap[1])), sp_make(ap[2]));
    sprecn_t bm1 = sp_add(sp_sub(sp_make(bp[0]), sp_make(bp[1])), sp_make(bp[2]));
    precn_t ap1 = ap[0] + ap[1] + ap[2];
    precn_t bp1 = bp[0] + bp[1] + bp[2];
    precn_t ap2 = ap[0] + mul_u32(ap[1], 2) + mul_u32(ap[2], 4);
    precn_t bp2 = bp[0] + mul_u32(bp[1], 2) + mul_u32(bp[2], 4);

    sprecn_t w0 = toom64_mul(sp_make(ap[0]), sp_make(bp[0]));
    sprecn_t w1 = toom64_mul(sp_make(ap1), sp_make(bp1));
    sprecn_t wm1 = toom64_mul(am1, bm1);
    sprecn_t w2 = toom64_mul(sp_make(ap2), sp_make(bp2));
    sprecn_t w4 = toom64_mul(sp_make(ap[2]), sp_make(bp[2]));

    sprecn_t c0 = w0;
    sprecn_t c4 = w4;
    sprecn_t c2 = sp_sub(sp_sub(sp_divexact_2(sp_add(w1, wm1)), c0), c4);
    sprecn_t c1c3 = sp_divexact_2(sp_sub(w1, wm1));
    sprecn_t half_w2 = sp_divexact_2(sp_sub(sp_sub(w2, c0), sp_mul_u32(c4, 16)));
    sprecn_t c3 = sp_divexact_3(sp_sub(sp_sub(half_w2, c1c3), sp_mul_u32(c2, 2)));
    sprecn_t c1 = sp_sub(c1c3, c3);

    sprecn_t out = c0;
    out = sp_add(out, toom64_shift(c1, k));
    out = sp_add(out, toom64_shift(c2, 2 * k));
    out = sp_add(out, toom64_shift(c3, 3 * k));
    out = sp_add(out, toom64_shift(c4, 4 * k));
    return out.neg ? precn_t() : out.v;
}

precn_t mul_toom23(const precn_t &a, const precn_t &b){
    return toom64_33(a, b);
}

precn_t mul_toom24(const precn_t &a, const precn_t &b){
    return toom64_33(a, b);
}

precn_t mul_toom33(const precn_t &a, const precn_t &b){
    return toom64_33(a, b);
}

precn_t mul_toom(const precn_t &a, const precn_t &b){
    return toom64_33(a, b);
}
