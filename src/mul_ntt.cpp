#include"../prec.hpp"

#include<vector>

#if defined(__AVX2__) || defined(_M_AVX2)
#include<immintrin.h>
#define PRECN_NTT_HAVE_AVX2 1
#else
#define PRECN_NTT_HAVE_AVX2 0
#endif

struct mont_ctx_t{
    uint32_t mod;
    uint32_t root;
    uint32_t ninv;
    uint32_t r2;
    uint32_t one;
};

struct ntt_mod_plan_t{
    mont_ctx_t c;
    uint32_t inv_n;
    std::vector<uint32_t> roots;
};

static const size_t NTT_MAX_LIMBS = (size_t)1 << 24;
static const size_t NTT_MAX_TRANSFORM = (size_t)1 << 26;
static const uint32_t NTT_MOD1 = 469762049u;
static const uint32_t NTT_MOD2 = 1811939329u;
static const uint32_t NTT_MOD3 = 2013265921u;
static const uint32_t NTT_ROOT1 = 3u;
static const uint32_t NTT_ROOT2 = 13u;
static const uint32_t NTT_ROOT3 = 31u;
static const uint64_t NTT_DIGIT_MAX2 = 0xFFFFULL * 0xFFFFULL;

static const mont_ctx_t NTT_CTX[] = {
    {469762049u, 3u, 469762047u, 460175152u, 67108855u},
    {1811939329u, 13u, 1811939327u, 959408210u, 671088638u},
    {2013265921u, 31u, 2013265919u, 1172168163u, 268435454u},
};

static uint32_t mont_reduce(const mont_ctx_t &c, uint64_t x){
    uint32_t m = (uint32_t)x * c.ninv;
    uint64_t t = (x + (uint64_t)m * c.mod) >> 32;
    if(t >= c.mod) t -= c.mod;
    return (uint32_t)t;
}

static uint32_t mont_in(const mont_ctx_t &c, uint32_t x){
    return mont_reduce(c, (uint64_t)(x % c.mod) * c.r2);
}

static uint32_t mont_mul(const mont_ctx_t &c, uint32_t a, uint32_t b){
    return mont_reduce(c, (uint64_t)a * b);
}

#if PRECN_NTT_HAVE_AVX2
static __m256i ntt_load4_u32(const uint32_t *p){
    return _mm256_cvtepu32_epi64(_mm_loadu_si128((const __m128i*)p));
}

static void ntt_store4_u32(uint32_t *p, __m256i x){
    alignas(32) uint64_t t[4];
    _mm256_store_si256((__m256i*)t, x);
    p[0] = (uint32_t)t[0];
    p[1] = (uint32_t)t[1];
    p[2] = (uint32_t)t[2];
    p[3] = (uint32_t)t[3];
}

static __m256i mont_reduce4(const mont_ctx_t &c, __m256i x){
    __m256i ninv = _mm256_set1_epi64x((long long)c.ninv);
    __m256i mod = _mm256_set1_epi64x((long long)c.mod);
    __m256i m = _mm256_mul_epu32(x, ninv);
    __m256i t = _mm256_srli_epi64(_mm256_add_epi64(x, _mm256_mul_epu32(m, mod)), 32);
    __m256i ge = _mm256_cmpgt_epi64(t, _mm256_set1_epi64x((long long)c.mod - 1));
    return _mm256_sub_epi64(t, _mm256_and_si256(ge, mod));
}

static __m256i mont_mul4(const mont_ctx_t &c, __m256i a, __m256i b){
    return mont_reduce4(c, _mm256_mul_epu32(a, b));
}

static void mont_mul4_store(uint32_t *out, const uint32_t *a, const uint32_t *b,
                            const mont_ctx_t &c){
    ntt_store4_u32(out, mont_mul4(c, ntt_load4_u32(a), ntt_load4_u32(b)));
}
#endif

static mont_ctx_t mont_make(uint32_t mod, uint32_t root){
    for(size_t i = 0; i < sizeof(NTT_CTX) / sizeof(NTT_CTX[0]); ++i){
        if(NTT_CTX[i].mod == mod && NTT_CTX[i].root == root) return NTT_CTX[i];
    }
    fprintf(stderr, "mul_ntt tantrum: missing Montgomery constants for mod %u root %u\n", mod, root);
    abort();
}

static uint32_t mont_pow(const mont_ctx_t &c, uint32_t a, uint64_t e){
    uint32_t r = c.one;
    uint32_t x = mont_in(c, a);
    while(e){
        if(e & 1) r = mont_mul(c, r, x);
        e >>= 1;
        if(e) x = mont_mul(c, x, x);
    }
    return r;
}

static void ntt_build_rev(std::vector<uint32_t> &rev, size_t n){
    rev.resize(n);
    size_t bits = 0;
    while(((size_t)1 << bits) < n) ++bits;
    rev[0] = 0;
    for(size_t i = 1; i < n; ++i){
        rev[i] = (rev[i >> 1] >> 1) | (uint32_t)((i & 1) << (bits - 1));
    }
}

static void ntt_build_roots(std::vector<uint32_t> &roots, const mont_ctx_t &c, size_t n, int inv){
    roots.resize(n);
    if(n) roots[0] = c.one;
    for(size_t len = 2; len <= n; len <<= 1){
        size_t half = len >> 1;
        uint64_t e = (c.mod - 1) / len;
        if(inv) e = (uint64_t)c.mod - 1 - e;
        uint32_t wlen = mont_pow(c, c.root, e);
        uint32_t w = c.one;
        for(size_t i = 0; i < half; ++i){
            roots[half + i] = w;
            w = mont_mul(c, w, wlen);
        }
    }
}

static ntt_mod_plan_t ntt_make_mod_plan(size_t n, uint32_t mod, uint32_t root){
    ntt_mod_plan_t p;
    p.c = mont_make(mod, root);
    p.inv_n = mont_pow(p.c, (uint32_t)(n % mod), mod - 2);
    return p;
}

static void ntt(std::vector<uint32_t> &a, int inv, const ntt_mod_plan_t &p,
                const std::vector<uint32_t> &rev){
    size_t n = a.size();
    const mont_ctx_t &c = p.c;
    const std::vector<uint32_t> &roots = p.roots;
    uint32_t mod = c.mod;

    for(size_t i = 1; i < n; ++i){
        size_t j = rev[i];
        if(i < j) std::swap(a[i], a[j]);
    }

    for(size_t len = 2; len <= n; len <<= 1){
        size_t half = len >> 1;
        for(size_t i = 0; i < n; i += len){
            size_t j = 0;
#if PRECN_NTT_HAVE_AVX2
            __m256i mod4 = _mm256_set1_epi64x((long long)mod);
            __m256i modm1 = _mm256_set1_epi64x((long long)mod - 1);
            __m256i all = _mm256_cmpeq_epi64(mod4, mod4);
            for(; j + 3 < half; j += 4){
                uint32_t *lo = a.data() + i + j;
                uint32_t *hi = lo + half;
                __m256i u = ntt_load4_u32(lo);
                __m256i v = mont_mul4(c, ntt_load4_u32(hi), ntt_load4_u32(roots.data() + half + j));

                __m256i s = _mm256_add_epi64(u, v);
                __m256i s_ge = _mm256_cmpgt_epi64(s, modm1);
                s = _mm256_sub_epi64(s, _mm256_and_si256(s_ge, mod4));

                __m256i d_plain = _mm256_sub_epi64(u, v);
                __m256i d_wrap = _mm256_sub_epi64(_mm256_add_epi64(u, mod4), v);
                __m256i v_gt_u = _mm256_cmpgt_epi64(v, u);
                __m256i u_ge_v = _mm256_xor_si256(v_gt_u, all);
                __m256i d = _mm256_or_si256(_mm256_and_si256(u_ge_v, d_plain),
                                            _mm256_andnot_si256(u_ge_v, d_wrap));

                ntt_store4_u32(lo, s);
                ntt_store4_u32(hi, d);
            }
#endif
            for(; j < half; ++j){
                uint32_t u = a[i + j];
                uint32_t v = mont_mul(c, a[i + j + half], roots[half + j]);

                uint32_t s = u + v;
                if(s >= mod) s -= mod;
                uint32_t d = u >= v ? u - v : u + mod - v;

                a[i + j] = s;
                a[i + j + half] = d;
            }
        }
    }

    if(inv){
        uint32_t inv_n = p.inv_n;
        size_t i = 0;
#if PRECN_NTT_HAVE_AVX2
        __m256i inv4 = _mm256_set1_epi64x((long long)inv_n);
        for(; i + 3 < n; i += 4){
            ntt_store4_u32(a.data() + i, mont_mul4(c, ntt_load4_u32(a.data() + i), inv4));
        }
#endif
        for(; i < n; ++i) a[i] = mont_mul(c, a[i], inv_n);
    }
}

static std::vector<uint32_t> ntt_digits(const precn_t &a){
    std::vector<uint32_t> d;
    d.reserve(a.rsiz * 2);
    for(size_t i = 0; i < a.rsiz; ++i){
        d.push_back(a.a[i] & 0xFFFFu);
        d.push_back(a.a[i] >> 16);
    }
    while(!d.empty() && d.back() == 0) d.pop_back();
    return d;
}

static void ntt_zero(std::vector<uint32_t> &a, size_t n){
    a.resize(n);
    memset(a.data(), 0, n * 4);
}

static void ntt_convolve_mod(const std::vector<uint32_t> &a,
                             const std::vector<uint32_t> &b,
                             size_t n,
                             uint32_t mod,
                             uint32_t root,
                             const std::vector<uint32_t> &rev,
                             std::vector<uint32_t> &out,
                             std::vector<uint32_t> &scratch){
    ntt_mod_plan_t p = ntt_make_mod_plan(n, mod, root);
    ntt_zero(out, n);
    ntt_zero(scratch, n);
    for(size_t i = 0; i < a.size(); ++i) out[i] = mont_in(p.c, a[i]);
    for(size_t i = 0; i < b.size(); ++i) scratch[i] = mont_in(p.c, b[i]);

    ntt_build_roots(p.roots, p.c, n, 0);
    ntt(out, 0, p, rev);
    ntt(scratch, 0, p, rev);
    size_t i = 0;
#if PRECN_NTT_HAVE_AVX2
    for(; i + 3 < n; i += 4) mont_mul4_store(out.data() + i, out.data() + i, scratch.data() + i, p.c);
#endif
    for(; i < n; ++i) out[i] = mont_mul(p.c, out[i], scratch[i]);
    ntt_build_roots(p.roots, p.c, n, 1);
    ntt(out, 1, p, rev);

    i = 0;
#if PRECN_NTT_HAVE_AVX2
    for(; i + 3 < n; i += 4){
        ntt_store4_u32(out.data() + i, mont_reduce4(p.c, ntt_load4_u32(out.data() + i)));
    }
#endif
    for(; i < n; ++i) out[i] = mont_reduce(p.c, out[i]);
}

static uint32_t mod_inv_u32(uint64_t a, uint32_t mod){
    long long t = 0, nt = 1;
    long long r = mod, nr = (long long)(a % mod);
    while(nr){
        long long q = r / nr;
        long long ot = t;
        t = nt;
        nt = ot - q * nt;
        long long orr = r;
        r = nr;
        nr = orr - q * nr;
    }
    if(t < 0) t += mod;
    return (uint32_t)t;
}

static uint64_t ntt_crt2(uint32_t r1, uint32_t r2){
    static uint32_t inv_m1_m2 = mod_inv_u32(NTT_MOD1, NTT_MOD2);
    uint64_t x1 = r1;
    uint64_t x1_m2 = x1 % NTT_MOD2;
    uint64_t d2 = r2 >= x1_m2 ? r2 - x1_m2 : r2 + (uint64_t)NTT_MOD2 - x1_m2;
    uint64_t t2 = d2 * inv_m1_m2 % NTT_MOD2;
    return x1 + (uint64_t)NTT_MOD1 * t2;
}

static uint64_t ntt_crt3(uint32_t r1, uint32_t r2, uint32_t r3){
    const uint64_t m1m2 = (uint64_t)NTT_MOD1 * NTT_MOD2;
    static uint32_t inv_m1m2_m3 = mod_inv_u32(((uint64_t)NTT_MOD1 * NTT_MOD2) % NTT_MOD3, NTT_MOD3);

    uint64_t x12 = ntt_crt2(r1, r2);
    uint64_t t2 = (x12 - r1) / NTT_MOD1;
    uint64_t x12_m3 = ((uint64_t)r1 % NTT_MOD3 + (uint64_t)(NTT_MOD1 % NTT_MOD3) * (t2 % NTT_MOD3) % NTT_MOD3) % NTT_MOD3;
    uint64_t d3 = r3 >= x12_m3 ? r3 - x12_m3 : r3 + (uint64_t)NTT_MOD3 - x12_m3;
    uint64_t t3 = d3 * inv_m1m2_m3 % NTT_MOD3;
    return x12 + m1m2 * t3;
}

static void ntt_put_digit(precn_t &r, size_t id, uint32_t digit){
    size_t limb = id >> 1;
    if(limb >= r.asiz){
        size_t old = r.asiz;
        while(r.asiz <= limb) r.asiz <<= 1;
        r.a = (uint32_t*) realloc(r.a, r.asiz * 4);
        memset(r.a + old, 0, (r.asiz - old) * 4);
    }
    if(id & 1) r.a[limb] = (r.a[limb] & 0x0000FFFFu) | (digit << 16);
    else r.a[limb] = (r.a[limb] & 0xFFFF0000u) | digit;
    if(r.rsiz < limb + 1) r.rsiz = limb + 1;
}

static precn_t ntt_from_residues2(const std::vector<uint32_t> &r1,
                                  const std::vector<uint32_t> &r2){
    precn_t r;
    r.asiz = r1.size() / 2 + 8;
    r.a = (uint32_t*) realloc(r.a, r.asiz * 4);
    memset(r.a, 0, r.asiz * 4);
    r.rsiz = 0;

    uint64_t carry = 0;
    size_t digit_id = 0;
    for(size_t i = 0; i < r1.size(); ++i, ++digit_id){
        uint64_t cur = ntt_crt2(r1[i], r2[i]) + carry;
        ntt_put_digit(r, digit_id, (uint32_t)(cur & 0xFFFFu));
        carry = cur >> 16;
    }
    while(carry){
        ntt_put_digit(r, digit_id++, (uint32_t)(carry & 0xFFFFu));
        carry >>= 16;
    }

    while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}

static precn_t ntt_from_residues3(const std::vector<uint32_t> &r1,
                                  const std::vector<uint32_t> &r2,
                                  const std::vector<uint32_t> &r3){
    precn_t r;
    r.asiz = r1.size() / 2 + 8;
    r.a = (uint32_t*) realloc(r.a, r.asiz * 4);
    memset(r.a, 0, r.asiz * 4);
    r.rsiz = 0;

    uint64_t carry = 0;
    size_t digit_id = 0;
    for(size_t i = 0; i < r1.size(); ++i, ++digit_id){
        uint64_t cur = ntt_crt3(r1[i], r2[i], r3[i]) + carry;
        ntt_put_digit(r, digit_id, (uint32_t)(cur & 0xFFFFu));
        carry = cur >> 16;
    }
    while(carry){
        ntt_put_digit(r, digit_id++, (uint32_t)(carry & 0xFFFFu));
        carry >>= 16;
    }

    while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}

static int ntt_two_mod_ok(size_t terms){
    uint64_t m12 = (uint64_t)NTT_MOD1 * NTT_MOD2;
    return terms <= (m12 - 1) / NTT_DIGIT_MAX2;
}

precn_t mul_ntt(const precn_t &a, const precn_t &b){
    if(a.rsiz == 0 || b.rsiz == 0) return precn_t();
    size_t limbs = std::max(a.rsiz, b.rsiz);
    if(limbs > NTT_MAX_LIMBS) return mul_fft(a, b);

    std::vector<uint32_t> da = ntt_digits(a);
    std::vector<uint32_t> db = ntt_digits(b);
    if(da.empty() || db.empty()) return precn_t();

    size_t n = 1;
    while(n < da.size() + db.size()) n <<= 1;
    if(n > NTT_MAX_TRANSFORM) return mul_fft(a, b);

    std::vector<uint32_t> rev;
    ntt_build_rev(rev, n);

    std::vector<uint32_t> r1, r2, r3, scratch;
    ntt_convolve_mod(da, db, n, NTT_MOD1, NTT_ROOT1, rev, r1, scratch);
    ntt_convolve_mod(da, db, n, NTT_MOD2, NTT_ROOT2, rev, r2, scratch);

    if(ntt_two_mod_ok(std::min(da.size(), db.size()))){
        return ntt_from_residues2(r1, r2);
    }

    ntt_convolve_mod(da, db, n, NTT_MOD3, NTT_ROOT3, rev, r3, scratch);
    return ntt_from_residues3(r1, r2, r3);
}
