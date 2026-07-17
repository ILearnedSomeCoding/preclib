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
    std::vector<uint32_t> roots_f;
    std::vector<uint32_t> roots_i;
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
    // All callers pass either a base-2^16 digit, a root, or n % mod.
    // Therefore x is already reduced; a hardware division here dominated
    // transform setup for large operands.
    return mont_reduce(c, (uint64_t)x * c.r2);
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

static __m256i ntt_pack_even_odd(__m256i even, __m256i odd){
    return _mm256_blend_epi32(even, _mm256_slli_epi64(odd, 32), 0xAA);
}

static __m256i mont_mul8(const mont_ctx_t &c, __m256i a, __m256i b){
    __m256i even = mont_reduce4(c, _mm256_mul_epu32(a, b));
    __m256i odd = mont_reduce4(c, _mm256_mul_epu32(_mm256_srli_epi64(a, 32),
                                                  _mm256_srli_epi64(b, 32)));
    return ntt_pack_even_odd(even, odd);
}

static __m256i mont_out8(const mont_ctx_t &c, __m256i a){
    __m256i mask = _mm256_set1_epi64x(0xFFFFFFFFULL);
    __m256i even = mont_reduce4(c, _mm256_and_si256(a, mask));
    __m256i odd = mont_reduce4(c, _mm256_srli_epi64(a, 32));
    return ntt_pack_even_odd(even, odd);
}

static __m256i ntt_cmpgt_epu32(__m256i a, __m256i b){
    __m256i sign = _mm256_set1_epi32((int)0x80000000u);
    return _mm256_cmpgt_epi32(_mm256_xor_si256(a, sign),
                              _mm256_xor_si256(b, sign));
}

static __m256i ntt_add8(__m256i a, __m256i b, uint32_t mod){
    __m256i s = _mm256_add_epi32(a, b);
    __m256i m = _mm256_set1_epi32((int)mod);
    __m256i ge = ntt_cmpgt_epu32(s, _mm256_set1_epi32((int)(mod - 1)));
    return _mm256_sub_epi32(s, _mm256_and_si256(ge, m));
}

static __m256i ntt_sub8(__m256i a, __m256i b, uint32_t mod){
    __m256i d = _mm256_sub_epi32(a, b);
    __m256i lt = ntt_cmpgt_epu32(b, a);
    return _mm256_add_epi32(d, _mm256_and_si256(lt, _mm256_set1_epi32((int)mod)));
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

static void ntt_build_roots(ntt_mod_plan_t &p, size_t n){
    const mont_ctx_t &c = p.c;
    p.roots_f.resize(n);
    p.roots_i.resize(n);
    if(n){
        p.roots_f[0] = c.one;
        p.roots_i[0] = c.one;
    }
    for(size_t len = 2; len <= n; len <<= 1){
        size_t half = len >> 1;
        uint64_t e = (c.mod - 1) / len;
        uint32_t wlen = mont_pow(c, c.root, e);
        uint32_t w = c.one;
        for(size_t i = 0; i < half; ++i){
            p.roots_f[half + i] = w;
            w = mont_mul(c, w, wlen);
        }
        p.roots_i[half] = c.one;
        for(size_t i = 1; i < half; ++i){
            p.roots_i[half + i] = c.mod - p.roots_f[half + half - i];
        }
    }
}

static ntt_mod_plan_t ntt_make_mod_plan(size_t n, uint32_t mod, uint32_t root){
    ntt_mod_plan_t p;
    p.c = mont_make(mod, root);
    p.inv_n = mont_pow(p.c, (uint32_t)(n % mod), mod - 2);
    ntt_build_roots(p, n);
    return p;
}

static const ntt_mod_plan_t &ntt_get_mod_plan(size_t n, uint32_t mod, uint32_t root){
    static thread_local ntt_mod_plan_t plans[3];
    static thread_local size_t sizes[3] = {0, 0, 0};
    size_t slot = mod == NTT_MOD1 ? 0 : mod == NTT_MOD2 ? 1 : 2;
    if(sizes[slot] != n){
        plans[slot] = ntt_make_mod_plan(n, mod, root);
        sizes[slot] = n;
    }
    return plans[slot];
}

static void ntt_forward(std::vector<uint32_t> &a, const ntt_mod_plan_t &p){
    size_t n = a.size();
    const mont_ctx_t &c = p.c;
    const std::vector<uint32_t> &roots = p.roots_f;
    uint32_t mod = c.mod;

    // ProtoNTT's forward-DIF/inverse-DIT ordering leaves both transformed
    // operands bit-reversed, so pointwise multiplication needs no permutation.
    for(size_t len = n; len >= 2; len >>= 1){
        size_t half = len >> 1;
        for(size_t i = 0; i < n; i += len){
            size_t j = 0;
#if PRECN_NTT_HAVE_AVX2
            __m256i mod4 = _mm256_set1_epi64x((long long)mod);
            __m256i modm1 = _mm256_set1_epi64x((long long)mod - 1);
            __m256i all = _mm256_cmpeq_epi64(mod4, mod4);
            for(; j + 7 < half; j += 8){
                uint32_t *lo = a.data() + i + j;
                uint32_t *hi = lo + half;
                __m256i u = _mm256_loadu_si256((const __m256i*)lo);
                __m256i v = _mm256_loadu_si256((const __m256i*)hi);
                __m256i s = ntt_add8(u, v, mod);
                __m256i d = mont_mul8(c, ntt_sub8(u, v, mod),
                                      _mm256_loadu_si256((const __m256i*)(roots.data() + half + j)));
                _mm256_storeu_si256((__m256i*)lo, s);
                _mm256_storeu_si256((__m256i*)hi, d);
            }
            for(; j + 3 < half; j += 4){
                uint32_t *lo = a.data() + i + j;
                uint32_t *hi = lo + half;
                __m256i u = ntt_load4_u32(lo);
                __m256i v = ntt_load4_u32(hi);

                __m256i s = _mm256_add_epi64(u, v);
                __m256i s_ge = _mm256_cmpgt_epi64(s, modm1);
                s = _mm256_sub_epi64(s, _mm256_and_si256(s_ge, mod4));

                __m256i d_plain = _mm256_sub_epi64(u, v);
                __m256i d_wrap = _mm256_sub_epi64(_mm256_add_epi64(u, mod4), v);
                __m256i v_gt_u = _mm256_cmpgt_epi64(v, u);
                __m256i u_ge_v = _mm256_xor_si256(v_gt_u, all);
                __m256i d = _mm256_or_si256(_mm256_and_si256(u_ge_v, d_plain),
                                            _mm256_andnot_si256(u_ge_v, d_wrap));
                d = mont_mul4(c, d, ntt_load4_u32(roots.data() + half + j));

                ntt_store4_u32(lo, s);
                ntt_store4_u32(hi, d);
            }
#endif
            for(; j < half; ++j){
                uint32_t u = a[i + j];
                uint32_t v = a[i + j + half];

                uint32_t s = u + v;
                if(s >= mod) s -= mod;
                uint32_t d = u >= v ? u - v : u + mod - v;

                a[i + j] = s;
                a[i + j + half] = mont_mul(c, d, roots[half + j]);
            }
        }
    }
}

static void ntt_inverse(std::vector<uint32_t> &a, const ntt_mod_plan_t &p){
    size_t n = a.size();
    const mont_ctx_t &c = p.c;
    const std::vector<uint32_t> &roots = p.roots_i;
    uint32_t mod = c.mod;

    for(size_t len = 2; len <= n; len <<= 1){
        size_t half = len >> 1;
        for(size_t i = 0; i < n; i += len){
            size_t j = 0;
#if PRECN_NTT_HAVE_AVX2
            __m256i mod4 = _mm256_set1_epi64x((long long)mod);
            __m256i modm1 = _mm256_set1_epi64x((long long)mod - 1);
            __m256i all = _mm256_cmpeq_epi64(mod4, mod4);
            for(; j + 7 < half; j += 8){
                uint32_t *lo = a.data() + i + j;
                uint32_t *hi = lo + half;
                __m256i u = _mm256_loadu_si256((const __m256i*)lo);
                __m256i v = mont_mul8(c, _mm256_loadu_si256((const __m256i*)hi),
                                      _mm256_loadu_si256((const __m256i*)(roots.data() + half + j)));
                _mm256_storeu_si256((__m256i*)lo, ntt_add8(u, v, mod));
                _mm256_storeu_si256((__m256i*)hi, ntt_sub8(u, v, mod));
            }
            for(; j + 3 < half; j += 4){
                uint32_t *lo = a.data() + i + j;
                uint32_t *hi = lo + half;
                __m256i u = ntt_load4_u32(lo);
                __m256i v = mont_mul4(c, ntt_load4_u32(hi),
                                      ntt_load4_u32(roots.data() + half + j));

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

    uint32_t inv_n = p.inv_n;
    size_t i = 0;
#if PRECN_NTT_HAVE_AVX2
    __m256i inv8 = _mm256_set1_epi32((int)inv_n);
    for(; i + 7 < n; i += 8){
        __m256i x = _mm256_loadu_si256((const __m256i*)(a.data() + i));
        _mm256_storeu_si256((__m256i*)(a.data() + i), mont_mul8(c, x, inv8));
    }
    __m256i inv4 = _mm256_set1_epi64x((long long)inv_n);
    for(; i + 3 < n; i += 4){
        ntt_store4_u32(a.data() + i,
                       mont_mul4(c, ntt_load4_u32(a.data() + i), inv4));
    }
#endif
    for(; i < n; ++i) a[i] = mont_mul(c, a[i], inv_n);
}

static std::vector<uint32_t> ntt_digits(const precn_t &a){
    std::vector<uint32_t> d;
    d.reserve(a.rsiz * 4);
    for(size_t i = 0; i < a.rsiz; ++i){
        d.push_back((uint32_t)(a.a[i] & 0xFFFFu));
        d.push_back((uint32_t)((a.a[i] >> 16) & 0xFFFFu));
        d.push_back((uint32_t)((a.a[i] >> 32) & 0xFFFFu));
        d.push_back((uint32_t)(a.a[i] >> 48));
    }
    while(!d.empty() && d.back() == 0) d.pop_back();
    return d;
}

static void ntt_zero(std::vector<uint32_t> &a, size_t n){
    a.resize(n);
    memset(a.data(), 0, n * sizeof(uint32_t));
}

static void ntt_convolve_mod(const std::vector<uint32_t> &a,
                             const std::vector<uint32_t> &b,
                             size_t n,
                             uint32_t mod,
                             uint32_t root,
                             std::vector<uint32_t> &out,
                             std::vector<uint32_t> &scratch){
    const ntt_mod_plan_t &p = ntt_get_mod_plan(n, mod, root);
    ntt_zero(out, n);
    ntt_zero(scratch, n);
    for(size_t i = 0; i < a.size(); ++i) out[i] = mont_in(p.c, a[i]);
    for(size_t i = 0; i < b.size(); ++i) scratch[i] = mont_in(p.c, b[i]);

    ntt_forward(out, p);
    ntt_forward(scratch, p);
    size_t i = 0;
#if PRECN_NTT_HAVE_AVX2
    for(; i + 7 < n; i += 8){
        __m256i x = _mm256_loadu_si256((const __m256i*)(out.data() + i));
        __m256i y = _mm256_loadu_si256((const __m256i*)(scratch.data() + i));
        _mm256_storeu_si256((__m256i*)(out.data() + i), mont_mul8(p.c, x, y));
    }
    for(; i + 3 < n; i += 4) mont_mul4_store(out.data() + i, out.data() + i, scratch.data() + i, p.c);
#endif
    for(; i < n; ++i) out[i] = mont_mul(p.c, out[i], scratch[i]);
    ntt_inverse(out, p);

    i = 0;
#if PRECN_NTT_HAVE_AVX2
    for(; i + 7 < n; i += 8){
        __m256i x = _mm256_loadu_si256((const __m256i*)(out.data() + i));
        _mm256_storeu_si256((__m256i*)(out.data() + i), mont_out8(p.c, x));
    }
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
    // mod1 < mod2, so r1 is already reduced modulo mod2.
    uint64_t d2 = r2 >= x1 ? r2 - x1 : r2 + (uint64_t)NTT_MOD2 - x1;
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
    size_t limb = id >> 2;
    if(limb >= r.asiz){
        size_t old = r.asiz;
        while(r.asiz <= limb) r.asiz <<= 1;
        r.a = (uint64_t*) realloc(r.a, r.asiz * sizeof(uint64_t));
        memset(r.a + old, 0, (r.asiz - old) * sizeof(uint64_t));
    }
    r.a[limb] |= (uint64_t)digit << ((id & 3) * 16);
    if(r.rsiz < limb + 1) r.rsiz = limb + 1;
}

static precn_t ntt_from_residues2(const std::vector<uint32_t> &r1,
                                  const std::vector<uint32_t> &r2){
    precn_t r;
    r.asiz = r1.size() / 4 + 8;
    r.a = (uint64_t*) realloc(r.a, r.asiz * sizeof(uint64_t));
    memset(r.a, 0, r.asiz * sizeof(uint64_t));
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
    r.asiz = r1.size() / 4 + 8;
    r.a = (uint64_t*) realloc(r.a, r.asiz * sizeof(uint64_t));
    memset(r.a, 0, r.asiz * sizeof(uint64_t));
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
    if(std::max(a.rsiz, b.rsiz) <= 192) return mul_basic(a, b);
    size_t limbs = std::max(a.rsiz, b.rsiz);
    if(limbs > NTT_MAX_LIMBS) return mul_fft(a, b);

    std::vector<uint32_t> da = ntt_digits(a);
    std::vector<uint32_t> db = ntt_digits(b);
    if(da.empty() || db.empty()) return precn_t();

    size_t n = 1;
    while(n < da.size() + db.size()) n <<= 1;
    if(n > NTT_MAX_TRANSFORM) return mul_fft(a, b);

    std::vector<uint32_t> r1, r2, r3, scratch;
    ntt_convolve_mod(da, db, n, NTT_MOD1, NTT_ROOT1, r1, scratch);
    ntt_convolve_mod(da, db, n, NTT_MOD2, NTT_ROOT2, r2, scratch);

    if(ntt_two_mod_ok(std::min(da.size(), db.size()))){
        return ntt_from_residues2(r1, r2);
    }

    ntt_convolve_mod(da, db, n, NTT_MOD3, NTT_ROOT3, r3, scratch);
    return ntt_from_residues3(r1, r2, r3);
}
