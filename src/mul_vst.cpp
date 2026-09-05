#include"../prec.hpp"

#include<map>
#include<memory>
#include<mutex>
#include<thread>
#include<type_traits>
#include<vector>

#if defined(PRECN_VST_PROFILE) && PRECN_VST_PROFILE
#include<chrono>
#endif

#if !defined(__EMSCRIPTEN__)
#include<atomic>
#endif

#if defined(PRECN_FORCE_NO_SIMD) && PRECN_FORCE_NO_SIMD
#define PRECN_VST_HAVE_AVX2 0
#elif defined(__AVX2__) || defined(_M_AVX2)
#include<immintrin.h>
#define PRECN_VST_HAVE_AVX2 1
#else
#define PRECN_VST_HAVE_AVX2 0
#endif

#if !defined(PRECN_VST_STRICT_CHECKS)
#define PRECN_VST_STRICT_CHECKS 0
#endif

// These primes all contain 2^20 in p-1 and satisfy p^2 < 2^53. Therefore a
// product of two residues is still an exactly represented double integer.
static const uint32_t VST_MODS[4] = {
    7340033u, 13631489u, 26214401u, 28311553u
};
static const uint32_t VST_ROOTS[4] = {3u, 15u, 3u, 5u};
// The AVX2 packed path can use much larger primes while retaining exact
// double products.  Their product covers every 16-bit convolution whose
// transform fits VST_MAX_TRANSFORM, avoiding the old 15-bit size doubling.
static const uint32_t VST_PACKED_MODS[2] = {70254593u, 81788929u};
static const uint32_t VST_PACKED_ROOTS[2] = {3u, 7u};
static const size_t VST_MAX_TRANSFORM = (size_t)1 << 20;
// Compact conversion pays off earlier when several workers share the work.
static const size_t VST_COMPACT_DATA_TRANSFORM = (size_t)1 << 15;
static const size_t VST_COMPACT_DATA_SERIAL_TRANSFORM = (size_t)1 << 19;
static const size_t VST_PARALLEL_TRANSFORM = (size_t)1 << 15;
static const size_t VST_EIGHT_THREAD_TRANSFORM = (size_t)1 << 20;
static const size_t VST_EIGHT_THREAD_SQUARE_TRANSFORM = (size_t)1 << 19;
static const uint64_t VST_P01 = 100055579099137ULL;
static const uint64_t VST_PACKED_PRODUCT = 5746047918800897ULL;
static const uint32_t VST_INV_P0_MOD_P1 = 2271917u;
static const uint32_t VST_INV_P01_MOD_P2 = 18325811u;
static const uint32_t VST_PACKED_INVERSE = 37176793u;

struct alignas(32) vst_word_t{
    double v[4];
};

static_assert(sizeof(vst_word_t) == 32, "VST word must fill one AVX2 vector");

#if PRECN_VST_HAVE_AVX2
struct alignas(16) vst_packed_word_t{
    uint32_t v[4];
};

static_assert(sizeof(vst_packed_word_t) == 16,
              "Packed VST word must fill one SSE vector");
#endif

struct vst_plan_t{
    size_t n;
    vst_word_t mod;
    vst_word_t reciprocal;
    vst_word_t inv_n;
    std::vector<vst_word_t> roots_f;
    std::vector<vst_word_t> roots_i;
#if PRECN_VST_HAVE_AVX2
    vst_word_t mod2;
    vst_word_t reciprocal2;
    vst_word_t inv_n2;
    std::vector<vst_packed_word_t> roots2_f;
    std::vector<vst_packed_word_t> roots2_i;
#endif
};

struct vst_workspace_t{
    std::vector<vst_word_t> a;
    std::vector<vst_word_t> b;
#if PRECN_VST_HAVE_AVX2
    std::vector<vst_word_t> a2;
    std::vector<vst_word_t> b2;
    std::vector<vst_packed_word_t> a2_compact;
    std::vector<vst_packed_word_t> b2_compact;
    std::vector<uint64_t> coefficients;
#endif
};

#if defined(PRECN_VST_PROFILE) && PRECN_VST_PROFILE
struct vst_profile_t{
    double setup;
    double load;
    double forward;
    double pipeline;
    double pointwise;
    double inverse;
    double collect;
    double verify;
    uint64_t calls;
};

static thread_local vst_profile_t vst_profile = {};

static double vst_profile_now(){
    return std::chrono::duration<double>(
        std::chrono::steady_clock::now().time_since_epoch()).count();
}

void precn_vst_profile_reset(){
    vst_profile = vst_profile_t();
}

void precn_vst_profile_dump(){
    double total = vst_profile.setup + vst_profile.load +
                   vst_profile.forward + vst_profile.pipeline +
                   vst_profile.pointwise +
                   vst_profile.inverse + vst_profile.collect +
                   vst_profile.verify;
    double scale = vst_profile.calls ? 1.0 / (double)vst_profile.calls : 0.0;
    printf("VST phases (%llu calls, seconds/call): setup %.9f  load %.9f  "
           "forward %.9f  pipeline %.9f  pointwise %.9f  inverse %.9f  "
           "collect %.9f  verify %.9f  total %.9f\n",
           (unsigned long long)vst_profile.calls,
           vst_profile.setup * scale, vst_profile.load * scale,
           vst_profile.forward * scale, vst_profile.pipeline * scale,
           vst_profile.pointwise * scale,
           vst_profile.inverse * scale, vst_profile.collect * scale,
           vst_profile.verify * scale, total * scale);
}
#endif

static uint32_t vst_pow_mod(uint32_t a, uint64_t e, uint32_t mod){
    uint64_t r = 1;
    uint64_t x = a;
    while(e){
        if(e & 1) r = r * x % mod;
        e >>= 1;
        if(e) x = x * x % mod;
    }
    return (uint32_t)r;
}

static double vst_reduce_scalar(double x, double mod, double reciprocal){
    double q = std::floor(x * reciprocal);
    double r = x - q * mod;
    if(r < 0.0) r += mod;
    if(r >= mod) r -= mod;
    return r;
}

#if PRECN_VST_HAVE_AVX2
static inline __m256d vst_load(const vst_word_t &a){
    return _mm256_load_pd(a.v);
}

static inline void vst_store(vst_word_t &a, __m256d x){
    _mm256_store_pd(a.v, x);
}

static inline __m256d vst_load(const vst_packed_word_t &a){
    __m128i x = _mm_load_si128((const __m128i*)a.v);
    return _mm256_cvtepi32_pd(x);
}

static inline void vst_store(vst_packed_word_t &a, __m256d x){
    _mm_store_si128((__m128i*)a.v, _mm256_cvttpd_epi32(x));
}

static inline void vst_store_digit_pair(vst_word_t &a,
                                        uint32_t lo, uint32_t hi){
    vst_store(a, _mm256_set_pd((double)hi, (double)hi,
                               (double)lo, (double)lo));
}

static inline void vst_store_digit_pair(vst_packed_word_t &a,
                                        uint32_t lo, uint32_t hi){
    _mm_store_si128((__m128i*)a.v,
                    _mm_set_epi32((int)hi, (int)hi,
                                  (int)lo, (int)lo));
}

static inline __m256d vst_add4(__m256d a, __m256d b, __m256d mod){
    __m256d s = _mm256_add_pd(a, b);
    __m256d reduced = _mm256_sub_pd(s, mod);
    return _mm256_blendv_pd(s, reduced,
                            _mm256_cmp_pd(s, mod, _CMP_GE_OQ));
}

static inline __m256d vst_sub4(__m256d a, __m256d b, __m256d mod){
    __m256d d = _mm256_sub_pd(a, b);
    __m256d wrapped = _mm256_add_pd(d, mod);
    return _mm256_blendv_pd(d, wrapped,
                            _mm256_cmp_pd(d, _mm256_setzero_pd(), _CMP_LT_OQ));
}

static inline __m256d vst_mul4(__m256d a, __m256d b, __m256d mod,
                               __m256d reciprocal){
    __m256d x = _mm256_mul_pd(a, b);
    // x < p^2 < 2^53 and p < 2^27, so reciprocal and multiplication error
    // move x/p by far less than 1/2.  Rounding the quotient therefore chooses
    // either floor(x/p) or ceil(x/p), leaving r in (-p, p).  Only a negative
    // correction is needed; floor-based reduction needed a second r >= p test.
    __m256d scaled = _mm256_mul_pd(x, reciprocal);
    __m256d q = _mm256_round_pd(scaled, _MM_FROUND_TO_NEAREST_INT |
                                _MM_FROUND_NO_EXC);
#if defined(__FMA__)
    __m256d r = _mm256_fnmadd_pd(q, mod, x);
#else
    __m256d r = _mm256_sub_pd(x, _mm256_mul_pd(q, mod));
#endif
    r = _mm256_blendv_pd(r, _mm256_add_pd(r, mod),
                         _mm256_cmp_pd(r, _mm256_setzero_pd(), _CMP_LT_OQ));
    return r;
}

#endif

static vst_word_t vst_mul_word(const vst_word_t &a, const vst_word_t &b,
                               const vst_word_t &mod,
                               const vst_word_t &reciprocal){
    vst_word_t r;
#if PRECN_VST_HAVE_AVX2
    vst_store(r, vst_mul4(vst_load(a), vst_load(b), vst_load(mod),
                          vst_load(reciprocal)));
#else
    for(size_t lane = 0; lane < 4; ++lane)
        r.v[lane] = vst_reduce_scalar(a.v[lane] * b.v[lane], mod.v[lane],
                                      reciprocal.v[lane]);
#endif
    return r;
}

static std::shared_ptr<vst_plan_t> vst_make_plan(size_t n, bool packed){
    std::shared_ptr<vst_plan_t> plan = std::make_shared<vst_plan_t>();
    plan->n = n;
    if(!packed){
        for(size_t lane = 0; lane < 4; ++lane){
            plan->mod.v[lane] = (double)VST_MODS[lane];
            plan->reciprocal.v[lane] = 1.0 / (double)VST_MODS[lane];
            plan->inv_n.v[lane] = (double)vst_pow_mod(
                (uint32_t)n, VST_MODS[lane] - 2, VST_MODS[lane]);
        }

        plan->roots_f.resize(n);
        plan->roots_i.resize(n);
        for(size_t lane = 0; lane < 4; ++lane){
            plan->roots_f[0].v[lane] = 1.0;
            plan->roots_i[0].v[lane] = 1.0;
        }

        for(size_t len = 2; len <= n; len <<= 1){
            size_t half = len >> 1;
            vst_word_t step_f;
            vst_word_t step_i;
            vst_word_t w_f;
            vst_word_t w_i;
            for(size_t lane = 0; lane < 4; ++lane){
                uint64_t exponent = (VST_MODS[lane] - 1) / len;
                step_f.v[lane] = (double)vst_pow_mod(
                    VST_ROOTS[lane], exponent, VST_MODS[lane]);
                step_i.v[lane] = (double)vst_pow_mod(
                    VST_ROOTS[lane], VST_MODS[lane] - 1 - exponent,
                    VST_MODS[lane]);
                w_f.v[lane] = 1.0;
                w_i.v[lane] = 1.0;
            }
            for(size_t j = 0; j < half; ++j){
                plan->roots_f[half + j] = w_f;
                plan->roots_i[half + j] = w_i;
                w_f = vst_mul_word(w_f, step_f, plan->mod,
                                   plan->reciprocal);
                w_i = vst_mul_word(w_i, step_i, plan->mod,
                                   plan->reciprocal);
            }
        }
    }
#if PRECN_VST_HAVE_AVX2
    if(packed){
        // Two-modulus mode packs
        // [x0 mod p0, x0 mod p1, x1 mod p0, x1 mod p1].
        for(size_t lane = 0; lane < 4; ++lane){
            size_t source = lane & 1;
            plan->mod2.v[lane] = (double)VST_PACKED_MODS[source];
            plan->reciprocal2.v[lane] =
                1.0 / (double)VST_PACKED_MODS[source];
            plan->inv_n2.v[lane] = (double)vst_pow_mod(
                (uint32_t)n, VST_PACKED_MODS[source] - 2,
                VST_PACKED_MODS[source]);
        }
        plan->roots2_f.resize(n >> 1);
        plan->roots2_i.resize(n >> 1);
        for(size_t len = 4; len <= n; len <<= 1){
            size_t half = len >> 1;
            double step_f[2];
            double step_i[2];
            double w_f[2] = {1.0, 1.0};
            double w_i[2] = {1.0, 1.0};
            for(size_t mod_index = 0; mod_index < 2; ++mod_index){
                uint64_t exponent =
                    (VST_PACKED_MODS[mod_index] - 1) / len;
                step_f[mod_index] = (double)vst_pow_mod(
                    VST_PACKED_ROOTS[mod_index], exponent,
                    VST_PACKED_MODS[mod_index]);
                step_i[mod_index] = (double)vst_pow_mod(
                    VST_PACKED_ROOTS[mod_index],
                    VST_PACKED_MODS[mod_index] - 1 - exponent,
                    VST_PACKED_MODS[mod_index]);
            }
            for(size_t j = 0; j < half; j += 2){
                size_t packed_index = (half >> 1) + (j >> 1);
                for(size_t mod_index = 0; mod_index < 2; ++mod_index){
                    double mod = (double)VST_PACKED_MODS[mod_index];
                    double reciprocal = 1.0 / mod;
                    plan->roots2_f[packed_index].v[mod_index] =
                        (uint32_t)w_f[mod_index];
                    plan->roots2_i[packed_index].v[mod_index] =
                        (uint32_t)w_i[mod_index];
                    w_f[mod_index] = vst_reduce_scalar(
                        w_f[mod_index] * step_f[mod_index], mod,
                        reciprocal);
                    w_i[mod_index] = vst_reduce_scalar(
                        w_i[mod_index] * step_i[mod_index], mod,
                        reciprocal);
                    plan->roots2_f[packed_index].v[mod_index + 2] =
                        (uint32_t)w_f[mod_index];
                    plan->roots2_i[packed_index].v[mod_index + 2] =
                        (uint32_t)w_i[mod_index];
                    w_f[mod_index] = vst_reduce_scalar(
                        w_f[mod_index] * step_f[mod_index], mod,
                        reciprocal);
                    w_i[mod_index] = vst_reduce_scalar(
                        w_i[mod_index] * step_i[mod_index], mod,
                        reciprocal);
                }
            }
        }
        // Fold n^-1 into the final inverse-stage roots. The low half is
        // scaled explicitly there, avoiding another full-array multiply.
        if(n >= 4){
            for(size_t i = n >> 2; i < (n >> 1); ++i){
                __m256d scaled = vst_mul4(
                    vst_load(plan->roots2_i[i]), vst_load(plan->inv_n2),
                    vst_load(plan->mod2), vst_load(plan->reciprocal2));
                vst_store(plan->roots2_i[i], scaled);
            }
        }
    }
#else
    (void)packed;
#endif
    return plan;
}

static const vst_plan_t &vst_get_plan(size_t n, bool packed){
    static std::mutex plans_mutex;
    static std::map<size_t, std::shared_ptr<vst_plan_t> > plans;
    size_t key = (n << 1) | (packed ? 1 : 0);
    size_t log_n = 0;
    for(size_t value = n; value > 1; value >>= 1) ++log_n;
    size_t local_index = (log_n << 1) | (packed ? 1 : 0);
    static thread_local const vst_plan_t *local_plans[
        sizeof(size_t) * 16] = {};
    if(local_plans[local_index]) return *local_plans[local_index];
    std::lock_guard<std::mutex> lock(plans_mutex);
    std::map<size_t, std::shared_ptr<vst_plan_t> >::iterator found =
        plans.find(key);
    if(found == plans.end())
        found = plans.emplace(key, vst_make_plan(n, packed)).first;
    local_plans[local_index] = found->second.get();
    return *local_plans[local_index];
}

static void vst_forward(std::vector<vst_word_t> &a, const vst_plan_t &plan){
    size_t n = a.size();
#if PRECN_VST_HAVE_AVX2
    __m256d mod = vst_load(plan.mod);
    __m256d reciprocal = vst_load(plan.reciprocal);
    for(size_t len = n; len >= 2; len >>= 1){
        size_t half = len >> 1;
        for(size_t base = 0; base < n; base += len){
            for(size_t j = 0; j < half; ++j){
                __m256d u = vst_load(a[base + j]);
                __m256d v = vst_load(a[base + half + j]);
                vst_store(a[base + j], vst_add4(u, v, mod));
                vst_store(a[base + half + j],
                          vst_mul4(vst_sub4(u, v, mod),
                                   vst_load(plan.roots_f[half + j]), mod,
                                   reciprocal));
            }
        }
    }
#else
    for(size_t len = n; len >= 2; len >>= 1){
        size_t half = len >> 1;
        for(size_t base = 0; base < n; base += len){
            for(size_t j = 0; j < half; ++j){
                for(size_t lane = 0; lane < 4; ++lane){
                    double mod = plan.mod.v[lane];
                    double u = a[base + j].v[lane];
                    double v = a[base + half + j].v[lane];
                    double sum = u + v;
                    if(sum >= mod) sum -= mod;
                    double diff = u - v;
                    if(diff < 0.0) diff += mod;
                    a[base + j].v[lane] = sum;
                    a[base + half + j].v[lane] = vst_reduce_scalar(
                        diff * plan.roots_f[half + j].v[lane], mod,
                        plan.reciprocal.v[lane]);
                }
            }
        }
    }
#endif
}

static void vst_inverse(std::vector<vst_word_t> &a, const vst_plan_t &plan){
    size_t n = a.size();
#if PRECN_VST_HAVE_AVX2
    __m256d mod = vst_load(plan.mod);
    __m256d reciprocal = vst_load(plan.reciprocal);
    for(size_t len = 2; len <= n; len <<= 1){
        size_t half = len >> 1;
        for(size_t base = 0; base < n; base += len){
            for(size_t j = 0; j < half; ++j){
                __m256d u = vst_load(a[base + j]);
                __m256d v = vst_mul4(vst_load(a[base + half + j]),
                                     vst_load(plan.roots_i[half + j]), mod,
                                     reciprocal);
                vst_store(a[base + j], vst_add4(u, v, mod));
                vst_store(a[base + half + j], vst_sub4(u, v, mod));
            }
        }
    }
#else
    for(size_t len = 2; len <= n; len <<= 1){
        size_t half = len >> 1;
        for(size_t base = 0; base < n; base += len){
            for(size_t j = 0; j < half; ++j){
                for(size_t lane = 0; lane < 4; ++lane){
                    double mod = plan.mod.v[lane];
                    double u = a[base + j].v[lane];
                    double v = vst_reduce_scalar(
                        a[base + half + j].v[lane] *
                            plan.roots_i[half + j].v[lane],
                        mod, plan.reciprocal.v[lane]);
                    double sum = u + v;
                    if(sum >= mod) sum -= mod;
                    double diff = u - v;
                    if(diff < 0.0) diff += mod;
                    a[base + j].v[lane] = sum;
                    a[base + half + j].v[lane] = diff;
                }
            }
        }
    }
#endif
}

static void vst_pointwise(std::vector<vst_word_t> &a,
                          const std::vector<vst_word_t> *b,
                          const vst_plan_t &plan){
#if PRECN_VST_HAVE_AVX2
    __m256d mod = vst_load(plan.mod);
    __m256d reciprocal = vst_load(plan.reciprocal);
    __m256d inv_n = vst_load(plan.inv_n);
    for(size_t i = 0; i < a.size(); ++i){
        __m256d x = vst_load(a[i]);
        __m256d y = b ? vst_load((*b)[i]) : x;
        vst_store(a[i], vst_mul4(vst_mul4(x, y, mod, reciprocal), inv_n,
                                 mod, reciprocal));
    }
#else
    for(size_t i = 0; i < a.size(); ++i){
        for(size_t lane = 0; lane < 4; ++lane){
            double mod = plan.mod.v[lane];
            double y = b ? (*b)[i].v[lane] : a[i].v[lane];
            double product = vst_reduce_scalar(a[i].v[lane] * y, mod,
                                                plan.reciprocal.v[lane]);
            a[i].v[lane] = vst_reduce_scalar(product * plan.inv_n.v[lane],
                                              mod,
                                              plan.reciprocal.v[lane]);
        }
    }
#endif
}

#if PRECN_VST_HAVE_AVX2
template<class Word>
static void vst_forward2_outer(std::vector<Word> &a,
                               const vst_plan_t &plan){
    size_t n = a.size() << 1;
    __m256d mod = vst_load(plan.mod2);
    __m256d reciprocal = vst_load(plan.reciprocal2);
    for(size_t len = n; len >= 4; len >>= 1){
        size_t half_words = len >> 2;
        size_t len_words = len >> 1;
        size_t root_base = len >> 2;
        for(size_t base = 0; base < a.size(); base += len_words){
            for(size_t j = 0; j < half_words; ++j){
                __m256d u = vst_load(a[base + j]);
                __m256d v = vst_load(a[base + half_words + j]);
                vst_store(a[base + j], vst_add4(u, v, mod));
                vst_store(a[base + half_words + j],
                          // The product reducer accepts a residue in
                          // (-p, p).  Multiplying the signed difference
                          // directly avoids wrapping it before the twiddle.
                          vst_mul4(
                              _mm256_sub_pd(u, v),
                              vst_load(plan.roots2_f[root_base + j]),
                              mod, reciprocal));
            }
        }
    }
}

static inline void vst_forward2_radix4_range(
    std::vector<vst_packed_word_t> &a, const vst_plan_t &plan,
    size_t len, size_t first, size_t last,
    __m256d mod, __m256d reciprocal){
    size_t quarter_words = len >> 3;
    size_t len_words = len >> 1;
    size_t roots_large = len >> 2;
    size_t roots_small = len >> 3;
    while(first < last){
        size_t block = first / quarter_words;
        size_t j = first - block * quarter_words;
        size_t count = std::min(last - first, quarter_words - j);
        size_t base = block * len_words;
        for(size_t k = 0; k < count; ++k){
            size_t index = j + k;
            __m256d x0 = vst_load(a[base + index]);
            __m256d x1 = vst_load(a[base + quarter_words + index]);
            __m256d x2 = vst_load(a[base + 2 * quarter_words + index]);
            __m256d x3 = vst_load(a[base + 3 * quarter_words + index]);
            __m256d y0 = vst_add4(x0, x2, mod);
            __m256d y1 = vst_add4(x1, x3, mod);
            __m256d y2 = vst_mul4(
                _mm256_sub_pd(x0, x2),
                vst_load(plan.roots2_f[roots_large + index]),
                mod, reciprocal);
            __m256d y3 = vst_mul4(
                _mm256_sub_pd(x1, x3),
                vst_load(plan.roots2_f[
                    roots_large + quarter_words + index]),
                mod, reciprocal);
            __m256d root = vst_load(plan.roots2_f[roots_small + index]);
            vst_store(a[base + index], vst_add4(y0, y1, mod));
            vst_store(a[base + quarter_words + index],
                      vst_mul4(_mm256_sub_pd(y0, y1), root,
                               mod, reciprocal));
            vst_store(a[base + 2 * quarter_words + index],
                      vst_add4(y2, y3, mod));
            vst_store(a[base + 3 * quarter_words + index],
                      vst_mul4(_mm256_sub_pd(y2, y3), root,
                               mod, reciprocal));
        }
        first += count;
    }
}

static inline void vst_forward2_radix2_range(
    std::vector<vst_packed_word_t> &a, const vst_plan_t &plan,
    size_t first, size_t last, __m256d mod, __m256d reciprocal){
    __m256d root = vst_load(plan.roots2_f[1]);
    for(size_t i = first; i < last; ++i){
        size_t base = i << 1;
        __m256d u = vst_load(a[base]);
        __m256d v = vst_load(a[base + 1]);
        vst_store(a[base], vst_add4(u, v, mod));
        vst_store(a[base + 1], vst_mul4(
            _mm256_sub_pd(u, v), root, mod, reciprocal));
    }
}

static void vst_forward2_outer(std::vector<vst_packed_word_t> &a,
                               const vst_plan_t &plan){
    size_t n = a.size() << 1;
    __m256d mod = vst_load(plan.mod2);
    __m256d reciprocal = vst_load(plan.reciprocal2);
    size_t len = n;
    for(; len >= 8; len >>= 2)
        vst_forward2_radix4_range(a, plan, len, 0, a.size() >> 2,
                                  mod, reciprocal);
    if(len == 4)
        vst_forward2_radix2_range(a, plan, 0, a.size() >> 1,
                                  mod, reciprocal);
}

// Fuse the final DIF length-2 butterfly, pointwise product, and first DIT
// length-2 butterfly.  All three operations use the two coefficients packed
// into one vector, so keeping them in registers removes several full-array
// load/store passes.
template<class Word>
static void vst_fused_len2_product(std::vector<Word> &a,
                                   const std::vector<Word> *b,
                                   const vst_plan_t &plan,
                                   size_t begin, size_t end){
    __m256d mod = vst_load(plan.mod2);
    __m256d reciprocal = vst_load(plan.reciprocal2);
    __m256d inv_n = vst_load(plan.inv_n2);
    bool normalize_here = a.size() == 1;
    for(size_t i = begin; i < end; ++i){
        __m256d x = vst_load(a[i]);
        __m256d x_lo = _mm256_permute2f128_pd(x, x, 0x00);
        __m256d x_hi = _mm256_permute2f128_pd(x, x, 0x11);
        __m256d x_sum = vst_add4(x_lo, x_hi, mod);
        __m256d x_diff = vst_sub4(x_lo, x_hi, mod);
        x = _mm256_blend_pd(x_sum, x_diff, 0x0c);

        __m256d y = x;
        if(b){
            y = vst_load((*b)[i]);
            __m256d y_lo = _mm256_permute2f128_pd(y, y, 0x00);
            __m256d y_hi = _mm256_permute2f128_pd(y, y, 0x11);
            __m256d y_sum = vst_add4(y_lo, y_hi, mod);
            __m256d y_diff = vst_sub4(y_lo, y_hi, mod);
            y = _mm256_blend_pd(y_sum, y_diff, 0x0c);
        }

        __m256d product = vst_mul4(x, y, mod, reciprocal);
        if(normalize_here)
            product = vst_mul4(product, inv_n, mod, reciprocal);

        __m256d p_lo = _mm256_permute2f128_pd(product, product, 0x00);
        __m256d p_hi = _mm256_permute2f128_pd(product, product, 0x11);
        __m256d sum = vst_add4(p_lo, p_hi, mod);
        __m256d diff = vst_sub4(p_lo, p_hi, mod);
        vst_store(a[i], _mm256_blend_pd(sum, diff, 0x0c));
    }
}

template<class Word>
static void vst_inverse2_outer(std::vector<Word> &a,
                               const vst_plan_t &plan){
    size_t n = a.size() << 1;
    __m256d mod = vst_load(plan.mod2);
    __m256d reciprocal = vst_load(plan.reciprocal2);
    for(size_t len = 4; len <= n; len <<= 1){
        size_t half_words = len >> 2;
        size_t len_words = len >> 1;
        size_t root_base = len >> 2;
        bool final_stage = len == n;
        for(size_t base = 0; base < a.size(); base += len_words){
            for(size_t j = 0; j < half_words; ++j){
                __m256d u = vst_load(a[base + j]);
                if(final_stage)
                    u = vst_mul4(u, vst_load(plan.inv_n2), mod, reciprocal);
                __m256d v = vst_mul4(
                    vst_load(a[base + half_words + j]),
                    vst_load(plan.roots2_i[root_base + j]), mod, reciprocal);
                vst_store(a[base + j],
                          vst_add4(u, v, mod));
                vst_store(a[base + half_words + j],
                          vst_sub4(u, v, mod));
            }
        }
    }
}

static void vst_inverse2_outer(std::vector<vst_packed_word_t> &a,
                               const vst_plan_t &plan){
    size_t n = a.size() << 1;
    __m256d mod = vst_load(plan.mod2);
    __m256d reciprocal = vst_load(plan.reciprocal2);
    __m256d inv_n = vst_load(plan.inv_n2);
    size_t len = 4;
    for(; len <= (n >> 1); len <<= 2){
        size_t quarter_words = len >> 2;
        size_t combined_words = len;
        size_t roots_small = len >> 2;
        size_t roots_large = len >> 1;
        bool final_stage = (len << 1) == n;
        for(size_t base = 0; base < a.size(); base += combined_words){
            for(size_t j = 0; j < quarter_words; ++j){
                __m256d x0 = vst_load(a[base + j]);
                __m256d x1 = vst_load(a[base + quarter_words + j]);
                __m256d x2 = vst_load(a[base + 2 * quarter_words + j]);
                __m256d x3 = vst_load(a[base + 3 * quarter_words + j]);

                __m256d t1 = vst_mul4(
                    x1, vst_load(plan.roots2_i[roots_small + j]),
                    mod, reciprocal);
                __m256d t3 = vst_mul4(
                    x3, vst_load(plan.roots2_i[roots_small + j]),
                    mod, reciprocal);
                __m256d y0 = vst_add4(x0, t1, mod);
                __m256d y1 = vst_sub4(x0, t1, mod);
                __m256d y2 = vst_add4(x2, t3, mod);
                __m256d y3 = vst_sub4(x2, t3, mod);

                if(final_stage){
                    y0 = vst_mul4(y0, inv_n, mod, reciprocal);
                    y1 = vst_mul4(y1, inv_n, mod, reciprocal);
                }
                __m256d t2 = vst_mul4(
                    y2, vst_load(plan.roots2_i[roots_large + j]),
                    mod, reciprocal);
                __m256d t4 = vst_mul4(
                    y3, vst_load(plan.roots2_i[
                        roots_large + quarter_words + j]),
                    mod, reciprocal);

                vst_store(a[base + j], vst_add4(y0, t2, mod));
                vst_store(a[base + quarter_words + j],
                          vst_add4(y1, t4, mod));
                vst_store(a[base + 2 * quarter_words + j],
                          vst_sub4(y0, t2, mod));
                vst_store(a[base + 3 * quarter_words + j],
                          vst_sub4(y1, t4, mod));
            }
        }
    }

    if(len <= n){
        size_t half_words = len >> 2;
        size_t len_words = len >> 1;
        size_t root_base = len >> 2;
        bool final_stage = len == n;
        for(size_t base = 0; base < a.size(); base += len_words){
            for(size_t j = 0; j < half_words; ++j){
                __m256d u = vst_load(a[base + j]);
                if(final_stage)
                    u = vst_mul4(u, inv_n, mod, reciprocal);
                __m256d v = vst_mul4(
                    vst_load(a[base + half_words + j]),
                    vst_load(plan.roots2_i[root_base + j]),
                    mod, reciprocal);
                vst_store(a[base + j], vst_add4(u, v, mod));
                vst_store(a[base + half_words + j],
                          vst_sub4(u, v, mod));
            }
        }
    }
}

#if !defined(__EMSCRIPTEN__)
struct vst_spin_barrier_t{
    std::atomic<unsigned int> arrived;
    std::atomic<unsigned int> generation;
    unsigned int participants;

    explicit vst_spin_barrier_t(unsigned int count)
        : arrived(0), generation(0), participants(count){}

    void wait(){
        unsigned int g = generation.load(std::memory_order_acquire);
        if(arrived.fetch_add(1, std::memory_order_acq_rel) + 1 ==
           participants){
            arrived.store(0, std::memory_order_relaxed);
            generation.store(g + 1, std::memory_order_release);
            return;
        }
        while(generation.load(std::memory_order_acquire) == g) _mm_pause();
    }
};

static void vst_forward2_outer_parallel_part(
    std::vector<vst_packed_word_t> &a, const vst_plan_t &plan,
    size_t part, size_t parts, vst_spin_barrier_t &barrier){
    size_t n = a.size() << 1;
    __m256d mod = vst_load(plan.mod2);
    __m256d reciprocal = vst_load(plan.reciprocal2);
    size_t len = n;
    for(; len >= 8; len >>= 2){
        size_t total = a.size() >> 2;
        size_t first = part * total / parts;
        size_t last = (part + 1) * total / parts;
        vst_forward2_radix4_range(a, plan, len, first, last,
                                  mod, reciprocal);
        barrier.wait();
    }

    if(len == 4){
        size_t total = a.size() >> 1;
        size_t first = part * total / parts;
        size_t last = (part + 1) * total / parts;
        vst_forward2_radix2_range(a, plan, first, last,
                                  mod, reciprocal);
        barrier.wait();
    }
}

template<class Word>
static void vst_inverse2_outer_parallel_part(
    std::vector<Word> &a, const vst_plan_t &plan, size_t part,
    size_t parts, vst_spin_barrier_t &barrier){
    size_t n = a.size() << 1;
    __m256d mod = vst_load(plan.mod2);
    __m256d reciprocal = vst_load(plan.reciprocal2);
    __m256d inv_n = vst_load(plan.inv_n2);
    for(size_t len = 4; len <= n; len <<= 1){
        size_t half_words = len >> 2;
        size_t len_words = len >> 1;
        size_t root_base = len >> 2;
        bool final_stage = len == n;
        size_t total = n >> 2;
        size_t first = part * total / parts;
        size_t last = (part + 1) * total / parts;
        while(first < last){
            size_t block = first / half_words;
            size_t j = first - block * half_words;
            size_t count = std::min(last - first, half_words - j);
            size_t base = block * len_words;
            for(size_t k = 0; k < count; ++k){
                __m256d u = vst_load(a[base + j + k]);
                if(final_stage)
                    u = vst_mul4(u, inv_n, mod, reciprocal);
                __m256d v = vst_mul4(
                    vst_load(a[base + half_words + j + k]),
                    vst_load(plan.roots2_i[root_base + j + k]), mod,
                    reciprocal);
                vst_store(a[base + j + k], vst_add4(u, v, mod));
                vst_store(a[base + half_words + j + k],
                          vst_sub4(u, v, mod));
            }
            first += count;
        }
        barrier.wait();
    }
}

static void vst_inverse2_outer_parallel_part(
    std::vector<vst_packed_word_t> &a, const vst_plan_t &plan,
    size_t part, size_t parts, vst_spin_barrier_t &barrier){
    size_t n = a.size() << 1;
    __m256d mod = vst_load(plan.mod2);
    __m256d reciprocal = vst_load(plan.reciprocal2);
    __m256d inv_n = vst_load(plan.inv_n2);
    size_t len = 4;
    for(; len <= (n >> 1); len <<= 2){
        size_t quarter_words = len >> 2;
        size_t roots_small = len >> 2;
        size_t roots_large = len >> 1;
        bool final_stage = (len << 1) == n;
        size_t total = a.size() >> 2;
        size_t first = part * total / parts;
        size_t last = (part + 1) * total / parts;
        while(first < last){
            size_t block = first / quarter_words;
            size_t j = first - block * quarter_words;
            size_t count = std::min(last - first, quarter_words - j);
            size_t base = block * len;
            for(size_t k = 0; k < count; ++k){
                size_t index = j + k;
                __m256d x0 = vst_load(a[base + index]);
                __m256d x1 = vst_load(a[base + quarter_words + index]);
                __m256d x2 = vst_load(a[base + 2 * quarter_words + index]);
                __m256d x3 = vst_load(a[base + 3 * quarter_words + index]);

                __m256d t1 = vst_mul4(
                    x1, vst_load(plan.roots2_i[roots_small + index]),
                    mod, reciprocal);
                __m256d t3 = vst_mul4(
                    x3, vst_load(plan.roots2_i[roots_small + index]),
                    mod, reciprocal);
                __m256d y0 = vst_add4(x0, t1, mod);
                __m256d y1 = vst_sub4(x0, t1, mod);
                __m256d y2 = vst_add4(x2, t3, mod);
                __m256d y3 = vst_sub4(x2, t3, mod);
                if(final_stage){
                    y0 = vst_mul4(y0, inv_n, mod, reciprocal);
                    y1 = vst_mul4(y1, inv_n, mod, reciprocal);
                }
                __m256d t2 = vst_mul4(
                    y2, vst_load(plan.roots2_i[roots_large + index]),
                    mod, reciprocal);
                __m256d t4 = vst_mul4(
                    y3, vst_load(plan.roots2_i[
                        roots_large + quarter_words + index]),
                    mod, reciprocal);

                vst_store(a[base + index], vst_add4(y0, t2, mod));
                vst_store(a[base + quarter_words + index],
                          vst_add4(y1, t4, mod));
                vst_store(a[base + 2 * quarter_words + index],
                          vst_sub4(y0, t2, mod));
                vst_store(a[base + 3 * quarter_words + index],
                          vst_sub4(y1, t4, mod));
            }
            first += count;
        }
        barrier.wait();
    }

    if(len <= n){
        size_t half_words = len >> 2;
        size_t len_words = len >> 1;
        size_t root_base = len >> 2;
        bool final_stage = len == n;
        size_t total = n >> 2;
        size_t first = part * total / parts;
        size_t last = (part + 1) * total / parts;
        while(first < last){
            size_t block = first / half_words;
            size_t j = first - block * half_words;
            size_t count = std::min(last - first, half_words - j);
            size_t base = block * len_words;
            for(size_t k = 0; k < count; ++k){
                __m256d u = vst_load(a[base + j + k]);
                if(final_stage)
                    u = vst_mul4(u, inv_n, mod, reciprocal);
                __m256d v = vst_mul4(
                    vst_load(a[base + half_words + j + k]),
                    vst_load(plan.roots2_i[root_base + j + k]),
                    mod, reciprocal);
                vst_store(a[base + j + k], vst_add4(u, v, mod));
                vst_store(a[base + half_words + j + k],
                          vst_sub4(u, v, mod));
            }
            first += count;
        }
        barrier.wait();
    }
}

template<class Word, class Finish>
static void vst_pointwise_inverse2_parallel(
    std::vector<Word> &a, std::vector<Word> *b,
    const vst_plan_t &plan, bool include_forward, Finish finish){
    size_t n = a.size() << 1;
    size_t parts = 2;
    if constexpr(std::is_same<Word, vst_packed_word_t>::value){
        size_t eight_thread_threshold = b ? VST_EIGHT_THREAD_TRANSFORM :
            VST_EIGHT_THREAD_SQUARE_TRANSFORM;
        parts = n >= eight_thread_threshold ? 8 : 4;
    }
    vst_spin_barrier_t barrier((unsigned int)parts);
    vst_spin_barrier_t forward_a_barrier((unsigned int)(parts >> 1));
    vst_spin_barrier_t forward_b_barrier((unsigned int)(parts >> 1));
    auto run_half = [&](size_t part){
        if(include_forward){
            if constexpr(std::is_same<Word,
                                      vst_packed_word_t>::value){
                if(parts >= 4 && !b){
                    vst_forward2_outer_parallel_part(
                        a, plan, part, parts, barrier);
                }else if(parts >= 4){
                    size_t local_part = part >> 1;
                    if((part & 1) == 0)
                        vst_forward2_outer_parallel_part(
                            a, plan, local_part, parts >> 1,
                            forward_a_barrier);
                    else
                        vst_forward2_outer_parallel_part(
                            *b, plan, local_part, parts >> 1,
                            forward_b_barrier);
                }else{
                    if(part == 0) vst_forward2_outer(a, plan);
                    else if(b) vst_forward2_outer(*b, plan);
                }
            }else if(part < 2){
                if(part == 0) vst_forward2_outer(a, plan);
                else if(b) vst_forward2_outer(*b, plan);
            }
            // A parallel square transform already synchronized on its last
            // radix pair. Other paths still need to rendezvous here.
            if constexpr(std::is_same<Word,
                                      vst_packed_word_t>::value){
                if(parts < 4 || b) barrier.wait();
            }else{
                barrier.wait();
            }
        }

        size_t begin = part * a.size() / parts;
        size_t end = (part + 1) * a.size() / parts;
        vst_fused_len2_product(a, b, plan, begin, end);
        barrier.wait();

        vst_inverse2_outer_parallel_part(
            a, plan, part, parts, barrier);
        finish(part, parts);
    };

    std::vector<std::thread> workers;
    workers.reserve(parts - 1);
    for(size_t part = 1; part < parts; ++part)
        workers.emplace_back(run_half, part);
    run_half(0);
    for(size_t i = 0; i < workers.size(); ++i) workers[i].join();
}
#endif
#endif

static size_t vst_bit_length(const precn_t &a){
    if(a.rsiz == 0) return 0;
    uint64_t top = a.a[a.rsiz - 1];
    size_t bits = 0;
    while(top){
        ++bits;
        top >>= 1;
    }
    return (a.rsiz - 1) * 64 + bits;
}

static size_t vst_digit_count(const precn_t &a, unsigned int bits){
    size_t length = vst_bit_length(a);
    return (length + bits - 1) / bits;
}

static uint64_t vst_digit(const precn_t &a, size_t index,
                          unsigned int bits){
    size_t bit = index * bits;
    size_t limb = bit >> 6;
    unsigned int shift = (unsigned int)(bit & 63);
    uint64_t value = a.a[limb] >> shift;
    if(shift + bits > 64 && limb + 1 < a.rsiz)
        value |= a.a[limb + 1] << (64 - shift);
    return value & (((uint64_t)1 << bits) - 1);
}

static inline uint64_t vst_mersenne61_push(uint64_t r, uint64_t limb){
    const uint64_t mod = ((uint64_t)1 << 61) - 1;
    // 2^64 == 8 (mod 2^61-1).  Fold both the ordinary high bits and the
    // carry from limb+r*8 back into the 61-bit residue.
    uint64_t add = r << 3;
    uint64_t sum = limb + add;
    uint64_t carry = sum < limb;
    r = (sum & mod) + (sum >> 61) + (carry << 3);
    if(r >= mod) r -= mod;
    return r;
}

static void vst_load_digits(std::vector<vst_word_t> &out, size_t n,
                            const precn_t &a, size_t digits,
                            unsigned int bits){
    out.resize(n);
    memset(out.data(), 0, n * sizeof(vst_word_t));
    for(size_t i = 0; i < digits; ++i){
        double digit = (double)vst_digit(a, i, bits);
        for(size_t lane = 0; lane < 4; ++lane) out[i].v[lane] = digit;
    }
}

#if PRECN_VST_HAVE_AVX2
template<class Word>
static uint64_t vst_load_digits2(std::vector<Word> &out, size_t n,
                                 const precn_t &a, size_t digits,
                                 unsigned int bits){
    out.resize(n >> 1);
    uint64_t residue = 0;
    if(bits == 16){
        size_t used_words = (digits + 1) >> 1;
        if(used_words > out.size()){
            fputs("mul_vst tantrum: packed digit buffer is too small\n",
                  stderr);
            std::abort();
        }
        memset(out.data() + used_words, 0,
               (out.size() - used_words) * sizeof(Word));
        for(size_t pos = a.rsiz; pos > 0; --pos){
            size_t i = pos - 1;
            uint64_t x = a.a[i];
            residue = vst_mersenne61_push(residue, x);
            uint32_t d0 = (uint32_t)(x & 0xffffu);
            uint32_t d1 = (uint32_t)((x >> 16) & 0xffffu);
            uint32_t d2 = (uint32_t)((x >> 32) & 0xffffu);
            uint32_t d3 = (uint32_t)(x >> 48);
            size_t word = i << 1;
            if(word < used_words)
                vst_store_digit_pair(out[word], d0, d1);
            if(word + 1 < used_words)
                vst_store_digit_pair(out[word + 1], d2, d3);
        }
        return residue;
    }
    memset(out.data(), 0, (n >> 1) * sizeof(Word));
    for(size_t i = a.rsiz; i > 0; --i)
        residue = vst_mersenne61_push(residue, a.a[i - 1]);
    for(size_t i = 0; i < digits; i += 2){
        uint32_t x0 = (uint32_t)vst_digit(a, i, bits);
        uint32_t x1 = 0;
        if(i + 1 < digits) x1 = (uint32_t)vst_digit(a, i + 1, bits);
        vst_store_digit_pair(out[i >> 1], x0, x1);
    }
    return residue;
}
#endif

static uint32_t vst_reduce_u53(uint64_t x, uint32_t mod){
    return (uint32_t)vst_reduce_scalar((double)x, (double)mod,
                                       1.0 / (double)mod);
}

static uint32_t vst_mul_mod_u32(uint32_t a, uint32_t b, uint32_t mod){
    return (uint32_t)vst_reduce_scalar((double)a * b, (double)mod,
                                       1.0 / (double)mod);
}

static uint64_t vst_mersenne61_mod(const precn_t &a){
    uint64_t r = 0;
    for(size_t i = a.rsiz; i > 0; --i)
        r = vst_mersenne61_push(r, a.a[i - 1]);
    return r;
}

static uint64_t vst_mersenne61_mul(uint64_t a, uint64_t b){
    const uint64_t mod = ((uint64_t)1 << 61) - 1;
    uint64_t hi, lo;
    precn_mul_wide(a, b, hi, lo);
    uint64_t r = (lo & mod) + (lo >> 61) + (hi << 3);
    r = (r & mod) + (r >> 61);
    if(r >= mod) r -= mod;
    return r;
}

static void vst_verify_product(const precn_t &out, uint64_t a_residue,
                               uint64_t b_residue){
    uint64_t expected = vst_mersenne61_mul(a_residue, b_residue);
    if(vst_mersenne61_mod(out) != expected){
        fputs("mul_vst tantrum: modulo 2^61-1 verification failed\n", stderr);
        std::abort();
    }
}

static uint32_t vst_residue(const vst_word_t &a, size_t lane){
    double x = a.v[lane];
    if(!(x >= 0.0 && x < (double)VST_MODS[lane]) || x != std::floor(x)){
        fprintf(stderr, "mul_vst tantrum: non-integral residue in lane %zu\n",
                lane);
        std::abort();
    }
    return (uint32_t)x;
}

static uint64_t vst_crt_coefficient(const vst_word_t &a,
                                    uint64_t max_coefficient){
    uint32_t r0 = vst_residue(a, 0);
    uint32_t r1 = vst_residue(a, 1);
    uint32_t d1 = r1 >= r0 ? r1 - r0 : r1 + VST_MODS[1] - r0;
    uint32_t t1 = vst_mul_mod_u32(d1, VST_INV_P0_MOD_P1, VST_MODS[1]);
    uint64_t x01 = r0 + (uint64_t)VST_MODS[0] * t1;

    uint32_t r2 = vst_residue(a, 2);
    uint32_t x2 = vst_reduce_u53(x01, VST_MODS[2]);
    uint32_t d2 = r2 >= x2 ? r2 - x2 : r2 + VST_MODS[2] - x2;
    uint32_t t2 = vst_mul_mod_u32(d2, VST_INV_P01_MOD_P2, VST_MODS[2]);
    if(t2 > (UINT64_MAX - x01) / VST_P01){
        fprintf(stderr,
                "mul_vst tantrum: CRT overflow r=(%u,%u,%u) t=(%u,%u)\n",
                r0, r1, r2, t1, t2);
        std::abort();
    }
    uint64_t value = x01 + VST_P01 * t2;
    if(value > max_coefficient ||
       vst_reduce_u53(value, VST_MODS[3]) != vst_residue(a, 3)){
        fputs("mul_vst tantrum: CRT checksum mismatch\n", stderr);
        std::abort();
    }
    return value;
}

static precn_t vst_collect(const std::vector<vst_word_t> &data,
                           size_t coefficients, uint64_t max_coefficient,
                           unsigned int bits){
    size_t extra_digits = (53 + bits - 1) / bits + 1;
    size_t capacity = ((coefficients + extra_digits) * bits + 63) / 64 + 1;
    precn_t out;
    if(out.asiz < capacity){
        out.a = (uint64_t*)realloc(out.a, capacity * sizeof(uint64_t));
        out.asiz = capacity;
    }
    memset(out.a, 0, capacity * sizeof(uint64_t));

    size_t digit_index = 0;
    uint64_t carry = 0;
    uint64_t mask = ((uint64_t)1 << bits) - 1;
    for(size_t i = 0; i < coefficients; ++i){
        uint64_t coefficient = vst_crt_coefficient(data[i], max_coefficient);
        if(UINT64_MAX - coefficient < carry){
            fputs("mul_vst tantrum: carry overflow\n", stderr);
            std::abort();
        }
        uint64_t value = coefficient + carry;
        size_t bit = digit_index * bits;
        size_t limb = bit >> 6;
        unsigned int shift = (unsigned int)(bit & 63);
        uint64_t digit = value & mask;
        out.a[limb] |= digit << shift;
        if(shift + bits > 64) out.a[limb + 1] |= digit >> (64 - shift);
        ++digit_index;
        carry = value >> bits;
    }
    while(carry){
        size_t bit = digit_index * bits;
        size_t limb = bit >> 6;
        unsigned int shift = (unsigned int)(bit & 63);
        uint64_t digit = carry & mask;
        out.a[limb] |= digit << shift;
        if(shift + bits > 64) out.a[limb + 1] |= digit >> (64 - shift);
        ++digit_index;
        carry >>= bits;
    }
    out.rsiz = (digit_index * bits + 63) / 64;
    while(out.rsiz && out.a[out.rsiz - 1] == 0) --out.rsiz;
    if(out.rsiz == 0) out.a[0] = 0;
    return out;
}

#if PRECN_VST_HAVE_AVX2
static uint64_t vst_crt_coefficient2(const vst_word_t &a, size_t item,
                                     uint64_t max_coefficient){
    size_t offset = (item & 1) << 1;
    double x0 = a.v[offset];
    double x1 = a.v[offset + 1];
    if(!(x0 >= 0.0 && x0 < (double)VST_PACKED_MODS[0]) ||
       !(x1 >= 0.0 && x1 < (double)VST_PACKED_MODS[1]) ||
       x0 != std::floor(x0) || x1 != std::floor(x1)){
        fputs("mul_vst tantrum: non-integral packed residue\n", stderr);
        std::abort();
    }
    uint32_t r0 = (uint32_t)x0;
    uint32_t r1 = (uint32_t)x1;
    uint32_t d1 = r1 >= r0 ? r1 - r0 :
                  r1 + VST_PACKED_MODS[1] - r0;
    uint32_t t1 = vst_mul_mod_u32(d1, VST_PACKED_INVERSE,
                                  VST_PACKED_MODS[1]);
    uint64_t value = r0 + (uint64_t)VST_PACKED_MODS[0] * t1;
    if(value > max_coefficient){
        fputs("mul_vst tantrum: packed CRT bound mismatch\n", stderr);
        std::abort();
    }
    return value;
}

static uint64_t vst_crt_coefficient2(const vst_packed_word_t &a,
                                     size_t item,
                                     uint64_t max_coefficient){
    size_t offset = (item & 1) << 1;
    uint32_t r0 = a.v[offset];
    uint32_t r1 = a.v[offset + 1];
    if(r0 >= VST_PACKED_MODS[0] || r1 >= VST_PACKED_MODS[1]){
        fputs("mul_vst tantrum: invalid packed residue\n", stderr);
        std::abort();
    }
    uint32_t d1 = r1 >= r0 ? r1 - r0 :
                  r1 + VST_PACKED_MODS[1] - r0;
    uint32_t t1 = vst_mul_mod_u32(d1, VST_PACKED_INVERSE,
                                  VST_PACKED_MODS[1]);
    uint64_t value = r0 + (uint64_t)VST_PACKED_MODS[0] * t1;
    if(value > max_coefficient){
        fputs("mul_vst tantrum: packed CRT bound mismatch\n", stderr);
        std::abort();
    }
    return value;
}

// Reconstruct four adjacent coefficients at once.  Packed transform words are
// laid out as [c0 mod p2, c0 mod p3, c1 mod p2, c1 mod p3], so two shuffles
// turn two words into one p2 vector and one p3 vector.
static inline __m256d vst_crt_coefficients2x4(const vst_word_t *data,
                                              uint64_t max_coefficient){
    __m256d x0 = _mm256_permute4x64_pd(vst_load(data[0]), 0xd8);
    __m256d x1 = _mm256_permute4x64_pd(vst_load(data[1]), 0xd8);
    __m256d r2 = _mm256_permute2f128_pd(x0, x1, 0x20);
    __m256d r3 = _mm256_permute2f128_pd(x0, x1, 0x31);
    __m256d zero = _mm256_setzero_pd();
    __m256d p2 = _mm256_set1_pd((double)VST_PACKED_MODS[0]);
    __m256d p3 = _mm256_set1_pd((double)VST_PACKED_MODS[1]);

#if PRECN_VST_STRICT_CHECKS
    __m256d valid = _mm256_cmp_pd(r2, zero, _CMP_GE_OQ);
    valid = _mm256_and_pd(valid, _mm256_cmp_pd(r2, p2, _CMP_LT_OQ));
    valid = _mm256_and_pd(valid,
                          _mm256_cmp_pd(r2, _mm256_floor_pd(r2), _CMP_EQ_OQ));
    valid = _mm256_and_pd(valid, _mm256_cmp_pd(r3, zero, _CMP_GE_OQ));
    valid = _mm256_and_pd(valid, _mm256_cmp_pd(r3, p3, _CMP_LT_OQ));
    valid = _mm256_and_pd(valid,
                          _mm256_cmp_pd(r3, _mm256_floor_pd(r3), _CMP_EQ_OQ));
    if(_mm256_movemask_pd(valid) != 15){
        fputs("mul_vst tantrum: non-integral packed residue\n", stderr);
        std::abort();
    }
#endif

    __m256d d = _mm256_sub_pd(r3, r2);
    d = _mm256_blendv_pd(d, _mm256_add_pd(d, p3),
                         _mm256_cmp_pd(d, zero, _CMP_LT_OQ));
    __m256d t = vst_mul4(d,
                         _mm256_set1_pd((double)VST_PACKED_INVERSE),
                         p3,
                         _mm256_set1_pd(1.0 /
                                        (double)VST_PACKED_MODS[1]));
#if defined(__FMA__)
    __m256d value = _mm256_fmadd_pd(
        p2, t, r2);
#else
    __m256d value = _mm256_add_pd(r2, _mm256_mul_pd(p2, t));
#endif
#if PRECN_VST_STRICT_CHECKS
    if(_mm256_movemask_pd(_mm256_cmp_pd(
           value, _mm256_set1_pd((double)max_coefficient), _CMP_GT_OQ))){
        fputs("mul_vst tantrum: packed CRT bound mismatch\n", stderr);
        std::abort();
    }
#else
    (void)max_coefficient;
#endif
    return value;
}

static inline __m256d vst_crt_coefficients2x4(
    const vst_packed_word_t *data, uint64_t max_coefficient){
    __m256i packed = _mm256_castsi128_si256(
        _mm_load_si128((const __m128i*)data[0].v));
    packed = _mm256_inserti128_si256(
        packed, _mm_load_si128((const __m128i*)data[1].v), 1);
    packed = _mm256_permutevar8x32_epi32(
        packed, _mm256_setr_epi32(0, 2, 4, 6, 1, 3, 5, 7));
    __m256d r0 = _mm256_cvtepi32_pd(_mm256_castsi256_si128(packed));
    __m256d r1 = _mm256_cvtepi32_pd(
        _mm256_extracti128_si256(packed, 1));
    __m256d zero = _mm256_setzero_pd();
    __m256d p0 = _mm256_set1_pd((double)VST_PACKED_MODS[0]);
    __m256d p1 = _mm256_set1_pd((double)VST_PACKED_MODS[1]);

#if PRECN_VST_STRICT_CHECKS
    __m256d valid = _mm256_cmp_pd(r0, p0, _CMP_LT_OQ);
    valid = _mm256_and_pd(valid, _mm256_cmp_pd(r1, p1, _CMP_LT_OQ));
    if(_mm256_movemask_pd(valid) != 15){
        fputs("mul_vst tantrum: invalid packed residue\n", stderr);
        std::abort();
    }
#endif

    __m256d d = _mm256_sub_pd(r1, r0);
    d = _mm256_blendv_pd(d, _mm256_add_pd(d, p1),
                         _mm256_cmp_pd(d, zero, _CMP_LT_OQ));
    __m256d t = vst_mul4(
        d, _mm256_set1_pd((double)VST_PACKED_INVERSE), p1,
        _mm256_set1_pd(1.0 / (double)VST_PACKED_MODS[1]));
#if defined(__FMA__)
    __m256d value = _mm256_fmadd_pd(p0, t, r0);
#else
    __m256d value = _mm256_add_pd(r0, _mm256_mul_pd(p0, t));
#endif
#if PRECN_VST_STRICT_CHECKS
    if(_mm256_movemask_pd(_mm256_cmp_pd(
           value, _mm256_set1_pd((double)max_coefficient), _CMP_GT_OQ))){
        fputs("mul_vst tantrum: packed CRT bound mismatch\n", stderr);
        std::abort();
    }
#else
    (void)max_coefficient;
#endif
    return value;
}

static inline __m256i vst_u52_to_u64x4(__m256d value){
    // For an integer x in [0, 2^52), the mantissa bits of x + 2^52 are x.
    // This replaces four scalar double-to-u64 conversions with two AVX2 ops.
    const __m256d bias = _mm256_set1_pd(4503599627370496.0);
    const __m256i bias_bits = _mm256_set1_epi64x(
        (long long)0x4330000000000000ULL);
    return _mm256_sub_epi64(
        _mm256_castpd_si256(_mm256_add_pd(value, bias)), bias_bits);
}

template<class Word>
static precn_t vst_collect2(const std::vector<Word> &data,
                            size_t coefficients, uint64_t max_coefficient,
                            unsigned int bits,
                            const uint64_t *parallel_coefficients = nullptr){
    size_t extra_digits = (53 + bits - 1) / bits + 1;
    size_t capacity = ((coefficients + extra_digits) * bits + 63) / 64 + 1;
    precn_t out;
    if(out.asiz < capacity){
        out.a = (uint64_t*)realloc(out.a, capacity * sizeof(uint64_t));
        out.asiz = capacity;
    }
    if(bits == 16){
        size_t overwritten = coefficients >> 2;
        memset(out.a + overwritten, 0,
               (capacity - overwritten) * sizeof(uint64_t));
    }else{
        memset(out.a, 0, capacity * sizeof(uint64_t));
    }

    size_t digit_index = 0;
    uint64_t carry = 0;
    uint64_t mask = ((uint64_t)1 << bits) - 1;
    size_t i = 0;
    if(bits == 16){
        if(parallel_coefficients){
            for(; i + 3 < coefficients; i += 4){
                uint64_t packed_digits = 0;
                for(size_t lane = 0; lane < 4; ++lane){
                    uint64_t value = parallel_coefficients[i + lane] + carry;
                    packed_digits |= (value & 0xffffu) << (lane * 16);
                    carry = value >> 16;
                }
                out.a[i >> 2] = packed_digits;
            }
        }else{
            for(; i + 3 < coefficients; i += 4){
                alignas(32) uint64_t reconstructed[4];
                _mm256_store_si256((__m256i*)reconstructed,
                    vst_u52_to_u64x4(vst_crt_coefficients2x4(
                        &data[i >> 1], max_coefficient)));
                uint64_t packed_digits = 0;
                for(size_t lane = 0; lane < 4; ++lane){
                    uint64_t value = reconstructed[lane] + carry;
                    packed_digits |= (value & 0xffffu) << (lane * 16);
                    carry = value >> 16;
                }
                out.a[i >> 2] = packed_digits;
            }
        }
        digit_index = i;
    }else{
        for(; i + 3 < coefficients; i += 4){
            alignas(32) uint64_t reconstructed[4];
            _mm256_store_si256((__m256i*)reconstructed,
                vst_u52_to_u64x4(vst_crt_coefficients2x4(
                    &data[i >> 1], max_coefficient)));
            for(size_t lane = 0; lane < 4; ++lane){
                uint64_t value = reconstructed[lane] + carry;
                size_t bit = digit_index * bits;
                size_t limb = bit >> 6;
                unsigned int shift = (unsigned int)(bit & 63);
                uint64_t digit = value & mask;
                out.a[limb] |= digit << shift;
                if(shift + bits > 64)
                    out.a[limb + 1] |= digit >> (64 - shift);
                ++digit_index;
                carry = value >> bits;
            }
        }
    }
    for(; i < coefficients; ++i){
        uint64_t coefficient = parallel_coefficients ?
            parallel_coefficients[i] :
            vst_crt_coefficient2(data[i >> 1], i, max_coefficient);
        uint64_t value = coefficient + carry;
        size_t bit = digit_index * bits;
        size_t limb = bit >> 6;
        unsigned int shift = (unsigned int)(bit & 63);
        uint64_t digit = value & mask;
        out.a[limb] |= digit << shift;
        if(shift + bits > 64) out.a[limb + 1] |= digit >> (64 - shift);
        ++digit_index;
        carry = value >> bits;
    }
    while(carry){
        size_t bit = digit_index * bits;
        size_t limb = bit >> 6;
        unsigned int shift = (unsigned int)(bit & 63);
        uint64_t digit = carry & mask;
        out.a[limb] |= digit << shift;
        if(shift + bits > 64) out.a[limb + 1] |= digit >> (64 - shift);
        ++digit_index;
        carry >>= bits;
    }
    out.rsiz = (digit_index * bits + 63) / 64;
    while(out.rsiz && out.a[out.rsiz - 1] == 0) --out.rsiz;
    if(out.rsiz == 0) out.a[0] = 0;
    return out;
}

#endif

precn_t mul_vst(const precn_t &a, const precn_t &b){
    if(a.rsiz == 0 || b.rsiz == 0) return precn_t();
#if defined(PRECN_VST_PROFILE) && PRECN_VST_PROFILE
    double profile_begin = vst_profile_now();
#endif
    unsigned int digit_bits = 16;
    size_t da = vst_digit_count(a, digit_bits);
    size_t db = vst_digit_count(b, digit_bits);
    if(da == 0 || db == 0) return precn_t();

    size_t n = 1;
    while(n < da + db) n <<= 1;
    uint64_t terms = std::min(da, db);
    uint64_t digit_max = ((uint64_t)1 << digit_bits) - 1;
    uint64_t max_coefficient = terms * digit_max * digit_max;
    bool packed = false;
#if PRECN_VST_HAVE_AVX2
    packed = max_coefficient < VST_PACKED_PRODUCT;
#endif
    if(n > VST_MAX_TRANSFORM) return mul_ntt(a, b);
    if(max_coefficient >= (1ULL << 53)){
        fputs("mul_vst tantrum: coefficient exceeds exact double range\n",
              stderr);
        std::abort();
    }

    const vst_plan_t &plan = vst_get_plan(n, packed);
    static thread_local vst_workspace_t workspace;
    bool square = &a == &b;
#if defined(PRECN_VST_PROFILE) && PRECN_VST_PROFILE
    vst_profile.setup += vst_profile_now() - profile_begin;
    ++vst_profile.calls;
#endif

#if PRECN_VST_HAVE_AVX2
    if(packed){
        auto multiply_packed = [&](auto &left, auto &right) -> precn_t {
#if defined(PRECN_VST_PROFILE) && PRECN_VST_PROFILE
        profile_begin = vst_profile_now();
#endif
        uint64_t a_residue = vst_load_digits2(left, n, a, da,
                                              digit_bits);
        uint64_t b_residue = a_residue;
        if(!square)
            b_residue = vst_load_digits2(right, n, b, db, digit_bits);
#if defined(PRECN_VST_PROFILE) && PRECN_VST_PROFILE
        vst_profile.load += vst_profile_now() - profile_begin;
        profile_begin = vst_profile_now();
#endif
        bool use_parallel = false;
#if !defined(__EMSCRIPTEN__)
        use_parallel = n >= VST_PARALLEL_TRANSFORM &&
                       precn_ntt_thread_parallel_enabled();
#endif
        size_t coefficient_count = da + db - 1;
        uint64_t *parallel_coefficients = nullptr;
#if !defined(__EMSCRIPTEN__)
        if(use_parallel && coefficient_count >= ((size_t)1 << 19)){
            workspace.coefficients.resize(coefficient_count);
            parallel_coefficients = workspace.coefficients.data();
        }
        auto finish_pipeline = [&](size_t part, size_t parts){
            if(!parallel_coefficients) return;
            size_t groups = coefficient_count >> 2;
            size_t first = part * groups / parts;
            size_t last = (part + 1) * groups / parts;
            for(size_t group = first; group < last; ++group){
                __m256d value = vst_crt_coefficients2x4(
                    &left[group << 1], max_coefficient);
                _mm256_storeu_si256(
                    (__m256i*)(&parallel_coefficients[group << 2]),
                    vst_u52_to_u64x4(value));
            }
            if(part == 0){
                for(size_t i = groups << 2; i < coefficient_count; ++i)
                    parallel_coefficients[i] = vst_crt_coefficient2(
                        left[i >> 1], i, max_coefficient);
            }
        };
#endif
        bool pipeline_done = false;
#if !defined(__EMSCRIPTEN__)
        if(use_parallel){
            vst_pointwise_inverse2_parallel(left, square ? nullptr : &right,
                                            plan, true, finish_pipeline);
            pipeline_done = true;
#if defined(PRECN_VST_PROFILE) && PRECN_VST_PROFILE
            vst_profile.pipeline += vst_profile_now() - profile_begin;
            profile_begin = vst_profile_now();
#endif
        }
#endif
        if(!pipeline_done){
            vst_forward2_outer(left, plan);
            if(!square) vst_forward2_outer(right, plan);
#if defined(PRECN_VST_PROFILE) && PRECN_VST_PROFILE
            vst_profile.forward += vst_profile_now() - profile_begin;
            profile_begin = vst_profile_now();
#endif
            vst_fused_len2_product(
                left, square ? nullptr : &right, plan,
                0, left.size());
#if defined(PRECN_VST_PROFILE) && PRECN_VST_PROFILE
            vst_profile.pointwise += vst_profile_now() - profile_begin;
            profile_begin = vst_profile_now();
#endif
            vst_inverse2_outer(left, plan);
#if defined(PRECN_VST_PROFILE) && PRECN_VST_PROFILE
            vst_profile.inverse += vst_profile_now() - profile_begin;
            profile_begin = vst_profile_now();
#endif
        }
        precn_t out = vst_collect2(left, coefficient_count,
                                   max_coefficient, digit_bits,
                                   parallel_coefficients);
#if defined(PRECN_VST_PROFILE) && PRECN_VST_PROFILE
        vst_profile.collect += vst_profile_now() - profile_begin;
        profile_begin = vst_profile_now();
#endif
        vst_verify_product(out, a_residue, b_residue);
#if defined(PRECN_VST_PROFILE) && PRECN_VST_PROFILE
        vst_profile.verify += vst_profile_now() - profile_begin;
#endif
        return out;
        };

        bool compact_data = n >= VST_COMPACT_DATA_SERIAL_TRANSFORM;
#if !defined(__EMSCRIPTEN__)
        compact_data = compact_data ||
            (n >= VST_COMPACT_DATA_TRANSFORM &&
             precn_ntt_thread_parallel_enabled());
#endif
        if(compact_data)
            return multiply_packed(workspace.a2_compact,
                                   workspace.b2_compact);
        return multiply_packed(workspace.a2, workspace.b2);
    }
#endif

    vst_load_digits(workspace.a, n, a, da, digit_bits);
    if(!square) vst_load_digits(workspace.b, n, b, db, digit_bits);

#if !defined(__EMSCRIPTEN__)
    if(!square && n >= ((size_t)1 << 17) &&
       precn_ntt_thread_parallel_enabled()){
        std::vector<vst_word_t> *right = &workspace.b;
        std::thread worker([right, &plan]{ vst_forward(*right, plan); });
        vst_forward(workspace.a, plan);
        worker.join();
    }else
#endif
    {
        vst_forward(workspace.a, plan);
        if(!square) vst_forward(workspace.b, plan);
    }

    vst_pointwise(workspace.a, square ? nullptr : &workspace.b, plan);
    vst_inverse(workspace.a, plan);
    return vst_collect(workspace.a, da + db - 1, max_coefficient, digit_bits);
}
