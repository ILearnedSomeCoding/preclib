#include"../prec.hpp"

#include<map>
#include<memory>
#include<mutex>
#include<vector>

#if !defined(__EMSCRIPTEN__)
#include<atomic>
#include<condition_variable>
#include<functional>
#include<thread>
#endif

#if defined(PRECN_FORCE_NO_SIMD) && PRECN_FORCE_NO_SIMD
#define PRECN_NTT_HAVE_AVX2 0
#elif defined(__AVX2__) || defined(_M_AVX2)
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
#if defined(COUNT_NTT_CALLS) && COUNT_NTT_CALLS
static std::atomic<uint64_t> ntt_call_count[32];
static std::atomic<uint64_t> ntt_high_call_count[32];

static void ntt_record_call(size_t n, bool high){
    unsigned int bucket = 0;
    while(n > 1){ ++bucket; n >>= 1; }
    if(bucket > 31) bucket = 31;
    (high ? ntt_high_call_count[bucket] : ntt_call_count[bucket]).fetch_add(
        1, std::memory_order_relaxed);
}

void precn_ntt_call_profile_dump(){
    for(unsigned int i = 0; i < 32; ++i){
        uint64_t normal = ntt_call_count[i].load(std::memory_order_relaxed);
        uint64_t high = ntt_high_call_count[i].load(std::memory_order_relaxed);
        if(normal || high)
            fprintf(stderr, "ntt_calls 2^%u normal=%llu high=%llu\n", i,
                    (unsigned long long)normal, (unsigned long long)high);
    }
}
#endif

static const uint32_t NTT_MOD4 = 998244353u;
static const uint32_t NTT_MOD5 = 1004535809u;
static const uint32_t NTT_ROOT4 = 3u;
static const uint32_t NTT_ROOT5 = 3u;

#ifndef NTT_26BIT_THRESHOLD
#define NTT_26BIT_THRESHOLD ((size_t)1 << 30)
#endif

#ifndef NTT_64BIT_THRESHOLD
#define NTT_64BIT_THRESHOLD ((size_t)1 << 30)
#endif




#if !defined(__EMSCRIPTEN__)
// A transform has a barrier after every layer, so creating threads per layer
// loses badly.  Keep a small pool alive and let every worker claim contiguous
// ranges of butterflies.  The caller participates as one worker.
class ntt_thread_pool_t{
    std::mutex run_mutex;
    std::mutex mutex;
    std::condition_variable have_work;
    std::condition_variable finished;
    std::vector<std::thread> workers;
    std::function<void(size_t, size_t)> task;
    std::atomic<size_t> next;
    size_t task_count;
    size_t grain;
    size_t total_size;
    size_t done;
    uint64_t generation;
    bool stop;

    void worker(){
        std::unique_lock<std::mutex> lock(mutex);
        uint64_t seen_generation = 0;
        for(;;){
            have_work.wait(lock, [this, &seen_generation]{ return generation != seen_generation || stop; });
            if(stop) return;
            seen_generation = generation;
            lock.unlock();
            for(;;){
                size_t block = next.fetch_add(1, std::memory_order_relaxed);
                if(block >= task_count) break;
                size_t begin = block * grain;
                task(begin, std::min(begin + grain, total_size));
            }
            lock.lock();
            if(++done == workers.size()) finished.notify_one();
        }
    }

public:
    explicit ntt_thread_pool_t(unsigned int thread_count)
        : next(0), task_count(0), grain(1), total_size(0), done(0), generation(0), stop(false){
        for(unsigned int i = 1; i < thread_count; ++i) workers.emplace_back(&ntt_thread_pool_t::worker, this);
    }

    ~ntt_thread_pool_t(){
        {
            std::lock_guard<std::mutex> lock(mutex);
            stop = true;
        }
        have_work.notify_all();
        for(size_t i = 0; i < workers.size(); ++i) workers[i].join();
    }

    void run(size_t total, const std::function<void(size_t, size_t)> &f){
        if(total == 0){
            return;
        }
        if(workers.empty() || total == 1){
            f(0, total);
            return;
        }

        std::lock_guard<std::mutex> serial(run_mutex);
        size_t thread_count = workers.size() + 1;
        size_t local_grain = std::max((size_t)256, total / (thread_count * 4));
        size_t blocks = (total + local_grain - 1) / local_grain;
        {
            std::lock_guard<std::mutex> lock(mutex);
            task = f;
            grain = local_grain;
            task_count = blocks;
            total_size = total;
            next.store(0, std::memory_order_relaxed);
            done = 0;
            ++generation;
        }
        have_work.notify_all();
        for(;;){
            size_t block = next.fetch_add(1, std::memory_order_relaxed);
            if(block >= blocks) break;
            size_t begin = block * local_grain;
            f(begin, std::min(begin + local_grain, total));
        }
        std::unique_lock<std::mutex> lock(mutex);
        finished.wait(lock, [this]{ return done == workers.size(); });
    }

    void run_tasks(size_t count, const std::function<void(size_t)> &f){
        if(count == 0) return;
        if(workers.empty() || count == 1){
            for(size_t i = 0; i < count; ++i) f(i);
            return;
        }

        std::lock_guard<std::mutex> serial(run_mutex);
        {
            std::lock_guard<std::mutex> lock(mutex);
            task = [&f](size_t begin, size_t end){
                for(size_t i = begin; i < end; ++i) f(i);
            };
            grain = 1;
            task_count = count;
            total_size = count;
            next.store(0, std::memory_order_relaxed);
            done = 0;
            ++generation;
        }
        have_work.notify_all();
        for(;;){
            size_t index = next.fetch_add(1, std::memory_order_relaxed);
            if(index >= count) break;
            f(index);
        }
        std::unique_lock<std::mutex> lock(mutex);
        finished.wait(lock, [this]{ return done == workers.size(); });
    }
};

static std::mutex ntt_pool_config_mutex;
static std::unique_ptr<ntt_thread_pool_t> ntt_pool;
static unsigned int ntt_pool_threads;
static thread_local bool ntt_parallel_disabled;
static thread_local size_t ntt_parallel_min_transform;

bool precn_ntt_thread_parallel_enabled(){
    return !ntt_parallel_disabled;
}

void precn_set_ntt_thread_parallel(bool enabled){
    ntt_parallel_disabled = !enabled;
}

size_t precn_ntt_parallel_min_transform(){
    return ntt_parallel_min_transform;
}

void precn_set_ntt_parallel_min_transform(size_t min_transform){
    ntt_parallel_min_transform = min_transform;
}

static bool ntt_parallel_allowed(size_t transform_size){
    return !ntt_parallel_disabled &&
        transform_size >= ntt_parallel_min_transform;
}

static unsigned int ntt_default_thread_count(){
    unsigned int n = std::thread::hardware_concurrency();
    // Two independent residue convolutions already expose useful parallelism.
    // A pool sized to every logical CPU makes the small/medium NTT layers pay
    // much more synchronization and cache traffic than arithmetic on a mini
    // PC.  Callers with a genuinely wider memory subsystem can still request
    // a different value through precn_set_ntt_threads().
    return n > 1 ? 2 : 1;
}

static ntt_thread_pool_t &ntt_pool_get(){
    std::lock_guard<std::mutex> lock(ntt_pool_config_mutex);
    if(!ntt_pool){
        ntt_pool_threads = ntt_default_thread_count();
        ntt_pool = std::make_unique<ntt_thread_pool_t>(ntt_pool_threads);
    }
    return *ntt_pool;
}

static unsigned int ntt_worker_count(){
    ntt_pool_get();
    return ntt_pool_threads;
}

void precn_set_ntt_threads(unsigned int threads){
    std::lock_guard<std::mutex> lock(ntt_pool_config_mutex);
    if(ntt_pool) return;
    ntt_pool_threads = threads ? threads : ntt_default_thread_count();
    ntt_pool = std::make_unique<ntt_thread_pool_t>(ntt_pool_threads);
}

template<class F>
static void ntt_parallel_for(size_t total, F f){
    if(ntt_parallel_disabled){
        if(total) f(0, total);
        return;
    }
    ntt_pool_get().run(total, std::function<void(size_t, size_t)>(f));
}

template<class F>
static void ntt_parallel_tasks(size_t count, F f){
    ntt_pool_get().run_tasks(count, std::function<void(size_t)>(f));
}
#else
void precn_set_ntt_threads(unsigned int){}

bool precn_ntt_thread_parallel_enabled(){ return false; }
void precn_set_ntt_thread_parallel(bool){}
size_t precn_ntt_parallel_min_transform(){ return 0; }
void precn_set_ntt_parallel_min_transform(size_t){}
static bool ntt_parallel_allowed(size_t){ return false; }

template<class F>
static void ntt_parallel_for(size_t total, F f){
    if(total) f(0, total);
}
#endif

static const mont_ctx_t NTT_CTX[] = {
    {469762049u, 3u, 469762047u, 460175152u, 67108855u},
    {1811939329u, 13u, 1811939327u, 959408210u, 671088638u},
    {2013265921u, 31u, 2013265919u, 1172168163u, 268435454u},
    {998244353u, 3u, 998244351u, 932051910u, 301989884u},
    {1004535809u, 3u, 1004535807u, 542374313u, 276824060u},
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
    // Plans are immutable after construction.  Sharing them prevents the
    // independent binary-split workers from rebuilding identical O(n) root
    // tables in their thread-local caches.
    static std::mutex plans_mutex;
    static std::map<size_t, std::shared_ptr<ntt_mod_plan_t> > plans[5];
    static thread_local std::map<size_t, std::shared_ptr<ntt_mod_plan_t> > local_plans[5];
    size_t slot = mod == NTT_MOD1 ? 0 : mod == NTT_MOD2 ? 1 : mod == NTT_MOD3 ? 2 : mod == NTT_MOD4 ? 3 : 4;
    std::map<size_t, std::shared_ptr<ntt_mod_plan_t> >::iterator local =
        local_plans[slot].find(n);
    if(local != local_plans[slot].end()) return *local->second;

    std::lock_guard<std::mutex> lock(plans_mutex);
    std::map<size_t, std::shared_ptr<ntt_mod_plan_t> >::iterator found = plans[slot].find(n);
    if(found == plans[slot].end()){
        found = plans[slot].emplace(n,
            std::make_shared<ntt_mod_plan_t>(ntt_make_mod_plan(n, mod, root))).first;
    }
    local_plans[slot].emplace(n, found->second);
    return *found->second;
}

#if defined(NTT_RADIX4_FORWARD) && NTT_RADIX4_FORWARD
static void ntt_forward_radix4(std::vector<uint32_t> &a, const ntt_mod_plan_t &p){
    size_t n = a.size();
    const mont_ctx_t &c = p.c;
    const std::vector<uint32_t> &roots = p.roots_f;
    uint32_t mod = c.mod;
    size_t len = n;

    for(; len >= 4; len >>= 2){
        size_t quarter = len >> 2;
        size_t half = len >> 1;
        size_t block_count = n / len;
        auto transform_blocks = [&](size_t block_begin, size_t block_end){
        for(size_t block = block_begin; block < block_end; ++block){
            size_t base = block * len;
            size_t j = 0;
#if PRECN_NTT_HAVE_AVX2
            for(; j + 7 < quarter; j += 8){
                uint32_t *a0 = a.data() + base + j;
                uint32_t *a1 = a0 + quarter;
                uint32_t *a2 = a1 + quarter;
                uint32_t *a3 = a2 + quarter;
                __m256i u0 = _mm256_loadu_si256((const __m256i*)a0);
                __m256i u2 = _mm256_loadu_si256((const __m256i*)a2);
                __m256i s02 = ntt_add8(u0, u2, mod);
                __m256i d02 = ntt_sub8(u0, u2, mod);
                __m256i h0 = mont_mul8(c, d02, _mm256_loadu_si256((const __m256i*)(roots.data() + half + j)));
                __m256i u1 = _mm256_loadu_si256((const __m256i*)a1);
                __m256i u3 = _mm256_loadu_si256((const __m256i*)a3);
                __m256i s13 = ntt_add8(u1, u3, mod);
                __m256i d13 = ntt_sub8(u1, u3, mod);
                __m256i h1 = mont_mul8(c, d13, _mm256_loadu_si256((const __m256i*)(roots.data() + half + quarter + j)));
                __m256i w2 = _mm256_loadu_si256((const __m256i*)(roots.data() + quarter + j));
                _mm256_storeu_si256((__m256i*)a0, ntt_add8(s02, s13, mod));
                _mm256_storeu_si256((__m256i*)a1, mont_mul8(c, ntt_sub8(s02, s13, mod), w2));
                _mm256_storeu_si256((__m256i*)a2, ntt_add8(h0, h1, mod));
                _mm256_storeu_si256((__m256i*)a3, mont_mul8(c, ntt_sub8(h0, h1, mod), w2));
            }
#endif
            for(; j < quarter; ++j){
                uint32_t u0 = a[base + j];
                uint32_t u1 = a[base + quarter + j];
                uint32_t u2 = a[base + half + j];
                uint32_t u3 = a[base + half + quarter + j];
                uint32_t s02 = u0 + u2;
                if(s02 >= mod) s02 -= mod;
                uint32_t d02 = u0 >= u2 ? u0 - u2 : u0 + mod - u2;
                uint32_t s13 = u1 + u3;
                if(s13 >= mod) s13 -= mod;
                uint32_t d13 = u1 >= u3 ? u1 - u3 : u1 + mod - u3;
                uint32_t h0 = mont_mul(c, d02, roots[half + j]);
                uint32_t h1 = mont_mul(c, d13, roots[half + quarter + j]);
                uint32_t y0 = s02 + s13;
                if(y0 >= mod) y0 -= mod;
                uint32_t y1 = s02 >= s13 ? s02 - s13 : s02 + mod - s13;
                uint32_t y2 = h0 + h1;
                if(y2 >= mod) y2 -= mod;
                uint32_t y3 = h0 >= h1 ? h0 - h1 : h0 + mod - h1;
                a[base + j] = y0;
                a[base + quarter + j] = mont_mul(c, y1, roots[quarter + j]);
                a[base + half + j] = y2;
                a[base + half + quarter + j] = mont_mul(c, y3, roots[quarter + j]);
            }
        }
        };
        if(ntt_parallel_allowed(n) && n >= ((size_t)1 << 16) && block_count > 1)
            ntt_parallel_for(block_count, transform_blocks);
        else transform_blocks(0, block_count);
    }

    if(len == 2){
        for(size_t i = 0; i < n; i += 2){
            uint32_t u = a[i], v = a[i + 1];
            uint32_t sum = u + v;
            if(sum >= mod) sum -= mod;
            a[i] = sum;
            a[i + 1] = u >= v ? u - v : u + mod - v;
        }
    }
}
#endif

static void ntt_forward(std::vector<uint32_t> &a, const ntt_mod_plan_t &p){
#if defined(NTT_RADIX4_FORWARD) && NTT_RADIX4_FORWARD
    ntt_forward_radix4(a, p);
    return;
#endif
    size_t n = a.size();
    const mont_ctx_t &c = p.c;
    const std::vector<uint32_t> &roots = p.roots_f;
    uint32_t mod = c.mod;

    // ProtoNTT's forward-DIF/inverse-DIT ordering leaves both transformed
    // operands bit-reversed, so pointwise multiplication needs no permutation.
    for(size_t len = n; len >= 2; len >>= 1){
        size_t half = len >> 1;
        size_t block_count = n / len;
        auto transform_blocks = [&](size_t block_begin, size_t block_end){
        for(size_t block = block_begin; block < block_end; ++block){
            size_t i = block * len;
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
        };
        if(ntt_parallel_allowed(n) && n >= ((size_t)1 << 16) && block_count > 1)
            ntt_parallel_for(block_count, transform_blocks);
        else transform_blocks(0, block_count);
    }
}

static void ntt_inverse(std::vector<uint32_t> &a, const ntt_mod_plan_t &p){
    size_t n = a.size();
    const mont_ctx_t &c = p.c;
    const std::vector<uint32_t> &roots = p.roots_i;
    uint32_t mod = c.mod;

    for(size_t len = 2; len <= n; len <<= 1){
        size_t half = len >> 1;
        size_t block_count = n / len;
        auto transform_blocks = [&](size_t block_begin, size_t block_end){
        for(size_t block = block_begin; block < block_end; ++block){
            size_t i = block * len;
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
        };
        if(ntt_parallel_allowed(n) && n >= ((size_t)1 << 16) && block_count > 1)
            ntt_parallel_for(block_count, transform_blocks);
        else transform_blocks(0, block_count);
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

static void ntt_digits(const precn_t &a, std::vector<uint32_t> &d){
    d.resize(a.rsiz * 4);
    for(size_t i = 0; i < a.rsiz; ++i){
        uint64_t limb = a.a[i];
        d[i * 4] = (uint32_t)(limb & 0xFFFFu);
        d[i * 4 + 1] = (uint32_t)((limb >> 16) & 0xFFFFu);
        d[i * 4 + 2] = (uint32_t)((limb >> 32) & 0xFFFFu);
        d[i * 4 + 3] = (uint32_t)(limb >> 48);
    }
    while(!d.empty() && d.back() == 0) d.pop_back();
}

// 26-bit digits halve the transform size for the Pi-scale products where the
// three-modulus reconstruction below is cheaper than another NTT level.
static void ntt_digits26(const precn_t &a, std::vector<uint32_t> &d){
    const uint32_t mask = (1u << 26) - 1;
    d.clear();
    d.reserve((a.rsiz * 64 + 25) / 26);
    for(size_t bit = 0; bit < a.rsiz * 64; bit += 26){
        size_t limb = bit >> 6;
        unsigned shift = (unsigned)(bit & 63);
        uint64_t value = a.a[limb] >> shift;
        if(shift > 38 && limb + 1 < a.rsiz)
            value |= a.a[limb + 1] << (64 - shift);
        d.push_back((uint32_t)(value & mask));
    }
    while(!d.empty() && d.back() == 0) d.pop_back();
}

static void ntt_zero(std::vector<uint32_t> &a, size_t n){
    a.resize(n);
    memset(a.data(), 0, n * sizeof(uint32_t));
}

static void ntt_load_inputs(const std::vector<uint32_t> &a,
                            const std::vector<uint32_t> &b,
                            size_t n,
                            const ntt_mod_plan_t &p,
                            std::vector<uint32_t> &out,
                            std::vector<uint32_t> &scratch){
    ntt_zero(out, n);
    ntt_zero(scratch, n);
    for(size_t i = 0; i < a.size(); ++i) out[i] = mont_in(p.c, a[i]);
    for(size_t i = 0; i < b.size(); ++i) scratch[i] = mont_in(p.c, b[i]);
}

static void ntt_finish_convolution(std::vector<uint32_t> &out,
                                   std::vector<uint32_t> &scratch,
                                   const ntt_mod_plan_t &p){
    size_t n = out.size();
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

static void ntt_convolve_plan(const std::vector<uint32_t> &a,
                              const std::vector<uint32_t> &b,
                              size_t n,
                              const ntt_mod_plan_t &p,
                              std::vector<uint32_t> &out,
                              std::vector<uint32_t> &scratch){
    ntt_load_inputs(a, b, n, p, out, scratch);
    ntt_forward(out, p);
    ntt_forward(scratch, p);
    ntt_finish_convolution(out, scratch, p);
}

static void ntt_negacyclic_convolve_plan(const std::vector<uint32_t> &a,
                                         const std::vector<uint32_t> &b,
                                         size_t n,
                                         const ntt_mod_plan_t &p,
                                         std::vector<uint32_t> &out,
                                         std::vector<uint32_t> &scratch){
    // psi is a primitive 2n-th root.  Multiplying input digit i by psi^i
    // turns an ordinary n-point cyclic convolution into one modulo X^n+1.
    const mont_ctx_t &c = p.c;
    uint64_t psi_exponent = (c.mod - 1) / (n << 1);
    uint32_t psi = mont_pow(c, c.root, psi_exponent);
    // mont_pow accepts an ordinary residue, while psi is already in
    // Montgomery form.  Build psi^-1 from the primitive root directly.
    uint32_t psi_inv = mont_pow(c, c.root, c.mod - 1 - psi_exponent);
    ntt_zero(out, n);
    ntt_zero(scratch, n);
    uint32_t pw = c.one;
    for(size_t i = 0; i < n; ++i){
        out[i] = mont_mul(c, mont_in(c, a[i]), pw);
        scratch[i] = mont_mul(c, mont_in(c, b[i]), pw);
        pw = mont_mul(c, pw, psi);
    }
    ntt_forward(out, p);
    ntt_forward(scratch, p);
    for(size_t i = 0; i < n; ++i) out[i] = mont_mul(c, out[i], scratch[i]);
    ntt_inverse(out, p);
    pw = c.one;
    for(size_t i = 0; i < n; ++i){
        out[i] = mont_reduce(c, mont_mul(c, out[i], pw));
        pw = mont_mul(c, pw, psi_inv);
    }
}

static void ntt_negacyclic_square_plan(const std::vector<uint32_t> &a,
                                       size_t n,
                                       const ntt_mod_plan_t &p,
                                       std::vector<uint32_t> &out){
    const mont_ctx_t &c = p.c;
    uint64_t psi_exponent = (c.mod - 1) / (n << 1);
    uint32_t psi = mont_pow(c, c.root, psi_exponent);
    uint32_t psi_inv = mont_pow(c, c.root, c.mod - 1 - psi_exponent);
    ntt_zero(out, n);
    uint32_t pw = c.one;
    for(size_t i = 0; i < n; ++i){
        out[i] = mont_mul(c, mont_in(c, a[i]), pw);
        pw = mont_mul(c, pw, psi);
    }
    ntt_forward(out, p);
    for(size_t i = 0; i < n; ++i) out[i] = mont_mul(c, out[i], out[i]);
    ntt_inverse(out, p);
    pw = c.one;
    for(size_t i = 0; i < n; ++i){
        out[i] = mont_reduce(c, mont_mul(c, out[i], pw));
        pw = mont_mul(c, pw, psi_inv);
    }
}

static void ntt_convolve_mod(const std::vector<uint32_t> &a,
                             const std::vector<uint32_t> &b,
                             size_t n,
                             uint32_t mod,
                             uint32_t root,
                             std::vector<uint32_t> &out,
                             std::vector<uint32_t> &scratch){
    ntt_convolve_plan(a, b, n, ntt_get_mod_plan(n, mod, root), out, scratch);
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

struct ntt_u96_t{
    uint64_t lo;
    uint32_t hi;
};

static ntt_u96_t ntt_crt3_u96(uint32_t r1, uint32_t r2, uint32_t r3){
    const uint64_t m1m2 = (uint64_t)NTT_MOD1 * NTT_MOD2;
    static uint32_t inv_m1m2_m3 = mod_inv_u32(m1m2 % NTT_MOD3, NTT_MOD3);
    uint64_t x12 = ntt_crt2(r1, r2);
    uint64_t t2 = (x12 - r1) / NTT_MOD1;
    uint64_t x12_m3 = ((uint64_t)r1 % NTT_MOD3 +
        (uint64_t)(NTT_MOD1 % NTT_MOD3) * (t2 % NTT_MOD3) % NTT_MOD3) % NTT_MOD3;
    uint64_t d3 = r3 >= x12_m3 ? r3 - x12_m3 :
        r3 + (uint64_t)NTT_MOD3 - x12_m3;
    uint64_t t3 = d3 * inv_m1m2_m3 % NTT_MOD3;

    // m1*m2 is below 2^60 and t3 below 2^31.  A 64-by-32 product fits
    // exactly in this 96-bit pair, keeping the large-digit path int128-free.
    uint64_t low_part = (uint64_t)(uint32_t)m1m2 * t3;
    uint64_t high_part = (m1m2 >> 32) * t3;
    uint64_t lo = low_part + (high_part << 32);
    uint32_t hi = (uint32_t)(high_part >> 32) + (lo < low_part);
    uint64_t old = lo;
    lo += x12;
    hi += lo < old;
    return ntt_u96_t{lo, hi};
}

struct ntt_u192_t{
    uint64_t v[3];
};

static void ntt_u192_add(ntt_u192_t &a, const ntt_u192_t &b){
    uint64_t old = a.v[0];
    a.v[0] += b.v[0];
    uint64_t carry = a.v[0] < old;
    old = a.v[1];
    a.v[1] += b.v[1];
    uint64_t carry1 = a.v[1] < old;
    old = a.v[1];
    a.v[1] += carry;
    carry = carry1 | (a.v[1] < old);
    old = a.v[2];
    a.v[2] += b.v[2];
    carry1 = a.v[2] < old;
    old = a.v[2];
    a.v[2] += carry;
    (void)carry1;
}

static ntt_u192_t ntt_u192_mul_u32(const ntt_u192_t &a, uint32_t b){
    ntt_u192_t r = {{0, 0, 0}};
    uint64_t carry = 0;
    for(size_t i = 0; i < 3; ++i){
        uint64_t low_part = (uint64_t)(uint32_t)a.v[i] * b;
        uint64_t high_part = (a.v[i] >> 32) * b;
        uint64_t lo = low_part + (high_part << 32);
        uint64_t hi = (high_part >> 32) + (lo < low_part);
        uint64_t old = lo;
        lo += carry;
        hi += lo < old;
        r.v[i] = lo;
        carry = hi;
    }
    return r;
}

static uint32_t ntt_u192_mod_u32(const ntt_u192_t &a, uint32_t mod){
    uint64_t rem = 0;
    for(size_t i = 3; i > 0; --i){
        uint64_t word = a.v[i - 1];
        rem = (rem * 4294967296ULL + (word >> 32)) % mod;
        rem = (rem * 4294967296ULL + (uint32_t)word) % mod;
    }
    return (uint32_t)rem;
}

static ntt_u192_t ntt_crt5_u192(uint32_t r1, uint32_t r2, uint32_t r3,
                                 uint32_t r4, uint32_t r5){
    const uint32_t mods[5] = {NTT_MOD1, NTT_MOD2, NTT_MOD3, NTT_MOD4, NTT_MOD5};
    const uint32_t residues[5] = {r1, r2, r3, r4, r5};
    ntt_u192_t x = {{0, 0, 0}};
    ntt_u192_t product = {{1, 0, 0}};
    for(size_t i = 0; i < 5; ++i){
        uint32_t mod = mods[i];
        uint32_t xmod = ntt_u192_mod_u32(x, mod);
        uint32_t delta = residues[i] >= xmod ? residues[i] - xmod :
            residues[i] + mod - xmod;
        uint32_t inv = mod_inv_u32(ntt_u192_mod_u32(product, mod), mod);
        uint32_t factor = (uint64_t)delta * inv % mod;
        ntt_u192_add(x, ntt_u192_mul_u32(product, factor));
        product = ntt_u192_mul_u32(product, mod);
    }
    return x;
}

static precn_t ntt_from_residues5_64(const std::vector<uint32_t> &r1,
                                     const std::vector<uint32_t> &r2,
                                     const std::vector<uint32_t> &r3,
                                     const std::vector<uint32_t> &r4,
                                     const std::vector<uint32_t> &r5){
    precn_t r;
    r.asiz = std::max<size_t>(r1.size() + 4, 1);
    r.a = (uint64_t*)realloc(r.a, r.asiz * sizeof(uint64_t));
    memset(r.a, 0, r.asiz * sizeof(uint64_t));

    ntt_u192_t carry = {{0, 0, 0}};
    size_t i = 0;
    for(; i < r1.size(); ++i){
        ntt_u192_t value = ntt_crt5_u192(r1[i], r2[i], r3[i], r4[i], r5[i]);
        ntt_u192_add(value, carry);
        r.a[i] = value.v[0];
        carry.v[0] = value.v[1];
        carry.v[1] = value.v[2];
        carry.v[2] = 0;
    }
    while(carry.v[0] || carry.v[1]){
        r.a[i++] = carry.v[0];
        carry.v[0] = carry.v[1];
        carry.v[1] = 0;
    }
    r.rsiz = i;
    while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
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

static void ntt_put_digit26(precn_t &r, size_t id, uint32_t digit){
    size_t bit = id * 26;
    size_t limb = bit >> 6;
    unsigned shift = (unsigned)(bit & 63);
    if(limb + 1 >= r.asiz){
        size_t old = r.asiz;
        while(r.asiz <= limb + 1) r.asiz <<= 1;
        r.a = (uint64_t*)realloc(r.a, r.asiz * sizeof(uint64_t));
        memset(r.a + old, 0, (r.asiz - old) * sizeof(uint64_t));
    }
    r.a[limb] |= (uint64_t)digit << shift;
    if(shift > 38) r.a[limb + 1] |= (uint64_t)digit >> (64 - shift);
}

static precn_t ntt_from_residues3_26(const std::vector<uint32_t> &r1,
                                      const std::vector<uint32_t> &r2,
                                      const std::vector<uint32_t> &r3){
    const uint32_t mask = (1u << 26) - 1;
    precn_t r;
    r.asiz = std::max<size_t>((r1.size() * 26 + 63) / 64 + 4, 1);
    r.a = (uint64_t*)realloc(r.a, r.asiz * sizeof(uint64_t));
    memset(r.a, 0, r.asiz * sizeof(uint64_t));

    uint64_t carry = 0;
    size_t digit_id = 0;
    for(size_t i = 0; i < r1.size(); ++i, ++digit_id){
        ntt_u96_t value = ntt_crt3_u96(r1[i], r2[i], r3[i]);
        uint64_t old = value.lo;
        value.lo += carry;
        value.hi += value.lo < old;
        ntt_put_digit26(r, digit_id, (uint32_t)(value.lo & mask));
        carry = (value.lo >> 26) | ((uint64_t)value.hi << 38);
    }
    while(carry){
        ntt_put_digit26(r, digit_id++, (uint32_t)(carry & mask));
        carry >>= 26;
    }
    r.rsiz = (digit_id * 26 + 63) / 64;
    while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}

static precn_t ntt_from_residues2(const std::vector<uint32_t> &r1,
                                  const std::vector<uint32_t> &r2,
                                  size_t skip_digits = 0){
    precn_t r;
    r.asiz = std::max<size_t>((r1.size() > skip_digits ?
        r1.size() - skip_digits : 0) / 4 + 8, 1);
    r.a = (uint64_t*) realloc(r.a, r.asiz * sizeof(uint64_t));
    memset(r.a, 0, r.asiz * sizeof(uint64_t));
    r.rsiz = 0;

    if(skip_digits == 0){
        uint64_t carry = 0;
        uint64_t packed = 0;
        size_t out_limbs = 0;
        unsigned int packed_digits = 0;

        for(size_t i = 0; i < r1.size(); ++i){
            uint64_t cur = ntt_crt2(r1[i], r2[i]) + carry;
            packed |= (cur & 0xFFFFu) << (packed_digits * 16);
            carry = cur >> 16;
            if(++packed_digits == 4){
                r.a[out_limbs++] = packed;
                packed = 0;
                packed_digits = 0;
            }
        }
        while(carry){
            packed |= (carry & 0xFFFFu) << (packed_digits * 16);
            carry >>= 16;
            if(++packed_digits == 4){
                r.a[out_limbs++] = packed;
                packed = 0;
                packed_digits = 0;
            }
        }
        if(packed_digits) r.a[out_limbs++] = packed;
        r.rsiz = out_limbs;

        while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
        if(r.rsiz == 0) r.a[0] = 0;
        return r;
    }

    uint64_t carry = 0;
    size_t digit_id = 0;
    for(size_t i = 0; i < r1.size(); ++i, ++digit_id){
        uint64_t cur = ntt_crt2(r1[i], r2[i]) + carry;
        if(digit_id >= skip_digits){
            size_t out_digit = digit_id - skip_digits;
            r.a[out_digit >> 2] |= (cur & 0xFFFFu) << ((out_digit & 3) * 16);
        }
        carry = cur >> 16;
    }
    while(carry){
        if(digit_id >= skip_digits){
            size_t out_digit = digit_id - skip_digits;
            ntt_put_digit(r, out_digit, (uint32_t)(carry & 0xFFFFu));
        }
        ++digit_id;
        carry >>= 16;
    }
    r.rsiz = digit_id <= skip_digits ? 0 : (digit_id - skip_digits + 3) >> 2;

    while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}

static precn_t ntt_from_residues3(const std::vector<uint32_t> &r1,
                                  const std::vector<uint32_t> &r2,
                                  const std::vector<uint32_t> &r3,
                                  size_t skip_digits = 0){
    precn_t r;
    r.asiz = std::max<size_t>((r1.size() > skip_digits ?
        r1.size() - skip_digits : 0) / 4 + 8, 1);
    r.a = (uint64_t*) realloc(r.a, r.asiz * sizeof(uint64_t));
    memset(r.a, 0, r.asiz * sizeof(uint64_t));
    r.rsiz = 0;

    uint64_t carry = 0;
    size_t digit_id = 0;
    for(size_t i = 0; i < r1.size(); ++i, ++digit_id){
        uint64_t cur = ntt_crt3(r1[i], r2[i], r3[i]) + carry;
        if(digit_id >= skip_digits){
            size_t out_digit = digit_id - skip_digits;
            r.a[out_digit >> 2] |= (cur & 0xFFFFu) << ((out_digit & 3) * 16);
        }
        carry = cur >> 16;
    }
    while(carry){
        if(digit_id >= skip_digits){
            size_t out_digit = digit_id - skip_digits;
            ntt_put_digit(r, out_digit, (uint32_t)(carry & 0xFFFFu));
        }
        ++digit_id;
        carry >>= 16;
    }
    r.rsiz = digit_id <= skip_digits ? 0 : (digit_id - skip_digits + 3) >> 2;

    while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}

// Recover only the high digits when the incoming carry can be proved from a
// short guard region.  A coefficient is at most terms*(B-1)^2, so the carry
// entering an omitted prefix is bounded by ceil(Cmax/(B-1)).  Propagating that
// whole interval through four 64-bit guard limbs either collapses to one value
// (the usual case) or safely falls back to the ordinary full carry scan.
static precn_t ntt_high_from_residues2_guarded(const std::vector<uint32_t> &r1,
                                               const std::vector<uint32_t> &r2,
                                               size_t skip_digits, size_t terms){
    const size_t guard_digits = 16;
    const uint64_t digit_base = 1ULL << 16;
    if(skip_digits < guard_digits || skip_digits >= r1.size())
        return ntt_from_residues2(r1, r2, skip_digits);

    uint64_t coeff_max = (uint64_t)terms * NTT_DIGIT_MAX2;
    uint64_t carry_lo = 0;
    uint64_t carry_hi = (coeff_max + digit_base - 2) / (digit_base - 1);
    for(size_t i = skip_digits - guard_digits; i < skip_digits; ++i){
        uint64_t coefficient = ntt_crt2(r1[i], r2[i]);
        carry_lo = (coefficient + carry_lo) >> 16;
        carry_hi = (coefficient + carry_hi) >> 16;
    }
    if(carry_lo != carry_hi)
        return ntt_from_residues2(r1, r2, skip_digits);

    precn_t r;
    r.asiz = std::max<size_t>((r1.size() - skip_digits) / 4 + 8, 1);
    r.a = (uint64_t*)realloc(r.a, r.asiz * sizeof(uint64_t));
    memset(r.a, 0, r.asiz * sizeof(uint64_t));
    r.rsiz = 0;

    uint64_t carry = carry_lo;
    uint64_t packed = 0;
    size_t out_limbs = 0;
    unsigned int packed_digits = 0;
    for(size_t i = skip_digits; i < r1.size(); ++i){
        uint64_t cur = ntt_crt2(r1[i], r2[i]) + carry;
        packed |= (cur & 0xFFFFu) << (packed_digits * 16);
        carry = cur >> 16;
        if(++packed_digits == 4){
            r.a[out_limbs++] = packed;
            packed = 0;
            packed_digits = 0;
        }
    }
    while(carry){
        packed |= (carry & 0xFFFFu) << (packed_digits * 16);
        carry >>= 16;
        if(++packed_digits == 4){
            r.a[out_limbs++] = packed;
            packed = 0;
            packed_digits = 0;
        }
    }
    if(packed_digits) r.a[out_limbs++] = packed;
    r.rsiz = out_limbs;
    while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}

static int ntt_two_mod_ok(size_t terms){
    uint64_t m12 = (uint64_t)NTT_MOD1 * NTT_MOD2;
    return terms <= (m12 - 1) / NTT_DIGIT_MAX2;
}

struct ntt_workspace_t{
    std::vector<uint32_t> digits_a;
    std::vector<uint32_t> digits_b;
    std::vector<uint32_t> residue1;
    std::vector<uint32_t> residue2;
    std::vector<uint32_t> residue3;
    std::vector<uint32_t> scratch1;
    std::vector<uint32_t> scratch2;
    std::vector<uint32_t> scratch3;
};

struct ntt64_workspace_t{
    std::vector<uint32_t> input_a[5];
    std::vector<uint32_t> input_b[5];
    std::vector<uint32_t> residue[5];
    std::vector<uint32_t> scratch[5];
};

static void ntt_limbs_mod(const precn_t &a, uint32_t mod,
                          std::vector<uint32_t> &out){
    out.resize(a.rsiz);
    for(size_t i = 0; i < a.rsiz; ++i) out[i] = (uint32_t)(a.a[i] % mod);
}

#if !defined(__EMSCRIPTEN__)
static void ntt_forward64_item(ntt64_workspace_t &workspace,
                               const ntt_mod_plan_t *plans[5], size_t item){
    size_t index = item >> 1;
    if(item & 1) ntt_forward(workspace.scratch[index], *plans[index]);
    else ntt_forward(workspace.residue[index], *plans[index]);
}

static void ntt_forward64_batch(ntt64_workspace_t &workspace,
                                const ntt_mod_plan_t *plans[5],
                                size_t first, size_t count){
    std::vector<std::thread> workers;
    workers.reserve(count - 1);
    for(size_t i = 1; i < count; ++i){
        workers.emplace_back([&, item = first + i]{
            ntt_parallel_disabled = true;
            ntt_forward64_item(workspace, plans, item);
        });
    }
    bool old = ntt_parallel_disabled;
    ntt_parallel_disabled = true;
    ntt_forward64_item(workspace, plans, first);
    ntt_parallel_disabled = old;
    for(size_t i = 0; i < workers.size(); ++i) workers[i].join();
}

static void ntt_finish64_batch(ntt64_workspace_t &workspace,
                               const ntt_mod_plan_t *plans[5],
                               size_t first, size_t count){
    std::vector<std::thread> workers;
    workers.reserve(count - 1);
    for(size_t i = 1; i < count; ++i){
        workers.emplace_back([&, index = first + i]{
            ntt_parallel_disabled = true;
            ntt_finish_convolution(workspace.residue[index], workspace.scratch[index],
                                   *plans[index]);
        });
    }
    bool old = ntt_parallel_disabled;
    ntt_parallel_disabled = true;
    ntt_finish_convolution(workspace.residue[first], workspace.scratch[first],
                           *plans[first]);
    ntt_parallel_disabled = old;
    for(size_t i = 0; i < workers.size(); ++i) workers[i].join();
}

static void ntt_convolve5_phased(ntt64_workspace_t &workspace,
                                 const ntt_mod_plan_t *plans[5], size_t n){
    for(size_t i = 0; i < 5; ++i)
        ntt_load_inputs(workspace.input_a[i], workspace.input_b[i], n, *plans[i],
                        workspace.residue[i], workspace.scratch[i]);
    ntt_forward64_batch(workspace, plans, 0, 4);
    ntt_forward64_batch(workspace, plans, 4, 4);
    ntt_forward64_batch(workspace, plans, 8, 2);
    ntt_finish64_batch(workspace, plans, 0, 2);
    ntt_finish64_batch(workspace, plans, 2, 2);
    ntt_finish64_batch(workspace, plans, 4, 1);
}
#endif

static precn_t mul_ntt64_impl(const precn_t &a, const precn_t &b){
    static thread_local ntt64_workspace_t workspace;
    size_t n = 1;
    while(n < a.rsiz + b.rsiz) n <<= 1;
    if(n > NTT_MAX_TRANSFORM) return mul_fft(a, b);

    const uint32_t mods[5] = {NTT_MOD1, NTT_MOD2, NTT_MOD3, NTT_MOD4, NTT_MOD5};
    const uint32_t roots[5] = {NTT_ROOT1, NTT_ROOT2, NTT_ROOT3, NTT_ROOT4, NTT_ROOT5};
    const ntt_mod_plan_t *plans[5];
    for(size_t i = 0; i < 5; ++i){
        ntt_limbs_mod(a, mods[i], workspace.input_a[i]);
        ntt_limbs_mod(b, mods[i], workspace.input_b[i]);
        plans[i] = &ntt_get_mod_plan(n, mods[i], roots[i]);
    }
#if !defined(__EMSCRIPTEN__)
    if(ntt_parallel_allowed(n) && n >= ((size_t)1 << 17) && ntt_worker_count() == 2){
        ntt_convolve5_phased(workspace, plans, n);
    }else
#endif
    {
        for(size_t i = 0; i < 5; ++i){
        ntt_convolve_plan(workspace.input_a[i], workspace.input_b[i], n,
            *plans[i],
            workspace.residue[i], workspace.scratch[i]);
        }
    }
    return ntt_from_residues5_64(workspace.residue[0], workspace.residue[1],
                                 workspace.residue[2], workspace.residue[3],
                                 workspace.residue[4]);
}

#if !defined(__EMSCRIPTEN__)
static void ntt_convolve3_phased(const std::vector<uint32_t> &a,
                                 const std::vector<uint32_t> &b, size_t n,
                                 const ntt_mod_plan_t &p1,
                                 const ntt_mod_plan_t &p2,
                                 const ntt_mod_plan_t &p3,
                                 ntt_workspace_t &workspace){
    ntt_load_inputs(a, b, n, p1, workspace.residue1, workspace.scratch1);
    ntt_load_inputs(a, b, n, p2, workspace.residue2, workspace.scratch2);
    ntt_load_inputs(a, b, n, p3, workspace.residue3, workspace.scratch3);

    // The established two-modulus path parallelizes individual transforms,
    // not entire convolutions.  Do the same here: the transform kernels are
    // independent while their serial layer state stays private to a thread.
    std::thread f1([&]{
        ntt_parallel_disabled = true;
        ntt_forward(workspace.residue1, p1);
    });
    std::thread f2([&]{
        ntt_parallel_disabled = true;
        ntt_forward(workspace.scratch1, p1);
    });
    std::thread f3([&]{
        ntt_parallel_disabled = true;
        ntt_forward(workspace.residue2, p2);
    });
    ntt_parallel_disabled = true;
    ntt_forward(workspace.scratch2, p2);
    ntt_parallel_disabled = false;
    f1.join();
    f2.join();
    f3.join();

    std::thread f4([&]{
        ntt_parallel_disabled = true;
        ntt_forward(workspace.residue3, p3);
    });
    ntt_parallel_disabled = true;
    ntt_forward(workspace.scratch3, p3);
    ntt_parallel_disabled = false;
    f4.join();

    std::thread first([&]{
        ntt_parallel_disabled = true;
        ntt_finish_convolution(workspace.residue1, workspace.scratch1, p1);
    });
    ntt_parallel_disabled = true;
    ntt_finish_convolution(workspace.residue2, workspace.scratch2, p2);
    ntt_parallel_disabled = false;
    first.join();
    ntt_finish_convolution(workspace.residue3, workspace.scratch3, p3);
}
#endif

static precn_t mul_ntt26_impl(const precn_t &a, const precn_t &b){
    static thread_local ntt_workspace_t workspace;
    std::vector<uint32_t> &da = workspace.digits_a;
    std::vector<uint32_t> &db = workspace.digits_b;
    ntt_digits26(a, da);
    ntt_digits26(b, db);
    if(da.empty() || db.empty()) return precn_t();

    size_t n = 1;
    while(n < da.size() + db.size()) n <<= 1;
    if(n > NTT_MAX_TRANSFORM) return mul_fft(a, b);

    const ntt_mod_plan_t &plan1 = ntt_get_mod_plan(n, NTT_MOD1, NTT_ROOT1);
    const ntt_mod_plan_t &plan2 = ntt_get_mod_plan(n, NTT_MOD2, NTT_ROOT2);
    const ntt_mod_plan_t &plan3 = ntt_get_mod_plan(n, NTT_MOD3, NTT_ROOT3);
#if !defined(__EMSCRIPTEN__)
    if(ntt_parallel_allowed(n) && n >= ((size_t)1 << 17) && ntt_worker_count() == 2){
        ntt_convolve3_phased(da, db, n, plan1, plan2, plan3, workspace);
    }else
#endif
    {
        ntt_convolve_plan(da, db, n, plan1, workspace.residue1, workspace.scratch1);
        ntt_convolve_plan(da, db, n, plan2, workspace.residue2, workspace.scratch1);
        ntt_convolve_plan(da, db, n, plan3, workspace.residue3, workspace.scratch1);
    }
    return ntt_from_residues3_26(workspace.residue1, workspace.residue2,
                                 workspace.residue3);
}

static precn_t mul_ntt_impl(const precn_t &a, const precn_t &b,
                            size_t skip_digits){
    if(a.rsiz == 0 || b.rsiz == 0) return precn_t();
    if(std::max(a.rsiz, b.rsiz) <= 192){
        precn_t r = mul_basic(a, b);
        return skip_digits ? r >> (skip_digits * 16) : r;
    }
    size_t limbs = std::max(a.rsiz, b.rsiz);
    if(std::min(a.rsiz, b.rsiz) >= NTT_64BIT_THRESHOLD){
        precn_t r = mul_ntt64_impl(a, b);
        return skip_digits ? r >> (skip_digits * 16) : r;
    }

    if(limbs > NTT_MAX_LIMBS){
        precn_t r = mul_fft(a, b);
        return skip_digits ? r >> (skip_digits * 16) : r;
    }
    if(skip_digits == 0 && std::min(a.rsiz, b.rsiz) >= NTT_26BIT_THRESHOLD)
        return mul_ntt26_impl(a, b);

    static thread_local ntt_workspace_t workspace;
    std::vector<uint32_t> &da = workspace.digits_a;
    std::vector<uint32_t> &db = workspace.digits_b;
    bool square = &a == &b;
    ntt_digits(a, da);
    if(!square) ntt_digits(b, db);
    if(da.empty() || (!square && db.empty())) return precn_t();

    size_t n = 1;
    while(n < da.size() + (square ? da.size() : db.size())) n <<= 1;
    if(n > NTT_MAX_TRANSFORM){
        precn_t r = mul_fft(a, b);
        return skip_digits ? r >> (skip_digits * 16) : r;
    }
#if defined(COUNT_NTT_CALLS) && COUNT_NTT_CALLS
    ntt_record_call(n, skip_digits != 0);
#endif

    const ntt_mod_plan_t &plan1 = ntt_get_mod_plan(n, NTT_MOD1, NTT_ROOT1);
    const ntt_mod_plan_t &plan2 = ntt_get_mod_plan(n, NTT_MOD2, NTT_ROOT2);
    if(square){
        std::vector<uint32_t> &residue1 = workspace.residue1;
        std::vector<uint32_t> &residue2 = workspace.residue2;
        ntt_zero(residue1, n);
        ntt_zero(residue2, n);
        for(size_t i = 0; i < da.size(); ++i){
            residue1[i] = mont_in(plan1.c, da[i]);
            residue2[i] = mont_in(plan2.c, da[i]);
        }
#if !defined(__EMSCRIPTEN__)
        if(ntt_parallel_allowed(n) && n >= ((size_t)1 << 15) && ntt_worker_count() == 2){
            std::thread first([&]{
                ntt_parallel_disabled = true;
                ntt_forward(residue1, plan1);
            });
            ntt_parallel_disabled = true;
            ntt_forward(residue2, plan2);
            ntt_parallel_disabled = false;
            first.join();

            std::thread finish([&]{
                ntt_parallel_disabled = true;
                ntt_finish_convolution(residue1, residue1, plan1);
            });
            ntt_parallel_disabled = true;
            ntt_finish_convolution(residue2, residue2, plan2);
            ntt_parallel_disabled = false;
            finish.join();
        }else
#endif
        {
            ntt_forward(residue1, plan1);
            ntt_forward(residue2, plan2);
            ntt_finish_convolution(residue1, residue1, plan1);
            ntt_finish_convolution(residue2, residue2, plan2);
        }
        return skip_digits ? ntt_high_from_residues2_guarded(residue1, residue2,
            skip_digits, da.size()) : ntt_from_residues2(residue1, residue2);
    }
#if !defined(__EMSCRIPTEN__)
    if(ntt_parallel_allowed(n) && n >= ((size_t)1 << 17) && ntt_worker_count() == 2){
        std::vector<uint32_t> &residue1 = workspace.residue1;
        std::vector<uint32_t> &residue2 = workspace.residue2;
        std::vector<uint32_t> &scratch1 = workspace.scratch1;
        std::vector<uint32_t> &scratch2 = workspace.scratch2;

        // There are four independent forward transforms here: two inputs for
        // each CRT modulus.  Running only one full convolution per core left
        // half the available cores idle during the forward half of a large
        // multiplication.  Keep the transforms serial internally so they do
        // not contend for the shared layer pool.
        ntt_load_inputs(da, db, n, plan1, residue1, scratch1);
        ntt_load_inputs(da, db, n, plan2, residue2, scratch2);
        std::thread f1([&]{
            ntt_parallel_disabled = true;
            ntt_forward(residue1, plan1);
        });
        std::thread f2([&]{
            ntt_parallel_disabled = true;
            ntt_forward(scratch1, plan1);
        });
        std::thread f3([&]{
            ntt_parallel_disabled = true;
            ntt_forward(residue2, plan2);
        });
#if defined(NTT_OUTER_INNER_ASSIST) && NTT_OUTER_INNER_ASSIST
        ntt_forward(scratch2, plan2);
#else
        ntt_parallel_disabled = true;
        ntt_forward(scratch2, plan2);
        ntt_parallel_disabled = false;
#endif
        f1.join();
        f2.join();
        f3.join();

        std::thread first([&]{
            // This is already an outer worker.  Keep the inverse serial so
            // a task never recursively asks the shared NTT pool for workers.
            ntt_parallel_disabled = true;
            ntt_finish_convolution(residue1, scratch1, plan1);
        });
#if defined(NTT_OUTER_INNER_ASSIST) && NTT_OUTER_INNER_ASSIST
        ntt_finish_convolution(residue2, scratch2, plan2);
#else
        ntt_parallel_disabled = true;
        ntt_finish_convolution(residue2, scratch2, plan2);
        ntt_parallel_disabled = false;
#endif
        first.join();
    }else if(ntt_parallel_allowed(n) && n >= ((size_t)1 << 15) && ntt_worker_count() == 2){
        std::vector<uint32_t> &residue1 = workspace.residue1;
        std::vector<uint32_t> &residue2 = workspace.residue2;
        std::vector<uint32_t> &scratch1 = workspace.scratch1;
        std::vector<uint32_t> &scratch2 = workspace.scratch2;
        ntt_parallel_tasks(2, [&](size_t task_index){
            bool old = ntt_parallel_disabled;
            ntt_parallel_disabled = true;
            if(task_index == 0)
                ntt_convolve_plan(da, db, n, plan1, residue1, scratch1);
            else
                ntt_convolve_plan(da, db, n, plan2, residue2, scratch2);
            ntt_parallel_disabled = old;
        });
    }else
#endif
    {
        ntt_convolve_plan(da, db, n, plan1, workspace.residue1, workspace.scratch1);
        ntt_convolve_plan(da, db, n, plan2, workspace.residue2, workspace.scratch1);
    }

    if(ntt_two_mod_ok(std::min(da.size(), db.size()))){
        return skip_digits ? ntt_high_from_residues2_guarded(workspace.residue1,
            workspace.residue2, skip_digits, std::min(da.size(), db.size())) :
            ntt_from_residues2(workspace.residue1, workspace.residue2);
    }

    ntt_convolve_mod(da, db, n, NTT_MOD3, NTT_ROOT3, workspace.residue3, workspace.scratch1);
    return ntt_from_residues3(workspace.residue1, workspace.residue2,
                              workspace.residue3, skip_digits);
}

#if PRECN_NTT_HAVE_AVX2
// Each logical coefficient occupies three adjacent words: residues modulo
// NTT_MOD1, NTT_MOD2, and NTT_MOD3.  AVX2 widens those three 32-bit lanes to
// 64-bit products for Montgomery reduction in one instruction stream.
static __m128i ntt3_load(const uint32_t *p){
    return _mm_set_epi32(0, (int)p[2], (int)p[1], (int)p[0]);
}

static void ntt3_store(uint32_t *p, __m128i x){
    _mm_storel_epi64((__m128i*)p, x);
    p[2] = (uint32_t)_mm_extract_epi32(x, 2);
}

static __m128i ntt3_mont_mul(__m128i a, __m128i b){
    const __m256i mod = _mm256_set_epi32(0, 0, 0, (int)NTT_MOD3,
                                          0, (int)NTT_MOD2, 0, (int)NTT_MOD1);
    const __m256i ninv = _mm256_set_epi32(0, 0, 0, (int)NTT_CTX[2].ninv,
                                           0, (int)NTT_CTX[1].ninv, 0, (int)NTT_CTX[0].ninv);
    const __m256i sign = _mm256_set1_epi64x((long long)0x8000000000000000ULL);
    const __m256i mod_shift = _mm256_slli_epi64(mod, 32);
    const __m256i order = _mm256_set_epi32(7, 6, 5, 4, 7, 5, 3, 1);
    __m256i x = _mm256_mul_epu32(_mm256_cvtepu32_epi64(a), _mm256_cvtepu32_epi64(b));
    __m256i q = _mm256_mul_epu32(x, ninv);
    x = _mm256_add_epi64(x, _mm256_mul_epu32(q, mod));
    __m256i below = _mm256_cmpgt_epi64(_mm256_xor_si256(mod_shift, sign),
                                       _mm256_xor_si256(x, sign));
    x = _mm256_sub_epi64(x, _mm256_andnot_si256(below, mod_shift));
    return _mm256_castsi256_si128(_mm256_permutevar8x32_epi32(x, order));
}

static __m128i ntt3_add(__m128i a, __m128i b){
    const __m128i mod = _mm_set_epi32(0, (int)NTT_MOD3, (int)NTT_MOD2, (int)NTT_MOD1);
    const __m128i sign = _mm_set1_epi32((int)0x80000000u);
    __m128i sum = _mm_add_epi32(a, b);
    __m128i wrap_limit = _mm_sub_epi32(mod, b);
    __m128i ge = _mm_cmpgt_epi32(_mm_xor_si128(a, sign), _mm_xor_si128(_mm_sub_epi32(wrap_limit, _mm_set1_epi32(1)), sign));
    return _mm_sub_epi32(sum, _mm_and_si128(ge, mod));
}

static __m128i ntt3_sub(__m128i a, __m128i b){
    const __m128i mod = _mm_set_epi32(0, (int)NTT_MOD3, (int)NTT_MOD2, (int)NTT_MOD1);
    const __m128i sign = _mm_set1_epi32((int)0x80000000u);
    __m128i lt = _mm_cmplt_epi32(_mm_xor_si128(a, sign), _mm_xor_si128(b, sign));
    return _mm_add_epi32(_mm_sub_epi32(a, b), _mm_and_si128(lt, mod));
}

static __m128i ntt3_roots(const std::vector<uint32_t> &r1, const std::vector<uint32_t> &r2,
                           const std::vector<uint32_t> &r3, size_t i){
    return _mm_set_epi32(0, (int)r3[i], (int)r2[i], (int)r1[i]);
}

static void ntt3_forward(std::vector<uint32_t> &v, const ntt_mod_plan_t &p1,
                         const ntt_mod_plan_t &p2, const ntt_mod_plan_t &p3){
    size_t n = v.size() / 3;
    for(size_t len = n; len >= 2; len >>= 1){
        size_t half = len >> 1;
        for(size_t base = 0; base < n; base += len){
            for(size_t j = 0; j < half; ++j){
                uint32_t *lo = v.data() + (base + j) * 3;
                uint32_t *hi = lo + half * 3;
                __m128i a = ntt3_load(lo), b = ntt3_load(hi);
                ntt3_store(lo, ntt3_add(a, b));
                ntt3_store(hi, ntt3_mont_mul(ntt3_sub(a, b),
                    ntt3_roots(p1.roots_f, p2.roots_f, p3.roots_f, half + j)));
            }
        }
    }
}

static void ntt3_inverse(std::vector<uint32_t> &v, const ntt_mod_plan_t &p1,
                         const ntt_mod_plan_t &p2, const ntt_mod_plan_t &p3){
    size_t n = v.size() / 3;
    for(size_t len = 2; len <= n; len <<= 1){
        size_t half = len >> 1;
        for(size_t base = 0; base < n; base += len){
            for(size_t j = 0; j < half; ++j){
                uint32_t *lo = v.data() + (base + j) * 3;
                uint32_t *hi = lo + half * 3;
                __m128i a = ntt3_load(lo);
                __m128i b = ntt3_mont_mul(ntt3_load(hi),
                    ntt3_roots(p1.roots_i, p2.roots_i, p3.roots_i, half + j));
                ntt3_store(lo, ntt3_add(a, b));
                ntt3_store(hi, ntt3_sub(a, b));
            }
        }
    }
    __m128i inv = _mm_set_epi32(0, (int)p3.inv_n, (int)p2.inv_n, (int)p1.inv_n);
    for(size_t i = 0; i < n; ++i)
        ntt3_store(v.data() + i * 3, ntt3_mont_mul(ntt3_load(v.data() + i * 3), inv));
}
#endif

precn_t mul_ntt_interleaved3_experimental(const precn_t &a, const precn_t &b){
#if !PRECN_NTT_HAVE_AVX2
    return mul_ntt(a, b);
#else
    if(a.rsiz == 0 || b.rsiz == 0) return precn_t();
    std::vector<uint32_t> da, db;
    ntt_digits(a, da);
    ntt_digits(b, db);
    size_t n = 1;
    while(n < da.size() + db.size()) n <<= 1;
    if(n > NTT_MAX_TRANSFORM) return mul_ntt(a, b);
    const ntt_mod_plan_t &p1 = ntt_get_mod_plan(n, NTT_MOD1, NTT_ROOT1);
    const ntt_mod_plan_t &p2 = ntt_get_mod_plan(n, NTT_MOD2, NTT_ROOT2);
    const ntt_mod_plan_t &p3 = ntt_get_mod_plan(n, NTT_MOD3, NTT_ROOT3);
    std::vector<uint32_t> x(n * 3), y(n * 3);
    for(size_t i = 0; i < da.size(); ++i){
        x[i * 3] = mont_in(p1.c, da[i]);
        x[i * 3 + 1] = mont_in(p2.c, da[i]);
        x[i * 3 + 2] = mont_in(p3.c, da[i]);
    }
    for(size_t i = 0; i < db.size(); ++i){
        y[i * 3] = mont_in(p1.c, db[i]);
        y[i * 3 + 1] = mont_in(p2.c, db[i]);
        y[i * 3 + 2] = mont_in(p3.c, db[i]);
    }
    ntt3_forward(x, p1, p2, p3);
    ntt3_forward(y, p1, p2, p3);
    for(size_t i = 0; i < n; ++i)
        ntt3_store(x.data() + i * 3, ntt3_mont_mul(ntt3_load(x.data() + i * 3), ntt3_load(y.data() + i * 3)));
    ntt3_inverse(x, p1, p2, p3);
    std::vector<uint32_t> r1(n), r2(n), r3(n);
    for(size_t i = 0; i < n; ++i){
        r1[i] = mont_reduce(p1.c, x[i * 3]);
        r2[i] = mont_reduce(p2.c, x[i * 3 + 1]);
        r3[i] = mont_reduce(p3.c, x[i * 3 + 2]);
    }
    return ntt_from_residues3(r1, r2, r3, 0);
#endif
}
bool mul_ntt_pair_shared_right_into(
    precn_t &ra, precn_t &rc, const precn_t &a, const precn_t &c,
    const precn_t &shared_right){
    if(a.rsiz == 0 || c.rsiz == 0 || shared_right.rsiz == 0) return false;

    struct pair_workspace_t{
        std::vector<uint32_t> da, dc, db;
        std::vector<uint32_t> a1, a2, c1, c2, b1, b2;
    };
    static thread_local pair_workspace_t workspace;
    std::vector<uint32_t> &da = workspace.da;
    std::vector<uint32_t> &dc = workspace.dc;
    std::vector<uint32_t> &db = workspace.db;
    ntt_digits(a, da);
    ntt_digits(c, dc);
    ntt_digits(shared_right, db);
    if(da.empty() || dc.empty() || db.empty()) return false;

    size_t na = 1;
    while(na < da.size() + db.size()) na <<= 1;
    size_t nc = 1;
    while(nc < dc.size() + db.size()) nc <<= 1;
    if(na != nc || na > NTT_MAX_TRANSFORM) return false;
    if(!ntt_two_mod_ok(std::min(da.size(), db.size())) ||
       !ntt_two_mod_ok(std::min(dc.size(), db.size()))) return false;

#if defined(COUNT_NTT_CALLS) && COUNT_NTT_CALLS
    ntt_record_call(na, false);
    ntt_record_call(na, false);
#endif

    const ntt_mod_plan_t &p1 =
        ntt_get_mod_plan(na, NTT_MOD1, NTT_ROOT1);
    const ntt_mod_plan_t &p2 =
        ntt_get_mod_plan(na, NTT_MOD2, NTT_ROOT2);
    std::vector<uint32_t> &a1 = workspace.a1;
    std::vector<uint32_t> &a2 = workspace.a2;
    std::vector<uint32_t> &c1 = workspace.c1;
    std::vector<uint32_t> &c2 = workspace.c2;
    std::vector<uint32_t> &b1 = workspace.b1;
    std::vector<uint32_t> &b2 = workspace.b2;

    auto load_one = [&](const std::vector<uint32_t> &digits,
                        const ntt_mod_plan_t &plan,
                        std::vector<uint32_t> &out){
        ntt_zero(out, na);
        for(size_t i = 0; i < digits.size(); ++i)
            out[i] = mont_in(plan.c, digits[i]);
    };
    load_one(da, p1, a1);
    load_one(da, p2, a2);
    load_one(dc, p1, c1);
    load_one(dc, p2, c2);
    load_one(db, p1, b1);
    load_one(db, p2, b2);

    auto forward_item = [&](size_t item){
        if(item == 0) ntt_forward(a1, p1);
        else if(item == 1) ntt_forward(a2, p2);
        else if(item == 2) ntt_forward(c1, p1);
        else if(item == 3) ntt_forward(c2, p2);
        else if(item == 4) ntt_forward(b1, p1);
        else ntt_forward(b2, p2);
    };

#if !defined(__EMSCRIPTEN__)
    if(ntt_parallel_allowed(na) && na >= ((size_t)1 << 17)){
        std::vector<std::thread> workers;
        workers.reserve(5);
        for(size_t item = 1; item < 6; ++item){
            workers.emplace_back([&, item]{
                bool old = ntt_parallel_disabled;
                ntt_parallel_disabled = true;
                forward_item(item);
                ntt_parallel_disabled = old;
            });
        }
        bool old = ntt_parallel_disabled;
        ntt_parallel_disabled = true;
        forward_item(0);
        ntt_parallel_disabled = old;
        for(size_t i = 0; i < workers.size(); ++i) workers[i].join();
    }else
#endif
    {
        for(size_t item = 0; item < 6; ++item) forward_item(item);
    }

    auto finish_item = [&](size_t item){
        if(item == 0) ntt_finish_convolution(a1, b1, p1);
        else if(item == 1) ntt_finish_convolution(a2, b2, p2);
        else if(item == 2) ntt_finish_convolution(c1, b1, p1);
        else ntt_finish_convolution(c2, b2, p2);
    };

#if !defined(__EMSCRIPTEN__)
    if(ntt_parallel_allowed(na) && na >= ((size_t)1 << 17)){
        std::thread workers[3];
        for(size_t item = 1; item < 4; ++item){
            workers[item - 1] = std::thread([&, item]{
                bool old = ntt_parallel_disabled;
                ntt_parallel_disabled = true;
                finish_item(item);
                ntt_parallel_disabled = old;
            });
        }
        bool old = ntt_parallel_disabled;
        ntt_parallel_disabled = true;
        finish_item(0);
        ntt_parallel_disabled = old;
        for(size_t i = 0; i < 3; ++i) workers[i].join();
    }else
#endif
    {
        for(size_t item = 0; item < 4; ++item) finish_item(item);
    }

    ra = ntt_from_residues2(a1, a2);
    rc = ntt_from_residues2(c1, c2);
    return true;
}
precn_t mul_ntt(const precn_t &a, const precn_t &b){
    return mul_ntt_impl(a, b, 0);
}

precn_t mul_mersenne(const precn_t &a, const precn_t &b, size_t limbs){
    if(limbs == 0 || (limbs & (limbs - 1)) || a.rsiz > limbs || b.rsiz > limbs){
        fprintf(stderr, "mul_mersenne: limbs must be a power of two and contain both operands\n");
        abort();
    }
    if(a.rsiz == 0 || b.rsiz == 0) return precn_t();

    // In R = Z/(X^n-1), an n-point NTT gives the cyclic convolution
    // directly.  Ordinary multiplication needs a 2n-point transform, so
    // this is the essential primitive for Newton iterations modulo B^n-1.
    size_t digits = limbs * 4;
    std::vector<uint32_t> da, db, r1, r2, scratch;
    ntt_digits(a, da);
    ntt_digits(b, db);
    da.resize(digits, 0);
    db.resize(digits, 0);

    const ntt_mod_plan_t &p1 = ntt_get_mod_plan(digits, NTT_MOD1, NTT_ROOT1);
    const ntt_mod_plan_t &p2 = ntt_get_mod_plan(digits, NTT_MOD2, NTT_ROOT2);
#if !defined(__EMSCRIPTEN__)
    if(ntt_parallel_allowed(digits) && digits >= ((size_t)1 << 15) && ntt_worker_count() == 2){
        std::thread first([&]{
            ntt_parallel_disabled = true;
            ntt_convolve_plan(da, db, digits, p1, r1, scratch);
        });
        std::vector<uint32_t> scratch2;
        ntt_parallel_disabled = true;
        ntt_convolve_plan(da, db, digits, p2, r2, scratch2);
        ntt_parallel_disabled = false;
        first.join();
    }else
#endif
    {
        ntt_convolve_plan(da, db, digits, p1, r1, scratch);
        ntt_convolve_plan(da, db, digits, p2, r2, scratch);
    }

    std::vector<uint32_t> out(digits);
    uint64_t carry = 0;
    for(size_t i = 0; i < digits; ++i){
        uint64_t cur = ntt_crt2(r1[i], r2[i]) + carry;
        out[i] = (uint32_t)(cur & 0xFFFFu);
        carry = cur >> 16;
    }
    // B^digits == 1 in the cyclic ring, so fold the final carry through
    // digit zero.  The carry strictly shrinks after each wrapped pass.
    for(size_t i = 0; carry; i = (i + 1) % digits){
        uint64_t cur = (uint64_t)out[i] + carry;
        out[i] = (uint32_t)(cur & 0xFFFFu);
        carry = cur >> 16;
    }

    bool all_ones = true;
    for(size_t i = 0; i < digits; ++i){
        if(out[i] != 0xFFFFu){
            all_ones = false;
            break;
        }
    }
    if(all_ones) return precn_t();

    precn_t r;
    r.asiz = limbs;
    r.a = (uint64_t*)realloc(r.a, r.asiz * sizeof(uint64_t));
    memset(r.a, 0, r.asiz * sizeof(uint64_t));
    r.rsiz = limbs;
    for(size_t i = 0; i < digits; ++i)
        r.a[i >> 2] |= (uint64_t)out[i] << ((i & 3) * 16);
    while(r.rsiz && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}

precn_t mul_fermat(const precn_t &a, const precn_t &b, size_t limbs){
    if(limbs == 0 || (limbs & (limbs - 1)) || a.rsiz > limbs || b.rsiz > limbs){
        fprintf(stderr, "mul_fermat: limbs must be a power of two and contain both operands\n");
        abort();
    }
    if(a.rsiz == 0 || b.rsiz == 0) return precn_t();

    size_t digits = limbs * 4;
    std::vector<uint32_t> da, db, r1, r2, scratch;
    ntt_digits(a, da);
    ntt_digits(b, db);
    da.resize(digits, 0);
    db.resize(digits, 0);

    const ntt_mod_plan_t &p1 = ntt_get_mod_plan(digits, NTT_MOD1, NTT_ROOT1);
    const ntt_mod_plan_t &p2 = ntt_get_mod_plan(digits, NTT_MOD2, NTT_ROOT2);
    bool square = &a == &b;
#if !defined(__EMSCRIPTEN__)
    if(ntt_parallel_allowed(digits) && digits >= ((size_t)1 << 15) && ntt_worker_count() == 2){
        std::thread first([&]{
            ntt_parallel_disabled = true;
            if(square) ntt_negacyclic_square_plan(da, digits, p1, r1);
            else ntt_negacyclic_convolve_plan(da, db, digits, p1, r1, scratch);
        });
        ntt_parallel_disabled = true;
        if(square) ntt_negacyclic_square_plan(da, digits, p2, r2);
        else{
            std::vector<uint32_t> scratch2;
            ntt_negacyclic_convolve_plan(da, db, digits, p2, r2, scratch2);
        }
        ntt_parallel_disabled = false;
        first.join();
    }else
#endif
    {
        if(square){
            ntt_negacyclic_square_plan(da, digits, p1, r1);
            ntt_negacyclic_square_plan(da, digits, p2, r2);
        }else{
            ntt_negacyclic_convolve_plan(da, db, digits, p1, r1, scratch);
            ntt_negacyclic_convolve_plan(da, db, digits, p2, r2, scratch);
        }
    }

    // CRT gives residues in [0,p1*p2).  The true negacyclic coefficients
    // are small signed integers, so map the upper half back below zero.
    const uint64_t crt_modulus = (uint64_t)NTT_MOD1 * NTT_MOD2;
    std::vector<uint32_t> out(digits);
    int64_t carry = 0;
    for(size_t i = 0; i < digits; ++i){
        uint64_t residue = ntt_crt2(r1[i], r2[i]);
        int64_t coeff = residue > crt_modulus / 2 ?
            (int64_t)(residue - crt_modulus) : (int64_t)residue;
        int64_t value = coeff + carry;
        uint32_t digit = (uint32_t)(value & 0xFFFF);
        out[i] = digit;
        carry = (value - digit) / 65536;
    }

    // The final carry is the coefficient of B^digits.  Here B^digits=-1,
    // so fold it once into digit zero.  This avoids the cyclic carry loop
    // and preserves the otherwise unrepresentable residue B^digits.
    carry = -carry;
    for(size_t i = 0; i < digits; ++i){
        int64_t value = (int64_t)out[i] + carry;
        uint32_t digit = (uint32_t)(value & 0xFFFF);
        out[i] = digit;
        carry = (value - digit) / 65536;
    }

    bool top = false;
    if(carry == 1){
        size_t i = 0;
        while(i < digits && out[i] == 0){ out[i] = 0xFFFFu; ++i; }
        if(i == digits) top = true;
        else --out[i];
    }else if(carry == -1){
        size_t i = 0;
        while(i < digits && out[i] == 0xFFFFu){ out[i] = 0; ++i; }
        if(i == digits) top = true;
        else ++out[i];
    }else if(carry != 0){
        fprintf(stderr, "mul_fermat: carry escaped normalization\n");
        abort();
    }

    precn_t r;
    r.asiz = limbs + (top ? 1 : 0);
    r.a = (uint64_t*)realloc(r.a, r.asiz * sizeof(uint64_t));
    memset(r.a, 0, r.asiz * sizeof(uint64_t));
    r.rsiz = r.asiz;
    for(size_t i = 0; i < digits; ++i)
        r.a[i >> 2] |= (uint64_t)out[i] << ((i & 3) * 16);
    if(top) r.a[limbs] = 1;
    while(r.rsiz && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}

precn_t mul_high_half_ntt(const precn_t &a, const precn_t &b, size_t limbs){
    if(limbs == 0 || (limbs & (limbs - 1)) || a.rsiz > limbs || b.rsiz > limbs){
        fprintf(stderr, "mul_high_half_ntt: invalid power-of-two size\n");
        abort();
    }
    if(a.rsiz == 0 || b.rsiz == 0) return precn_t();

    // Write P=L+S*H with S=2^(64*limbs).  The two ring products give
    // U=L+H (mod S-1) and V=L-H (mod S+1).  U has two possible lifts and
    // V has at most two signed lifts; exactly one pair produces L,H in
    // [0,S).  This is O(limbs) work after the two length-n transforms.
    precn_t c = mul_mersenne(a, b, limbs);
    precn_t f = mul_fermat(a, b, limbs);
    precn_t s = precn_t(1) << (limbs * 64);
    precn_t sm1 = s - precn_t(1);
    precn_t sp1 = s + precn_t(1);
    precn_t u[2] = {c, c + sm1};
    bool f_is_s = f == s;

    for(size_t ui = 0; ui < 2; ++ui){
        // V >= 0: V=f.  The special canonical residue S represents -1,
        // not the out-of-range positive value S.
        if(!f_is_s && (u[ui] >= f) && ((u[ui].a[0] ^ f.a[0]) & 1) == 0){
            precn_t high = (u[ui] - f) >> 1;
            precn_t low = (u[ui] + f) >> 1;
            if(low < s && high < s) return high;
        }
        // V < 0: V=f-(S+1), so its magnitude is S+1-f.
        if(f.rsiz){
            precn_t magnitude = sp1 - f;
            if(u[ui] >= magnitude && ((u[ui].a[0] ^ magnitude.a[0]) & 1) == 0){
                precn_t high = (u[ui] + magnitude) >> 1;
                precn_t low = (u[ui] - magnitude) >> 1;
                if(low < s && high < s) return high;
            }
        }
    }

    fprintf(stderr, "mul_high_half_ntt: CRT lift failed\n");
    abort();
}

precn_t mul_high(const precn_t &a, const precn_t &b, size_t drop_limbs){
    if(a.rsiz == 0 || b.rsiz == 0 || drop_limbs >= a.rsiz + b.rsiz)
        return precn_t();
#if defined(COUNT_NTT_HIGH_SHAPES) && COUNT_NTT_HIGH_SHAPES
    fprintf(stderr, "mul_high a=%zu b=%zu drop=%zu\n", a.rsiz, b.rsiz, drop_limbs);
#endif
    // Let x = x0 + B^cut*x1, where B is one 64-bit limb. If
    // cut + y.rsiz == drop_limbs, then x0*y is strictly below B^drop,
    // so it cannot affect floor(x*y / B^drop). This removes the low
    // prefix before the NTT and is especially important for Newton division.
    const precn_t *x = &a;
    const precn_t *y = &b;
    if(x->rsiz < y->rsiz) std::swap(x, y);
    if(drop_limbs > y->rsiz){
        size_t cut_x = drop_limbs - y->rsiz;

        // When the discarded range extends past both operands, both low
        // prefixes can add together and carry across the requested boundary.
        // Keeping one guard limb on each side bounds their sum below that
        // boundary, while still reducing both transform operands sharply.
        if(drop_limbs > x->rsiz){
            size_t cut_y = drop_limbs - x->rsiz;
            size_t result_limbs = y->rsiz - cut_y;
            --cut_x;
            --cut_y;
            precn_t high_x = *x >> (cut_x * 64);
            precn_t high_y = *y >> (cut_y * 64);
            return mul_ntt_impl(high_x, high_y, (result_limbs + 2) * 4);
        }
        precn_t high_x = *x >> (cut_x * 64);
        return mul_ntt_impl(high_x, *y, y->rsiz * 4);
    }
    return mul_ntt_impl(a, b, drop_limbs * 4);
}
