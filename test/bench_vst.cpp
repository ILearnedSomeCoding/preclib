#include"../prec.hpp"

#include<algorithm>
#include<chrono>
#include<cstdio>
#include<vector>

#if defined(PRECN_VST_PROFILE) && PRECN_VST_PROFILE
void precn_vst_profile_reset();
void precn_vst_profile_dump();
#endif

static precn_t pattern(size_t n, uint64_t seed){
    precn_t r;
    r.asiz = n;
    r.a = (uint64_t*)realloc(r.a, n * sizeof(uint64_t));
    r.rsiz = n;
    uint64_t x = seed;
    for(size_t i = 0; i < n; ++i){
        x = x * 6364136223846793005ULL + 1442695040888963407ULL;
        r.a[i] = x | 1;
    }
    r.a[n - 1] |= 1ULL << 63;
    return r;
}

static bool same(const precn_t &a, const precn_t &b){
    if(a.rsiz != b.rsiz) return false;
    for(size_t i = 0; i < a.rsiz; ++i)
        if(a.a[i] != b.a[i]) return false;
    return true;
}

typedef precn_t (*mul_fn_t)(const precn_t&, const precn_t&);

static precn_t square_fft(const precn_t &a, const precn_t&){
    return mul_fft(a, a);
}

static precn_t square_ntt(const precn_t &a, const precn_t&){
    return mul_ntt(a, a);
}

static precn_t square_vst(const precn_t &a, const precn_t&){
    return mul_vst(a, a);
}

static double measure(mul_fn_t fn, const precn_t &a, const precn_t &b,
                      const precn_t &reference, size_t reps){
    std::vector<double> samples;
    precn_t result;
    for(size_t trial = 0; trial < 3; ++trial){
        std::chrono::steady_clock::time_point begin =
            std::chrono::steady_clock::now();
        for(size_t i = 0; i < reps; ++i) result = fn(a, b);
        double seconds = std::chrono::duration<double>(
            std::chrono::steady_clock::now() - begin).count() / reps;
        if(!same(result, reference)) std::abort();
        samples.push_back(seconds);
    }
    std::sort(samples.begin(), samples.end());
    return samples[1];
}

int main(int argc, char **argv){
    size_t min_limbs = 256;
    size_t max_limbs = 131072;
    bool square = false;
    for(int i = 1; i < argc; ++i){
        if(strcmp(argv[i], "--serial") == 0)
            precn_set_ntt_thread_parallel(false);
        else if(strcmp(argv[i], "--square") == 0) square = true;
        else if(strcmp(argv[i], "--min") == 0 && i + 1 < argc)
            min_limbs = (size_t)strtoull(argv[++i], nullptr, 10);
        else if(strcmp(argv[i], "--max") == 0 && i + 1 < argc)
            max_limbs = (size_t)strtoull(argv[++i], nullptr, 10);
    }

    puts("floating-point modular transform timing");
    printf("%-10s %-6s %-15s %-15s %-15s %-10s %-10s\n",
           "limbs", "reps", "fft", "ntt", "vst", "vst/fft", "vst/ntt");
    for(size_t n = 256; n <= max_limbs; n <<= 1){
        if(n < min_limbs) continue;
        size_t reps = n <= 2048 ? 10 : n <= 8192 ? 5 : n <= 32768 ? 3 : 1;
        precn_t a = pattern(n, 1000 + n);
        precn_t b = square ? a : pattern(n, 2000 + n);

        // Warm plans and buffers before collecting the median.
        precn_t reference = square ? mul_fft(a, a) : mul_fft(a, b);
        precn_t integer_ntt = square ? mul_ntt(a, a) : mul_ntt(a, b);
        precn_t floating_ntt = square ? mul_vst(a, a) : mul_vst(a, b);
        if(!same(reference, integer_ntt) || !same(reference, floating_ntt)){
            fprintf(stderr, "mismatch at %zu limbs\n", n);
            return 1;
        }

        mul_fn_t fft_fn = square ? square_fft : mul_fft;
        mul_fn_t ntt_fn = square ? square_ntt : mul_ntt;
        mul_fn_t vst_fn = square ? square_vst : mul_vst;
        double fft_seconds = measure(fft_fn, a, b, reference, reps);
        double ntt_seconds = measure(ntt_fn, a, b, reference, reps);
#if defined(PRECN_VST_PROFILE) && PRECN_VST_PROFILE
        precn_vst_profile_reset();
#endif
        double vst_seconds = measure(vst_fn, a, b, reference, reps);
        printf("%-10zu %-6zu %-15.9f %-15.9f %-15.9f %-10.3f %-10.3f\n",
               n, reps, fft_seconds, ntt_seconds, vst_seconds,
               vst_seconds / fft_seconds, vst_seconds / ntt_seconds);
#if defined(PRECN_VST_PROFILE) && PRECN_VST_PROFILE
        precn_vst_profile_dump();
#endif
    }
    return 0;
}
