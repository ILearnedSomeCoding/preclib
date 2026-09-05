#include"../prec.hpp"

#include<algorithm>
#include<chrono>
#include<cstdio>
#include<vector>

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

typedef precn_t (*mul_fn)(const precn_t&, const precn_t&);

static precn_t mul_dispatch(const precn_t &a, const precn_t &b){
    return a * b;
}

static double measure(mul_fn fn, const precn_t &a, const precn_t &b,
                      const precn_t &want, size_t reps){
    std::vector<double> samples;
    precn_t out;
    for(size_t trial = 0; trial < 5; ++trial){
        auto begin = std::chrono::steady_clock::now();
        for(size_t i = 0; i < reps; ++i) out = fn(a, b);
        double elapsed = std::chrono::duration<double>(
            std::chrono::steady_clock::now() - begin).count() / reps;
        if(out != want) std::abort();
        samples.push_back(elapsed);
    }
    std::sort(samples.begin(), samples.end());
    return samples[samples.size() / 2];
}

int main(){
    const size_t shapes[][2] = {
        {24, 24}, {32, 32}, {33, 33}, {36, 36}, {40, 40},
        {44, 44}, {48, 48}, {56, 56},
        {64, 64}, {80, 64}, {80, 80}, {96, 64}, {96, 96},
        {112, 112}, {128, 64}, {128, 96}, {128, 128},
        {160, 128}, {160, 160}, {192, 128}, {192, 192},
        {224, 128}, {224, 224}, {256, 128}, {256, 192}, {256, 256},
        {320, 256}, {320, 320}, {384, 256}, {384, 384},
        {512, 256}, {512, 384}, {512, 512},
        {768, 768}, {960, 768}, {1152, 768}, {1536, 768}, {1024, 1024},
        {1280, 1024}, {1536, 1024}, {2048, 1024},
        {2560, 2560}, {3072, 1536}, {3072, 3072}, {4096, 4096}
    };
    struct algorithm { const char *name; mul_fn fn; };
    const algorithm algorithms[] = {
        {"dispatch", mul_dispatch}, {"basic", mul_basic},
        {"kara", mul_karatsuba}, {"toom", mul_toom},
        {"fft", mul_fft}, {"ntt", mul_ntt}
    };

    puts("a      b      reps  dispatch     basic        kara         toom         fft          ntt          fastest");
    for(const auto &shape : shapes){
        size_t na = shape[0], nb = shape[1];
        size_t reps = na <= 256 ? 100 : 10;
        precn_t a = pattern(na, na * 17 + nb);
        precn_t b = pattern(nb, na + nb * 29);
        precn_t want = mul_basic(a, b);
        double times[sizeof(algorithms) / sizeof(algorithms[0])];
        size_t best = 0;
        for(size_t i = 0; i < sizeof(algorithms) / sizeof(algorithms[0]); ++i){
            times[i] = measure(algorithms[i].fn, a, b, want, reps);
            if(times[i] < times[best]) best = i;
        }
        printf("%-6zu %-6zu %-5zu", na, nb, reps);
        for(double t : times) printf(" %-12.9f", t);
        printf(" %s\n", algorithms[best].name);
    }
    return 0;
}
