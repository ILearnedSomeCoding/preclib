#include"../prec.hpp"

#include<algorithm>
#include<chrono>
#include<cstdio>
#include<vector>

static volatile uint64_t sink;

static precn_t pattern(size_t n, uint64_t seed){
    precn_t r = precn_t::with_capacity(n);
    r.rsiz = n;
    for(size_t i = 0; i < n; ++i){
        seed = seed * 6364136223846793005ULL + 1442695040888963407ULL;
        r.a[i] = seed;
    }
    r.a[n - 1] |= 1ULL << 63;
    return r;
}

static double measure(const precn_t &a, uint64_t divisor, size_t reps){
    std::vector<double> samples;
    for(size_t trial = 0; trial < 5; ++trial){
        auto begin = std::chrono::steady_clock::now();
        for(size_t i = 0; i < reps; ++i){
            precn_t q = div_u64(a, divisor + (i & 1) * 2);
            sink ^= q.rsiz ? q.a[0] : 0;
        }
        samples.push_back(std::chrono::duration<double>(
            std::chrono::steady_clock::now() - begin).count() / reps);
    }
    std::sort(samples.begin(), samples.end());
    return samples[2];
}

int main(int argc, char **argv){
    uint64_t divisor = argc > 1 ? strtoull(argv[1], nullptr, 0)
                                : 0xd6e8feb86659fd93ULL;
    puts("limbs    reps       div_u64 seconds");
    for(size_t n = 1; n <= 256; n <<= 1){
        size_t reps = n <= 8 ? 100000 : n <= 64 ? 20000 : 5000;
        precn_t a = pattern(n, 1000 + n);
        printf("%-8zu %-10zu %.9f\n", n, reps,
               measure(a, divisor, reps));
    }
    return sink == UINT64_MAX;
}
