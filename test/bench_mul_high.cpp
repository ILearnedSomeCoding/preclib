#include"../prec.hpp"

#include<chrono>
#include<cstdio>

static precn_t pattern(size_t n, uint64_t seed){
    precn_t r;
    r.asiz = n;
    r.a = (uint64_t*) realloc(r.a, n * sizeof(uint64_t));
    r.rsiz = n;
    uint64_t x = seed;
    for(size_t i = 0; i < n; ++i){
        x = x * 6364136223846793005ULL + 1442695040888963407ULL;
        r.a[i] = x | 1;
    }
    return r;
}

static double seconds_since(std::chrono::steady_clock::time_point start){
    return std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
}

int main(){
    const size_t sizes[] = {1024, 2048, 4096, 8192, 16384};
    puts("limbs      full+shift   mul_high     speedup");
    for(size_t n : sizes){
        precn_t a = pattern(n, 101 + n);
        precn_t b = pattern(n, 503 + n);
        size_t drop = n + n / 2;
        int reps = n <= 4096 ? 5 : 3;

        auto begin = std::chrono::steady_clock::now();
        precn_t full;
        for(int i = 0; i < reps; ++i) full = mul_ntt(a, b) >> (drop * 64);
        double full_time = seconds_since(begin) / reps;

        begin = std::chrono::steady_clock::now();
        precn_t high;
        for(int i = 0; i < reps; ++i) high = mul_high(a, b, drop);
        double high_time = seconds_since(begin) / reps;

        if(full != high){
            fprintf(stderr, "mismatch at %zu limbs\n", n);
            return 1;
        }
        printf("%-10zu %.9f  %.9f  %.2fx\n", n, full_time, high_time,
               full_time / high_time);
    }
    return 0;
}
