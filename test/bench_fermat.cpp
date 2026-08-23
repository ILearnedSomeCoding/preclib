#include"../prec.hpp"

#include<chrono>
#include<cstdio>

static precn_t pattern(size_t n, uint64_t seed){
    precn_t r;
    r.asiz = n;
    r.a = (uint64_t*)realloc(r.a, n * sizeof(uint64_t));
    r.rsiz = n;
    for(size_t i = 0; i < n; ++i){
        seed = seed * 6364136223846793005ULL + 1442695040888963407ULL;
        r.a[i] = seed | 1;
    }
    return r;
}

int main(){
    precn_set_ntt_threads(2);
    const size_t sizes[] = {4096, 8192, 16384, 32768};
    puts("limbs     full ntt      high-half     cyclic        negacyclic");
    for(size_t i = 0; i < sizeof(sizes) / sizeof(sizes[0]); ++i){
        size_t n = sizes[i];
        precn_t a = pattern(n, 100 + i);
        precn_t b = pattern(n, 200 + i);
        std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
        precn_t full = mul_ntt(a, b);
        double full_time = std::chrono::duration<double>(std::chrono::steady_clock::now() - begin).count();
        begin = std::chrono::steady_clock::now();
        precn_t high = mul_high_half_ntt(a, b, n);
        double high_time = std::chrono::duration<double>(std::chrono::steady_clock::now() - begin).count();
        begin = std::chrono::steady_clock::now();
        precn_t cyclic = mul_mersenne(a, b, n);
        double cyclic_time = std::chrono::duration<double>(std::chrono::steady_clock::now() - begin).count();
        begin = std::chrono::steady_clock::now();
        precn_t negacyclic = mul_fermat(a, b, n);
        double negacyclic_time = std::chrono::duration<double>(std::chrono::steady_clock::now() - begin).count();
        printf("%-9zu %.6f     %.6f     %.6f     %.6f\n", n, full_time, high_time, cyclic_time, negacyclic_time);
        (void)full;
        (void)high;
        (void)cyclic;
        (void)negacyclic;
    }
    return 0;
}
