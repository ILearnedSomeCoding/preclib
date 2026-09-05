#include"../prec.hpp"

#include<chrono>
#include<cstdio>

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

template<class F>
static double timed(F f){
    auto begin = std::chrono::steady_clock::now();
    f();
    return std::chrono::duration<double>(
        std::chrono::steady_clock::now() - begin).count();
}

int main(){
    const size_t sizes[] = {512, 1024, 2048, 4096, 8192, 16384};
    puts("divisor ratio blocked_dc   mulinv       winner");
    for(size_t n : sizes){
        for(size_t ratio = 2; ratio <= 3; ++ratio){
            precn_t d = pattern(n, n + ratio);
            precn_t want = pattern(n * ratio, n * 7 + ratio);
            precn_t a = d * want + (d - 1);
            precn_t qb, rb, qm;
            double tb = timed([&]{
                if(!div_dc_blocked_into(qb, rb, a, d)) std::abort();
            });
            double tm = timed([&]{ qm = div_mulinv(a, d); });
            if(qb != want || qm != want || rb != d - 1) std::abort();
            printf("%-7zu %zu     %.9f  %.9f  %s\n", n, ratio, tb, tm,
                   tb <= tm ? "blocked" : "mulinv");
        }
    }
    return 0;
}
