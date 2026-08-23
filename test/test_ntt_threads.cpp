#include"../prec.hpp"

#include<cassert>
#include<cstdio>

static precn_t pattern(size_t n, uint64_t seed){
    precn_t r;
    r.asiz = n ? n : 1;
    r.a = (uint64_t*)realloc(r.a, r.asiz * sizeof(uint64_t));
    r.rsiz = n;
    for(size_t i = 0; i < n; ++i){
        seed = seed * 6364136223846793005ULL + 1442695040888963407ULL;
        r.a[i] = seed | 1;
    }
    return r;
}

static void same(const precn_t &a, const precn_t &b){
    assert(a.rsiz == b.rsiz);
    for(size_t i = 0; i < a.rsiz; ++i) assert(a.a[i] == b.a[i]);
}

int main(){
    precn_set_ntt_threads(2);
    const size_t sizes[] = {8192, 16384, 32768};
    for(size_t i = 0; i < sizeof(sizes) / sizeof(sizes[0]); ++i){
        precn_t a = pattern(sizes[i], 100 + i);
        precn_t b = pattern(sizes[i] - 17, 200 + i);
        precn_t full = mul_fft(a, b);
        same(mul_ntt(a, b), full);
        same(precn_sqr(a), mul_fft(a, a));
        same(mul_high(a, b, 0), full);
        same(mul_high(a, b, 1), full >> 64);
        same(mul_high(a, b, sizes[i] / 2), full >> (sizes[i] / 2 * 64));
    }
    puts("threaded ntt ok");
    return 0;
}
