#include"../prec.hpp"

#include<cassert>
#include<cstdio>

#if !defined(PRECN_FORCE_NO_SIMD) || !PRECN_FORCE_NO_SIMD
#error Build test_no_simd.cpp with -DPRECN_FORCE_NO_SIMD=1
#endif

#if !defined(COUNT_FFTS) || !COUNT_FFTS
#error Build test_no_simd.cpp with -DCOUNT_FFTS=1
#endif

static precn_t pattern(size_t n, uint64_t seed){
    precn_t r;
    r.asiz = n ? n : 1;
    r.a = (uint64_t*) realloc(r.a, r.asiz * sizeof(uint64_t));
    r.rsiz = n;
    uint64_t x = seed;
    for(size_t i = 0; i < n; ++i){
        x = x * 6364136223846793005ULL + 1442695040888963407ULL;
        r.a[i] = x | 1;
    }
    return r;
}

static void expect_same(const precn_t &a, const precn_t &b){
    assert(a.rsiz == b.rsiz);
    for(size_t i = 0; i < a.rsiz; ++i) assert(a.a[i] == b.a[i]);
}

int main(){
    precn_t a = pattern(16384, 3001);
    precn_t b = pattern(16384, 4001);
    uint64_t before = total_fftmuls;
    precn_t dispatched = a * b;
    assert(total_fftmuls == before + 1);
    expect_same(dispatched, mul_ntt(a, b));

    precn_t vst_a = pattern(257, 5001);
    precn_t vst_b = pattern(263, 6001);
    expect_same(mul_vst(vst_a, vst_b), mul_ntt(vst_a, vst_b));

    puts("no-simd dispatch ok");
    return 0;
}
