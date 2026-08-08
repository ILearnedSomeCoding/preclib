#include"../prec.hpp"

#include<cassert>
#include<cstdio>

#if defined(__AVX2__) || defined(_M_AVX2)
#error Build test_no_avx2.cpp without -mavx2
#endif

#if !defined(COUNT_FFTS) || !COUNT_FFTS
#error Build test_no_avx2.cpp with -DCOUNT_FFTS=1
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
    precn_t a = pattern(8192, 1001);
    precn_t b = pattern(8192, 2001);
    uint64_t before = total_fftmuls;
    precn_t fft_dispatched = a * b;
    assert(total_fftmuls == before + 1);
    expect_same(fft_dispatched, mul_ntt(a, b));

    a = pattern(16384, 1002);
    b = pattern(16384, 2002);
    before = total_fftmuls;
    precn_t ntt_dispatched = a * b;
    assert(total_fftmuls == before);
    expect_same(ntt_dispatched, mul_fft(a, b));

    puts("no-avx2 dispatch ok");
    return 0;
}
