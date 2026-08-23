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
    if(a.rsiz != b.rsiz){
        fprintf(stderr, "size mismatch %zu != %zu\n", a.rsiz, b.rsiz);
        assert(false);
    }
    for(size_t i = 0; i < a.rsiz; ++i){
        if(a.a[i] != b.a[i]){
            fprintf(stderr, "limb %zu: %llx != %llx\n", i,
                    (unsigned long long)a.a[i], (unsigned long long)b.a[i]);
            assert(false);
        }
    }
}

int main(){
    precn_set_ntt_threads(2);
    const size_t cyclic_sizes[] = {1, 2, 4, 8, 16};
    for(size_t i = 0; i < sizeof(cyclic_sizes) / sizeof(cyclic_sizes[0]); ++i){
        size_t n = cyclic_sizes[i];
        precn_t a = pattern(n, 700 + i);
        precn_t b = pattern(n, 800 + i);
        precn_t modulus = (precn_t(1) << (n * 64)) - precn_t(1);
        same(mul_mersenne(a, b, n), (a * b) % modulus);
        same(mul_mersenne(modulus, a, n), precn_t());

        precn_t fermat = (precn_t(1) << (n * 64)) + precn_t(1);
        same(mul_fermat(a, b, n), (a * b) % fermat);
        same(mul_high_half_ntt(a, b, n), (a * b) >> (n * 64));

        precn_t all_ones = (precn_t(1) << (n * 64)) - precn_t(1);
        same(mul_fermat(all_ones, all_ones, n), precn_t(4));
    }
    for(size_t n = 1; n <= 16; n <<= 1){
        for(size_t seed = 0; seed < 32; ++seed){
            precn_t a = pattern(n, 1000 + n * 97 + seed);
            precn_t b = pattern(n, 2000 + n * 131 + seed * 3);
            same(mul_high_half_ntt(a, b, n), (a * b) >> (n * 64));
        }
    }
    const size_t sizes[] = {8192, 16384, 32768};
    for(size_t i = 0; i < sizeof(sizes) / sizeof(sizes[0]); ++i){
        precn_t a = pattern(sizes[i], 100 + i);
        precn_t b = pattern(sizes[i] - 17, 200 + i);
        precn_t full = mul_fft(a, b);
        if(i == 0){
            precn_t modulus = (precn_t(1) << (sizes[i] * 64)) - precn_t(1);
            same(mul_mersenne(a, b, sizes[i]), full % modulus);
            precn_t fermat = (precn_t(1) << (sizes[i] * 64)) + precn_t(1);
            same(mul_fermat(a, b, sizes[i]), full % fermat);
            same(mul_high_half_ntt(a, b, sizes[i]), full >> (sizes[i] * 64));
        }
        same(mul_ntt(a, b), full);
        same(precn_sqr(a), mul_fft(a, a));
        same(mul_high(a, b, 0), full);
        same(mul_high(a, b, 1), full >> 64);
        same(mul_high(a, b, sizes[i] / 2), full >> (sizes[i] / 2 * 64));
    }
    puts("threaded ntt ok");
    return 0;
}
