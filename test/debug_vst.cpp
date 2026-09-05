#include"../prec.hpp"

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
    r.a[n - 1] |= (uint64_t)1 << 63;
    return r;
}

int main(){
    for(size_t n = 1; n <= 1024; ++n){
        printf("n=%zu\n", n);
        fflush(stdout);
        precn_t a = pattern(n, 1000 + n);
        precn_t b = pattern(n - n / 7, 2000 + n);
        precn_t got = mul_vst(a, b);
        precn_t expected = mul_basic(a, b);
        if(got != expected){
            printf("mismatch %zu %zu\n", got.rsiz, expected.rsiz);
            return 1;
        }
    }
    return 0;
}
