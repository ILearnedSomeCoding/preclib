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
    const size_t sizes[] = {3, 5, 9, 15, 31};
    for(size_t i = 0; i < sizeof(sizes) / sizeof(sizes[0]); ++i){
        precn_t a = pattern(sizes[i], 100 + i);
        precn_t b = pattern(sizes[i] - 1, 200 + i);
        same(mul_ssa(a, b), mul_basic(a, b));
    }
    puts("ssa ok");
    return 0;
}
