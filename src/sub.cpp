#include"../prec.hpp"

static int precn_cmp_abs(const precn_t &a, const precn_t &b){
    if(a.rsiz != b.rsiz) return a.rsiz < b.rsiz ? -1 : 1;
    for(size_t i = a.rsiz; i > 0; --i){
        uint32_t av = a.a[i - 1];
        uint32_t bv = b.a[i - 1];
        if(av != bv) return av < bv ? -1 : 1;
    }
    return 0;
}

precn_t operator-(const precn_t &a, const precn_t &b){
    if(precn_cmp_abs(a, b) < 0) return precn_t();

    precn_t r;
    r.asiz = std::max<size_t>(a.rsiz, 1);
    r.a = (uint32_t*) realloc(r.a, r.asiz * 4);
    r.rsiz = a.rsiz;

    uint64_t borrow = 0;
    for(size_t i = 0; i < a.rsiz; ++i){
        uint64_t av = a.a[i];
        uint64_t bv = i < b.rsiz ? b.a[i] : 0;
        uint64_t sub = bv + borrow;

        if(av < sub){
            r.a[i] = (uint32_t)((1ULL << 32) + av - sub);
            borrow = 1;
        }else{
            r.a[i] = (uint32_t)(av - sub);
            borrow = 0;
        }
    }

    while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}
