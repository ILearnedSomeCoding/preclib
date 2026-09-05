#include"../prec.hpp"

static int precn_cmp_abs(const precn_t &a, const precn_t &b){
    if(a.rsiz != b.rsiz) return a.rsiz < b.rsiz ? -1 : 1;
    for(size_t i = a.rsiz; i > 0; --i){
        uint64_t av = a.a[i - 1];
        uint64_t bv = b.a[i - 1];
        if(av != bv) return av < bv ? -1 : 1;
    }
    return 0;
}

precn_t operator-(const precn_t &a, const precn_t &b){
    if(precn_cmp_abs(a, b) < 0) return precn_t();

    precn_t r = precn_t::with_capacity(a.rsiz);
    r.rsiz = a.rsiz;

    uint64_t borrow = 0;
    size_t i = 0;
    for(; i < b.rsiz; ++i){
        borrow = precn_sub_borrow(a.a[i], b.a[i], borrow, r.a[i]);
    }
    for(; i < a.rsiz && borrow; ++i){
        borrow = precn_sub_borrow(a.a[i], 0, borrow, r.a[i]);
    }
    if(i < a.rsiz) memcpy(r.a + i, a.a + i,
                          (a.rsiz - i) * sizeof(uint64_t));

    while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}
