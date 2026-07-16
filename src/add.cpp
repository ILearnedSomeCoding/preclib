#include"../prec.hpp"

precn_t add_u64(const precn_t &a, uint64_t b){
    if(a.rsiz == 0) return precn_t(b);
    if(b == 0) return a;

    precn_t r;
    r.asiz = a.rsiz + 1;
    r.a = (uint64_t*) realloc(r.a, r.asiz * sizeof(uint64_t));
    memcpy(r.a, a.a, a.rsiz * sizeof(uint64_t));
    r.rsiz = a.rsiz;

    uint64_t out;
    uint64_t carry = precn_add_carry(r.a[0], b, 0, out);
    r.a[0] = out;
    for(size_t i = 1; i < r.rsiz && carry; ++i){
        carry = precn_add_carry(r.a[i], 0, carry, out);
        r.a[i] = out;
    }
    if(carry) r.a[r.rsiz++] = carry;
    return r;
}

precn_t operator+(const precn_t &a, const precn_t &b){
    precn_t r;
    size_t n = std::max(a.rsiz, b.rsiz);
    r.asiz = n + 1;
    r.a = (uint64_t*) realloc(r.a, r.asiz * sizeof(uint64_t));
    r.rsiz = 0;

    uint64_t carry = 0;
    for(size_t i = 0;i < n;++i){
        uint64_t av = i < a.rsiz ? a.a[i] : 0;
        uint64_t bv = i < b.rsiz ? b.a[i] : 0;
        uint64_t sum;
        carry = precn_add_carry(av, bv, carry, sum);
        r.a[r.rsiz++] = sum;
    }

    if(carry) r.a[r.rsiz++] = carry;
    while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}
