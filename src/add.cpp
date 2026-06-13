#include"../prec.hpp"

precn_t operator+(const precn_t &a, const precn_t &b){
    precn_t r;
    size_t n = std::max(a.rsiz, b.rsiz);
    r.asiz = n + 1;
    r.a = (uint32_t*) realloc(r.a, r.asiz * 4);
    r.rsiz = 0;

    uint64_t carry = 0;
    for(size_t i = 0;i < n;++i){
        uint64_t av = i < a.rsiz ? a.a[i] : 0;
        uint64_t bv = i < b.rsiz ? b.a[i] : 0;
        uint64_t sum = av + bv + carry;
        r.a[r.rsiz++] = (uint32_t)(sum & 0xFFFFFFFFu);
        carry = sum >> 32;
    }

    if(carry) r.a[r.rsiz++] = (uint32_t)carry;
    while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}
