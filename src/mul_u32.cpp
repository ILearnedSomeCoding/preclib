#include"../prec.hpp"

precn_t mul_u32(const precn_t &a, uint32_t b){
    if(a.rsiz == 0 || b == 0) return precn_t();
    precn_t r;
    r.asiz = a.rsiz + 1;
    r.a = (uint32_t*) realloc(r.a, r.asiz * 4);
    r.rsiz = a.rsiz;
    uint64_t carry = 0;
    for(size_t i = 0;i < a.rsiz;++i){
        uint64_t prod = (uint64_t)a.a[i] * b + carry;
        r.a[i] = (uint32_t)(prod & 0xFFFFFFFFu);
        carry = prod >> 32;
    }
    if(carry) r.a[r.rsiz++] = (uint32_t)carry;
    while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}
