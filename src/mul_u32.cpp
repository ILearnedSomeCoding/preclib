#include"../prec.hpp"

precn_t mul_u32(const precn_t &a, uint32_t b){
    return mul_u64(a, b);
}

precn_t mul_u64(const precn_t &a, uint64_t b){
    if(a.rsiz == 0 || b == 0) return precn_t();
    precn_t r;
    r.asiz = a.rsiz + 1;
    r.a = (uint64_t*) realloc(r.a, r.asiz * sizeof(uint64_t));
    r.rsiz = a.rsiz;
    uint64_t carry = 0;
    for(size_t i = 0;i < a.rsiz;++i){
        uint64_t hi, lo;
        precn_mul_wide(a.a[i], b, hi, lo);
        uint64_t out;
        uint64_t c = precn_add_carry(lo, carry, 0, out);
        r.a[i] = out;
        carry = hi + c;
    }
    if(carry) r.a[r.rsiz++] = carry;
    while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}
