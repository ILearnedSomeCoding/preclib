#include"../prec.hpp"

precn_t add_u64(const precn_t &a, uint64_t b){
    if(a.rsiz == 0) return precn_t(b);
    if(b == 0) return a;

    precn_t r = precn_t::with_capacity(a.rsiz + 1);
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
    size_t n = std::max(a.rsiz, b.rsiz);
    size_t common = std::min(a.rsiz, b.rsiz);
    const precn_t &longer = a.rsiz >= b.rsiz ? a : b;
    precn_t r = precn_t::with_capacity(n + 1);
    r.rsiz = n;

    uint64_t carry = 0;
    size_t i = 0;
    for(; i < common; ++i){
        uint64_t sum;
        carry = precn_add_carry(a.a[i], b.a[i], carry, sum);
        r.a[i] = sum;
    }
    for(; i < n && carry; ++i){
        carry = precn_add_carry(longer.a[i], 0, carry, r.a[i]);
    }
    if(i < n) memcpy(r.a + i, longer.a + i,
                     (n - i) * sizeof(uint64_t));

    if(carry) r.a[r.rsiz++] = carry;
    return r;
}
