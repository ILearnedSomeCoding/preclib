#include"../prec.hpp"

precn_t mul_u32(const precn_t &a, uint32_t b){
    return mul_u64(a, b);
}

precn_t mul_u64(const precn_t &a, uint64_t b){
    if(a.rsiz == 0 || b == 0) return precn_t();
    if(b == 1) return a;
    if((b & (b - 1)) == 0){
#if defined(__clang__) || defined(__GNUC__)
        return a << (unsigned)__builtin_ctzll(b);
#else
        unsigned shift = 0;
        while((b >> shift) != 1) ++shift;
        return a << shift;
#endif
    }

    precn_t r = precn_t::with_capacity(a.rsiz + 1);
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
    return r;
}
