#include"../prec.hpp"

static int precn_cmp(const precn_t &a, const precn_t &b){
    if(a.rsiz != b.rsiz) return a.rsiz < b.rsiz ? -1 : 1;
    for(size_t i = a.rsiz; i > 0; --i){
        if(a.a[i - 1] != b.a[i - 1]) return a.a[i - 1] < b.a[i - 1] ? -1 : 1;
    }
    return 0;
}

bool operator==(const precn_t &a, const precn_t &b){
    return precn_cmp(a, b) == 0;
}

bool operator!=(const precn_t &a, const precn_t &b){
    return precn_cmp(a, b) != 0;
}

bool operator<(const precn_t &a, const precn_t &b){
    return precn_cmp(a, b) < 0;
}

bool operator>(const precn_t &a, const precn_t &b){
    return precn_cmp(a, b) > 0;
}

bool operator<=(const precn_t &a, const precn_t &b){
    return precn_cmp(a, b) <= 0;
}

bool operator>=(const precn_t &a, const precn_t &b){
    return precn_cmp(a, b) >= 0;
}

precn_t operator<<(const precn_t &a, size_t b){
    if(a.rsiz == 0) return precn_t();

    size_t limbs = b / 64;
    unsigned shift = (unsigned)(b % 64);

    precn_t r = precn_t::with_capacity(a.rsiz + limbs + 1);
    if(limbs) memset(r.a, 0, limbs * sizeof(uint64_t));

    if(shift == 0){
        memcpy(r.a + limbs, a.a, a.rsiz * sizeof(uint64_t));
        r.rsiz = a.rsiz + limbs;
    }else{
        uint64_t carry = 0;
        for(size_t i = 0; i < a.rsiz; ++i){
            r.a[i + limbs] = (a.a[i] << shift) | carry;
            carry = a.a[i] >> (64 - shift);
        }
        r.rsiz = a.rsiz + limbs;
        if(carry) r.a[r.rsiz++] = carry;
    }

    return r;
}

precn_t operator>>(const precn_t &a, size_t b){
    if(a.rsiz == 0) return precn_t();

    size_t limbs = b / 64;
    unsigned shift = (unsigned)(b % 64);
    if(limbs >= a.rsiz) return precn_t();

    precn_t r = precn_t::with_capacity(a.rsiz - limbs);
    r.rsiz = r.asiz;

    if(shift == 0){
        memcpy(r.a, a.a + limbs, r.rsiz * sizeof(uint64_t));
    }else{
        uint64_t carry = 0;
        for(size_t i = a.rsiz; i > limbs; --i){
            uint64_t cur = a.a[i - 1];
            r.a[i - 1 - limbs] = (cur >> shift) | carry;
            carry = cur << (64 - shift);
        }
    }

    while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}
