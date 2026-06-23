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

    size_t limbs = b / 32;
    unsigned shift = (unsigned)(b % 32);

    precn_t r;
    r.asiz = a.rsiz + limbs + 1;
    r.a = (uint32_t*) realloc(r.a, r.asiz * 4);
    memset(r.a, 0, r.asiz * 4);

    if(shift == 0){
        for(size_t i = 0; i < a.rsiz; ++i) r.a[i + limbs] = a.a[i];
        r.rsiz = a.rsiz + limbs;
    }else{
        uint32_t carry = 0;
        for(size_t i = 0; i < a.rsiz; ++i){
            uint64_t cur = ((uint64_t)a.a[i] << shift) | carry;
            r.a[i + limbs] = (uint32_t)cur;
            carry = (uint32_t)(cur >> 32);
        }
        r.rsiz = a.rsiz + limbs;
        if(carry) r.a[r.rsiz++] = carry;
    }

    while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}

precn_t operator>>(const precn_t &a, size_t b){
    if(a.rsiz == 0) return precn_t();

    size_t limbs = b / 32;
    unsigned shift = (unsigned)(b % 32);
    if(limbs >= a.rsiz) return precn_t();

    precn_t r;
    r.asiz = a.rsiz - limbs;
    r.a = (uint32_t*) realloc(r.a, r.asiz * 4);
    r.rsiz = r.asiz;

    if(shift == 0){
        for(size_t i = limbs; i < a.rsiz; ++i) r.a[i - limbs] = a.a[i];
    }else{
        uint32_t carry = 0;
        for(size_t i = a.rsiz; i > limbs; --i){
            uint32_t cur = a.a[i - 1];
            r.a[i - 1 - limbs] = (cur >> shift) | carry;
            carry = cur << (32 - shift);
        }
    }

    while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}
