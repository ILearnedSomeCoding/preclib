#include"../prec.hpp"

#define MUL_DISPATCH_KARATSUBA_THRESHOLD 48
#define MUL_DISPATCH_FFT_THRESHOLD 384
#define MUL_DISPATCH_NTT_THRESHOLD 6144
#define MUL_DISPATCH_TOOM_UNBALANCED_MIN 768
#define MUL_DISPATCH_TOOM_UNBALANCED_MAX 1280

static precn_t mul_schoolbook(const precn_t &a, const precn_t &b){
    if(a.rsiz == 0 || b.rsiz == 0) return precn_t();

    precn_t r;
    r.asiz = a.rsiz + b.rsiz + 1;
    r.a = (uint32_t*) realloc(r.a, r.asiz * 4);
    memset(r.a, 0, r.asiz * 4);
    r.rsiz = a.rsiz + b.rsiz;

    for(size_t i = 0; i < a.rsiz; ++i){
        uint64_t carry = 0;
        for(size_t j = 0; j < b.rsiz; ++j){
            size_t k = i + j;
            uint64_t prod = (uint64_t)a.a[i] * b.a[j] + r.a[k] + carry;
            r.a[k] = (uint32_t)(prod & 0xFFFFFFFFu);
            carry = prod >> 32;
        }

        size_t k = i + b.rsiz;
        while(carry){
            uint64_t sum = (uint64_t)r.a[k] + carry;
            r.a[k] = (uint32_t)(sum & 0xFFFFFFFFu);
            carry = sum >> 32;
            ++k;
        }
    }

    while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}

precn_t operator*(const precn_t &a, const precn_t &b){
    if(a.rsiz == 0 || b.rsiz == 0) return precn_t();

    size_t lo = std::min(a.rsiz, b.rsiz);
    size_t hi = std::max(a.rsiz, b.rsiz);
    if(hi > MUL_DISPATCH_NTT_THRESHOLD) return mul_ntt(a, b);
    if(hi >= MUL_DISPATCH_TOOM_UNBALANCED_MIN && hi < MUL_DISPATCH_TOOM_UNBALANCED_MAX && hi * 5 > lo * 6){
        return mul_toom(a, b);
    }
    if(hi > MUL_DISPATCH_FFT_THRESHOLD) return mul_fft(a, b);
    if(hi > MUL_DISPATCH_KARATSUBA_THRESHOLD) return mul_karatsuba(a, b);
    return mul_schoolbook(a, b);
}

precn_t mul_basic(const precn_t &a, const precn_t &b){
    return mul_schoolbook(a, b);
}
