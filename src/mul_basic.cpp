#include"../prec.hpp"

#define MUL_DISPATCH_KARATSUBA_THRESHOLD 48
#define MUL_DISPATCH_FFT_THRESHOLD 384
#define MUL_DISPATCH_NTT_THRESHOLD 4194304
#define MUL_DISPATCH_TOOM_UNBALANCED_MIN 768
#define MUL_DISPATCH_TOOM_UNBALANCED_MAX 1280

static void mul_norm(precn_t &r){
    while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
}

static void mul_reserve(precn_t &r, size_t n){
    if(r.asiz >= n) return;
    r.a = (uint32_t*) realloc(r.a, n * 4);
    r.asiz = n;
}

static void mul_zero(precn_t &r){
    r.rsiz = 0;
    if(r.asiz == 0){
        r.asiz = 1;
        r.a = (uint32_t*) malloc(4);
    }
    r.a[0] = 0;
}

static void mul_limb_into(precn_t &r, const precn_t &a, uint32_t b){
    if(a.rsiz == 0 || b == 0){
        mul_zero(r);
        return;
    }

    mul_reserve(r, a.rsiz + 1);
    r.rsiz = a.rsiz;

    uint64_t carry = 0;
    for(size_t i = 0; i < a.rsiz; ++i){
        uint64_t p = (uint64_t)a.a[i] * b + carry;
        r.a[i] = (uint32_t)p;
        carry = p >> 32;
    }
    if(carry) r.a[r.rsiz++] = (uint32_t)carry;
    mul_norm(r);
}

static void mul_schoolbook_into(precn_t &r, const precn_t &a, const precn_t &b){
    if(&r == &a || &r == &b){
        precn_t t;
        mul_schoolbook_into(t, a, b);
        r = t;
        return;
    }

    if(a.rsiz == 0 || b.rsiz == 0){
        mul_zero(r);
        return;
    }

    if(a.rsiz == 1){
        mul_limb_into(r, b, a.a[0]);
        return;
    }
    if(b.rsiz == 1){
        mul_limb_into(r, a, b.a[0]);
        return;
    }

    const precn_t *x = &a;
    const precn_t *y = &b;
    if(y->rsiz > x->rsiz) std::swap(x, y);

    mul_reserve(r, x->rsiz + y->rsiz + 1);
    memset(r.a, 0, (x->rsiz + y->rsiz + 1) * 4);
    r.rsiz = x->rsiz + y->rsiz;

    for(size_t i = 0; i < x->rsiz; ++i){
        uint64_t carry = 0;
        uint64_t av = x->a[i];
        for(size_t j = 0; j < y->rsiz; ++j){
            size_t k = i + j;
            uint64_t prod = av * y->a[j] + r.a[k] + carry;
            r.a[k] = (uint32_t)prod;
            carry = prod >> 32;
        }

        size_t k = i + y->rsiz;
        while(carry){
            uint64_t sum = (uint64_t)r.a[k] + carry;
            r.a[k] = (uint32_t)sum;
            carry = sum >> 32;
            ++k;
        }
    }

    mul_norm(r);
}

static precn_t mul_schoolbook(const precn_t &a, const precn_t &b){
    precn_t r;
    mul_schoolbook_into(r, a, b);
    return r;
}

void mul_into(precn_t &r, const precn_t &a, const precn_t &b){
    if(a.rsiz == 0 || b.rsiz == 0){
        mul_zero(r);
        return;
    }

    size_t lo = std::min(a.rsiz, b.rsiz);
    size_t hi = std::max(a.rsiz, b.rsiz);
    if(hi > MUL_DISPATCH_NTT_THRESHOLD){
        r = mul_ntt(a, b);
        return;
    }
    if(hi >= MUL_DISPATCH_TOOM_UNBALANCED_MIN && hi < MUL_DISPATCH_TOOM_UNBALANCED_MAX && hi * 5 > lo * 6){
        r = mul_toom(a, b);
        return;
    }
    if(hi > MUL_DISPATCH_FFT_THRESHOLD){
        r = mul_fft(a, b);
        return;
    }
    if(hi > MUL_DISPATCH_KARATSUBA_THRESHOLD){
        r = mul_karatsuba(a, b);
        return;
    }
    mul_schoolbook_into(r, a, b);
}

precn_t operator*(const precn_t &a, const precn_t &b){
    if(a.rsiz == 0 || b.rsiz == 0) return precn_t();

    precn_t r;
    mul_into(r, a, b);
    return r;
}

precn_t mul_basic(const precn_t &a, const precn_t &b){
    return mul_schoolbook(a, b);
}
