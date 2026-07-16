#include"../prec.hpp"

#define MUL_DISPATCH_KARATSUBA_THRESHOLD 24
#define MUL_DISPATCH_FFT_THRESHOLD 192
#define MUL_DISPATCH_NTT_THRESHOLD 4194304
#define MUL_DISPATCH_TOOM_UNBALANCED_MIN 768
#define MUL_DISPATCH_TOOM_UNBALANCED_MAX 1280

static void mul_norm(precn_t &r){
    while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
}

static void mul_reserve(precn_t &r, size_t n){
    if(r.asiz >= n) return;
    r.a = (uint64_t*) realloc(r.a, n * sizeof(uint64_t));
    r.asiz = n;
}

static void mul_zero(precn_t &r){
    r.rsiz = 0;
    if(r.asiz == 0){
        r.asiz = 1;
        r.a = (uint64_t*) malloc(sizeof(uint64_t));
    }
    r.a[0] = 0;
}

static void mul_limb_into(precn_t &r, const precn_t &a, uint64_t b){
    if(a.rsiz == 0 || b == 0){
        mul_zero(r);
        return;
    }

    mul_reserve(r, a.rsiz + 1);
    r.rsiz = a.rsiz;

    uint64_t carry = 0;
    for(size_t i = 0; i < a.rsiz; ++i){
        uint64_t hi, lo;
        precn_mul_wide(a.a[i], b, hi, lo);
        uint64_t out;
        uint64_t c = precn_add_carry(lo, carry, 0, out);
        r.a[i] = out;
        carry = hi + c;
    }
    if(carry) r.a[r.rsiz++] = carry;
    mul_norm(r);
}

static void mul_add_shift(precn_t &r, const precn_t &a, size_t shift){
    if(a.rsiz == 0) return;

    size_t need = shift + a.rsiz + 1;
    mul_reserve(r, need);
    if(r.rsiz < need){
        memset(r.a + r.rsiz, 0, (need - r.rsiz) * sizeof(uint64_t));
        r.rsiz = need;
    }

    uint64_t carry = 0;
    size_t i = 0;
    for(; i < a.rsiz; ++i){
        uint64_t out;
        carry = precn_add_carry(r.a[shift + i], a.a[i], carry, out);
        r.a[shift + i] = out;
    }
    while(carry){
        uint64_t out;
        carry = precn_add_carry(r.a[shift + i], 0, carry, out);
        r.a[shift + i] = out;
        ++i;
    }
}

static void mul_square_schoolbook_into(precn_t &r, const precn_t &a){
    if(&r == &a){
        precn_t t;
        mul_square_schoolbook_into(t, a);
        r = t;
        return;
    }
    if(a.rsiz == 0){
        mul_zero(r);
        return;
    }

    size_t n = a.rsiz;
    mul_reserve(r, n * 2 + 2);
    memset(r.a, 0, (n * 2 + 2) * sizeof(uint64_t));
    r.rsiz = n * 2 + 1;

    for(size_t i = 0; i < n; ++i){
        uint64_t hi, lo;
        precn_mul_wide(a.a[i], a.a[i], hi, lo);

        uint64_t out;
        uint64_t carry = precn_add_carry(r.a[i * 2], lo, 0, out);
        r.a[i * 2] = out;
        carry = precn_add_carry(r.a[i * 2 + 1], hi, carry, out);
        r.a[i * 2 + 1] = out;
        size_t k = i * 2 + 2;
        while(carry){
            carry = precn_add_carry(r.a[k], 0, carry, out);
            r.a[k++] = out;
        }

        for(size_t j = i + 1; j < n; ++j){
            precn_mul_wide(a.a[i], a.a[j], hi, lo);
            uint64_t d0 = lo << 1;
            uint64_t d1 = (hi << 1) | (lo >> 63);
            uint64_t d2 = hi >> 63;
            size_t p = i + j;

            carry = precn_add_carry(r.a[p], d0, 0, out);
            r.a[p] = out;
            carry = precn_add_carry(r.a[p + 1], d1, carry, out);
            r.a[p + 1] = out;
            carry = precn_add_carry(r.a[p + 2], d2, carry, out);
            r.a[p + 2] = out;
            p += 3;
            while(carry){
                carry = precn_add_carry(r.a[p], 0, carry, out);
                r.a[p++] = out;
            }
        }
    }
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
    memset(r.a, 0, (x->rsiz + y->rsiz + 1) * sizeof(uint64_t));
    r.rsiz = x->rsiz + y->rsiz;

    for(size_t i = 0; i < x->rsiz; ++i){
        uint64_t carry = 0;
        uint64_t av = x->a[i];
        for(size_t j = 0; j < y->rsiz; ++j){
            size_t k = i + j;
            uint64_t hi, lo;
            precn_mul_wide(av, y->a[j], hi, lo);
            uint64_t out;
            uint64_t c1 = precn_add_carry(r.a[k], lo, 0, out);
            uint64_t c2 = precn_add_carry(out, carry, 0, out);
            r.a[k] = out;
            carry = hi + c1 + c2;
        }

        size_t k = i + y->rsiz;
        while(carry){
            uint64_t out;
            carry = precn_add_carry(r.a[k], carry, 0, out);
            r.a[k] = out;
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

precn_t precn_sqr(const precn_t &a){
    if(a.rsiz == 0) return precn_t();

    // The dedicated basecase wins before recursive multiplication has enough
    // work to repay its temporary allocations.
    if(a.rsiz <= 64){
        precn_t r;
        mul_square_schoolbook_into(r, a);
        return r;
    }
    if(a.rsiz > MUL_DISPATCH_FFT_THRESHOLD) return mul_fft(a, a);
    return mul_karatsuba(a, a);
}

static void mul_unbalanced_into(precn_t &r, const precn_t &a, const precn_t &b){
    const precn_t *x = &a;
    const precn_t *y = &b;
    if(x->rsiz < y->rsiz) std::swap(x, y);

    mul_reserve(r, x->rsiz + y->rsiz + 1);
    memset(r.a, 0, (x->rsiz + y->rsiz + 1) * sizeof(uint64_t));
    r.rsiz = x->rsiz + y->rsiz + 1;

    // Keep every recursive product within a 2:1 aspect ratio.  This is the
    // same blocking idea ilmp uses for long-by-short products, and prevents
    // dispatching a tiny multiplier through an enormous FFT.
    size_t block = y->rsiz * 2;
    precn_t part;
    precn_t product;
    for(size_t off = 0; off < x->rsiz; off += block){
        size_t n = std::min(block, x->rsiz - off);
        if(part.asiz < n){
            part.a = (uint64_t*) realloc(part.a, n * sizeof(uint64_t));
            part.asiz = n;
        }
        part.rsiz = n;
        memcpy(part.a, x->a + off, n * sizeof(uint64_t));
        while(part.rsiz && part.a[part.rsiz - 1] == 0) --part.rsiz;

        mul_into(product, part, *y);
        mul_add_shift(r, product, off);
    }
    mul_norm(r);
}

void mul_into(precn_t &r, const precn_t &a, const precn_t &b){
    if(a.rsiz == 0 || b.rsiz == 0){
        mul_zero(r);
        return;
    }

    if(&a == &b){
        r = precn_sqr(a);
        return;
    }

    size_t lo = std::min(a.rsiz, b.rsiz);
    size_t hi = std::max(a.rsiz, b.rsiz);
    if(lo == 1){
        mul_limb_into(r, a.rsiz == 1 ? b : a, a.rsiz == 1 ? a.a[0] : b.a[0]);
        return;
    }
    if(lo <= MUL_DISPATCH_KARATSUBA_THRESHOLD){
        mul_schoolbook_into(r, a, b);
        return;
    }
    if(hi > lo * 2){
        mul_unbalanced_into(r, a, b);
        return;
    }
    if(hi > MUL_DISPATCH_NTT_THRESHOLD){
        r = mul_ntt(a, b);
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
