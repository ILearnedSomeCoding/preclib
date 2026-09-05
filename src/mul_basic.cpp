#include"../prec.hpp"

#ifndef MUL_DISPATCH_KARATSUBA_THRESHOLD
#define MUL_DISPATCH_KARATSUBA_THRESHOLD 32
#endif
#ifndef MUL_DISPATCH_SQUARE_BASECASE_THRESHOLD
#define MUL_DISPATCH_SQUARE_BASECASE_THRESHOLD 232
#endif
#ifndef MUL_DISPATCH_KARATSUBA_MAX
#define MUL_DISPATCH_KARATSUBA_MAX 320
#endif
#ifndef MUL_DISPATCH_FFT_THRESHOLD
#define MUL_DISPATCH_FFT_THRESHOLD 192
#endif
#ifndef MUL_DISPATCH_USE_VST
#define MUL_DISPATCH_USE_VST 1
#endif
#if !defined(MUL_DISPATCH_NTT_THRESHOLD)
#if defined(PRECN_FORCE_NO_SIMD) && PRECN_FORCE_NO_SIMD
// The scalar NTT remains slower than the scalar FFT through the largest
// benchmark sizes, so do not select it automatically in this configuration.
#define MUL_DISPATCH_NTT_THRESHOLD ((size_t)-1)
#elif defined(__AVX2__) || defined(_M_AVX2)
#define MUL_DISPATCH_NTT_THRESHOLD 2048
#else
// Scalar Montgomery butterflies do not catch the SSE2 FFT until roughly
// 16K limbs on x86-64.  Keep medium products on FFT without AVX2.
#define MUL_DISPATCH_NTT_THRESHOLD 12288
#endif
#endif
#define MUL_DISPATCH_TOOM_UNBALANCED_MIN 768
#define MUL_DISPATCH_TOOM_UNBALANCED_MAX 1280

void precn_mul_karatsuba_into_internal(precn_t &r, const precn_t &a,
                                       const precn_t &b);

static bool mul_fft_padding_favors_toom(size_t a, size_t b){
    // Above 1024 limbs the FFT uses eight-bit digits. Just after a power-of-two
    // boundary, padding can make Toom-3 cheaper than a nearly half-empty FFT.
    size_t digits = (a + b) * 8;
    size_t transform = 1;
    while(transform < digits) transform <<= 1;
    return transform / 4 * 3 >= digits;
}

static bool mul_ntt_padding_favors_toom(size_t a, size_t b){
    size_t digits = (a + b) * 4;
    size_t transform = 1;
    while(transform < digits) transform <<= 1;
    return transform / 4 * 3 >= digits;
}

static bool mul_fft16_padding_favors_karatsuba(size_t a, size_t b){
    size_t digits = (a + b) * 4;
    size_t transform = 1;
    while(transform < digits) transform <<= 1;
    return transform / 4 * 3 >= digits;
}

static precn_t mul_large_transform(const precn_t &a, const precn_t &b){
#if MUL_DISPATCH_USE_VST && \
    (defined(__AVX2__) || defined(_M_AVX2)) && \
    !(defined(PRECN_FORCE_NO_SIMD) && PRECN_FORCE_NO_SIMD)
    // mul_vst falls back to the integer NTT when its exact two-prime
    // transform would exceed the supported 2^20-point range.
    return mul_vst(a, b);
#else
    return mul_ntt(a, b);
#endif
}

static void mul_norm(precn_t &r){
    while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
}

static size_t mul_low_zero_limbs(const precn_t &a){
    size_t n = 0;
    while(n < a.rsiz && a.a[n] == 0) ++n;
    return n;
}

static void mul_shift_limbs_inplace(precn_t &a, size_t limbs){
    if(a.rsiz == 0 || limbs == 0) return;
    size_t need = a.rsiz + limbs;
    if(a.asiz < need){
        a.a = (uint64_t*)realloc(a.a, need * sizeof(uint64_t));
        a.asiz = need;
    }
    memmove(a.a + limbs, a.a, a.rsiz * sizeof(uint64_t));
    memset(a.a, 0, limbs * sizeof(uint64_t));
    a.rsiz = need;
}

static precn_t mul_without_low_limbs(const precn_t &a, size_t limbs){
    return a >> (limbs * 64);
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
        r = std::move(t);
        return;
    }
    if(a.rsiz == 0){
        mul_zero(r);
        return;
    }

    size_t n = a.rsiz;
    mul_reserve(r, n * 2 + 2);
    memset(r.a, 0, (n * 2 + 2) * sizeof(uint64_t));
    r.rsiz = n * 2 + 2;

    // Accumulate only the upper triangle.  Doubling every 128-bit product
    // separately needs a third output limb and three carry additions.  A
    // single linear doubling pass after the triangle is substantially cheaper.
    for(size_t i = 0; i + 1 < n; ++i){
        uint64_t carry = 0;
        uint64_t av = a.a[i];
        for(size_t j = i + 1; j < n; ++j){
            size_t k = i + j;
            uint64_t hi, lo, out;
            precn_mul_wide(av, a.a[j], hi, lo);
            uint64_t c1 = precn_add_carry(r.a[k], lo, 0, out);
            uint64_t c2 = precn_add_carry(out, carry, 0, out);
            r.a[k] = out;
            carry = hi + c1 + c2;
        }
        size_t k = i + n;
        while(carry){
            uint64_t out;
            carry = precn_add_carry(r.a[k], 0, carry, out);
            r.a[k++] = out;
        }
    }

    uint64_t carry = 0;
    for(size_t i = 0; i < n * 2 + 1; ++i){
        uint64_t next = r.a[i] >> 63;
        r.a[i] = (r.a[i] << 1) | carry;
        carry = next;
    }
    r.a[n * 2 + 1] = carry;

    // Add the diagonal terms a[i]^2 after 2*sum(i<j) is normalized.
    for(size_t i = 0; i < n; ++i){
        uint64_t hi, lo, out;
        precn_mul_wide(a.a[i], a.a[i], hi, lo);
        size_t k = i * 2;
        uint64_t diagonal_carry = precn_add_carry(r.a[k], lo, 0, out);
        r.a[k] = out;
        diagonal_carry = precn_add_carry(r.a[k + 1], hi,
                                         diagonal_carry, out);
        r.a[k + 1] = out;
        k += 2;
        while(diagonal_carry){
            diagonal_carry = precn_add_carry(r.a[k], 0,
                                              diagonal_carry, out);
            r.a[k++] = out;
        }
    }
    mul_norm(r);
}

static void mul_schoolbook_into(precn_t &r, const precn_t &a, const precn_t &b){
    if(&r == &a || &r == &b){
        precn_t t;
        mul_schoolbook_into(t, a, b);
        r = std::move(t);
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
    if(x->rsiz < y->rsiz) std::swap(x, y);

    mul_reserve(r, x->rsiz + y->rsiz + 1);
    memset(r.a, 0, (x->rsiz + y->rsiz + 1) * sizeof(uint64_t));
    r.rsiz = x->rsiz + y->rsiz;

    // Each outer iteration is one addmul_1 row.  Put the shorter operand on
    // the outside so unbalanced products execute fewer row prologues and
    // carry tails while the long operand is streamed contiguously.
    for(size_t i = 0; i < y->rsiz; ++i){
        uint64_t carry = 0;
        uint64_t av = y->a[i];
        for(size_t j = 0; j < x->rsiz; ++j){
            size_t k = i + j;
            uint64_t hi, lo;
            precn_mul_wide(av, x->a[j], hi, lo);
            uint64_t out;
            uint64_t c1 = precn_add_carry(r.a[k], lo, 0, out);
            uint64_t c2 = precn_add_carry(out, carry, 0, out);
            r.a[k] = out;
            carry = hi + c1 + c2;
        }

        size_t k = i + x->rsiz;
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

void precn_sqr_into(precn_t &r, const precn_t &a){
    if(&r == &a){
        precn_t t;
        precn_sqr_into(t, a);
        r = std::move(t);
        return;
    }
    if(a.rsiz == 0){
        mul_zero(r);
        return;
    }
    if(a.rsiz == 1){
        mul_limb_into(r, a, a.a[0]);
        return;
    }

    if(a.rsiz > MUL_DISPATCH_FFT_THRESHOLD){
        size_t zeros = mul_low_zero_limbs(a);
        if(zeros){
            precn_t core = precn_sqr(mul_without_low_limbs(a, zeros));
            mul_shift_limbs_inplace(core, zeros * 2);
            r = std::move(core);
            return;
        }
    }

    if(a.rsiz <= MUL_DISPATCH_SQUARE_BASECASE_THRESHOLD){
        mul_square_schoolbook_into(r, a);
        return;
    }
    if(a.rsiz >= MUL_DISPATCH_NTT_THRESHOLD){
        if(a.rsiz < 3072 && mul_ntt_padding_favors_toom(a.rsiz, a.rsiz))
            r = mul_toom(a, a);
        else r = mul_large_transform(a, a);
        return;
    }
    if(a.rsiz > MUL_DISPATCH_FFT_THRESHOLD) r = mul_fft(a, a);
    else r = mul_karatsuba(a, a);
}

precn_t precn_sqr(const precn_t &a){
    precn_t r;
    precn_sqr_into(r, a);
    return r;
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
    size_t block = x->rsiz == y->rsiz * 2 ? y->rsiz : y->rsiz * 2;
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

static size_t mul_ntt_transform_size(size_t a_limbs, size_t b_limbs){
    size_t need = (a_limbs + b_limbs) * 4;
    size_t n = 1;
    while(n < need) n <<= 1;
    return n;
}

void mul_into(precn_t &r, const precn_t &a, const precn_t &b){
    if(a.rsiz == 0 || b.rsiz == 0){
        mul_zero(r);
        return;
    }

    if(&a == &b){
        precn_sqr_into(r, a);
        return;
    }

    size_t lo = std::min(a.rsiz, b.rsiz);
    size_t hi = std::max(a.rsiz, b.rsiz);
    if(std::max(a.rsiz, b.rsiz) > MUL_DISPATCH_FFT_THRESHOLD){
        size_t za = mul_low_zero_limbs(a);
        size_t zb = mul_low_zero_limbs(b);
        if(za || zb){
            precn_t aa;
            precn_t bb;
            const precn_t *pa = &a;
            const precn_t *pb = &b;
            if(za){
                aa = mul_without_low_limbs(a, za);
                pa = &aa;
            }
            if(zb){
                bb = mul_without_low_limbs(b, zb);
                pb = &bb;
            }
            r = *pa * *pb;
            mul_shift_limbs_inplace(r, za + zb);
            return;
        }
    }

    if(lo == 1){
        mul_limb_into(r, a.rsiz == 1 ? b : a, a.rsiz == 1 ? a.a[0] : b.a[0]);
        return;
    }
    if(lo <= MUL_DISPATCH_KARATSUBA_THRESHOLD){
        mul_schoolbook_into(r, a, b);
        return;
    }
    if(hi <= 192 && hi <= lo * 2){
        precn_mul_karatsuba_into_internal(r, a, b);
        return;
    }
    if(hi <= 192){
        mul_schoolbook_into(r, a, b);
        return;
    }
    bool split_exact_2x = hi == lo * 2 && lo >= 512 && lo <= 1024;
    if(hi > lo * 2 || split_exact_2x){
        // For mildly unbalanced large products, blocking can make the first
        // block use exactly the same transform as the whole product, then add
        // another product for the tail. Keep it whole in that case.
        size_t first_block = lo * 2;
        if(lo >= MUL_DISPATCH_NTT_THRESHOLD &&
           mul_ntt_transform_size(hi, lo) == mul_ntt_transform_size(first_block, lo)){
            r = mul_large_transform(a, b);
            return;
        }
        mul_unbalanced_into(r, a, b);
        return;
    }
    if(hi <= MUL_DISPATCH_KARATSUBA_MAX &&
       mul_fft16_padding_favors_karatsuba(hi, lo)){
        precn_mul_karatsuba_into_internal(r, a, b);
        return;
    }
    if(hi >= MUL_DISPATCH_NTT_THRESHOLD){
        if(hi < 3072 && lo * 2 >= hi && mul_ntt_padding_favors_toom(hi, lo)){
            r = mul_toom(a, b);
            return;
        }
        r = mul_large_transform(a, b);
        return;
    }
    if(hi > 1024 && hi < MUL_DISPATCH_NTT_THRESHOLD &&
       lo * 2 >= hi && mul_fft_padding_favors_toom(hi, lo)){
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
    if(a.rsiz == 1) return mul_u64(b, a.a[0]);
    if(b.rsiz == 1) return mul_u64(a, b.a[0]);

    bool small = &a == &b ? a.rsiz <= MUL_DISPATCH_SQUARE_BASECASE_THRESHOLD
                          : std::max(a.rsiz, b.rsiz) <= 192;
    size_t capacity = &a == &b ? a.rsiz * 2 + 2
                               : a.rsiz + b.rsiz + 1;
    precn_t r = small ? precn_t::with_capacity(capacity) : precn_t();
    mul_into(r, a, b);
    return r;
}

precn_t mul_basic(const precn_t &a, const precn_t &b){
    return mul_schoolbook(a, b);
}
