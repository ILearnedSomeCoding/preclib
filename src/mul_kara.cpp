#include"../prec.hpp"
#include"toom_cook_ptr.hpp"

static size_t kara_trim(ptr_len x){
    while(x.siz > 0 && x.a[x.siz - 1] == 0) --x.siz;
    return x.siz;
}

static precn_t kara_from_ptr(ptr_len x){
    x.siz = kara_trim(x);
    precn_t r;
    r.asiz = std::max<size_t>(x.siz, 1);
    r.a = (uint32_t*) realloc(r.a, r.asiz * 4);
    r.rsiz = x.siz;
    if(x.siz) memcpy(r.a, x.a, x.siz * 4);
    else r.a[0] = 0;
    return r;
}

static int kara_cmp(const precn_t &a, const precn_t &b){
    if(a.rsiz != b.rsiz) return a.rsiz < b.rsiz ? -1 : 1;
    for(size_t i = a.rsiz; i > 0; --i){
        if(a.a[i - 1] != b.a[i - 1]) return a.a[i - 1] < b.a[i - 1] ? -1 : 1;
    }
    return 0;
}

static precn_t kara_basic(ptr_len a, ptr_len b){
    a.siz = kara_trim(a);
    b.siz = kara_trim(b);
    if(a.siz == 0 || b.siz == 0) return precn_t();

    precn_t r;
    r.asiz = a.siz + b.siz + 1;
    r.a = (uint32_t*) realloc(r.a, r.asiz * 4);
    memset(r.a, 0, r.asiz * 4);
    r.rsiz = a.siz + b.siz;

    for(size_t i = 0; i < a.siz; ++i){
        uint64_t carry = 0;
        for(size_t j = 0; j < b.siz; ++j){
            size_t k = i + j;
            uint64_t prod = (uint64_t)a.a[i] * b.a[j] + r.a[k] + carry;
            r.a[k] = (uint32_t)(prod & 0xFFFFFFFFu);
            carry = prod >> 32;
        }

        size_t k = i + b.siz;
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

static precn_t kara_shift(const precn_t &a, size_t limbs){
    if(a.rsiz == 0) return precn_t();

    precn_t r;
    r.asiz = a.rsiz + limbs;
    r.a = (uint32_t*) realloc(r.a, r.asiz * 4);
    memset(r.a, 0, limbs * 4);
    memcpy(r.a + limbs, a.a, a.rsiz * 4);
    r.rsiz = a.rsiz + limbs;
    return r;
}

static precn_t kara_mul(ptr_len a, ptr_len b){
    a.siz = kara_trim(a);
    b.siz = kara_trim(b);
    if(a.siz == 0 || b.siz == 0) return precn_t();

    size_t n = std::max(a.siz, b.siz);
    if(n <= 32) return kara_basic(a, b);

    size_t m = n / 2;
    ptr_len a0 = {std::min(a.siz, m), a.a};
    ptr_len b0 = {std::min(b.siz, m), b.a};
    ptr_len a1 = {a.siz > m ? a.siz - m : 0, a.a + std::min(a.siz, m)};
    ptr_len b1 = {b.siz > m ? b.siz - m : 0, b.a + std::min(b.siz, m)};

    precn_t z0 = kara_mul(a0, b0);
    precn_t z2 = kara_mul(a1, b1);
    precn_t pa0 = kara_from_ptr(a0);
    precn_t pa1 = kara_from_ptr(a1);
    precn_t pb0 = kara_from_ptr(b0);
    precn_t pb1 = kara_from_ptr(b1);
    int da_neg = kara_cmp(pa0, pa1) < 0;
    int db_neg = kara_cmp(pb0, pb1) < 0;
    precn_t da = da_neg ? pa1 - pa0 : pa0 - pa1;
    precn_t db = db_neg ? pb1 - pb0 : pb0 - pb1;
    ptr_len dap = {da.rsiz, da.a};
    ptr_len dbp = {db.rsiz, db.a};
    precn_t vm1 = kara_mul(dap, dbp);
    precn_t z1 = (da_neg ^ db_neg) ? z0 + z2 + vm1 : z0 + z2 - vm1;

    return z0 + kara_shift(z1, m) + kara_shift(z2, m * 2);
}

precn_t mul_karatsuba(const precn_t &a, const precn_t &b){
    ptr_len ap = {a.rsiz, a.a};
    ptr_len bp = {b.rsiz, b.a};
    return kara_mul(ap, bp);
}
