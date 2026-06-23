#include"../prec.hpp"

#include<vector>

static int div_cmp(const precn_t &a, const precn_t &b){
    if(a.rsiz != b.rsiz) return a.rsiz < b.rsiz ? -1 : 1;
    for(size_t i = a.rsiz; i > 0; --i){
        if(a.a[i - 1] != b.a[i - 1]) return a.a[i - 1] < b.a[i - 1] ? -1 : 1;
    }
    return 0;
}

static unsigned div_clz32(uint32_t x){
    unsigned n = 0;
    while((x & 0x80000000u) == 0){
        x <<= 1;
        ++n;
    }
    return n;
}

precn_t div_u32(const precn_t &a, uint32_t b){
    if(a.rsiz == 0 || b == 0) return precn_t();

    precn_t q;
    q.asiz = std::max<size_t>(a.rsiz, 1);
    q.a = (uint32_t*) realloc(q.a, q.asiz * 4);
    q.rsiz = a.rsiz;

    uint64_t rem = 0;
    for(size_t i = a.rsiz; i > 0; --i){
        uint64_t cur = (rem << 32) | a.a[i - 1];
        q.a[i - 1] = (uint32_t)(cur / b);
        rem = cur % b;
    }

    while(q.rsiz > 0 && q.a[q.rsiz - 1] == 0) --q.rsiz;
    if(q.rsiz == 0) q.a[0] = 0;
    return q;
}

precn_t mod_u32(const precn_t &a, uint32_t b){
    if(a.rsiz == 0 || b == 0) return precn_t();

    uint64_t rem = 0;
    for(size_t i = a.rsiz; i > 0; --i){
        uint64_t cur = (rem << 32) | a.a[i - 1];
        rem = cur % b;
    }
    return precn_t((uint32_t)rem);
}

static precn_t div_schoolbook_impl(const precn_t &a, const precn_t &b,
                                   precn_t *remainder, int want_quotient){
    if(a.rsiz == 0 || b.rsiz == 0){
        if(remainder) *remainder = precn_t();
        return precn_t();
    }
    if(div_cmp(a, b) < 0){
        if(remainder) *remainder = a;
        return precn_t();
    }
    if(b.rsiz == 1){
        if(remainder) *remainder = mod_u32(a, b.a[0]);
        return want_quotient ? div_u32(a, b.a[0]) : precn_t();
    }

    const uint64_t base = 1ULL << 32;
    size_t n = b.rsiz;
    size_t m = a.rsiz - n;
    unsigned shift = div_clz32(b.a[n - 1]);

    std::vector<uint32_t> vn(n);
    std::vector<uint32_t> un(a.rsiz + 1, 0);

    if(shift == 0){
        for(size_t i = 0; i < n; ++i) vn[i] = b.a[i];
        for(size_t i = 0; i < a.rsiz; ++i) un[i] = a.a[i];
    }else{
        uint32_t carry = 0;
        for(size_t i = 0; i < n; ++i){
            uint64_t cur = ((uint64_t)b.a[i] << shift) | carry;
            vn[i] = (uint32_t)cur;
            carry = (uint32_t)(cur >> 32);
        }

        carry = 0;
        for(size_t i = 0; i < a.rsiz; ++i){
            uint64_t cur = ((uint64_t)a.a[i] << shift) | carry;
            un[i] = (uint32_t)cur;
            carry = (uint32_t)(cur >> 32);
        }
        un[a.rsiz] = carry;
    }

    precn_t q;
    if(want_quotient){
        q.asiz = std::max<size_t>(m + 1, 1);
        q.a = (uint32_t*) realloc(q.a, q.asiz * 4);
        memset(q.a, 0, q.asiz * 4);
        q.rsiz = m + 1;
    }

    for(size_t jj = m + 1; jj > 0; --jj){
        size_t j = jj - 1;
        uint64_t top = ((uint64_t)un[j + n] << 32) | un[j + n - 1];
        uint64_t qhat = top / vn[n - 1];
        uint64_t rhat = top % vn[n - 1];

        while(qhat == base ||
              (qhat * vn[n - 2] > base * rhat + un[j + n - 2])){
            --qhat;
            rhat += vn[n - 1];
            if(rhat >= base) break;
        }

        uint64_t borrow = 0;
        for(size_t i = 0; i < n; ++i){
            uint64_t prod = qhat * vn[i] + borrow;
            uint32_t low = (uint32_t)prod;
            borrow = prod >> 32;

            uint32_t old = un[j + i];
            un[j + i] = old - low;
            if(old < low) ++borrow;
        }

        uint32_t old_top = un[j + n];
        un[j + n] = old_top - (uint32_t)borrow;
        if(old_top < borrow){
            --qhat;
            uint64_t carry = 0;
            for(size_t i = 0; i < n; ++i){
                uint64_t sum = (uint64_t)un[j + i] + vn[i] + carry;
                un[j + i] = (uint32_t)sum;
                carry = sum >> 32;
            }
            un[j + n] += (uint32_t)carry;
        }

        if(want_quotient) q.a[j] = (uint32_t)qhat;
    }

    if(want_quotient){
        while(q.rsiz > 0 && q.a[q.rsiz - 1] == 0) --q.rsiz;
        if(q.rsiz == 0) q.a[0] = 0;
    }

    if(remainder){
        precn_t r;
        r.asiz = std::max<size_t>(n, 1);
        r.a = (uint32_t*) realloc(r.a, r.asiz * 4);
        r.rsiz = n;
        if(shift == 0){
            for(size_t i = 0; i < n; ++i) r.a[i] = un[i];
        }else{
            for(size_t i = 0; i < n; ++i){
                r.a[i] = (un[i] >> shift) | (un[i + 1] << (32 - shift));
            }
        }
        while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
        if(r.rsiz == 0) r.a[0] = 0;
        *remainder = r;
    }
    return want_quotient ? q : precn_t();
}

precn_t div_schoolbook(const precn_t &a, const precn_t &b){
    return div_schoolbook_impl(a, b, nullptr, 1);
}

precn_t mod_schoolbook(const precn_t &a, const precn_t &b){
    precn_t remainder;
    div_schoolbook_impl(a, b, &remainder, 0);
    return remainder;
}

precn_t operator/(const precn_t &a, const precn_t &b){
    if(b.rsiz >= 65536) return div_mulinv(a, b);
    return div_schoolbook(a, b);
}

precn_t operator%(const precn_t &a, const precn_t &b){
    if(b.rsiz >= 65536) return mod_mulinv(a, b);
    return mod_schoolbook(a, b);
}
