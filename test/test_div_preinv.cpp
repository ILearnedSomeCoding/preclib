#include"../prec.hpp"

#include<cstdio>

static precn_t pattern(size_t n, uint64_t &state){
    precn_t r = precn_t::with_capacity(n);
    r.rsiz = n;
    for(size_t i = 0; i < n; ++i){
        state = state * 6364136223846793005ULL + 1442695040888963407ULL;
        r.a[i] = state;
    }
    r.a[n - 1] |= 1ULL << 63;
    return r;
}

int main(){
    uint64_t state = 1;
    for(size_t n = 4; n <= 32; ++n){
        for(size_t trial = 0; trial < 10000; ++trial){
            precn_t a = pattern(n, state);
            state = state * 6364136223846793005ULL + 1442695040888963407ULL;
            uint64_t d = state | 3;
            precn_t q = div_u64(a, d);
            precn_t r = mod_u64(a, d);
            if(q * d + r != a || (r.rsiz && r.a[0] >= d)){
                fprintf(stderr, "scalar mismatch n=%zu trial=%zu d=%llu\n",
                        n, trial, (unsigned long long)d);
                return 1;
            }
        }
    }
    for(size_t n = 1; n <= 512; n = n < 16 ? n + 1 : n * 2){
        for(size_t trial = 0; trial < 200; ++trial){
            precn_t a = pattern(n, state);
            precn_t expected = div_u64(a, 10000000000ULL);
            precn_t got;
            precn_div_1e10_into(got, a);
            if(got != expected){
                fprintf(stderr, "fixed 1e10 mismatch n=%zu trial=%zu\n",
                        n, trial);
                return 1;
            }
            precn_div_1e10_into(a, a);
            if(a != expected){
                fprintf(stderr, "fixed 1e10 alias mismatch n=%zu trial=%zu\n",
                        n, trial);
                return 1;
            }
        }
    }
    for(size_t n = 2; n <= 64; ++n){
        for(size_t trial = 0; trial < 1000; ++trial){
            precn_t d = pattern(n, state);
            precn_t want = pattern(1 + trial % 128, state);
            precn_t rem = d - precn_t(1);
            precn_t a = d * want + rem;
            precn_t q;
            precn_t r;
            divmod_into(q, r, a, d);
            if(q != want || r != rem){
                fprintf(stderr, "schoolbook mismatch n=%zu trial=%zu\n",
                        n, trial);
                return 1;
            }
        }
    }
    puts("preinverse division ok");
    return 0;
}
