#include<cstdint>
#include<cstdio>
#include<vector>

static uint64_t pow_mod(uint64_t a, uint64_t e, uint64_t p){
    uint64_t r = 1;
    while(e){
        if(e & 1) r = r * a % p;
        a = a * a % p;
        e >>= 1;
    }
    return r;
}

static bool is_prime(uint32_t n){
    if(n < 2) return false;
    for(uint32_t p = 2; (uint64_t)p * p <= n; ++p)
        if(n % p == 0) return n == p;
    return true;
}

static uint32_t primitive_root(uint32_t p){
    uint32_t x = p - 1;
    std::vector<uint32_t> factors;
    for(uint32_t q = 2; (uint64_t)q * q <= x; ++q){
        if(x % q) continue;
        factors.push_back(q);
        while(x % q == 0) x /= q;
    }
    if(x > 1) factors.push_back(x);
    for(uint32_t g = 2; g < p; ++g){
        bool ok = true;
        for(uint32_t q : factors)
            if(pow_mod(g, (p - 1) / q, p) == 1){ ok = false; break; }
        if(ok) return g;
    }
    return 0;
}

static uint32_t inverse_mod(uint32_t a, uint32_t p){
    return (uint32_t)pow_mod(a, p - 2, p);
}

int main(){
    const uint32_t unit = 1u << 20;
    const uint64_t exact_limit = 1ULL << 53;
    for(uint32_t k = 1; k <= 90; ++k){
        uint32_t p = k * unit + 1;
        if(!is_prime(p) || (uint64_t)p * p >= exact_limit) continue;
        printf("k=%u p=%u root=%u p2=%llu\n", k, p, primitive_root(p),
               (unsigned long long)p * p);
    }
    const uint32_t p0 = 70254593u;
    const uint32_t p1 = 81788929u;
    printf("pair product=%llu inverse=%u root_order=(%llu,%llu)\n",
           (unsigned long long)p0 * p1, inverse_mod(p0, p1),
           (unsigned long long)pow_mod(3, (p0 - 1) >> 1, p0),
           (unsigned long long)pow_mod(7, (p1 - 1) >> 1, p1));
}
