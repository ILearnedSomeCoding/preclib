#include"../prec.hpp"

#include<chrono>
#include<cstdio>
#include<vector>

static uint64_t divq_1e19(uint64_t hi, uint64_t lo, uint64_t &rem){
    const uint64_t d = 10000000000000000000ULL;
#if defined(__clang__) && defined(__x86_64__)
    __asm__ volatile("divq %2" : "+a"(lo), "+d"(hi) : "r"(d) : "cc");
    rem = hi;
    return lo;
#else
    precn_t a = (precn_t(hi) << 64) + precn_t(lo);
    precn_t q = div_u64(a, d);
    precn_t r = mod_u64(a, d);
    rem = r.rsiz ? r.a[0] : 0;
    return q.rsiz ? q.a[0] : 0;
#endif
}

static uint64_t preinv_1e19(uint64_t hi, uint64_t lo, uint64_t &rem){
    const uint64_t d = 10000000000000000000ULL;
    const uint64_t inverse = 15581492618384294730ULL;
    uint64_t qh, ql;
    precn_mul_wide(hi, inverse, qh, ql);
    uint64_t estimate_low;
    uint64_t carry = precn_add_carry(ql, lo, 0, estimate_low);
    uint64_t estimate;
    precn_add_carry(qh, hi + 1, carry, estimate);
    uint64_t r = lo - estimate * d;
    if(r > estimate_low){ --estimate; r += d; }
    if(r >= d){ ++estimate; r -= d; }
    rem = r;
    return estimate;
}

int main(){
    const size_t count = 1 << 20;
    std::vector<uint64_t> hi(count), lo(count);
    uint64_t state = 1;
    for(size_t i = 0; i < count; ++i){
        state = state * 6364136223846793005ULL + 1442695040888963407ULL;
        hi[i] = state % 10000000000000000000ULL;
        state = state * 6364136223846793005ULL + 1442695040888963407ULL;
        lo[i] = state;
    }

    uint64_t sum_divq = 0, sum_preinv = 0;
    auto start = std::chrono::steady_clock::now();
    for(size_t repeat = 0; repeat < 64; ++repeat){
        for(size_t i = 0; i < count; ++i){
            uint64_t rem;
            sum_divq += divq_1e19(hi[i], lo[i], rem) ^ rem;
        }
    }
    auto middle = std::chrono::steady_clock::now();
    for(size_t repeat = 0; repeat < 64; ++repeat){
        for(size_t i = 0; i < count; ++i){
            uint64_t rem;
            sum_preinv += preinv_1e19(hi[i], lo[i], rem) ^ rem;
        }
    }
    auto finish = std::chrono::steady_clock::now();
    double divq_time = std::chrono::duration<double>(middle - start).count();
    double preinv_time = std::chrono::duration<double>(finish - middle).count();
    printf("divq %.9f sec\npreinv %.9f sec\nratio %.4f\ncheck %s\n",
           divq_time, preinv_time, preinv_time / divq_time,
           sum_divq == sum_preinv ? "ok" : "mismatch");
    return sum_divq == sum_preinv ? 0 : 1;
}
