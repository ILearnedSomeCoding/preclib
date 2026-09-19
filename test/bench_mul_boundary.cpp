#include "../prec.hpp"
#include <algorithm>
#include <chrono>
#include <cstdio>
#include <vector>

static precn_t pattern(size_t n, uint64_t seed){
    precn_t r = precn_t::with_capacity(n);
    r.rsiz = n;
    for(size_t i = 0; i < n; ++i){
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        r.a[i] = seed;
    }
    r.a[n - 1] |= uint64_t(1) << 63;
    return r;
}

int main(){
    precn_set_ntt_threads(1);
    precn_set_ntt_thread_parallel(false);
    const size_t shapes[][2] = {
        {17000, 15768}, {17000, 15769}, {18000, 16000},
        {17700, 16092}, {17701, 16092}, {37783, 31123},
        {41040, 11827}, {70000, 65536}, {80000, 60000}
    };
    puts("a_limbs,b_limbs,round,dispatch_seconds,whole_vst_seconds");
    for(const auto &shape : shapes){
        precn_t a = pattern(shape[0], 713), b = pattern(shape[1], 997);
        precn_t want = mul_ntt(a, b);
        if(a * b != want || mul_vst(a, b) != want) return 1;
        for(unsigned round = 0; round < 9; ++round){
            double times[2];
            for(unsigned j = 0; j < 2; ++j){
                unsigned method = (j + round) % 2;
                auto begin = std::chrono::steady_clock::now();
                precn_t product = method ? mul_vst(a, b) : a * b;
                times[method] = std::chrono::duration<double>(
                    std::chrono::steady_clock::now() - begin).count();
                if(product != want) return 2;
            }
            printf("%zu,%zu,%u,%.9f,%.9f\n", shape[0], shape[1], round,
                   times[0], times[1]);
        }
    }
}
