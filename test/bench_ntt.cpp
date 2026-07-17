#include"../prec.hpp"

#include<chrono>
#include<cstdio>

static precn_t pattern(size_t n, uint64_t seed){
    precn_t r;
    r.asiz = n ? n : 1;
    r.a = (uint64_t*) realloc(r.a, r.asiz * sizeof(uint64_t));
    r.rsiz = n;
    uint64_t x = seed;
    for(size_t i = 0; i < n; ++i){
        x = x * 6364136223846793005ULL + 1442695040888963407ULL;
        r.a[i] = x | 1;
    }
    return r;
}

static bool same(const precn_t &a, const precn_t &b){
    if(a.rsiz != b.rsiz) return false;
    for(size_t i = 0; i < a.rsiz; ++i) if(a.a[i] != b.a[i]) return false;
    return true;
}

int main(){
    using clock_t = std::chrono::steady_clock;
    puts("ntt timing");
    printf("%-10s %-8s %-15s %-15s %-10s\n", "limbs", "reps", "fft", "ntt", "ntt/fft");
    for(size_t n = 1024; n <= 65536; n <<= 1){
        size_t reps = n <= 4096 ? 5 : n <= 16384 ? 3 : 2;
        precn_t a = pattern(n, 1000 + n);
        precn_t b = pattern(n, 2000 + n);
        precn_t result, reference;
        double fft_sec = 0.0;
        double ntt_sec = 0.0;
        for(size_t i = 0; i < reps; ++i){
            bool fft_first = (i & 1) == 0;
            for(size_t pass = 0; pass < 2; ++pass){
                bool run_fft = pass == 0 ? fft_first : !fft_first;
                clock_t::time_point begin = clock_t::now();
                if(run_fft) reference = mul_fft(a, b);
                else result = mul_ntt(a, b);
                double sec = std::chrono::duration<double>(clock_t::now() - begin).count();
                if(run_fft) fft_sec += sec;
                else ntt_sec += sec;
            }
        }
        fft_sec /= reps;
        ntt_sec /= reps;
        if(!same(result, reference)){
            fprintf(stderr, "mismatch at %zu limbs\n", n);
            return 1;
        }
        printf("%-10zu %-8zu %-15.9f %-15.9f %-10.3f\n",
               n, reps, fft_sec, ntt_sec, ntt_sec / fft_sec);
    }
    return 0;
}
