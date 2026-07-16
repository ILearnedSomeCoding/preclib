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
    for(size_t i = 0; i < a.rsiz; ++i){
        if(a.a[i] != b.a[i]) return false;
    }
    return true;
}

typedef precn_t (*div_fn_t)(const precn_t &, const precn_t &);

struct bench_result_t{
    precn_t value;
    double seconds;
};

static bench_result_t bench(div_fn_t fn, const precn_t &a, const precn_t &b, size_t reps){
    using clock_t = std::chrono::steady_clock;
    clock_t::time_point start = clock_t::now();
    precn_t value;
    for(size_t i = 0; i < reps; ++i) value = fn(a, b);
    double seconds = std::chrono::duration<double>(clock_t::now() - start).count() / reps;
    return bench_result_t{value, seconds};
}

static size_t reps_for(size_t limbs){
    if(limbs <= 64) return 1000;
    if(limbs <= 256) return 100;
    if(limbs <= 1024) return 20;
    if(limbs <= 4096) return 3;
    return 1;
}

int main(int argc, char **argv){
    size_t max_n = 10;
    if(argc > 1) max_n = (size_t)strtoull(argv[1], nullptr, 10);
    if(max_n > 20) max_n = 20;

    puts("division benchmark");
    printf("%-8s %-10s %-10s %-6s %-15s %-15s %-10s\n",
           "n", "dividend", "divisor", "reps", "basecase", "mulinv", "ratio");

    for(size_t n = 0; n <= max_n; ++n){
        size_t limbs = (size_t)1 << n;
        size_t reps = reps_for(limbs);
        precn_t divisor = pattern(limbs, 1000 + n);
        precn_t quotient = pattern(limbs, 2000 + n);
        precn_t dividend = divisor * quotient + (divisor - 1);

        bench_result_t basecase = bench(div_schoolbook, dividend, divisor, reps);
        bench_result_t mulinv = bench(div_mulinv, dividend, divisor, reps);
        if(!same(basecase.value, quotient) || !same(mulinv.value, quotient)){
            fprintf(stderr, "wrong quotient at 2^%zu\n", n);
            return 1;
        }

        char label[16];
        snprintf(label, sizeof(label), "2^%zu", n);
        printf("%-8s %-10zu %-10zu %-6zu %-15.9f %-15.9f %-10.2f\n",
               label, dividend.rsiz, divisor.rsiz, reps,
               basecase.seconds, mulinv.seconds, basecase.seconds / mulinv.seconds);
        fflush(stdout);
    }
    puts("ok");
    return 0;
}
