#include"../prec.hpp"

#include<gmp.h>

#include<cassert>
#include<cstdio>
#include<cstdlib>
#include<ctime>

static double now_sec(){
    return (double)clock() / CLOCKS_PER_SEC;
}

static precn_t pattern(size_t n, uint32_t seed){
    precn_t r;
    r.asiz = n ? n : 1;
    r.a = (uint32_t*) realloc(r.a, r.asiz * 4);
    r.rsiz = n;
    uint32_t x = seed;
    for(size_t i = 0; i < n; ++i){
        x = x * 1664525u + 1013904223u;
        r.a[i] = x | 1u;
    }
    while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}

static void precn_to_mpz(mpz_t z, const precn_t &a){
    if(a.rsiz == 0){
        mpz_set_ui(z, 0);
        return;
    }
    mpz_import(z, a.rsiz, -1, sizeof(uint32_t), 0, 0, a.a);
}

static size_t mpz_limbs(const mpz_t z){
    if(mpz_sgn(z) == 0) return 0;
    return (mpz_sizeinbase(z, 2) + 31) / 32;
}

static void check_same(const precn_t &a, const mpz_t b){
    mpz_t t;
    mpz_init(t);
    precn_to_mpz(t, a);
    assert(mpz_cmp(t, b) == 0);
    mpz_clear(t);
}

static int reps_for(size_t n){
    if(n < 256) return 100000;
    if(n <= 1024) return 100;
    if(n <= 32768) return 10;
    return 1;
}

static double bench_prec_mul(const precn_t &a, const precn_t &b, int reps, precn_t &out){
    double st = now_sec();
    for(int i = 0; i < reps; ++i) mul_into(out, a, b);
    return now_sec() - st;
}

static double bench_gmp_mul(const mpz_t a, const mpz_t b, int reps, mpz_t out){
    double st = now_sec();
    for(int i = 0; i < reps; ++i) mpz_mul(out, a, b);
    return now_sec() - st;
}

static double bench_prec_div(const precn_t &a, const precn_t &b, int reps, precn_t &out){
    double st = now_sec();
    for(int i = 0; i < reps; ++i) out = a / b;
    return now_sec() - st;
}

static double bench_gmp_div(const mpz_t a, const mpz_t b, int reps, mpz_t out){
    double st = now_sec();
    for(int i = 0; i < reps; ++i) mpz_tdiv_q(out, a, b);
    return now_sec() - st;
}

static void run_mul(size_t max_pow){
    std::printf("mul speed vs gmp\n");
    std::printf("%-8s %-8s %-6s %-15s %-15s %-10s %-10s\n",
                "n", "limbs", "reps", "prec", "gmp", "ratio", "result");
    for(size_t p = 0; p <= max_pow; ++p){
        size_t n = (size_t)1 << p;
        int reps = reps_for(n);
        precn_t a = pattern(n, 11u + (uint32_t)p);
        precn_t b = pattern(n, 19u + (uint32_t)p);
        precn_t rp;

        mpz_t ga, gb, gr;
        mpz_inits(ga, gb, gr, NULL);
        precn_to_mpz(ga, a);
        precn_to_mpz(gb, b);

        double tp = bench_prec_mul(a, b, reps, rp);
        double tg = bench_gmp_mul(ga, gb, reps, gr);
        check_same(rp, gr);

        std::printf("2^%-6zu %-8zu %-6d %-15.9f %-15.9f %-10.2f %-10zu\n",
                    p, n, reps, tp / reps, tg / reps,
                    tg > 0.0 ? tp / tg : 0.0, rp.rsiz);
        mpz_clears(ga, gb, gr, NULL);
    }
}

static void run_div(size_t max_pow){
    std::printf("\ndiv speed vs gmp\n");
    std::printf("%-8s %-8s %-8s %-6s %-15s %-15s %-10s %-10s\n",
                "n", "den", "num", "reps", "prec", "gmp", "ratio", "quot");
    for(size_t p = 0; p <= max_pow; ++p){
        size_t n = (size_t)1 << p;
        int reps = reps_for(n);
        precn_t den = pattern(n, 31u + (uint32_t)p);
        precn_t want_q = pattern(n, 43u + (uint32_t)p);
        precn_t num = den * want_q + (den - precn_t(1));
        precn_t rq;

        mpz_t gnum, gden, gq, gwant;
        mpz_inits(gnum, gden, gq, gwant, NULL);
        precn_to_mpz(gnum, num);
        precn_to_mpz(gden, den);
        precn_to_mpz(gwant, want_q);

        double tp = bench_prec_div(num, den, reps, rq);
        double tg = bench_gmp_div(gnum, gden, reps, gq);
        check_same(rq, gq);
        assert(mpz_cmp(gq, gwant) == 0);

        std::printf("2^%-6zu %-8zu %-8zu %-6d %-15.9f %-15.9f %-10.2f %-10zu\n",
                    p, den.rsiz, num.rsiz, reps, tp / reps, tg / reps,
                    tg > 0.0 ? tp / tg : 0.0, mpz_limbs(gq));
        mpz_clears(gnum, gden, gq, gwant, NULL);
    }
}

int main(int argc, char **argv){
    size_t max_pow = 14;
    if(argc >= 2) max_pow = (size_t)std::atoi(argv[1]);

    run_mul(max_pow);
    run_div(max_pow);
    std::printf("ok\n");
    return 0;
}
