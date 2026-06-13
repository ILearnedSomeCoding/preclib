#include"../prec.hpp"

#include<cassert>
#include<cstdio>
#include<ctime>
#include<vector>

static precn_t make_prec(const std::vector<uint32_t> &v){
    precn_t r;
    r.asiz = std::max<size_t>(v.size(), 1);
    r.a = (uint32_t*) realloc(r.a, r.asiz * 4);
    r.rsiz = v.size();
    for(size_t i = 0; i < v.size(); ++i) r.a[i] = v[i];
    while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}

static void expect(const precn_t &a, const std::vector<uint32_t> &v){
    size_t n = v.size();
    while(n > 0 && v[n - 1] == 0) --n;
    assert(a.rsiz == n);
    for(size_t i = 0; i < n; ++i) assert(a.a[i] == v[i]);
}

static void expect_eq_named(const char *name, const precn_t &a, const precn_t &b){
    if(a.rsiz != b.rsiz){
        printf("%s size mismatch: %zu != %zu\n", name, a.rsiz, b.rsiz);
        assert(a.rsiz == b.rsiz);
    }
    for(size_t i = 0; i < a.rsiz; ++i){
        if(a.a[i] != b.a[i]){
            printf("%s limb mismatch at %zu: %08x != %08x\n", name, i, a.a[i], b.a[i]);
            fflush(stdout);
            assert(a.a[i] == b.a[i]);
        }
    }
}

static void expect_eq(const precn_t &a, const precn_t &b){
    expect_eq_named("expect_eq", a, b);
}

static void print_dec(const precn_t &a){
    if(a.rsiz == 0){
        puts("0");
        return;
    }

    std::vector<uint32_t> x(a.a, a.a + a.rsiz);
    std::vector<char> out;
    while(!x.empty()){
        uint64_t rem = 0;
        for(size_t i = x.size(); i > 0; --i){
            uint64_t cur = (rem << 32) | x[i - 1];
            x[i - 1] = (uint32_t)(cur / 10);
            rem = cur % 10;
        }
        out.push_back((char)('0' + rem));
        while(!x.empty() && x.back() == 0) x.pop_back();
    }

    for(size_t i = out.size(); i > 0; --i) putchar(out[i - 1]);
    putchar('\n');
}

static precn_t pattern(size_t n, uint32_t seed){
    precn_t r;
    r.asiz = std::max<size_t>(n, 1);
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

static void test_init(){
    expect(precn_t(), {});
    expect(precn_t(0), {});
    expect(precn_t(1), {1});
    expect(precn_t(-7), {});
    expect(precn_t(0x100000000ULL), {0, 1});
    expect(precn_t(std::string("4294967296")), {0, 1});
}

static void test_add_sub(){
    precn_t a = make_prec({0xFFFFFFFFu, 0xFFFFFFFFu});
    precn_t b = make_prec({1});
    expect(a + b, {0, 0, 1});
    expect((a + b) - b, {0xFFFFFFFFu, 0xFFFFFFFFu});
    expect(b - a, {});
    expect(make_prec({0, 1}) - make_prec({1}), {0xFFFFFFFFu});
}

static void test_mul_u32(){
    expect(mul_u32(make_prec({0xFFFFFFFFu}), 2), {0xFFFFFFFEu, 1});
    expect(mul_u32(make_prec({123, 456}), 0), {});
    expect(mul_u32(make_prec({0xFFFFFFFFu, 0xFFFFFFFFu}), 0xFFFFFFFFu),
           {1, 0xFFFFFFFFu, 0xFFFFFFFEu});
}

static void test_mul_basic(){
    precn_t a = make_prec({0xFFFFFFFFu, 1});
    precn_t b = make_prec({2});
    expect(a * b, {0xFFFFFFFEu, 3});
    expect_eq(mul_basic(a, b), a * b);
    expect(mul_fft(make_prec({0xFFFFFFFFu}), make_prec({0xFFFFFFFFu})), {1, 0xFFFFFFFEu});
    expect_eq(mul_fft(a, b), a * b);
    expect(mul_ntt(make_prec({0xFFFFFFFFu}), make_prec({0xFFFFFFFFu})), {1, 0xFFFFFFFEu});
    expect_eq(mul_ntt(a, b), a * b);
}

static void test_divexact(){
    expect(precn_divexact_2(make_prec({0, 2})), {0, 1});
    expect(precn_divexact_3(make_prec({3, 3})), {1, 1});
}

typedef precn_t (*mul_fn_t)(const precn_t&, const precn_t&);

struct bench_mul_result_t{
    precn_t v;
    double sec;
};

static bench_mul_result_t bench_mul_once(mul_fn_t mul, const precn_t &a, const precn_t &b, size_t reps){
    clock_t start = clock();
    clock_t end = start;
    precn_t r;
    for(size_t i = 0; i < reps; ++i){
        precn_t t = mul(a, b);
        if(i + 1 == reps){
            end = clock();
            r = t;
        }
    }
    return bench_mul_result_t{r, (double)(end - start) / CLOCKS_PER_SEC / reps};
}

static size_t bench_reps_for_n(size_t n){
    if(n <= 10) return 100;
    if(n <= 15) return 10;
    return 1;
}

static precn_t mul_op(const precn_t &a, const precn_t &b){
    return a * b;
}

static precn_t pow_fast(precn_t base, size_t exp, mul_fn_t mul){
    precn_t r(1);
    while(exp){
        if(exp & 1) r = mul(r, base);
        exp >>= 1;
        if(exp) base = mul(base, base);
    }
    return r;
}

struct pow_rep_t{
    precn_t pow10;
    precn_t repunit;
};

static pow_rep_t pow_rep_fast(size_t n, mul_fn_t mul){
    if(n == 0) return pow_rep_t{precn_t(1), precn_t()};

    pow_rep_t h = pow_rep_fast(n / 2, mul);
    precn_t p2 = mul(h.pow10, h.pow10);
    precn_t r2 = mul(h.repunit, h.pow10 + precn_t(1));

    if(n & 1){
        return pow_rep_t{mul(p2, precn_t(10)), mul(r2, precn_t(10)) + precn_t(1)};
    }
    return pow_rep_t{p2, r2};
}

static void test_repunit_1000_with(mul_fn_t mul, int print){
    precn_t pow10 = pow_fast(precn_t(10), 10000, mul);
    precn_t repunit = pow_rep_fast(10000, mul).repunit;

    precn_t expr = precn_divexact_3(precn_divexact_3(pow10 - precn_t(1)));
    expect_eq(expr, repunit);
    if(print) print_dec(expr);
}

static void test_repunit_1000(){
    test_repunit_1000_with(mul_op, 1);
    test_repunit_1000_with(mul_karatsuba, 0);
    test_repunit_1000_with(mul_toom, 0);
    test_repunit_1000_with(mul_ntt, 0);
}

static void expect_all_mul_eq(size_t an, size_t bn, uint32_t seed){
    precn_t a = pattern(an, seed);
    precn_t b = pattern(bn, seed + 1009);
    precn_t ref = a * b;

    expect_eq(mul_basic(a, b), ref);
    expect_eq(mul_karatsuba(a, b), ref);
    expect_eq(mul_toom(a, b), ref);
    expect_eq(mul_toom23(a, b), ref);
    expect_eq(mul_toom24(a, b), ref);
    expect_eq(mul_toom33(a, b), ref);
    expect_eq(mul_fft(a, b), ref);
    expect_eq(mul_ntt(a, b), ref);
}

static void test_mul_algorithms(){
    precn_t small_a = pattern(10, 11);
    precn_t small_b = pattern(9, 19);
    precn_t large_a = pattern(36, 23);
    precn_t large_b = pattern(31, 29);
    precn_t wide_b = pattern(70, 31);

    expect_eq(mul_karatsuba(small_a, small_b), small_a * small_b);
    expect_eq(mul_karatsuba(large_a, large_b), large_a * large_b);

    expect_eq(mul_toom23(large_a, large_b), large_a * large_b);
    expect_eq(mul_toom33(large_a, large_b), large_a * large_b);
    expect_eq(mul_toom24(large_a, wide_b), large_a * wide_b);
    expect_eq(mul_toom(large_a, large_b), large_a * large_b);
    expect_eq(mul_toom(large_a, wide_b), large_a * wide_b);
    expect_eq(mul_fft(large_a, large_b), large_a * large_b);
    expect_eq(mul_fft(large_a, wide_b), large_a * wide_b);
    expect_eq(mul_ntt(large_a, large_b), large_a * large_b);
    expect_eq(mul_ntt(large_a, wide_b), large_a * wide_b);

    size_t bases[] = {32, 128, 512, 2048};
    for(size_t i = 0; i < sizeof(bases) / sizeof(bases[0]); ++i){
        size_t n = bases[i];
        expect_all_mul_eq(n, n, (uint32_t)(3000 + i));
        expect_all_mul_eq(n, n + n / 4, (uint32_t)(3100 + i));
        expect_all_mul_eq(n, n + n / 3, (uint32_t)(3150 + i));
        expect_all_mul_eq(n, n + n / 2, (uint32_t)(3200 + i));
        expect_all_mul_eq(n, n * 2, (uint32_t)(3300 + i));
        expect_all_mul_eq(n, n * 3, (uint32_t)(3400 + i));
    }

}

static void bench_balanced_size_row(const char *label, size_t limbs, size_t reps, int run_basic, uint32_t seed){
    precn_t a = pattern(limbs, seed);
    precn_t b = pattern(limbs, seed + 1000);

    precn_t basic;
    double basic_sec = 0.0;
    if(run_basic){
        bench_mul_result_t r = bench_mul_once(mul_basic, a, b, reps);
        basic = r.v;
        basic_sec = r.sec;
    }

    bench_mul_result_t kr = bench_mul_once(mul_karatsuba, a, b, reps);
    precn_t kara = kr.v;
    double kara_sec = kr.sec;
    if(run_basic) expect_eq_named("karatsuba/basic", kara, basic);

    bench_mul_result_t tr = bench_mul_once(mul_toom, a, b, reps);
    precn_t toom = tr.v;
    double toom_sec = tr.sec;
    expect_eq_named(run_basic ? "toom/basic" : "toom/karatsuba", toom, run_basic ? basic : kara);

    bench_mul_result_t fr = bench_mul_once(mul_fft, a, b, reps);
    precn_t fft = fr.v;
    double fft_sec = fr.sec;
    expect_eq_named(run_basic ? "fft/basic" : "fft/karatsuba", fft, run_basic ? basic : kara);

    bench_mul_result_t nr = bench_mul_once(mul_ntt, a, b, reps);
    precn_t ntt = nr.v;
    double ntt_sec = nr.sec;
    expect_eq_named(run_basic ? "ntt/basic" : "ntt/karatsuba", ntt, run_basic ? basic : kara);

    if(run_basic){
        printf("%-8s %-8zu %-6zu %-12.6f %-12.6f %-12.6f %-12.6f %-12.6f %-12zu\n",
               label, limbs, reps, basic_sec, kara_sec, toom_sec, fft_sec, ntt_sec, basic.rsiz);
    }else{
        printf("%-8s %-8zu %-6zu %-12s %-12.6f %-12.6f %-12.6f %-12.6f %-12zu\n",
               label, limbs, reps, "-", kara_sec, toom_sec, fft_sec, ntt_sec, kara.rsiz);
    }
}

static void bench_mul_sizes(){
    puts("mul timing");
    printf("%-8s %-8s %-6s %-12s %-12s %-12s %-12s %-12s %-12s\n", "n", "limbs", "reps", "basic", "karatsuba", "toom", "fft", "ntt", "result");
    const size_t basic_limit_n = 16;
    const size_t max_n = 20;
    const size_t small_extra_limit_n = 15;
    for(size_t n = 0; n <= max_n; ++n){
        size_t limbs = (size_t)1 << n;
        size_t reps = bench_reps_for_n(n);
        char label[16];
        snprintf(label, sizeof(label), "2^%zu", n);
        bench_balanced_size_row(label, limbs, reps, n <= basic_limit_n, (uint32_t)(100 + n));

        if(n > 0 && n <= small_extra_limit_n){
            snprintf(label, sizeof(label), "1.5*2^%zu", n);
            bench_balanced_size_row(label, limbs + limbs / 2, reps, 1, (uint32_t)(9000 + n));
        }
    }
}

static void bench_unbalanced_sizes(){
    puts("unbalanced mul timing");
    printf("%-8s %-10s %-8s %-12s %-12s %-12s %-12s %-12s %-12s\n",
           "ratio", "a", "b", "basic", "karatsuba", "toom", "fft", "ntt", "result");

    const char *names[] = {"1.25x", "1.333x", "1.5x", "2x", "3x"};
    size_t bases[] = {640, 768, 1024, 1280, 1536, 2048, 2560, 4096, 8192, 16384};

    for(size_t bi = 0; bi < sizeof(bases) / sizeof(bases[0]); ++bi){
        size_t base = bases[bi];
        size_t bs[] = {base + base / 4, base + base / 3, base + base / 2, base * 2, base * 3};
        for(size_t i = 0; i < sizeof(bs) / sizeof(bs[0]); ++i){
            precn_t a = pattern(base, (uint32_t)(5000 + bi * 17 + i));
            precn_t b = pattern(bs[i], (uint32_t)(6000 + bi * 17 + i));

            clock_t start = clock();
            precn_t basic = mul_basic(a, b);
            double basic_sec = (double)(clock() - start) / CLOCKS_PER_SEC;

            start = clock();
            precn_t kara = mul_karatsuba(a, b);
            double kara_sec = (double)(clock() - start) / CLOCKS_PER_SEC;
            expect_eq(kara, basic);

            start = clock();
            precn_t toom = mul_toom(a, b);
            double toom_sec = (double)(clock() - start) / CLOCKS_PER_SEC;
            expect_eq(toom, basic);

            start = clock();
            precn_t fft = mul_fft(a, b);
            double fft_sec = (double)(clock() - start) / CLOCKS_PER_SEC;
            expect_eq(fft, basic);

            start = clock();
            precn_t ntt = mul_ntt(a, b);
            double ntt_sec = (double)(clock() - start) / CLOCKS_PER_SEC;
            expect_eq(ntt, basic);

            printf("%-8s %-10zu %-8zu %-12.6f %-12.6f %-12.6f %-12.6f %-12.6f %-12zu\n",
                   names[i], base, bs[i], basic_sec, kara_sec, toom_sec, fft_sec, ntt_sec, basic.rsiz);
        }
    }
}

int main(){
    clock_t start = clock();
    test_init();
    test_add_sub();
    test_mul_u32();
    test_mul_basic();
    test_divexact();
    test_repunit_1000();
    test_mul_algorithms();
    puts("ok");
    printf("time %.3f sec\n", (double)(clock() - start) / CLOCKS_PER_SEC);
    bench_mul_sizes();
    bench_unbalanced_sizes();
    return 0;
}
