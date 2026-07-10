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
    std::vector<uint32_t> digits(a.rsiz * 10 + 1);
    size_t n = 0;
    precn_base_convert(a, 10, digits.data(), n);
    if(n == 0){
        puts("0");
        return;
    }

    for(size_t i = n; i > 0; --i) putchar((char)('0' + digits[i - 1]));
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

static precn_t power_of_two(size_t bit){
    precn_t r;
    r.asiz = bit / 32 + 1;
    r.a = (uint32_t*) realloc(r.a, r.asiz * 4);
    memset(r.a, 0, r.asiz * 4);
    r.a[bit / 32] = (uint32_t)1u << (bit % 32);
    r.rsiz = r.asiz;
    return r;
}

static void test_init(){
    expect(precn_t(), {});
    expect(precn_t(0), {});
    expect(precn_t(1), {1});
    expect(precn_t(-7), {});
    expect(precn_t(0x100000000ULL), {0, 1});
    expect(precn_t(std::string("4294967296")), {0, 1});
    expect(precn_t(std::string("12a34")), {1234});
}

static void test_compare_shift(){
    precn_t z;
    precn_t one(1);
    precn_t two(2);
    precn_t big = make_prec({0, 1});

    assert(z == precn_t());
    assert(one != two);
    assert(one < two);
    assert(two > one);
    assert(one <= one);
    assert(one >= one);
    assert(big > make_prec({0xFFFFFFFFu}));

    expect(one << 0, {1});
    expect(one << 1, {2});
    expect(one << 32, {0, 1});
    expect(one << 65, {0, 0, 2});
    expect(make_prec({0x80000000u}) << 1, {0, 1});
    expect(make_prec({0xFFFFFFFFu}) << 4, {0xFFFFFFF0u, 15});

    expect(make_prec({0, 1}) >> 0, {0, 1});
    expect(make_prec({0, 1}) >> 1, {0x80000000u});
    expect(make_prec({0, 0, 2}) >> 65, {1});
    expect(make_prec({0xFFFFFFF0u, 15}) >> 4, {0xFFFFFFFFu});
    expect(one >> 1, {});
    expect(z << 100, {});
    expect(z >> 100, {});
}

static void test_base_convert(){
    size_t n = 99;
    precn_base_convert(precn_t(), 10, nullptr, n);
    assert(n == 0);
    precn_base_convert(precn_t(123), 1, nullptr, n);
    assert(n == 0);

    precn_t h = make_prec({0x89ABCDEFu, 0x01234567u});
    std::vector<uint32_t> out(128);
    precn_base_convert(h, 16, out.data(), n);
    std::vector<uint32_t> hex_expect = {15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1};
    assert(n == hex_expect.size());
    for(size_t i = 0; i < n; ++i) assert(out[i] == hex_expect[i]);

    uint32_t bases[] = {2u, 10u, 16u, 1000u, 1000000000u, 0xFFFFFFFFu};
    precn_t a = pattern(96, 909);
    for(size_t bi = 0; bi < sizeof(bases) / sizeof(bases[0]); ++bi){
        uint32_t base = bases[bi];
        precn_base_convert(a, base, nullptr, n);
        out.assign(n + 1, 0);
        precn_base_convert(a, base, out.data(), n);

        precn_t r;
        for(size_t i = n; i > 0; --i){
            assert(out[i - 1] < base);
            r = mul_u32(r, base) + precn_t(out[i - 1]);
        }
        expect_eq(r, a);
    }

    precn_t sparse(1);
    for(size_t i = 0; i < 32; ++i) sparse = mul_u32(sparse, 1000000000u);
    sparse = sparse + precn_t(12345);
    precn_base_convert(sparse, 10, nullptr, n);
    out.assign(n + 1, 0);
    precn_base_convert(sparse, 10, out.data(), n);
    precn_t r;
    for(size_t i = n; i > 0; --i) r = mul_u32(r, 10) + precn_t(out[i - 1]);
    expect_eq(r, sparse);
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
    expect(mul_ssa(make_prec({0xFFFFFFFFu}), make_prec({0xFFFFFFFFu})), {1, 0xFFFFFFFEu});
    expect_eq(mul_ssa(a, b), a * b);
}

static void test_divexact(){
    expect(precn_divexact_2(make_prec({0, 2})), {0, 1});
    expect(precn_divexact_3(make_prec({3, 3})), {1, 1});
}

static void test_division(){
    expect(div_u32(make_prec({0xFFFFFFFFu, 0xFFFFFFFFu}), 2),
           {0xFFFFFFFFu, 0x7FFFFFFFu});
    expect(div_u32(make_prec({123, 456}), 0), {});
    expect(mod_u32(make_prec({0xFFFFFFFFu, 0xFFFFFFFFu}), 2), {1});
    expect(mod_u32(make_prec({123, 456}), 0), {});
    expect(precn_t(7) / precn_t(3), {2});
    expect(precn_t(7) % precn_t(3), {1});
    expect(precn_t(3) / precn_t(7), {});
    expect(precn_t(3) % precn_t(7), {3});
    expect(precn_t(9) / precn_t(9), {1});
    expect(precn_t(9) % precn_t(9), {});
    expect(precn_t(9) / precn_t(), {});
    expect(precn_t(9) % precn_t(), {});
    precn_t into_q;
    precn_t into_r;
    div_into(into_q, make_prec({0xFFFFFFFFu, 0xFFFFFFFFu}), make_prec({2}));
    mod_into(into_r, make_prec({0xFFFFFFFFu, 0xFFFFFFFFu}), make_prec({2}));
    expect(into_q, {0xFFFFFFFFu, 0x7FFFFFFFu});
    expect(into_r, {1});

    precn_t q1 = pattern(7, 501);
    precn_t d1 = make_prec({0x89ABCDEFu, 1u});
    precn_t p1 = mul_basic(q1, d1);
    expect_eq(p1 / d1, q1);
    expect_eq((p1 + (d1 - precn_t(1))) % d1, d1 - precn_t(1));
    expect_eq((p1 + (d1 - precn_t(1))) / d1, q1);
    into_q = p1 + (d1 - precn_t(1));
    div_into(into_q, into_q, d1);
    expect_eq(into_q, q1);
    into_r = p1 + (d1 - precn_t(1));
    mod_into(into_r, into_r, d1);
    expect_eq(into_r, d1 - precn_t(1));

    precn_t q2 = pattern(9, 701);
    precn_t d2 = make_prec({0x10203040u, 0xF1234567u});
    precn_t p2 = mul_basic(q2, d2);
    expect_eq(p2 / d2, q2);
    expect_eq((p2 + (d2 - precn_t(1))) % d2, d2 - precn_t(1));
    expect_eq((p2 + (d2 - precn_t(1))) / d2, q2);

    expect(precn_reciprocal_newton(precn_t(3), 8), {85});
    expect(precn_reciprocal_newton(precn_t(5), 3), {1});
    expect(precn_reciprocal_newton(precn_t(9), 3), {});
    expect(precn_reciprocal_newton(precn_t(), 128), {});
    expect(div_newton(precn_t(7), precn_t(3)), {2});
    expect(div_newton(precn_t(3), precn_t(7)), {});
    expect(div_newton(precn_t(9), precn_t()), {});
    expect_eq(div_mulinv(p1, d1), q1);
    expect_eq(mod_mulinv(p1 + (d1 - precn_t(1)), d1), d1 - precn_t(1));
    expect_eq(div_newton(p1, d1), q1);
    expect_eq(div_newton(p1 + (d1 - precn_t(1)), d1), q1);
    expect_eq(div_newton(p2, d2), q2);
    expect_eq(div_newton(p2 + (d2 - precn_t(1)), d2), q2);

    precn_t large_a = pattern(80, 811);
    precn_t large_b = pattern(40, 821);
    expect_eq(precn_reciprocal_newton(large_b, 4096), power_of_two(4096) / large_b);
    expect_eq(div_newton(large_a, large_b), large_a / large_b);
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

static size_t bench_reps_for_limbs(size_t limbs){
    if(limbs < 256) return 100000;
    if(limbs <= 1024) return 100;
    if(limbs <= 32768) return 10;
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
    if(an + bn <= 1024) expect_eq(mul_ssa(a, b), ref);
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
    expect_eq(mul_ssa(large_a, large_b), large_a * large_b);
    expect_eq(mul_ssa(large_a, wide_b), large_a * wide_b);

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

    bench_mul_result_t sr = bench_mul_once(mul_ssa, a, b, 1);
    precn_t ssa = sr.v;
    double ssa_sec = sr.sec;
    expect_eq_named(run_basic ? "ssa/basic" : "ssa/karatsuba", ssa, run_basic ? basic : kara);

    if(run_basic){
        printf("%-8s %-8zu %-6zu %-15.9f %-15.9f %-15.9f %-15.9f %-15.9f %-15.9f %-12zu\n",
               label, limbs, reps, basic_sec, kara_sec, toom_sec, fft_sec, ntt_sec, ssa_sec, basic.rsiz);
    }else{
        printf("%-8s %-8zu %-6zu %-15s %-15.9f %-15.9f %-15.9f %-15.9f %-15.9f %-12zu\n",
               label, limbs, reps, "-", kara_sec, toom_sec, fft_sec, ntt_sec, ssa_sec, kara.rsiz);
    }
}

static void bench_mul_sizes(){
    puts("mul timing");
    printf("%-8s %-8s %-6s %-15s %-15s %-15s %-15s %-15s %-15s %-12s\n", "n", "limbs", "reps", "basic", "karatsuba", "toom", "fft", "ntt", "ssa", "result");
    const size_t basic_limit_n = 16;
    const size_t max_n = 20;
    const size_t small_extra_limit_n = 15;
    for(size_t n = 0; n <= max_n; ++n){
        size_t limbs = (size_t)1 << n;
        size_t reps = bench_reps_for_limbs(limbs);
        char label[16];
        snprintf(label, sizeof(label), "2^%zu", n);
        bench_balanced_size_row(label, limbs, reps, n <= basic_limit_n, (uint32_t)(100 + n));

        if(n > 0 && n <= small_extra_limit_n){
            snprintf(label, sizeof(label), "1.5*2^%zu", n);
            bench_balanced_size_row(label, limbs + limbs / 2, bench_reps_for_limbs(limbs + limbs / 2), 1, (uint32_t)(9000 + n));
        }
    }
}

static void bench_unbalanced_sizes(){
    puts("unbalanced mul timing");
    printf("%-8s %-10s %-8s %-15s %-15s %-15s %-15s %-15s %-15s %-12s\n",
           "ratio", "a", "b", "basic", "karatsuba", "toom", "fft", "ntt", "ssa", "result");

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

            start = clock();
            precn_t ssa = mul_ssa(a, b);
            double ssa_sec = (double)(clock() - start) / CLOCKS_PER_SEC;
            expect_eq(ssa, basic);

            printf("%-8s %-10zu %-8zu %-15.9f %-15.9f %-15.9f %-15.9f %-15.9f %-15.9f %-12zu\n",
                   names[i], base, bs[i], basic_sec, kara_sec, toom_sec, fft_sec, ntt_sec, ssa_sec, basic.rsiz);
        }
    }
}

typedef precn_t (*div_fn_t)(const precn_t&, const precn_t&);

static precn_t div_schoolbook_op(const precn_t &a, const precn_t &b){
    return ::div_schoolbook(a, b);
}

static bench_mul_result_t bench_div_once(div_fn_t div, const precn_t &a, const precn_t &b, size_t reps){
    clock_t start = clock();
    clock_t end = start;
    precn_t r;
    for(size_t i = 0; i < reps; ++i){
        precn_t t = div(a, b);
        if(i + 1 == reps){
            end = clock();
            r = t;
        }
    }
    return bench_mul_result_t{r, (double)(end - start) / CLOCKS_PER_SEC / reps};
}

static size_t bench_div_reps_for_limbs(size_t limbs){
    if(limbs < 256) return 100000;
    if(limbs <= 1024) return 10;
    return 1;
}

static void bench_div_sizes(){
    puts("division timing");
    printf("%-8s %-10s %-10s %-6s %-15s %-15s %-12s\n",
           "n", "dividend", "divisor", "reps", "schoolbook", "mulinv", "result");

    const size_t max_n = 18;
    for(size_t n = 0; n <= max_n; ++n){
        size_t limbs = (size_t)1 << n;
        size_t reps = bench_div_reps_for_limbs(limbs);
        precn_t divisor = pattern(limbs, (uint32_t)(12000 + n));
        precn_t quotient = pattern(limbs, (uint32_t)(13000 + n));
        precn_t dividend = divisor * quotient + (divisor - precn_t(1));

        precn_t schoolbook;
        double schoolbook_sec = 0.0;
        bench_mul_result_t sr = bench_div_once(div_schoolbook_op, dividend, divisor, reps);
        schoolbook = sr.v;
        schoolbook_sec = sr.sec;
        expect_eq_named("division schoolbook", schoolbook, quotient);

        bench_mul_result_t nr = bench_div_once(div_mulinv, dividend, divisor, reps);
        precn_t mulinv = nr.v;
        expect_eq_named("division mulinv", mulinv, quotient);
        expect_eq_named("mulinv/schoolbook", mulinv, schoolbook);

        char label[16];
        snprintf(label, sizeof(label), "2^%zu", n);
        printf("%-8s %-10zu %-10zu %-6zu %-15.9f %-15.9f %-12zu\n",
               label, dividend.rsiz, divisor.rsiz, reps, schoolbook_sec, nr.sec, mulinv.rsiz);
        fflush(stdout);
    }
}

int main(int argc, char **argv){
    if(argc > 1 && strcmp(argv[1], "--division-timing") == 0){
        bench_div_sizes();
        return 0;
    }

    clock_t start = clock();
    test_init();
    test_compare_shift();
    test_base_convert();
    test_add_sub();
    test_mul_u32();
    test_mul_basic();
    test_divexact();
    test_division();
    test_repunit_1000();
    test_mul_algorithms();
    puts("ok");
    printf("time %.9f sec\n", (double)(clock() - start) / CLOCKS_PER_SEC);
    bench_mul_sizes();
    bench_unbalanced_sizes();
    bench_div_sizes();
    return 0;
}
