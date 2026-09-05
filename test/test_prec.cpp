#include"../prec.hpp"

#include<cassert>
#include<cstdio>
#include<ctime>
#include<vector>

static precn_t make_prec(const std::vector<uint32_t> &v){
    precn_t r;
    r.asiz = std::max<size_t>((v.size() + 1) / 2, 1);
    r.a = (uint64_t*) realloc(r.a, r.asiz * sizeof(uint64_t));
    memset(r.a, 0, r.asiz * sizeof(uint64_t));
    r.rsiz = (v.size() + 1) / 2;
    for(size_t i = 0; i < v.size(); ++i){
        r.a[i / 2] |= (uint64_t)v[i] << ((i & 1) * 32);
    }
    while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}

static void expect(const precn_t &a, const std::vector<uint32_t> &v){
    size_t n = v.size();
    while(n > 0 && v[n - 1] == 0) --n;
    assert(a.rsiz == (n + 1) / 2);
    for(size_t i = 0; i < n; ++i){
        assert((uint32_t)(a.a[i / 2] >> ((i & 1) * 32)) == v[i]);
    }
}

static void expect_eq_named(const char *name, const precn_t &a, const precn_t &b){
    if(a.rsiz != b.rsiz){
        printf("%s size mismatch: %zu != %zu\n", name, a.rsiz, b.rsiz);
        assert(a.rsiz == b.rsiz);
    }
    for(size_t i = 0; i < a.rsiz; ++i){
        if(a.a[i] != b.a[i]){
            printf("%s limb mismatch at %zu: %016llx != %016llx\n", name, i,
                   (unsigned long long)a.a[i], (unsigned long long)b.a[i]);
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
    r.a = (uint64_t*) realloc(r.a, r.asiz * sizeof(uint64_t));
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
    r.asiz = bit / 64 + 1;
    r.a = (uint64_t*) realloc(r.a, r.asiz * sizeof(uint64_t));
    memset(r.a, 0, r.asiz * sizeof(uint64_t));
    r.a[bit / 64] = (uint64_t)1 << (bit % 64);
    r.rsiz = r.asiz;
    return r;
}

static void test_init(){
    expect(precn_t(), {});
    expect(precn_t(0), {});
    expect(precn_t(1), {1});
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
    precn_t powers = pattern(17, 457);
    expect_eq(mul_u64(powers, 1), powers);
    expect_eq(mul_u64(powers, 8), powers << 3);
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

    precn_t square;
    const size_t square_sizes[] = {1, 2, 4, 8, 16, 32, 64, 96, 128, 192, 2560, 3072};
    for(size_t n : square_sizes){
        precn_t x = pattern(n, 900 + n);
        precn_sqr_into(square, x);
        expect_eq_named("sqr_into", square, mul_basic(x, x));
    }
    precn_t square_carry = pattern(232, 1199);
    for(size_t i = 0; i < square_carry.rsiz; ++i)
        square_carry.a[i] = UINT64_MAX;
    precn_sqr_into(square, square_carry);
    expect_eq_named("sqr_into carry", square,
                    mul_basic(square_carry, square_carry));
}

static void test_mul_ntt_shared_right(){
    precn_t a = pattern(257, 1201);
    precn_t c = pattern(301, 1207);
    precn_t b = pattern(263, 1213);
    precn_t ab;
    precn_t cb;
    assert(mul_ntt_pair_shared_right_into(ab, cb, a, c, b));
    expect_eq_named("shared-right ntt first", ab, mul_basic(a, b));
    expect_eq_named("shared-right ntt second", cb, mul_basic(c, b));
}
static void test_mul_low_zero_limbs(){
    precn_t a = pattern(260, 701);
    precn_t b = pattern(230, 709);
    precn_t shifted_a = a << (37 * 64);
    precn_t shifted_b = b << (23 * 64);

    expect_eq_named("low-zero mul", shifted_a * shifted_b,
                    (a * b) << (60 * 64));
    expect_eq_named("low-zero square", precn_sqr(shifted_a),
                    precn_sqr(a) << (74 * 64));
}

static void test_mul_high(){
    const size_t cases[][3] = {
        {1025, 2051, 2050},
        {2049, 4099, 4098},
        {4097, 8195, 8194},
        {257, 901, 700},
        {901, 257, 700},
        {700, 700, 417},
        {700, 700, 1000},
        {901, 700, 1100},
        {700, 901, 1100},
    };
    for(size_t i = 0; i < sizeof(cases) / sizeof(cases[0]); ++i){
        precn_t a = pattern(cases[i][0], (uint64_t)(1301 + i));
        precn_t b = pattern(cases[i][1], (uint64_t)(1701 + i));
        precn_t reference = (a * b) >> (cases[i][2] * 64);
        expect_eq(mul_high(a, b, cases[i][2]), reference);
    }
}

static void test_divexact(){
    expect(precn_divexact_2(make_prec({0, 2})), {0, 1});
    expect(precn_divexact_3(make_prec({3, 3})), {1, 1});

    const size_t sizes[] = {1, 3, 32, 100, 257};
    for(size_t i = 0; i < sizeof(sizes) / sizeof(sizes[0]); ++i){
        precn_t divisor = pattern(sizes[i], (uint32_t)(101 + i));
        divisor.a[0] |= 1;
        precn_t quotient = pattern(sizes[i] + 7, (uint32_t)(211 + i));
        expect_eq(precn_divexact(divisor * quotient, divisor), quotient);

        precn_t even_divisor = divisor << 137;
        expect_eq(precn_divexact(even_divisor * quotient, even_divisor), quotient);
    }

    precn_t unbalanced_divisor = pattern(64, 307);
    unbalanced_divisor.a[0] |= 1;
    precn_t unbalanced_quotient = pattern(200, 401);
    expect_eq(precn_divexact(unbalanced_divisor * unbalanced_quotient,
                            unbalanced_divisor), unbalanced_quotient);
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
    precn_t power_dividend = pattern(17, 493);
    expect_eq(div_u64(power_dividend, 1), power_dividend);
    expect_eq(div_u64(power_dividend, 8), power_dividend >> 3);
    expect_eq(mod_u64(power_dividend, 8), precn_t(power_dividend.a[0] & 7));
    precn_t into_q;
    precn_t into_r;
    div_into(into_q, make_prec({0xFFFFFFFFu, 0xFFFFFFFFu}), make_prec({2}));
    mod_into(into_r, make_prec({0xFFFFFFFFu, 0xFFFFFFFFu}), make_prec({2}));
    expect(into_q, {0xFFFFFFFFu, 0x7FFFFFFFu});
    expect(into_r, {1});
    into_q = power_dividend;
    div_into(into_q, into_q, precn_t(8));
    expect_eq(into_q, power_dividend >> 3);
    into_r = power_dividend;
    mod_into(into_r, into_r, precn_t(8));
    expect_eq(into_r, precn_t(power_dividend.a[0] & 7));

    precn_t fixed_dividend = pattern(257, 497);
    precn_t fixed_expected = div_u64(fixed_dividend, 10000000000ULL);
    precn_t fixed_quotient;
    precn_div_1e10_into(fixed_quotient, fixed_dividend);
    expect_eq(fixed_quotient, fixed_expected);
    fixed_quotient = fixed_dividend;
    precn_div_1e10_into(fixed_quotient, fixed_quotient);
    expect_eq(fixed_quotient, fixed_expected);

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
    expect(div_mulinv(precn_t(7), precn_t(3)), {2});
    expect(div_mulinv(precn_t(3), precn_t(7)), {});
    expect(div_mulinv(precn_t(9), precn_t()), {});
    expect_eq(div_mulinv(p1, d1), q1);
    expect_eq(mod_mulinv(p1 + (d1 - precn_t(1)), d1), d1 - precn_t(1));
    expect_eq(div_mulinv(p1, d1), q1);
    expect_eq(div_mulinv(p1 + (d1 - precn_t(1)), d1), q1);
    expect_eq(div_mulinv(p2, d2), q2);
    expect_eq(div_mulinv(p2 + (d2 - precn_t(1)), d2), q2);

    precn_t large_a = pattern(80, 811);
    precn_t large_b = pattern(40, 821);
    expect_eq(precn_reciprocal_newton(large_b, 4096), power_of_two(4096) / large_b);
    expect_eq(div_mulinv(large_a, large_b), large_a / large_b);

    precn_t pair_d = pattern(128, 831);
    precn_t pair_qa = pattern(220, 839);
    precn_t pair_qc = pattern(173, 853);
    precn_t got_qa, got_qc;
    div_mulinv_pair_into(got_qa, got_qc,
                         pair_d * pair_qa, pair_d * pair_qc, pair_d);
    expect_eq(got_qa, pair_qa);
    expect_eq(got_qc, pair_qc);

    // Exercise the blocked long-quotient path just above the DC threshold.
    precn_t block_d = pattern(257, 901);
    const size_t quotient_sizes[] = {514, 771};
    for(size_t i = 0; i < 2; ++i){
        precn_t block_q = pattern(quotient_sizes[i], 911 + i);
        precn_t block_r = block_d - precn_t(1);
        precn_t block_a = block_d * block_q + block_r;
        precn_t got_q, got_r;
        divmod_into(got_q, got_r, block_a, block_d);
        expect_eq(got_q, block_q);
        expect_eq(got_r, block_r);
        expect_eq(block_a / block_d, block_q);
        expect_eq(block_a % block_d, block_r);
    }
}

static void test_gcd(){
    expect_eq(gcd(precn_t(), precn_t()), precn_t());
    expect_eq(gcd(precn_t(42), precn_t()), precn_t(42));
    expect_eq(gcd(precn_t(), precn_t(42)), precn_t(42));
    expect_eq(gcd(precn_t(48), precn_t(18)), precn_t(6));
    expect_eq(gcd(precn_t(18), precn_t(48)), precn_t(6));
    expect_eq(gcd(precn_t(17), precn_t(13)), precn_t(1));

    precn_t common = pattern(40, 1701);
    precn_t factor = pattern(70, 1702);
    precn_t a = common * factor;
    precn_t b = common * (factor + 1);
    expect_eq(gcd(a, b), common);
}

static void expect_z(const precz_t &a, const char *value){
    assert((std::string)a == std::string(value));
    if(a.is_zero()) assert(!a.is_negative());
}

static void test_signed(){
    expect_z(precz_t(), "0");
    expect_z(precz_t(0), "0");
    expect_z(precz_t(-0), "0");
    expect_z(precz_t(std::string("-0")), "0");
    expect_z(-precz_t(), "0");
    expect_z(precz_t(INT64_MIN), "-9223372036854775808");
    expect_z(precz_t(std::string("-12345678901234567890")),
             "-12345678901234567890");

    expect_z(precz_t(7) + precz_t(-3), "4");
    expect_z(precz_t(3) + precz_t(-7), "-4");
    expect_z(precz_t(-7) + precz_t(7), "0");
    expect_z(precz_t(-7) - precz_t(-3), "-4");
    expect_z(precz_t(-7) * precz_t(-3), "21");
    expect_z(precz_t(-7) * precz_t(0), "0");

    // Division truncates toward zero and remainder has the dividend's sign.
    expect_z(precz_t(-7) / precz_t(3), "-2");
    expect_z(precz_t(7) / precz_t(-3), "-2");
    expect_z(precz_t(-7) / precz_t(-3), "2");
    expect_z(precz_t(-7) % precz_t(3), "-1");
    expect_z(precz_t(7) % precz_t(-3), "1");
    expect_z(precz_t(-6) % precz_t(3), "0");
    expect_z(precz_t(-7) / precz_t(0), "0");
    expect_z(precz_t(-7) % precz_t(0), "0");

    for(int64_t a = -100; a <= 100; ++a){
        for(int64_t b = -100; b <= 100; ++b){
            if(b == 0) continue;
            precz_t za(a);
            precz_t zb(b);
            precz_t q = za / zb;
            precz_t r = za % zb;
            assert((int64_t)q == a / b);
            assert((int64_t)r == a % b);
            assert(q * zb + r == za);
            assert(abs(r) < abs(zb));
            assert(r.is_zero() || r.is_negative() == za.is_negative());
        }
    }

    expect_z(precz_t(-3) << 4, "-48");
    expect_z(precz_t(-3) >> 1, "-1");
    expect_z(precz_t(-1) >> 100, "0");
    assert(precz_t(-5) < precz_t(-3));
    assert(precz_t(-1) < precz_t(0));
    assert(precz_t(3) > precz_t(-3));

    precz_t x(-1);
    expect_z(++x, "0");
    expect_z(--x, "-1");
    expect_z(abs(precz_t(-42)), "42");
    expect_z(gcd(precz_t(-48), precz_t(18)), "6");
    expect_z(precz_sqrt(precz_t(81)), "9");
    expect_z(precz_sqrt(precz_t(-81)), "0");

    precz_t large_abs_a(std::string("123456789012345678901234567890"));
    precz_t large_abs_b(std::string("98765432109876543210"));
    for(int sa = 0; sa < 2; ++sa){
        for(int sb = 0; sb < 2; ++sb){
            precz_t large_a = sa ? -large_abs_a : large_abs_a;
            precz_t large_b = sb ? -large_abs_b : large_abs_b;
            precz_t q = large_a / large_b;
            precz_t r = large_a % large_b;
            assert(q * large_b + r == large_a);
            assert(abs(r) < abs(large_b));
            assert(r.is_zero() || r.is_negative() == large_a.is_negative());
            assert(q.is_zero() || q.is_negative() == (sa != sb));
        }
    }
    assert(!(-large_abs_a + large_abs_a).is_negative());
}

static void expect_q(const precq_t &a, const char *value){
    assert((std::string)a == std::string(value));
    assert(a.denominator().rsiz != 0);
    assert(gcd(a.numerator(), a.denominator()) == precn_t(1));
    if(a.is_zero()){
        assert(!a.is_negative());
        assert(a.numerator() == precn_t());
        assert(a.denominator() == precn_t(1));
    }
}

static void test_rational(){
    expect_q(precq_t(), "0/1");
    expect_q(precq_t(0), "0/1");
    expect_q(precq_t(precn_t(), precn_t(99), true), "0/1");
    expect_q(precq_t(precn_t(6), precn_t(8)), "3/4");
    expect_q(precq_t(precn_t(6), precn_t(8), true), "-3/4");
    expect_q(precq_t(std::string("-6/8")), "-3/4");
    expect_q(precq_t(std::string("-6/-8")), "3/4");
    expect_q(precq_t(precz_t(-12), precn_t(18)), "-2/3");

    precq_t a(precn_t(1), precn_t(2));
    precq_t b(precn_t(1), precn_t(3));
    expect_q(a + b, "5/6");
    expect_q(a - b, "1/6");
    expect_q(b - a, "-1/6");
    expect_q(-a + a, "0/1");
    expect_q(-precq_t(), "0/1");
    expect_q(precq_t(precn_t(6), precn_t(35)) *
             precq_t(precn_t(14), precn_t(15)), "4/25");
    expect_q(precq_t(precn_t(6), precn_t(35)) /
             precq_t(precn_t(14), precn_t(15)), "9/49");
    expect_q(precq_t(-2) * precq_t(0), "0/1");
    expect_q(reciprocal(precq_t(precn_t(2), precn_t(3), true)), "-3/2");
    expect_q(abs(precq_t(precn_t(2), precn_t(3), true)), "2/3");

    assert(precq_t(precn_t(1), precn_t(2)) ==
           precq_t(precn_t(2), precn_t(4)));
    assert(precq_t(-1) < precq_t(precn_t(-0), precn_t(1)));
    assert(precq_t(precn_t(2), precn_t(3)) >
           precq_t(precn_t(3), precn_t(5)));

    precq_t large_a(std::string("12345678901234567890/9876543210"));
    precq_t large_b(std::string("-112233445566778899/9988776655"));
    expect_q((large_a + large_b) - large_b,
             ((std::string)large_a).c_str());
    expect_q((large_a * large_b) / large_b,
             ((std::string)large_a).c_str());
}

static void test_sqrt_large(){
    const size_t sizes[] = {127, 256, 1024, 4096};
    for(size_t i = 0; i < sizeof(sizes) / sizeof(sizes[0]); ++i){
        precn_t root = pattern(sizes[i], (uint32_t)(17000 + i));
        precn_t square = root * root;
        expect_eq_named("sqrt square", precn_sqrt(square), root);
        expect_eq_named("sqrt below square", precn_sqrt(square - 1), root - 1);
        expect_eq_named("sqrt below next square",
                        precn_sqrt(square + root + root), root);
        expect_eq_named("sqrt next square",
                        precn_sqrt(square + root + root + 1), root + 1);
    }
}

static void expect_f(const precf_t &a, const char *value){
    assert((std::string)a == std::string(value));
}

static void test_fixed_point(){
    unsigned int old_digit = precf_digit;
    precf_digit = 8;

    precf_t a(std::string("1.25"));
    precf_t b(std::string("-0.5"));
    assert(a.precision() == 8);
    assert(a.scaled_integer() == precz_t(320));
    expect_f(precf_t(), "0");
    expect_f(precf_t(3), "3");
    expect_f(a + b, "0.75");
    expect_f(a - b, "1.75");
    expect_f(a * b, "-0.625");
    expect_f(precf_t(3) / precf_t(2), "1.5");
    expect_f(precf_t(1) / precf_t(3), "0.33203125");
    expect_f(-a, "-1.25");
    expect_f(abs(b), "0.5");
    assert(b < a);
    assert((precz_t)precf_t(std::string("-3.75")) == precz_t(-3));

    precf_t c(1);
    c += precf_t(std::string("0.5"));
    c *= precf_t(2);
    c /= precf_t(4);
    expect_f(c, "0.75");

    precf_digit = 16;
    precf_t higher(1);
    assert(higher.precision() == 16);
    assert(a.precision() == 8);

    precf_digit = old_digit;
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
    precn_t pow10 = pow_fast(precn_t(10), 1000, mul);
    precn_t repunit = pow_rep_fast(1000, mul).repunit;

    expect_eq_named("repunit identity", mul_u64(repunit, 9) + precn_t(1), pow10);
    if(print) print_dec(repunit);
}

static void test_repunit_1000(){
    test_repunit_1000_with(mul_basic, 1);
}

static void expect_all_mul_eq(size_t an, size_t bn, uint32_t seed){
    precn_t a = pattern(an, seed);
    precn_t b = pattern(bn, seed + 1009);
    precn_t ref = a * b;

    expect_eq_named("basic", mul_basic(a, b), ref);
    expect_eq_named("karatsuba", mul_karatsuba(a, b), ref);
    expect_eq_named("toom", mul_toom(a, b), ref);
    expect_eq_named("toom23", mul_toom23(a, b), ref);
    expect_eq_named("toom24", mul_toom24(a, b), ref);
    expect_eq_named("toom33", mul_toom33(a, b), ref);
    expect_eq_named("fft", mul_fft(a, b), ref);
    expect_eq_named("ntt", mul_ntt(a, b), ref);
    expect_eq_named("vst", mul_vst(a, b), ref);
    if(an + bn <= 1024) expect_eq_named("ssa", mul_ssa(a, b), ref);
}

static void test_mul_algorithms(){
    expect_eq_named("one-limb vst", mul_vst(precn_t(7), precn_t(11)),
                    precn_t(77));
    precn_t small_a = pattern(10, 11);
    precn_t small_b = pattern(9, 19);
    precn_t large_a = pattern(36, 23);
    precn_t large_b = pattern(31, 29);
    precn_t wide_b = pattern(70, 31);

    expect_eq_named("small karatsuba", mul_karatsuba(small_a, small_b), small_a * small_b);
    expect_eq_named("large karatsuba", mul_karatsuba(large_a, large_b), large_a * large_b);

    expect_eq_named("direct toom23", mul_toom23(large_a, large_b), large_a * large_b);
    expect_eq_named("direct toom33", mul_toom33(large_a, large_b), large_a * large_b);
    expect_eq_named("direct toom24", mul_toom24(large_a, wide_b), large_a * wide_b);
    expect_eq_named("direct toom", mul_toom(large_a, large_b), large_a * large_b);
    expect_eq_named("direct wide toom", mul_toom(large_a, wide_b), large_a * wide_b);
    expect_eq_named("direct fft", mul_fft(large_a, large_b), large_a * large_b);
    expect_eq_named("direct wide fft", mul_fft(large_a, wide_b), large_a * wide_b);
    expect_eq_named("direct ntt", mul_ntt(large_a, large_b), large_a * large_b);
    expect_eq_named("direct wide ntt", mul_ntt(large_a, wide_b), large_a * wide_b);
    expect_eq_named("direct vst", mul_vst(large_a, large_b), large_a * large_b);
    expect_eq_named("direct wide vst", mul_vst(large_a, wide_b), large_a * wide_b);
    expect_eq_named("direct ssa", mul_ssa(large_a, large_b), large_a * large_b);
    expect_eq_named("direct wide ssa", mul_ssa(large_a, wide_b), large_a * wide_b);

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

    const size_t karatsuba_edges[][2] = {
        {33, 33}, {47, 48}, {63, 64}, {64, 65}, {95, 127},
        {127, 128}, {128, 129}, {128, 256}, {191, 192},
        {193, 257}, {256, 320}, {256, 384}
    };
    for(size_t i = 0;
        i < sizeof(karatsuba_edges) / sizeof(karatsuba_edges[0]); ++i){
        precn_t a = pattern(karatsuba_edges[i][0], (uint32_t)(4100 + i));
        precn_t b = pattern(karatsuba_edges[i][1], (uint32_t)(4200 + i));
        expect_eq_named("karatsuba edge", mul_karatsuba(a, b),
                        mul_basic(a, b));
    }
    precn_t karatsuba_carry_a = pattern(129, 4301);
    precn_t karatsuba_carry_b = pattern(193, 4303);
    for(size_t i = 0; i < karatsuba_carry_a.rsiz; ++i)
        karatsuba_carry_a.a[i] = UINT64_MAX;
    for(size_t i = 0; i < karatsuba_carry_b.rsiz; ++i)
        karatsuba_carry_b.a[i] = UINT64_MAX;
    expect_eq_named("karatsuba carry",
                    mul_karatsuba(karatsuba_carry_a, karatsuba_carry_b),
                    mul_basic(karatsuba_carry_a, karatsuba_carry_b));
    precn_t karatsuba_expected = mul_basic(karatsuba_carry_a,
                                           karatsuba_carry_b);
    precn_t karatsuba_reused;
    mul_into(karatsuba_reused, karatsuba_carry_a, karatsuba_carry_b);
    expect_eq_named("karatsuba into", karatsuba_reused,
                    karatsuba_expected);
    mul_into(karatsuba_reused, karatsuba_carry_b, karatsuba_carry_a);
    expect_eq_named("karatsuba into reused", karatsuba_reused,
                    karatsuba_expected);
    precn_t karatsuba_alias_left = karatsuba_carry_a;
    mul_into(karatsuba_alias_left, karatsuba_alias_left,
             karatsuba_carry_b);
    expect_eq_named("karatsuba into left alias", karatsuba_alias_left,
                    karatsuba_expected);
    precn_t karatsuba_alias_right = karatsuba_carry_b;
    mul_into(karatsuba_alias_right, karatsuba_carry_a,
             karatsuba_alias_right);
    expect_eq_named("karatsuba into right alias", karatsuba_alias_right,
                    karatsuba_expected);

    precn_t vst_carry = pattern(513, 4401);
    for(size_t i = 0; i < vst_carry.rsiz; ++i) vst_carry.a[i] = UINT64_MAX;
    expect_eq_named("vst carry square", mul_vst(vst_carry, vst_carry),
                    mul_ntt(vst_carry, vst_carry));

    // This exceeds the old two-prime 16-bit range.  The larger packed primes
    // must keep it exact without doubling the transform through 15-bit digits.
    precn_t vst_large_mod_a = pattern(45000, 4409);
    precn_t vst_large_mod_b = pattern(45000, 4421);
    expect_eq_named("vst large packed primes",
                    mul_vst(vst_large_mod_a, vst_large_mod_b),
                    mul_ntt(vst_large_mod_a, vst_large_mod_b));

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

    bench_mul_result_t nr = bench_mul_once(mul_ntt, a, b, reps);
    precn_t ntt = nr.v;
    double ntt_sec = nr.sec;
    expect_eq_named(run_basic ? "ntt/basic" : "ntt/karatsuba", ntt, run_basic ? basic : kara);

    bench_mul_result_t fr = bench_mul_once(mul_fft, a, b, reps);
    precn_t fft = fr.v;
    double fft_sec = fr.sec;
    expect_eq_named(run_basic ? "fft/basic" : "fft/karatsuba", fft, run_basic ? basic : kara);

    bench_mul_result_t sr = bench_mul_once(mul_ssa, a, b, 1);
    precn_t ssa = sr.v;
    double ssa_sec = sr.sec;
    expect_eq_named(run_basic ? "ssa/basic" : "ssa/karatsuba", ssa, run_basic ? basic : kara);

    if(run_basic){
        printf("%-8s %-8zu %-6zu %-15.9f %-15.9f %-15.9f %-15.9f %-15.9f %-15.9f %-12zu\n",
               label, limbs, reps, basic_sec, kara_sec, toom_sec, ntt_sec, fft_sec, ssa_sec, basic.rsiz);
    }else{
        printf("%-8s %-8zu %-6zu %-15s %-15.9f %-15.9f %-15.9f %-15.9f %-15.9f %-12zu\n",
               label, limbs, reps, "-", kara_sec, toom_sec, ntt_sec, fft_sec, ssa_sec, kara.rsiz);
    }
}

static void bench_mul_sizes(){
    puts("mul timing");
    printf("%-8s %-8s %-6s %-15s %-15s %-15s %-15s %-15s %-15s %-12s\n", "n", "limbs", "reps", "basic", "karatsuba", "toom", "ntt", "fft", "ssa", "result");
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
           "ratio", "a", "b", "basic", "karatsuba", "toom", "ntt", "fft", "ssa", "result");

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
            precn_t ntt = mul_ntt(a, b);
            double ntt_sec = (double)(clock() - start) / CLOCKS_PER_SEC;
            expect_eq(ntt, basic);

            start = clock();
            precn_t fft = mul_fft(a, b);
            double fft_sec = (double)(clock() - start) / CLOCKS_PER_SEC;
            expect_eq(fft, basic);

            start = clock();
            precn_t ssa = mul_ssa(a, b);
            double ssa_sec = (double)(clock() - start) / CLOCKS_PER_SEC;
            expect_eq(ssa, basic);

            printf("%-8s %-10zu %-8zu %-15.9f %-15.9f %-15.9f %-15.9f %-15.9f %-15.9f %-12zu\n",
                   names[i], base, bs[i], basic_sec, kara_sec, toom_sec, ntt_sec, fft_sec, ssa_sec, basic.rsiz);
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
    test_mul_ntt_shared_right();
    test_divexact();
    test_division();
    test_gcd();
    test_mul_low_zero_limbs();
    test_mul_high();
    test_sqrt_large();
    test_signed();
    test_rational();
    test_fixed_point();
    test_mul_algorithms();
    puts("ok");
    printf("time %.9f sec\n", (double)(clock() - start) / CLOCKS_PER_SEC);
    if(argc > 1 && strcmp(argv[1], "--checks-only") == 0) return 0;
    bench_mul_sizes();
    bench_unbalanced_sizes();
    bench_div_sizes();
    return 0;
}
