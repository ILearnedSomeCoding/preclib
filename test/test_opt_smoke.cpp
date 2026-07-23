#include"../prec.hpp"

#include<cassert>
#include<cstdio>
#include<string>
#include<vector>

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

static void same(const precn_t &a, const precn_t &b){
    assert(a.rsiz == b.rsiz);
    for(size_t i = 0; i < a.rsiz; ++i) assert(a.a[i] == b.a[i]);
}

int main(){
    size_t sizes[] = {1, 2, 3, 16, 24, 25, 63, 64, 65, 127, 193};
    for(size_t i = 0; i < sizeof(sizes) / sizeof(sizes[0]); ++i){
        precn_t a = pattern(sizes[i], 100 + i);
        same(precn_sqr(a), mul_basic(a, a));
        same(a * a, mul_basic(a, a));
    }

    size_t short_sizes[] = {1, 2, 24, 25, 64, 100, 193};
    for(size_t i = 0; i < sizeof(short_sizes) / sizeof(short_sizes[0]); ++i){
        precn_t a = pattern(short_sizes[i] * 5 + 3, 400 + i);
        precn_t b = pattern(short_sizes[i], 500 + i);
        same(a * b, mul_basic(a, b));
    }

    size_t toom_sizes[] = {64, 96, 128, 192};
    for(size_t i = 0; i < sizeof(toom_sizes) / sizeof(toom_sizes[0]); ++i){
        precn_t a = pattern(toom_sizes[i], 600 + i);
        precn_t b = pattern(toom_sizes[i] - 3, 700 + i);
        same(mul_toom(a, b), mul_basic(a, b));
    }

    precn_t fft_a = pattern(2049, 750);
    precn_t fft_b = pattern(2039, 760);
    same(mul_fft(fft_a, fft_b), mul_basic(fft_a, fft_b));

    for(size_t i = 1; i <= 257; ++i){
        precn_t a = pattern(i, 800 + i);
        same(precn_divexact_3(mul_u64(a, 3)), a);

        uint32_t d = (uint32_t)(1000000007u + i);
        precn_t q = pattern(i, 1200 + i);
        precn_t rem((uint64_t)(i % d));
        precn_t n = mul_u64(q, d) + rem;
        same(n / d, q);
        same(n % d, rem);
    }

    uint64_t wide_divisors[] = {
        0x1000000000000001ULL,
        0xFEDCBA9876543211ULL,
        UINT64_MAX
    };
    for(size_t i = 0; i < sizeof(wide_divisors) / sizeof(wide_divisors[0]); ++i){
        precn_t q = pattern(80 + i, 1600 + i);
        precn_t rem(wide_divisors[i] - 1);
        precn_t n = mul_u64(q, wide_divisors[i]) + rem;
        same(n / wide_divisors[i], q);
        same(n % wide_divisors[i], rem);
    }

    size_t div_sizes[] = {2, 3, 16, 65};
    for(size_t i = 0; i < sizeof(div_sizes) / sizeof(div_sizes[0]); ++i){
        precn_t b = pattern(div_sizes[i], 2000 + i);
        precn_t q = pattern(div_sizes[i] + 4, 2100 + i);
        precn_t n = mul_basic(q, b) + (b - 1);
        same(n / b, q);
        same(n % b, b - 1);
    }

    size_t dc_sizes[] = {256, 257, 383, 512, 777, 1024, 2048};
    uint64_t dc_tops[] = {1, 0x8000000000000001ULL, UINT64_MAX};
    for(size_t i = 0; i < sizeof(dc_sizes) / sizeof(dc_sizes[0]); ++i){
        for(size_t j = 0; j < sizeof(dc_tops) / sizeof(dc_tops[0]); ++j){
            precn_t b = pattern(dc_sizes[i], 2200 + i * 10 + j);
            precn_t q = pattern(dc_sizes[i], 2300 + i * 10 + j);
            b.a[b.rsiz - 1] = dc_tops[j];
            precn_t rem = b - precn_t(1);
            precn_t n = b * q + rem;
            precn_t got_q, got_r;
            divmod_into(got_q, got_r, n, b);
            same(got_q, q);
            same(got_r, rem);
            same(n / b, q);
            same(n % b, rem);
        }
    }

    for(size_t i = 0; i < 96; ++i){
        precn_t root = pattern(i + 1, 2400 + i);
        precn_t square = root * root;
        same(precn_sqrt(square), root);
        same(precn_sqrt(square + root), root);
        same(precn_sqrt(square + root + root + 1), root + 1);
    }

    precn_t common = pattern(32, 2800);
    precn_t factor = pattern(48, 2801);
    same(gcd(common * factor, common * (factor + 1)), common);

    precn_t converted = pattern(257, 3001);
    size_t digit_count = 0;
    precn_base_convert(converted, 10, nullptr, digit_count);
    std::vector<uint32_t> digits(digit_count);
    precn_base_convert(converted, 10, digits.data(), digit_count);
    precn_t rebuilt;
    for(size_t i = digit_count; i > 0; --i) rebuilt = rebuilt * 10 + digits[i - 1];
    same(rebuilt, converted);
    same(precn_t((std::string)converted), converted);

    puts("ok");
    return 0;
}
