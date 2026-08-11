/* Pi computation using Chudnovsky's algorithm.
 * Copyright 2002, 2005 Hanhong Xue (macroxue at yahoo dot com)
 * Slightly modified 2005 by Torbjorn Granlund to allow more than 2G
 * digits to be computed.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHORS "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 * IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * This preclib port replaces GMP mpz_t/mpf_t with precz_t and an integer
 * fixed-point final evaluation while retaining the original P/Q/G recurrence.
 */

#include"../prec.hpp"

#include<algorithm>
#include<chrono>
#include<cstdlib>
#include<fstream>
#include<iostream>
#include<string>
#include<utility>
#include<vector>

static const uint64_t CHUD_A = 13591409ULL;
static const uint64_t CHUD_B = 545140134ULL;
static const uint64_t CHUD_C = 640320ULL;
static const uint64_t CHUD_D = 12ULL;
static const double DIGITS_PER_TERM = 14.1816474627254776555;

struct factor_power_t{
    uint32_t prime;
    uint32_t power;
};

typedef std::vector<factor_power_t> factors_t;

class factor_sieve_t{
    std::vector<uint32_t> smallest_;

public:
    explicit factor_sieve_t(size_t n) : smallest_(n + 1, 0){
        for(size_t i = 2; i <= n; ++i){
            if(smallest_[i]) continue;
            smallest_[i] = (uint32_t)i;
            if(i > n / i) continue;
            for(size_t j = i * i; j <= n; j += i){
                if(!smallest_[j]) smallest_[j] = (uint32_t)i;
            }
        }
    }

    void append(factors_t &out, size_t value, uint32_t multiplier = 1) const{
        while(value > 1){
            uint32_t prime = smallest_[value];
            uint32_t power = 0;
            do{
                value /= prime;
                ++power;
            }while(value > 1 && smallest_[value] == prime);
            out.push_back(factor_power_t{prime, power * multiplier});
        }
    }
};

static void factor_normalize(factors_t &f){
    std::sort(f.begin(), f.end(), [](const factor_power_t &a,
                                     const factor_power_t &b){
        return a.prime < b.prime;
    });
    size_t out = 0;
    for(size_t i = 0; i < f.size(); ++i){
        if(out && f[out - 1].prime == f[i].prime){
            f[out - 1].power += f[i].power;
        }else{
            f[out++] = f[i];
        }
    }
    f.resize(out);
}

static factors_t factor_merge(const factors_t &a, const factors_t &b){
    factors_t r;
    r.reserve(a.size() + b.size());
    size_t i = 0, j = 0;
    while(i < a.size() || j < b.size()){
        if(j == b.size() || (i < a.size() && a[i].prime < b[j].prime)){
            r.push_back(a[i++]);
        }else if(i == a.size() || b[j].prime < a[i].prime){
            r.push_back(b[j++]);
        }else{
            r.push_back(factor_power_t{a[i].prime, a[i].power + b[j].power});
            ++i;
            ++j;
        }
    }
    return r;
}

static precz_t uint_pow(uint64_t base, uint32_t power){
    precz_t r(1);
    precz_t b(base);
    while(power){
        if(power & 1) r *= b;
        power >>= 1;
        if(power) b *= b;
    }
    return r;
}

static precz_t factor_product(const factors_t &f, size_t begin, size_t end){
    if(begin == end) return precz_t(1);
    if(end - begin == 1) return uint_pow(f[begin].prime, f[begin].power);
    size_t mid = begin + (end - begin) / 2;
    return factor_product(f, begin, mid) * factor_product(f, mid, end);
}

// Divide both values by their factor-table GCD, exactly as fac_remove_gcd in
// the original program.  Updating the tables avoids rediscovering the GCD.
static void factor_cancel(precz_t &p, factors_t &fp,
                          precz_t &g, factors_t &fg){
    factors_t common;
    size_t i = 0, j = 0;
    while(i < fp.size() && j < fg.size()){
        if(fp[i].prime < fg[j].prime){
            ++i;
        }else if(fg[j].prime < fp[i].prime){
            ++j;
        }else{
            uint32_t power = std::min(fp[i].power, fg[j].power);
            if(power){
                common.push_back(factor_power_t{fp[i].prime, power});
                fp[i].power -= power;
                fg[j].power -= power;
            }
            ++i;
            ++j;
        }
    }
    if(common.empty()) return;

    precz_t divisor = factor_product(common, 0, common.size());
    p = precz_divexact(p, divisor);
    g = precz_divexact(g, divisor);
    fp.erase(std::remove_if(fp.begin(), fp.end(), [](const factor_power_t &x){
        return x.power == 0;
    }), fp.end());
    fg.erase(std::remove_if(fg.begin(), fg.end(), [](const factor_power_t &x){
        return x.power == 0;
    }), fg.end());
}

struct bs_result_t{
    precz_t p;
    precz_t q;
    precz_t g;
    factors_t fp;
    factors_t fg;
};

static bs_result_t binary_split(size_t a, size_t b, bool need_g,
                                size_t level, const factor_sieve_t &sieve){
    if(b - a == 1){
        uint64_t k = (uint64_t)b;
        precz_t p(k);
        p *= precz_t(k);
        p *= precz_t(k);
        p *= precz_t((CHUD_C / 24) * (CHUD_C / 24));
        p *= precz_t(CHUD_C * 24);

        precz_t g(2 * k - 1);
        g *= precz_t(6 * k - 1);
        g *= precz_t(6 * k - 5);
        precz_t q = precz_t(CHUD_A + CHUD_B * k) * g;
        if(k & 1) q = -q;

        factors_t fp;
        sieve.append(fp, (size_t)k, 3);
        fp.push_back(factor_power_t{2, 15});
        fp.push_back(factor_power_t{3, 2});
        fp.push_back(factor_power_t{5, 3});
        fp.push_back(factor_power_t{23, 3});
        fp.push_back(factor_power_t{29, 3});
        factor_normalize(fp);

        factors_t fg;
        sieve.append(fg, (size_t)(2 * k - 1));
        sieve.append(fg, (size_t)(6 * k - 1));
        sieve.append(fg, (size_t)(6 * k - 5));
        factor_normalize(fg);
        if(!need_g) g = precz_t();
        return bs_result_t{std::move(p), std::move(q), std::move(g),
                           std::move(fp), std::move(fg)};
    }

    // Preserve Xue's tuned, slightly unbalanced split.
    size_t mid = a + (b - a) * 5224 / 10000;
    if(mid <= a) mid = a + 1;
    if(mid >= b) mid = b - 1;
    bs_result_t left = binary_split(a, mid, true, level + 1, sieve);
    bs_result_t right = binary_split(mid, b, need_g, level + 1, sieve);

    if(level >= 4) factor_cancel(right.p, right.fp, left.g, left.fg);
    precz_t q = left.q * right.p + right.q * left.g;
    precz_t p = left.p * right.p;
    factors_t fp = factor_merge(left.fp, right.fp);

    precz_t g;
    factors_t fg;
    if(need_g){
        g = left.g * right.g;
        fg = factor_merge(left.fg, right.fg);
    }
    return bs_result_t{std::move(p), std::move(q), std::move(g),
                       std::move(fp), std::move(fg)};
}

static precz_t pow10(size_t exponent){
    precz_t r(1);
    precz_t b(10);
    while(exponent){
        if(exponent & 1) r *= b;
        exponent >>= 1;
        if(exponent) b *= b;
    }
    return r;
}

static std::string format_pi(precz_t scaled, size_t digits){
    std::string s = (std::string)scaled;
    if(s.size() <= digits) s.insert(0, digits + 1 - s.size(), '0');
    s.insert(s.end() - (long long)digits, '.');
    return s;
}

int main(int argc, char **argv){
    size_t digits = argc > 1 ? (size_t)std::strtoull(argv[1], nullptr, 10) : 100;
    std::string output_file;
    bool full = false;
    for(int i = 2; i < argc; ++i){
        std::string arg(argv[i]);
        if(arg == "--full") full = true;
        if(arg == "--file" && i + 1 < argc) output_file = argv[++i];
    }

    size_t terms = std::max<size_t>(1, (size_t)(digits / DIGITS_PER_TERM) + 1);
    if(terms > (UINT32_MAX - 1) / 6){
        std::cerr << "too many digits\n";
        return 1;
    }
    std::cerr << "terms " << terms << "\n";
    auto start = std::chrono::steady_clock::now();

    factor_sieve_t sieve(6 * terms + 1);
    bs_result_t bs = binary_split(0, terms, false, 0, sieve);
    auto split_done = std::chrono::steady_clock::now();

    // pi = P*(C/D)*sqrt(C)/(Q + A*P).  sqrt(C)*10^scale is
    // evaluated as the exact integer sqrt(C*10^(2*scale)).
    const size_t guard = 12;
    size_t scale_digits = digits + guard;
    precz_t scale = pow10(scale_digits);
    precz_t sqrt_scaled = precz_sqrt(precz_t(CHUD_C) * scale * scale);
    precz_t denominator = bs.q + precz_t(CHUD_A) * bs.p;
    precz_t numerator = bs.p * precz_t(CHUD_C / CHUD_D) * sqrt_scaled;
    precz_t pi_scaled = numerator / denominator;
    pi_scaled /= pow10(guard);
    std::string pi = format_pi(pi_scaled, digits);
    auto end = std::chrono::steady_clock::now();

    double split_sec = std::chrono::duration<double>(split_done - start).count();
    double final_sec = std::chrono::duration<double>(end - split_done).count();
    std::cerr << "binary_split " << split_sec << " sec\n";
    std::cerr << "final " << final_sec << " sec\n";
    std::cerr << "time " << split_sec + final_sec << " sec\n";

    if(!output_file.empty()){
        std::ofstream file(output_file.c_str(), std::ios::binary);
        if(!file){
            std::cerr << "failed to open " << output_file << "\n";
            return 1;
        }
        file << pi << '\n';
    }
    if(full || pi.size() <= 24){
        std::cout << pi << '\n';
    }else{
        std::cout << pi.substr(0, 11) << "..." << pi.substr(pi.size() - 10) << '\n';
    }
    return 0;
}
