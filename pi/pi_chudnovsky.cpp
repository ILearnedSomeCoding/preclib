#include"../prec.hpp"

#include<cstdlib>
#include<chrono>
#include<fstream>
#include<iostream>
#include<string>
#include<utility>
#include<vector>

#define CHUD_C3_OVER_24 10939058860032000ULL
#define CHUD_A 13591409u
#define CHUD_B 545140134u

static bool show_phases = false;
static bool full_output = false;
static std::string output_file;

static double now_sec(){
    using clock_t = std::chrono::steady_clock;
    static clock_t::time_point start = clock_t::now();
    return std::chrono::duration<double>(clock_t::now() - start).count();
}

struct factor_power_t{
    uint32_t prime;
    uint32_t power;
};

struct bs_t{
    precn_t p;
    precn_t q;
    precz_t t;
    std::vector<factor_power_t> fp;
    std::vector<factor_power_t> fq;
};

class chud_factor_sieve_t{
    std::vector<uint32_t> smallest_;

public:
    chud_factor_sieve_t(size_t n) : smallest_(n + 1, 0){
        for(size_t i = 2; i <= n; ++i){
            if(smallest_[i]) continue;
            smallest_[i] = (uint32_t)i;
            if(i > n / i) continue;
            for(size_t j = i * i; j <= n; j += i){
                if(!smallest_[j]) smallest_[j] = (uint32_t)i;
            }
        }
    }

    void append(std::vector<factor_power_t> &out, size_t value,
                uint32_t multiplier = 1) const{
        while(value > 1){
            uint32_t p = smallest_[value];
            uint32_t power = 0;
            do{
                value /= p;
                ++power;
            }while(value > 1 && smallest_[value] == p);
            out.push_back(factor_power_t{p, power * multiplier});
        }
    }
};

static std::vector<factor_power_t> factor_merge(
    const std::vector<factor_power_t> &a,
    const std::vector<factor_power_t> &b){
    std::vector<factor_power_t> r;
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

static precn_t factor_pow(uint32_t base, uint32_t power){
    precn_t r(1);
    precn_t b(base);
    while(power){
        if(power & 1) r = r * b;
        power >>= 1;
        if(power) b = b * b;
    }
    return r;
}

static precn_t factor_product(const std::vector<factor_power_t> &f,
                              size_t begin, size_t end){
    if(begin == end) return precn_t(1);
    if(end - begin == 1) return factor_pow(f[begin].prime, f[begin].power);
    size_t mid = begin + (end - begin) / 2;
    return factor_product(f, begin, mid) * factor_product(f, mid, end);
}

static void factor_compact(std::vector<factor_power_t> &f){
    size_t out = 0;
    for(size_t i = 0; i < f.size(); ++i){
        if(f[i].power) f[out++] = f[i];
    }
    f.resize(out);
}

static void factor_cancel(precn_t &p, std::vector<factor_power_t> &fp,
                          precn_t &q, std::vector<factor_power_t> &fq){
    std::vector<factor_power_t> common;
    common.reserve(std::min(fp.size(), fq.size()));
    size_t i = 0, j = 0;
    while(i < fp.size() && j < fq.size()){
        if(fp[i].prime < fq[j].prime){
            ++i;
        }else if(fq[j].prime < fp[i].prime){
            ++j;
        }else{
            uint32_t power = std::min(fp[i].power, fq[j].power);
            if(power){
                fp[i].power -= power;
                fq[j].power -= power;
                common.push_back(factor_power_t{fp[i].prime, power});
            }
            ++i;
            ++j;
        }
    }
    if(common.empty()) return;

    precn_t divisor = factor_product(common, 0, common.size());
    p = p / divisor;
    q = q / divisor;
    factor_compact(fp);
    factor_compact(fq);
}

static size_t bit_length(const precn_t &a){
    if(a.rsiz == 0) return 0;
    uint64_t top = a.a[a.rsiz - 1];
    size_t bits = (a.rsiz - 1) * 64;
    while(top){
        ++bits;
        top >>= 1;
    }
    return bits;
}

static precn_t pow_u32(uint32_t base, size_t exp){
    precn_t r(1);
    precn_t b(base);
    while(exp){
        if(exp & 1) r = r * b;
        exp >>= 1;
        if(exp) b = b * b;
    }
    return r;
}

static void mul_u64_self(precn_t &a, uint64_t b){
    if(a.rsiz == 0 || b == 1) return;
    if(b == 0){
        a.rsiz = 0;
        a.a[0] = 0;
        return;
    }
    if(a.asiz < a.rsiz + 1){
        a.a = (uint64_t*)realloc(a.a, (a.rsiz + 1) * sizeof(uint64_t));
        a.asiz = a.rsiz + 1;
    }

    uint64_t carry = 0;
    for(size_t i = 0; i < a.rsiz; ++i){
        uint64_t hi, lo, out;
        precn_mul_wide(a.a[i], b, hi, lo);
        uint64_t c = precn_add_carry(lo, carry, 0, out);
        a.a[i] = out;
        carry = hi + c;
    }
    if(carry) a.a[a.rsiz++] = carry;
}

struct pow10_entry_t{
    size_t digits;
    precn_t value;
};

static size_t pow10_index(size_t digits, std::vector<pow10_entry_t> &cache){
    for(size_t i = 0; i < cache.size(); ++i){
        if(cache[i].digits == digits) return i;
    }
    cache.push_back(pow10_entry_t{digits, pow_u32(10, digits)});
    return cache.size() - 1;
}

static precn_t sqrt10005_scaled(size_t, size_t scale_index,
                                std::vector<pow10_entry_t> &pow10_cache){
    precn_t n = mul_u32(pow10_cache[scale_index].value, 10005);
    return precn_sqrt(n);
}

// A parent only needs P from its left child to form T.  Matching ilmPi's
// needp scheduling avoids forming product-tree nodes that will not be used.
static bs_t chud_bs(size_t a, size_t b, bool need_p, size_t level,
                    const chud_factor_sieve_t &sieve){
    if(b - a == 1){
        uint64_t k = (uint64_t)b;
        precn_t p((uint64_t)(6 * k - 5));
        mul_u64_self(p, (uint64_t)(2 * k - 1));
        mul_u64_self(p, (uint64_t)(6 * k - 1));

        precn_t q(k);
        mul_u64_self(q, k);
        mul_u64_self(q, k);
        mul_u64_self(q, (uint64_t)CHUD_C3_OVER_24);

        precn_t term = p * (uint64_t)(CHUD_B * k + CHUD_A);
        precz_t t(std::move(term));
        if(k & 1) t = -t;

        std::vector<factor_power_t> fp;
        sieve.append(fp, (size_t)(6 * k - 5));
        sieve.append(fp, (size_t)(2 * k - 1));
        sieve.append(fp, (size_t)(6 * k - 1));
        std::sort(fp.begin(), fp.end(), [](const factor_power_t &x,
                                           const factor_power_t &y){
            return x.prime < y.prime;
        });
        std::vector<factor_power_t> fp_merged;
        for(size_t i = 0; i < fp.size(); ++i){
            if(!fp_merged.empty() && fp_merged.back().prime == fp[i].prime){
                fp_merged.back().power += fp[i].power;
            }else{
                fp_merged.push_back(fp[i]);
            }
        }

        std::vector<factor_power_t> fq;
        sieve.append(fq, (size_t)k, 3);
        fq.push_back(factor_power_t{2, 15});
        fq.push_back(factor_power_t{3, 2});
        fq.push_back(factor_power_t{5, 3});
        fq.push_back(factor_power_t{23, 3});
        fq.push_back(factor_power_t{29, 3});
        std::sort(fq.begin(), fq.end(), [](const factor_power_t &x,
                                           const factor_power_t &y){
            return x.prime < y.prime;
        });
        std::vector<factor_power_t> fq_merged;
        for(size_t i = 0; i < fq.size(); ++i){
            if(!fq_merged.empty() && fq_merged.back().prime == fq[i].prime){
                fq_merged.back().power += fq[i].power;
            }else{
                fq_merged.push_back(fq[i]);
            }
        }
        return bs_t{std::move(p), std::move(q), std::move(t),
                    std::move(fp_merged), std::move(fq_merged)};
    }

    size_t m = a + (b - a) / 2;
    bs_t l = chud_bs(a, m, true, level + 1, sieve);
    bs_t r = chud_bs(m, b, need_p, level + 1, sieve);

    // This is ilmPi's factor-aware cancellation: scaling P_left and Q_right
    // by the same exact factor scales Q and T equally, preserving T/Q while
    // keeping every multiplication above this node smaller.
    if(level >= 4) factor_cancel(l.p, l.fp, r.q, r.fq);

    precn_t q = l.q * r.q;
    precz_t t = l.t * precz_t(r.q) + r.t * precz_t(l.p);
    std::vector<factor_power_t> fq = factor_merge(l.fq, r.fq);
    if(need_p){
        precn_t p = l.p * r.p;
        std::vector<factor_power_t> fp = factor_merge(l.fp, r.fp);
        return bs_t{std::move(p), std::move(q), std::move(t),
                    std::move(fp), std::move(fq)};
    }
    return bs_t{precn_t(), std::move(q), std::move(t),
                std::vector<factor_power_t>(), std::move(fq)};
}

static std::string to_dec(const precn_t &a){
    size_t n = bit_length(a) * 30103 / 100000 + 1;
    std::vector<uint32_t> d(n);
    precn_base_convert(a, 10, d.data(), n);
    if(n == 0) return "0";

    std::string s;
    s.reserve(n);
    for(size_t i = n; i > 0; --i) s.push_back((char)('0' + d[i - 1]));
    return s;
}

static std::string pi_digits(size_t digits){
    size_t guard = 10;
    size_t work_digits = digits + guard;
    size_t terms = work_digits / 14 + 1;

    double t0 = now_sec();
    if(terms > (UINT32_MAX - 1) / 6) return "error";
    chud_factor_sieve_t sieve(6 * terms + 1);
    bs_t bs = chud_bs(0, terms, false, 0, sieve);
    bs.t += precz_t(bs.q * CHUD_A);
    double t1 = now_sec();
    if(bs.t.is_negative() || bs.t.is_zero()) return "error";

    std::vector<pow10_entry_t> pow10_cache;
    size_t scale_index = pow10_index(work_digits * 2, pow10_cache);
    precn_t sqrt_scaled = sqrt10005_scaled(work_digits, scale_index, pow10_cache);
    double t2 = now_sec();
    precn_t numerator = mul_u32(bs.q, 426880) * sqrt_scaled;
    precn_t pi_scaled = numerator / bs.t.magnitude();
    pi_scaled = pi_scaled / 10000000000ULL;
    double t3 = now_sec();

    std::string s = to_dec(pi_scaled);
    double t4 = now_sec();
    if(show_phases){
        std::cerr << "binary_split " << (t1 - t0) << " sec\n";
        std::cerr << "sqrt_scale " << (t2 - t1) << " sec\n";
        std::cerr << "final_div " << (t3 - t2) << " sec\n";
        std::cerr << "to_decimal " << (t4 - t3) << " sec\n";
    }
    if(digits == 0) return s;
    if(s.size() <= digits) s.insert(0, digits + 1 - s.size(), '0');
    s.insert(s.end() - (long long)digits, '.');
    return s;
}

static std::string short_pi(const std::string &s){
    if(full_output || s.size() <= 24) return s;

    size_t first = 0;
    size_t first_end = 0;
    while(first_end < s.size() && first < 10){
        if(s[first_end] >= '0' && s[first_end] <= '9') ++first;
        ++first_end;
    }
    if(first < 10 || s.size() <= first_end + 10) return s;
    return s.substr(0, first_end) + "..." + s.substr(s.size() - 10);
}

int main(int argc, char **argv){
    size_t digits = 100;
    if(argc > 1){
        digits = (size_t)std::strtoull(argv[1], nullptr, 10);
    }
    for(int i = 2; i < argc; ++i){
        std::string arg(argv[i]);
        if(arg == "--phases") show_phases = true;
        if(arg == "--full") full_output = true;
        if(arg == "--file" && i + 1 < argc) output_file = argv[++i];
    }
    double start = now_sec();
    std::string out = pi_digits(digits);
    double sec = now_sec() - start;

    if(!output_file.empty()){
        std::ofstream file(output_file.c_str(), std::ios::out | std::ios::binary);
        if(!file){
            std::cerr << "failed to open " << output_file << "\n";
            return 1;
        }
        file << out << "\n";
    }

    std::cout << short_pi(out) << "\n";
    if(!output_file.empty()) std::cerr << "wrote " << output_file << "\n";
#if defined(COUNT_FFTS) && COUNT_FFTS
    std::cerr << "total_fftmuls " << total_fftmuls << "\n";
    std::cerr << "danger_fftmuls " << danger_fftmuls << "\n";
    std::cerr << "danger_fftmuls_1_4 " << danger_fftmuls_1_4 << "\n";
    std::cerr << "danger_fftmuls_3_8 " << danger_fftmuls_3_8 << "\n";
    std::cerr << "max_fft_rounding_error " << max_fft_rounding_error << "\n";
#endif
    std::cerr << "time " << sec << " sec\n";
    return 0;
}
