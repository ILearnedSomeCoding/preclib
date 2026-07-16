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

struct sprecn_t{
    precn_t v;
    bool neg;
};

struct bs_t{
    precn_t p;
    precn_t q;
    sprecn_t t;
};

static sprecn_t sp_make(precn_t v, bool neg){
    bool sign = neg && v.rsiz != 0;
    return sprecn_t{std::move(v), sign};
}

static sprecn_t sp_add(const sprecn_t &a, const sprecn_t &b){
    if(a.neg == b.neg) return sp_make(a.v + b.v, a.neg);
    if(a.v >= b.v) return sp_make(a.v - b.v, a.neg);
    return sp_make(b.v - a.v, b.neg);
}

static sprecn_t sp_mul(const sprecn_t &a, const precn_t &b){
    return sp_make(a.v * b, a.neg);
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
static bs_t chud_bs(size_t a, size_t b, bool need_p){
    if(b - a == 1){
        if(a == 0){
            return bs_t{precn_t(1), precn_t(1), sp_make(precn_t(CHUD_A), false)};
        }

        uint64_t k = (uint64_t)a;
        precn_t p((uint64_t)(6 * k - 5));
        mul_u64_self(p, (uint64_t)(2 * k - 1));
        mul_u64_self(p, (uint64_t)(6 * k - 1));

        precn_t q(k);
        mul_u64_self(q, k);
        mul_u64_self(q, k);
        mul_u64_self(q, (uint64_t)CHUD_C3_OVER_24);

        precn_t term = p * (uint64_t)(CHUD_B * k + CHUD_A);
        return bs_t{std::move(p), std::move(q), sp_make(std::move(term), (a & 1) != 0)};
    }

    size_t m = a + (b - a) / 2;
    bs_t l = chud_bs(a, m, true);
    bs_t r = chud_bs(m, b, need_p);

    precn_t q = l.q * r.q;
    sprecn_t t = sp_add(sp_mul(l.t, r.q), sp_mul(r.t, l.p));
    if(need_p){
        precn_t p = l.p * r.p;
        return bs_t{std::move(p), std::move(q), std::move(t)};
    }
    return bs_t{precn_t(), std::move(q), std::move(t)};
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
    size_t terms = work_digits / 14 + 2;

    double t0 = now_sec();
    bs_t bs = chud_bs(0, terms, false);
    double t1 = now_sec();
    if(bs.t.neg || bs.t.v.rsiz == 0) return "error";

    std::vector<pow10_entry_t> pow10_cache;
    size_t scale_index = pow10_index(work_digits * 2, pow10_cache);
    precn_t sqrt_scaled = sqrt10005_scaled(work_digits, scale_index, pow10_cache);
    double t2 = now_sec();
    precn_t numerator = mul_u32(bs.q, 426880) * sqrt_scaled;
    precn_t pi_scaled = numerator / bs.t.v;
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
    std::cerr << "time " << sec << " sec\n";
    return 0;
}
