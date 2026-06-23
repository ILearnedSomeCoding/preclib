#include"../prec.hpp"

#include<cstdlib>
#include<chrono>
#include<fstream>
#include<iostream>
#include<string>
#include<vector>

#define CHUD_C3_OVER_24 10939058860032000ULL
#define CHUD_A 13591409u
#define CHUD_B 545140134u

static bool show_phases = false;
static bool full_output = false;
static std::string output_file;
static size_t sqrt_iterations = 0;

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
    sprecn_t r;
    r.v = v;
    r.neg = neg && v.rsiz != 0;
    return r;
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
    uint32_t top = a.a[a.rsiz - 1];
    size_t bits = (a.rsiz - 1) * 32;
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

static precn_t isqrt_guess(const precn_t &n, precn_t x){
    if(n.rsiz == 0) return precn_t();
    for(;;){
        ++sqrt_iterations;
        // Use ceil(n / x) and ceil-average so an upper guess stays upper.
        // That avoids dropping below sqrt(n), which would make correction
        // painfully expensive at high precision.
        precn_t div = (n + x - precn_t(1)) / x;
        precn_t y = (x + div + precn_t(1)) >> 1;
        if(y >= x) break;
        x = y;
    }

    while(x * x > n) x = x - precn_t(1);
    return x;
}

static precn_t isqrt(const precn_t &n){
    if(n.rsiz == 0) return precn_t();

    size_t bits = bit_length(n);
    return isqrt_guess(n, precn_t(1) << ((bits + 1) / 2));
}

static precn_t sqrt10005_scaled(size_t digits){
    if(digits <= 32){
        precn_t n = mul_u32(pow_u32(10, digits * 2), 10005);
        return isqrt(n);
    }

    size_t half = (digits + 1) / 2;
    precn_t low = sqrt10005_scaled(half);
    precn_t factor = pow_u32(10, digits - half);
    precn_t upper = (low + precn_t(1)) * factor;
    precn_t n = mul_u32(pow_u32(10, digits * 2), 10005);
    return isqrt_guess(n, upper);
}

static bs_t chud_bs(size_t a, size_t b){
    if(b - a == 1){
        bs_t r;
        if(a == 0){
            r.p = precn_t(1);
            r.q = precn_t(1);
        }else{
            r.p = precn_t((uint64_t)(6 * a - 5));
            r.p = r.p * precn_t((uint64_t)(2 * a - 1));
            r.p = r.p * precn_t((uint64_t)(6 * a - 1));

            r.q = precn_t((uint64_t)a) * precn_t((uint64_t)a);
            r.q = r.q * precn_t((uint64_t)a);
            r.q = r.q * precn_t((uint64_t)CHUD_C3_OVER_24);
        }

        precn_t term = r.p * (mul_u32(precn_t((uint64_t)a), CHUD_B) + precn_t(CHUD_A));
        r.t = sp_make(term, (a & 1) != 0);
        return r;
    }

    size_t m = a + (b - a) / 2;
    bs_t l = chud_bs(a, m);
    bs_t r = chud_bs(m, b);

    bs_t out;
    out.p = l.p * r.p;
    out.q = l.q * r.q;
    out.t = sp_add(sp_mul(l.t, r.q), sp_mul(r.t, l.p));
    return out;
}

static std::string to_dec(const precn_t &a){
    size_t n = 0;
    precn_base_convert(a, 10, nullptr, n);
    if(n == 0) return "0";

    std::vector<uint32_t> d(n);
    precn_base_convert(a, 10, d.data(), n);

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
    bs_t bs = chud_bs(0, terms);
    double t1 = now_sec();
    if(bs.t.neg || bs.t.v.rsiz == 0) return "error";

    sqrt_iterations = 0;
    precn_t sqrt_scaled = sqrt10005_scaled(work_digits);
    double t2 = now_sec();
    precn_t numerator = mul_u32(bs.q, 426880) * sqrt_scaled;
    precn_t pi_scaled = numerator / bs.t.v;
    pi_scaled = pi_scaled / pow_u32(10, guard);
    double t3 = now_sec();

    std::string s = to_dec(pi_scaled);
    double t4 = now_sec();
    if(show_phases){
        std::cerr << "binary_split " << (t1 - t0) << " sec\n";
        std::cerr << "sqrt_scale " << (t2 - t1) << " sec\n";
        std::cerr << "sqrt_iterations " << sqrt_iterations << "\n";
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
