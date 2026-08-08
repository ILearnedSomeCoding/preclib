#include"../../prec_num.hpp"

#include<algorithm>
#include<cmath>
#include<cstdlib>
#include<utility>
#include<vector>

namespace{

const uint64_t chud_c3_over_24 = 10939058860032000ULL;
const uint32_t chud_a = 13591409u;
const uint32_t chud_b = 545140134u;
const int pi_cache_digits = 1000;
const size_t pi_guard_digits = 16;

// A binary-splitting node stores P, Q, and signed T for a Chudnovsky interval.
// Prime-power lists let upper levels cancel exact factors before multiplying.
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

class factor_sieve_t{
    std::vector<uint32_t> smallest_;

public:
    // Smallest-prime-factor table used to factor every leaf in near-linear time.
    factor_sieve_t(size_t n) : smallest_(n + 1, 0){
        for(size_t i = 2; i <= n; ++i){
            if(smallest_[i]) continue;
            smallest_[i] = (uint32_t)i;
            if(i > n / i) continue;
            for(size_t j = i * i; j <= n; j += i)
                if(!smallest_[j]) smallest_[j] = (uint32_t)i;
        }
    }

    void append(std::vector<factor_power_t> &out, size_t value,
                uint32_t multiplier = 1) const{
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

static std::vector<factor_power_t> factor_merge(
    const std::vector<factor_power_t> &a,
    const std::vector<factor_power_t> &b){
    std::vector<factor_power_t> result;
    result.reserve(a.size() + b.size());
    size_t i = 0, j = 0;
    while(i < a.size() || j < b.size()){
        if(j == b.size() || (i < a.size() && a[i].prime < b[j].prime)){
            result.push_back(a[i++]);
        }else if(i == a.size() || b[j].prime < a[i].prime){
            result.push_back(b[j++]);
        }else{
            result.push_back(factor_power_t{a[i].prime,
                                            a[i].power + b[j].power});
            ++i;
            ++j;
        }
    }
    return result;
}

static precn_t factor_pow(uint32_t base, uint32_t power){
    precn_t result(1), value(base);
    while(power){
        if(power & 1) result = result * value;
        power >>= 1;
        if(power) value = value * value;
    }
    return result;
}

static precn_t factor_product(const std::vector<factor_power_t> &f,
                              size_t begin, size_t end){
    if(begin == end) return precn_t(1);
    if(end - begin == 1) return factor_pow(f[begin].prime, f[begin].power);
    size_t middle = begin + (end - begin) / 2;
    return factor_product(f, begin, middle) * factor_product(f, middle, end);
}

static void factor_compact(std::vector<factor_power_t> &f){
    size_t out = 0;
    for(size_t i = 0; i < f.size(); ++i)
        if(f[i].power) f[out++] = f[i];
    f.resize(out);
}

static void factor_cancel(precn_t &p, std::vector<factor_power_t> &fp,
                          precn_t &q, std::vector<factor_power_t> &fq){
    // Divide matching factors from a left P and right Q. Scaling both by the
    // same exact divisor preserves the parent T/Q ratio and shrinks products.
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

static void mul_u64_self(precn_t &a, uint64_t b){
    // Leaves multiply several one-limb factors; doing it in place avoids a
    // temporary precn_t allocation for each factor.
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
        uint64_t extra = precn_add_carry(lo, carry, 0, out);
        a.a[i] = out;
        carry = hi + extra;
    }
    if(carry) a.a[a.rsiz++] = carry;
}

static void merge_leaf_factors(std::vector<factor_power_t> &f){
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

static bs_t chud_bs(size_t a, size_t b, bool need_p, size_t level,
                    const factor_sieve_t &sieve){
    if(b - a == 1){
        // One Chudnovsky term. The interval convention uses k=b, so the root
        // call chud_bs(0, terms) covers k=1 through k=terms.
        uint64_t k = (uint64_t)b;
        precn_t p((uint64_t)(6 * k - 5));
        mul_u64_self(p, (uint64_t)(2 * k - 1));
        mul_u64_self(p, (uint64_t)(6 * k - 1));

        precn_t q(k);
        mul_u64_self(q, k);
        mul_u64_self(q, k);
        mul_u64_self(q, chud_c3_over_24);

        precn_t term = p * (uint64_t)(chud_b * k + chud_a);
        precz_t t(std::move(term));
        if(k & 1) t = -t;

        std::vector<factor_power_t> fp;
        sieve.append(fp, (size_t)(6 * k - 5));
        sieve.append(fp, (size_t)(2 * k - 1));
        sieve.append(fp, (size_t)(6 * k - 1));
        merge_leaf_factors(fp);

        std::vector<factor_power_t> fq;
        sieve.append(fq, (size_t)k, 3);
        fq.push_back(factor_power_t{2, 15});
        fq.push_back(factor_power_t{3, 2});
        fq.push_back(factor_power_t{5, 3});
        fq.push_back(factor_power_t{23, 3});
        fq.push_back(factor_power_t{29, 3});
        merge_leaf_factors(fq);
        return bs_t{std::move(p), std::move(q), std::move(t),
                    std::move(fp), std::move(fq)};
    }

    size_t middle = a + (b - a) / 2;
    bs_t left = chud_bs(a, middle, true, level + 1, sieve);
    bs_t right = chud_bs(middle, b, need_p, level + 1, sieve);
    // P is needed only by a parent's left child. Avoid building unused P
    // products on the right edge of the binary-splitting tree.
    if(level >= 4)
        factor_cancel(left.p, left.fp, right.q, right.fq);

    precn_t q = left.q * right.q;
    precz_t t = left.t * precz_t(right.q) + right.t * precz_t(left.p);
    std::vector<factor_power_t> fq = factor_merge(left.fq, right.fq);
    if(need_p){
        precn_t p = left.p * right.p;
        std::vector<factor_power_t> fp = factor_merge(left.fp, right.fp);
        return bs_t{std::move(p), std::move(q), std::move(t),
                    std::move(fp), std::move(fq)};
    }
    return bs_t{precn_t(), std::move(q), std::move(t),
                std::vector<factor_power_t>(), std::move(fq)};
}

static precn_t pow10(size_t exponent){
    precn_t result(1), value(10);
    while(exponent){
        if(exponent & 1) result = result * value;
        exponent >>= 1;
        if(exponent) value = value * value;
    }
    return result;
}

static precn_t pi_scaled(size_t digits){
    // Produce floor(pi * 10^digits) entirely with integer arithmetic:
    // pi = 426880 * sqrt(10005) * Q / T.
    size_t terms = digits / 14 + 1;
    if(terms > (UINT32_MAX - 1) / 6) std::abort();
    factor_sieve_t sieve(6 * terms + 1);
    bs_t bs = chud_bs(0, terms, false, 0, sieve);
    bs.t += precz_t(bs.q * chud_a);
    if(bs.t.is_negative() || bs.t.is_zero()) std::abort();

    precn_t scale = pow10(digits * 2);
    precn_t sqrt_scaled = precn_sqrt(mul_u32(scale, 10005));
    precn_t numerator = mul_u32(bs.q, 426880) * sqrt_scaled;
    return numerator / bs.t.magnitude();
}

static double pi_precision_bits(int digits){
    return std::ceil(((double)digits + 2.0) * 3.32192809488736234787);
}

static Number calculate_pi(int digits){
    // Chudnovsky gives a decimal-scaled integer. Keep extra decimal digits,
    // divide by the matching power of ten, then trim to the public precision.
    size_t scale_digits = (size_t)digits + pi_guard_digits;
    precn_t numerator = pi_scaled(scale_digits);
    precn_t denominator = pow10(scale_digits);
    double precision = pi_precision_bits(digits);
    double work_precision = precision + 64.0;
    Number n(std::move(numerator));
    Number d(std::move(denominator));
    n.set_precision(work_precision + 1.0);
    d.set_precision(work_precision + 1.0);
    Number result = n / d;
    result.set_precision(precision);
    return result;
}

} // namespace

Number getpi(int digits){
    if(digits <= 0) std::abort();
    // C++11 guarantees one thread initializes this cache while others wait.
    // Returning a copy lets each caller reduce precision independently.
    static const Number cached_pi = calculate_pi(pi_cache_digits);
    if(digits <= pi_cache_digits){
        Number result = cached_pi;
        result.set_precision(pi_precision_bits(digits));
        return result;
    }
    return calculate_pi(digits);
}
