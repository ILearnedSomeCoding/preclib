#include"../../prec_num.hpp"

#include<algorithm>
#include<cmath>
#include<cstdlib>
#include<limits>
#include<utility>

namespace{

const int e_cache_digits = 1000;

// These helpers estimate exponents only. Series values remain arbitrary
// precision Numbers; long double is never used as the numerical result.
static size_t trans_bit_length(const precn_t &a){
    if(a.rsiz == 0) return 0;
#if defined(__clang__) || defined(__GNUC__)
    return (a.rsiz - 1) * 64 + 64 -
           (size_t)__builtin_clzll(a.a[a.rsiz - 1]);
#else
    size_t bits = (a.rsiz - 1) * 64;
    uint64_t top = a.a[a.rsiz - 1];
    while(top){ ++bits; top >>= 1; }
    return bits;
#endif
}

static long double trans_log2_abs(const Number &a){
    if(a.is_zero()) return -std::numeric_limits<long double>::infinity();
    const precn_t &mag = a.significand().magnitude();
    uint64_t top = mag.a[mag.rsiz - 1];
    long double lead = (long double)top;
    if(mag.rsiz > 1)
        lead += std::ldexp((long double)mag.a[mag.rsiz - 2], -64);
    return std::log2(lead) + (long double)(mag.rsiz - 1) * 64.0L -
           (long double)a.radix_point() * 64.0L;
}

static double trans_precision(const Number &a){
    // Exact integers do not imply exact transcendental results. Use the same
    // 64-bit default policy as exact Number division.
    double precision = a.is_exact() ? 64.0 : a.precision();
    if(!std::isfinite(precision) || precision < 1.0) std::abort();
    return precision;
}

static double trans_precision(const Number &a, const Number &b){
    if(a.is_exact()) return trans_precision(b);
    if(b.is_exact()) return trans_precision(a);
    return std::min(trans_precision(a), trans_precision(b));
}

static size_t trans_bit_length(const precz_t &a){
    return trans_bit_length(a.magnitude());
}

static size_t checked_count(long double value){
    if(value < 0.0L || value > (long double)INT64_MAX) std::abort();
    return (size_t)value;
}

static bool term_is_small(const Number &term, const Number &sum,
                          double bits){
    if(term.is_zero()) return true;
    if(sum.is_zero()) return false;
    // Stop after the term is eight bits below the requested relative error.
    return trans_log2_abs(term) <= trans_log2_abs(sum) - bits - 8.0L;
}

struct exp_bs_t{
    // For Taylor terms t_k = x^k/k!, [begin,end) represents
    //   sum(t_k)/t_begin = t/q, and t_end/t_begin = p/q.
    Number p;
    Number q;
    Number t;
};

static exp_bs_t exp_binary_split(const Number &x, size_t begin, size_t end){
    if(end - begin == 1){
        if(begin == SIZE_MAX) std::abort();
        Number q((uint64_t)(begin + 1));
        return exp_bs_t{x, q, q};
    }
    size_t middle = begin + (end - begin) / 2;
    exp_bs_t left = exp_binary_split(x, begin, middle);
    exp_bs_t right = exp_binary_split(x, middle, end);
    // Concatenate the ranges:
    // R = R_left + (P_left/Q_left) * R_right.
    Number t = left.t * right.q + left.p * right.t;
    Number p = left.p * right.p;
    Number q = left.q * right.q;
    return exp_bs_t{std::move(p), std::move(q), std::move(t)};
}

static size_t exp_last_term(const Number &x, double bits){
    long double logx = trans_log2_abs(x);
    long double cutoff = -(long double)bits - 16.0L;
    size_t limit = checked_count(std::ceil(bits)) + 32;
    const long double inv_log_2 = 1.44269504088896340736L;
    for(size_t k = 1; k <= limit; ++k){
        long double term_bits = (long double)k * logx -
                                std::lgammal((long double)k + 1.0L) * inv_log_2;
        if(term_bits <= cutoff) return k;
    }
    std::abort();
}

static Number exp_taylor_binary(Number x, double precision, bool minus_one){
    size_t last = exp_last_term(x, precision);
    size_t begin = minus_one ? 1 : 0;
    if(last < begin) last = begin;
    if(last == SIZE_MAX) std::abort();

    // Multiplication along the tree loses only logarithmically many tracked
    // bits. Supply those bits before constructing the balanced sum.
    double tree_guard = std::ceil(std::log2((double)(last + 1))) + 32.0;
    x.set_precision(precision + tree_guard);
    exp_bs_t split = exp_binary_split(x, begin, last + 1);
    Number result = split.t / split.q;
    if(minus_one) result *= x;
    result.set_precision(precision);
    return result;
}

static Number exp_positive(Number x, double target_precision){
    // Evaluate exp(x / 2^shifts), where the reduced argument is tiny. The
    // Taylor series then needs few terms; repeated squaring reconstructs exp(x).
    long double logx = trans_log2_abs(x);
    size_t magnitude_shifts = logx > -1.0L
        ? checked_count(std::ceil(logx + 1.0L)) : 0;
    // Binary splitting performs about two significant multiplications per
    // retained Taylor term, so sqrt(2p) balances terms against reconstruction.
    size_t series_shifts =
        checked_count(std::ceil(std::sqrt(target_precision * 2.0))) + 2;
    if(magnitude_shifts > (size_t)INT64_MAX - series_shifts) std::abort();
    size_t shifts = magnitude_shifts + series_shifts;
    // Every reconstruction square can consume about one tracked bit. Budget
    // those bits up front and retain a fixed guard margin for the series.
    double work_precision = target_precision + (double)shifts + 96.0;
    x.set_precision(work_precision);
    Number reduced = x >> (int64_t)shifts;
    Number sum = exp_taylor_binary(reduced, work_precision, false);
    for(size_t i = 0; i < shifts; ++i) sum *= sum;
    sum.set_precision(target_precision);
    return sum;
}

static Number expm1_series(Number x, double target_precision){
    long double logx = trans_log2_abs(x);
    long double reduction_goal =
        std::ceil(std::sqrt(target_precision * 2.0)) + 2.0L;
    size_t shifts = logx > -reduction_goal
        ? checked_count(std::ceil(logx + reduction_goal)) : 0;
    double work_precision = target_precision + (double)shifts * 2.0 + 96.0;
    x.set_precision(work_precision);
    Number reduced = x >> (int64_t)shifts;

    // Starting the split at t_1 factors x out of the rational sum, retaining
    // it as the leading significant term instead of subtracting one afterward.
    Number sum = exp_taylor_binary(reduced, work_precision, true);

    Number two(2);
    two.set_precision(work_precision);
    // If u = expm1(y), then expm1(2y) = u * (u + 2).
    for(size_t i = 0; i < shifts; ++i) sum *= sum + two;
    sum.set_precision(target_precision);
    return sum;
}

static Number calculate_e(int digits){
    // Convert requested decimal places to significant binary precision, then
    // use the same exp implementation as every other caller.
    double precision = std::ceil(((double)digits + 2.0) *
                                 3.32192809488736234787);
    Number one(1);
    one.set_precision(precision);
    Number result = exp(one);
    result.set_precision(precision);
    return result;
}

} // namespace

Number exp(const Number &a){
    double target_precision = trans_precision(a);
    if(a.is_zero()) return Number(1);
    if(a.is_negative()){
        // The positive series is simpler and better conditioned; obtain the
        // negative branch from exp(-x) = 1 / exp(x).
        Number denominator = exp_positive(abs(a), target_precision + 16.0);
        Number numerator(1);
        numerator.set_precision(target_precision + 16.0);
        Number result = numerator / denominator;
        result.set_precision(target_precision);
        return result;
    }
    return exp_positive(a, target_precision);
}

Number expm1(const Number &a){
    if(a.is_zero()) return a;
    return expm1_series(a, trans_precision(a));
}

Number ln(const Number &a){
    if(a.is_zero() || a.is_negative()) std::abort();
    if(a == Number(1)) return Number(0);

    double target_precision = trans_precision(a);
    // First remove extreme magnitude. atanh performs its own series reduction,
    // so ln only needs enough square roots to keep (x-1)/(x+1) away from 1.
    long double magnitude = std::fabs(trans_log2_abs(a));
    size_t shifts = magnitude > 1.0L
        ? checked_count(std::ceil(std::log2(magnitude + 1.0L))) + 2 : 2;
    double work_precision = target_precision + (double)shifts * 2.0 + 128.0;

    Number reduced = a;
    reduced.set_precision(work_precision);
    for(size_t i = 0; i < shifts; ++i) reduced = sqrt(reduced);

    Number one(1);
    one.set_precision(work_precision);
    // ln(x) = 2 * atanh((x - 1)/(x + 1)). Keeping atanh as the shared
    // kernel gives ln and the public inverse hyperbolic function one path.
    Number z = (reduced - one) / (reduced + one);
    z.set_precision(target_precision + 64.0);
    Number result = atanh(z) << (int64_t)(shifts + 1);
    result.set_precision(target_precision);
    return result;
}

static Number log_base(const Number &a, uint64_t base){
    if(a.is_zero() || a.is_negative()) std::abort();
    if(a == Number(1)) return Number(0);

    // Compute both logarithms with guard bits because the final division loses
    // some relative accuracy, especially when the requested result is tiny.
    double target_precision = trans_precision(a);
    double work_precision = target_precision + 64.0;
    Number value = a;
    value.set_precision(work_precision);
    Number radix(base);
    radix.set_precision(work_precision);
    Number result = ln(value) / ln(radix);
    result.set_precision(target_precision);
    return result;
}

Number log10(const Number &a){
    return log_base(a, 10);
}

Number log2(const Number &a){
    return log_base(a, 2);
}

static Number pow_integer(const Number &a, const precz_t &exponent,
                          double target_precision){
    const precn_t &magnitude = exponent.magnitude();
    if(magnitude.rsiz == 0) return Number(1);
    if(a.is_zero()){
        if(exponent.is_negative()) std::abort();
        return Number(0);
    }

    // Binary exponentiation accepts arbitrarily large integer exponents
    // without converting them to a machine integer.
    double work_precision = target_precision +
                            (double)trans_bit_length(exponent) + 32.0;
    Number factor = a;
    if(!factor.is_exact()) factor.set_precision(work_precision);
    Number result(1);
    if(!factor.is_exact()) result.set_precision(work_precision);
    for(size_t limb = 0; limb < magnitude.rsiz; ++limb){
        uint64_t bits = magnitude.a[limb];
        for(unsigned bit = 0; bit < 64; ++bit){
            if(bits & 1) result *= factor;
            bits >>= 1;
            bool more = bits != 0 || limb + 1 < magnitude.rsiz;
            if(more) factor *= factor;
            if(!more) break;
        }
    }
    if(exponent.is_negative()){
        Number one(1);
        one.set_precision(work_precision);
        result = one / result;
    }
    if(!result.is_exact()) result.set_precision(target_precision);
    return result;
}

Number pow(const Number &a, const Number &b){
    // Exact-in-value integer exponents have a faster path which also supports
    // negative bases and preserves exact positive powers of exact inputs.
    precz_t integer_exponent = b.to_integer();
    double target_precision = trans_precision(a, b);
    if(b == Number(integer_exponent))
        return pow_integer(a, integer_exponent, target_precision);

    // This Number type currently represents reals only. A negative base with
    // a fractional exponent would require a complex result.
    if(a.is_zero()){
        if(b.is_negative()) std::abort();
        return Number(0);
    }
    if(a.is_negative()) std::abort();
    double work_precision = target_precision + 64.0;
    Number base = a;
    Number exponent = b;
    base.set_precision(work_precision);
    exponent.set_precision(work_precision);
    Number result = exp(exponent * ln(base));
    result.set_precision(target_precision);
    return result;
}

namespace{

struct trig_pair_t{
    Number sine;
    Number cosine;
};

static unsigned trans_mod4(const precz_t &a){
    const precn_t &magnitude = a.magnitude();
    unsigned remainder = magnitude.rsiz ? (unsigned)(magnitude.a[0] & 3) : 0;
    if(a.is_negative() && remainder) remainder = 4 - remainder;
    return remainder;
}

static uint64_t trig_denominator(size_t a, size_t b){
    if(a > (size_t)UINT64_MAX || b > (size_t)UINT64_MAX ||
       (uint64_t)a > UINT64_MAX / (uint64_t)b) std::abort();
    return (uint64_t)a * (uint64_t)b;
}

static trig_pair_t trig_pair(const Number &a){
    double target_precision = trans_precision(a);
    if(a.is_zero()) return trig_pair_t{Number(0), Number(1)};

    // Reducing a large argument subtracts two nearly equal values. Compute pi
    // with enough leading bits to retain the requested precision afterward.
    long double argument_bits = std::max(0.0L, trans_log2_abs(a));
    long double work_bits_ld = (long double)target_precision + argument_bits + 128.0L;
    if(work_bits_ld > (long double)INT_MAX) std::abort();
    double work_precision = (double)work_bits_ld;
    long double decimal_digits_ld =
        std::ceil(work_bits_ld * 0.30102999566398119521L) + 8.0L;
    if(decimal_digits_ld > (long double)INT_MAX) std::abort();

    Number pi = getpi((int)decimal_digits_ld);
    pi.set_precision(work_precision);
    Number half_pi = pi >> 1;
    Number value = a;
    value.set_precision(work_precision);

    // Select the nearest multiple of pi/2. This leaves a reduced argument in
    // [-pi/4, pi/4], where both Taylor series converge quickly.
    Number quotient = value / half_pi;
    Number half = Number(1) >> 1;
    precz_t quadrant_index = quotient.is_negative()
        ? (quotient - half).to_integer() : (quotient + half).to_integer();
    Number reduced = value - Number(quadrant_index) * half_pi;
    unsigned quadrant = trans_mod4(quadrant_index);

    if(reduced.is_zero()){
        if(quadrant == 0) return trig_pair_t{Number(0), Number(1)};
        if(quadrant == 1) return trig_pair_t{Number(1), Number(0)};
        if(quadrant == 2) return trig_pair_t{Number(0), Number(-1)};
        return trig_pair_t{Number(-1), Number(0)};
    }

    Number one(1);
    one.set_precision(work_precision);
    Number negative_square = -(reduced * reduced);
    Number sine_term = reduced;
    Number sine_sum = reduced;
    Number cosine_term = one;
    Number cosine_sum = one;
    size_t limit = checked_count(std::ceil(work_precision)) + 32;
    for(size_t n = 1; n <= limit; ++n){
        size_t twice = n * 2;
        if(twice < n || twice == SIZE_MAX) std::abort();
        sine_term = (sine_term * negative_square) /
                    Number(trig_denominator(twice, twice + 1));
        cosine_term = (cosine_term * negative_square) /
                      Number(trig_denominator(twice - 1, twice));
        sine_sum += sine_term;
        cosine_sum += cosine_term;
        bool sine_done = term_is_small(sine_term, sine_sum, work_precision);
        bool cosine_done = term_is_small(cosine_term, cosine_sum, work_precision);
        if(sine_done && cosine_done) break;
        if(n == limit) std::abort();
    }

    Number sine, cosine;
    if(quadrant == 0){ sine = sine_sum; cosine = cosine_sum; }
    else if(quadrant == 1){ sine = cosine_sum; cosine = -sine_sum; }
    else if(quadrant == 2){ sine = -sine_sum; cosine = -cosine_sum; }
    else{ sine = -cosine_sum; cosine = sine_sum; }
    sine.set_precision(target_precision);
    cosine.set_precision(target_precision);
    return trig_pair_t{std::move(sine), std::move(cosine)};
}

} // namespace

Number sin(const Number &a){
    return trig_pair(a).sine;
}

Number cos(const Number &a){
    return trig_pair(a).cosine;
}

Number tan(const Number &a){
    double target_precision = trans_precision(a);
    trig_pair_t pair = trig_pair(a);
    if(pair.cosine.is_zero()) std::abort();
    Number result = pair.sine / pair.cosine;
    result.set_precision(target_precision);
    return result;
}

namespace{

static Number trans_pi(double precision){
    long double digits =
        std::ceil((long double)precision * 0.30102999566398119521L) + 8.0L;
    if(digits < 1.0L || digits > (long double)INT_MAX) std::abort();
    Number result = getpi((int)digits);
    result.set_precision(precision);
    return result;
}

static Number atan_positive(Number x, double target_precision){
    Number one(1);
    bool reciprocal = x > one;
    size_t shifts = checked_count(std::ceil(std::sqrt(target_precision))) + 2;
    double work_precision = target_precision + (double)shifts * 2.0 + 128.0;
    x.set_precision(work_precision);
    one.set_precision(work_precision);
    if(reciprocal) x = one / x;

    // tan(theta/2) = tan(theta)/(1 + sqrt(1 + tan(theta)^2)). Repeating
    // this makes the alternating atan series short without changing quadrant.
    for(size_t i = 0; i < shifts; ++i)
        x = x / (one + sqrt(one + x * x));

    Number negative_square = -(x * x);
    Number term = x;
    Number sum = x;
    size_t limit = checked_count(std::ceil(work_precision)) + 32;
    for(size_t n = 1; n <= limit; ++n){
        if(n > (SIZE_MAX - 1) / 2) std::abort();
        term *= negative_square;
        Number add = term / Number((uint64_t)(n * 2 + 1));
        sum += add;
        if(term_is_small(add, sum, work_precision)) break;
        if(n == limit) std::abort();
    }
    Number result = sum << (int64_t)shifts;
    if(reciprocal) result = (trans_pi(work_precision) >> 1) - result;
    result.set_precision(target_precision);
    return result;
}

} // namespace

Number atan(const Number &a){
    if(a.is_zero()) return a;
    double target_precision = trans_precision(a);
    Number result = atan_positive(abs(a), target_precision);
    return a.is_negative() ? -result : result;
}

Number asin(const Number &a){
    Number one(1);
    if(a < -one || a > one) std::abort();
    if(a.is_zero()) return a;

    double target_precision = trans_precision(a);
    double work_precision = target_precision + 96.0;
    Number x = a;
    x.set_precision(work_precision);
    one.set_precision(work_precision);
    // asin(x) = 2 atan(x/(1 + sqrt(1 - x^2))). This remains well behaved
    // at both endpoints and avoids subtracting the answer from pi/2.
    Number root = sqrt(one - x * x);
    Number result = atan(x / (one + root)) << 1;
    result.set_precision(target_precision);
    return result;
}

Number acos(const Number &a){
    Number one(1);
    if(a < -one || a > one) std::abort();
    if(a == one) return Number(0);

    double target_precision = trans_precision(a);
    double work_precision = target_precision + 96.0;
    if(a == -one){
        Number result = trans_pi(work_precision);
        result.set_precision(target_precision);
        return result;
    }

    Number x = a;
    x.set_precision(work_precision);
    one.set_precision(work_precision);
    // acos(x) = 2 atan(sqrt((1 - x)/(1 + x))). Unlike pi/2 - asin(x),
    // this retains relative accuracy when x is close to one.
    Number ratio = (one - x) / (one + x);
    Number result = atan(sqrt(ratio)) << 1;
    result.set_precision(target_precision);
    return result;
}

namespace{

struct hyperbolic_seed_t{
    Number sine;
    Number cosine;
    size_t shifts;
    double target_precision;
    double work_precision;
};

static hyperbolic_seed_t hyperbolic_seed(const Number &a){
    double target_precision = trans_precision(a);
    long double logx = trans_log2_abs(a);
    size_t magnitude_shifts = logx > -1.0L
        ? checked_count(std::ceil(logx + 1.0L)) : 0;
    size_t series_shifts = checked_count(std::ceil(std::sqrt(target_precision))) + 2;
    if(magnitude_shifts > (size_t)INT64_MAX - series_shifts) std::abort();
    size_t shifts = magnitude_shifts + series_shifts;
    double work_precision = target_precision + (double)shifts * 2.0 + 128.0;

    Number reduced = a;
    reduced.set_precision(work_precision);
    reduced >>= (int64_t)shifts;
    Number one(1);
    one.set_precision(work_precision);
    Number square = reduced * reduced;
    Number sine_term = reduced;
    Number sine_sum = reduced;
    Number cosine_term = one;
    Number cosine_sum = one;
    size_t limit = checked_count(std::ceil(work_precision)) + 32;
    for(size_t n = 1; n <= limit; ++n){
        size_t twice = n * 2;
        if(twice < n || twice == SIZE_MAX) std::abort();
        sine_term = (sine_term * square) /
                    Number(trig_denominator(twice, twice + 1));
        cosine_term = (cosine_term * square) /
                      Number(trig_denominator(twice - 1, twice));
        sine_sum += sine_term;
        cosine_sum += cosine_term;
        bool sine_done = term_is_small(sine_term, sine_sum, work_precision);
        bool cosine_done = term_is_small(cosine_term, cosine_sum, work_precision);
        if(sine_done && cosine_done) break;
        if(n == limit) std::abort();
    }
    return hyperbolic_seed_t{std::move(sine_sum), std::move(cosine_sum),
                             shifts, target_precision, work_precision};
}

static Number atanh_reduced(Number x, double target_precision){
    Number one(1);
    Number magnitude = abs(x);
    if(magnitude >= one) std::abort();
    if(x.is_zero()) return x;

    // Near +/-1, atanh(x) is large. Account for that magnitude before the
    // usual precision-balanced half-angle reductions.
    Number distance = one - magnitude;
    long double near_bits = std::max(0.0L, -trans_log2_abs(distance));
    size_t magnitude_shifts = near_bits > 1.0L
        ? checked_count(std::ceil(std::log2(near_bits + 1.0L))) + 2 : 2;
    size_t series_shifts = checked_count(std::ceil(std::sqrt(target_precision))) + 2;
    if(magnitude_shifts > (size_t)INT64_MAX - series_shifts) std::abort();
    size_t shifts = magnitude_shifts + series_shifts;
    double work_precision = target_precision + (double)shifts * 2.0 + 128.0;
    x.set_precision(work_precision);
    one.set_precision(work_precision);

    // tanh(y/2) = tanh(y)/(1 + sqrt(1 - tanh(y)^2)).
    for(size_t i = 0; i < shifts; ++i)
        x = x / (one + sqrt(one - x * x));

    Number square = x * x;
    Number term = x;
    Number sum = x;
    size_t limit = checked_count(std::ceil(work_precision)) + 32;
    for(size_t n = 1; n <= limit; ++n){
        if(n > (SIZE_MAX - 1) / 2) std::abort();
        term *= square;
        Number add = term / Number((uint64_t)(n * 2 + 1));
        sum += add;
        if(term_is_small(add, sum, work_precision)) break;
        if(n == limit) std::abort();
    }
    Number result = sum << (int64_t)shifts;
    result.set_precision(target_precision);
    return result;
}

} // namespace

Number sinh(const Number &a){
    if(a.is_zero()) return a;
    hyperbolic_seed_t seed = hyperbolic_seed(a);
    Number sine = std::move(seed.sine);
    Number cosine = std::move(seed.cosine);
    for(size_t i = 0; i < seed.shifts; ++i){
        Number next_sine = (sine * cosine) << 1;
        Number next_cosine = cosine * cosine + sine * sine;
        sine = std::move(next_sine);
        cosine = std::move(next_cosine);
    }
    sine.set_precision(seed.target_precision);
    return sine;
}

Number cosh(const Number &a){
    if(a.is_zero()) return Number(1);
    hyperbolic_seed_t seed = hyperbolic_seed(a);
    Number sine = std::move(seed.sine);
    Number cosine = std::move(seed.cosine);
    for(size_t i = 0; i < seed.shifts; ++i){
        Number next_sine = (sine * cosine) << 1;
        Number next_cosine = cosine * cosine + sine * sine;
        sine = std::move(next_sine);
        cosine = std::move(next_cosine);
    }
    cosine.set_precision(seed.target_precision);
    return cosine;
}

Number tanh(const Number &a){
    if(a.is_zero()) return a;
    hyperbolic_seed_t seed = hyperbolic_seed(a);
    Number value = seed.sine / seed.cosine;
    Number one(1);
    one.set_precision(seed.work_precision);
    // Reconstruct tanh directly. Unlike sinh/cosh, this stays bounded even
    // when the original argument is very large.
    for(size_t i = 0; i < seed.shifts; ++i)
        value = (value << 1) / (one + value * value);
    value.set_precision(seed.target_precision);
    return value;
}

Number atanh(const Number &a){
    return atanh_reduced(a, trans_precision(a));
}

Number asinh(const Number &a){
    if(a.is_zero()) return a;
    double target_precision = trans_precision(a);
    double work_precision = target_precision + 96.0;
    Number x = a;
    x.set_precision(work_precision);
    Number one(1);
    one.set_precision(work_precision);
    Number result = atanh(x / (one + sqrt(one + x * x))) << 1;
    result.set_precision(target_precision);
    return result;
}

Number acosh(const Number &a){
    Number one(1);
    if(a < one) std::abort();
    if(a == one) return Number(0);
    double target_precision = trans_precision(a);
    double work_precision = target_precision + 96.0;
    Number x = a;
    x.set_precision(work_precision);
    one.set_precision(work_precision);
    Number two(2);
    two.set_precision(work_precision);
    Number result = asinh(sqrt((x - one) / two)) << 1;
    result.set_precision(target_precision);
    return result;
}

Number gete(int digits){
    if(digits <= 0) std::abort();
    // Function-local static initialization is thread-safe since C++11. Small
    // requests return normalized copies and never recompute the 1000-digit e.
    static const Number cached_e = calculate_e(e_cache_digits);
    double precision = std::ceil(((double)digits + 2.0) *
                                 3.32192809488736234787);
    if(digits <= e_cache_digits){
        Number result = cached_e;
        result.set_precision(precision);
        return result;
    }
    return calculate_e(digits);
}
