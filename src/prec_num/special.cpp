#include"../../prec_num.hpp"

#include<algorithm>
#include<cmath>
#include<cstdlib>

namespace{

static double special_precision(const Number &a){
    double p = a.is_exact() ? 64.0 : a.precision();
    if(!std::isfinite(p) || p < 1.0) std::abort();
    return p;
}

static double special_precision(const Number &a, const Number &b){
    if(a.is_exact()) return special_precision(b);
    if(b.is_exact()) return special_precision(a);
    return std::min(special_precision(a), special_precision(b));
}

static bool converged(const Number &term, const Number &sum, double bits){
    if(term.is_zero()) return true;
    if(sum.is_zero()) return false;
    return abs(term) <= (abs(sum) >> (int64_t)(std::ceil(bits) + 12.0));
}

static Number decimal_constant(const char *digits, size_t fractional,
                               double precision){
    precn_t numerator(digits), denominator(1);
    for(size_t i = 0; i < fractional; ++i) denominator = mul_u64(denominator, 10);
    Number result(numerator);
    result.set_precision(precision + 32.0);
    Number divisor(denominator);
    divisor.set_precision(precision + 32.0);
    result /= divisor;
    result.set_precision(precision);
    return result;
}

static Number gamma_spouge(const Number &argument, double precision);

static Number euler_gamma(double precision){
    static const char digits[] =
        "57721566490153286060651209008240243104215933593992359880576723488486"
        "77267776646709369470632917467495146314472498070824809605040144865428"
        "36224173997644923536253500333742937337737673942792595258247094916008"
        "73520394816567085323315177661152862119950150798479374508570574002992"
        "13547861466940296043254215190587755352673313992540129674205137541395";
    if(precision <= 1000.0)
        return decimal_constant(digits, sizeof(digits) - 1, precision);

    // gamma = -Gamma'(1). A symmetric difference has O(h^2) truncation;
    // evaluate Gamma with enough cancellation guard to retain the requested
    // bits after division by h.
    int64_t shift = (int64_t)std::ceil(precision * 0.5 + 24.0);
    double work = precision + (double)shift + 128.0;
    Number one(1);
    one.set_precision(work);
    Number h = one >> shift;
    h.set_precision(work);
    Number derivative = (gamma_spouge(one + h, work) -
                         gamma_spouge(one - h, work)) / (h << 1);
    Number result = -derivative;
    result.set_precision(precision);
    return result;
}

static Number gamma_spouge(const Number &argument, double precision){
    if(argument <= Number(0)) std::abort();
    size_t count = (size_t)std::ceil(precision * 0.45 + 16.0);
    // Spouge coefficients are much larger than their final sum. Preserve the
    // cancellation bits instead of letting Number's precision tracking round
    // the coefficient sum too early.
    double work = precision + (double)count * std::log2((double)count) + 128.0;
    Number z = argument - Number(1);
    z.set_precision(work);
    Number pi = getpi((int)std::ceil(work / 3.32192809488736234787) + 4);
    pi.set_precision(work);
    Number sum = sqrt((pi * Number(2)));
    sum.set_precision(work);
    Number factorial(1);
    factorial.set_precision(work);
    for(size_t k = 1; k < count; ++k){
        Number ak((uint64_t)(count - k));
        ak.set_precision(work);
        Number exponent((uint64_t)k);
        exponent.set_precision(work);
        Number half = Number(1) / Number(2);
        half.set_precision(work);
        exponent -= half;
        Number coefficient = exp(ak) * pow(ak, exponent) / factorial;
        if((k & 1) == 0) coefficient = -coefficient;
        sum += coefficient / (z + Number((uint64_t)k));
        factorial *= Number((uint64_t)k);
    }
    Number t = z + Number((uint64_t)count);
    t.set_precision(work);
    Number half = Number(1) / Number(2);
    half.set_precision(work);
    Number exponent = z + half;
    exponent.set_precision(work);
    Number result = pow(t, exponent) * exp(-t) * sum;
    result.set_precision(precision);
    return result;
}

static Number upper_gamma_cf(const Number &a, const Number &x,
                             double precision){
    double work = precision + 64.0;
    Number tiny = Number(1) >> (int64_t)(std::ceil(work) + 32.0);
    Number b = x + Number(1) - a;
    Number c = Number(1) / tiny;
    Number d = Number(1) / b;
    Number h = d;
    for(size_t i = 1; i < (size_t)std::ceil(work * 2.0) + 64; ++i){
        Number ni((uint64_t)i);
        Number an = -(ni * (ni - a));
        b += Number(2);
        d = an * d + b;
        if(abs(d) < tiny) d = tiny;
        c = b + an / c;
        if(abs(c) < tiny) c = tiny;
        d = Number(1) / d;
        Number delta = d * c;
        h *= delta;
        if(converged(delta - Number(1), Number(1), precision)) break;
    }
    Number result = exp(a * ln(x) - x) * h;
    result.set_precision(precision);
    return result;
}

} // namespace

Number partial_gamma(const Number &a, const Number &x){
    if(a <= Number(0) || x.is_negative()) std::abort();
    double precision = special_precision(a, x);
    if(x.is_zero()) return gamma_spouge(a, precision);
    if(x >= a + Number(1)) return upper_gamma_cf(a, x, precision);

    double work = precision + 64.0;
    Number term = Number(1) / a;
    Number sum = term;
    for(size_t n = 1; n < (size_t)std::ceil(work * 2.0) + 64; ++n){
        term *= x / (a + Number((uint64_t)n));
        sum += term;
        if(converged(term, sum, precision)) break;
    }
    Number lower = exp(a * ln(x) - x) * sum;
    Number result = gamma_spouge(a, work) - lower;
    result.set_precision(precision);
    return result;
}

Number erf(const Number &x){
    if(x.is_zero()) return x;
    double precision = special_precision(x);
    bool negative = x.is_negative();
    Number y = abs(x);
    Number half = Number(1) / Number(2);
    half.set_precision(precision + 48.0);
    Number root_pi = sqrt(getpi((int)std::ceil(precision / 3.32192809488736234787) + 8));
    root_pi.set_precision(precision + 48.0);
    Number result = Number(1) - partial_gamma(half, y * y) / root_pi;
    if(negative) result = -result;
    result.set_precision(precision);
    return result;
}

Number erfi(const Number &x){
    if(x.is_zero()) return x;
    double precision = special_precision(x);
    double work = precision + 48.0;
    Number xx = x * x;
    Number term = x;
    Number sum = term;
    int64_t magnitude_bits = x.radix_point();
    if(magnitude_bits < 0) magnitude_bits = -magnitude_bits;
    size_t limit = (size_t)std::ceil(work) +
        (size_t)std::min<int64_t>(magnitude_bits * magnitude_bits, 1000000) +
        256;
    for(size_t k = 1; k < limit; ++k){
        uint64_t two_k = (uint64_t)(2 * k);
        term *= xx * Number(two_k - 1) /
                (Number((uint64_t)k) * Number(two_k + 1));
        sum += term;
        if(converged(term, sum, precision)) break;
    }
    Number root_pi = sqrt(getpi((int)std::ceil(precision / 3.32192809488736234787) + 8));
    Number result = Number(2) * sum / root_pi;
    result.set_precision(precision);
    return result;
}

Number Si(const Number &x){
    if(x.is_zero()) return x;
    double precision = special_precision(x);
    Number y = abs(x);
    Number result;
    Number asymptotic_cutoff((uint64_t)std::ceil(precision));
    if(y < asymptotic_cutoff){
        Number xx = y * y;
        Number term = y;
        Number sum = term;
        for(size_t k = 1; k < (size_t)std::ceil(precision) + 64; ++k){
            uint64_t two_k = (uint64_t)(2 * k);
            term *= -xx * Number(two_k - 1) /
                    (Number(two_k) * Number(two_k + 1) * Number(two_k + 1));
            sum += term;
            if(converged(term, sum, precision)) break;
        }
        result = sum;
    }else{
        Number inv = Number(1) / y;
        Number inv2 = inv * inv;
        Number fterm = inv, f = fterm;
        Number gterm = inv2, g = gterm;
        Number previous = abs(fterm);
        for(size_t k = 1; k < (size_t)std::ceil(precision) + 32; ++k){
            fterm *= -inv2 * Number((uint64_t)(2*k)) * Number((uint64_t)(2*k-1));
            gterm *= -inv2 * Number((uint64_t)(2*k+1)) * Number((uint64_t)(2*k));
            if(abs(fterm) > previous) break;
            f += fterm; g += gterm; previous = abs(fterm);
            if(converged(fterm, f, precision) && converged(gterm, g, precision)) break;
        }
        Number pi = getpi((int)std::ceil(precision / 3.32192809488736234787) + 8);
        result = pi / Number(2) - cos(y) * f - sin(y) * g;
    }
    if(x.is_negative()) result = -result;
    result.set_precision(precision);
    return result;
}

Number Ci(const Number &x){
    if(x <= Number(0)) std::abort();
    double precision = special_precision(x);
    Number result;
    Number asymptotic_cutoff((uint64_t)std::ceil(precision));
    if(x < asymptotic_cutoff){
        Number xx = x * x;
        Number term = -xx / Number(4);
        Number sum = term;
        for(size_t k = 2; k < (size_t)std::ceil(precision) + 64; ++k){
            uint64_t two_k = (uint64_t)(2 * k);
            term *= -xx * Number(two_k - 2) /
                    (Number(two_k - 1) * Number(two_k) * Number(two_k));
            sum += term;
            if(converged(term, sum, precision)) break;
        }
        result = euler_gamma(precision + 32.0) + ln(x) + sum;
    }else{
        Number inv = Number(1) / x, inv2 = inv * inv;
        Number fterm = inv, f = fterm;
        Number gterm = inv2, g = gterm;
        Number previous = abs(fterm);
        for(size_t k = 1; k < (size_t)std::ceil(precision) + 32; ++k){
            fterm *= -inv2 * Number((uint64_t)(2*k)) * Number((uint64_t)(2*k-1));
            gterm *= -inv2 * Number((uint64_t)(2*k+1)) * Number((uint64_t)(2*k));
            if(abs(fterm) > previous) break;
            f += fterm; g += gterm; previous = abs(fterm);
        }
        result = sin(x) * f - cos(x) * g;
    }
    result.set_precision(precision);
    return result;
}

Number Ei(const Number &x){
    if(x.is_zero()) std::abort();
    double precision = special_precision(x);
    if(x.is_negative()){
        Number result = -upper_gamma_cf(Number(0), -x, precision);
        result.set_precision(precision);
        return result;
    }
    Number term = x;
    Number sum = term;
    for(size_t k = 2; k < (size_t)std::ceil(precision * 2.0) + 128; ++k){
        term *= x * Number((uint64_t)(k - 1)) /
                (Number((uint64_t)k) * Number((uint64_t)k));
        sum += term;
        if(converged(term, sum, precision)) break;
    }
    Number result = euler_gamma(precision + 32.0) + ln(x) + sum;
    result.set_precision(precision);
    return result;
}
