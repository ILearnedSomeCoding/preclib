#include"../../prec_num.hpp"

#include<algorithm>
#include<cmath>
#include<cstdlib>
#include<limits>
#include<utility>

// Number is a signed integer times a power of 2^64. Keeping the radix point in
// limbs makes normalization cheap and lets all heavy work reuse precz_t.
static size_t number_bit_length(const precn_t &a){
    if(a.rsiz == 0) return 0;
#if defined(__clang__) || defined(__GNUC__)
    return (a.rsiz - 1) * 64 + 64 - (size_t)__builtin_clzll(a.a[a.rsiz - 1]);
#else
    size_t bits = (a.rsiz - 1) * 64;
    uint64_t top = a.a[a.rsiz - 1];
    while(top){ ++bits; top >>= 1; }
    return bits;
#endif
}

static double number_log2_abs(const Number &a){
    if(a.is_zero()) return -std::numeric_limits<double>::infinity();
    const precn_t &m = a.significand().magnitude();
    uint64_t top = m.a[m.rsiz - 1];
    // Two leading limbs are enough for an exponent/error estimate; arithmetic
    // itself never uses this floating-point approximation.
    double lead = (double)top;
    if(m.rsiz > 1) lead += std::ldexp((double)m.a[m.rsiz - 2], -64);
    return std::log2(lead) + (double)(m.rsiz - 1) * 64.0
           - (double)a.radix_point() * 64.0;
}

static precn_t number_pow_u32(uint32_t base, size_t exp){
    precn_t r(1), b(base);
    while(exp){
        if(exp & 1) r = r * b;
        exp >>= 1;
        if(exp) b = b * b;
    }
    return r;
}

static precz_t number_signed(precn_t mag, bool negative){
    precz_t r(std::move(mag));
    return negative ? -r : r;
}

static size_t number_checked_shift(int64_t limbs){
    if(limbs < 0 || (uint64_t)limbs > (uint64_t)SIZE_MAX / 64) std::abort();
    return (size_t)limbs * 64;
}

double Number::exact_precision(){
    return std::numeric_limits<double>::infinity();
}

Number::Number(precz_t significand, int64_t dotp, double precision,
               raw_tag_t)
    : significand_(std::move(significand)), dotp_(dotp), precision_(precision){
    normalize();
}

Number::Number() : significand_(), dotp_(0), precision_(exact_precision()){}
Number::Number(const precn_t &val)
    : significand_(val), dotp_(0), precision_(exact_precision()){}
Number::Number(precn_t &&val)
    : significand_(std::move(val)), dotp_(0), precision_(exact_precision()){}
Number::Number(const precz_t &val)
    : significand_(val), dotp_(0), precision_(exact_precision()){}
Number::Number(precz_t &&val)
    : significand_(std::move(val)), dotp_(0), precision_(exact_precision()){}

static Number number_from_double(double val, unsigned bits){
    if(!std::isfinite(val)) std::abort();
    if(val == 0.0) return Number::from_raw(precz_t(), 0, bits);
    bool negative = val < 0;
    double magnitude = negative ? -val : val;
    int exponent = 0;
    // frexp exposes the source's exact binary mantissa and exponent. This does
    // not round again: it embeds the existing float/double value as a dyadic.
    double fraction = std::frexp(magnitude, &exponent);
    uint64_t mantissa = (uint64_t)std::ldexp(fraction, bits);
    int64_t binary_exponent = (int64_t)exponent - bits;
    int64_t dotp = binary_exponent < 0 ? (-binary_exponent + 63) / 64 : 0;
    int64_t left = binary_exponent + dotp * 64;
    precn_t mag = precn_t(mantissa) << (size_t)left;
    return Number::from_raw(number_signed(std::move(mag), negative), dotp, bits);
}

Number::Number(float val) : Number(number_from_double((double)val, 24)){}
Number::Number(double val) : Number(number_from_double(val, 53)){}

Number Number::from_raw(precz_t significand, int64_t dotp,
                        double precision_bits){
    if(!(precision_bits > 0.0) && !std::isinf(precision_bits)) std::abort();
    return Number(std::move(significand), dotp, precision_bits, raw_tag_t());
}

bool Number::is_exact() const{ return std::isinf(precision_); }
bool Number::is_zero() const{ return significand_.is_zero(); }
bool Number::is_negative() const{ return significand_.is_negative(); }
double Number::precision() const{ return precision_; }
int64_t Number::radix_point() const{ return dotp_; }
const precz_t &Number::significand() const{ return significand_; }

double Number::combine_precision(double a, double b){
    if(std::isinf(a)) return b;
    if(std::isinf(b)) return a;
    // Multiplication/division add relative errors. Work in log2(error) so
    // operands with very different precisions do not underflow.
    double hi = std::max(-a, -b);
    double lo = std::min(-a, -b);
    return -(hi + std::log2(1.0 + std::exp2(lo - hi)));
}

void Number::normalize(){
    if(significand_.is_zero()){
        dotp_ = 0;
        return;
    }
    if(is_exact()) return;

    // Retain the requested significant limbs plus two guard limbs. Dropping
    // low limbs requires moving dotp_ in the opposite direction so the scale
    // of the surviving significand stays unchanged.
    size_t keep = (size_t)std::ceil(precision_ / 64.0) + 2;
    size_t size = significand_.magnitude().rsiz;
    if(size > keep){
        size_t drop = size - keep;
        significand_ >>= drop * 64;
        if(drop > (size_t)INT64_MAX || dotp_ < INT64_MIN + (int64_t)drop)
            std::abort();
        dotp_ -= (int64_t)drop;
    }
}

void Number::set_precision(double bits){
    if(!(bits > 0.0) && !std::isinf(bits)) std::abort();
    precision_ = bits;
    normalize();
}

precz_t Number::to_integer() const{
    if(dotp_ > 0) return significand_ >> number_checked_shift(dotp_);
    if(dotp_ < 0) return significand_ << number_checked_shift(-dotp_);
    return significand_;
}

static precn_t number_rounded_magnitude(const Number &value){
    precn_t mag = value.significand().magnitude();
    if(value.is_exact() || mag.rsiz == 0) return mag;

    size_t bits = number_bit_length(mag);
    double requested = std::max(1.0, std::floor(value.precision()));
    if((double)bits <= requested) return mag;
    size_t drop = bits - (size_t)requested;

    // Keep guard bits during arithmetic, then round the observable value to
    // its declared binary precision. Ties are rounded away from zero.
    precn_t half = precn_t(1) << (drop - 1);
    return ((mag + half) >> drop) << drop;
}

std::string Number::to_string(size_t fractional_digits) const{
    bool negative = significand_.is_negative();
    precn_t mag = number_rounded_magnitude(*this);
    if(dotp_ < 0) mag = mag << number_checked_shift(-dotp_);

    // Convert floor(abs(value) * 10^fractional_digits) as one large integer.
    // Number formatting truncates; callers such as the calculator may round.
    if(fractional_digits) mag = mag * number_pow_u32(10, fractional_digits);
    if(dotp_ > 0) mag = mag >> number_checked_shift(dotp_);

    std::string digits = (std::string)mag;
    if(fractional_digits){
        if(digits.size() <= fractional_digits)
            digits.insert(0, fractional_digits + 1 - digits.size(), '0');
        digits.insert(digits.size() - fractional_digits, 1, '.');
        while(digits.size() > 1 && digits.back() == '0') digits.pop_back();
        if(digits.back() == '.') digits.pop_back();
    }
    if(negative && mag.rsiz) digits.insert(digits.begin(), '-');
    return digits;
}

static std::string number_round_decimal(const Number &value,
                                        size_t fractional_digits){
    if(fractional_digits == SIZE_MAX) std::abort();
    std::string text = value.to_string(fractional_digits + 1);
    size_t dot = text.find('.');
    if(dot == std::string::npos){
        text.push_back('.');
        dot = text.size() - 1;
    }
    while(text.size() < dot + fractional_digits + 2) text.push_back('0');

    size_t next = dot + fractional_digits + 1;
    bool round_up = text[next] >= '5';
    text.erase(next);
    if(round_up){
        size_t position = next - 1;
        for(;;){
            if(text[position] == '.' || text[position] == '-'){
                if(position == 0) break;
                --position;
                continue;
            }
            if(text[position] != '9'){
                ++text[position];
                round_up = false;
                break;
            }
            text[position] = '0';
            if(position == 0) break;
            --position;
        }
        if(round_up) text.insert(text[0] == '-' ? 1 : 0, 1, '1');
    }
    while(text.size() > dot + 1 && text.back() == '0') text.pop_back();
    if(!text.empty() && text.back() == '.') text.pop_back();
    return text;
}

Number::operator std::string() const{
    if(is_zero()) return "0";
    if(is_exact() && dotp_ <= 0) return to_string(0);
    double decimal_precision = std::max(1.0, std::floor(precision_ * 0.3010299956639812));
    double exponent10 = std::floor(number_log2_abs(*this) * 0.3010299956639812);
    size_t fractional = exponent10 < decimal_precision
        ? (size_t)(decimal_precision - exponent10 - 1) : 0;
    return number_round_decimal(*this, fractional);
}

Number operator+(const Number &a, const Number &b){
    if(a.is_zero()) return b;
    if(b.is_zero()) return a;
    // Align both signed significands to the finer common binary scale before
    // adding. The shifts append zero limbs and therefore lose no information.
    int64_t dotp = std::max(a.dotp_, b.dotp_);
    int64_t ash = dotp - a.dotp_;
    int64_t bsh = dotp - b.dotp_;
    precz_t av = ash ? a.significand_ << number_checked_shift(ash) : a.significand_;
    precz_t bv = bsh ? b.significand_ << number_checked_shift(bsh) : b.significand_;

    if(a.is_exact() && b.is_exact())
        return Number(av + bv, dotp, Number::exact_precision(), Number::raw_tag_t());

    // Convert each relative precision into an absolute error exponent, add
    // those errors, then convert back relative to the result. This captures
    // precision loss from cancellation.
    double ea = a.is_exact() ? -std::numeric_limits<double>::infinity()
                             : number_log2_abs(a) - a.precision_;
    double eb = b.is_exact() ? -std::numeric_limits<double>::infinity()
                             : number_log2_abs(b) - b.precision_;
    Number r(av + bv, dotp, std::min(a.precision_, b.precision_), Number::raw_tag_t());
    if(r.is_zero()) return r;
    double error = std::max(ea, eb);
    if(std::isfinite(ea) && std::isfinite(eb)){
        double lo = std::min(ea, eb);
        error += std::log2(1.0 + std::exp2(lo - error));
    }
    if(std::isfinite(error)){
        r.precision_ = std::max(1.0, number_log2_abs(r) - error);
        r.normalize();
    }
    return r;
}

Number operator-(const Number &a, const Number &b){ return a + (-b); }
Number operator-(const Number &a){
    return Number(-a.significand_, a.dotp_, a.precision_, Number::raw_tag_t());
}
Number operator+(const Number &a){ return a; }

Number operator*(const Number &a, const Number &b){
    if(a.is_zero() || b.is_zero())
        return Number(precz_t(), 0, Number::combine_precision(a.precision_, b.precision_),
                      Number::raw_tag_t());
    if((b.dotp_ > 0 && a.dotp_ > INT64_MAX - b.dotp_) ||
       (b.dotp_ < 0 && a.dotp_ < INT64_MIN - b.dotp_)) std::abort();
    return Number(a.significand_ * b.significand_, a.dotp_ + b.dotp_,
                  Number::combine_precision(a.precision_, b.precision_),
                  Number::raw_tag_t());
}

Number operator/(const Number &a, const Number &b){
    if(b.is_zero()) std::abort();
    if(a.is_zero()) return Number();
    double precision = a.is_exact() && b.is_exact()
        ? 64.0 : Number::combine_precision(a.precision_, b.precision_);
    size_t target = (size_t)std::ceil(precision / 64.0) + 2;
    size_t na = a.significand_.magnitude().rsiz;
    size_t nb = b.significand_.magnitude().rsiz;
    // Integer division needs enough numerator zero limbs to leave `target`
    // quotient limbs. Include the full size deficit when the divisor's raw
    // significand is larger; omitting it would make reciprocals become zero.
    size_t extra;
    if(na >= nb){
        size_t existing = na - nb;
        extra = target > existing ? target - existing : 0;
    }else{
        size_t deficit = nb - na;
        if(deficit > SIZE_MAX - target) std::abort();
        extra = target + deficit;
    }
    if(extra > (size_t)INT64_MAX) std::abort();
    precz_t numerator = a.significand_ << (extra * 64);
    int64_t dotp = a.dotp_ - b.dotp_;
    if(dotp > INT64_MAX - (int64_t)extra) std::abort();
    dotp += (int64_t)extra;
    return Number(numerator / b.significand_, dotp, precision, Number::raw_tag_t());
}

Number operator<<(const Number &a, int64_t bits){
    if(bits == INT64_MIN) std::abort();
    if(bits < 0) return a >> -bits;
    return Number(a.significand_ << (size_t)bits, a.dotp_, a.precision_,
                  Number::raw_tag_t());
}
Number operator>>(const Number &a, int64_t bits){
    if(bits == INT64_MIN) std::abort();
    if(bits < 0) return a << -bits;
    // Encode a non-limb shift by shifting the significand left and advancing
    // dotp_ one extra limb. The represented value is divided exactly by 2^bits.
    int64_t limbs = bits / 64;
    unsigned rem = (unsigned)(bits % 64);
    if(a.dotp_ > INT64_MAX - limbs) std::abort();
    precz_t sig = rem ? a.significand_ << (64 - rem) : a.significand_;
    return Number(std::move(sig), a.dotp_ + limbs + (rem != 0), a.precision_,
                  Number::raw_tag_t());
}

static int number_compare_abs(const Number &a, const Number &b){
    size_t abits = number_bit_length(a.significand().magnitude());
    size_t bbits = number_bit_length(b.significand().magnitude());
    // Compare binary exponents first, then align only equal-sized values for
    // the exact magnitude comparison.
    long double ae = (long double)abits - (long double)a.radix_point() * 64;
    long double be = (long double)bbits - (long double)b.radix_point() * 64;
    if(ae != be) return ae < be ? -1 : 1;
    int64_t dotp = std::max(a.radix_point(), b.radix_point());
    precn_t av = a.significand().magnitude()
                 << number_checked_shift(dotp - a.radix_point());
    precn_t bv = b.significand().magnitude()
                 << number_checked_shift(dotp - b.radix_point());
    if(av == bv) return 0;
    return av < bv ? -1 : 1;
}

bool operator==(const Number &a, const Number &b){
    if(a.is_zero() || b.is_zero()) return a.is_zero() && b.is_zero();
    if(a.is_negative() != b.is_negative()) return false;
    return number_compare_abs(a, b) == 0;
}
bool operator!=(const Number &a, const Number &b){ return !(a == b); }
bool operator<(const Number &a, const Number &b){
    if(a.is_zero()) return !b.is_zero() && !b.is_negative();
    if(b.is_zero()) return a.is_negative();
    if(a.is_negative() != b.is_negative()) return a.is_negative();
    int cmp = number_compare_abs(a, b);
    return a.is_negative() ? cmp > 0 : cmp < 0;
}
bool operator>(const Number &a, const Number &b){ return b < a; }
bool operator<=(const Number &a, const Number &b){ return !(b < a); }
bool operator>=(const Number &a, const Number &b){ return !(a < b); }

Number &Number::operator+=(const Number &o){ return *this = *this + o; }
Number &Number::operator-=(const Number &o){ return *this = *this - o; }
Number &Number::operator*=(const Number &o){ return *this = *this * o; }
Number &Number::operator/=(const Number &o){ return *this = *this / o; }
Number &Number::operator<<=(int64_t bits){ return *this = *this << bits; }
Number &Number::operator>>=(int64_t bits){ return *this = *this >> bits; }

Number abs(const Number &a){
    return Number(::abs(a.significand_), a.dotp_, a.precision_, Number::raw_tag_t());
}

Number sqrt(const Number &a){
    if(a.is_negative()) std::abort();
    if(a.is_zero()) return a;
    int64_t dotp = a.dotp_;
    precn_t mag = a.significand_.magnitude();
    // Make the radix point even. Multiplying the significand by 2^64 while
    // incrementing dotp preserves the value and makes the square-root scale integral.
    if(dotp % 2 != 0){
        mag = mag << 64;
        ++dotp;
    }

    // Preserve exactness for perfect dyadic squares such as 121 and 1/4.
    if(a.is_exact()){
        precn_t exact_root = precn_sqrt(mag);
        if(precn_sqr(exact_root) == mag)
            return Number(precz_t(std::move(exact_root)), dotp / 2,
                          Number::exact_precision(), Number::raw_tag_t());
    }

    double precision = a.is_exact()
        ? std::max(64.0, number_log2_abs(a) + 64.0) : a.precision_;
    // Append pairs of limbs before integer sqrt: two input limbs become one
    // output limb, giving the root enough fractional guard precision.
    size_t target = (size_t)std::ceil(precision / 64.0) + 2;
    size_t natural = (mag.rsiz + 1) / 2;
    size_t extra = target > natural ? target - natural : 0;
    mag = mag << (extra * 128);
    precn_t root = precn_sqrt(mag);
    if(extra > (size_t)INT64_MAX || dotp / 2 > INT64_MAX - (int64_t)extra)
        std::abort();
    return Number(precz_t(std::move(root)), dotp / 2 + (int64_t)extra,
                  precision, Number::raw_tag_t());
}
