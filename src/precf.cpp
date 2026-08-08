#include"../prec.hpp"

#include<utility>

unsigned int precf_digit = 64;

static precn_t precf_pow_u32(uint32_t base, size_t exp){
    precn_t r(1);
    precn_t b(base);
    while(exp){
        if(exp & 1) r = r * b;
        exp >>= 1;
        if(exp) b = b * b;
    }
    return r;
}

static precz_t precf_signed(precn_t mag, bool negative){
    precz_t r(std::move(mag));
    return negative ? -r : r;
}

precf_t::precf_t(precz_t scaled, unsigned int digit, raw_tag_t)
    : scaled_(std::move(scaled)), digit_(digit){}

void precf_t::require_same_precision(const precf_t &a, const precf_t &b){
    if(a.digit_ != b.digit_) std::abort();
}

precf_t::precf_t() : scaled_(), digit_(precf_digit){}

precf_t::precf_t(const precn_t &val)
    : scaled_(precz_t(val) << precf_digit), digit_(precf_digit){}

precf_t::precf_t(const precz_t &val)
    : scaled_(val << precf_digit), digit_(precf_digit){}

precf_t::precf_t(std::string val) : scaled_(), digit_(precf_digit){
    size_t p = 0;
    while(p < val.size() && (val[p] == ' ' || val[p] == '\t' ||
                             val[p] == '\n' || val[p] == '\r')) ++p;

    bool negative = false;
    if(p < val.size() && (val[p] == '+' || val[p] == '-')){
        negative = val[p] == '-';
        ++p;
    }

    std::string digits;
    size_t fractional = 0;
    bool point = false;
    bool any = false;
    for(; p < val.size(); ++p){
        char c = val[p];
        if(c >= '0' && c <= '9'){
            digits.push_back(c);
            if(point) ++fractional;
            any = true;
        }else if(c == '.' && !point){
            point = true;
        }else if(c == ' ' || c == '\t' || c == '\n' || c == '\r'){
            while(p < val.size() && (val[p] == ' ' || val[p] == '\t' ||
                                     val[p] == '\n' || val[p] == '\r')) ++p;
            if(p != val.size()) std::abort();
            break;
        }else{
            std::abort();
        }
    }
    if(!any) std::abort();

    precn_t mag(digits);
    mag = mag << digit_;
    if(fractional) mag = mag / precf_pow_u32(10, fractional);
    scaled_ = precf_signed(std::move(mag), negative);
}

precf_t &precf_t::operator=(const precf_t &o){
    if(this == &o) return *this;
    require_same_precision(*this, o);
    scaled_ = o.scaled_;
    return *this;
}

precf_t &precf_t::operator=(precf_t &&o){
    if(this == &o) return *this;
    require_same_precision(*this, o);
    scaled_ = std::move(o.scaled_);
    return *this;
}

unsigned int precf_t::precision() const{ return digit_; }
bool precf_t::is_negative() const{ return scaled_.is_negative(); }
bool precf_t::is_zero() const{ return scaled_.is_zero(); }
const precz_t &precf_t::scaled_integer() const{ return scaled_; }

precf_t::operator precz_t() const{ return scaled_ >> digit_; }

precf_t::operator std::string() const{
    const precn_t &mag = scaled_.magnitude();
    precn_t integer = mag >> digit_;
    precn_t fraction = mag - (integer << digit_);
    std::string out = (std::string)integer;

    if(fraction.rsiz){
        precn_t decimal = fraction * precf_pow_u32(5, digit_);
        std::string frac = (std::string)decimal;
        if(frac.size() < digit_) frac.insert(0, digit_ - frac.size(), '0');
        while(!frac.empty() && frac.back() == '0') frac.pop_back();
        out.push_back('.');
        out += frac;
    }
    if(scaled_.is_negative() && mag.rsiz) out.insert(out.begin(), '-');
    return out;
}

precf_t operator+(const precf_t &a, const precf_t &b){
    precf_t::require_same_precision(a, b);
    return precf_t(a.scaled_ + b.scaled_, a.digit_, precf_t::raw_tag_t());
}

precf_t operator-(const precf_t &a, const precf_t &b){
    precf_t::require_same_precision(a, b);
    return precf_t(a.scaled_ - b.scaled_, a.digit_, precf_t::raw_tag_t());
}

precf_t operator-(const precf_t &a){
    return precf_t(-a.scaled_, a.digit_, precf_t::raw_tag_t());
}

precf_t operator+(const precf_t &a){ return a; }

precf_t operator*(const precf_t &a, const precf_t &b){
    precf_t::require_same_precision(a, b);
    return precf_t((a.scaled_ * b.scaled_) >> a.digit_,
                   a.digit_, precf_t::raw_tag_t());
}

precf_t operator/(const precf_t &a, const precf_t &b){
    precf_t::require_same_precision(a, b);
    if(b.scaled_.is_zero()) std::abort();
    return precf_t((a.scaled_ << a.digit_) / b.scaled_,
                   a.digit_, precf_t::raw_tag_t());
}

bool operator==(const precf_t &a, const precf_t &b){
    precf_t::require_same_precision(a, b);
    return a.scaled_ == b.scaled_;
}

bool operator!=(const precf_t &a, const precf_t &b){ return !(a == b); }

bool operator<(const precf_t &a, const precf_t &b){
    precf_t::require_same_precision(a, b);
    return a.scaled_ < b.scaled_;
}

bool operator>(const precf_t &a, const precf_t &b){ return b < a; }
bool operator<=(const precf_t &a, const precf_t &b){ return !(b < a); }
bool operator>=(const precf_t &a, const precf_t &b){ return !(a < b); }

precf_t &precf_t::operator+=(const precf_t &o){ return *this = *this + o; }
precf_t &precf_t::operator-=(const precf_t &o){ return *this = *this - o; }
precf_t &precf_t::operator*=(const precf_t &o){ return *this = *this * o; }
precf_t &precf_t::operator/=(const precf_t &o){ return *this = *this / o; }

precf_t abs(const precf_t &a){
    return precf_t(abs(a.scaled_), a.digit_, precf_t::raw_tag_t());
}
