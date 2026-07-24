#include"../prec.hpp"

#include<utility>

static bool precq_token_negative(const std::string &s){
    size_t p = 0;
    while(p < s.size() && (s[p] == ' ' || s[p] == '\t' ||
                           s[p] == '\n' || s[p] == '\r')) ++p;
    return p < s.size() && s[p] == '-';
}

void precq_t::normalize(){
    if(den_.rsiz == 0) std::abort();
    if(num_.rsiz == 0){
        den_ = precn_t(1);
        neg_ = false;
        return;
    }

    precn_t g = gcd(num_, den_);
    if(g != precn_t(1)){
        num_ = num_ / g;
        den_ = den_ / g;
    }
}

precq_t::precq_t(precn_t num, precn_t den, bool negative)
    : num_(std::move(num)), den_(std::move(den)), neg_(negative){
    normalize();
}

precq_t::precq_t() : num_(), den_(1), neg_(false){}

precq_t::precq_t(const precn_t &num) : num_(num), den_(1), neg_(false){}

precq_t::precq_t(const precz_t &num)
    : num_(num.magnitude()), den_(1), neg_(num.is_negative()){}

precq_t::precq_t(const precz_t &num, const precn_t &den)
    : num_(num.magnitude()), den_(den), neg_(num.is_negative()){
    normalize();
}

precq_t::precq_t(std::string val) : num_(), den_(1), neg_(false){
    size_t slash = val.find('/');
    std::string ns = slash == std::string::npos ? val : val.substr(0, slash);
    std::string ds = slash == std::string::npos ? std::string("1") : val.substr(slash + 1);
    num_ = precn_t(ns);
    den_ = precn_t(ds);
    neg_ = precq_token_negative(ns) != precq_token_negative(ds);
    normalize();
}

bool precq_t::is_negative() const{ return neg_; }
bool precq_t::is_zero() const{ return num_.rsiz == 0; }
const precn_t &precq_t::numerator() const{ return num_; }
const precn_t &precq_t::denominator() const{ return den_; }

precq_t::operator std::string() const{
    std::string s;
    if(neg_) s.push_back('-');
    s += (std::string)num_;
    s.push_back('/');
    s += (std::string)den_;
    return s;
}

precq_t operator+(const precq_t &a, const precq_t &b){
    precn_t g = gcd(a.den_, b.den_);
    precn_t ad = a.den_ / g;
    precn_t bd = b.den_ / g;
    precn_t left = a.num_ * bd;
    precn_t right = b.num_ * ad;
    precn_t den = ad * b.den_;

    if(a.neg_ == b.neg_) return precq_t(left + right, std::move(den), a.neg_);
    if(left >= right) return precq_t(left - right, std::move(den), a.neg_);
    return precq_t(right - left, std::move(den), b.neg_);
}

precq_t operator-(const precq_t &a, const precq_t &b){ return a + (-b); }

precq_t operator-(const precq_t &a){ return precq_t(a.num_, a.den_, !a.neg_); }

precq_t operator+(const precq_t &a){ return a; }

precq_t operator*(const precq_t &a, const precq_t &b){
    precn_t g1 = gcd(a.num_, b.den_);
    precn_t g2 = gcd(b.num_, a.den_);
    precn_t num = (a.num_ / g1) * (b.num_ / g2);
    precn_t den = (a.den_ / g2) * (b.den_ / g1);
    return precq_t(std::move(num), std::move(den), a.neg_ != b.neg_);
}

precq_t operator/(const precq_t &a, const precq_t &b){
    if(b.num_.rsiz == 0) std::abort();
    precn_t g1 = gcd(a.num_, b.num_);
    precn_t g2 = gcd(b.den_, a.den_);
    precn_t num = (a.num_ / g1) * (b.den_ / g2);
    precn_t den = (a.den_ / g2) * (b.num_ / g1);
    return precq_t(std::move(num), std::move(den), a.neg_ != b.neg_);
}

bool operator==(const precq_t &a, const precq_t &b){
    return a.neg_ == b.neg_ && a.num_ == b.num_ && a.den_ == b.den_;
}

bool operator!=(const precq_t &a, const precq_t &b){ return !(a == b); }

bool operator<(const precq_t &a, const precq_t &b){
    if(a.neg_ != b.neg_) return a.neg_;
    precn_t left = a.num_ * b.den_;
    precn_t right = b.num_ * a.den_;
    return a.neg_ ? left > right : left < right;
}

bool operator>(const precq_t &a, const precq_t &b){ return b < a; }
bool operator<=(const precq_t &a, const precq_t &b){ return !(b < a); }
bool operator>=(const precq_t &a, const precq_t &b){ return !(a < b); }

precq_t &precq_t::operator+=(const precq_t &o){ return *this = *this + o; }
precq_t &precq_t::operator-=(const precq_t &o){ return *this = *this - o; }
precq_t &precq_t::operator*=(const precq_t &o){ return *this = *this * o; }
precq_t &precq_t::operator/=(const precq_t &o){ return *this = *this / o; }

precq_t abs(const precq_t &a){ return precq_t(a.num_, a.den_, false); }

precq_t reciprocal(const precq_t &a){
    if(a.num_.rsiz == 0) std::abort();
    return precq_t(a.den_, a.num_, a.neg_);
}
