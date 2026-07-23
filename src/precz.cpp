#include"../prec.hpp"

#include<utility>

precz_t::precz_t(precn_t mag, bool neg) : mag_(std::move(mag)), neg_(neg){
    if(mag_.rsiz == 0) neg_ = false;
}

precz_t::precz_t() : mag_(), neg_(false){}

precz_t::precz_t(const precn_t &mag) : mag_(mag), neg_(false){}

precz_t::precz_t(precn_t &&mag) : mag_(std::move(mag)), neg_(false){}

precz_t::precz_t(std::string val) : mag_(val), neg_(false){
    size_t p = 0;
    while(p < val.size() && (val[p] == ' ' || val[p] == '\t' ||
                             val[p] == '\n' || val[p] == '\r')) ++p;
    neg_ = p < val.size() && val[p] == '-' && mag_.rsiz != 0;
}

bool precz_t::is_negative() const{ return neg_; }
bool precz_t::is_zero() const{ return mag_.rsiz == 0; }
const precn_t &precz_t::magnitude() const{ return mag_; }

precz_t::operator std::string() const{
    std::string s = (std::string)mag_;
    if(neg_) s.insert(s.begin(), '-');
    return s;
}

precz_t operator+(const precz_t &a, const precz_t &b){
    if(a.neg_ == b.neg_) return precz_t(a.mag_ + b.mag_, a.neg_);
    if(a.mag_ >= b.mag_) return precz_t(a.mag_ - b.mag_, a.neg_);
    return precz_t(b.mag_ - a.mag_, b.neg_);
}

precz_t operator-(const precz_t &a, const precz_t &b){ return a + (-b); }

precz_t operator-(const precz_t &a){ return precz_t(a.mag_, !a.neg_); }

precz_t operator+(const precz_t &a){ return a; }

precz_t operator*(const precz_t &a, const precz_t &b){
    return precz_t(a.mag_ * b.mag_, a.neg_ != b.neg_);
}

precz_t operator/(const precz_t &a, const precz_t &b){
    return precz_t(a.mag_ / b.mag_, a.neg_ != b.neg_);
}

precz_t operator%(const precz_t &a, const precz_t &b){
    return precz_t(a.mag_ % b.mag_, a.neg_);
}

precz_t operator<<(const precz_t &a, size_t bits){
    return precz_t(a.mag_ << bits, a.neg_);
}

precz_t operator>>(const precz_t &a, size_t bits){
    return precz_t(a.mag_ >> bits, a.neg_);
}

bool operator==(const precz_t &a, const precz_t &b){
    return a.neg_ == b.neg_ && a.mag_ == b.mag_;
}

bool operator!=(const precz_t &a, const precz_t &b){ return !(a == b); }

bool operator<(const precz_t &a, const precz_t &b){
    if(a.neg_ != b.neg_) return a.neg_;
    return a.neg_ ? a.mag_ > b.mag_ : a.mag_ < b.mag_;
}

bool operator>(const precz_t &a, const precz_t &b){ return b < a; }
bool operator<=(const precz_t &a, const precz_t &b){ return !(b < a); }
bool operator>=(const precz_t &a, const precz_t &b){ return !(a < b); }

precz_t &precz_t::operator+=(const precz_t &o){ return *this = *this + o; }
precz_t &precz_t::operator-=(const precz_t &o){ return *this = *this - o; }
precz_t &precz_t::operator*=(const precz_t &o){ return *this = *this * o; }
precz_t &precz_t::operator/=(const precz_t &o){ return *this = *this / o; }
precz_t &precz_t::operator%=(const precz_t &o){ return *this = *this % o; }
precz_t &precz_t::operator<<=(size_t bits){ return *this = *this << bits; }
precz_t &precz_t::operator>>=(size_t bits){ return *this = *this >> bits; }

precz_t operator++(precz_t &a){ a += precz_t(1); return a; }
precz_t operator++(precz_t &a, int){ precz_t old(a); ++a; return old; }
precz_t operator--(precz_t &a){ a -= precz_t(1); return a; }
precz_t operator--(precz_t &a, int){ precz_t old(a); --a; return old; }

precz_t abs(const precz_t &a){ return precz_t(a.mag_, false); }

precz_t gcd(const precz_t &a, const precz_t &b){
    return precz_t(::gcd(a.mag_, b.mag_), false);
}

precz_t precz_sqrt(const precz_t &a){
    if(a.neg_) return precz_t();
    return precz_t(precn_sqrt(a.mag_), false);
}
