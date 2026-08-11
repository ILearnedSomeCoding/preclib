#pragma once

#include<cstdio>
#include<cmath>
#include<cstring>
#include<algorithm>
#include<cstdlib>
#include<type_traits>
#include<string>
#include<cstdint>

#if defined(_WIN32) && defined(_MSC_VER)
#if defined(PRECLIB_BUILD_DLL)
#define PRECLIB_API __declspec(dllexport)
#elif defined(PRECLIB_USE_DLL)
#define PRECLIB_API __declspec(dllimport)
#else
#define PRECLIB_API
#endif
#elif defined(_WIN32) && defined(__GNUC__)
#if defined(PRECLIB_BUILD_DLL)
#define PRECLIB_API __attribute__((dllexport))
#elif defined(PRECLIB_USE_DLL)
#define PRECLIB_API __attribute__((dllimport))
#else
#define PRECLIB_API
#endif
#else
#define PRECLIB_API
#endif

#if defined(__SIZEOF_INT128__)
typedef unsigned __int128 uint128_t;
#endif

static inline uint64_t precn_add_carry(uint64_t a, uint64_t b, uint64_t carry, uint64_t &out){
    uint64_t s = a + b;
    uint64_t c = s < a;
    uint64_t t = s + carry;
    c += t < s;
    out = t;
    return c;
}

static inline uint64_t precn_sub_borrow(uint64_t a, uint64_t b, uint64_t borrow, uint64_t &out){
    uint64_t s = b + borrow;
    uint64_t c = s < b;
    uint64_t br = c | (a < s);
    out = a - s;
    return br;
}

static inline void precn_mul_wide(uint64_t a, uint64_t b, uint64_t &hi, uint64_t &lo){
#if defined(__SIZEOF_INT128__)
    unsigned __int128 p = (unsigned __int128)a * b;
    lo = (uint64_t)p;
    hi = (uint64_t)(p >> 64);
#else
    uint64_t a0 = (uint32_t)a, a1 = a >> 32;
    uint64_t b0 = (uint32_t)b, b1 = b >> 32;
    uint64_t p0 = a0 * b0;
    uint64_t p1 = a0 * b1;
    uint64_t p2 = a1 * b0;
    uint64_t p3 = a1 * b1;
    uint64_t mid = (p0 >> 32) + (uint32_t)p1 + (uint32_t)p2;
    lo = (mid << 32) | (uint32_t)p0;
    hi = p3 + (p1 >> 32) + (p2 >> 32) + (mid >> 32);
#endif
}

struct PRECLIB_API precn_t{  // unsigned arbitrary precision number, base 2^64
    size_t asiz; // allocated size
    size_t rsiz; // real size
    uint64_t *a; // array
    precn_t();
    template<class T, typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
    precn_t(T val){
        a = (uint64_t*) malloc(sizeof(uint64_t));
        asiz = 1;
        rsiz = 0;
        *a = 0;

        if(std::is_signed<T>::value && val < 0) std::abort();

        uint64_t x = (uint64_t)val;
        while(x > 0){
            if(rsiz == asiz){
                asiz *= 2;
                a = (uint64_t*) realloc(a, asiz * sizeof(uint64_t));
            }
            a[rsiz++] = (uint64_t)x;
            x = 0;
        }
    }
    precn_t(const precn_t &o);
    precn_t(precn_t &&o);
    precn_t(std::string o);
    template<class T, typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
    explicit operator T() const{
        return rsiz == 0 ? (T)0 : (T)a[0];
    }
    explicit operator std::string() const;
    precn_t &operator=(const precn_t &o);
    precn_t &operator=(precn_t &&o);
    ~precn_t();
};

PRECLIB_API precn_t mul_basic(const precn_t &a, const precn_t &b);
PRECLIB_API precn_t mul_karatsuba(const precn_t &a, const precn_t &b);
PRECLIB_API precn_t mul_toom(const precn_t &a, const precn_t &b);
PRECLIB_API precn_t mul_toom23(const precn_t &a, const precn_t &b);
PRECLIB_API precn_t mul_toom24(const precn_t &a, const precn_t &b);
PRECLIB_API precn_t mul_toom33(const precn_t &a, const precn_t &b);
PRECLIB_API precn_t precn_divexact_2(const precn_t &a);
PRECLIB_API precn_t precn_divexact_3(const precn_t &a);
PRECLIB_API precn_t precn_divexact(const precn_t &a, const precn_t &b);
PRECLIB_API precn_t mul_fft(const precn_t &a, const precn_t &b);
#if defined(COUNT_FFTS) && COUNT_FFTS
extern PRECLIB_API uint64_t total_fftmuls;
extern PRECLIB_API uint64_t danger_fftmuls;
extern PRECLIB_API uint64_t danger_fftmuls_1_4;
extern PRECLIB_API uint64_t danger_fftmuls_3_8;
extern PRECLIB_API double max_fft_rounding_error;
#endif
PRECLIB_API precn_t mul_ntt(const precn_t &a, const precn_t &b);
PRECLIB_API precn_t mul_ssa(const precn_t &a, const precn_t &b);

PRECLIB_API precn_t operator+(const precn_t &a, const precn_t &b);
PRECLIB_API precn_t operator-(const precn_t &a, const precn_t &b);
PRECLIB_API precn_t add_u64(const precn_t &a, uint64_t b);

template<class T, typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
static inline uint64_t precn_scalar_u64(T b){
    if(std::is_signed<T>::value && b < 0) std::abort();
    return (uint64_t)b;
}

template<class T, typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
precn_t operator+(const precn_t &a, T b){
    return add_u64(a, precn_scalar_u64(b));
}

template<class T, typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
precn_t operator+(T a, const precn_t &b){
    return add_u64(b, precn_scalar_u64(a));
}

PRECLIB_API precn_t operator*(const precn_t &a, const precn_t &b);
PRECLIB_API void mul_into(precn_t &r, const precn_t &a, const precn_t &b);
PRECLIB_API precn_t mul_u32(const precn_t &a, uint32_t b);
PRECLIB_API precn_t mul_u64(const precn_t &a, uint64_t b);
PRECLIB_API precn_t precn_sqr(const precn_t &a);

template<class T, typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
precn_t operator*(const precn_t &a, T b){
    return mul_u64(a, precn_scalar_u64(b));
}

template<class T, typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
precn_t operator*(T a, const precn_t &b){
    return mul_u64(b, precn_scalar_u64(a));
}

PRECLIB_API precn_t operator/(const precn_t &a, const precn_t &b);
PRECLIB_API void div_into(precn_t &q, const precn_t &a, const precn_t &b);
PRECLIB_API void divmod_into(precn_t &q, precn_t &r, const precn_t &a, const precn_t &b);
PRECLIB_API void divmod_schoolbook_into(precn_t &q, precn_t &r, const precn_t &a, const precn_t &b);
PRECLIB_API bool div_dc_into(precn_t &q, precn_t &r, const precn_t &a, const precn_t &b);
PRECLIB_API precn_t div_schoolbook(const precn_t &a, const precn_t &b);
PRECLIB_API precn_t mod_schoolbook(const precn_t &a, const precn_t &b);
PRECLIB_API precn_t div_u32(const precn_t &a, uint32_t b);
PRECLIB_API precn_t div_u64(const precn_t &a, uint64_t b);
PRECLIB_API precn_t precn_reciprocal_newton(const precn_t &b, size_t n);
PRECLIB_API precn_t div_mulinv(const precn_t &a, const precn_t &b);
PRECLIB_API precn_t mod_mulinv(const precn_t &a, const precn_t &b);
PRECLIB_API precn_t operator%(const precn_t &a, const precn_t &b);
PRECLIB_API void mod_into(precn_t &r, const precn_t &a, const precn_t &b);
PRECLIB_API precn_t mod_u32(const precn_t &a, uint32_t b);
PRECLIB_API precn_t mod_u64(const precn_t &a, uint64_t b);

template<class T, typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
precn_t operator/(const precn_t &a, T b){
    return div_u64(a, precn_scalar_u64(b));
}

template<class T, typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
precn_t operator/(T a, const precn_t &b){
    return precn_t(precn_scalar_u64(a)) / b;
}

template<class T, typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
precn_t operator%(const precn_t &a, T b){
    return mod_u64(a, precn_scalar_u64(b));
}

template<class T, typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
precn_t operator%(T a, const precn_t &b){
    return precn_t(precn_scalar_u64(a)) % b;
}

PRECLIB_API precn_t operator<<(const precn_t &a, size_t b);
PRECLIB_API precn_t operator>>(const precn_t &a, size_t b);

PRECLIB_API precn_t operator&(const precn_t &a, const precn_t &b);
PRECLIB_API precn_t operator|(const precn_t &a, const precn_t &b);
PRECLIB_API precn_t operator^(const precn_t &a, const precn_t &b);

// no precn_t operator~(const precn_t &a); becuz it is arbritrary, not like 2's complement precision

// precn_t operator-(const precn_t &a); becuz it is unsigned
PRECLIB_API precn_t operator+(const precn_t &a); // unary plus, which does nothing

PRECLIB_API precn_t operator++(precn_t &a); // prefix increment
PRECLIB_API precn_t operator++(precn_t &a, int); // postfix increment
PRECLIB_API precn_t operator--(precn_t &a); // prefix decrement
PRECLIB_API precn_t operator--(precn_t &a, int); // postfix decrement

PRECLIB_API bool operator==(const precn_t &a, const precn_t &b);
PRECLIB_API bool operator!=(const precn_t &a, const precn_t &b);
PRECLIB_API bool operator<(const precn_t &a, const precn_t &b);
PRECLIB_API bool operator>(const precn_t &a, const precn_t &b);
PRECLIB_API bool operator<=(const precn_t &a, const precn_t &b);
PRECLIB_API bool operator>=(const precn_t &a, const precn_t &b);

PRECLIB_API precn_t gcd(const precn_t &a, const precn_t &b);
PRECLIB_API precn_t precn_sqrt(const precn_t &a);

PRECLIB_API void precn_base_convert(const precn_t &a, uint32_t base, uint32_t *out, size_t &out_siz);

class PRECLIB_API precz_t{ // signed arbitrary precision number, sign and precn_t magnitude
    precn_t mag_;
    bool neg_;

    precz_t(precn_t mag, bool neg);

public:
    precz_t();
    template<class T, typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
    precz_t(T val) : mag_(), neg_(false){
        uint64_t bits = (uint64_t)val;
        if(std::is_signed<T>::value && val < 0){
            neg_ = true;
            bits = (uint64_t)0 - bits;
        }
        mag_ = precn_t(bits);
        if(mag_.rsiz == 0) neg_ = false;
    }
    precz_t(const precn_t &mag);
    precz_t(precn_t &&mag);
    precz_t(std::string val);

    bool is_negative() const;
    bool is_zero() const;
    const precn_t &magnitude() const;

    template<class T, typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
    explicit operator T() const{
        uint64_t bits = mag_.rsiz == 0 ? 0 : mag_.a[0];
        if(neg_) bits = (uint64_t)0 - bits;
        return (T)bits;
    }
    explicit operator std::string() const;

    precz_t &operator+=(const precz_t &o);
    precz_t &operator-=(const precz_t &o);
    precz_t &operator*=(const precz_t &o);
    precz_t &operator/=(const precz_t &o);
    precz_t &operator%=(const precz_t &o);
    precz_t &operator<<=(size_t bits);
    precz_t &operator>>=(size_t bits);

    friend PRECLIB_API precz_t operator+(const precz_t &a, const precz_t &b);
    friend PRECLIB_API precz_t operator-(const precz_t &a, const precz_t &b);
    friend PRECLIB_API precz_t operator-(const precz_t &a);
    friend PRECLIB_API precz_t operator+(const precz_t &a);
    friend PRECLIB_API precz_t operator*(const precz_t &a, const precz_t &b);
    friend PRECLIB_API precz_t operator/(const precz_t &a, const precz_t &b);
    friend PRECLIB_API precz_t operator%(const precz_t &a, const precz_t &b);
    friend PRECLIB_API precz_t operator<<(const precz_t &a, size_t bits);
    friend PRECLIB_API precz_t operator>>(const precz_t &a, size_t bits);
    friend PRECLIB_API bool operator==(const precz_t &a, const precz_t &b);
    friend PRECLIB_API bool operator<(const precz_t &a, const precz_t &b);
    friend PRECLIB_API precz_t abs(const precz_t &a);
    friend PRECLIB_API precz_t gcd(const precz_t &a, const precz_t &b);
    friend PRECLIB_API precz_t precz_sqrt(const precz_t &a);
};

PRECLIB_API precz_t operator+(const precz_t &a, const precz_t &b);
PRECLIB_API precz_t operator-(const precz_t &a, const precz_t &b);
PRECLIB_API precz_t operator-(const precz_t &a);
PRECLIB_API precz_t operator+(const precz_t &a);
PRECLIB_API precz_t operator*(const precz_t &a, const precz_t &b);
PRECLIB_API precz_t operator/(const precz_t &a, const precz_t &b);
PRECLIB_API precz_t operator%(const precz_t &a, const precz_t &b);
PRECLIB_API precz_t operator<<(const precz_t &a, size_t bits);
PRECLIB_API precz_t operator>>(const precz_t &a, size_t bits);

PRECLIB_API precz_t operator++(precz_t &a);
PRECLIB_API precz_t operator++(precz_t &a, int);
PRECLIB_API precz_t operator--(precz_t &a);
PRECLIB_API precz_t operator--(precz_t &a, int);

PRECLIB_API bool operator==(const precz_t &a, const precz_t &b);
PRECLIB_API bool operator!=(const precz_t &a, const precz_t &b);
PRECLIB_API bool operator<(const precz_t &a, const precz_t &b);
PRECLIB_API bool operator>(const precz_t &a, const precz_t &b);
PRECLIB_API bool operator<=(const precz_t &a, const precz_t &b);
PRECLIB_API bool operator>=(const precz_t &a, const precz_t &b);

PRECLIB_API precz_t abs(const precz_t &a);
PRECLIB_API precz_t gcd(const precz_t &a, const precz_t &b);
PRECLIB_API precz_t precz_sqrt(const precz_t &a); // returns zero for negative inputs
PRECLIB_API precz_t precz_divexact(const precz_t &a, const precz_t &b);

class PRECLIB_API precq_t{ // reduced signed rational: (-1)^neg_ * num_ / den_
    precn_t num_;
    precn_t den_;
    bool neg_;

    void normalize();

public:
    precq_t();
    template<class T, typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
    precq_t(T val) : num_(), den_(1), neg_(false){
        precz_t z(val);
        num_ = z.magnitude();
        neg_ = z.is_negative();
    }
    precq_t(const precn_t &num);
    precq_t(const precz_t &num);
    precq_t(precn_t num, precn_t den, bool negative = false);
    precq_t(const precz_t &num, const precn_t &den);
    precq_t(std::string val);

    bool is_negative() const;
    bool is_zero() const;
    const precn_t &numerator() const;
    const precn_t &denominator() const;
    explicit operator std::string() const;

    precq_t &operator+=(const precq_t &o);
    precq_t &operator-=(const precq_t &o);
    precq_t &operator*=(const precq_t &o);
    precq_t &operator/=(const precq_t &o);

    friend PRECLIB_API precq_t operator+(const precq_t &a, const precq_t &b);
    friend PRECLIB_API precq_t operator-(const precq_t &a, const precq_t &b);
    friend PRECLIB_API precq_t operator-(const precq_t &a);
    friend PRECLIB_API precq_t operator+(const precq_t &a);
    friend PRECLIB_API precq_t operator*(const precq_t &a, const precq_t &b);
    friend PRECLIB_API precq_t operator/(const precq_t &a, const precq_t &b);
    friend PRECLIB_API bool operator==(const precq_t &a, const precq_t &b);
    friend PRECLIB_API bool operator<(const precq_t &a, const precq_t &b);
    friend PRECLIB_API precq_t abs(const precq_t &a);
    friend PRECLIB_API precq_t reciprocal(const precq_t &a);
};

PRECLIB_API precq_t operator+(const precq_t &a, const precq_t &b);
PRECLIB_API precq_t operator-(const precq_t &a, const precq_t &b);
PRECLIB_API precq_t operator-(const precq_t &a);
PRECLIB_API precq_t operator+(const precq_t &a);
PRECLIB_API precq_t operator*(const precq_t &a, const precq_t &b);
PRECLIB_API precq_t operator/(const precq_t &a, const precq_t &b);

PRECLIB_API bool operator==(const precq_t &a, const precq_t &b);
PRECLIB_API bool operator!=(const precq_t &a, const precq_t &b);
PRECLIB_API bool operator<(const precq_t &a, const precq_t &b);
PRECLIB_API bool operator>(const precq_t &a, const precq_t &b);
PRECLIB_API bool operator<=(const precq_t &a, const precq_t &b);
PRECLIB_API bool operator>=(const precq_t &a, const precq_t &b);

PRECLIB_API precq_t abs(const precq_t &a);
PRECLIB_API precq_t reciprocal(const precq_t &a); // aborts when a is zero

extern PRECLIB_API unsigned int precf_digit;

class PRECLIB_API precf_t{ // fixed point: scaled_ * 2^(-digit_)
    precz_t scaled_;
    unsigned int digit_;

    struct raw_tag_t{};
    precf_t(precz_t scaled, unsigned int digit, raw_tag_t);
    static void require_same_precision(const precf_t &a, const precf_t &b);

public:
    precf_t();
    template<class T, typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
    precf_t(T val) : scaled_(precz_t(val) << precf_digit), digit_(precf_digit){}
    precf_t(const precn_t &val);
    precf_t(const precz_t &val);
    precf_t(std::string val);

    precf_t(const precf_t &o) = default;
    precf_t(precf_t &&o) = default;
    precf_t &operator=(const precf_t &o);
    precf_t &operator=(precf_t &&o);

    unsigned int precision() const;
    bool is_negative() const;
    bool is_zero() const;
    const precz_t &scaled_integer() const;
    explicit operator precz_t() const;
    explicit operator std::string() const;

    precf_t &operator+=(const precf_t &o);
    precf_t &operator-=(const precf_t &o);
    precf_t &operator*=(const precf_t &o);
    precf_t &operator/=(const precf_t &o);

    friend PRECLIB_API precf_t operator+(const precf_t &a, const precf_t &b);
    friend PRECLIB_API precf_t operator-(const precf_t &a, const precf_t &b);
    friend PRECLIB_API precf_t operator-(const precf_t &a);
    friend PRECLIB_API precf_t operator+(const precf_t &a);
    friend PRECLIB_API precf_t operator*(const precf_t &a, const precf_t &b);
    friend PRECLIB_API precf_t operator/(const precf_t &a, const precf_t &b);
    friend PRECLIB_API bool operator==(const precf_t &a, const precf_t &b);
    friend PRECLIB_API bool operator<(const precf_t &a, const precf_t &b);
    friend PRECLIB_API precf_t abs(const precf_t &a);
};

PRECLIB_API precf_t operator+(const precf_t &a, const precf_t &b);
PRECLIB_API precf_t operator-(const precf_t &a, const precf_t &b);
PRECLIB_API precf_t operator-(const precf_t &a);
PRECLIB_API precf_t operator+(const precf_t &a);
PRECLIB_API precf_t operator*(const precf_t &a, const precf_t &b);
PRECLIB_API precf_t operator/(const precf_t &a, const precf_t &b);

PRECLIB_API bool operator==(const precf_t &a, const precf_t &b);
PRECLIB_API bool operator!=(const precf_t &a, const precf_t &b);
PRECLIB_API bool operator<(const precf_t &a, const precf_t &b);
PRECLIB_API bool operator>(const precf_t &a, const precf_t &b);
PRECLIB_API bool operator<=(const precf_t &a, const precf_t &b);
PRECLIB_API bool operator>=(const precf_t &a, const precf_t &b);

PRECLIB_API precf_t abs(const precf_t &a);
