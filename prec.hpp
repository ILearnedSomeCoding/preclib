#include<cstdio>
#include<cmath>
#include<cstring>
#include<algorithm>
#include<cstdlib>
#include<type_traits>
#include<string>
#include<cstdint>

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

struct precn_t{  // unsigned arbitrary precision number, base 2^64
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

precn_t mul_basic(const precn_t &a, const precn_t &b);
precn_t mul_karatsuba(const precn_t &a, const precn_t &b);
precn_t mul_toom(const precn_t &a, const precn_t &b);
precn_t mul_toom23(const precn_t &a, const precn_t &b);
precn_t mul_toom24(const precn_t &a, const precn_t &b);
precn_t mul_toom33(const precn_t &a, const precn_t &b);
precn_t precn_divexact_2(const precn_t &a);
precn_t precn_divexact_3(const precn_t &a);
precn_t mul_fft(const precn_t &a, const precn_t &b);
precn_t mul_ntt(const precn_t &a, const precn_t &b);
precn_t mul_ssa(const precn_t &a, const precn_t &b);

precn_t operator+(const precn_t &a, const precn_t &b);
precn_t operator-(const precn_t &a, const precn_t &b);
precn_t add_u64(const precn_t &a, uint64_t b);

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

precn_t operator*(const precn_t &a, const precn_t &b);
void mul_into(precn_t &r, const precn_t &a, const precn_t &b);
precn_t mul_u32(const precn_t &a, uint32_t b);
precn_t mul_u64(const precn_t &a, uint64_t b);
precn_t precn_sqr(const precn_t &a);

template<class T, typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
precn_t operator*(const precn_t &a, T b){
    return mul_u64(a, precn_scalar_u64(b));
}

template<class T, typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
precn_t operator*(T a, const precn_t &b){
    return mul_u64(b, precn_scalar_u64(a));
}

precn_t operator/(const precn_t &a, const precn_t &b);
void div_into(precn_t &q, const precn_t &a, const precn_t &b);
void divmod_into(precn_t &q, precn_t &r, const precn_t &a, const precn_t &b);
void divmod_schoolbook_into(precn_t &q, precn_t &r, const precn_t &a, const precn_t &b);
bool div_dc_into(precn_t &q, precn_t &r, const precn_t &a, const precn_t &b);
precn_t div_schoolbook(const precn_t &a, const precn_t &b);
precn_t mod_schoolbook(const precn_t &a, const precn_t &b);
precn_t div_u32(const precn_t &a, uint32_t b);
precn_t div_u64(const precn_t &a, uint64_t b);
precn_t precn_reciprocal_newton(const precn_t &b, size_t n);
precn_t div_mulinv(const precn_t &a, const precn_t &b);
precn_t mod_mulinv(const precn_t &a, const precn_t &b);
precn_t operator%(const precn_t &a, const precn_t &b);
void mod_into(precn_t &r, const precn_t &a, const precn_t &b);
precn_t mod_u32(const precn_t &a, uint32_t b);
precn_t mod_u64(const precn_t &a, uint64_t b);

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

precn_t operator<<(const precn_t &a, size_t b);
precn_t operator>>(const precn_t &a, size_t b);

precn_t operator&(const precn_t &a, const precn_t &b);
precn_t operator|(const precn_t &a, const precn_t &b);
precn_t operator^(const precn_t &a, const precn_t &b);

// no precn_t operator~(const precn_t &a); becuz it is arbritrary, not like 2's complement precision

// precn_t operator-(const precn_t &a); becuz it is unsigned
precn_t operator+(const precn_t &a); // unary plus, which does nothing

precn_t operator++(precn_t &a); // prefix increment
precn_t operator++(precn_t &a, int); // postfix increment
precn_t operator--(precn_t &a); // prefix decrement
precn_t operator--(precn_t &a, int); // postfix decrement

bool operator==(const precn_t &a, const precn_t &b);
bool operator!=(const precn_t &a, const precn_t &b);
bool operator<(const precn_t &a, const precn_t &b);
bool operator>(const precn_t &a, const precn_t &b);
bool operator<=(const precn_t &a, const precn_t &b);
bool operator>=(const precn_t &a, const precn_t &b);

precn_t gcd(const precn_t &a, const precn_t &b);
precn_t precn_sqrt(const precn_t &a);

void precn_base_convert(const precn_t &a, uint32_t base, uint32_t *out, size_t &out_siz);
