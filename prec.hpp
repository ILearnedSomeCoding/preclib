#include<cstdio>
#include<cmath>
#include<cstring>
#include<algorithm>
#include<cstdlib>
#include<type_traits>
#include<string>
#include<cstdint>
struct precn_t{  // unsigned arbitrary precision number, base 2^32
    size_t asiz; // allocated size
    size_t rsiz; // real size
    uint32_t *a; // array
    precn_t();
    template<class T, typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
    precn_t(T val){
        a = (uint32_t*) malloc(4);
        asiz = 1;
        rsiz = 0;
        *a = 0;

        if(std::is_signed<T>::value && val < 0) return;

        uint64_t x = (uint64_t)val;
        while(x > 0){
            if(rsiz == asiz){
                asiz *= 2;
                a = (uint32_t*) realloc(a, asiz * 4);
            }
            a[rsiz++] = (uint32_t)(x & 0xFFFFFFFFu);
            x >>= 32;
        }
    }
    precn_t(const precn_t &o);
    precn_t(precn_t &&o);
    precn_t(std::string o);
    template<class T, typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
    explicit operator T() const{
        if(rsiz == 0) return (T)0;
        uint64_t x = 0;
        for(size_t i = rsiz; i > 0; --i){
            x <<= 32;
            x |= a[i - 1];
        }
        return (T)x;
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

precn_t operator*(const precn_t &a, const precn_t &b);
void mul_into(precn_t &r, const precn_t &a, const precn_t &b);
precn_t mul_u32(const precn_t &a, uint32_t b);
precn_t precn_sqr(const precn_t &a);

precn_t operator/(const precn_t &a, const precn_t &b);
void div_into(precn_t &q, const precn_t &a, const precn_t &b);
precn_t div_schoolbook(const precn_t &a, const precn_t &b);
precn_t mod_schoolbook(const precn_t &a, const precn_t &b);
precn_t div_u32(const precn_t &a, uint32_t b);
precn_t precn_reciprocal_newton(const precn_t &b, size_t n);
precn_t div_mulinv(const precn_t &a, const precn_t &b);
precn_t mod_mulinv(const precn_t &a, const precn_t &b);
precn_t div_newton(const precn_t &a, const precn_t &b);
precn_t operator%(const precn_t &a, const precn_t &b);
void mod_into(precn_t &r, const precn_t &a, const precn_t &b);
precn_t mod_u32(const precn_t &a, uint32_t b);

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

void precn_base_convert(const precn_t &a, uint32_t base, uint32_t *out, size_t &out_siz);
