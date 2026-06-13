#include"../prec.hpp"

#include<complex>
#include<vector>

static const double PI = acos(-1.0);

static void fft(std::vector<std::complex<double> > &a, int inv){
    size_t n = a.size();
    for(size_t i = 1, j = 0; i < n; ++i){
        size_t bit = n >> 1;
        for(; j & bit; bit >>= 1) j ^= bit;
        j ^= bit;
        if(i < j) std::swap(a[i], a[j]);
    }

    for(size_t len = 2; len <= n; len <<= 1){
        double ang = 2.0 * PI / len * (inv ? -1.0 : 1.0);
        std::complex<double> wlen(cos(ang), sin(ang));
        for(size_t i = 0; i < n; i += len){
            std::complex<double> w(1.0, 0.0);
            for(size_t j = 0; j < len / 2; ++j){
                if((j & 1023) == 0 && j != 0) w = std::complex<double>(cos(ang * j), sin(ang * j));
                std::complex<double> u = a[i + j];
                std::complex<double> v = a[i + j + len / 2] * w;
                a[i + j] = u + v;
                a[i + j + len / 2] = u - v;
                w *= wlen;
            }
        }
    }

    if(inv){
        for(size_t i = 0; i < n; ++i) a[i] /= (double)n;
    }
}

static std::vector<int> fft_digits(const precn_t &a, int bits){
    std::vector<int> d;
    uint32_t mask = (1u << bits) - 1;
    size_t per = 32 / bits;
    d.reserve(a.rsiz * per);
    for(size_t i = 0; i < a.rsiz; ++i){
        uint32_t x = a.a[i];
        for(size_t j = 0; j < per; ++j){
            d.push_back((int)(x & mask));
            x >>= bits;
        }
    }
    while(!d.empty() && d.back() == 0) d.pop_back();
    return d;
}

static precn_t fft_from_digits(std::vector<long long> &d, int bits){
    uint32_t mask = (1u << bits) - 1;
    long long carry = 0;
    for(size_t i = 0; i < d.size(); ++i){
        long long cur = d[i] + carry;
        d[i] = cur & mask;
        carry = cur >> bits;
    }
    while(carry){
        d.push_back(carry & mask);
        carry >>= bits;
    }
    while(!d.empty() && d.back() == 0) d.pop_back();

    precn_t r;
    if(d.empty()) return r;

    size_t per = 32 / bits;
    r.rsiz = (d.size() + per - 1) / per;
    r.asiz = std::max<size_t>(r.rsiz, 1);
    r.a = (uint32_t*) realloc(r.a, r.asiz * 4);
    memset(r.a, 0, r.asiz * 4);

    for(size_t i = 0; i < d.size(); ++i){
        r.a[i / per] |= (uint32_t)d[i] << ((i % per) * bits);
    }
    while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}

static precn_t mul_fft_bits(const precn_t &a, const precn_t &b, int bits){
    std::vector<int> da = fft_digits(a, bits);
    std::vector<int> db = fft_digits(b, bits);
    if(da.empty() || db.empty()) return precn_t();

    size_t n = 1;
    while(n < da.size() + db.size()) n <<= 1;
    std::vector<std::complex<double> > fa(n), fb(n);
    for(size_t i = 0; i < da.size(); ++i) fa[i] = da[i];
    for(size_t i = 0; i < db.size(); ++i) fb[i] = db[i];

    fft(fa, 0);
    fft(fb, 0);
    for(size_t i = 0; i < n; ++i) fa[i] *= fb[i];
    fft(fa, 1);

    std::vector<long long> out(n);
    for(size_t i = 0; i < n; ++i) out[i] = (long long)llround(fa[i].real());
    return fft_from_digits(out, bits);
}

precn_t mul_fft(const precn_t &a, const precn_t &b){
    if(a.rsiz == 0 || b.rsiz == 0) return precn_t();

    size_t digits16 = std::max(a.rsiz, b.rsiz) * 2;
    if(digits16 <= (1u << 12)) return mul_fft_bits(a, b, 16);
    return mul_fft_bits(a, b, 8);
}
