#include"../prec.hpp"

#include<vector>

#if defined(__AVX2__) || defined(_M_AVX2)
#include<immintrin.h>
#define PRECN_FFT_HAVE_AVX2 1
#define PRECN_FFT_HAVE_SSE2 1
#elif defined(__SSE2__) || defined(_M_X64) || defined(_M_AMD64)
#include<emmintrin.h>
#define PRECN_FFT_HAVE_AVX2 0
#define PRECN_FFT_HAVE_SSE2 1
#else
#define PRECN_FFT_HAVE_AVX2 0
#define PRECN_FFT_HAVE_SSE2 0
#endif

struct fft_vec_t{
    std::vector<double> re;
    std::vector<double> im;
};

static const double PI = acos(-1.0);

static void fft_resize(fft_vec_t &a, size_t n){
    a.re.assign(n, 0.0);
    a.im.assign(n, 0.0);
}

static void fft_build_rev(std::vector<size_t> &rev, size_t n){
    rev.resize(n);
    size_t bits = 0;
    while(((size_t)1 << bits) < n) ++bits;
    rev[0] = 0;
    for(size_t i = 1; i < n; ++i){
        rev[i] = (rev[i >> 1] >> 1) | ((i & 1) << (bits - 1));
    }
}

static void fft_fill_roots(double *wr, double *wi, size_t half, double ang){
    if(half == 0) return;

    double wlr = cos(ang);
    double wli = sin(ang);
    wr[0] = 1.0;
    wi[0] = 0.0;

    for(size_t i = 1; i < half; ++i){
        if((i & 1023) == 0){
            wr[i] = cos(ang * (double)i);
            wi[i] = sin(ang * (double)i);
        }else{
            double r = wr[i - 1] * wlr - wi[i - 1] * wli;
            double m = wr[i - 1] * wli + wi[i - 1] * wlr;
            wr[i] = r;
            wi[i] = m;
        }
    }
}

static void fft_stage(fft_vec_t &a, size_t len, const double *wr, const double *wi){
    size_t n = a.re.size();
    size_t half = len >> 1;
    double *re = a.re.data();
    double *im = a.im.data();

    for(size_t i = 0; i < n; i += len){
        size_t j = 0;

#if PRECN_FFT_HAVE_AVX2
        for(; j + 3 < half; j += 4){
            size_t p = i + j;
            size_t q = p + half;

            __m256d ur = _mm256_loadu_pd(re + p);
            __m256d ui = _mm256_loadu_pd(im + p);
            __m256d br = _mm256_loadu_pd(re + q);
            __m256d bi = _mm256_loadu_pd(im + q);
            __m256d tr = _mm256_loadu_pd(wr + j);
            __m256d ti = _mm256_loadu_pd(wi + j);

            __m256d vr = _mm256_sub_pd(_mm256_mul_pd(br, tr), _mm256_mul_pd(bi, ti));
            __m256d vi = _mm256_add_pd(_mm256_mul_pd(br, ti), _mm256_mul_pd(bi, tr));

            _mm256_storeu_pd(re + p, _mm256_add_pd(ur, vr));
            _mm256_storeu_pd(im + p, _mm256_add_pd(ui, vi));
            _mm256_storeu_pd(re + q, _mm256_sub_pd(ur, vr));
            _mm256_storeu_pd(im + q, _mm256_sub_pd(ui, vi));
        }
#endif

#if PRECN_FFT_HAVE_SSE2
        for(; j + 1 < half; j += 2){
            size_t p = i + j;
            size_t q = p + half;

            __m128d ur = _mm_loadu_pd(re + p);
            __m128d ui = _mm_loadu_pd(im + p);
            __m128d br = _mm_loadu_pd(re + q);
            __m128d bi = _mm_loadu_pd(im + q);
            __m128d tr = _mm_loadu_pd(wr + j);
            __m128d ti = _mm_loadu_pd(wi + j);

            __m128d vr = _mm_sub_pd(_mm_mul_pd(br, tr), _mm_mul_pd(bi, ti));
            __m128d vi = _mm_add_pd(_mm_mul_pd(br, ti), _mm_mul_pd(bi, tr));

            _mm_storeu_pd(re + p, _mm_add_pd(ur, vr));
            _mm_storeu_pd(im + p, _mm_add_pd(ui, vi));
            _mm_storeu_pd(re + q, _mm_sub_pd(ur, vr));
            _mm_storeu_pd(im + q, _mm_sub_pd(ui, vi));
        }
#endif

        for(; j < half; ++j){
            size_t p = i + j;
            size_t q = p + half;

            double br = re[q];
            double bi = im[q];
            double vr = br * wr[j] - bi * wi[j];
            double vi = br * wi[j] + bi * wr[j];
            double ur = re[p];
            double ui = im[p];

            re[p] = ur + vr;
            im[p] = ui + vi;
            re[q] = ur - vr;
            im[q] = ui - vi;
        }
    }
}

static void fft_scale(fft_vec_t &a, double s){
    size_t n = a.re.size();
    size_t i = 0;

#if PRECN_FFT_HAVE_AVX2
    __m256d ss4 = _mm256_set1_pd(s);
    for(; i + 3 < n; i += 4){
        _mm256_storeu_pd(a.re.data() + i, _mm256_mul_pd(_mm256_loadu_pd(a.re.data() + i), ss4));
        _mm256_storeu_pd(a.im.data() + i, _mm256_mul_pd(_mm256_loadu_pd(a.im.data() + i), ss4));
    }
#endif

#if PRECN_FFT_HAVE_SSE2
    __m128d ss = _mm_set1_pd(s);
    for(; i + 1 < n; i += 2){
        _mm_storeu_pd(a.re.data() + i, _mm_mul_pd(_mm_loadu_pd(a.re.data() + i), ss));
        _mm_storeu_pd(a.im.data() + i, _mm_mul_pd(_mm_loadu_pd(a.im.data() + i), ss));
    }
#endif

    for(; i < n; ++i){
        a.re[i] *= s;
        a.im[i] *= s;
    }
}

static void fft(fft_vec_t &a, int inv, const std::vector<size_t> &rev,
                std::vector<double> &wr, std::vector<double> &wi){
    size_t n = a.re.size();
    double *re = a.re.data();
    double *im = a.im.data();

    for(size_t i = 1; i < n; ++i){
        size_t j = rev[i];
        if(i < j){
            std::swap(re[i], re[j]);
            std::swap(im[i], im[j]);
        }
    }

    if(wr.size() < n / 2){
        wr.resize(n / 2);
        wi.resize(n / 2);
    }

    for(size_t len = 2; len <= n; len <<= 1){
        double ang = 2.0 * PI / (double)len * (inv ? -1.0 : 1.0);
        size_t half = len >> 1;
        fft_fill_roots(wr.data(), wi.data(), half, ang);
        fft_stage(a, len, wr.data(), wi.data());
    }

    if(inv) fft_scale(a, 1.0 / (double)n);
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

static void fft_pair_convolution(const fft_vec_t &f, fft_vec_t &out){
    size_t n = f.re.size();
    fft_resize(out, n);

    size_t k = 0;

#if PRECN_FFT_HAVE_AVX2
    if(n){
        double xr = f.re[0];
        double xi = f.im[0];
        double yr = f.re[0];
        double yi = f.im[0];

        double ar = (xr + yr) * 0.5;
        double ai = (xi - yi) * 0.5;
        double br = (xi + yi) * 0.5;
        double bi = (yr - xr) * 0.5;

        out.re[0] = ar * br - ai * bi;
        out.im[0] = ar * bi + ai * br;
        k = 1;
    }

    const __m256d half = _mm256_set1_pd(0.5);
    for(; k + 3 < n; k += 4){
        __m256d xr = _mm256_loadu_pd(f.re.data() + k);
        __m256d xi = _mm256_loadu_pd(f.im.data() + k);
        __m256d yr = _mm256_loadu_pd(f.re.data() + n - k - 3);
        __m256d yi = _mm256_loadu_pd(f.im.data() + n - k - 3);

        yr = _mm256_permute4x64_pd(yr, 0x1B);
        yi = _mm256_permute4x64_pd(yi, 0x1B);

        __m256d ar = _mm256_mul_pd(_mm256_add_pd(xr, yr), half);
        __m256d ai = _mm256_mul_pd(_mm256_sub_pd(xi, yi), half);
        __m256d br = _mm256_mul_pd(_mm256_add_pd(xi, yi), half);
        __m256d bi = _mm256_mul_pd(_mm256_sub_pd(yr, xr), half);

        _mm256_storeu_pd(out.re.data() + k,
                         _mm256_sub_pd(_mm256_mul_pd(ar, br), _mm256_mul_pd(ai, bi)));
        _mm256_storeu_pd(out.im.data() + k,
                         _mm256_add_pd(_mm256_mul_pd(ar, bi), _mm256_mul_pd(ai, br)));
    }
#endif

    for(; k < n; ++k){
        size_t j = (n - k) & (n - 1);
        double xr = f.re[k];
        double xi = f.im[k];
        double yr = f.re[j];
        double yi = f.im[j];

        double ar = (xr + yr) * 0.5;
        double ai = (xi - yi) * 0.5;
        double br = (xi + yi) * 0.5;
        double bi = (yr - xr) * 0.5;

        out.re[k] = ar * br - ai * bi;
        out.im[k] = ar * bi + ai * br;
    }
}

static long long fft_round(double x){
    return (long long)(x >= 0.0 ? x + 0.5 : x - 0.5);
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

    fft_vec_t f, prod;
    fft_resize(f, n);
    for(size_t i = 0; i < da.size(); ++i) f.re[i] = (double)da[i];
    for(size_t i = 0; i < db.size(); ++i) f.im[i] = (double)db[i];

    std::vector<size_t> rev;
    std::vector<double> wr, wi;
    fft_build_rev(rev, n);

    fft(f, 0, rev, wr, wi);
    fft_pair_convolution(f, prod);
    fft(prod, 1, rev, wr, wi);

    std::vector<long long> out(n);
    for(size_t i = 0; i < n; ++i) out[i] = fft_round(prod.re[i]);
    return fft_from_digits(out, bits);
}

precn_t mul_fft(const precn_t &a, const precn_t &b){
    if(a.rsiz == 0 || b.rsiz == 0) return precn_t();

    size_t digits16 = std::max(a.rsiz, b.rsiz) * 2;
    if(digits16 <= (1u << 12)) return mul_fft_bits(a, b, 16);
    return mul_fft_bits(a, b, 8);
}
