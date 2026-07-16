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

struct fft_plan_t{
    size_t n;
    std::vector<size_t> rev;
    std::vector<std::vector<double> > forward_re;
    std::vector<std::vector<double> > forward_im;
    std::vector<std::vector<double> > inverse_re;
    std::vector<std::vector<double> > inverse_im;
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

static fft_plan_t &fft_plan(size_t n){
    static std::vector<fft_plan_t> plans;
    for(size_t i = 0; i < plans.size(); ++i){
        if(plans[i].n == n) return plans[i];
    }

    fft_plan_t plan;
    plan.n = n;
    fft_build_rev(plan.rev, n);
    for(size_t len = 2; len <= n; len <<= 1){
        size_t half = len >> 1;
        plan.forward_re.push_back(std::vector<double>(half));
        plan.forward_im.push_back(std::vector<double>(half));
        plan.inverse_re.push_back(std::vector<double>(half));
        plan.inverse_im.push_back(std::vector<double>(half));
        fft_fill_roots(plan.forward_re.back().data(), plan.forward_im.back().data(),
                       half, 2.0 * PI / (double)len);
        fft_fill_roots(plan.inverse_re.back().data(), plan.inverse_im.back().data(),
                       half, -2.0 * PI / (double)len);
    }
    plans.push_back(std::move(plan));
    return plans.back();
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

static void fft(fft_vec_t &a, int inv, const fft_plan_t &plan){
    size_t n = a.re.size();
    double *re = a.re.data();
    double *im = a.im.data();

    for(size_t i = 1; i < n; ++i){
        size_t j = plan.rev[i];
        if(i < j){
            std::swap(re[i], re[j]);
            std::swap(im[i], im[j]);
        }
    }

    for(size_t level = 0, len = 2; len <= n; len <<= 1, ++level){
        const std::vector<double> &wr = inv ? plan.inverse_re[level] : plan.forward_re[level];
        const std::vector<double> &wi = inv ? plan.inverse_im[level] : plan.forward_im[level];
        fft_stage(a, len, wr.data(), wi.data());
    }

    if(inv) fft_scale(a, 1.0 / (double)n);
}

static size_t fft_digit_count(const precn_t &a, int bits){
    if(a.rsiz == 0) return 0;
    size_t per = 64 / bits;
    size_t n = (a.rsiz - 1) * per;
    uint64_t top = a.a[a.rsiz - 1];
    do{
        ++n;
        top >>= bits;
    }while(top);
    return n;
}

static void fft_load_digits(fft_vec_t &f, const precn_t &a, int bits, int imag){
    uint64_t mask = ((uint64_t)1 << bits) - 1;
    size_t per = 64 / bits;
    double *dst = imag ? f.im.data() : f.re.data();
    size_t k = 0;
    for(size_t i = 0; i < a.rsiz; ++i){
        uint64_t x = a.a[i];
        for(size_t j = 0; j < per; ++j){
            dst[k++] = (double)(x & mask);
            x >>= bits;
        }
    }
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

    const __m256d half4 = _mm256_set1_pd(0.5);
    for(; k + 3 < n; k += 4){
        __m256d xr = _mm256_loadu_pd(f.re.data() + k);
        __m256d xi = _mm256_loadu_pd(f.im.data() + k);
        __m256d yr = _mm256_loadu_pd(f.re.data() + n - k - 3);
        __m256d yi = _mm256_loadu_pd(f.im.data() + n - k - 3);

        yr = _mm256_permute4x64_pd(yr, 0x1B);
        yi = _mm256_permute4x64_pd(yi, 0x1B);
        __m256d ar = _mm256_mul_pd(_mm256_add_pd(xr, yr), half4);
        __m256d ai = _mm256_mul_pd(_mm256_sub_pd(xi, yi), half4);
        __m256d br = _mm256_mul_pd(_mm256_add_pd(xi, yi), half4);
        __m256d bi = _mm256_mul_pd(_mm256_sub_pd(yr, xr), half4);
        __m256d rr = _mm256_sub_pd(_mm256_mul_pd(ar, br), _mm256_mul_pd(ai, bi));
        __m256d ri = _mm256_add_pd(_mm256_mul_pd(ar, bi), _mm256_mul_pd(ai, br));
        _mm256_storeu_pd(out.re.data() + k, rr);
        _mm256_storeu_pd(out.im.data() + k, ri);
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
    uint64_t mask = ((uint64_t)1 << bits) - 1;
    size_t per = 64 / bits;
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
    r.rsiz = (d.size() + per - 1) / per;
    r.asiz = std::max<size_t>(r.rsiz, 1);
    r.a = (uint64_t*) realloc(r.a, r.asiz * sizeof(uint64_t));
    memset(r.a, 0, r.asiz * sizeof(uint64_t));
    for(size_t i = 0; i < d.size(); ++i){
        r.a[i / per] |= (uint64_t)d[i] << ((i % per) * bits);
    }
    while(r.rsiz > 0 && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
}

static precn_t mul_fft_bits(const precn_t &a, const precn_t &b, int bits){
    size_t da = fft_digit_count(a, bits);
    size_t db = fft_digit_count(b, bits);
    if(da == 0 || db == 0) return precn_t();

    size_t n = 1;
    while(n < da + db) n <<= 1;

    fft_vec_t f, product;
    fft_resize(f, n);
    fft_load_digits(f, a, bits, 0);
    fft_load_digits(f, b, bits, 1);

    fft_plan_t &plan = fft_plan(n);

    fft(f, 0, plan);
    fft_pair_convolution(f, product);
    fft(product, 1, plan);
    std::vector<long long> out(n);
    for(size_t i = 0; i < n; ++i) out[i] = fft_round(product.re[i]);
    return fft_from_digits(out, bits);
}

precn_t mul_fft(const precn_t &a, const precn_t &b){
    if(a.rsiz == 0 || b.rsiz == 0) return precn_t();
    if(std::max(a.rsiz, b.rsiz) <= 192) return mul_basic(a, b);

    size_t digits16 = std::max(a.rsiz, b.rsiz) * 2;
    if(digits16 <= (1u << 12)) return mul_fft_bits(a, b, 16);
    return mul_fft_bits(a, b, 8);
}
