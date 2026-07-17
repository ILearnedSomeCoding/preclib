#include"../prec.hpp"

#include<cstdio>

#if !defined(COUNT_FFTS) || !COUNT_FFTS
#error Build fft_torture.cpp with -DCOUNT_FFTS=1
#endif

struct torture_shape_t{
    size_t an;
    size_t bn;
};

struct torture_pattern_t{
    const char *name;
    uint64_t a;
    uint64_t b;
    bool alternate;
};

static precn_t filled(size_t n, uint64_t even, uint64_t odd, bool alternate){
    precn_t r;
    r.asiz = n ? n : 1;
    r.a = (uint64_t*) realloc(r.a, r.asiz * sizeof(uint64_t));
    r.rsiz = n;
    for(size_t i = 0; i < n; ++i) r.a[i] = alternate && (i & 1) ? odd : even;
    if(n && r.a[n - 1] == 0) r.a[n - 1] = even ? even : UINT64_MAX;
    return r;
}

static bool same(const precn_t &a, const precn_t &b){
    if(a.rsiz != b.rsiz) return false;
    for(size_t i = 0; i < a.rsiz; ++i) if(a.a[i] != b.a[i]) return false;
    return true;
}

int main(){
    const torture_shape_t shapes[] = {
        {193, 193}, {255, 256}, {511, 767}, {1024, 1024},
        {1536, 2048}, {2048, 2048}, {2049, 2049}, {3072, 4096},
        {4096, 4096}, {6144, 8192}, {8192, 8192}
    };
    const torture_pattern_t patterns[] = {
        {"all-ones", UINT64_MAX, UINT64_MAX, false},
        {"ffff0000", 0xFFFF0000FFFF0000ULL, 0xFFFF0000FFFF0000ULL, false},
        {"0000ffff", 0x0000FFFF0000FFFFULL, 0x0000FFFF0000FFFFULL, false},
        {"ff00x00ff", 0xFF00FF00FF00FF00ULL, 0x00FF00FF00FF00FFULL, false},
        {"highxlow", 0xFFFFFFFF00000000ULL, 0x00000000FFFFFFFFULL, false},
        {"carry-run", 0xFFFFFFFFFFFFFF00ULL, 0x00FFFFFFFFFFFFFFULL, false},
        {"alternating", UINT64_MAX, 0, true}
    };

    size_t cases = 0;
    puts("fft torture");
    for(size_t si = 0; si < sizeof(shapes) / sizeof(shapes[0]); ++si){
        for(size_t pi = 0; pi < sizeof(patterns) / sizeof(patterns[0]); ++pi){
            const torture_shape_t &s = shapes[si];
            const torture_pattern_t &p = patterns[pi];
            precn_t a = filled(s.an, p.a, p.b, p.alternate);
            precn_t b = filled(s.bn, p.b, p.a, p.alternate);

            uint64_t before_1_8 = danger_fftmuls;
            uint64_t before_1_4 = danger_fftmuls_1_4;
            uint64_t before_3_8 = danger_fftmuls_3_8;
            double before_max = max_fft_rounding_error;
            precn_t actual = mul_fft(a, b);
            precn_t expected = mul_ntt(a, b);
            ++cases;

            if(!same(actual, expected)){
                fprintf(stderr, "mismatch: %s %zux%zu\n", p.name, s.an, s.bn);
                return 1;
            }
            if(danger_fftmuls != before_1_8 || danger_fftmuls_1_4 != before_1_4 ||
               danger_fftmuls_3_8 != before_3_8 || max_fft_rounding_error > before_max){
                printf("%-12s %5zux%-5zu error %.9f zones %d/%d/%d\n",
                       p.name, s.an, s.bn, max_fft_rounding_error,
                       danger_fftmuls != before_1_8, danger_fftmuls_1_4 != before_1_4,
                       danger_fftmuls_3_8 != before_3_8);
            }
        }
    }

    printf("cases %zu\n", cases);
    printf("total_fftmuls %llu\n", (unsigned long long)total_fftmuls);
    printf("danger_fftmuls %llu\n", (unsigned long long)danger_fftmuls);
    printf("danger_fftmuls_1_4 %llu\n", (unsigned long long)danger_fftmuls_1_4);
    printf("danger_fftmuls_3_8 %llu\n", (unsigned long long)danger_fftmuls_3_8);
    printf("max_fft_rounding_error %.9f\n", max_fft_rounding_error);
    puts("ok");
    return 0;
}
