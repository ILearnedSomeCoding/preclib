#include"../prec.hpp"

#include<gmp.h>

#include<algorithm>
#include<chrono>
#include<cstdio>
#include<cstdlib>
#include<cstring>
#include<string>
#include<vector>

struct options_t{
    size_t max_pow = 18;
    int samples = 5;
    double sample_seconds = 0.08;
    int max_reps = 100000;
    bool quick = false;
    const char *csv_path = "test/bench_gmp_full.csv";
};

static double now_seconds(){
    return std::chrono::duration<double>(
        std::chrono::steady_clock::now().time_since_epoch()).count();
}

static precn_t pattern(size_t n, uint64_t seed){
    precn_t r;
    r.asiz = n ? n : 1;
    r.a = (uint64_t*)realloc(r.a, r.asiz * sizeof(uint64_t));
    r.rsiz = n;
    uint64_t x = seed;
    for(size_t i = 0; i < n; ++i){
        x = x * 6364136223846793005ULL + 1442695040888963407ULL;
        r.a[i] = x | 1ULL;
    }
    if(n) r.a[n - 1] |= 1ULL << 63;
    return r;
}

static void precn_to_mpz(mpz_t z, const precn_t &a){
    mpz_import(z, a.rsiz, -1, sizeof(uint64_t), 0, 0, a.a);
}

static void require_same(const precn_t &a, const mpz_t b){
    mpz_t t;
    mpz_init(t);
    precn_to_mpz(t, a);
    if(mpz_cmp(t, b) != 0){
        std::fprintf(stderr, "result mismatch\n");
        std::abort();
    }
    mpz_clear(t);
}

template<class F>
static double timed(int reps, F f){
    double begin = now_seconds();
    for(int i = 0; i < reps; ++i) f();
    return now_seconds() - begin;
}

static double median(std::vector<double> values){
    std::sort(values.begin(), values.end());
    size_t m = values.size() / 2;
    return values.size() & 1 ? values[m] : (values[m - 1] + values[m]) * 0.5;
}

template<class FP, class FG>
static void measure_pair(const options_t &opt, FP fp, FG fg,
                         int &reps, double &prec_time, double &gmp_time){
    fp();
    fg();
    int calibration_reps = 1;
    double cp = 0.0, cg = 0.0;
    do{
        cp = timed(calibration_reps, fp);
        cg = timed(calibration_reps, fg);
        if(std::max(cp, cg) >= 0.002 || calibration_reps >= opt.max_reps) break;
        calibration_reps = std::min(calibration_reps * 4, opt.max_reps);
    }while(true);

    double per_call = std::max(cp, cg) / calibration_reps;
    reps = per_call > 0.0 ? (int)(opt.sample_seconds / per_call) : opt.max_reps;
    reps = std::max(1, std::min(reps, opt.max_reps));

    std::vector<double> pt, gt;
    pt.reserve(opt.samples);
    gt.reserve(opt.samples);
    for(int sample = 0; sample < opt.samples; ++sample){
        double p, g;
        if(sample & 1){
            g = timed(reps, fg);
            p = timed(reps, fp);
        }else{
            p = timed(reps, fp);
            g = timed(reps, fg);
        }
        pt.push_back(p / reps);
        gt.push_back(g / reps);
    }
    prec_time = median(pt);
    gmp_time = median(gt);
}

static void write_row(FILE *csv, const char *op, const std::string &shape,
                      size_t a_size, size_t b_size, size_t result_size,
                      int reps, int samples, double pt, double gt){
    double ratio = gt > 0.0 ? pt / gt : 0.0;
    std::printf("%-7s %-10s %8zu %8zu %7d  %.9f  %.9f  %6.2f\n",
                op, shape.c_str(), a_size, b_size, reps, pt, gt, ratio);
    std::fprintf(csv, "%s,%s,%zu,%zu,%zu,%d,%d,%.12g,%.12g,%.9g\n",
                 op, shape.c_str(), a_size, b_size, result_size, reps, samples,
                 pt, gt, ratio);
    std::fflush(csv);
}

static std::vector<size_t> benchmark_sizes(const options_t &opt){
    std::vector<size_t> sizes;
    for(size_t p = 0; p <= opt.max_pow; ++p){
        size_t n = (size_t)1 << p;
        sizes.push_back(n);
        if(!opt.quick && p >= 5 && p < opt.max_pow) sizes.push_back(n + n / 2);
    }
    return sizes;
}

static void run_mul_case(FILE *csv, const options_t &opt, size_t na, size_t nb,
                         const std::string &shape, bool square, uint64_t seed){
    precn_t a = pattern(na, seed);
    precn_t b = square ? a : pattern(nb, seed + 0x9e3779b97f4a7c15ULL);
    precn_t rp;
    mpz_t ga, gb, gr;
    mpz_inits(ga, gb, gr, NULL);
    precn_to_mpz(ga, a);
    precn_to_mpz(gb, b);

    auto fp = [&]{
        if(square) precn_sqr_into(rp, a);
        else mul_into(rp, a, b);
    };
    auto fg = [&]{ mpz_mul(gr, ga, gb); };
    fp(); fg(); require_same(rp, gr);

    int reps;
    double pt, gt;
    measure_pair(opt, fp, fg, reps, pt, gt);
    require_same(rp, gr);
    write_row(csv, square ? "square" : "mul", shape, na, nb, rp.rsiz,
              reps, opt.samples, pt, gt);
    mpz_clears(ga, gb, gr, NULL);
}

static void run_div_case(FILE *csv, const options_t &opt, size_t den_size,
                         size_t q_size, const std::string &shape, uint64_t seed){
    precn_t den = pattern(den_size, seed);
    precn_t wanted = pattern(q_size, seed + 0x517cc1b727220a95ULL);
    precn_t num = den * wanted + (den - precn_t(1));
    precn_t rp;
    mpz_t gn, gd, gq, gw;
    mpz_inits(gn, gd, gq, gw, NULL);
    precn_to_mpz(gn, num);
    precn_to_mpz(gd, den);
    precn_to_mpz(gw, wanted);

    auto fp = [&]{ div_into(rp, num, den); };
    auto fg = [&]{ mpz_tdiv_q(gq, gn, gd); };
    fp(); fg(); require_same(rp, gq);
    if(mpz_cmp(gq, gw) != 0) std::abort();

    int reps;
    double pt, gt;
    measure_pair(opt, fp, fg, reps, pt, gt);
    require_same(rp, gq);
    write_row(csv, "div", shape, num.rsiz, den.rsiz, rp.rsiz,
              reps, opt.samples, pt, gt);
    mpz_clears(gn, gd, gq, gw, NULL);
}

static options_t parse_options(int argc, char **argv){
    options_t opt;
    for(int i = 1; i < argc; ++i){
        if(std::strcmp(argv[i], "--quick") == 0){
            opt.quick = true;
            opt.max_pow = 12;
            opt.samples = 3;
            opt.sample_seconds = 0.02;
        }else if(std::strcmp(argv[i], "--full") == 0){
            opt.max_pow = 22;
        }else if(std::strcmp(argv[i], "--max-pow") == 0 && i + 1 < argc){
            opt.max_pow = (size_t)std::strtoul(argv[++i], nullptr, 10);
        }else if(std::strcmp(argv[i], "--samples") == 0 && i + 1 < argc){
            opt.samples = std::max(1, std::atoi(argv[++i]));
        }else if(std::strcmp(argv[i], "--csv") == 0 && i + 1 < argc){
            opt.csv_path = argv[++i];
        }else{
            std::fprintf(stderr, "unknown option: %s\n", argv[i]);
            std::exit(2);
        }
    }
    return opt;
}

int main(int argc, char **argv){
    options_t opt = parse_options(argc, argv);
    FILE *csv = std::fopen(opt.csv_path, "wb");
    if(!csv){
        std::perror(opt.csv_path);
        return 1;
    }
    std::fprintf(csv, "operation,shape,a_limbs,b_limbs,result_limbs,reps,samples,prec_seconds,gmp_seconds,ratio\n");
    std::printf("operation shape       a_limbs  b_limbs reps     prec_s       gmp_s       ratio\n");

    std::vector<size_t> sizes = benchmark_sizes(opt);
    uint64_t seed = 101;
    for(size_t n : sizes){
        run_mul_case(csv, opt, n, n, "balanced", false, seed++);
        run_mul_case(csv, opt, n, n, "square", true, seed++);
        if(n >= 32){
            run_mul_case(csv, opt, n + n / 4, n, "1.25x", false, seed++);
            run_mul_case(csv, opt, n + n / 2, n, "1.5x", false, seed++);
            run_mul_case(csv, opt, n * 2, n, "2x", false, seed++);
            run_mul_case(csv, opt, n * 3, n, "3x", false, seed++);
        }
    }

    for(size_t n : sizes){
        run_div_case(csv, opt, n, std::max<size_t>(1, n / 4), "q=0.25d", seed++);
        run_div_case(csv, opt, n, n, "q=d", seed++);
        if(n >= 32){
            run_div_case(csv, opt, n, n * 2, "q=2d", seed++);
            run_div_case(csv, opt, n, n * 3, "q=3d", seed++);
        }
    }
    std::fclose(csv);
    std::printf("ok; csv: %s\n", opt.csv_path);
    return 0;
}
