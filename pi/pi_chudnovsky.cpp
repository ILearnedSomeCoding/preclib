#include"../prec.hpp"

#include<atomic>
#include<ctime>
#include<cstdlib>
#include<chrono>
#include<fstream>
#include<iostream>
#include<string>
#include<thread>
#include<unordered_map>
#include<utility>
#include<vector>

#define CHUD_C3_OVER_24 10939058860032000ULL
#define CHUD_A 13591409u
#define CHUD_B 545140134u

#ifndef PI_ENABLE_FACTOR_CANCEL
#define PI_ENABLE_FACTOR_CANCEL 1
#endif

#ifndef PI_PARALLEL_SPLIT
#define PI_PARALLEL_SPLIT 1
#endif

#ifndef PI_PARALLEL_SPLIT_DEPTH
#define PI_PARALLEL_SPLIT_DEPTH 4
#endif

// The straightforward reciprocal-square-root prototype is kept for
// experimentation, but it needs truncated products before it can beat the
// divide-and-refine integer square root used below.
#ifndef PI_ENABLE_INVSQRT
#define PI_ENABLE_INVSQRT 0
#endif

#ifndef PI_USE_LOCAL_MULINV_DIV
#define PI_USE_LOCAL_MULINV_DIV 1
#endif

#ifndef PI_DECIMAL_1E19
#define PI_DECIMAL_1E19 0
#endif

#ifndef PI_DIV_GUARD_BITS
#define PI_DIV_GUARD_BITS 128
#endif

#ifndef PI_INVSQRT_GUARD_BITS
#define PI_INVSQRT_GUARD_BITS 64
#endif

#ifndef PI_DIV_TRACE
#define PI_DIV_TRACE 0
#endif

#ifndef PI_DIV_SKIP_PRODUCT_VERIFY
#define PI_DIV_SKIP_PRODUCT_VERIFY 0
#endif

static bool show_phases = false;
static bool full_output = false;
static bool show_progress = false;
static std::string output_file;
// The NTT kernel already exposes modulus- and transform-level parallelism.
// Two pool threads avoid oversubscribing the small desktop CPUs this program
// targets; callers can still override it with --threads N.
static unsigned int ntt_threads = 2;

static std::atomic<int> progress_phase(-1);
static std::atomic<uint64_t> progress_done(0);
static std::atomic<uint64_t> progress_total(0);
static std::atomic<uint64_t> progress_started_ms(0);
static std::atomic<uint64_t> progress_started_cpu_ms(0);
static std::atomic<bool> progress_stop(false);
static uint64_t progress_local = 0;
static uint64_t progress_next_publish = 0;
static uint64_t progress_publish_step = 1;

static uint64_t steady_ms(){
    using clock_t = std::chrono::steady_clock;
    return (uint64_t)std::chrono::duration_cast<std::chrono::milliseconds>(
        clock_t::now().time_since_epoch()).count();
}

static uint64_t process_cpu_ms(){
    return (uint64_t)((double)std::clock() * 1000.0 / (double)CLOCKS_PER_SEC);
}

static uint64_t binary_tracked_work(size_t terms){
    std::unordered_map<size_t, uint64_t> memo;
    auto work = [&](auto &&self, size_t n) -> uint64_t{
        if(n < 64) return 0;
        auto found = memo.find(n);
        if(found != memo.end()) return found->second;
        size_t left = n / 2;
        uint64_t result = (uint64_t)n + self(self, left) + self(self, n - left);
        memo.emplace(n, result);
        return result;
    };
    return work(work, terms);
}

static void progress_begin(int phase, uint64_t total = 0){
    if(!show_progress) return;
    progress_local = 0;
    progress_publish_step = std::max<uint64_t>(1, total / 2000);
    progress_next_publish = progress_publish_step;
    progress_done.store(0, std::memory_order_relaxed);
    progress_total.store(total, std::memory_order_relaxed);
    progress_started_ms.store(steady_ms(), std::memory_order_relaxed);
    progress_started_cpu_ms.store(process_cpu_ms(), std::memory_order_relaxed);
    progress_phase.store(phase, std::memory_order_release);
}

static void progress_add(uint64_t amount){
    if(!show_progress) return;
    progress_local += amount;
    if(progress_local < progress_next_publish) return;
    progress_done.store(progress_local, std::memory_order_relaxed);
    progress_next_publish = progress_local + progress_publish_step;
}

static void progress_set(uint64_t done){
    if(show_progress) progress_done.store(done, std::memory_order_relaxed);
}

static void progress_reporter(){
    static const char *names[] = {
        "binary_split", "sqrt_scale", "final_div", "to_decimal"
    };
    int previous = -2;
    while(!progress_stop.load(std::memory_order_acquire)){
        int phase = progress_phase.load(std::memory_order_acquire);
        if(phase >= 0 && phase < 4){
            if(previous != -2 && previous != phase) std::cerr << '\n';
            previous = phase;
            uint64_t started = progress_started_ms.load(std::memory_order_relaxed);
            uint64_t cpu_started = progress_started_cpu_ms.load(std::memory_order_relaxed);
            double wall_elapsed = (double)(steady_ms() - started) / 1000.0;
            double cpu_elapsed = (double)(process_cpu_ms() - cpu_started) / 1000.0;
            uint64_t total = progress_total.load(std::memory_order_relaxed);
            uint64_t done = progress_done.load(std::memory_order_relaxed);
            const int width = 30;
            std::string bar((size_t)width, '.');
            if(total){
                if(done > total) done = total;
                int filled = (int)(done * (uint64_t)width / total);
                for(int i = 0; i < filled; ++i) bar[(size_t)i] = '#';
                double percent = 100.0 * (double)done / (double)total;
                std::cerr << '\r' << names[phase] << " [" << bar << "] "
                          << percent << "%  cpu " << cpu_elapsed
                          << " sec  wall " << wall_elapsed << " sec   " << std::flush;
            }else{
                int position = (int)((steady_ms() / 200) % (uint64_t)width);
                bar[(size_t)position] = '>';
                std::cerr << '\r' << names[phase] << " [" << bar << "] working  "
                          << "cpu " << cpu_elapsed << " sec  wall "
                          << wall_elapsed << " sec   " << std::flush;
            }
        }
        std::this_thread::sleep_for(std::chrono::milliseconds(200));
    }
    if(previous != -2) std::cerr << '\n';
}

static double now_sec(){
    using clock_t = std::chrono::steady_clock;
    static clock_t::time_point start = clock_t::now();
    return std::chrono::duration<double>(clock_t::now() - start).count();
}

struct factor_power_t{
    uint32_t prime;
    uint32_t power;
};

struct bs_t{
    precn_t p;
    precn_t q;
    precz_t t;
    std::vector<factor_power_t> fp;
    std::vector<factor_power_t> fq;
};

class chud_factor_sieve_t{
    std::vector<uint32_t> smallest_;

public:
    chud_factor_sieve_t(size_t n) : smallest_(n + 1, 0){
        for(size_t i = 2; i <= n; ++i){
            if(smallest_[i]) continue;
            smallest_[i] = (uint32_t)i;
            if(i > n / i) continue;
            for(size_t j = i * i; j <= n; j += i){
                if(!smallest_[j]) smallest_[j] = (uint32_t)i;
            }
        }
    }

    void append(std::vector<factor_power_t> &out, size_t value,
                uint32_t multiplier = 1) const{
        while(value > 1){
            uint32_t p = smallest_[value];
            uint32_t power = 0;
            do{
                value /= p;
                ++power;
            }while(value > 1 && smallest_[value] == p);
            out.push_back(factor_power_t{p, power * multiplier});
        }
    }
};

static std::vector<factor_power_t> factor_merge(
    const std::vector<factor_power_t> &a,
    const std::vector<factor_power_t> &b){
    std::vector<factor_power_t> r;
    r.reserve(a.size() + b.size());
    size_t i = 0, j = 0;
    while(i < a.size() || j < b.size()){
        if(j == b.size() || (i < a.size() && a[i].prime < b[j].prime)){
            r.push_back(a[i++]);
        }else if(i == a.size() || b[j].prime < a[i].prime){
            r.push_back(b[j++]);
        }else{
            r.push_back(factor_power_t{a[i].prime, a[i].power + b[j].power});
            ++i;
            ++j;
        }
    }
    return r;
}

static precn_t factor_pow(uint32_t base, uint32_t power){
    precn_t r(1);
    precn_t b(base);
    while(power){
        if(power & 1) r = r * b;
        power >>= 1;
        if(power) b = b * b;
    }
    return r;
}

static precn_t factor_product(const std::vector<factor_power_t> &f,
                              size_t begin, size_t end){
    if(begin == end) return precn_t(1);
    if(end - begin == 1) return factor_pow(f[begin].prime, f[begin].power);
    size_t mid = begin + (end - begin) / 2;
    return factor_product(f, begin, mid) * factor_product(f, mid, end);
}

static void factor_compact(std::vector<factor_power_t> &f){
    size_t out = 0;
    for(size_t i = 0; i < f.size(); ++i){
        if(f[i].power) f[out++] = f[i];
    }
    f.resize(out);
}

static void factor_cancel(precn_t &p, std::vector<factor_power_t> &fp,
                          precn_t &q, std::vector<factor_power_t> &fq){
    std::vector<factor_power_t> common;
    common.reserve(std::min(fp.size(), fq.size()));
    size_t i = 0, j = 0;
    while(i < fp.size() && j < fq.size()){
        if(fp[i].prime < fq[j].prime){
            ++i;
        }else if(fq[j].prime < fp[i].prime){
            ++j;
        }else{
            uint32_t power = std::min(fp[i].power, fq[j].power);
            if(power){
                fp[i].power -= power;
                fq[j].power -= power;
                common.push_back(factor_power_t{fp[i].prime, power});
            }
            ++i;
            ++j;
        }
    }
    if(common.empty()) return;

    precn_t divisor = factor_product(common, 0, common.size());
    p = p / divisor;
    q = q / divisor;
    factor_compact(fp);
    factor_compact(fq);
}

static size_t bit_length(const precn_t &a){
    if(a.rsiz == 0) return 0;
    uint64_t top = a.a[a.rsiz - 1];
    size_t bits = (a.rsiz - 1) * 64;
    while(top){
        ++bits;
        top >>= 1;
    }
    return bits;
}

static precn_t pow_u32(uint32_t base, size_t exp){
    precn_t r(1);
    precn_t b(base);
    while(exp){
        if(exp & 1) r = r * b;
        exp >>= 1;
        if(exp) b = b * b;
    }
    return r;
}

static void mul_u64_self(precn_t &a, uint64_t b){
    if(a.rsiz == 0 || b == 1) return;
    if(b == 0){
        a.rsiz = 0;
        a.a[0] = 0;
        return;
    }
    if(a.asiz < a.rsiz + 1){
        a.a = (uint64_t*)realloc(a.a, (a.rsiz + 1) * sizeof(uint64_t));
        a.asiz = a.rsiz + 1;
    }

    uint64_t carry = 0;
    for(size_t i = 0; i < a.rsiz; ++i){
        uint64_t hi, lo, out;
        precn_mul_wide(a.a[i], b, hi, lo);
        uint64_t c = precn_add_carry(lo, carry, 0, out);
        a.a[i] = out;
        carry = hi + c;
    }
    if(carry) a.a[a.rsiz++] = carry;
}

struct pow10_entry_t{
    size_t digits;
    precn_t value;
};

static size_t pow10_index(size_t digits, std::vector<pow10_entry_t> &cache){
    for(size_t i = 0; i < cache.size(); ++i){
        if(cache[i].digits == digits) return i;
    }
    cache.push_back(pow10_entry_t{digits, pow_u32(10, digits)});
    return cache.size() - 1;
}

static uint64_t pi_sqrt_work(size_t limbs){
    uint64_t total = 0;
    while(limbs > 4){
        size_t drop = (limbs / 2) & ~(size_t)1;
        if(drop == 0) break;
        // Integer Newton normally takes about two full divisions per level.
        total += (uint64_t)limbs * 2;
        limbs -= drop;
    }
    return total + (uint64_t)std::max<size_t>(limbs, 1) * 4;
}

static uint64_t pi_sqrt_top_bits(const precn_t &a, size_t bits, size_t take){
    size_t shift = bits - take;
    size_t limb = shift / 64;
    unsigned offset = (unsigned)(shift % 64);
    uint64_t top = a.a[limb] >> offset;
    if(offset && limb + 1 < a.rsiz) top |= a.a[limb + 1] << (64 - offset);
    return top;
}

static precn_t pi_sqrt_seed(const precn_t &a){
    size_t bits = bit_length(a);
    size_t take = std::min<size_t>(bits, 53);
    size_t shift = bits - take;
    double estimate = std::sqrt((double)pi_sqrt_top_bits(a, bits, take));
    if(shift & 1) estimate *= 1.4142135623730950488;
    return precn_t((uint64_t)estimate + 4) << (shift / 2);
}

static void pi_sqrt_advance(uint64_t &done, uint64_t total, size_t limbs){
    done += (uint64_t)std::max<size_t>(limbs, 1);
    uint64_t part = total ? std::min<uint64_t>(done, total) * 850 / total : 850;
    progress_set(150 + part);
}

static precn_t pi_sqrt_refine(const precn_t &a, precn_t x,
                              uint64_t &done, uint64_t total){
    for(;;){
        precn_t y = (x + a / x) >> 1;
        pi_sqrt_advance(done, total, a.rsiz);
        if(y >= x) return x;
        x = y;
    }
}

static precn_t pi_sqrt_high_part(const precn_t &a, size_t drop){
    precn_t high;
    high.rsiz = a.rsiz - drop;
    high.asiz = high.rsiz;
    high.a = (uint64_t*)realloc(high.a, high.asiz * sizeof(uint64_t));
    memcpy(high.a, a.a + drop, high.rsiz * sizeof(uint64_t));
    return high;
}

static precn_t pi_sqrt_tracked_impl(const precn_t &a, uint64_t &done,
                                    uint64_t total){
    if(a.rsiz == 0) return precn_t();
    if(a.rsiz <= 4) return pi_sqrt_refine(a, pi_sqrt_seed(a), done, total);

    size_t drop = (a.rsiz / 2) & ~(size_t)1;
    if(drop == 0) return pi_sqrt_refine(a, pi_sqrt_seed(a), done, total);
    precn_t high_root = pi_sqrt_tracked_impl(pi_sqrt_high_part(a, drop),
                                             done, total);
    precn_t upper = (high_root + 1) << (drop * 32);
    return pi_sqrt_refine(a, upper, done, total);
}

static precn_t pi_sqrt_tracked(const precn_t &a){
    uint64_t done = 0;
    precn_t root = pi_sqrt_tracked_impl(a, done, pi_sqrt_work(a.rsiz));
    progress_set(1000);
    return root;
}

// Return floor(sqrt(10005) * 10^digits).  For the large fixed-point scale in
// Chudnovsky, reciprocal-square-root Newton avoids the full divisions used by
// integer sqrt.  Y represents 2^bits / sqrt(10005):
//
//     Y <- Y * (3 - 10005 * Y^2) / 2
//
// All quantities are stored as integers with `bits` fractional binary bits.
// A final exact square comparison makes the returned integer exact.
static precn_t sqrt10005_invsqrt(size_t digits, size_t scale_index,
                                 std::vector<pow10_entry_t> &pow10_cache){
    const uint32_t c = 10005;
    // The final multiplication by 10005 amplifies a one-unit reciprocal
    // error by at most 10005.  Sixty-four binary guard bits leave that far
    // below one output unit, while 192 bits only make the final NTT rounds
    // larger.
    const size_t guard_bits = PI_INVSQRT_GUARD_BITS;
    const size_t scale_bits = bit_length(pow10_cache[pow10_index(digits, pow10_cache)].value);
    const size_t target_bits = scale_bits + guard_bits;
    size_t bits = 56;
    uint64_t seed = (uint64_t)std::ldexp(1.0 / std::sqrt((double)c), (int)bits);
    precn_t y(seed);

    while(bits < target_bits){
        size_t next_bits = std::min(target_bits, bits << 1);
        y = y << (next_bits - bits);
        // Keep 16 extra low bits before multiplying by 10005.  The discarded
        // tail is then smaller than one unit after the final shift, so q is
        // still exactly floor(10005*y^2 / 2^next_bits).
        size_t square_drop = (next_bits - 16) / 64;
        size_t square_shift = next_bits - square_drop * 64;
        precn_t q = mul_u32(mul_high(y, y, square_drop), c) >> square_shift;
        precn_t correction = (precn_t(3) << next_bits) - q;
        size_t product_drop = (next_bits + 1) / 64;
        y = mul_high(y, correction, product_drop) >>
            (next_bits + 1 - product_drop * 64);
        bits = next_bits;
    }

    const precn_t &scale = pow10_cache[pow10_index(digits, pow10_cache)].value;
    precn_t root = mul_u32(scale * y, c) >> bits;
    const precn_t target = mul_u32(pow10_cache[scale_index].value, c);

    // With the guard bits this loop normally takes zero or one iteration.
    // Keeping a short bounded correction makes the fast path exact even if a
    // rounded seed or intermediate product lands on the other side.
    for(unsigned int i = 0; i < 8; ++i){
        precn_t square = root * root;
        if(square > target){
            root = root - precn_t(1);
            continue;
        }
        precn_t next = root + precn_t(1);
        if(next * next <= target){
            root = next;
            continue;
        }
        return root;
    }

    // Do not trade correctness for speed if a future arithmetic change makes
    // the error bound above invalid.
    return precn_sqrt(target);
}

static precn_t sqrt10005_scaled(size_t digits, size_t scale_index,
                                std::vector<pow10_entry_t> &pow10_cache){
    if(PI_ENABLE_INVSQRT && !show_progress && digits >= 8192)
        return sqrt10005_invsqrt(digits, scale_index, pow10_cache);
    precn_t n = mul_u32(pow10_cache[scale_index].value, 10005);
    return show_progress ? pi_sqrt_tracked(n) : precn_sqrt(n);
}

// A parent only needs P from its left child to form T.  Matching ilmPi's
// needp scheduling avoids forming product-tree nodes that will not be used.
static bs_t chud_bs(size_t a, size_t b, bool need_p, size_t level,
                    const chud_factor_sieve_t &sieve){
    if(b - a == 1){
        uint64_t k = (uint64_t)b;
        precn_t p((uint64_t)(6 * k - 5));
        mul_u64_self(p, (uint64_t)(2 * k - 1));
        mul_u64_self(p, (uint64_t)(6 * k - 1));

        precn_t q(k);
        mul_u64_self(q, k);
        mul_u64_self(q, k);
        mul_u64_self(q, (uint64_t)CHUD_C3_OVER_24);

        precn_t term = p * (uint64_t)(CHUD_B * k + CHUD_A);
        precz_t t(std::move(term));
        if(k & 1) t = -t;

        std::vector<factor_power_t> fp;
        sieve.append(fp, (size_t)(6 * k - 5));
        sieve.append(fp, (size_t)(2 * k - 1));
        sieve.append(fp, (size_t)(6 * k - 1));
        std::sort(fp.begin(), fp.end(), [](const factor_power_t &x,
                                           const factor_power_t &y){
            return x.prime < y.prime;
        });
        std::vector<factor_power_t> fp_merged;
        for(size_t i = 0; i < fp.size(); ++i){
            if(!fp_merged.empty() && fp_merged.back().prime == fp[i].prime){
                fp_merged.back().power += fp[i].power;
            }else{
                fp_merged.push_back(fp[i]);
            }
        }

        std::vector<factor_power_t> fq;
        sieve.append(fq, (size_t)k, 3);
        fq.push_back(factor_power_t{2, 15});
        fq.push_back(factor_power_t{3, 2});
        fq.push_back(factor_power_t{5, 3});
        fq.push_back(factor_power_t{23, 3});
        fq.push_back(factor_power_t{29, 3});
        std::sort(fq.begin(), fq.end(), [](const factor_power_t &x,
                                           const factor_power_t &y){
            return x.prime < y.prime;
        });
        std::vector<factor_power_t> fq_merged;
        for(size_t i = 0; i < fq.size(); ++i){
            if(!fq_merged.empty() && fq_merged.back().prime == fq[i].prime){
                fq_merged.back().power += fq[i].power;
            }else{
                fq_merged.push_back(fq[i]);
            }
        }
        return bs_t{std::move(p), std::move(q), std::move(t),
                    std::move(fp_merged), std::move(fq_merged)};
    }

    size_t m = a + (b - a) / 2;
    bs_t l;
    bs_t r;
#if PI_PARALLEL_SPLIT
    if(!show_progress && level < PI_PARALLEL_SPLIT_DEPTH && b - a >= 8192){
        std::thread right_worker([&]{ r = chud_bs(m, b, need_p, level + 1, sieve); });
        l = chud_bs(a, m, true, level + 1, sieve);
        right_worker.join();
    }else
#endif
    {
        l = chud_bs(a, m, true, level + 1, sieve);
        r = chud_bs(m, b, need_p, level + 1, sieve);
    }

    // This is ilmPi's factor-aware cancellation: scaling P_left and Q_right
    // by the same exact factor scales Q and T equally, preserving T/Q while
    // keeping every multiplication above this node smaller.
#if PI_ENABLE_FACTOR_CANCEL
    if(level >= 4) factor_cancel(l.p, l.fp, r.q, r.fq);
#endif

    precn_t q = l.q * r.q;
    precz_t t = l.t * precz_t(r.q) + r.t * precz_t(l.p);
    std::vector<factor_power_t> fq = factor_merge(l.fq, r.fq);
    if(need_p){
        precn_t p = l.p * r.p;
        std::vector<factor_power_t> fp = factor_merge(l.fp, r.fp);
        if(b - a >= 64) progress_add((uint64_t)(b - a));
        return bs_t{std::move(p), std::move(q), std::move(t),
                    std::move(fp), std::move(fq)};
    }
    if(b - a >= 64) progress_add((uint64_t)(b - a));
    return bs_t{precn_t(), std::move(q), std::move(t),
                std::vector<factor_power_t>(), std::move(fq)};
}

static std::string to_dec(const precn_t &a){
#if PI_DECIMAL_1E19
    return precn_to_decimal(a);
#else
    // The generic decimal formatter uses 10^19 leaves.  With the current
    // division kernel, 10^9 chunks benchmark faster for this Pi workload.
    size_t n = bit_length(a) / 29 + 2;
    std::vector<uint32_t> chunks(n);
    precn_base_convert(a, 1000000000u, chunks.data(), n);
    if(n == 0) return "0";

    std::string s = std::to_string(chunks[n - 1]);
    s.reserve(n * 9);
    for(size_t i = n - 1; i > 0; --i){
        uint32_t value = chunks[i - 1];
        size_t start = s.size();
        s.append(9, '0');
        for(size_t j = 0; j < 9; ++j){
            s[start + 8 - j] = (char)('0' + value % 10);
            value /= 10;
        }
    }
    return s;
#endif
}

// Progress builds use a local copy of the multiplication-inverse division.
// The normal operator/ currently selects divide-and-conquer first for Pi's
// similarly sized operands, whose recursion has no progress hook.
static size_t pi_div_bits(const precn_t &a){
    if(a.rsiz == 0) return 0;
    uint64_t top = a.a[a.rsiz - 1];
    size_t bits = (a.rsiz - 1) * 64;
    while(top){
        ++bits;
        top >>= 1;
    }
    return bits;
}

static precn_t pi_div_top_ceil(const precn_t &b, size_t divisor_bits,
                               size_t keep_bits){
    if(keep_bits >= divisor_bits) return b;
    return (b >> (divisor_bits - keep_bits)) + 1;
}

// Newton reciprocal updates and the final quotient discard a large low tail.
// mul_high reconstructs only the required high base-2^64 limbs, with a
// deterministic carry guard/fallback in the NTT backend.  Keep medium inputs
// on the ordinary dispatcher because their FFT/Toom setup is cheaper.
static precn_t pi_mul_shift_right(const precn_t &a, const precn_t &b,
                                  size_t shift){
    size_t drop = shift / 64;
    if(drop && std::max(a.rsiz, b.rsiz) >= 2048)
        return mul_high(a, b, drop) >> (shift % 64);
    return (a * b) >> shift;
}

static precn_t pi_div_reciprocal(const precn_t &b, size_t bits){
    size_t divisor_bits = pi_div_bits(b);
    if(b.rsiz == 0 || bits < divisor_bits) return precn_t();

    size_t target_known = bits - divisor_bits;
    size_t known = std::min<size_t>(target_known, 64);
    size_t keep = std::min(divisor_bits, known + PI_DIV_GUARD_BITS);
    precn_t bt = pi_div_top_ceil(b, divisor_bits, keep);
    size_t precision = keep + known;
    precn_t x = div_schoolbook(precn_t(1) << precision, bt);
    progress_set(100);

    while(known < target_known){
        size_t next_known = std::min(target_known, known * 2);
        size_t next_keep = std::min(divisor_bits, next_known + PI_DIV_GUARD_BITS);
        precn_t next_b = pi_div_top_ceil(b, divisor_bits, next_keep);
        size_t next = next_keep + next_known;
        precn_t scaled_x = x << (next_known - known);
        precn_t two_scale = precn_t(1) << (next + 1);
        precn_t bx = next_b * scaled_x;
        if(bx >= two_scale){
            scaled_x = scaled_x >> 1;
            bx = next_b * scaled_x;
        }
        x = pi_mul_shift_right(scaled_x, two_scale - bx, next);
        known = next_known;
        uint64_t fraction = target_known ?
            (uint64_t)((600.0 * (double)known) / (double)target_known) : 600;
        progress_set(100 + std::min<uint64_t>(fraction, 600));
    }
    return x;
}

static precn_t pi_div_mulinv(const precn_t &a, const precn_t &b){
    if(a.rsiz == 0 || b.rsiz == 0 || a < b) return precn_t();
    if(b.rsiz == 1) return div_u64(a, b.a[0]);

    size_t scale = pi_div_bits(a) + PI_DIV_GUARD_BITS;
    precn_t inverse = pi_div_reciprocal(b, scale);
    progress_set(700);
    precn_t q = pi_mul_shift_right(a, inverse, scale);
    progress_set(820);
#if PI_DIV_SKIP_PRODUCT_VERIFY
    progress_set(1000);
    return q;
#else
    precn_t product = b * q;
    progress_set(940);

    unsigned int down_corrections = 0;
    unsigned int up_corrections = 0;

    while(product > a){
        precn_t delta = div_schoolbook(product - a, b);
        if(delta.rsiz == 0) delta = precn_t(1);
        q = q - delta;
        product = product - b * delta;
        ++down_corrections;
    }
    while(product + b <= a){
        precn_t delta = div_schoolbook(a - product, b);
        if(delta.rsiz == 0) delta = precn_t(1);
        q = q + delta;
        product = product + b * delta;
        ++up_corrections;
    }
#if PI_DIV_TRACE
    fprintf(stderr, "pi division corrections: down=%u up=%u\n",
            down_corrections, up_corrections);
#endif
    progress_set(1000);
    return q;
#endif
}

static std::string pi_digits(size_t digits){
    size_t guard = 10;
    size_t work_digits = digits + guard;
    size_t terms = work_digits / 14 + 1;

    double t0 = now_sec();
    if(terms > (UINT32_MAX - 1) / 6) return "error";
    progress_begin(0, binary_tracked_work(terms));
    chud_factor_sieve_t sieve(6 * terms + 1);
    bs_t bs = chud_bs(0, terms, false, 0, sieve);
    bs.t += precz_t(bs.q * CHUD_A);
    if(show_progress){
        progress_done.store(progress_total.load(std::memory_order_relaxed),
                            std::memory_order_relaxed);
    }
    double t1 = now_sec();
    if(bs.t.is_negative() || bs.t.is_zero()) return "error";

    progress_begin(1, show_progress ? 1000 : 0);
    std::vector<pow10_entry_t> pow10_cache;
    size_t scale_index = pow10_index(work_digits * 2, pow10_cache);
    progress_set(150);
    precn_t sqrt_scaled = sqrt10005_scaled(work_digits, scale_index, pow10_cache);
    double t2 = now_sec();
    progress_begin(2, show_progress ? 1000 : 0);
    precn_t numerator = mul_u32(bs.q, 426880) * sqrt_scaled;
    progress_set(50);
    precn_t pi_scaled = (show_progress || PI_USE_LOCAL_MULINV_DIV) ?
        pi_div_mulinv(numerator, bs.t.magnitude()) :
        numerator / bs.t.magnitude();
    pi_scaled = pi_scaled / 10000000000ULL;
    double t3 = now_sec();

    progress_begin(3);
    std::string s = to_dec(pi_scaled);
    double t4 = now_sec();
    if(show_progress) progress_phase.store(-1, std::memory_order_release);
    if(show_phases){
        std::cerr << "binary_split " << (t1 - t0) << " sec\n";
        std::cerr << "sqrt_scale " << (t2 - t1) << " sec\n";
        std::cerr << "final_div " << (t3 - t2) << " sec\n";
        std::cerr << "to_decimal " << (t4 - t3) << " sec\n";
    }
    if(digits == 0) return s;
    if(s.size() <= digits) s.insert(0, digits + 1 - s.size(), '0');
    s.insert(s.end() - (long long)digits, '.');
    return s;
}

static std::string short_pi(const std::string &s){
    if(full_output || s.size() <= 24) return s;

    size_t first = 0;
    size_t first_end = 0;
    while(first_end < s.size() && first < 10){
        if(s[first_end] >= '0' && s[first_end] <= '9') ++first;
        ++first_end;
    }
    if(first < 10 || s.size() <= first_end + 10) return s;
    return s.substr(0, first_end) + "..." + s.substr(s.size() - 10);
}

int main(int argc, char **argv){
    size_t digits = 100;
    if(argc > 1){
        digits = (size_t)std::strtoull(argv[1], nullptr, 10);
    }
    for(int i = 2; i < argc; ++i){
        std::string arg(argv[i]);
        if(arg == "--phases") show_phases = true;
        if(arg == "--full") full_output = true;
        if(arg == "--progress") show_progress = true;
        if(arg == "--file" && i + 1 < argc) output_file = argv[++i];
        if(arg == "--threads" && i + 1 < argc)
            ntt_threads = (unsigned int)std::strtoul(argv[++i], nullptr, 10);
    }
    precn_set_ntt_threads(ntt_threads);
    double start = now_sec();
    uint64_t cpu_start = process_cpu_ms();
    std::thread reporter;
    if(show_progress){
        progress_stop.store(false, std::memory_order_relaxed);
        reporter = std::thread(progress_reporter);
    }

    std::string out;
    try{
        out = pi_digits(digits);
    }catch(...){
        if(reporter.joinable()){
            progress_stop.store(true, std::memory_order_release);
            reporter.join();
        }
        throw;
    }
    if(reporter.joinable()){
        progress_stop.store(true, std::memory_order_release);
        reporter.join();
    }
    double sec = now_sec() - start;
    double cpu_sec = (double)(process_cpu_ms() - cpu_start) / 1000.0;

    if(!output_file.empty()){
        std::ofstream file(output_file.c_str(), std::ios::out | std::ios::binary);
        if(!file){
            std::cerr << "failed to open " << output_file << "\n";
            return 1;
        }
        file << out << "\n";
    }

    std::cout << short_pi(out) << "\n";
    if(!output_file.empty()) std::cerr << "wrote " << output_file << "\n";
#if defined(COUNT_FFTS) && COUNT_FFTS
    std::cerr << "total_fftmuls " << total_fftmuls << "\n";
    std::cerr << "danger_fftmuls " << danger_fftmuls << "\n";
    std::cerr << "danger_fftmuls_1_4 " << danger_fftmuls_1_4 << "\n";
    std::cerr << "danger_fftmuls_3_8 " << danger_fftmuls_3_8 << "\n";
    std::cerr << "max_fft_rounding_error " << max_fft_rounding_error << "\n";
#endif
    std::cerr << "time " << sec << " sec\n";
    std::cerr << "cpu_time " << cpu_sec << " sec\n";
    return 0;
}
