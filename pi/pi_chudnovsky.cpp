#include"../prec.hpp"

#include<atomic>
#include<ctime>
#include<cstdlib>
#include<chrono>
#include<condition_variable>
#include<deque>
#include<exception>
#include<fstream>
#include<iostream>
#include<mutex>
#include<string>
#include<thread>
#include<unordered_map>
#include<utility>
#include<vector>

#if defined(_WIN32) && !defined(__EMSCRIPTEN__)
#ifndef NOMINMAX
#define NOMINMAX
#endif
#include<windows.h>
#endif

#define CHUD_C3_OVER_24 10939058860032000ULL
#define CHUD_A 13591409u
#define CHUD_B 545140134u

#ifndef PI_ENABLE_FACTOR_CANCEL
#define PI_ENABLE_FACTOR_CANCEL 1
#endif

#ifndef PI_FACTOR_CANCEL_MIN_LEVEL
#define PI_FACTOR_CANCEL_MIN_LEVEL 5
#endif

#ifndef PI_FACTOR_PAIR_THRESHOLD
#define PI_FACTOR_PAIR_THRESHOLD 2048
#endif


#ifndef PI_PARALLEL_SPLIT_DEPTH
#define PI_PARALLEL_SPLIT_DEPTH 5
#endif

// The straightforward reciprocal-square-root prototype is kept for
// experimentation, but it needs truncated products before it can beat the
// divide-and-refine integer square root used below.
#ifndef PI_ENABLE_INVSQRT
#define PI_ENABLE_INVSQRT 1
#endif

#ifndef PI_INVSQRT_MIN_DIGITS
#define PI_INVSQRT_MIN_DIGITS 10000000
#endif

#ifndef PI_USE_LOCAL_MULINV_DIV
#define PI_USE_LOCAL_MULINV_DIV 1
#endif

#ifndef PI_DECIMAL_1E19
#define PI_DECIMAL_1E19 1
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
#define PI_DIV_SKIP_PRODUCT_VERIFY 1
#endif

#ifndef PI_GUARD_DIGITS
#define PI_GUARD_DIGITS 10
#endif

#ifndef PI_DIV_1E10_SPECIAL
#define PI_DIV_1E10_SPECIAL 1
#endif

#ifndef PI_SPLIT_SERIAL_NTT
#define PI_SPLIT_SERIAL_NTT 0
#endif

// A binary-split worker keeps short transforms local.  Once the tree has
// narrowed to a large merge, an NTT may borrow its two-worker pool again.
#ifndef PI_NESTED_NTT_MIN_TRANSFORM
#define PI_NESTED_NTT_MIN_TRANSFORM ((size_t)1 << 19)
#endif

// Deep binary-split tasks already run concurrently. Letting each of them
// enter the shared NTT pool makes workers queue behind the pool mutex and
// produces large run-to-run jitter. Only merges near the root may borrow it.
#ifndef PI_NESTED_NTT_MAX_LEVEL
#define PI_NESTED_NTT_MAX_LEVEL 1
#endif

#ifndef PI_ROOT_TASK_SCHEDULER
#define PI_ROOT_TASK_SCHEDULER 1
#endif

#ifndef PI_ROOT_TASK_DEPTH
#define PI_ROOT_TASK_DEPTH 5
#endif

#ifndef PI_ROOT_TASK_THREADS
#define PI_ROOT_TASK_THREADS 8
#endif

#ifndef PI_ROOT_MERGE_PRODUCTS_PARALLEL
#define PI_ROOT_MERGE_PRODUCTS_PARALLEL 0
#endif
#ifndef PI_ROOT_SHARED_NTT
#define PI_ROOT_SHARED_NTT 1
#endif
#ifndef PI_ROOT_SHARED_NTT_TRACE
#define PI_ROOT_SHARED_NTT_TRACE 0
#endif
#ifndef PI_TREE_SHARED_NTT
#define PI_TREE_SHARED_NTT 0
#endif

#ifndef PI_OVERLAP_BS_SQRT
#define PI_OVERLAP_BS_SQRT 0
#endif

#ifndef PI_OVERLAP_BS_SQRT_MIN_DIGITS
#define PI_OVERLAP_BS_SQRT_MIN_DIGITS 100000
#endif

#ifndef PI_OVERLAP_NUMERATOR_RECIPROCAL
#define PI_OVERLAP_NUMERATOR_RECIPROCAL 1
#endif

static bool show_phases = false;
static bool full_output = false;
static bool show_progress = false;
static std::string output_file;
// The NTT kernel already exposes modulus- and transform-level parallelism.
// Two pool threads avoid oversubscribing the small desktop CPUs this program
// targets; callers can still override it with --threads N.
static unsigned int ntt_threads = 2;
static unsigned int bs_threads = PI_ROOT_TASK_THREADS;

static std::atomic<int> progress_phase(-1);
static std::atomic<uint64_t> progress_done(0);
static std::atomic<uint64_t> progress_total(0);
static std::atomic<uint64_t> progress_started_ms(0);
static std::atomic<uint64_t> progress_started_cpu_ms(0);
static std::atomic<bool> progress_stop(false);
static std::mutex progress_wait_mutex;
static std::condition_variable progress_wakeup;

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
    progress_done.store(0, std::memory_order_relaxed);
    progress_total.store(total, std::memory_order_relaxed);
    progress_started_ms.store(steady_ms(), std::memory_order_relaxed);
    progress_started_cpu_ms.store(process_cpu_ms(), std::memory_order_relaxed);
    progress_phase.store(phase, std::memory_order_release);
    progress_wakeup.notify_one();
}

static void progress_add(uint64_t amount){
    if(show_progress)
        progress_done.fetch_add(amount, std::memory_order_relaxed);
}

static void progress_set(uint64_t done){
    if(show_progress) progress_done.store(done, std::memory_order_relaxed);
}

static void progress_reporter(){
    static const char *names[] = {
        "binary_split", "sqrt_scale", "final_div", "to_decimal"
    };
    int previous = -1;
    uint64_t last_done = 0;
    uint64_t last_change_ms = 0;
    while(!progress_stop.load(std::memory_order_acquire)){
        int phase = progress_phase.load(std::memory_order_acquire);
        if(phase >= 0 && phase < 4){
            uint64_t now = steady_ms();
            if(previous != phase){
                if(previous >= 0) std::cerr << '\n';
                previous = phase;
                last_done = 0;
                last_change_ms = now;
            }
            uint64_t started = progress_started_ms.load(std::memory_order_relaxed);
            uint64_t cpu_started = progress_started_cpu_ms.load(std::memory_order_relaxed);
            double elapsed = (double)(now - started) / 1000.0;
            double cpu = (double)(process_cpu_ms() - cpu_started) / 1000.0;
            uint64_t total = progress_total.load(std::memory_order_relaxed);
            uint64_t done = progress_done.load(std::memory_order_relaxed);
            if(done != last_done){
                last_done = done;
                last_change_ms = now;
            }
            const int width = 32;
            std::string bar((size_t)width, ' ');
            char line[512];
            if(total){
                if(done > total) done = total;
                int filled = (int)(done * (uint64_t)width / total);
                for(int i = 0; i < filled; ++i) bar[(size_t)i] = '=';
                if(filled < width) bar[(size_t)filled] = '>';
                double percent = 100.0 * (double)done / (double)total;
                if(phase == 0 && done && done < total && elapsed >= 0.5 &&
                   now - last_change_ms <= 750){
                    double eta = elapsed * (double)(total - done) / (double)done;
                    snprintf(line, sizeof(line),
                             "\r[%d/4] %-12s [%s] %5.1f%%  elapsed %.1fs  cpu %.1fs  eta %.1fs    ",
                             phase + 1, names[phase], bar.c_str(), percent,
                             elapsed, cpu, eta);
                }else{
                    snprintf(line, sizeof(line),
                             "\r[%d/4] %-12s [%s] %5.1f%%  elapsed %.1fs  cpu %.1fs             ",
                             phase + 1, names[phase], bar.c_str(), percent,
                             elapsed, cpu);
                }
            }else{
                int position = (int)((now / 150) % (uint64_t)(2 * width - 2));
                if(position >= width) position = 2 * width - 2 - position;
                bar[(size_t)position] = '>';
                snprintf(line, sizeof(line),
                         "\r[%d/4] %-12s [%s] working  elapsed %.1fs  cpu %.1fs    ",
                         phase + 1, names[phase], bar.c_str(), elapsed, cpu);
            }
            std::cerr << line << std::flush;
        }
        std::unique_lock<std::mutex> lock(progress_wait_mutex);
        progress_wakeup.wait_for(lock, std::chrono::milliseconds(250), []{
            return progress_stop.load(std::memory_order_acquire);
        });
    }
    if(previous >= 0) std::cerr << '\n';
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

class factor_list_t{
    static const size_t inline_capacity = 12;
    factor_power_t inline_[inline_capacity];
    size_t inline_size_;
    bool spilled_;
    std::vector<factor_power_t> heap_;

    void spill(size_t capacity){
        if(!spilled_){
            heap_.reserve(std::max(capacity, inline_capacity * 2));
            heap_.insert(heap_.end(), inline_, inline_ + inline_size_);
            inline_size_ = 0;
            spilled_ = true;
        }else if(capacity > heap_.capacity()){
            heap_.reserve(capacity);
        }
    }

public:
    factor_list_t() : inline_size_(0), spilled_(false){}
    factor_list_t(const factor_list_t &) = delete;
    factor_list_t &operator=(const factor_list_t &) = delete;

    factor_list_t(factor_list_t &&o) noexcept
        : inline_size_(o.inline_size_), spilled_(o.spilled_), heap_(std::move(o.heap_)){
        memcpy(inline_, o.inline_, inline_size_ * sizeof(factor_power_t));
        o.inline_size_ = 0;
        o.spilled_ = false;
    }

    factor_list_t &operator=(factor_list_t &&o) noexcept{
        if(this == &o) return *this;
        inline_size_ = o.inline_size_;
        spilled_ = o.spilled_;
        memcpy(inline_, o.inline_, inline_size_ * sizeof(factor_power_t));
        heap_ = std::move(o.heap_);
        o.inline_size_ = 0;
        o.spilled_ = false;
        return *this;
    }

    size_t size() const{ return spilled_ ? heap_.size() : inline_size_; }
    bool empty() const{ return size() == 0; }
    size_t capacity() const{ return spilled_ ? heap_.capacity() : inline_capacity; }
    factor_power_t &operator[](size_t i){ return spilled_ ? heap_[i] : inline_[i]; }
    const factor_power_t &operator[](size_t i) const{ return spilled_ ? heap_[i] : inline_[i]; }
    void reserve(size_t n){ if(n > inline_capacity) spill(n); }
    void push_back(factor_power_t value){
        if(!spilled_ && inline_size_ < inline_capacity){
            inline_[inline_size_++] = value;
            return;
        }
        spill(size() + 1);
        heap_.push_back(value);
    }
    void resize(size_t n){
        if(!spilled_ && n <= inline_capacity){
            inline_size_ = n;
            return;
        }
        spill(n);
        heap_.resize(n);
    }
};

struct bs_t{
    precn_t p;
    precn_t q;
    precz_t t;
    factor_list_t fp;
    factor_list_t fq;
};

static void factor_add(factor_list_t &out, uint32_t prime, uint32_t power){
    size_t first = 0, last = out.size();
    while(first < last){
        size_t mid = first + (last - first) / 2;
        if(out[mid].prime < prime) first = mid + 1;
        else last = mid;
    }
    if(first < out.size() && out[first].prime == prime){
        out[first].power += power;
        return;
    }
    size_t size = out.size();
    out.resize(size + 1);
    for(size_t i = size; i > first; --i) out[i] = out[i - 1];
    out[first] = factor_power_t{prime, power};
}
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

    void append_merged(factor_list_t &out, size_t value,
                       uint32_t multiplier = 1) const{
        while(value > 1){
            uint32_t p = smallest_[value];
            uint32_t power = 0;
            do{
                value /= p;
                ++power;
            }while(value > 1 && smallest_[value] == p);
            factor_add(out, p, power * multiplier);
        }
    }
};

static factor_list_t factor_merge(
    factor_list_t a,
    factor_list_t b){
    if(b.empty()) return a;
    if(a.empty()) return b;
    // Both child lists die at the merge.  Keep the buffer with more spare
    // capacity as the output so a growing product tree reallocates less.
    if(b.capacity() > a.capacity()) std::swap(a, b);
    size_t left = a.size();
    a.resize(left + b.size());
    size_t i = left;
    size_t j = b.size();
    size_t out = a.size();
    while(j){
        if(i && a[i - 1].prime > b[j - 1].prime){
            a[--out] = a[--i];
        }else{
            a[--out] = b[--j];
        }
    }
    while(i) a[--out] = a[--i];

    out = 0;
    for(i = 0; i < a.size(); ++i){
        if(out && a[out - 1].prime == a[i].prime){
            a[out - 1].power += a[i].power;
        }else{
            a[out++] = a[i];
        }
    }
    a.resize(out);
    return a;
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

static precn_t factor_product_small(const factor_power_t *f,
                                    size_t begin, size_t end){
    if(begin == end) return precn_t(1);
    if(end - begin == 1) return factor_pow(f[begin].prime, f[begin].power);
    size_t mid = begin + (end - begin) / 2;
    return factor_product_small(f, begin, mid) *
           factor_product_small(f, mid, end);
}

static void factor_compact(factor_list_t &f){
    size_t out = 0;
    for(size_t i = 0; i < f.size(); ++i){
        if(f[i].power) f[out++] = f[i];
    }
    f.resize(out);
}

static void factor_cancel(precn_t &p, factor_list_t &fp,
                          precn_t &q, factor_list_t &fq){
    factor_power_t common_small[32];
    size_t common_small_size = 0;
    std::vector<factor_power_t> common;
    bool common_spilled = false;
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
                factor_power_t value{fp[i].prime, power};
                if(!common_spilled && common_small_size < 32){
                    common_small[common_small_size++] = value;
                }else{
                    if(!common_spilled){
                        common.assign(common_small,
                                      common_small + common_small_size);
                        common_spilled = true;
                    }
                    common.push_back(value);
                }
            }
            ++i;
            ++j;
        }
    }
    if(!common_spilled && common_small_size == 0) return;

    precn_t divisor = common_spilled ?
        factor_product(common, 0, common.size()) :
        factor_product_small(common_small, 0, common_small_size);
    if(divisor.rsiz >= PI_FACTOR_PAIR_THRESHOLD){
        precn_t next_p, next_q;
        div_mulinv_pair_into(next_p, next_q, p, q, divisor);
        p = std::move(next_p);
        q = std::move(next_q);
    }else{
    p = p / divisor;
    q = q / divisor;
    }
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
    // 10^n = 5^n * 2^n.  Building the odd part keeps every squaring about
    // 30% shorter in binary; applying the power of two is one linear shift.
    cache.push_back(pow10_entry_t{digits, pow_u32(5, digits) << digits});
    return cache.size() - 1;
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
        // (root + 1)^2 = root^2 + 2*root + 1. Reusing the square above
        // avoids a second full NTT multiplication in the correction path.
        if(square + (root << 1) + precn_t(1) <= target){
            root = root + precn_t(1);
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
    if(PI_ENABLE_INVSQRT && digits >= PI_INVSQRT_MIN_DIGITS)
        return sqrt10005_invsqrt(digits, scale_index, pow10_cache);
    precn_t n = mul_u32(pow10_cache[scale_index].value, 10005);
    return precn_sqrt(n);
}

// A parent only needs P from its left child to form T.  Matching ilmPi's
// needp scheduling avoids forming product-tree nodes that will not be used.
static precz_t chud_signed_product_sum(const precz_t &a, const precn_t &b,
                                       const precz_t &c, const precn_t &d){
    // b and d are positive.  Multiplying magnitudes directly avoids copying
    // each huge multiplier into a temporary precz_t before the NTT product.
    precn_t ab = a.magnitude() * b;
    precn_t cd = c.magnitude() * d;
    if(a.is_negative() == c.is_negative())
        return precz_t::from_magnitude(ab + cd, a.is_negative());
    if(ab >= cd)
        return precz_t::from_magnitude(ab - cd, a.is_negative());
    return precz_t::from_magnitude(cd - ab, c.is_negative());
}

static bs_t chud_merge(bs_t l, bs_t r, bool need_p, size_t level, size_t span){
#if PI_ENABLE_FACTOR_CANCEL
    if(level >= PI_FACTOR_CANCEL_MIN_LEVEL)
        factor_cancel(l.p, l.fp, r.q, r.fq);
#endif
#if PI_ROOT_SHARED_NTT
    if(!need_p && level == 0 && l.q.rsiz >= 2048 &&
       l.t.magnitude().rsiz >= 2048 && r.q.rsiz >= 2048){
        precn_t q;
        precn_t ab;
#if PI_ROOT_SHARED_NTT_TRACE
        double shared_begin = now_sec();
#endif
        if(mul_ntt_pair_shared_right_into(q, ab, l.q, l.t.magnitude(), r.q)){
#if PI_ROOT_SHARED_NTT_TRACE
            double shared_end = now_sec();
            precn_t reference_q = l.q * r.q;
            precn_t reference_ab = l.t.magnitude() * r.q;
            double separate_end = now_sec();
            if(q != reference_q || ab != reference_ab) std::abort();
            fprintf(stderr,
                    "root_shared_ntt limbs=%zu/%zu shared=%zu ntt_pair=%.6f separate=%.6f\n",
                    l.q.rsiz, l.t.magnitude().rsiz, r.q.rsiz,
                    shared_end - shared_begin, separate_end - shared_end);
#endif
            precn_t cd = r.t.magnitude() * l.p;
            precz_t t;
            if(l.t.is_negative() == r.t.is_negative())
                t = precz_t::from_magnitude(ab + cd, l.t.is_negative());
            else if(ab >= cd)
                t = precz_t::from_magnitude(ab - cd, l.t.is_negative());
            else
                t = precz_t::from_magnitude(cd - ab, r.t.is_negative());
            if(span >= 64) progress_add((uint64_t)span);
            return bs_t{precn_t(), std::move(q), std::move(t),
                        factor_list_t(), factor_list_t()};
        }
    }
#endif
#if PI_ROOT_MERGE_PRODUCTS_PARALLEL && !defined(__EMSCRIPTEN__)
    if(!need_p && level == 0 && !show_progress && span >= 8192){
        precn_t q, ab, cd;
        auto multiply_serial_ntt = [](precn_t &out, const precn_t &x,
                                      const precn_t &y){
            bool old_parallel = precn_ntt_thread_parallel_enabled();
            precn_set_ntt_thread_parallel(false);
            out = x * y;
            precn_set_ntt_thread_parallel(old_parallel);
        };
        std::thread q_worker([&]{ multiply_serial_ntt(q, l.q, r.q); });
        std::thread ab_worker([&]{ multiply_serial_ntt(ab, l.t.magnitude(), r.q); });
        multiply_serial_ntt(cd, r.t.magnitude(), l.p);
        q_worker.join();
        ab_worker.join();
        precz_t t;
        if(l.t.is_negative() == r.t.is_negative())
            t = precz_t::from_magnitude(ab + cd, l.t.is_negative());
        else if(ab >= cd)
            t = precz_t::from_magnitude(ab - cd, l.t.is_negative());
        else
            t = precz_t::from_magnitude(cd - ab, r.t.is_negative());
        if(span >= 64) progress_add((uint64_t)span);
        return bs_t{precn_t(), std::move(q), std::move(t),
                    std::vector<factor_power_t>(), std::vector<factor_power_t>()};
    }
#endif
#if PI_TREE_SHARED_NTT
    // Levels 2 and deeper are already spread across the binary-split worker
    // set with inner NTT parallelism disabled. Reusing transforms here lowers
    // each worker's arithmetic without introducing nested worker creation.
    if(level >= 2 && l.q.rsiz >= 2048 && l.t.magnitude().rsiz >= 2048 &&
       r.q.rsiz >= 2048){
        precn_t q;
        precn_t ab;
        if(mul_ntt_pair_shared_right_into(q, ab, l.q, l.t.magnitude(), r.q)){
            precn_t p;
            precn_t cd;
            bool paired_p = false;
            if(need_p && r.p.rsiz >= 2048 && r.t.magnitude().rsiz >= 2048 &&
               l.p.rsiz >= 2048){
                paired_p = mul_ntt_pair_shared_right_into(
                    p, cd, r.p, r.t.magnitude(), l.p);
            }
            if(!paired_p){
                cd = r.t.magnitude() * l.p;
                if(need_p) p = l.p * r.p;
            }

            precz_t t;
            if(l.t.is_negative() == r.t.is_negative())
                t = precz_t::from_magnitude(ab + cd, l.t.is_negative());
            else if(ab >= cd)
                t = precz_t::from_magnitude(ab - cd, l.t.is_negative());
            else
                t = precz_t::from_magnitude(cd - ab, r.t.is_negative());

            bool keep_factors = level >= 5;
            factor_list_t fq;
            if(keep_factors) fq = factor_merge(std::move(l.fq), std::move(r.fq));
            if(need_p){
                factor_list_t fp;
                if(keep_factors) fp = factor_merge(std::move(l.fp), std::move(r.fp));
                if(span >= 64) progress_add((uint64_t)span);
                return bs_t{std::move(p), std::move(q), std::move(t),
                            std::move(fp), std::move(fq)};
            }
            if(span >= 64) progress_add((uint64_t)span);
            return bs_t{precn_t(), std::move(q), std::move(t),
                        factor_list_t(), std::move(fq)};
        }
    }
#endif
    precn_t q = l.q * r.q;
    precz_t t = chud_signed_product_sum(l.t, r.q, r.t, l.p);
    // The parent only consumes factor lists when it also cancels factors.
    // Level four consumes its children but its result reaches uncancelled
    // levels, so retaining lists there merely allocates and copies metadata.
    bool keep_factors = level >= 5;
    factor_list_t fq;
    if(keep_factors) fq = factor_merge(std::move(l.fq), std::move(r.fq));
    if(need_p){
        precn_t p = l.p * r.p;
        factor_list_t fp;
        if(keep_factors) fp = factor_merge(std::move(l.fp), std::move(r.fp));
        if(span >= 64) progress_add((uint64_t)span);
        return bs_t{std::move(p), std::move(q), std::move(t),
                    std::move(fp), std::move(fq)};
    }
    if(span >= 64) progress_add((uint64_t)span);
    return bs_t{precn_t(), std::move(q), std::move(t),
                factor_list_t(), std::move(fq)};
}

static bs_t chud_bs(size_t a, size_t b, bool need_p, size_t level,
                    const chud_factor_sieve_t &sieve){
#if PI_SPLIT_SERIAL_NTT
    struct ntt_scope_t{
        bool old;
        ntt_scope_t() : old(precn_ntt_thread_parallel_enabled()){
            precn_set_ntt_thread_parallel(false);
        }
        ~ntt_scope_t(){ precn_set_ntt_thread_parallel(old); }
    } ntt_scope;
#endif
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

        factor_list_t fp;
        fp.reserve(12);
        sieve.append_merged(fp, (size_t)(6 * k - 5));
        sieve.append_merged(fp, (size_t)(2 * k - 1));
        sieve.append_merged(fp, (size_t)(6 * k - 1));
        factor_list_t fq;
        fq.reserve(12);
        fq.push_back(factor_power_t{2, 15});
        fq.push_back(factor_power_t{3, 2});
        fq.push_back(factor_power_t{5, 3});
        fq.push_back(factor_power_t{23, 3});
        fq.push_back(factor_power_t{29, 3});
        sieve.append_merged(fq, (size_t)k, 3);
        return bs_t{std::move(p), std::move(q), std::move(t),
                    std::move(fp), std::move(fq)};
    }

    size_t m = a + (b - a) / 2;
    bs_t l;
    bs_t r;
    l = chud_bs(a, m, true, level + 1, sieve);
    r = chud_bs(m, b, need_p, level + 1, sieve);

    // This is ilmPi's factor-aware cancellation: scaling P_left and Q_right
    // by the same exact factor scales Q and T equally, preserving T/Q while
    // keeping every multiplication above this node smaller.
    return chud_merge(std::move(l), std::move(r), need_p, level, b - a);
}

#if PI_ROOT_TASK_SCHEDULER
struct pi_bs_task_t{
    size_t a;
    size_t b;
    size_t level;
    bool need_p;
    int left;
    int right;
    int parent;
    bs_t value;
};

static int pi_build_bs_tasks(std::vector<pi_bs_task_t> &tasks,
                             std::vector<int> &leaves,
                             size_t a, size_t b, bool need_p, size_t level){
    int index = (int)tasks.size();
    tasks.push_back(pi_bs_task_t{a, b, level, need_p, -1, -1, -1, bs_t()});
    if(level >= std::min<size_t>(PI_ROOT_TASK_DEPTH, PI_PARALLEL_SPLIT_DEPTH) ||
       b - a < 8192){
        leaves.push_back(index);
        return index;
    }
    size_t m = a + (b - a) / 2;
    int left = pi_build_bs_tasks(tasks, leaves, a, m, true, level + 1);
    int right = pi_build_bs_tasks(tasks, leaves, m, b, need_p, level + 1);
    tasks[index].left = left;
    tasks[index].right = right;
    tasks[left].parent = index;
    tasks[right].parent = index;
    return index;
}

static void pi_merge_bs_task(std::vector<pi_bs_task_t> &tasks, int index){
    pi_bs_task_t &task = tasks[index];
    bs_t left = std::move(tasks[task.left].value);
    bs_t right = std::move(tasks[task.right].value);
    task.value = chud_merge(std::move(left), std::move(right), task.need_p,
                            task.level, task.b - task.a);
}

static bs_t pi_chud_bs_root(size_t a, size_t b, bool need_p,
                            const chud_factor_sieve_t &sieve){
    if(PI_PARALLEL_SPLIT_DEPTH == 0 || b - a < 8192)
        return chud_bs(a, b, need_p, 0, sieve);

    std::vector<pi_bs_task_t> tasks;
    std::vector<int> leaves;
    int root = pi_build_bs_tasks(tasks, leaves, a, b, need_p, 0);
    if(leaves.size() < 2) return chud_bs(a, b, need_p, 0, sieve);

    std::vector<int> pending(tasks.size());
    for(size_t i = 0; i < tasks.size(); ++i)
        pending[i] = tasks[i].left < 0 ? 0 : 2;
    std::deque<int> queue(leaves.begin(), leaves.end());
    std::mutex mutex;
    std::condition_variable have_task;
    bool stop = false;

    // The fixed worker set is created once by the root.  A finished child
    // releases its parent immediately, so independent merges overlap without
    // layer barriers or nested worker creation.
    auto worker = [&]{
        bool old_parallel = precn_ntt_thread_parallel_enabled();
        size_t old_min_transform = precn_ntt_parallel_min_transform();
        precn_set_ntt_parallel_min_transform(PI_NESTED_NTT_MIN_TRANSFORM);
        for(;;){
            int index;
            {
                std::unique_lock<std::mutex> lock(mutex);
                have_task.wait(lock, [&]{ return stop || !queue.empty(); });
                if(stop && queue.empty()) break;
                index = queue.front();
                queue.pop_front();
            }

            pi_bs_task_t &task = tasks[index];
            precn_set_ntt_thread_parallel(task.level <= PI_NESTED_NTT_MAX_LEVEL);
            if(task.left < 0)
                task.value = chud_bs(task.a, task.b, task.need_p, task.level, sieve);
            else
                pi_merge_bs_task(tasks, index);

            std::lock_guard<std::mutex> lock(mutex);
            if(index == root){
                stop = true;
                have_task.notify_all();
                continue;
            }
            int parent = task.parent;
            if(--pending[parent] == 0){
                queue.push_back(parent);
                have_task.notify_one();
            }
        }
        precn_set_ntt_parallel_min_transform(old_min_transform);
        precn_set_ntt_thread_parallel(old_parallel);
    };

    std::vector<std::thread> workers;
    size_t worker_count = std::min<size_t>(leaves.size(), bs_threads);
    worker_count = std::max<size_t>(worker_count, 1);
    workers.reserve(worker_count - 1);
    for(size_t i = 1; i < worker_count; ++i) workers.emplace_back(worker);
    worker();
    for(size_t i = 0; i < workers.size(); ++i) workers[i].join();
    return std::move(tasks[root].value);
}
#else
static bs_t pi_chud_bs_root(size_t a, size_t b, bool need_p,
                            const chud_factor_sieve_t &sieve){
    return chud_bs(a, b, need_p, 0, sieve);
}
#endif

static std::string to_dec(const precn_t &a){
#if PI_DECIMAL_1E19
    return precn_to_decimal(a);
#else
    // Keep this fallback for platforms where 64-bit chunk division is not
    // favorable. The native default uses the faster 10^19 conversion tree.
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

static precn_t pi_pow2_minus(const precn_t &a, size_t bit){
    size_t limb = bit / 64;
    unsigned offset = (unsigned)(bit % 64);
    precn_t r;
    r.asiz = limb + 1;
    r.a = (uint64_t*)realloc(r.a, r.asiz * sizeof(uint64_t));
    memset(r.a, 0, r.asiz * sizeof(uint64_t));
    r.a[limb] = 1ULL << offset;
    r.rsiz = limb + 1;

    uint64_t borrow = 0;
    for(size_t i = 0; i < r.rsiz; ++i){
        uint64_t out;
        borrow = precn_sub_borrow(r.a[i], i < a.rsiz ? a.a[i] : 0,
                                  borrow, out);
        r.a[i] = out;
    }
    if(borrow) std::abort();
    while(r.rsiz && r.a[r.rsiz - 1] == 0) --r.rsiz;
    if(r.rsiz == 0) r.a[0] = 0;
    return r;
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
        precn_t bx = next_b * scaled_x;
        if(pi_div_bits(bx) > next + 1){
            scaled_x = scaled_x >> 1;
            bx = next_b * scaled_x;
        }
        precn_t correction = pi_pow2_minus(bx, next + 1);
        x = pi_mul_shift_right(scaled_x, correction, next);
        known = next_known;
        uint64_t fraction = target_known ?
            (uint64_t)((600.0 * (double)known) / (double)target_known) : 600;
        progress_set(100 + std::min<uint64_t>(fraction, 600));
    }
    return x;
}

static precn_t pi_div_apply_inverse(const precn_t &a, const precn_t &b,
                                    const precn_t &inverse, size_t scale){
    (void)b;
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

static precn_t pi_div_mulinv(const precn_t &a, const precn_t &b){
    if(a.rsiz == 0 || b.rsiz == 0 || a < b) return precn_t();
    if(b.rsiz == 1) return div_u64(a, b.a[0]);
    size_t scale = pi_div_bits(a) + PI_DIV_GUARD_BITS;
    precn_t inverse = pi_div_reciprocal(b, scale);
    return pi_div_apply_inverse(a, b, inverse, scale);
}

static std::string pi_digits(size_t digits){
    size_t guard = PI_GUARD_DIGITS;
    size_t work_digits = digits + guard;
    // A Chudnovsky term contributes about 14.181647 digits.  14.18 is a
    // conservative rational lower bound, so ceil(work_digits / 14.18) + 1
    // retains a full extra term without the old 14-digit overestimate.
    size_t terms = (work_digits * 50 + 708) / 709 + 1;

    if(terms > (UINT32_MAX - 1) / 6) return "error";
    bs_t bs;
    precn_t sqrt_scaled;
    double bs_seconds = 0.0;
    double sqrt_seconds = 0.0;

    auto calculate_bs = [&]{
        double begin = now_sec();
        progress_begin(0, binary_tracked_work(terms));
        chud_factor_sieve_t sieve(6 * terms + 1);
        bs = pi_chud_bs_root(0, terms, false, sieve);
        bs.t += precz_t(bs.q * CHUD_A);
        if(show_progress){
            progress_done.store(progress_total.load(std::memory_order_relaxed),
                                std::memory_order_relaxed);
        }
        bs_seconds = now_sec() - begin;
    };

    auto calculate_sqrt = [&]{
        double begin = now_sec();
        progress_begin(1);
        std::vector<pow10_entry_t> pow10_cache;
        size_t scale_index = pow10_index(work_digits * 2, pow10_cache);
        sqrt_scaled = sqrt10005_scaled(work_digits, scale_index, pow10_cache);
        sqrt_seconds = now_sec() - begin;
    };

    bool overlap = PI_OVERLAP_BS_SQRT && !show_progress &&
                   work_digits >= PI_OVERLAP_BS_SQRT_MIN_DIGITS;
#if defined(__EMSCRIPTEN__) || (defined(COUNT_NTT_CALLS) && COUNT_NTT_CALLS)
    overlap = false;
#endif
    double parallel_begin = now_sec();
    if(overlap){
        std::exception_ptr sqrt_error;
        std::thread sqrt_worker([&]{
            try{ calculate_sqrt(); }
            catch(...){ sqrt_error = std::current_exception(); }
        });
        calculate_bs();
        sqrt_worker.join();
        if(sqrt_error) std::rethrow_exception(sqrt_error);
    }else{
        calculate_bs();
        calculate_sqrt();
    }
    double t2 = now_sec();
#if defined(COUNT_NTT_CALLS) && COUNT_NTT_CALLS
    if(show_phases){ fprintf(stderr, "ntt after split_sqrt\n"); precn_ntt_call_profile_dump(); }
#endif
    if(bs.t.is_negative() || bs.t.is_zero()) return "error";
    progress_begin(2, show_progress ? 1000 : 0);
    precn_t numerator;
    precn_t pi_scaled;
    bool overlap_div = PI_OVERLAP_NUMERATOR_RECIPROCAL && overlap &&
                       PI_USE_LOCAL_MULINV_DIV && bs.t.magnitude().rsiz > 1;
    if(overlap_div){
        size_t scale = pi_div_bits(bs.q) + 19 + pi_div_bits(sqrt_scaled) +
                       PI_DIV_GUARD_BITS;
        precn_t inverse;
        std::exception_ptr inverse_error;
        std::thread inverse_worker([&]{
            try{ inverse = pi_div_reciprocal(bs.t.magnitude(), scale); }
            catch(...){ inverse_error = std::current_exception(); }
        });
        numerator = mul_u32(bs.q, 426880) * sqrt_scaled;
        inverse_worker.join();
        if(inverse_error) std::rethrow_exception(inverse_error);
        pi_scaled = pi_div_apply_inverse(numerator, bs.t.magnitude(),
                                         inverse, scale);
    }else{
        numerator = mul_u32(bs.q, 426880) * sqrt_scaled;
        progress_set(50);
        pi_scaled = (show_progress || PI_USE_LOCAL_MULINV_DIV) ?
            pi_div_mulinv(numerator, bs.t.magnitude()) :
            numerator / bs.t.magnitude();
    }
#if PI_DIV_1E10_SPECIAL
    if(guard == 10){
        precn_div_1e10_into(pi_scaled, pi_scaled);
    }else
#endif
    {
        uint64_t guard_scale = 1;
        for(size_t i = 0; i < guard; ++i) guard_scale *= 10;
        pi_scaled = pi_scaled / guard_scale;
    }
    double t3 = now_sec();
#if defined(COUNT_NTT_CALLS) && COUNT_NTT_CALLS
    if(show_phases){ fprintf(stderr, "ntt after final_div\n"); precn_ntt_call_profile_dump(); }
#endif

    progress_begin(3);
    std::string s = to_dec(pi_scaled);
    double t4 = now_sec();
#if defined(COUNT_NTT_CALLS) && COUNT_NTT_CALLS
    if(show_phases){ fprintf(stderr, "ntt after to_decimal\n"); precn_ntt_call_profile_dump(); }
#endif
    if(show_progress) progress_phase.store(-1, std::memory_order_release);
    if(show_phases){
        std::cerr << "binary_split " << bs_seconds << " sec\n";
        std::cerr << "sqrt_scale " << sqrt_seconds << " sec\n";
        if(overlap)
            std::cerr << "split_sqrt_wall " << (t2 - parallel_begin) << " sec\n";
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
#if defined(_WIN32) && !defined(__EMSCRIPTEN__)
    // A short CPU-bound run is very sensitive to desktop and scanner preemption.
    // ABOVE_NORMAL reduces that jitter without the starvation risk of HIGH/REALTIME.
    SetPriorityClass(GetCurrentProcess(), ABOVE_NORMAL_PRIORITY_CLASS);
#endif
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
        if(arg == "--bs-threads" && i + 1 < argc)
            bs_threads = (unsigned int)std::strtoul(argv[++i], nullptr, 10);
    }
    precn_set_ntt_threads(ntt_threads);
    if(bs_threads == 0) bs_threads = 1;
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
            progress_wakeup.notify_one();
            reporter.join();
        }
        throw;
    }
    if(reporter.joinable()){
        progress_stop.store(true, std::memory_order_release);
        progress_wakeup.notify_one();
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
#if defined(COUNT_NTT_CALLS) && COUNT_NTT_CALLS
    precn_ntt_call_profile_dump();
#endif
    std::cerr << "time " << sec << " sec\n";
    std::cerr << "cpu_time " << cpu_sec << " sec\n";
    return 0;
}
