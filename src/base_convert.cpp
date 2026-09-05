#include"../prec.hpp"

#include<vector>

#if defined(_MSC_VER) && defined(_M_X64) && !defined(__clang__)
#include<intrin.h>
#endif

#if defined(BC_TRACE) && BC_TRACE
#include<chrono>
#include<cstdio>
#endif

#if !defined(__EMSCRIPTEN__)
#include<thread>
#endif

#ifndef BC_MULINV_THRESHOLD
#define BC_MULINV_THRESHOLD 32768
#endif


#ifndef BC_CACHED_MULINV_THRESHOLD
#define BC_CACHED_MULINV_THRESHOLD 8192
#endif
#ifndef BC_CONVERT_PARALLEL_DEPTH
#define BC_CONVERT_PARALLEL_DEPTH 4
#endif
#ifndef BC_CONVERT_PARALLEL_MIN_LIMBS
// A million-digit conversion reaches 8079-limb nodes.  Splitting that level
// gives the scheduler enough independent work to balance the uneven top half
// of the conversion tree, while the next 4040-limb level remains serial.
#define BC_CONVERT_PARALLEL_MIN_LIMBS 7168
#endif

#ifndef BC_CONVERT_SERIAL_NTT
#define BC_CONVERT_SERIAL_NTT 0
#endif
#ifndef BC_DIV_1E19_SPECIAL
#define BC_DIV_1E19_SPECIAL 1
#endif

static int bc_cmp(const precn_t &a, const precn_t &b){
    if(a.rsiz != b.rsiz) return a.rsiz < b.rsiz ? -1 : 1;
    for(size_t i = a.rsiz; i > 0; --i){
        if(a.a[i - 1] != b.a[i - 1]) return a.a[i - 1] < b.a[i - 1] ? -1 : 1;
    }
    return 0;
}

static uint64_t bc_low_u64(const precn_t &a){
    return a.rsiz == 0 ? 0 : a.a[0];
}

static uint64_t bc_div_2by1(uint64_t hi, uint64_t lo, uint64_t d,
                            uint64_t &rem){
#if defined(_MSC_VER) && defined(_M_X64) && !defined(__clang__)
    return _udiv128(hi, lo, d, &rem);
#elif defined(__clang__) && defined(__x86_64__)
    __asm__ volatile("divq %2" : "+a"(lo), "+d"(hi) : "r"(d) : "cc");
    rem = hi;
    return lo;
#else
    precn_t n;
    n.asiz = 2;
    n.a = (uint64_t*)realloc(n.a, 2 * sizeof(uint64_t));
    n.a[0] = lo;
    n.a[1] = hi;
    n.rsiz = hi ? 2 : (lo ? 1 : 0);
    precn_t q = div_u64(n, d);
    rem = bc_low_u64(mod_u64(n, d));
    return bc_low_u64(q);
#endif
}

#if BC_DIV_1E19_SPECIAL
static uint64_t bc_div_2by1_1e19(uint64_t hi, uint64_t lo,
                                 uint64_t &rem){
    const uint64_t divisor = 10000000000000000000ULL;
    const uint64_t inverse = 15581492618384294730ULL;
    uint64_t qh, ql;
    precn_mul_wide(hi, inverse, qh, ql);

    uint64_t estimate_low;
    uint64_t carry = precn_add_carry(ql, lo, 0, estimate_low);
    uint64_t estimate;
    precn_add_carry(qh, hi + 1, carry, estimate);

    uint64_t r = lo - estimate * divisor;
    if(r > estimate_low){
        --estimate;
        r += divisor;
    }
    if(r >= divisor){
        ++estimate;
        r -= divisor;
    }
    rem = r;
    return estimate;
}

#endif
static unsigned bc_pow2_bits(uint32_t base){
    if(base < 2 || (base & (base - 1))) return 0;
    unsigned bits = 0;
    while(base > 1){
        ++bits;
        base >>= 1;
    }
    return bits;
}

static size_t bc_bit_length(const precn_t &a){
    if(a.rsiz == 0) return 0;
#if defined(__clang__) || defined(__GNUC__)
    return (a.rsiz - 1) * 64 + 64 - (size_t)__builtin_clzll(a.a[a.rsiz - 1]);
#else
    size_t bits = (a.rsiz - 1) * 64;
    uint64_t top = a.a[a.rsiz - 1];
    while(top){
        ++bits;
        top >>= 1;
    }
    return bits;
#endif
}

struct bc_div_plan_t{
    precn_t inverse;
    size_t scale = 0;
    bool enabled = false;
};

static void bc_split(const precn_t &a, const precn_t &p,
                     const bc_div_plan_t *plan, precn_t &q, precn_t &r){
    if(plan && plan->enabled){
        divmod_mulinv_precomputed_into(q, r, a, p, plan->inverse, plan->scale);
        return;
    }
    // Conversion repeatedly divides by the same large powers.  At this
    // aspect ratio reciprocal division wins earlier than the general division
    // dispatcher, whose threshold also has to serve short-lived operands.
    if(p.rsiz >= BC_MULINV_THRESHOLD){
        divmod_mulinv_into(q, r, a, p);
        return;
    }
    divmod_into(q, r, a, p);
}


static void bc_make_powers(uint64_t chunk_base, const precn_t &a, std::vector<precn_t> &pow2){
    // pow2[i] = chunk_base^(2^i).  These are the split points for the
    // divide-and-conquer conversion tree.
    pow2.push_back(precn_t(chunk_base));
    while(bc_cmp(a, pow2.back()) >= 0){
        pow2.push_back(pow2.back() * pow2.back());
    }
}

static void bc_make_div_plans(const std::vector<precn_t> &pow2,
                              std::vector<bc_div_plan_t> &plans){
    plans.resize(pow2.size());
    // pow2[i] splits nodes bounded by pow2[i + 1]. The root divisor is used
    // once, so leave it on the normal dispatcher; every lower cached inverse
    // is shared by at least two nodes and becomes more valuable down the tree.
    for(size_t i = 0; i + 2 < pow2.size(); ++i){
        if(pow2[i].rsiz < BC_CACHED_MULINV_THRESHOLD) continue;
        plans[i].scale = bc_bit_length(pow2[i + 1]) + 128;
        plans[i].inverse = precn_reciprocal_newton_approx(pow2[i], plans[i].scale);
        plans[i].enabled = plans[i].inverse.rsiz != 0;
    }
}
static void bc_emit_fixed_chunks(const precn_t &a, size_t level,
                                 const std::vector<precn_t> &pow2,
                                 const std::vector<bc_div_plan_t> &plans,
                                 uint64_t *chunks,
                                 unsigned int parallel_depth = 0){
#if BC_CONVERT_SERIAL_NTT
    struct ntt_scope_t{
        bool old;
        ntt_scope_t() : old(precn_ntt_thread_parallel_enabled()){
            precn_set_ntt_thread_parallel(false);
        }
        ~ntt_scope_t(){ precn_set_ntt_thread_parallel(old); }
    } ntt_scope;
#endif
    // The caller zero-initializes the complete output.  Every subtree writes
    // directly into its own fixed range, avoiding temporary vectors and the
    // repeated copying that used to happen while joining recursion results.
    if(a.rsiz == 0) return;
    if(level == 0){
        chunks[0] = bc_low_u64(a);
        return;
    }
    if(level == 1){
        uint64_t divisor = pow2[0].a[0];
        if(a.rsiz < 2){
            chunks[0] = bc_low_u64(a);
            chunks[1] = 0;
        }else{
#if BC_DIV_1E19_SPECIAL
            if(divisor == 10000000000000000000ULL){
                chunks[1] = bc_div_2by1_1e19(a.a[1], a.a[0], chunks[0]);
            }else
#endif
            chunks[1] = bc_div_2by1(a.a[1], a.a[0], divisor, chunks[0]);
        }
        return;
    }

    precn_t q, r;
    bc_split(a, pow2[level - 1], &plans[level - 1], q, r);
    size_t half = (size_t)1 << (level - 1);
#if !defined(__EMSCRIPTEN__)
    if(parallel_depth && a.rsiz >= BC_CONVERT_PARALLEL_MIN_LIMBS){
        std::thread low_worker([&]{
            bc_emit_fixed_chunks(r, level - 1, pow2, plans, chunks, parallel_depth - 1);
        });
        bc_emit_fixed_chunks(q, level - 1, pow2, plans, chunks + half, parallel_depth - 1);
        low_worker.join();
        return;
    }
#endif
    bc_emit_fixed_chunks(r, level - 1, pow2, plans, chunks, parallel_depth);
    bc_emit_fixed_chunks(q, level - 1, pow2, plans, chunks + half, parallel_depth);
}

void precn_base_convert(const precn_t &a, uint32_t base, uint32_t *out, size_t &out_siz){
    out_siz = 0;
    if(a.rsiz == 0 || base < 2) return;

    unsigned pow2_bits = bc_pow2_bits(base);
    if(pow2_bits){
        out_siz = (bc_bit_length(a) + pow2_bits - 1) / pow2_bits;
        if(!out) return;

        uint64_t mask = ((uint64_t)1 << pow2_bits) - 1;
        for(size_t i = 0; i < out_siz; ++i){
            size_t bit = i * pow2_bits;
            size_t limb = bit / 64;
            unsigned offset = (unsigned)(bit % 64);
            uint64_t digit = a.a[limb] >> offset;
            if(offset + pow2_bits > 64 && limb + 1 < a.rsiz){
                digit |= a.a[limb + 1] << (64 - offset);
            }
            out[i] = (uint32_t)(digit & mask);
        }
        return;
    }

    uint64_t power64 = base;
    size_t chunk_digits = 1;
    while(power64 <= UINT64_MAX / base){
        power64 *= base;
        ++chunk_digits;
    }

    // First convert to large chunks in base power=base^chunk_digits, then
    // expand each chunk into ordinary base digits.
    std::vector<precn_t> pow2;
    bc_make_powers(power64, a, pow2);

    size_t level = pow2.size() - 1;
    std::vector<bc_div_plan_t> plans;
    bc_make_div_plans(pow2, plans);
    std::vector<uint64_t> chunks((size_t)1 << level, 0);
    bc_emit_fixed_chunks(a, level, pow2, plans, chunks.data(), BC_CONVERT_PARALLEL_DEPTH);
    while(!chunks.empty() && chunks.back() == 0) chunks.pop_back();

    size_t top_digits = 0;
    for(uint64_t top = chunks.back(); top; top /= base) ++top_digits;
    out_siz = (chunks.size() - 1) * chunk_digits + top_digits;
    if(!out) return;

    size_t out_index = 0;
    for(size_t ci = 0; ci < chunks.size(); ++ci){
        uint64_t rem = chunks[ci];
        size_t limit = ci + 1 == chunks.size() ? top_digits : chunk_digits;
        for(size_t i = 0; i < limit; ++i){
            out[out_index++] = (uint32_t)(rem % base);
            rem /= base;
        }
    }
}

std::string precn_to_decimal(const precn_t &a){
    if(a.rsiz == 0) return "0";
#if defined(BC_TRACE) && BC_TRACE
    using bc_clock_t = std::chrono::steady_clock;
    bc_clock_t::time_point trace_begin = bc_clock_t::now();
#endif

    // 10^19 fits in uint64_t.  Keeping these full chunks through the whole
    // conversion tree avoids the final expansion into one base-10 digit per
    // byte and also removes one split level compared with 10^9 chunks.
    const uint64_t chunk_base = 10000000000000000000ULL;
    std::vector<precn_t> pow2;
    bc_make_powers(chunk_base, a, pow2);
#if defined(BC_TRACE) && BC_TRACE
    bc_clock_t::time_point trace_powers = bc_clock_t::now();
#endif

    size_t level = pow2.size() - 1;
    std::vector<bc_div_plan_t> plans;
    bc_make_div_plans(pow2, plans);
    std::vector<uint64_t> chunks((size_t)1 << level, 0);
    bc_emit_fixed_chunks(a, level, pow2, plans, chunks.data(), BC_CONVERT_PARALLEL_DEPTH);
    while(!chunks.empty() && chunks.back() == 0) chunks.pop_back();
    if(chunks.empty()) return "0";
#if defined(BC_TRACE) && BC_TRACE
    bc_clock_t::time_point trace_emit = bc_clock_t::now();
#endif

    std::string result = std::to_string(chunks.back());
    result.reserve(chunks.size() * 19);
    for(size_t i = chunks.size() - 1; i > 0; --i){
        uint64_t value = chunks[i - 1];
        size_t start = result.size();
        result.append(19, '0');
        for(size_t j = 0; j < 19; ++j){
            result[start + 18 - j] = (char)('0' + value % 10);
            value /= 10;
        }
    }
#if defined(BC_TRACE) && BC_TRACE
    bc_clock_t::time_point trace_end = bc_clock_t::now();
    fprintf(stderr, "decimal_profile powers=%.6f emit=%.6f format=%.6f\n",
            std::chrono::duration<double>(trace_powers - trace_begin).count(),
            std::chrono::duration<double>(trace_emit - trace_powers).count(),
            std::chrono::duration<double>(trace_end - trace_emit).count());
#endif
    return result;
}
