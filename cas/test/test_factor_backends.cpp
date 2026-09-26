// Standalone internal tests: compile with src/*.cpp, not cas/src/*.cpp.
#include "../ntheory/factor_integer.cpp"
#include "../ntheory/integer_properties.hpp"
#include <cassert>
#include <cstdio>
#include <chrono>
#include <stdexcept>

static void require_factor(const precn_t &n, const precn_t &factor){
    assert(factor > precn_t(1) && factor < n);
    assert((n % factor).rsiz == 0);
}

int main(int argc, char **){
    for(uint32_t divisor : {2u, 3u, 65537u, UINT32_MAX}){
        precn_t a = (precn_t(1) << 521) - 1;
        precn_t expected = mod_u64(a, divisor);
        assert(remainder_u32(a, divisor) == (expected.rsiz ? expected.a[0] : 0));
        precn_t product = mul_u64(a, divisor);
        divide_exact_u32(product, divisor);
        assert(product == a);
    }
    precn_t root;
    assert(cas_ntheory::perfect_cube_root(precn_t(125), root) && root == precn_t(5));
    assert(!cas_ntheory::perfect_cube_root(precn_t(126), root));
    assert(cas_ntheory::perfect_nth_root(precn_t(1) << 240, 12, root) &&
           root == (precn_t(1) << 20));
    uint64_t outside, inside;
    assert(cas_ntheory::split_small_square_factor_u64(72, outside, inside));
    assert(outside == 6 && inside == 2);
    assert(cas_ntheory::split_small_square_factor_u64(0, outside, inside));
    assert(outside == 0);
    assert(cas_ntheory::smallest_prime_factor(1) == 0);
    precn_t n("1000036000099");
    ecm_mont m(n);
    ecm_mont_point p{m.encode(precn_t(7)), m.encode(precn_t(1))};
    auto a24 = m.encode(precn_t(3));
    auto zero = ecm_mont_multiply(p, 0, a24, m);
    assert(m.decode(zero.z).rsiz == 0);
    assert(m.decode(zero.x) == precn_t(1));
    // Find a saturated first-stage product and verify checkpoint replay
    // recovers a proper factor instead of discarding the curve.
    precn_t saturated_modulus(10403);
    ecm_mont saturated_mont(saturated_modulus);
    ecm_plan saturated_plan(100, 100);
    bool recovered = false;
    for(uint64_t x = 2; x < 100 && !recovered; ++x){
        ecm_mont_point start{saturated_mont.encode(precn_t(x)),
                             saturated_mont.encode(precn_t(1))};
        auto full = start;
        auto parameter = saturated_mont.encode(precn_t(3));
        for(uint64_t power : saturated_plan.powers)
            full = ecm_mont_multiply(full, power, parameter, saturated_mont);
        if(gcd(saturated_mont.decode(full.z), saturated_modulus) != saturated_modulus)
            continue;
        bool cancelled = false;
        precn_t factor = ecm_stage1(start, parameter, saturated_mont,
            saturated_modulus, saturated_plan, nullptr, cancelled);
        if(factor > precn_t(1) && factor < saturated_modulus){
            require_factor(saturated_modulus, factor);
            recovered = true;
        }
    }
    assert(recovered);
    // Compare rolling giants against independent scalar ladders projectively.
    auto step = ecm_mont_multiply(p, 210, a24, m);
    auto previous = step, current = ecm_mont_double(step, a24, m);
    for(uint64_t k = 3; k < 32; ++k){
        auto next = ecm_mont_add(current, step, previous, m);
        auto reference = ecm_mont_multiply(p, 210 * k, a24, m);
        assert(m.decode(m.mul(next.x, reference.z)) ==
               m.decode(m.mul(reference.x, next.z)));
        previous = current;
        current = next;
    }
    assert(cas_ecm_factor(precn_t(0)).rsiz == 0);
    assert(cas_siqs_factor(precn_t(1)).rsiz == 0);
    require_factor(precn_t(202), cas_siqs_factor(precn_t(202)));
    require_factor(precn_t(10201), cas_siqs_factor(precn_t(10201)));
    size_t notifications = 0;
    auto progress = [&](const char *stage, size_t done, size_t total){
        assert(stage && *stage);
        assert(!total || done <= total);
        ++notifications;
    };
    require_factor(n, cas_siqs_factor_progress(n, progress, 128, 512));
    assert(notifications > 2);
    notifications = 0;
    require_factor(n, cas_ecm_factor_progress(n, progress, 64, 100, 5000));
    assert(notifications > 2);
    assert(cas_factor_progress_scope::current() == nullptr);
    {
        cas_factor_progress_scope outer(progress);
        require_factor(precn_t(202), cas_ecm_factor_progress(precn_t(202),
            [](const char *, size_t, size_t){ throw std::runtime_error("callback"); }));
        assert(cas_factor_progress_scope::current() == &outer);
    }
    assert(cas_factor_progress_scope::current() == nullptr);
    bool stage2_recovered = false;
    for(unsigned curve = 0; curve < 32 && !stage2_recovered; ++curve){
        if(ecm_factor_range(n, curve, 1, 100, 100, nullptr).rsiz) continue;
        precn_t factor = ecm_factor_range(n, curve, 1, 100, 5000, nullptr);
        if(factor.rsiz){
            require_factor(n, factor);
            stage2_recovered = true;
        }
    }
    assert(stage2_recovered);
    // Small B1 exercises stage-two centers at zero and one.
    require_factor(precn_t(10403), cas_ecm_factor(precn_t(10403), 64, 5, 1000));
    if(argc > 1){
        precn_t large("3275698819458552334773298987025285875460883388189256110657795199");
        auto begin = std::chrono::steady_clock::now();
        precn_t factor = cas_siqs_factor(large, 60000, 44072);
        require_factor(large, factor);
        std::printf("SIQS factor %s\ntime %.6f sec\n",
            ((std::string)factor).c_str(), std::chrono::duration<double>(
                std::chrono::steady_clock::now() - begin).count());
    }
    std::puts("factor backends ok");
}
