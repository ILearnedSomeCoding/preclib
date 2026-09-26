// Standalone internal tests: compile with src/*.cpp, not cas/src/*.cpp.
#include "../src/factor_integer.cpp"
#include <cassert>
#include <cstdio>
#include <chrono>

static void require_factor(const precn_t &n, const precn_t &factor){
    assert(factor > precn_t(1) && factor < n);
    assert((n % factor).rsiz == 0);
}

int main(int argc, char **){
    precn_t n("1000036000099");
    ecm_mont m(n);
    ecm_mont_point p{m.encode(precn_t(7)), m.encode(precn_t(1))};
    auto a24 = m.encode(precn_t(3));
    auto zero = ecm_mont_multiply(p, 0, a24, m);
    assert(m.decode(zero.z).rsiz == 0);
    assert(m.decode(zero.x) == precn_t(1));
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
    require_factor(n, cas_siqs_factor(n, 128, 512));
    require_factor(n, cas_ecm_factor(n, 64, 100, 5000));
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
