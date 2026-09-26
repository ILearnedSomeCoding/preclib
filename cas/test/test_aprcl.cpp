#include"../ntheory/aprcl.cpp"

#include<cassert>
#include<chrono>
#include<iostream>

static bool trial_prime(uint64_t n){
    if(n < 2) return false;
    for(uint64_t d = 2; d <= n / d; ++d) if(n % d == 0) return false;
    return true;
}

static void test_ring(){
    precn_t n(89);
    cyclotomic_ring ring(n, 3, 3);
    auto j = ring.jacobi(logarithms(7), 1, 1);
    // Primitive root 3 modulo 7 gives the conjugate of 2+3*z.
    assert(j[0] == precn_t(88) && j[1] == precn_t(86));
    assert(jacobi_test(n, 3, 3, 7, logarithms(7)) >= 0);
    for(uint32_t p : {2u, 3u, 5u, 7u}){
        for(uint32_t r : {p, p * p}){
            cyclotomic_ring current(n, p, r);
            polynomial a(current.degree), z(current.order);
            for(uint32_t i = 0; i < current.degree; ++i) a[i] = precn_t(i + 2);
            assert(current.multiply(a, current.unit()) == a);
            for(uint32_t x = 1; x < r; ++x){
                if(x % p == 0) continue;
                assert(current.automorphism(current.automorphism(a, x),
                                              inverse_unit(x, r)) == a);
            }
            for(uint32_t h = 0; h < r; ++h){
                std::fill(z.begin(), z.end(), precn_t());
                z[h] = precn_t(1);
                assert(current.root_exponent(current.reduce(z)) == (int)h);
            }
        }
    }
    // Every prime must pass every applicable prime-power character, including
    // the k=1, k=2 and k>=3 two-adic branches and all four odd residues mod 8.
    for(uint32_t q : {3u, 5u, 7u, 17u, 19u, 41u, 97u, 101u}){
        auto logs = logarithms(q);
        for(uint32_t p : prime_factors(q - 1)){
            uint32_t r = prime_power(q - 1, p);
            for(uint32_t value : {43u, 53u, 59u, 61u, 71u, 73u, 79u, 89u, 103u}){
                if(value != p && value != q){
                    assert(jacobi_test(precn_t(value), p, r, q, logs) >= 0);
                    assert(jacobi_test(precn_t(value), p, p, q, logs) >= 0);
                }
            }
        }
    }
    for(unsigned width : {255u, 256u, 257u, 511u, 3330u}){
        precn_t modulus = (precn_t(1) << width) - 19;
        for(auto pair : {std::make_pair(2u, 16u), std::make_pair(3u, 27u),
                         std::make_pair(5u, 25u), std::make_pair(13u, 13u)}){
            cyclotomic_ring current(modulus, pair.first, pair.second);
            polynomial a(current.degree, modulus - 1), b(current.degree);
            for(uint32_t i = 0; i < current.degree; ++i)
                b[i] = i % 3 == 0 ? precn_t() : modulus - (i + 1);
            assert(current.multiply(a, a) == current.multiply_direct(a, a));
            assert(current.multiply(a, b) == current.multiply_direct(a, b));
        }
    }
}

static void test_exhaustive(){
    cas_aprcl_options options;
    options.trial_division_bound = 0;
    options.probable_prime_filter = false;
    size_t cyclotomic_proofs = 0, rejected = 0, auxiliary_proofs = 0;
    for(uint32_t n = 0; n <= 10000; ++n){
        auto result = cas_aprcl(precn_t(n), options);
        if(trial_prime(n)){
            if(result.status != cas_primality_status::prime)
                std::cerr << "prime rejected: " << n << " " << result.reason << '\n';
            assert(result.status == cas_primality_status::prime);
            if(result.jacobi_tests) ++cyclotomic_proofs;
            if(result.additional_tests) ++auxiliary_proofs;
        }else{
            assert(result.status != cas_primality_status::prime);
            if(result.status == cas_primality_status::composite) ++rejected;
            if(result.factor.rsiz){
                assert(result.factor > precn_t(1) && result.factor < precn_t(n));
                assert(!(precn_t(n) % result.factor).rsiz);
            }
        }
    }
    assert(cyclotomic_proofs > 100 && rejected > 2000);
    std::cout << "exhaustive Jacobi proofs " << cyclotomic_proofs
              << ", auxiliary proofs " << auxiliary_proofs << '\n';
}

static void test_large(){
    for(const char *text : {"18446744073709551557", "170141183460469231731687303715884105727",
                           "59649589127497217", "5704689200685129054721"}){
        auto result = cas_aprcl(precn_t(std::string(text)));
        if(result.status != cas_primality_status::prime)
            std::cerr << text << ": " << result.reason << '\n';
        assert(result.status == cas_primality_status::prime && result.jacobi_tests > 0);
    }
    // Strong pseudoprimes are rejected; no passing MR result is a proof.
    cas_aprcl_options without_filter;
    without_filter.probable_prime_filter = false;
    without_filter.trial_division_bound = 0;
    for(const char *text : {"341550071728321", "3825123056546413051",
                           "318665857834031151167461", "3317044064679887385961981"}){
        assert(cas_aprcl(precn_t(std::string(text))).status == cas_primality_status::composite);
        assert(cas_aprcl(precn_t(std::string(text)), without_filter).status ==
               cas_primality_status::composite);
    }
    for(uint32_t p : {1009u, 10007u, 65537u})
        assert(cas_aprcl(precn_t((uint64_t)p * p), without_filter).status ==
               cas_primality_status::composite);
    std::string last_stage;
    size_t notifications = 0;
    {
        cas_factor_progress_scope scope([&](const char *stage, size_t, size_t){
            last_stage = stage;
            ++notifications;
        });
        assert(cas_aprcl(precn_t(std::string("18446744073709551557"))).status ==
               cas_primality_status::prime);
    }
    assert(notifications > 4 && last_stage == "APR-CL prime proved");
    cas_aprcl_options options;
    options.maximum_t = 2;
    auto incomplete = cas_aprcl(precn_t(std::string("170141183460469231731687303715884105727")), options);
    assert(incomplete.status == cas_primality_status::unknown);
    options = cas_aprcl_options();
    options.maximum_prime_power = 1;
    options.trial_division_bound = 0;
    assert(cas_aprcl(precn_t(1009), options).status == cas_primality_status::unknown);
    precn_t thousand(1);
    for(unsigned i = 0; i < 999; ++i) thousand = mul_u32(thousand, 10);
    thousand = thousand + 7;
    auto plan = make_plan(thousand, cas_aprcl_options());
    assert(plan.t > 720720 && plan.t <= cas_aprcl_options().maximum_t);
    assert(plan.s * plan.s > thousand);
    for(uint32_t q : plan.primes){
        assert(small_prime(q) && plan.t % (q - 1) == 0);
        for(uint32_t p : prime_factors(q - 1))
            assert(prime_power(q - 1, p) <= cas_aprcl_options().maximum_prime_power);
    }
    options = cas_aprcl_options();
    options.maximum_t = 720720;
    precn_t edge = (precn_t(1) << 1500) - 1;
    auto fallback = make_plan(edge, options);
    assert(fallback.t && fallback.s * fallback.s > edge);
    assert(fallback.s * fallback.s <= (edge << 128));
}

int main(int argc, char **argv){
    auto start = std::chrono::steady_clock::now();
    test_ring();
    test_exhaustive();
    test_large();
    if(argc > 1 && std::string(argv[1]) == "--large"){
        precn_t n(1);
        for(unsigned i = 0; i < 100; ++i) n = mul_u32(n, 10);
        n = n + 267;
        auto result = cas_aprcl(n);
        std::cout << "100-digit: " << result.reason << " t=" << result.t
                  << " Jacobi=" << result.jacobi_tests << '\n';
        assert(result.status == cas_primality_status::prime);
    }
    if(argc > 1 && std::string(argv[1]) == "--thousand"){
        precn_t n(1);
        for(unsigned i = 0; i < 999; ++i) n = mul_u32(n, 10);
        n = n + 7;
        cas_factor_progress_scope progress([](const char *stage, size_t done, size_t total){
            if(total && (done == total ||
                         (total <= 1000 ? done % 50 == 0 : done % 262144 == 0)))
                std::cout << stage << " " << done << '/' << total << std::endl;
        });
        auto result = cas_aprcl(n);
        std::cout << "1000-digit: " << result.reason << " t=" << result.t
                  << " Jacobi=" << result.jacobi_tests
                  << " orbit=" << result.final_divisors << '\n';
        assert(result.status == cas_primality_status::prime);
    }
    std::cout << "aprcl ok\ntime "
              << std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count()
              << " sec\n";
}
