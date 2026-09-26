#include"aprcl.hpp"
#include"factor_integer.hpp"

#include<algorithm>
#include<set>
#include<utility>
#include<vector>

namespace{

static bool one(const precn_t &a){ return a.rsiz == 1 && a.a[0] == 1; }

static void report(const char *stage, size_t done = 0, size_t total = 0){
    auto sink = cas_factor_progress_scope::current();
    if(sink) sink->report(stage, done, total);
}

static uint32_t remainder(const precn_t &a, uint32_t p){
    uint64_t r = 0;
    for(size_t i = a.rsiz; i-- > 0;){
        r = ((r << 32) | (a.a[i] >> 32)) % p;
        r = ((r << 32) | (uint32_t)a.a[i]) % p;
    }
    return (uint32_t)r;
}

static uint32_t small_power(uint32_t a, uint32_t e, uint32_t n){
    uint64_t r = 1;
    while(e){
        if(e & 1) r = r * a % n;
        e >>= 1;
        if(e) a = (uint32_t)((uint64_t)a * a % n);
    }
    return (uint32_t)r;
}

static bool small_prime(uint32_t n){
    if(n < 2) return false;
    if(!(n & 1)) return n == 2;
    for(uint32_t p = 3; p <= n / p; p += 2)
        if(n % p == 0) return false;
    return true;
}

static std::vector<uint32_t> prime_factors(uint32_t n){
    std::vector<uint32_t> factors;
    for(uint32_t p = 2; p <= n / p; ++p){
        if(n % p) continue;
        factors.push_back(p);
        do{ n /= p; }while(n % p == 0);
    }
    if(n > 1) factors.push_back(n);
    return factors;
}

static uint32_t prime_power(uint32_t n, uint32_t p){
    uint32_t r = 1;
    while(n % p == 0){ n /= p; r *= p; }
    return r;
}

static precn_t sub_mod(const precn_t &a, const precn_t &b, const precn_t &n){
    return a >= b ? a - b : n - (b - a);
}

static size_t bits(const precn_t &n){
    if(!n.rsiz) return 0;
    uint64_t top = n.a[n.rsiz - 1];
    size_t result = (n.rsiz - 1) * 64;
    while(top){ ++result; top >>= 1; }
    return result;
}

static bool bit(const precn_t &n, size_t i){
    return ((n.a[i / 64] >> (i % 64)) & 1) != 0;
}

static precn_t power_mod(precn_t a, const precn_t &e, const precn_t &n){
    precn_t r(1);
    a = a % n;
    for(size_t i = bits(e); i-- > 0;){
        r = (r * r) % n;
        if(bit(e, i)) r = (r * a) % n;
    }
    return r;
}

// Coefficients in (Z/nZ)[z]/Phi_(p^k)(z), in the canonical degree < phi(p^k).
// Folding modulo z^(p^k)-1 first makes both multiplication and automorphisms
// use the same reduction: z^(phi+j) = -sum z^(j+i*p^(k-1)).
using polynomial = std::vector<precn_t>;

class cyclotomic_ring{
    const precn_t &n_;
public:
    uint32_t p, order, step, degree;
    cyclotomic_ring(const precn_t &n, uint32_t prime, uint32_t r)
        : n_(n), p(prime), order(r), step(r / prime), degree(r - r / prime){}

    polynomial unit() const{
        polynomial r(degree);
        r[0] = precn_t(1);
        return r;
    }
    polynomial scalar(const precn_t &a) const{
        polynomial r(degree);
        r[0] = a % n_;
        return r;
    }
    polynomial reduce(polynomial a) const{
        for(auto &v : a) v = v % n_;
        for(uint32_t j = 0; j < step; ++j)
            if(a[degree + j].rsiz)
                for(uint32_t i = 0; i < p - 1; ++i)
                    a[j + i * step] = sub_mod(a[j + i * step],
                                               a[degree + j], n_);
        a.resize(degree);
        return a;
    }
    polynomial multiply_direct(const polynomial &a, const polynomial &b) const{
        polynomial r(order);
        if(&a == &b){
            for(uint32_t i = 0; i < degree; ++i){
                if(!a[i].rsiz) continue;
                for(uint32_t j = 0; j <= i; ++j){
                    if(!a[j].rsiz) continue;
                    precn_t term = a[i] * a[j];
                    if(i != j) term = term << 1;
                    uint32_t k = (i + j) % order;
                    r[k] = r[k] + term;
                }
            }
        }else{
            for(uint32_t i = 0; i < degree; ++i){
                if(!a[i].rsiz) continue;
                for(uint32_t j = 0; j < degree; ++j){
                    if(!b[j].rsiz) continue;
                    uint32_t k = (i + j) % order;
                    r[k] = r[k] + a[i] * b[j];
                }
            }
        }
        return reduce(std::move(r));
    }
    polynomial multiply(const polynomial &a, const polynomial &b) const{
        if(n_.rsiz < 4 || degree < 8) return multiply_direct(a, b);
        size_t guard = 0;
        for(uint32_t d = degree - 1; d; d >>= 1) ++guard;
        // Each convolution coefficient is < degree*2^(2*bits(n)). A whole-
        // limb radix above this bound prevents carries between coefficients.
        size_t stride = (2 * bits(n_) + guard + 63) / 64;
        auto pack = [&](const polynomial &v){
            precn_t r = precn_t::with_capacity(stride * degree);
            r.rsiz = stride * degree;
            std::memset(r.a, 0, r.rsiz * sizeof(uint64_t));
            for(uint32_t i = 0; i < degree; ++i)
                if(v[i].rsiz) std::memcpy(r.a + i * stride, v[i].a,
                                          v[i].rsiz * sizeof(uint64_t));
            while(r.rsiz && !r.a[r.rsiz - 1]) --r.rsiz;
            return r;
        };
        precn_t packed_a = pack(a);
        precn_t product = &a == &b ? packed_a * packed_a : packed_a * pack(b);
        polynomial r(order);
        for(uint32_t i = 0; i < 2 * degree - 1; ++i){
            size_t offset = i * stride;
            if(offset >= product.rsiz) break;
            size_t length = std::min(stride, product.rsiz - offset);
            precn_t coefficient = precn_t::with_capacity(length);
            coefficient.rsiz = length;
            std::memcpy(coefficient.a, product.a + offset, length * sizeof(uint64_t));
            while(coefficient.rsiz && !coefficient.a[coefficient.rsiz - 1]) --coefficient.rsiz;
            r[i % order] = r[i % order] + coefficient;
        }
        return reduce(std::move(r));
    }
    polynomial power(const polynomial &a, const precn_t &e) const{
        polynomial r = unit();
        for(size_t i = bits(e); i-- > 0;){
            r = multiply(r, r);
            if(bit(e, i)) r = multiply(r, a);
        }
        return r;
    }
    polynomial automorphism(const polynomial &a, uint32_t x) const{
        polynomial r(order);
        for(uint32_t i = 0; i < degree; ++i)
            r[(uint64_t)i * x % order] = a[i];
        return reduce(std::move(r));
    }
    int root_exponent(const polynomial &a) const{
        const precn_t minus_one = n_ - 1;
        for(uint32_t h = 0; h < order; ++h){
            bool equal = true;
            for(uint32_t i = 0; i < degree && equal; ++i){
                if(h < degree) equal = i == h ? one(a[i]) : !a[i].rsiz;
                else if(i % step == h - degree) equal = a[i] == minus_one;
                else equal = !a[i].rsiz;
            }
            if(equal) return (int)h;
        }
        return -1;
    }
    polynomial jacobi(const std::vector<uint32_t> &logs, uint32_t a,
                       uint32_t b) const{
        uint32_t q = (uint32_t)logs.size();
        std::vector<int64_t> counts(degree, 0);
        for(uint32_t x = 2; x < q; ++x){
            uint32_t h = (uint32_t)(((uint64_t)a * logs[x] +
                                    (uint64_t)b * logs[q + 1 - x]) % order);
            if(h < degree) ++counts[h];
            else for(uint32_t i = 0; i < p - 1; ++i) --counts[h - (i + 1) * step];
        }
        polynomial r(degree);
        for(uint32_t i = 0; i < degree; ++i){
            uint64_t magnitude = (uint64_t)(counts[i] < 0 ? -counts[i] : counts[i]);
            r[i] = precn_t(magnitude) % n_;
            if(counts[i] < 0 && r[i].rsiz) r[i] = n_ - r[i];
        }
        return r;
    }
};

static std::vector<uint32_t> logarithms(uint32_t q){
    const auto factors = prime_factors(q - 1);
    uint32_t g = 2;
    for(; g < q; ++g){
        bool primitive = true;
        for(uint32_t p : factors)
            if(small_power(g, (q - 1) / p, q) == 1){ primitive = false; break; }
        if(primitive) break;
    }
    std::vector<uint32_t> logs(q);
    uint32_t x = 1;
    for(uint32_t i = 0; i < q - 1; ++i){
        logs[x] = i;
        x = (uint32_t)((uint64_t)x * g % q);
    }
    return logs;
}

static uint32_t inverse_unit(uint32_t x, uint32_t r){
    for(uint32_t i = 1; i < r; ++i) if((uint64_t)i * x % r == 1) return i;
    return 0;
}

// Cohen/Lenstra 1987, (1.3)(i): n=u*p^k+v. Build j0 and jv using
// sigma_x^-1 and then check j0^u*jv is a p^k-th root of unity.
static int jacobi_test(const precn_t &n, uint32_t p, uint32_t r,
                       uint32_t q, const std::vector<uint32_t> &logs){
    if(r == 2){
        precn_t result = power_mod(precn_t(q), n >> 1, n);
        return one(result) ? 0 : result == n - 1 ? 1 : -1;
    }
    cyclotomic_ring ring(n, p, r);
    polynomial j = ring.jacobi(logs, 1, 1);
    uint32_t v = remainder(n, r);
    polynomial j0 = ring.unit(), jv = ring.unit();
    if(r == 4){
        polynomial j2 = ring.multiply(j, j);
        j0 = ring.multiply(j2, ring.scalar(precn_t(q)));
        if(v == 3) jv = std::move(j2);
    }else{
        if(p == 2) j = ring.multiply(j, ring.jacobi(logs, 2, 1));
        // All exponents in the two small products are less than p^k.
        std::vector<polynomial> powers;
        powers.reserve(r);
        powers.push_back(ring.unit());
        for(uint32_t i = 1; i < r; ++i)
            powers.push_back(ring.multiply(powers.back(), j));
        for(uint32_t x = 1; x < r; ++x){
            if(p == 2 ? (x % 8 != 1 && x % 8 != 3) : x % p == 0) continue;
            uint32_t inverse = inverse_unit(x, r);
            j0 = ring.multiply(j0, ring.automorphism(powers[x], inverse));
            uint32_t exponent = (uint32_t)((uint64_t)v * x / r);
            if(exponent)
                jv = ring.multiply(jv, ring.automorphism(powers[exponent], inverse));
        }
        if(p == 2 && (v % 8 == 5 || v % 8 == 7)){
            polynomial j3 = ring.jacobi(logs, 3 * (r / 8), r / 8);
            jv = ring.multiply(jv, ring.multiply(j3, j3));
        }
    }
    polynomial result = ring.multiply(ring.power(j0, div_u64(n, r)), jv);
    return ring.root_exponent(result);
}

static int jacobi_symbol(precn_t a, precn_t n){
    int sign = 1;
    a = a % n;
    while(a.rsiz){
        while(!(a.a[0] & 1)){
            a = a >> 1;
            uint64_t r = n.a[0] & 7;
            if(r == 3 || r == 5) sign = -sign;
        }
        if((a.a[0] & 3) == 3 && (n.a[0] & 3) == 3) sign = -sign;
        std::swap(a, n);
        a = a % n;
    }
    return one(n) ? sign : 0;
}

// The two-adic condition is supplied by the Lucas-Lehmer preliminary test,
// (4.4)(c), independently of any n-1 or n+1 factorization.
static cas_primality_status two_adic_condition(const precn_t &n){
    if((n.a[0] & 3) == 1){
        for(uint32_t a = 2; a <= 229; ++a){
            if(!small_prime(a)) continue;
            precn_t r = power_mod(precn_t(a), (n - 1) >> 1, n);
            if(r == n - 1) return cas_primality_status::prime;
            if(!one(r)) return cas_primality_status::composite;
        }
    }else{
        for(uint32_t u = 1; u <= 50; ++u){
            if(jacobi_symbol(precn_t(u * u + 4), n) != -1) continue;
            // alpha^2=u*alpha+1, represented by (constant, alpha coefficient).
            using quadratic = std::pair<precn_t, precn_t>;
            auto multiply = [&](const quadratic &a, const quadratic &b){
                precn_t cross = a.second * b.second;
                return quadratic((a.first * b.first + cross) % n,
                    (a.first * b.second + a.second * b.first + mul_u32(cross, u)) % n);
            };
            quadratic r(precn_t(1), precn_t()), alpha(precn_t(), precn_t(1));
            precn_t e = n + 1;
            for(size_t i = bits(e); i-- > 0;){
                r = multiply(r, r);
                if(bit(e, i)) r = multiply(r, alpha);
            }
            return r.first == n - 1 && !r.second.rsiz
                ? cas_primality_status::prime : cas_primality_status::composite;
        }
    }
    return cas_primality_status::unknown;
}

struct proof_plan{
    uint32_t t = 0;
    precn_t s;
    std::vector<uint32_t> primes;
};

static proof_plan make_plan(const precn_t &n, const cas_aprcl_options &options){
    std::set<uint32_t> candidates{2u, 6u, 12u, 24u, 36u, 60u, 120u, 180u, 360u,
        720u, 1260u, 2520u, 5040u, 10080u, 15120u, 27720u, 55440u,
        110880u, 166320u, 221760u, 332640u, 720720u};
    // Extend the divisor-rich 720720 family, keeping the character orders
    // bounded. Checked multiplication keeps the public uint32_t t valid.
    if(options.maximum_t > 720720){
        for(auto i = candidates.find(720720); i != candidates.end(); ++i){
            uint32_t t = *i;
            for(uint32_t p : {2u, 3u, 5u, 7u, 11u, 13u, 17u, 19u}){
                if(t > options.maximum_t / p) continue;
                if(prime_power(t, p) > options.maximum_prime_power / p) continue;
                candidates.insert(t * p);
            }
        }
    }
    // A surplus of 64 modulus bits makes almost every final residue larger
    // than sqrt(n), avoiding millions of divisions of n by candidates.
    precn_t proof_bound = bits(n) > 512 ? n << 128 : n;
    proof_plan fallback;
    size_t attempted = 0;
    for(uint32_t t : candidates){
        if(t > options.maximum_t) continue;
        report("APR-CL selecting parameters", ++attempted, 0);
        std::vector<uint32_t> qs;
        auto add = [&](uint32_t d){
            if(d == UINT32_MAX) return;
            uint32_t q = d + 1;
            if(q == 2 || !small_prime(q)) return;
            for(uint32_t p : prime_factors(d))
                if(prime_power(d, p) > options.maximum_prime_power) return;
            qs.push_back(q);
        };
        for(uint32_t d = 1; d <= t / d; ++d){
            if(t % d) continue;
            add(d);
            if(d != t / d) add(t / d);
        }
        std::sort(qs.begin(), qs.end());
        precn_t s(1);
        for(uint32_t q : qs) s = mul_u32(s, q);
        precn_t square = s * s;
        if(square <= proof_bound){
            if(!fallback.t && square > n) fallback = {t, s, qs};
            continue;
        }
        // Prefer the inexpensive small q-primes when surplus factors can go.
        for(size_t i = qs.size(); i-- > 0;){
            precn_t reduced = div_u64(s, qs[i]);
            if(reduced * reduced > proof_bound){
                s = std::move(reduced);
                qs.erase(qs.begin() + i);
            }
        }
        return {t, std::move(s), std::move(qs)};
    }
    return fallback;
}

} // namespace

cas_aprcl_result cas_aprcl(const precn_t &n, const cas_aprcl_options &options){
    cas_aprcl_result result;
    auto finish = [&](cas_primality_status status, const char *reason){
        result.status = status;
        result.reason = reason;
        report(status == cas_primality_status::prime ? "APR-CL prime proved" :
               status == cas_primality_status::composite ? "APR-CL composite" :
               "APR-CL proof incomplete", 1, 1);
        return result;
    };
    report("APR-CL preliminary tests");
    if(n < precn_t(2)) return finish(cas_primality_status::composite, "integer is below 2");
    if(n == precn_t(2)) return finish(cas_primality_status::prime, "small prime");
    if(!(n.a[0] & 1)){
        result.factor = precn_t(2);
        return finish(cas_primality_status::composite, "even integer");
    }
    // A bounded trial-divisor loop also proves primality for small integers.
    for(uint32_t p = 3; p <= std::min(options.trial_division_bound, 1000000u); p += 2){
        if(n < precn_t((uint64_t)p * p))
            return finish(cas_primality_status::prime, "trial division proof");
        if(!remainder(n, p)){
            result.factor = precn_t(p);
            return finish(cas_primality_status::composite, "trial divisor found");
        }
    }
    if(options.probable_prime_filter && !cas_probable_prime(n))
        return finish(cas_primality_status::composite, "Miller-Rabin witness");
    proof_plan plan = make_plan(n, options);
    if(!plan.t) return finish(cas_primality_status::unknown, "APR-CL parameter budget exhausted");
    result.t = plan.t;
    auto ps = prime_factors(plan.t);
    for(uint32_t p : ps){
        if(n == precn_t(p)) return finish(cas_primality_status::prime, "small prime");
        if(!remainder(n, p)){
            result.factor = precn_t(p);
            return finish(cas_primality_status::composite, "factor divides t");
        }
    }
    for(uint32_t q : plan.primes){
        if(n == precn_t(q)) return finish(cas_primality_status::prime, "small prime");
        if(!remainder(n, q)){
            result.factor = precn_t(q);
            return finish(cas_primality_status::composite, "factor divides proof modulus");
        }
    }
    auto condition = two_adic_condition(n);
    if(condition != cas_primality_status::prime)
        return finish(condition, "two-adic preliminary condition");
    std::vector<bool> good(ps.size(), false);
    for(size_t i = 0; i < ps.size(); ++i){
        uint32_t p = ps[i];
        good[i] = p == 2 || small_power(remainder(n, p * p), p - 1, p * p) != 1;
    }
    size_t total = 0;
    for(uint32_t q : plan.primes) total += prime_factors(q - 1).size();
    report("APR-CL Jacobi sums", 0, total);
    for(uint32_t q : plan.primes){
        auto logs = logarithms(q);
        for(size_t i = 0; i < ps.size(); ++i){
            uint32_t p = ps[i];
            if((q - 1) % p) continue;
            int h = jacobi_test(n, p, prime_power(q - 1, p), q, logs);
            report("APR-CL Jacobi sums", ++result.jacobi_tests, total);
            if(h < 0) return finish(cas_primality_status::composite, "Jacobi sum congruence failed");
            if(p != 2 && h % (int)p != 0) good[i] = true;
        }
    }
    // Exceptional p (Wieferich cases) need an auxiliary q, with an order-p
    // character even when a larger p-power happens to divide q-1.
    for(size_t i = 0; i < ps.size(); ++i){
        if(good[i]) continue;
        uint32_t p = ps[i];
        unsigned attempted = 0;
        uint32_t limit = std::min(options.additional_prime_limit, 1000000u);
        for(uint32_t q = 2 * p + 1; q <= limit && attempted < options.additional_trials;
            q += 2 * p){
            if(!small_prime(q) || std::binary_search(plan.primes.begin(), plan.primes.end(), q)) continue;
            uint32_t residue = remainder(n, q);
            if(!residue){
                if(n == precn_t(q)) return finish(cas_primality_status::prime, "small prime");
                result.factor = precn_t(q);
                return finish(cas_primality_status::composite, "auxiliary divisor found");
            }
            if(small_power(residue, (q - 1) / p, q) == 1) continue;
            ++attempted;
            report("APR-CL additional tests", ++result.additional_tests, 0);
            int h = jacobi_test(n, p, p, q, logarithms(q));
            if(h < 0 || h % (int)p == 0)
                return finish(cas_primality_status::composite, "auxiliary Jacobi condition failed");
            good[i] = true;
            break;
        }
        if(!good[i]) return finish(cas_primality_status::unknown, "auxiliary prime budget exhausted");
    }
    // The Jacobi and p-adic conditions restrict every prime divisor to a power
    // of n modulo s. Since s > sqrt(n), checking the orbit proves primality.
    precn_t base = n % plan.s, candidate(1);
    precn_t root = precn_sqrt(n);
    precn_t next_root = root + 1;
    if(root * root > n || next_root * next_root <= n)
        return finish(cas_primality_status::unknown, "integer square-root certification failed");
    report("APR-CL final divisors", 0, plan.t);
    for(uint32_t i = 1; i <= plan.t; ++i){
        candidate = (candidate * base) % plan.s;
        ++result.final_divisors;
        if(one(candidate)) return finish(cas_primality_status::prime, "Jacobi sum proof completed");
        if(candidate.rsiz && candidate <= root && !(n % candidate).rsiz){
            result.factor = candidate;
            return finish(cas_primality_status::composite, "final trial divisor found");
        }
        if((i & 255) == 0) report("APR-CL final divisors", i, plan.t);
    }
    return finish(cas_primality_status::unknown, "proof-modulus orbit did not close");
}
