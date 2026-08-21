#include"factor_integer.hpp"

#include<algorithm>
#include<array>
#include<atomic>
#include<cmath>
#ifdef CAS_SIQS_DIAGNOSTICS
#include<cstdio>
#endif
#include<cstdint>
#include<future>
#include<mutex>
#include<queue>
#include<string>
#include<thread>
#include<unordered_map>
#include<unordered_set>
#include<vector>
namespace{

static bool is_one(const precn_t &a){
    return a.rsiz == 1 && a.a[0] == 1;
}

static size_t bit_length(const precn_t &value){
    if(value.rsiz == 0) return 0;
    uint64_t top = value.a[value.rsiz - 1];
    size_t bits = (value.rsiz - 1) * 64;
    while(top){ ++bits; top >>= 1; }
    return bits;
}

static precn_t add_mod(const precn_t &a, const precn_t &b,
                       const precn_t &modulus){
    precn_t result = a + b;
    return result >= modulus ? result - modulus : result;
}

static precn_t sub_mod(const precn_t &a, const precn_t &b,
                       const precn_t &modulus){
    return a >= b ? a - b : modulus - (b - a);
}

static precn_t mul_mod(const precn_t &a, const precn_t &b,
                       const precn_t &modulus){
    return (a * b) % modulus;
}

static precn_t pow_mod(precn_t base, const precn_t &exponent,
                       const precn_t &modulus){
    precn_t result(1);
    base = base % modulus;
    for(size_t limb = exponent.rsiz; limb-- > 0;){
        uint64_t bits = exponent.a[limb];
        for(int bit = 63; bit >= 0; --bit){
            result = mul_mod(result, result, modulus);
            if((bits >> bit) & 1) result = mul_mod(result, base, modulus);
        }
    }
    return result;
}

static std::vector<uint32_t> primes_to(uint32_t limit){
    std::vector<bool> composite(limit + 1, false);
    std::vector<uint32_t> primes;
    for(uint32_t value = 2; value <= limit; ++value){
        if(composite[value]) continue;
        primes.push_back(value);
        if(value <= limit / value)
            for(uint32_t multiple = value * value; multiple <= limit;
                multiple += value) composite[multiple] = true;
    }
    return primes;
}

static uint32_t small_pow_mod(uint32_t base, uint32_t exponent,
                              uint32_t modulus){
    uint64_t result = 1;
    while(exponent){
        if(exponent & 1) result = result * base % modulus;
        exponent >>= 1;
        if(exponent) base = (uint32_t)((uint64_t)base * base % modulus);
    }
    return (uint32_t)result;
}

static uint32_t small_inverse_mod(uint32_t value, uint32_t modulus){
    int64_t old_r = modulus, r = value;
    int64_t old_t = 0, t = 1;
    while(r){
        int64_t quotient = old_r / r;
        int64_t next_r = old_r - quotient * r;
        int64_t next_t = old_t - quotient * t;
        old_r = r; r = next_r;
        old_t = t; t = next_t;
    }
    old_t %= modulus;
    if(old_t < 0) old_t += modulus;
    return (uint32_t)old_t;
}

static bool small_sqrt_mod(uint32_t value, uint32_t prime, uint32_t &root){
    value %= prime;
    if(value == 0){ root = 0; return true; }
    if(prime == 2){ root = value; return true; }
    if(small_pow_mod(value, (prime - 1) / 2, prime) != 1) return false;
    if((prime & 3) == 3){
        root = small_pow_mod(value, (prime + 1) / 4, prime);
        return true;
    }
    uint32_t odd = prime - 1, shifts = 0;
    while((odd & 1) == 0){ odd >>= 1; ++shifts; }
    uint32_t nonresidue = 2;
    while(small_pow_mod(nonresidue, (prime - 1) / 2, prime) != prime - 1)
        ++nonresidue;
    uint32_t c = small_pow_mod(nonresidue, odd, prime);
    uint32_t x = small_pow_mod(value, (odd + 1) / 2, prime);
    uint32_t t = small_pow_mod(value, odd, prime);
    uint32_t m = shifts;
    while(t != 1){
        uint32_t i = 1;
        uint32_t square = (uint32_t)((uint64_t)t * t % prime);
        while(i < m && square != 1){
            square = (uint32_t)((uint64_t)square * square % prime);
            ++i;
        }
        if(i == m) return false;
        uint32_t b = c;
        for(uint32_t j = 0; j < m - i - 1; ++j)
            b = (uint32_t)((uint64_t)b * b % prime);
        x = (uint32_t)((uint64_t)x * b % prime);
        uint32_t b2 = (uint32_t)((uint64_t)b * b % prime);
        t = (uint32_t)((uint64_t)t * b2 % prime);
        c = b2;
        m = i;
    }
    root = x;
    return true;
}

static bool inverse_mod(const precn_t &value, const precn_t &modulus,
                        precn_t &inverse, precn_t &factor){
    factor = gcd(value, modulus);
    if(!is_one(factor)) return false;
    precz_t old_r(modulus), r(value);
    precz_t old_t(0), t(1);
    while(!r.is_zero()){
        precz_t quotient = old_r / r;
        precz_t next_r = old_r - quotient * r;
        precz_t next_t = old_t - quotient * t;
        old_r = std::move(r); r = std::move(next_r);
        old_t = std::move(t); t = std::move(next_t);
    }
    precz_t signed_modulus(modulus);
    old_t %= signed_modulus;
    if(old_t.is_negative()) old_t += signed_modulus;
    inverse = old_t.magnitude();
    return true;
}

struct ecm_point{
    precn_t x, z;
};

// Fixed-size Montgomery arithmetic for ECM-sized operands. The generic
// (a*b)%n path performs a full division for every curve operation; REDC only
// uses limb multiply-adds once the modulus has been prepared.
struct ecm_mont{
    static const size_t maximum_limbs = 8;
    struct number{ std::array<uint64_t, maximum_limbs> a{}; };
    size_t limbs;
    std::array<uint64_t, maximum_limbs> modulus{};
    uint64_t inverse;
    const precn_t &normal_modulus;

    explicit ecm_mont(const precn_t &n) : limbs(n.rsiz), normal_modulus(n){
        for(size_t i = 0; i < limbs; ++i) modulus[i] = n.a[i];
        uint64_t x = 1;
        for(unsigned i = 0; i < 6; ++i) x *= 2 - modulus[0] * x;
        inverse = 0 - x;
    }

    int compare(const number &a) const{
        for(size_t i = limbs; i-- > 0;){
            if(a.a[i] != modulus[i]) return a.a[i] < modulus[i] ? -1 : 1;
        }
        return 0;
    }
    void subtract_modulus(number &a) const{
        uint64_t borrow = 0;
        for(size_t i = 0; i < limbs; ++i)
            borrow = precn_sub_borrow(a.a[i], modulus[i], borrow, a.a[i]);
    }
    number add(const number &a, const number &b) const{
        number r;
        uint64_t carry = 0;
        for(size_t i = 0; i < limbs; ++i)
            carry = precn_add_carry(a.a[i], b.a[i], carry, r.a[i]);
        if(carry || compare(r) >= 0) subtract_modulus(r);
        return r;
    }
    number sub(const number &a, const number &b) const{
        number r;
        uint64_t borrow = 0;
        for(size_t i = 0; i < limbs; ++i)
            borrow = precn_sub_borrow(a.a[i], b.a[i], borrow, r.a[i]);
        if(borrow){
            uint64_t carry = 0;
            for(size_t i = 0; i < limbs; ++i)
                carry = precn_add_carry(r.a[i], modulus[i], carry, r.a[i]);
        }
        return r;
    }
    number mul(const number &a, const number &b) const{
        std::array<uint64_t, maximum_limbs + 2> t{};
        for(size_t i = 0; i < limbs; ++i){
            uint128_t carry = 0;
            for(size_t j = 0; j < limbs; ++j){
                uint128_t z = (uint128_t)a.a[j] * b.a[i] + t[j] + carry;
                t[j] = (uint64_t)z;
                carry = z >> 64;
            }
            uint128_t top = (uint128_t)t[limbs] + carry;
            t[limbs] = (uint64_t)top;
            t[limbs + 1] += (uint64_t)(top >> 64);

            uint64_t multiplier = t[0] * inverse;
            carry = 0;
            for(size_t j = 0; j < limbs; ++j){
                uint128_t z = (uint128_t)multiplier * modulus[j] + t[j] + carry;
                if(j) t[j - 1] = (uint64_t)z;
                carry = z >> 64;
            }
            top = (uint128_t)t[limbs] + carry;
            t[limbs - 1] = (uint64_t)top;
            t[limbs] = t[limbs + 1] + (uint64_t)(top >> 64);
            t[limbs + 1] = 0;
        }
        number r;
        for(size_t i = 0; i < limbs; ++i) r.a[i] = t[i];
        if(t[limbs] || compare(r) >= 0) subtract_modulus(r);
        return r;
    }
    number encode(const precn_t &value) const{
        precn_t shifted = value << (limbs * 64);
        precn_t reduced = shifted % normal_modulus;
        number r;
        for(size_t i = 0; i < reduced.rsiz; ++i) r.a[i] = reduced.a[i];
        return r;
    }
    precn_t decode(const number &value) const{
        number one;
        one.a[0] = 1;
        number plain = mul(value, one);
        precn_t r;
        r.a = (uint64_t*)realloc(r.a, limbs * sizeof(uint64_t));
        r.asiz = limbs;
        r.rsiz = limbs;
        for(size_t i = 0; i < limbs; ++i) r.a[i] = plain.a[i];
        while(r.rsiz && r.a[r.rsiz - 1] == 0) --r.rsiz;
        return r;
    }
};

struct ecm_mont_point{ ecm_mont::number x, z; };

static ecm_mont_point ecm_mont_double(const ecm_mont_point &p,
                                      const ecm_mont::number &a24,
                                      const ecm_mont &m){
    ecm_mont::number sum = m.add(p.x, p.z), difference = m.sub(p.x, p.z);
    ecm_mont::number sum2 = m.mul(sum, sum), difference2 = m.mul(difference, difference);
    ecm_mont::number delta = m.sub(sum2, difference2);
    return {m.mul(sum2, difference2),
            m.mul(delta, m.add(difference2, m.mul(a24, delta)))};
}

static ecm_mont_point ecm_mont_add(const ecm_mont_point &a,
                                   const ecm_mont_point &b,
                                   const ecm_mont_point &difference,
                                   const ecm_mont &m){
    ecm_mont::number d1 = m.sub(a.x, a.z), s1 = m.add(a.x, a.z);
    ecm_mont::number d2 = m.sub(b.x, b.z), s2 = m.add(b.x, b.z);
    ecm_mont::number diagonal = m.mul(d1, s2), cross = m.mul(s1, d2);
    ecm_mont::number sum = m.add(diagonal, cross), delta = m.sub(diagonal, cross);
    return {m.mul(difference.z, m.mul(sum, sum)),
            m.mul(difference.x, m.mul(delta, delta))};
}

static ecm_mont_point ecm_mont_multiply(const ecm_mont_point &p,
                                        uint64_t scalar,
                                        const ecm_mont::number &a24,
                                        const ecm_mont &m){
    if(scalar == 1) return p;
    ecm_mont_point lower = p, upper = ecm_mont_double(p, a24, m);
    uint64_t bit = UINT64_C(1) << 63;
    while((scalar & bit) == 0) bit >>= 1;
    for(bit >>= 1; bit; bit >>= 1){
        ecm_mont_point sum = ecm_mont_add(lower, upper, p, m);
        if(scalar & bit){ lower = std::move(sum); upper = ecm_mont_double(upper, a24, m); }
        else{ upper = std::move(sum); lower = ecm_mont_double(lower, a24, m); }
    }
    return lower;
}

static ecm_point ecm_double(const ecm_point &point, const precn_t &a24,
                            const precn_t &modulus){
    precn_t sum = add_mod(point.x, point.z, modulus);
    precn_t difference = sub_mod(point.x, point.z, modulus);
    precn_t sum_square = mul_mod(sum, sum, modulus);
    precn_t difference_square = mul_mod(difference, difference, modulus);
    precn_t delta = sub_mod(sum_square, difference_square, modulus);
    return {mul_mod(sum_square, difference_square, modulus),
            mul_mod(delta, add_mod(difference_square,
                    mul_mod(a24, delta, modulus), modulus), modulus)};
}

static ecm_point ecm_add(const ecm_point &left, const ecm_point &right,
                         const ecm_point &difference,
                         const precn_t &modulus){
    precn_t left_sum = add_mod(left.x, left.z, modulus);
    precn_t left_difference = sub_mod(left.x, left.z, modulus);
    precn_t right_sum = add_mod(right.x, right.z, modulus);
    precn_t right_difference = sub_mod(right.x, right.z, modulus);
    precn_t diagonal = mul_mod(left_difference, right_sum, modulus);
    precn_t cross = mul_mod(left_sum, right_difference, modulus);
    precn_t sum = add_mod(diagonal, cross, modulus);
    precn_t delta = sub_mod(diagonal, cross, modulus);
    return {mul_mod(difference.z, mul_mod(sum, sum, modulus), modulus),
            mul_mod(difference.x, mul_mod(delta, delta, modulus), modulus)};
}

static ecm_point ecm_multiply(const ecm_point &point, uint64_t scalar,
                              const precn_t &a24,
                              const precn_t &modulus){
    if(scalar <= 1) return point;
    ecm_point lower = point;
    ecm_point upper = ecm_double(point, a24, modulus);
    uint64_t mask = UINT64_C(1) << 63;
    while((mask & scalar) == 0) mask >>= 1;
    mask >>= 1;
    while(mask){
        ecm_point sum = ecm_add(lower, upper, point, modulus);
        if(scalar & mask){
            lower = std::move(sum);
            upper = ecm_double(upper, a24, modulus);
        }else{
            upper = std::move(sum);
            lower = ecm_double(lower, a24, modulus);
        }
        mask >>= 1;
    }
    return lower;
}

static bool bit_test(const std::vector<uint64_t> &bits, size_t bit){
    return (bits[bit / 64] >> (bit % 64)) & 1;
}

static void bit_xor(std::vector<uint64_t> &a,
                    const std::vector<uint64_t> &b){
    for(size_t i = 0; i < a.size(); ++i) a[i] ^= b[i];
}

} // namespace

bool cas_probable_prime(const precn_t &value){
    if(value < precn_t(2)) return false;
    for(uint32_t prime : {2u, 3u, 5u, 7u, 11u, 13u, 17u, 19u, 23u, 29u,
                          31u, 37u, 41u}){
        precn_t p(prime);
        if(value == p) return true;
        if(mod_u64(value, prime).rsiz == 0) return false;
    }
    precn_t odd = value - 1;
    unsigned shifts = 0;
    while(mod_u64(odd, 2).rsiz == 0){ odd = odd >> 1; ++shifts; }
    for(uint32_t base : {2u, 3u, 5u, 7u, 11u, 13u, 17u, 19u, 23u}){
        precn_t witness = pow_mod(precn_t(base), odd, value);
        if(is_one(witness) || witness == value - 1) continue;
        bool composite = true;
        for(unsigned round = 1; round < shifts; ++round){
            witness = mul_mod(witness, witness, value);
            if(witness == value - 1){ composite = false; break; }
        }
        if(composite) return false;
    }
    return true;
}

precn_t cas_pollard_rho_factor(const precn_t &value,
                               size_t iteration_limit){
    if(mod_u64(value, 2).rsiz == 0) return precn_t(2);
    if(mod_u64(value, 3).rsiz == 0) return precn_t(3);
    constexpr size_t block = 128;
    size_t total_iterations = 0;
    for(uint64_t attempt = 1;
        attempt <= 16 && total_iterations < iteration_limit; ++attempt){
        precn_t constant(attempt * 2 + 1);
        precn_t y(attempt + 2), x, saved_y;
        precn_t factor(1), product(1);
        size_t cycle = 1;
        auto step = [&](const precn_t &current){
            return add_mod(mul_mod(current, current, value),
                           constant % value, value);
        };
        while(is_one(factor) && total_iterations < iteration_limit){
            x = y;
            for(size_t i = 0; i < cycle &&
                total_iterations < iteration_limit;
                ++i, ++total_iterations) y = step(y);
            for(size_t offset = 0; offset < cycle && is_one(factor) &&
                total_iterations < iteration_limit; offset += block){
                saved_y = y;
                product = precn_t(1);
                size_t count = std::min(block, cycle - offset);
                for(size_t i = 0; i < count; ++i, ++total_iterations){
                    y = step(y);
                    precn_t difference = x >= y ? x - y : y - x;
                    product = mul_mod(product, difference, value);
                }
                factor = gcd(product, value);
            }
            if(cycle > iteration_limit / 2) cycle = iteration_limit;
            else cycle *= 2;
        }
        if(factor == value){
            do{
                saved_y = step(saved_y);
                precn_t difference = x >= saved_y
                    ? x - saved_y : saved_y - x;
                factor = gcd(difference, value);
            }while(is_one(factor) && ++total_iterations < iteration_limit);
        }
        if(factor > precn_t(1) && factor < value) return factor;
    }
    return precn_t();
}

static precn_t ecm_factor_range(const precn_t &value, unsigned first_curve,
                                unsigned curves, uint32_t stage1_bound,
                                uint32_t stage2_bound,
                                std::atomic<bool> *stop){
    auto publish = [&](precn_t factor) -> precn_t{
        if(stop) stop->store(true, std::memory_order_relaxed);
        return factor;
    };
    if(mod_u64(value, 2).rsiz == 0) return publish(precn_t(2));
    if(stage2_bound < stage1_bound) stage2_bound = stage1_bound;
    std::vector<uint32_t> primes = primes_to(stage2_bound);
    for(unsigned local_curve = 0; local_curve < curves; ++local_curve){
        if(stop && stop->load(std::memory_order_relaxed)) break;
        unsigned curve = first_curve + local_curve;
        // Suyama's parametrization guarantees that the X:Z pair lies on the
        // generated Montgomery curve. Only this setup needs an inverse.
        uint64_t random_curve = (uint64_t)curve + UINT64_C(0x9e3779b97f4a7c15);
        random_curve = (random_curve ^ (random_curve >> 30)) *
                       UINT64_C(0xbf58476d1ce4e5b9);
        random_curve = (random_curve ^ (random_curve >> 27)) *
                       UINT64_C(0x94d049bb133111eb);
        random_curve ^= random_curve >> 31;
        precn_t sigma(random_curve | 6);
        precn_t u = sub_mod(mul_mod(sigma, sigma, value), precn_t(5), value);
        precn_t v = mul_u64(sigma, 4) % value;
        precn_t u2 = mul_mod(u, u, value);
        precn_t u3 = mul_mod(u2, u, value);
        precn_t v2 = mul_mod(v, v, value);
        precn_t v3 = mul_mod(v2, v, value);
        precn_t difference = sub_mod(v, u, value);
        precn_t numerator = mul_mod(
            mul_mod(mul_mod(difference, difference, value), difference, value),
            add_mod(mul_u64(u, 3) % value, v, value), value);
        precn_t denominator = mul_u64(mul_mod(u3, v, value), 16) % value;
        precn_t denominator_inverse, setup_factor;
        if(!inverse_mod(denominator, value, denominator_inverse, setup_factor)){
            if(setup_factor > precn_t(1) && setup_factor < value)
                return publish(std::move(setup_factor));
            continue;
        }
        precn_t a24 = mul_mod(numerator, denominator_inverse, value);
        ecm_point point{std::move(u3), std::move(v3)};
        if(value.rsiz <= ecm_mont::maximum_limbs){
            ecm_mont montgomery(value);
            ecm_mont_point fast_point{
                montgomery.encode(point.x), montgomery.encode(point.z)};
            ecm_mont::number fast_a24 = montgomery.encode(a24);
            for(uint32_t prime : primes){
                if(prime > stage1_bound) break;
                uint64_t power = prime;
                while(power <= stage1_bound / prime) power *= prime;
                fast_point = ecm_mont_multiply(
                    fast_point, power, fast_a24, montgomery);
            }
            precn_t fast_z = montgomery.decode(fast_point.z);
            precn_t factor = gcd(fast_z, value);
            if(factor > precn_t(1) && factor < value)
                return publish(std::move(factor));
            if(factor == value || stage2_bound == stage1_bound) continue;

            // Brent-style baby-step/giant-step continuation. For
            // p = kD +/- r, [p]Q is infinity when [kD]Q and [r]Q have the
            // same projective x-coordinate, so their cross product vanishes.
            const uint32_t step = 210;
            std::unordered_map<uint32_t, ecm_mont_point> babies;
            uint32_t first_giant = (stage1_bound + 1 + step / 2) / step;
            uint32_t last_giant = (stage2_bound + step / 2) / step;
            if(first_giant < 1) first_giant = 1;
            std::vector<ecm_mont_point> giants(last_giant - first_giant + 1);
            ecm_mont_point step_point = ecm_mont_multiply(
                fast_point, step, fast_a24, montgomery);
            giants[0] = ecm_mont_multiply(
                fast_point, (uint64_t)first_giant * step,
                fast_a24, montgomery);
            if(giants.size() > 1){
                giants[1] = ecm_mont_multiply(
                    fast_point, (uint64_t)(first_giant + 1) * step,
                    fast_a24, montgomery);
                for(size_t i = 2; i < giants.size(); ++i)
                    giants[i] = ecm_mont_add(
                        giants[i - 1], step_point, giants[i - 2], montgomery);
            }
            ecm_mont::number product = montgomery.encode(precn_t(1));
            std::vector<ecm_mont::number> batch;
            batch.reserve(256);
            auto finish_fast_batch = [&]() -> precn_t{
                if(batch.empty()) return precn_t();
                precn_t product_normal = montgomery.decode(product);
                precn_t batch_factor = gcd(product_normal, value);
                if(batch_factor > precn_t(1) && batch_factor < value)
                    return batch_factor;
                if(batch_factor == value){
                    for(const ecm_mont::number &entry : batch){
                        precn_t individual = gcd(montgomery.decode(entry), value);
                        if(individual > precn_t(1) && individual < value)
                            return individual;
                    }
                }
                product = montgomery.encode(precn_t(1));
                batch.clear();
                return precn_t();
            };
            for(uint32_t prime : primes){
                if(prime <= stage1_bound) continue;
                uint32_t giant_index = (prime + step / 2) / step;
                uint32_t center = giant_index * step;
                uint32_t baby_index = prime >= center
                    ? prime - center : center - prime;
                if(baby_index == 0) continue;
                auto baby = babies.find(baby_index);
                if(baby == babies.end())
                    baby = babies.emplace(baby_index,
                        ecm_mont_multiply(fast_point, baby_index,
                                          fast_a24, montgomery)).first;
                if(giant_index < first_giant || giant_index > last_giant)
                    continue;
                const ecm_mont_point &giant = giants[giant_index - first_giant];
                ecm_mont::number cross = montgomery.sub(
                    montgomery.mul(giant.x, baby->second.z),
                    montgomery.mul(baby->second.x, giant.z));
                product = montgomery.mul(product, cross);
                batch.push_back(cross);
                if(batch.size() == 256){
                    precn_t stage2_factor = finish_fast_batch();
                    if(stage2_factor.rsiz)
                        return publish(std::move(stage2_factor));
                }
            }
            factor = finish_fast_batch();
            if(factor.rsiz) return publish(std::move(factor));
            continue;
        }else{
        for(uint32_t prime : primes){
            if(prime > stage1_bound) break;
            uint64_t power = prime;
            while(power <= stage1_bound / prime) power *= prime;
            point = ecm_multiply(point, power, a24, value);
        }
        precn_t factor = gcd(point.z, value);
        if(factor > precn_t(1) && factor < value)
            return publish(std::move(factor));
        if(factor == value) continue;
        }
        // Stage 2 is substantially more expensive than another stage-1
        // curve in this straightforward prime-continuation implementation.
        // Apply it to a bounded curve subset; all requested curves still run
        // stage 1.
        if(curve >= 2) continue;

        // Stage 2 allows one additional prime factor of the curve order in
        // (B1, B2]. Batch Z-coordinate GCDs amortize the expensive division.
        precn_t batch_product(1);
        std::vector<precn_t> batch_z;
        batch_z.reserve(64);
        auto finish_batch = [&]() -> precn_t{
            if(batch_z.empty()) return precn_t();
            precn_t batch_factor = gcd(batch_product, value);
            if(batch_factor > precn_t(1) && batch_factor < value)
                return batch_factor;
            if(batch_factor == value){
                for(const precn_t &z : batch_z){
                    precn_t individual = gcd(z, value);
                    if(individual > precn_t(1) && individual < value)
                        return individual;
                }
            }
            batch_product = precn_t(1);
            batch_z.clear();
            return precn_t();
        };
        const ecm_point stage1_point = point;
        for(uint32_t prime : primes){
            if(prime <= stage1_bound) continue;
            // Stage 2 tests each remaining prime against the same stage-1
            // point. Chaining [p] multiplications changes the group-order
            // condition after the first prime and almost never finds p*B1-
            // smooth orders.
            ecm_point candidate = ecm_multiply(stage1_point, prime, a24, value);
            batch_z.push_back(candidate.z);
            batch_product = mul_mod(batch_product, candidate.z, value);
            if(batch_z.size() == 64){
                precn_t stage2_factor = finish_batch();
                if(stage2_factor.rsiz)
                    return publish(std::move(stage2_factor));
            }
        }
        precn_t stage2_factor = finish_batch();
        if(stage2_factor.rsiz) return publish(std::move(stage2_factor));
    }
    return precn_t();
}

precn_t cas_ecm_factor(const precn_t &value, unsigned curves,
                       uint32_t stage1_bound, uint32_t stage2_bound){
#ifdef __EMSCRIPTEN__
    return ecm_factor_range(value, 0, curves,
                            stage1_bound, stage2_bound, nullptr);
#else
    if(curves < 4)
        return ecm_factor_range(value, 0, curves,
                                stage1_bound, stage2_bound, nullptr);
    unsigned workers = std::thread::hardware_concurrency();
    if(workers == 0) workers = 1;
    workers = std::min<unsigned>(workers, 4);
    workers = std::min(workers, curves);
    std::vector<std::future<precn_t>> jobs;
    std::atomic<bool> stop(false);
    jobs.reserve(workers);
    unsigned first = 0;
    for(unsigned worker = 0; worker < workers; ++worker){
        unsigned count = curves / workers + (worker < curves % workers);
        unsigned begin = first;
        first += count;
        jobs.push_back(std::async(std::launch::async,
            [&, begin, count]{
                return ecm_factor_range(value, begin, count,
                                        stage1_bound, stage2_bound, &stop);
            }));
    }
    precn_t factor;
    for(auto &job : jobs){
        precn_t candidate = job.get();
        if(factor.rsiz == 0 && candidate.rsiz)
            factor = std::move(candidate);
    }
    return factor;
#endif
}

precn_t cas_siqs_factor(const precn_t &value, size_t polynomial_count,
                         size_t interval){
    // Algorithmic reference for log sieving, online GF(2) elimination, and
    // single-large-cofactor merging: https://loj.ac/s/2526450
    // This is an independent precn_t implementation; no source was copied.
    precn_t square_root = precn_sqrt(value);
    if(square_root * square_root == value) return square_root;

    struct base_prime{ uint32_t prime, root; };
    size_t input_bits = bit_length(value);
    double log_value = input_bits * std::log(2.0);
    size_t base_target = input_bits > 192
        ? (size_t)std::exp(0.363 * std::sqrt(log_value * std::log(log_value)) - 1.0)
        : 160;
    base_target = std::max<size_t>(base_target, 160);
    uint32_t prime_bound = input_bits > 192
        ? (uint32_t)std::min<size_t>(1000000, base_target * 24)
        : 4000;
    std::vector<base_prime> base;
    for(uint32_t prime : primes_to(prime_bound)){
        uint32_t residue_value = 0;
        precn_t residue = mod_u64(value, prime);
        if(residue.rsiz) residue_value = (uint32_t)residue.a[0];
        uint32_t root = 0;
        if(small_sqrt_mod(residue_value, prime, root))
            base.push_back({prime, root});
        if(base.size() >= base_target) break;
    }
    if(base.size() < 16) return precn_t();

    struct relation{
        precn_t x;
        std::vector<uint16_t> powers;
        precn_t square_multiplier;
    };
    struct partial_relation{
        precn_t x;
        std::vector<uint16_t> powers;
    };
    const size_t columns = base.size() + 1; // Column zero is the sign.
    const size_t parity_words = (columns + 63) / 64;
    const size_t dependency_margin = std::max<size_t>(128, columns / 32);
    const size_t relation_limit = columns * 4 + dependency_margin;
    std::vector<relation> relations;
    std::unordered_set<std::string> relation_keys;
    std::unordered_map<uint64_t, partial_relation> partial_relations;
    std::vector<std::vector<uint64_t>> collection_pivots(columns);
    size_t collection_rank = 0;
    std::atomic<bool> collection_complete(false);
    std::mutex relation_mutex;
#ifdef CAS_SIQS_DIAGNOSTICS
    size_t tested_candidates = 0;
    size_t smallest_remainder_bits = (size_t)-1;
    size_t invalid_relations = 0;
#endif

    auto submit_relation = [&](const precn_t &x, precn_t smooth,
                               bool negative,
                               std::vector<uint16_t> powers,
                               bool factor_smooth) -> precn_t{
        std::lock_guard<std::mutex> lock(relation_mutex);
        if(collection_complete.load(std::memory_order_relaxed))
            return precn_t();
        if(negative) powers[0] = 1;
        if(factor_smooth){
            for(size_t i = 0; i < base.size(); ++i){
                uint32_t prime = base[i].prime;
                while(smooth.rsiz && mod_u64(smooth, prime).rsiz == 0){
                    smooth = div_u64(smooth, prime);
                    ++powers[i + 1];
                }
            }
        }
        precn_t relation_x = x % value;
        precn_t square_multiplier(1);
        if(!is_one(smooth)){
#ifdef CAS_SIQS_DIAGNOSTICS
            ++tested_candidates;
            smallest_remainder_bits = std::min(smallest_remainder_bits,
                                                bit_length(smooth));
#endif
            uint64_t large_prime_limit =
                (uint64_t)base.back().prime * 100;
            if(smooth.rsiz != 1 || smooth.a[0] > large_prime_limit)
                return precn_t();
            uint64_t large_prime = smooth.a[0];
            auto found = partial_relations.find(large_prime);
            if(found == partial_relations.end()){
                partial_relations.emplace(large_prime,
                    partial_relation{std::move(relation_x), std::move(powers)});
                return precn_t();
            }
            relation_x = mul_mod(relation_x, found->second.x, value);
            for(size_t i = 0; i < columns; ++i)
                powers[i] += found->second.powers[i];
            square_multiplier = precn_t(large_prime);
            partial_relations.erase(found);
        }
        if(relations.size() >= relation_limit) return precn_t();

        std::string relation_key = (std::string)relation_x;
        relation_key.push_back(':');
        for(size_t i = 0; i < columns; ++i)
            if(powers[i]){
                relation_key += std::to_string(i);
                relation_key.push_back('=');
                relation_key += std::to_string(powers[i]);
                relation_key.push_back(',');
            }
        relation_key.push_back(':');
        relation_key += (std::string)square_multiplier;
        if(!relation_keys.emplace(std::move(relation_key)).second)
            return precn_t();

#ifdef CAS_SIQS_DIAGNOSTICS
        {
            precn_t check_right = mul_mod(square_multiplier,
                                          square_multiplier, value);
            for(size_t i = 0; i < base.size(); ++i)
                for(uint16_t exponent = 0; exponent < powers[i + 1]; ++exponent)
                    check_right = mul_mod(check_right,
                                          precn_t(base[i].prime), value);
            if(powers[0] & 1)
                check_right = check_right.rsiz ? value - check_right : precn_t();
            if(mul_mod(relation_x, relation_x, value) != check_right){
                ++invalid_relations;
                if(invalid_relations <= 4)
                    std::fprintf(stderr, "siqs: invalid relation %zu\n",
                                 relations.size());
            }
        }
#endif

        relations.push_back({std::move(relation_x), std::move(powers),
                             std::move(square_multiplier)});
        std::vector<uint64_t> parity(parity_words, 0);
        const auto &stored_powers = relations.back().powers;
        for(size_t i = 0; i < columns; ++i)
            if(stored_powers[i] & 1)
                parity[i / 64] |= UINT64_C(1) << (i % 64);
        for(size_t column = columns; column-- > 0;){
            if(!bit_test(parity, column)) continue;
            if(collection_pivots[column].empty()){
                collection_pivots[column] = std::move(parity);
                ++collection_rank;
                break;
            }
            bit_xor(parity, collection_pivots[column]);
        }
        // Counting relations alone is misleading when many polynomial-family
        // cycles occupy the same low-dimensional parity subspace.
        if(collection_rank * 4 >= columns * 3 &&
           relations.size() >= collection_rank + dependency_margin)
            collection_complete.store(true, std::memory_order_relaxed);
        return precn_t();
    };

    precn_t target_a = div_u64(square_root, std::max<size_t>(interval, 1));
    if(target_a < precn_t(2)) target_a = precn_t(2);
    size_t factors_in_a = input_bits > 192
        ? std::max<size_t>(3, (size_t)(input_bits * std::log(2.0) * 0.051 + 1.0))
        : 2;
    double target_factor = std::exp(
        bit_length(target_a) * std::log(2.0) / factors_in_a);
    size_t factor_center = 0;
    while(factor_center + 1 < base.size() &&
          base[factor_center].prime < target_factor) ++factor_center;
    size_t factor_span = std::max<size_t>(
        8, base.size() / (2 * factors_in_a * factors_in_a));
    const size_t family_size = input_bits > 192
        ? (((size_t)1 << (factors_in_a - 1)) - 1) : 4;
    std::atomic<size_t> next_family(0);
    precn_t sieve_factor;
    std::mutex factor_mutex;
    auto sieve_worker = [&]{
    size_t cached_family = (size_t)-1;
    precn_t cached_a;
    std::vector<size_t> cached_selected;
    std::vector<precn_t> cached_gamma;
    std::vector<uint16_t> cached_a_powers;
    std::vector<uint32_t> cached_a_mod;
    std::vector<uint32_t> cached_a_inverse;
    std::vector<uint32_t> cached_gamma_mod;
    const size_t sieve_size = interval * 2 + 1;
    std::vector<uint32_t> interval_remainders(base.size());
    std::vector<uint8_t> sieve_weights(base.size());
    for(size_t i = 0; i < base.size(); ++i){
        interval_remainders[i] = (uint32_t)(interval % base[i].prime);
        sieve_weights[i] = (uint8_t)std::min<int>(255, std::max<int>(1,
            (int)std::lround(std::log((double)base[i].prime) * 3.0)));
    }
    std::vector<uint8_t> sieve(sieve_size);
    std::vector<uint32_t> root1(base.size()), root2(base.size());
    std::vector<size_t> candidate_positions;
    std::vector<int32_t> candidate_slot(sieve_size);
    std::vector<int32_t> hit_head;
    std::vector<uint16_t> hit_prime;
    std::vector<int32_t> hit_next;
    candidate_positions.reserve(512);
    hit_prime.reserve(8192);
    hit_next.reserve(8192);
    uint64_t large_prime_limit = (uint64_t)base.back().prime * 100;
    double threshold_log = 0.5 * log_value + std::log((double)interval + 1.0)
                         - std::log((double)large_prime_limit) - 2.0;
    uint8_t threshold = (uint8_t)std::max<int>(1,
        std::min<int>(250, (int)std::lround(threshold_log * 3.0)));
    while(!collection_complete.load(std::memory_order_relaxed)){
        size_t family = next_family.fetch_add(1, std::memory_order_relaxed);
        size_t first_polynomial = family * family_size;
        if(first_polynomial >= polynomial_count) break;
        size_t variants = std::min(family_size,
                                   polynomial_count - first_polynomial);
        for(size_t variant = 0; variant < variants &&
            !collection_complete.load(std::memory_order_relaxed); ++variant){
        size_t polynomial = first_polynomial + variant;
        // Keep the first CRT sign fixed; the remaining factors follow Gray
        // code, yielding 2^(s-1) B values for an s-factor A.
        size_t sign_pattern = variant ^ (variant >> 1);
        if(family != cached_family){
            cached_family = family;
            cached_selected.clear();
            std::vector<bool> used(base.size(), false);
            size_t window_begin = factor_center > factor_span
                ? factor_center - factor_span : 0;
            size_t window_end = std::min(base.size(),
                                         factor_center + factor_span + 1);
            size_t window_size = window_end - window_begin;
            uint64_t family_state = UINT64_C(0x9e3779b97f4a7c15) ^
                ((uint64_t)family + 1) * UINT64_C(0xbf58476d1ce4e5b9);
            size_t attempts = 0;
            while(cached_selected.size() < factors_in_a &&
                  attempts++ < window_size * 4){
                family_state += UINT64_C(0x9e3779b97f4a7c15);
                uint64_t mixed = family_state;
                mixed = (mixed ^ (mixed >> 30)) *
                        UINT64_C(0xbf58476d1ce4e5b9);
                mixed = (mixed ^ (mixed >> 27)) *
                        UINT64_C(0x94d049bb133111eb);
                mixed ^= mixed >> 31;
                size_t index = window_begin + (size_t)(mixed % window_size);
                if(used[index] || base[index].prime == 2) continue;
                used[index] = true;
                cached_selected.push_back(index);
            }
            if(cached_selected.size() != factors_in_a) continue;
            cached_a = precn_t(1);
            for(size_t index : cached_selected)
                cached_a = mul_u64(cached_a, base[index].prime);
            cached_gamma.clear();
            cached_gamma.reserve(factors_in_a);
            for(size_t index : cached_selected){
                uint32_t q = base[index].prime;
                precn_t quotient = div_u64(cached_a, q);
                uint32_t quotient_mod = (uint32_t)mod_u64(quotient, q).a[0];
                uint32_t coefficient = (uint32_t)((uint64_t)base[index].root *
                    small_inverse_mod(quotient_mod, q) % q);
                cached_gamma.push_back(mul_u64(quotient, coefficient));
            }
            cached_a_powers.assign(columns, 0);
            for(size_t index : cached_selected)
                ++cached_a_powers[index + 1];
            cached_a_inverse.assign(base.size(), 0);
            cached_a_mod.assign(base.size(), 0);
            cached_gamma_mod.assign(base.size() * factors_in_a, 0);
            for(size_t index = 0; index < base.size(); ++index){
                uint32_t prime = base[index].prime;
                precn_t residue = mod_u64(cached_a, prime);
                if(residue.rsiz == 0) continue;
                cached_a_mod[index] = (uint32_t)residue.a[0];
                cached_a_inverse[index] = small_inverse_mod(
                    (uint32_t)residue.a[0], prime);
                for(size_t j = 0; j < factors_in_a; ++j){
                    precn_t gamma_residue = mod_u64(cached_gamma[j], prime);
                    cached_gamma_mod[index * factors_in_a + j] =
                        gamma_residue.rsiz ? (uint32_t)gamma_residue.a[0] : 0;
                }
            }
        }
        const precn_t &a = cached_a;
        const std::vector<size_t> &selected = cached_selected;
        const std::vector<uint16_t> &a_powers = cached_a_powers;
        precn_t b;
        int b_wraps = 0;
        for(size_t j = 0; j < factors_in_a; ++j){
            bool flip = j > 0 && ((sign_pattern >> (j - 1)) & 1);
            if(flip){
                if(b < cached_gamma[j]) --b_wraps;
                b = sub_mod(b, cached_gamma[j], a);
            }else{
                if(b + cached_gamma[j] >= a) ++b_wraps;
                b = add_mod(b, cached_gamma[j], a);
            }
        }

        std::fill(sieve.begin(), sieve.end(), 0);
        std::fill(root1.begin(), root1.end(), UINT32_MAX);
        std::fill(root2.begin(), root2.end(), UINT32_MAX);
        uint32_t interval_mod = 0;
        for(size_t index = 0; index < base.size(); ++index){
            uint32_t prime = base[index].prime;
            uint32_t inverse = cached_a_inverse[index];
            if(inverse == 0) continue;
            uint32_t bv = 0;
            for(size_t j = 0; j < factors_in_a; ++j){
                uint32_t term = cached_gamma_mod[index * factors_in_a + j];
                bool flip = j > 0 && ((sign_pattern >> (j - 1)) & 1);
                bv = flip ? (bv >= term ? bv - term : bv + prime - term)
                          : (uint32_t)(((uint64_t)bv + term) % prime);
            }
            int64_t correction = (int64_t)b_wraps * cached_a_mod[index];
            correction %= (int64_t)prime;
            int64_t corrected = (int64_t)bv - correction;
            corrected %= (int64_t)prime;
            if(corrected < 0) corrected += prime;
            bv = (uint32_t)corrected;
            uint32_t roots[2];
            roots[0] = (uint32_t)((uint64_t)(base[index].root + prime - bv) %
                                  prime * inverse % prime);
            uint32_t opposite = base[index].root == 0
                ? 0 : prime - base[index].root;
            roots[1] = (uint32_t)((uint64_t)(opposite + prime - bv) % prime *
                                  inverse % prime);
            root1[index] = roots[0];
            root2[index] = roots[1];
            interval_mod = interval_remainders[index];
            uint8_t weight = sieve_weights[index];
            for(unsigned which = 0; which < 2; ++which){
                uint32_t root = roots[which];
                if(which && root == roots[0]) continue;
                size_t position = (root + interval_mod) % prime;
                for(; position < sieve_size; position += prime){
                    unsigned sum = sieve[position] + weight;
                    sieve[position] = (uint8_t)std::min<unsigned>(sum, 255);
                }
            }
        }

        candidate_positions.clear();
        std::fill(candidate_slot.begin(), candidate_slot.end(), -1);
        for(size_t position = 0; position < sieve_size; ++position){
            if(sieve[position] < threshold) continue;
            candidate_slot[position] = (int32_t)candidate_positions.size();
            candidate_positions.push_back(position);
        }

        hit_head.assign(candidate_positions.size(), -1);
        hit_prime.clear();
        hit_next.clear();
        if(hit_prime.capacity() < candidate_positions.size() * 12){
            hit_prime.reserve(candidate_positions.size() * 12);
            hit_next.reserve(candidate_positions.size() * 12);
        }
        for(size_t index = 0; index < base.size(); ++index){
            if(root1[index] == UINT32_MAX) continue;
            uint32_t prime = base[index].prime;
            interval_mod = interval_remainders[index];
            uint32_t roots[2] = {root1[index], root2[index]};
            for(unsigned which = 0; which < 2; ++which){
                if(which && roots[which] == roots[0]) continue;
                size_t position = (roots[which] + interval_mod) % prime;
                for(; position < sieve_size; position += prime){
                    int32_t slot = candidate_slot[position];
                    if(slot < 0) continue;
                    hit_prime.push_back((uint16_t)index);
                    hit_next.push_back(hit_head[(size_t)slot]);
                    hit_head[(size_t)slot] = (int32_t)hit_prime.size() - 1;
                }
            }
        }

        for(size_t candidate_index = 0;
            candidate_index < candidate_positions.size(); ++candidate_index){
            int64_t signed_offset = (int64_t)candidate_positions[candidate_index]
                                  - (int64_t)interval;
            uint64_t offset = signed_offset < 0
                ? (uint64_t)(-signed_offset) : (uint64_t)signed_offset;
            precn_t step_value = mul_u64(a, offset);
            precn_t x = signed_offset < 0
                ? (b >= step_value ? b - step_value : step_value - b)
                : b + step_value;
            precn_t square = x * x;
            bool negative = square < value;
            precn_t numerator = negative ? value - square : square - value;
            if(numerator.rsiz == 0){
                precn_t factor = gcd(x, value);
                if(factor > precn_t(1) && factor < value){
                    std::lock_guard<std::mutex> lock(factor_mutex);
                    if(sieve_factor.rsiz == 0) sieve_factor = std::move(factor);
                    collection_complete.store(true, std::memory_order_relaxed);
                }
                continue;
            }
            precn_t remainder = numerator % a;
            if(remainder.rsiz) continue;
            precn_t smooth = numerator / a;
            std::vector<uint16_t> powers = a_powers;
            for(int32_t hit = hit_head[candidate_index]; hit >= 0;
                hit = hit_next[(size_t)hit]){
                size_t index = hit_prime[(size_t)hit];
                uint32_t prime = base[index].prime;
                while(smooth.rsiz && mod_u64(smooth, prime).rsiz == 0){
                    smooth = div_u64(smooth, prime);
                    ++powers[index + 1];
                }
            }
            precn_t factor = submit_relation(
                x, std::move(smooth), negative, std::move(powers), false);
            if(factor.rsiz){
                std::lock_guard<std::mutex> lock(factor_mutex);
                if(sieve_factor.rsiz == 0) sieve_factor = std::move(factor);
                collection_complete.store(true, std::memory_order_relaxed);
            }
        }
    }
    }
    };
#ifdef __EMSCRIPTEN__
    sieve_worker();
#else
    unsigned workers = std::thread::hardware_concurrency();
    if(workers == 0) workers = 1;
    workers = std::min<unsigned>(workers, 4);
    size_t family_count = (polynomial_count + family_size - 1) / family_size;
    workers = std::min<unsigned>(workers, (unsigned)std::max<size_t>(1,
                                  family_count));
    std::vector<std::future<void>> sieve_jobs;
    sieve_jobs.reserve(workers);
    for(unsigned worker = 0; worker < workers; ++worker)
        sieve_jobs.push_back(std::async(std::launch::async, sieve_worker));
    for(auto &job : sieve_jobs) job.get();
#endif
    if(sieve_factor.rsiz) return sieve_factor;
#ifdef CAS_SIQS_DIAGNOSTICS
    std::fprintf(stderr,
        "siqs: base=%zu tested=%zu relations=%zu rank=%zu partials=%zu min-rem=%zu bits invalid=%zu\n",
        base.size(), tested_candidates, relations.size(), collection_rank,
        partial_relations.size(),
        smallest_remainder_bits == (size_t)-1 ? 0 : smallest_remainder_bits,
        invalid_relations);
#endif
    if(relations.size() > collection_rank){
        const size_t relation_words = (relations.size() + 63) / 64;
        std::vector<std::vector<uint64_t>> pivot_parities(columns);
        std::vector<std::vector<uint64_t>> pivot_combinations(columns);
        std::vector<std::vector<uint64_t>> null_basis;
        size_t rank = 0;

        // Reduce the sparse relation rows of M while applying the same row
        // operations to an identity matrix.  Every row reduced to zero gives
        // a combination c with c^T*M = 0.
        for(size_t relation_index = 0; relation_index < relations.size();
            ++relation_index){
            std::vector<uint64_t> parity(parity_words, 0);
            for(size_t column = 0; column < columns; ++column)
                if(relations[relation_index].powers[column] & 1)
                    parity[column / 64] |= UINT64_C(1) << (column % 64);
            std::vector<uint64_t> combination(relation_words, 0);
            combination[relation_index / 64] |=
                UINT64_C(1) << (relation_index % 64);
            bool inserted = false;
            for(size_t column = columns; column-- > 0;){
                if(!bit_test(parity, column)) continue;
                if(pivot_parities[column].empty()){
                    pivot_parities[column] = std::move(parity);
                    pivot_combinations[column] = std::move(combination);
                    ++rank;
                    inserted = true;
                    break;
                }
                bit_xor(parity, pivot_parities[column]);
                bit_xor(combination, pivot_combinations[column]);
            }
            if(!inserted) null_basis.push_back(std::move(combination));
        }

        auto dependency_valid = [&](const std::vector<uint64_t> &dependency){
            for(size_t factor_column = 0; factor_column < columns;
                ++factor_column){
                unsigned parity = 0;
                for(size_t relation_index = 0;
                    relation_index < relations.size(); ++relation_index)
                    if(bit_test(dependency, relation_index))
                        parity ^= relations[relation_index]
                                      .powers[factor_column] & 1;
                if(parity) return false;
            }
            return true;
        };
        auto try_dependency = [&](const std::vector<uint64_t> &dependency){
            if(!dependency_valid(dependency)) return precn_t();
            precn_t left(1), right(1);
            std::vector<uint32_t> exponent_sums(columns, 0);
            for(size_t i = 0; i < relations.size(); ++i){
                if(!bit_test(dependency, i)) continue;
                left = mul_mod(left, relations[i].x, value);
                right = mul_mod(right, relations[i].square_multiplier, value);
                for(size_t j = 0; j < columns; ++j)
                    exponent_sums[j] += relations[i].powers[j];
            }
            for(size_t i = 0; i < base.size(); ++i)
                for(uint32_t exponent = exponent_sums[i + 1] / 2;
                    exponent; --exponent)
                    right = mul_mod(right, precn_t(base[i].prime), value);
            precn_t difference = left >= right ? left - right : right - left;
            precn_t factor = gcd(difference, value);
            if(factor > precn_t(1) && factor < value) return factor;
            factor = gcd(add_mod(left, right, value), value);
            return factor > precn_t(1) && factor < value
                ? factor : precn_t();
        };

#ifdef CAS_SIQS_DIAGNOSTICS
        std::fprintf(stderr, "siqs matrix: relations=%zu rank=%zu nullity=%zu\n",
                     relations.size(), rank, null_basis.size());
#endif
        size_t dependencies_tried = 0;
        size_t single_limit = std::min<size_t>(16, null_basis.size());
        for(size_t i = 0; i < single_limit; ++i){
            ++dependencies_tried;
            precn_t factor = try_dependency(null_basis[i]);
            if(factor.rsiz) return factor;
        }
        uint64_t random_state = UINT64_C(0x9e3779b97f4a7c15);
        for(size_t attempt = 0; attempt < 64 && null_basis.size() > 1;
            ++attempt){
            std::vector<uint64_t> dependency(relation_words, 0);
            size_t selected = 0;
            for(const auto &basis : null_basis){
                random_state ^= random_state >> 12;
                random_state ^= random_state << 25;
                random_state ^= random_state >> 27;
                if((random_state * UINT64_C(2685821657736338717)) & 1){
                    bit_xor(dependency, basis);
                    ++selected;
                }
            }
            if(selected < 2) continue;
            ++dependencies_tried;
            precn_t factor = try_dependency(dependency);
            if(factor.rsiz) return factor;
        }
#ifdef CAS_SIQS_DIAGNOSTICS
        std::fprintf(stderr, "siqs dependencies tried: %zu\n",
                     dependencies_tried);
#endif
    }
    return input_bits <= 192 ? cas_qs_factor(value) : precn_t();
}

precn_t cas_qs_factor(const precn_t &value, size_t maximum_relations){
    precn_t root = precn_sqrt(value);
    if(root * root == value) return root;
    root = root + 1;
    std::vector<uint32_t> base;
    for(uint32_t prime : primes_to(1000)){
        if(base.size() >= 96) break;
        precn_t residue = mod_u64(value, prime);
        uint32_t residue_u32 = residue.rsiz ? (uint32_t)residue.a[0] : 0;
        if(prime == 2 || small_pow_mod(residue_u32,
                                      (prime - 1) / 2, prime) == 1)
            base.push_back(prime);
    }
    struct relation{ precn_t x; std::vector<uint16_t> powers; };
    std::vector<relation> relations;
    size_t words = (base.size() + 63) / 64;
    std::vector<std::vector<uint64_t>> pivots(base.size());
    std::vector<std::vector<uint64_t>> pivot_combinations(base.size());
    for(size_t offset = 0; offset < maximum_relations; ++offset){
        precn_t x = root + (uint64_t)offset;
        precn_t smooth = x * x - value;
        std::vector<uint16_t> powers(base.size(), 0);
        std::vector<uint64_t> parity(words, 0);
        for(size_t i = 0; i < base.size(); ++i){
            while(smooth.rsiz && mod_u64(smooth, base[i]).rsiz == 0){
                smooth = div_u64(smooth, base[i]);
                ++powers[i];
            }
            if(powers[i] & 1) parity[i / 64] |= UINT64_C(1) << (i % 64);
        }
        if(!is_one(smooth)) continue;
        size_t index = relations.size();
        relations.push_back({x % value, std::move(powers)});
        std::vector<uint64_t> combination((maximum_relations + 63) / 64, 0);
        combination[index / 64] |= UINT64_C(1) << (index % 64);
        bool inserted = false;
        for(size_t column = base.size(); column-- > 0;){
            if(!bit_test(parity, column)) continue;
            if(pivots[column].empty()){
                pivots[column] = parity;
                pivot_combinations[column] = combination;
                inserted = true;
                break;
            }
            bit_xor(parity, pivots[column]);
            bit_xor(combination, pivot_combinations[column]);
        }
        if(inserted) continue;
        precn_t left(1), right(1);
        std::vector<uint32_t> exponent_sums(base.size(), 0);
        for(size_t i = 0; i < relations.size(); ++i){
            if(!bit_test(combination, i)) continue;
            left = mul_mod(left, relations[i].x, value);
            for(size_t j = 0; j < base.size(); ++j)
                exponent_sums[j] += relations[i].powers[j];
        }
        for(size_t i = 0; i < base.size(); ++i)
            for(uint32_t power = 0; power < exponent_sums[i] / 2; ++power)
                right = mul_mod(right, precn_t(base[i]), value);
        precn_t difference = left >= right ? left - right : right - left;
        precn_t factor = gcd(difference, value);
        if(factor > precn_t(1) && factor < value) return factor;
    }
    return precn_t();
}

static bool factor_big_impl(const precn_t &value,
                             std::vector<precn_t> &factors,
                             bool trial_division){
    if(is_one(value)) return true;
    if(cas_probable_prime(value)){
        factors.push_back(value);
        return true;
    }

    // Split numbers one below a perfect square before invoking a generic
    // factor finder. This cheaply handles a broad class of inputs via
    // a^2 - 1 = (a - 1)(a + 1), and the recursive calls may expose the same
    // structure again.
    precn_t successor = value + precn_t(1);
    precn_t successor_root = precn_sqrt(successor);
    if(successor_root * successor_root == successor){
        return factor_big_impl(successor_root - precn_t(1), factors, false) &&
               factor_big_impl(successor_root + precn_t(1), factors, false);
    }

    precn_t remaining = value;
    if(trial_division){
        // One top-level pass strips the factors for which ECM would be pure
        // overhead. Do not repeat this million-prime scan in recursive calls.
        static const std::vector<uint32_t> trial_primes = primes_to(10000000);
        for(uint32_t prime : trial_primes){
            while(mod_u64(remaining, prime).rsiz == 0){
                factors.emplace_back(prime);
                remaining = div_u64(remaining, prime);
            }
            if(is_one(remaining)) return true;
        }
    }
    if(cas_probable_prime(remaining)){
        factors.push_back(std::move(remaining));
        return true;
    }
    size_t remaining_bits = bit_length(remaining);
    precn_t factor = cas_pollard_rho_factor(remaining, 250000);
    if(factor.rsiz == 0){
        unsigned curves = remaining_bits > 160 ? 16 : 128;
        factor = cas_ecm_factor(remaining, curves, 10000, 30000);
    }
    if(factor.rsiz == 0){
        size_t polynomial_count = remaining_bits > 240 ? 512
                                : remaining_bits > 192 ? 512
                                : remaining_bits > 160 ? 1024 : 96;
        double log_remaining = remaining_bits * std::log(2.0);
        size_t sieve_interval = remaining_bits > 192
                              ? ((size_t)std::exp(8.5 + 0.015 * log_remaining) & ~(size_t)7)
                              : remaining_bits > 160 ? 8192 : 384;
        factor = cas_siqs_factor(remaining, polynomial_count, sieve_interval);
    }
    if(factor.rsiz == 0 && remaining_bits <= 240)
        factor = cas_ecm_factor(remaining, 900, 250000, 5000000);
    if(factor.rsiz == 0) factor = cas_qs_factor(remaining);
    if(factor.rsiz == 0 || factor == remaining) return false;
    return factor_big_impl(factor, factors, false) &&
           factor_big_impl(remaining / factor, factors, false);
}

bool cas_factor_big(const precn_t &value, std::vector<precn_t> &factors){
    return factor_big_impl(value, factors, true);
}
