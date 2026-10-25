#include "multiplicative_functions.hpp"

#include "factor_integer.hpp"

#include <algorithm>
#include <limits>
#include <stdexcept>

namespace cas_ntheory{
namespace{
struct prime_power{
    precn_t prime;
    size_t exponent;
};

std::vector<prime_power> factor_powers(const precz_t &value){
    if(value.is_zero())
        throw std::domain_error("multiplicative functions are undefined at zero");
    precn_t magnitude = value.magnitude();
    if(magnitude == precn_t(1)) return {};
    std::vector<precn_t> factors;
    if(!cas_factor_big(magnitude, factors))
        throw std::runtime_error("factorization budget exhausted");
    std::sort(factors.begin(), factors.end());
    std::vector<prime_power> result;
    for(precn_t &factor : factors){
        if(result.empty() || result.back().prime != factor)
            result.push_back({std::move(factor), 1});
        else
            ++result.back().exponent;
    }
    return result;
}

precn_t integer_power(precn_t base, uint64_t exponent){
    precn_t result(1);
    while(exponent){
        if(exponent & 1) result = result * base;
        exponent >>= 1;
        if(exponent) base = base * base;
    }
    return result;
}
}

precz_t euler_phi(const precz_t &value){
    std::vector<prime_power> factors = factor_powers(value);
    precn_t result = value.magnitude();
    for(const prime_power &factor : factors)
        result = (result / factor.prime) * (factor.prime - precn_t(1));
    return precz_t(std::move(result));
}

int mobius_mu(const precz_t &value){
    if(value.is_zero()) return 0;
    std::vector<prime_power> factors = factor_powers(value);
    int result = 1;
    for(const prime_power &factor : factors){
        if(factor.exponent > 1) return 0;
        result = -result;
    }
    return result;
}

precz_t divisor_sigma(uint64_t power, const precz_t &value){
    if(power > 1000000)
        throw std::out_of_range("divisor_sigma exponent exceeds the limit");
    std::vector<prime_power> factors = factor_powers(value);
    precn_t result(1);
    for(const prime_power &factor : factors){
        precn_t p_power = integer_power(factor.prime, power);
        precn_t term(1), sum(1);
        for(size_t i = 0; i < factor.exponent; ++i){
            term = term * p_power;
            sum = sum + term;
        }
        result = result * sum;
    }
    return precz_t(std::move(result));
}

size_t prime_nu(const precz_t &value){
    return factor_powers(value).size();
}

size_t prime_omega(const precz_t &value){
    size_t result = 0;
    for(const prime_power &factor : factor_powers(value)){
        if(factor.exponent > std::numeric_limits<size_t>::max() - result)
            throw std::overflow_error("prime_omega result overflows size_t");
        result += factor.exponent;
    }
    return result;
}

bool square_free_q(const precz_t &value){
    if(value.is_zero()) return false;
    for(const prime_power &factor : factor_powers(value))
        if(factor.exponent > 1) return false;
    return true;
}

bool prime_power_q(const precz_t &value){
    return value > precz_t(1) && factor_powers(value).size() == 1;
}

std::vector<precz_t> divisors(const precz_t &value, size_t maximum_count){
    if(value.is_zero()) throw std::domain_error("divisors is undefined at zero");
    std::vector<prime_power> factors = factor_powers(value);
    size_t count = 1;
    for(const prime_power &factor : factors){
        if(factor.exponent >= maximum_count ||
           count > maximum_count / (factor.exponent + 1))
            throw std::length_error("divisors result exceeds the item limit");
        count *= factor.exponent + 1;
    }
    if(count > maximum_count)
        throw std::length_error("divisors result exceeds the item limit");
    std::vector<precz_t> result{precz_t(1)};
    result.reserve(count);
    for(const prime_power &factor : factors){
        const size_t old_size = result.size();
        precn_t power(1);
        for(size_t exponent = 1; exponent <= factor.exponent; ++exponent){
            power = power * factor.prime;
            for(size_t i = 0; i < old_size; ++i)
                result.push_back(precz_t(result[i].magnitude() * power));
        }
    }
    std::sort(result.begin(), result.end());
    return result;
}
}
