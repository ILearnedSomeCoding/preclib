#include"../prec_cas.hpp"

#include<algorithm>
#include<cmath>
#include<cstdio>
#include<cstring>
#include<cstdlib>
#include<functional>
#include<iterator>
#include<limits>
#include<map>
#include<stdexcept>
#include<unordered_map>
#include<unordered_set>
#include<utility>

namespace{

static precz_t rational_integer(const precq_t &value){
    precz_t result(value.numerator());
    return value.is_negative() ? -result : result;
}

static exact_value normalized_rational(precq_t value){
    if(value.denominator() == precn_t(1))
        return exact_value(rational_integer(value));
    return exact_value(std::move(value));
}

static uint64_t hash_mix(uint64_t hash, uint64_t value){
    value ^= value >> 30;
    value *= UINT64_C(0xbf58476d1ce4e5b9);
    value ^= value >> 27;
    value *= UINT64_C(0x94d049bb133111eb);
    value ^= value >> 31;
    hash ^= value + UINT64_C(0x9e3779b97f4a7c15) + (hash << 6) + (hash >> 2);
    return hash;
}

static uint64_t hash_natural(const precn_t &value){
    uint64_t hash = hash_mix(UINT64_C(0x6e61747572616c), value.rsiz);
    for(size_t i = 0; i < value.rsiz; ++i) hash = hash_mix(hash, value.a[i]);
    return hash;
}

static uint64_t hash_exact_value(const exact_value &value){
    if(value.is_approximate()){
        const Number &number = value.number();
        uint64_t precision_bits = 0;
        double precision = number.precision();
        std::memcpy(&precision_bits, &precision, sizeof(precision_bits));
        uint64_t hash = hash_mix(UINT64_C(0x617070726f78696d),
                                 hash_natural(number.significand().magnitude()));
        hash = hash_mix(hash, number.significand().is_negative());
        hash = hash_mix(hash, (uint64_t)number.radix_point());
        return hash_mix(hash, precision_bits);
    }
    if(value.is_integer()){
        const precz_t &integer = value.integer();
        uint64_t hash = hash_mix(UINT64_C(0x696e7465676572),
                                 integer.is_negative());
        return hash_mix(hash, hash_natural(integer.magnitude()));
    }
    precq_t rational = value.rational();
    uint64_t hash = hash_mix(UINT64_C(0x726174696f6e616c),
                             rational.is_negative());
    hash = hash_mix(hash, hash_natural(rational.numerator()));
    return hash_mix(hash, hash_natural(rational.denominator()));
}

static bool integer_i64(const exact_value &value, int64_t &result){
    if(!value.is_integer()) return false;
    const precz_t &integer = value.integer();
    const precn_t &magnitude = integer.magnitude();
    if(magnitude.rsiz > 1) return false;
    uint64_t bits = magnitude.rsiz ? magnitude.a[0] : 0;
    if(integer.is_negative()){
        if(bits > (uint64_t)INT64_MAX + 1) return false;
        result = bits == (uint64_t)INT64_MAX + 1
            ? INT64_MIN : -(int64_t)bits;
    }else{
        if(bits > (uint64_t)INT64_MAX) return false;
        result = (int64_t)bits;
    }
    return true;
}

static bool approximate_integer_i64(const exact_value &value, int64_t &result){
    if(!value.is_approximate()) return false;
    const Number &number = value.number();
    precz_t integer = number.to_integer();
    if(Number(integer) != number || integer.magnitude().rsiz > 1) return false;
    uint64_t magnitude = integer.magnitude().rsiz
        ? integer.magnitude().a[0] : 0;
    if(integer.is_negative()){
        if(magnitude > (uint64_t)INT64_MAX + 1) return false;
        result = magnitude == (uint64_t)INT64_MAX + 1
            ? INT64_MIN : -(int64_t)magnitude;
    }else{
        if(magnitude > (uint64_t)INT64_MAX) return false;
        result = (int64_t)magnitude;
    }
    return true;
}

static exact_value exact_pow(exact_value base, int64_t exponent){
    bool negative = exponent < 0;
    uint64_t power = negative
        ? (uint64_t)0 - (uint64_t)exponent : (uint64_t)exponent;
    exact_value result(1);
    while(power){
        if(power & 1) result = result * base;
        power >>= 1;
        if(power) base = base * base;
    }
    return negative ? exact_value(1) / result : result;
}

static bool split_small_square_factor(const exact_value &value,
                                      uint64_t &outside, uint64_t &inside){
    if(!value.is_integer() || value.is_negative()) return false;
    const precn_t &magnitude = value.integer().magnitude();
    if(magnitude.rsiz != 1) return false;
    uint64_t remaining = magnitude.a[0];
    // Trial division is excellent for the small radicands produced by normal
    // symbolic expansion, but must not turn sqrt(huge_prime) into a long job.
    if(remaining > UINT64_C(1000000000000)) return false;
    outside = 1;
    inside = 1;
    for(uint64_t prime = 2; prime <= remaining / prime;
        prime = prime == 2 ? 3 : prime + 2){
        if(remaining % prime) continue;
        unsigned count = 0;
        do{
            remaining /= prime;
            ++count;
        }while(remaining % prime == 0);
        for(unsigned i = 0; i < count / 2; ++i) outside *= prime;
        if(count & 1) inside *= prime;
    }
    if(remaining > 1) inside *= remaining;
    return true;
}

static double approximate_precision(const exact_value &a,
                                    const exact_value &b){
    double precision = std::numeric_limits<double>::infinity();
    if(a.is_approximate() && !a.number().is_exact())
        precision = std::min(precision, a.number().precision());
    if(b.is_approximate() && !b.number().is_exact())
        precision = std::min(precision, b.number().precision());
    return std::isfinite(precision) ? precision : 64.0;
}

} // namespace

const char *exact_opcode_name(exact_opcode operation){
    switch(operation){
    case exact_opcode::value: return "value";
    case exact_opcode::symbol: return "symbol";
    case exact_opcode::add: return "add";
    case exact_opcode::multiply: return "multiply";
    case exact_opcode::power: return "power";
    case exact_opcode::square_root: return "sqrt";
    case exact_opcode::exponential: return "exp";
    case exact_opcode::sine: return "sin";
    case exact_opcode::cosine: return "cos";
    case exact_opcode::tangent: return "tan";
    case exact_opcode::hyperbolic_sine: return "sinh";
    case exact_opcode::hyperbolic_cosine: return "cosh";
    case exact_opcode::hyperbolic_tangent: return "tanh";
    case exact_opcode::bounded_sum: return "sum";
    }
    return "unknown";
}

exact_value::exact_value() : value_(precz_t()){}
exact_value::exact_value(const precz_t &value) : value_(value){}
exact_value::exact_value(precz_t &&value) : value_(std::move(value)){}

exact_value::exact_value(const precq_t &value) : value_(value){
    if(value.denominator() == precn_t(1)) value_ = rational_integer(value);
}

exact_value::exact_value(precq_t &&value) : value_(std::move(value)){
    if(std::get<precq_t>(value_).denominator() == precn_t(1))
        value_ = rational_integer(std::get<precq_t>(value_));
}
exact_value::exact_value(const Number &value) : value_(value){}
exact_value::exact_value(Number &&value) : value_(std::move(value)){}

bool exact_value::is_integer() const{
    return std::holds_alternative<precz_t>(value_);
}
bool exact_value::is_rational() const{
    return std::holds_alternative<precq_t>(value_);
}
bool exact_value::is_approximate() const{
    return std::holds_alternative<Number>(value_);
}

bool exact_value::is_zero() const{
    if(is_integer()) return std::get<precz_t>(value_).is_zero();
    if(is_rational()) return std::get<precq_t>(value_).is_zero();
    return std::get<Number>(value_).is_zero();
}

bool exact_value::is_one() const{
    if(is_integer()) return std::get<precz_t>(value_) == precz_t(1);
    if(is_rational()) return std::get<precq_t>(value_) == precq_t(1);
    return std::get<Number>(value_) == Number(1);
}

bool exact_value::is_negative() const{
    if(is_integer()) return std::get<precz_t>(value_).is_negative();
    if(is_rational()) return std::get<precq_t>(value_).is_negative();
    return std::get<Number>(value_).is_negative();
}

const precz_t &exact_value::integer() const{
    if(!is_integer()) throw std::logic_error("exact value is not an integer");
    return std::get<precz_t>(value_);
}

precq_t exact_value::rational() const{
    if(is_approximate())
        throw std::logic_error("approximate value is not an exact rational");
    return is_integer() ? precq_t(std::get<precz_t>(value_))
                        : std::get<precq_t>(value_);
}

const Number &exact_value::number() const{
    if(!is_approximate()) throw std::logic_error("exact value is not approximate");
    return std::get<Number>(value_);
}

Number exact_value::to_number(double precision_bits) const{
    if(!(precision_bits > 0.0) || !std::isfinite(precision_bits))
        throw std::invalid_argument("approximate precision must be finite and positive");
    if(is_approximate()) return std::get<Number>(value_);
    if(is_integer()) return Number(std::get<precz_t>(value_));
    const precq_t &value = std::get<precq_t>(value_);
    precz_t numerator(value.numerator());
    if(value.is_negative()) numerator = -numerator;
    Number n(std::move(numerator));
    Number d(value.denominator());
    n.set_precision(precision_bits + 32.0);
    d.set_precision(precision_bits + 32.0);
    Number result = n / d;
    result.set_precision(precision_bits);
    return result;
}

std::string exact_value::to_string() const{
    if(is_integer()) return (std::string)std::get<precz_t>(value_);
    if(is_approximate()) return (std::string)std::get<Number>(value_);
    const precq_t &value = std::get<precq_t>(value_);
    std::string result;
    if(value.is_negative()) result.push_back('-');
    result += (std::string)value.numerator();
    result.push_back('/');
    result += (std::string)value.denominator();
    return result;
}

exact_value operator+(const exact_value &a, const exact_value &b){
    if(a.is_approximate() || b.is_approximate()){
        double precision = approximate_precision(a, b);
        return exact_value(a.to_number(precision + 32.0) +
                           b.to_number(precision + 32.0));
    }
    if(a.is_integer() && b.is_integer())
        return exact_value(a.integer() + b.integer());
    return normalized_rational(a.rational() + b.rational());
}

exact_value operator-(const exact_value &a, const exact_value &b){
    if(a.is_approximate() || b.is_approximate()){
        double precision = approximate_precision(a, b);
        return exact_value(a.to_number(precision + 32.0) -
                           b.to_number(precision + 32.0));
    }
    if(a.is_integer() && b.is_integer())
        return exact_value(a.integer() - b.integer());
    return normalized_rational(a.rational() - b.rational());
}

exact_value operator-(const exact_value &a){
    if(a.is_approximate()) return exact_value(-a.number());
    return a.is_integer() ? exact_value(-a.integer())
                          : normalized_rational(-a.rational());
}

exact_value operator*(const exact_value &a, const exact_value &b){
    if(a.is_approximate() || b.is_approximate()){
        double precision = approximate_precision(a, b);
        return exact_value(a.to_number(precision + 32.0) *
                           b.to_number(precision + 32.0));
    }
    if(a.is_integer() && b.is_integer())
        return exact_value(a.integer() * b.integer());
    return normalized_rational(a.rational() * b.rational());
}

exact_value operator/(const exact_value &a, const exact_value &b){
    if(b.is_zero()) std::abort();
    if(a.is_approximate() || b.is_approximate()){
        double precision = approximate_precision(a, b);
        return exact_value(a.to_number(precision + 32.0) /
                           b.to_number(precision + 32.0));
    }
    return normalized_rational(a.rational() / b.rational());
}

bool operator==(const exact_value &a, const exact_value &b){
    if(a.is_approximate() || b.is_approximate()){
        if(!a.is_approximate() || !b.is_approximate()) return false;
        const Number &av = a.number();
        const Number &bv = b.number();
        return av.radix_point() == bv.radix_point() &&
               av.precision() == bv.precision() &&
               av.significand() == bv.significand();
    }
    if(a.is_integer() && b.is_integer()) return a.integer() == b.integer();
    return a.rational() == b.rational();
}

bool operator!=(const exact_value &a, const exact_value &b){ return !(a == b); }

struct exact_node{
    uint64_t hash;
    uint32_t operand_begin;
    uint32_t payload;
    uint32_t operand_count;
    exact_opcode op;
    uint8_t flags;
};

struct exact_storage{
    std::vector<exact_node> nodes;
    std::vector<uint32_t> operands;
    std::vector<exact_value> values;
    std::vector<std::string> symbols;
    std::unordered_map<uint64_t, std::vector<uint32_t>> hash_buckets;

    uint32_t intern_value(exact_value value);
    uint32_t intern_symbol(const std::string &name);
    uint32_t intern_compound(exact_opcode op, const std::vector<uint32_t> &args);
    uint32_t make_add(std::vector<uint32_t> args,
                      exact_value constant = exact_value(0));
    uint32_t make_multiply(std::vector<uint32_t> args,
                           exact_value constant = exact_value(1));
    uint32_t make_power(uint32_t base, uint32_t exponent);
    uint32_t make_sqrt(uint32_t value);
    uint32_t make_function(exact_opcode operation, uint32_t value);
    uint32_t make_sum(uint32_t variable, uint32_t lower,
                      uint32_t upper, uint32_t body);
    uint32_t promote_approximate(uint32_t expression);
    std::string print(uint32_t id, unsigned parent_precedence = 0) const;

    const exact_node &node(uint32_t id) const{ return nodes[id]; }
    const uint32_t *children(const exact_node &node) const{
        return operands.data() + node.operand_begin;
    }

private:
    uint32_t append_node(exact_opcode op, uint32_t payload,
                         const std::vector<uint32_t> &args, uint64_t hash);
    bool compound_equal(uint32_t id, exact_opcode op,
                        const std::vector<uint32_t> &args) const;
    bool id_less(uint32_t a, uint32_t b) const;
};

uint32_t exact_storage::append_node(exact_opcode op, uint32_t payload,
                                    const std::vector<uint32_t> &args,
                                    uint64_t hash){
    if(nodes.size() >= UINT32_MAX || args.size() > UINT32_MAX ||
       operands.size() > UINT32_MAX - args.size())
        throw std::length_error("exact expression arena is full");
    uint32_t id = (uint32_t)nodes.size();
    uint32_t begin = (uint32_t)operands.size();
    operands.insert(operands.end(), args.begin(), args.end());
    nodes.push_back(exact_node{hash, begin, payload, (uint32_t)args.size(), op, 0});
    hash_buckets[hash].push_back(id);
    return id;
}

uint32_t exact_storage::intern_value(exact_value value){
    uint64_t hash = hash_mix(UINT64_C(0x76616c7565), hash_exact_value(value));
    auto found = hash_buckets.find(hash);
    if(found != hash_buckets.end()){
        for(uint32_t id : found->second){
            const exact_node &candidate = node(id);
            if(candidate.op == exact_opcode::value && values[candidate.payload] == value)
                return id;
        }
    }
    if(values.size() >= UINT32_MAX) throw std::length_error("exact value pool is full");
    uint32_t payload = (uint32_t)values.size();
    values.push_back(std::move(value));
    return append_node(exact_opcode::value, payload, std::vector<uint32_t>(), hash);
}

uint32_t exact_storage::intern_symbol(const std::string &name){
    uint64_t hash = UINT64_C(0x73796d626f6c);
    for(unsigned char c : name) hash = hash_mix(hash, c);
    auto found = hash_buckets.find(hash);
    if(found != hash_buckets.end()){
        for(uint32_t id : found->second){
            const exact_node &candidate = node(id);
            if(candidate.op == exact_opcode::symbol && symbols[candidate.payload] == name)
                return id;
        }
    }
    if(symbols.size() >= UINT32_MAX) throw std::length_error("symbol pool is full");
    uint32_t payload = (uint32_t)symbols.size();
    symbols.push_back(name);
    return append_node(exact_opcode::symbol, payload, std::vector<uint32_t>(), hash);
}

bool exact_storage::compound_equal(uint32_t id, exact_opcode op,
                                   const std::vector<uint32_t> &args) const{
    const exact_node &candidate = node(id);
    if(candidate.op != op || candidate.operand_count != args.size()) return false;
    const uint32_t *candidate_args = children(candidate);
    return std::equal(args.begin(), args.end(), candidate_args);
}

uint32_t exact_storage::intern_compound(exact_opcode op,
                                        const std::vector<uint32_t> &args){
    uint64_t hash = hash_mix(UINT64_C(0x65787072657373), (uint64_t)op);
    for(uint32_t id : args) hash = hash_mix(hash, node(id).hash);
    auto found = hash_buckets.find(hash);
    if(found != hash_buckets.end())
        for(uint32_t id : found->second)
            if(compound_equal(id, op, args)) return id;
    return append_node(op, 0, args, hash);
}

bool exact_storage::id_less(uint32_t a, uint32_t b) const{
    if(node(a).hash != node(b).hash) return node(a).hash < node(b).hash;
    return a < b;
}

uint32_t exact_storage::make_add(std::vector<uint32_t> args,
                                 exact_value constant){
    std::vector<uint32_t> terms;
    std::vector<uint32_t> pending(std::move(args));
    while(!pending.empty()){
        uint32_t id = pending.back();
        pending.pop_back();
        const exact_node &current = node(id);
        if(current.op == exact_opcode::add){
            const uint32_t *child = children(current);
            pending.insert(pending.end(), child, child + current.operand_count);
        }else if(current.op == exact_opcode::value){
            constant = constant + values[current.payload];
        }else{
            terms.push_back(id);
        }
    }

    // Split each term into a numeric coefficient and a symbolic monomial.
    // Node IDs are canonical, so equal monomials can be combined directly.
    std::unordered_map<uint32_t, exact_value> coefficients;
    for(uint32_t term : terms){
        exact_value coefficient(1);
        uint32_t monomial = term;
        exact_node term_node = node(term);
        if(term_node.op == exact_opcode::multiply){
            std::vector<uint32_t> symbolic;
            const uint32_t *factor = children(term_node);
            for(size_t i = 0; i < term_node.operand_count; ++i){
                exact_node factor_node = node(factor[i]);
                if(factor_node.op == exact_opcode::value)
                    coefficient = coefficient * values[factor_node.payload];
                else
                    symbolic.push_back(factor[i]);
            }
            if(symbolic.empty()){
                constant = constant + coefficient;
                continue;
            }
            monomial = symbolic.size() == 1
                ? symbolic[0] : intern_compound(exact_opcode::multiply, symbolic);
        }
        auto found = coefficients.find(monomial);
        if(found == coefficients.end()) coefficients.emplace(monomial, coefficient);
        else found->second = found->second + coefficient;
    }

    std::vector<uint32_t> combined;
    combined.reserve(coefficients.size() + 1);
    for(auto &entry : coefficients){
        if(entry.second.is_zero()) continue;
        if(entry.second.is_one()) combined.push_back(entry.first);
        else combined.push_back(make_multiply(
            {intern_value(std::move(entry.second)), entry.first}));
    }
    if(!constant.is_zero()) combined.push_back(intern_value(std::move(constant)));
    if(combined.empty()) return intern_value(exact_value(0));
    if(combined.size() == 1) return combined[0];
    std::sort(combined.begin(), combined.end(),
              [this](uint32_t a, uint32_t b){
                  bool av = node(a).op == exact_opcode::value;
                  bool bv = node(b).op == exact_opcode::value;
                  if(av != bv) return !av;
                  return id_less(a, b);
              });
    return intern_compound(exact_opcode::add, combined);
}

uint32_t exact_storage::make_multiply(std::vector<uint32_t> args,
                                      exact_value constant){
    std::vector<uint32_t> factors;
    std::unordered_map<uint32_t, size_t> numeric_radicals;
    std::vector<uint32_t> pending(std::move(args));
    while(!pending.empty()){
        uint32_t id = pending.back();
        pending.pop_back();
        const exact_node &current = node(id);
        if(current.op == exact_opcode::multiply){
            const uint32_t *child = children(current);
            pending.insert(pending.end(), child, child + current.operand_count);
        }else if(current.op == exact_opcode::value){
            constant = constant * values[current.payload];
            if(constant.is_zero()) return intern_value(exact_value(0));
        }else if(current.op == exact_opcode::square_root){
            uint32_t radicand = children(current)[0];
            exact_node radicand_node = node(radicand);
            if(radicand_node.op == exact_opcode::value &&
               !values[radicand_node.payload].is_approximate() &&
               !values[radicand_node.payload].is_negative()){
                ++numeric_radicals[radicand];
            }else{
                factors.push_back(id);
            }
        }else{
            factors.push_back(id);
        }
    }
    exact_value odd_radical_product(1);
    bool has_odd_radical = false;
    for(const auto &entry : numeric_radicals){
        const exact_value &radicand = values[node(entry.first).payload];
        if(entry.second / 2)
            constant = constant * exact_pow(
                radicand, (int64_t)(entry.second / 2));
        if(entry.second & 1){
            odd_radical_product = odd_radical_product * radicand;
            has_odd_radical = true;
        }
    }
    if(has_odd_radical)
    {
        uint64_t outside = 1, inside = 1;
        if(split_small_square_factor(odd_radical_product, outside, inside)){
            constant = constant * exact_value(outside);
            if(inside != 1)
                factors.push_back(intern_compound(
                    exact_opcode::square_root,
                    {intern_value(exact_value(inside))}));
        }else{
            factors.push_back(make_sqrt(
                intern_value(std::move(odd_radical_product))));
        }
    }

    // Collect exact rational powers of each base. Besides cancelling x*x^-1,
    // this reduces algebraic products such as 2^(1/3)*2^(2/3) to 2.
    std::unordered_map<uint32_t, exact_value> exponents;
    for(uint32_t factor : factors){
        uint32_t base = factor;
        exact_value exponent(1);
        exact_node factor_node = node(factor);
        if(factor_node.op == exact_opcode::power){
            const uint32_t *power_args = children(factor_node);
            exact_node exponent_node = node(power_args[1]);
            if(exponent_node.op == exact_opcode::value &&
               !values[exponent_node.payload].is_approximate()){
                base = power_args[0];
                exponent = values[exponent_node.payload];
            }
        }
        auto found = exponents.find(base);
        if(found == exponents.end()) exponents.emplace(base, exponent);
        else found->second = found->second + exponent;
    }

    std::vector<uint32_t> combined;
    combined.reserve(exponents.size() + 1);
    for(auto &entry : exponents){
        if(entry.second.is_zero()) continue;
        if(entry.second.is_one()) combined.push_back(entry.first);
        else combined.push_back(make_power(
            entry.first, intern_value(std::move(entry.second))));
    }
    if(!constant.is_one() || combined.empty())
        combined.push_back(intern_value(std::move(constant)));
    if(combined.size() == 1) return combined[0];
    std::sort(combined.begin(), combined.end(),
              [this](uint32_t a, uint32_t b){
                  bool av = node(a).op == exact_opcode::value;
                  bool bv = node(b).op == exact_opcode::value;
                  if(av != bv) return av;
                  return id_less(a, b);
              });
    return intern_compound(exact_opcode::multiply, combined);
}

uint32_t exact_storage::make_power(uint32_t base, uint32_t exponent){
    const exact_node &exponent_node = node(exponent);
    if(exponent_node.op == exact_opcode::value){
        const exact_value &value = values[exponent_node.payload];
        if(value.is_approximate() &&
           (value.number() == Number(0.5) || value.number() == Number(-0.5))){
            bool reciprocal_root = value.number().is_negative();
            const exact_node &base_node = node(base);
            uint32_t root = 0;
            if(base_node.op == exact_opcode::value){
                double precision = value.number().is_exact()
                    ? 64.0 : value.number().precision();
                Number numeric_base = values[base_node.payload].to_number(precision);
                if(numeric_base.is_exact()) numeric_base.set_precision(precision);
                root = intern_value(exact_value(::sqrt(numeric_base)));
            }else{
                root = make_sqrt(base);
            }
            if(!reciprocal_root) return root;
            return make_power(root, intern_value(exact_value(-1)));
        }
        if(!value.is_approximate()){
            precq_t rational = value.rational();
            if(rational.numerator() == precn_t(1) &&
               rational.denominator() == precn_t(2)){
                uint32_t root = make_sqrt(base);
                if(!rational.is_negative()) return root;
                return make_power(root, intern_value(exact_value(-1)));
            }
            const exact_node &numeric_base = node(base);
            if(!rational.is_negative() && rational.numerator().rsiz <= 1 &&
               rational.denominator().rsiz == 1 &&
               numeric_base.op == exact_opcode::value &&
               !values[numeric_base.payload].is_approximate() &&
               !values[numeric_base.payload].is_negative()){
                uint64_t numerator = rational.numerator().rsiz
                    ? rational.numerator().a[0] : 0;
                uint64_t denominator = rational.denominator().a[0];
                if(denominator > 1 && numerator >= denominator){
                    uint64_t whole = numerator / denominator;
                    uint64_t remainder = numerator % denominator;
                    uint32_t integral = make_power(base,
                        intern_value(exact_value(whole)));
                    if(remainder == 0) return integral;
                    uint32_t fractional = make_power(base, intern_value(
                        exact_value(precq_t(precn_t(remainder),
                                            precn_t(denominator)))));
                    return make_multiply({integral, fractional});
                }
            }
        }
    }
    int64_t integer_exponent = 0;
    bool has_integer_exponent = exponent_node.op == exact_opcode::value &&
        (integer_i64(values[exponent_node.payload], integer_exponent) ||
         approximate_integer_i64(values[exponent_node.payload], integer_exponent));
    if(has_integer_exponent){
        if(integer_exponent == 0) return intern_value(exact_value(1));
        if(integer_exponent == 1) return base;

        exact_node base_copy = node(base);
        if(base_copy.op == exact_opcode::square_root && integer_exponent > 0){
            uint32_t radicand = children(base_copy)[0];
            uint32_t half_exponent = intern_value(
                exact_value((uint64_t)integer_exponent / 2));
            uint32_t reduced = make_power(radicand, half_exponent);
            if(integer_exponent & 1) return make_multiply({reduced, base});
            return reduced;
        }
        if(base_copy.op == exact_opcode::power){
            const uint32_t *base_args = children(base_copy);
            exact_node inner_exponent_node = node(base_args[1]);
            exact_node original_base = node(base_args[0]);
            bool nonnegative_numeric_base = original_base.op == exact_opcode::value &&
                !values[original_base.payload].is_negative();
            if(inner_exponent_node.op == exact_opcode::value &&
               (!values[inner_exponent_node.payload].is_approximate() ||
                nonnegative_numeric_base)){
                exact_value combined_exponent =
                    values[inner_exponent_node.payload] *
                    values[exponent_node.payload];
                return make_power(base_args[0],
                                  intern_value(std::move(combined_exponent)));
            }
        }
    }
    const exact_node &base_node = node(base);
    if(base_node.op == exact_opcode::value){
        const exact_value &base_value = values[base_node.payload];
        if(base_value.is_one()) return base;
        if(has_integer_exponent && integer_exponent >= -4096 &&
           integer_exponent <= 4096)
            return intern_value(exact_pow(base_value, integer_exponent));
    }
    return intern_compound(exact_opcode::power, {base, exponent});
}

uint32_t exact_storage::make_sqrt(uint32_t value){
    const exact_node &source = node(value);
    if(source.op == exact_opcode::value){
        const exact_value &exact = values[source.payload];
        if(exact.is_approximate())
            return intern_value(exact_value(::sqrt(exact.number())));
        if(!exact.is_negative()){
            precq_t rational = exact.rational();
            precn_t numerator = precn_sqrt(rational.numerator());
            precn_t denominator = precn_sqrt(rational.denominator());
            if(precn_sqr(numerator) == rational.numerator() &&
               precn_sqr(denominator) == rational.denominator())
                return intern_value(exact_value(
                    precq_t(std::move(numerator), std::move(denominator))));
            uint64_t outside = 1, inside = 1;
            if(split_small_square_factor(exact, outside, inside) && outside != 1){
                if(inside == 1) return intern_value(exact_value(outside));
                uint32_t coefficient = intern_value(exact_value(outside));
                uint32_t radical = intern_compound(
                    exact_opcode::square_root,
                    {intern_value(exact_value(inside))});
                return make_multiply({coefficient, radical});
            }
        }
    }
    return intern_compound(exact_opcode::square_root, {value});
}

uint32_t exact_storage::make_function(exact_opcode operation, uint32_t value){
    if(operation != exact_opcode::exponential && operation != exact_opcode::sine &&
       operation != exact_opcode::cosine && operation != exact_opcode::tangent &&
       operation != exact_opcode::hyperbolic_sine &&
       operation != exact_opcode::hyperbolic_cosine &&
       operation != exact_opcode::hyperbolic_tangent)
        throw std::invalid_argument("invalid unary exact function");
    const exact_node &argument = node(value);
    if(argument.op == exact_opcode::value){
        const exact_value &exact = values[argument.payload];
        if(exact.is_zero()){
            if(operation == exact_opcode::cosine ||
               operation == exact_opcode::hyperbolic_cosine ||
               operation == exact_opcode::exponential)
                return intern_value(exact_value(1));
            return value;
        }
        if(exact.is_approximate()){
            Number number = exact.number();
            if(operation == exact_opcode::exponential) number = ::exp(number);
            else if(operation == exact_opcode::sine) number = ::sin(number);
            else if(operation == exact_opcode::cosine) number = ::cos(number);
            else if(operation == exact_opcode::tangent) number = ::tan(number);
            else if(operation == exact_opcode::hyperbolic_sine) number = ::sinh(number);
            else if(operation == exact_opcode::hyperbolic_cosine) number = ::cosh(number);
            else number = ::tanh(number);
            return intern_value(exact_value(std::move(number)));
        }
    }
    return intern_compound(operation, {value});
}

uint32_t exact_storage::make_sum(uint32_t variable, uint32_t lower,
                                 uint32_t upper, uint32_t body){
    const exact_node &variable_node = node(variable);
    const exact_node &lower_node = node(lower);
    const exact_node &upper_node = node(upper);
    if(variable_node.op == exact_opcode::symbol && body == variable &&
       lower_node.op == exact_opcode::value &&
       upper_node.op == exact_opcode::value){
        const exact_value &lo_value = values[lower_node.payload];
        const exact_value &hi_value = values[upper_node.payload];
        if(lo_value.is_integer() && hi_value.is_integer() &&
           hi_value.integer() >= lo_value.integer()){
            precz_t count = hi_value.integer() - lo_value.integer() + precz_t(1);
            precz_t total = (lo_value.integer() + hi_value.integer()) * count;
            total /= precz_t(2);
            return intern_value(exact_value(std::move(total)));
        }
    }
    return intern_compound(exact_opcode::bounded_sum,
                           {variable, lower, upper, body});
}

uint32_t exact_storage::promote_approximate(uint32_t expression){
    bool saw_approximate = false;
    double precision = std::numeric_limits<double>::infinity();
    std::unordered_set<uint32_t> scanned;
    auto numeric_tree = [&](auto &&self, uint32_t id) -> bool{
        if(!scanned.insert(id).second) return true;
        const exact_node &current = node(id);
        if(current.op == exact_opcode::symbol ||
           current.op == exact_opcode::bounded_sum) return false;
        if(current.op == exact_opcode::value){
            const exact_value &value = values[current.payload];
            if(value.is_approximate()){
                saw_approximate = true;
                if(!value.number().is_exact())
                    precision = std::min(precision, value.number().precision());
            }
            return true;
        }
        const uint32_t *args = children(current);
        for(size_t i = 0; i < current.operand_count; ++i)
            if(!self(self, args[i])) return false;
        return current.op == exact_opcode::add ||
               current.op == exact_opcode::multiply ||
               current.op == exact_opcode::power ||
               current.op == exact_opcode::square_root ||
               current.op == exact_opcode::exponential ||
               current.op == exact_opcode::sine ||
               current.op == exact_opcode::cosine ||
               current.op == exact_opcode::tangent ||
               current.op == exact_opcode::hyperbolic_sine ||
               current.op == exact_opcode::hyperbolic_cosine ||
               current.op == exact_opcode::hyperbolic_tangent;
    };
    if(!numeric_tree(numeric_tree, expression) || !saw_approximate)
        return expression;
    if(!std::isfinite(precision)) precision = 64.0;

    std::unordered_map<uint32_t, Number> evaluated;
    auto evaluate = [&](auto &&self, uint32_t id) -> Number{
        auto cached = evaluated.find(id);
        if(cached != evaluated.end()) return cached->second;
        const exact_node &current = node(id);
        Number result;
        if(current.op == exact_opcode::value){
            result = values[current.payload].to_number(precision);
            if(result.is_exact() || result.precision() > precision)
                result.set_precision(precision);
        }else{
            const uint32_t *args = children(current);
            if(current.op == exact_opcode::add){
                result = Number(0);
                result.set_precision(precision);
                for(size_t i = 0; i < current.operand_count; ++i)
                    result += self(self, args[i]);
            }else if(current.op == exact_opcode::multiply){
                result = Number(1);
                result.set_precision(precision);
                for(size_t i = 0; i < current.operand_count; ++i)
                    result *= self(self, args[i]);
            }else if(current.op == exact_opcode::power){
                result = ::pow(self(self, args[0]), self(self, args[1]));
            }else if(current.op == exact_opcode::square_root){
                result = ::sqrt(self(self, args[0]));
            }else if(current.op == exact_opcode::exponential){
                result = ::exp(self(self, args[0]));
            }else if(current.op == exact_opcode::sine){
                result = ::sin(self(self, args[0]));
            }else if(current.op == exact_opcode::cosine){
                result = ::cos(self(self, args[0]));
            }else if(current.op == exact_opcode::tangent){
                result = ::tan(self(self, args[0]));
            }else if(current.op == exact_opcode::hyperbolic_sine){
                result = ::sinh(self(self, args[0]));
            }else if(current.op == exact_opcode::hyperbolic_cosine){
                result = ::cosh(self(self, args[0]));
            }else{
                result = ::tanh(self(self, args[0]));
            }
        }
        if(!result.is_exact() && result.precision() > precision)
            result.set_precision(precision);
        evaluated.emplace(id, result);
        return result;
    };
    Number result = evaluate(evaluate, expression);
    result.set_precision(precision);
    return intern_value(exact_value(std::move(result)));
}

static unsigned expression_precedence(exact_opcode op){
    if(op == exact_opcode::add) return 1;
    if(op == exact_opcode::multiply) return 2;
    if(op == exact_opcode::power) return 3;
    return 4;
}

std::string exact_storage::print(uint32_t id, unsigned parent_precedence) const{
    const exact_node &current = node(id);
    unsigned precedence = expression_precedence(current.op);
    std::string result;
    if(current.op == exact_opcode::value){
        result = values[current.payload].to_string();
    }else if(current.op == exact_opcode::symbol){
        result = symbols[current.payload];
    }else if(current.op == exact_opcode::add){
        const uint32_t *args = children(current);
        std::vector<uint32_t> ordered(args, args + current.operand_count);
        std::vector<size_t> degrees(current.operand_count);
        uint32_t variable = UINT32_MAX;
        auto monomial_degree = [this](auto &&self, uint32_t id,
                                      uint32_t &symbol, size_t &degree) -> bool{
            const exact_node &term = node(id);
            if(term.op == exact_opcode::value) return true;
            if(term.op == exact_opcode::symbol){
                if(symbol != UINT32_MAX && symbol != id) return false;
                symbol = id;
                ++degree;
                return true;
            }
            if(term.op == exact_opcode::power){
                const uint32_t *power_args = children(term);
                const exact_node &base = node(power_args[0]);
                const exact_node &power = node(power_args[1]);
                int64_t exponent = 0;
                if(base.op != exact_opcode::symbol ||
                   power.op != exact_opcode::value ||
                   !integer_i64(values[power.payload], exponent) || exponent < 0 ||
                   (uint64_t)exponent > SIZE_MAX - degree) return false;
                if(symbol != UINT32_MAX && symbol != power_args[0]) return false;
                symbol = power_args[0];
                degree += (size_t)exponent;
                return true;
            }
            if(term.op != exact_opcode::multiply) return false;
            const uint32_t *factors = children(term);
            for(size_t i = 0; i < term.operand_count; ++i)
                if(!self(self, factors[i], symbol, degree)) return false;
            return true;
        };
        bool polynomial = true;
        for(size_t i = 0; i < ordered.size(); ++i)
            if(!monomial_degree(monomial_degree, ordered[i], variable, degrees[i])){
                polynomial = false;
                break;
            }
        if(polynomial && variable != UINT32_MAX){
            std::vector<std::pair<uint32_t, size_t>> terms;
            terms.reserve(ordered.size());
            for(size_t i = 0; i < ordered.size(); ++i)
                terms.emplace_back(ordered[i], degrees[i]);
            std::stable_sort(terms.begin(), terms.end(),
                [this](const auto &a, const auto &b){
                    if(a.second != b.second) return a.second > b.second;
                    return id_less(a.first, b.first);
                });
            for(size_t i = 0; i < terms.size(); ++i) ordered[i] = terms[i].first;
        }else{
            using signature = std::map<uint32_t, size_t>;
            std::vector<signature> signatures(ordered.size());
            auto monomial_signature = [this](auto &&self, uint32_t id,
                                             signature &powers) -> bool{
                const exact_node &term = node(id);
                if(term.op == exact_opcode::value) return true;
                if(term.op == exact_opcode::symbol){
                    ++powers[id];
                    return true;
                }
                if(term.op == exact_opcode::power){
                    const uint32_t *power_args = children(term);
                    const exact_node &base = node(power_args[0]);
                    const exact_node &power = node(power_args[1]);
                    int64_t exponent = 0;
                    if(base.op != exact_opcode::symbol ||
                       power.op != exact_opcode::value ||
                       !integer_i64(values[power.payload], exponent) || exponent < 0)
                        return false;
                    powers[power_args[0]] += (size_t)exponent;
                    return true;
                }
                if(term.op != exact_opcode::multiply) return false;
                const uint32_t *factors = children(term);
                for(size_t i = 0; i < term.operand_count; ++i)
                    if(!self(self, factors[i], powers)) return false;
                return true;
            };
            bool monomials = true;
            for(size_t i = 0; i < ordered.size(); ++i)
                if(!monomial_signature(monomial_signature, ordered[i],
                                       signatures[i])){
                    monomials = false;
                    break;
                }
            if(monomials){
                std::vector<uint32_t> variables;
                for(const signature &term : signatures)
                    for(const auto &entry : term) variables.push_back(entry.first);
                std::sort(variables.begin(), variables.end(),
                    [this](uint32_t a, uint32_t b){
                        return symbols[node(a).payload] < symbols[node(b).payload];
                    });
                variables.erase(std::unique(variables.begin(), variables.end()),
                                variables.end());
                std::vector<size_t> order(ordered.size());
                for(size_t i = 0; i < order.size(); ++i) order[i] = i;
                std::stable_sort(order.begin(), order.end(),
                    [&](size_t a, size_t b){
                        size_t total_a = 0, total_b = 0;
                        for(const auto &entry : signatures[a]) total_a += entry.second;
                        for(const auto &entry : signatures[b]) total_b += entry.second;
                        if(total_a != total_b) return total_a > total_b;
                        for(uint32_t symbol : variables){
                            auto ai = signatures[a].find(symbol);
                            auto bi = signatures[b].find(symbol);
                            size_t av = ai == signatures[a].end() ? 0 : ai->second;
                            size_t bv = bi == signatures[b].end() ? 0 : bi->second;
                            if(av != bv) return av > bv;
                        }
                        return id_less(ordered[a], ordered[b]);
                    });
                std::vector<uint32_t> sorted;
                sorted.reserve(ordered.size());
                for(size_t index : order) sorted.push_back(ordered[index]);
                ordered.swap(sorted);
            }
        }
        for(size_t i = 0; i < ordered.size(); ++i){
            std::string term = print(ordered[i], precedence);
            bool negative = !term.empty() && term[0] == '-';
            if(negative){
                term.erase(0, 1);
                if(term.compare(0, 2, "1*") == 0) term.erase(0, 2);
            }
            if(i) result += negative ? " - " : " + ";
            else if(negative) result.push_back('-');
            result += term;
        }
    }else if(current.op == exact_opcode::multiply){
        const uint32_t *args = children(current);
        std::vector<uint32_t> numerator;
        std::vector<std::string> denominator;
        for(size_t i = 0; i < current.operand_count; ++i){
            const exact_node &factor = node(args[i]);
            int64_t exponent = 0;
            if(factor.op == exact_opcode::power){
                const uint32_t *power_args = children(factor);
                const exact_node &power = node(power_args[1]);
                if(power.op == exact_opcode::value &&
                   integer_i64(values[power.payload], exponent) && exponent < 0){
                    std::string text = print(power_args[0], precedence);
                    exact_opcode base_operation = node(power_args[0]).op;
                    if(base_operation == exact_opcode::multiply)
                        text = "(" + text + ")";
                    uint64_t magnitude = (uint64_t)0 - (uint64_t)exponent;
                    if(magnitude != 1) text += "^" + std::to_string(magnitude);
                    denominator.push_back(std::move(text));
                    continue;
                }
            }
            numerator.push_back(args[i]);
        }
        if(denominator.empty()){
            std::stable_sort(numerator.begin(), numerator.end(),
                [this](uint32_t a, uint32_t b){
                    bool av = node(a).op == exact_opcode::value;
                    bool bv = node(b).op == exact_opcode::value;
                    if(av != bv) return av;
                    return print(a) < print(b);
                });
            for(size_t i = 0; i < numerator.size(); ++i){
                if(i) result.push_back('*');
                result += print(numerator[i], precedence);
            }
        }else{
            std::stable_sort(numerator.begin(), numerator.end(),
                [this](uint32_t a, uint32_t b){
                    bool av = node(a).op == exact_opcode::value;
                    bool bv = node(b).op == exact_opcode::value;
                    if(av != bv) return av;
                    return print(a) < print(b);
                });
            if(numerator.empty()) result = "1";
            else for(size_t i = 0; i < numerator.size(); ++i){
                if(i) result.push_back('*');
                result += print(numerator[i], precedence);
            }
            result.push_back('/');
            if(denominator.size() > 1) result.push_back('(');
            for(size_t i = 0; i < denominator.size(); ++i){
                if(i) result.push_back('*');
                result += denominator[i];
            }
            if(denominator.size() > 1) result.push_back(')');
        }
    }else if(current.op == exact_opcode::power){
        const uint32_t *args = children(current);
        const exact_node &printed_base = node(args[0]);
        const exact_node &power = node(args[1]);
        int64_t exponent = 0;
        if(printed_base.op == exact_opcode::value &&
           power.op == exact_opcode::value &&
           (values[printed_base.payload].is_approximate() ||
            values[power.payload].is_approximate())){
            const exact_value &base_value = values[printed_base.payload];
            const exact_value &power_value = values[power.payload];
            double precision = approximate_precision(base_value, power_value);
            Number numeric = ::pow(base_value.to_number(precision + 32.0),
                                   power_value.to_number(precision + 32.0));
            numeric.set_precision(precision);
            result = (std::string)numeric;
        }else if(power.op == exact_opcode::value &&
           integer_i64(values[power.payload], exponent) && exponent < 0){
            result = "1/" + print(args[0], precedence);
            if(node(args[0]).op == exact_opcode::multiply)
                result = "1/(" + print(args[0]) + ")";
            uint64_t magnitude = (uint64_t)0 - (uint64_t)exponent;
            if(magnitude != 1) result += "^" + std::to_string(magnitude);
        }else{
            result = print(args[0], precedence);
            result.push_back('^');
            std::string exponent_text = print(args[1], precedence);
            const exact_node &printed_exponent = node(args[1]);
            if(printed_exponent.op == exact_opcode::value &&
               values[printed_exponent.payload].is_rational())
                exponent_text = "(" + exponent_text + ")";
            result += exponent_text;
        }
    }else if(current.op == exact_opcode::square_root){
        result = "sqrt(" + print(children(current)[0]) + ")";
    }else if(current.op == exact_opcode::exponential ||
             current.op == exact_opcode::sine ||
             current.op == exact_opcode::cosine ||
             current.op == exact_opcode::tangent ||
             current.op == exact_opcode::hyperbolic_sine ||
             current.op == exact_opcode::hyperbolic_cosine ||
             current.op == exact_opcode::hyperbolic_tangent){
        result = std::string(exact_opcode_name(current.op)) + "(" +
                 print(children(current)[0]) + ")";
    }else{
        const uint32_t *args = children(current);
        result = "sum(" + print(args[3]) + ", " + print(args[0]) + "=" +
                 print(args[1]) + ".." + print(args[2]) + ")";
    }
    if(precedence < parent_precedence) return "(" + result + ")";
    return result;
}

exact_expr::exact_expr(std::shared_ptr<exact_storage> storage, uint32_t root)
    : storage_(std::move(storage)), root_(root){}

exact_expr::exact_expr() : storage_(), root_(0){}
bool exact_expr::valid() const{ return (bool)storage_; }
uint32_t exact_expr::id() const{
    if(!valid()) throw std::logic_error("invalid exact expression");
    return root_;
}
exact_opcode exact_expr::operation() const{
    if(!valid()) throw std::logic_error("invalid exact expression");
    return storage_->node(root_).op;
}
size_t exact_expr::operand_count() const{
    if(!valid()) throw std::logic_error("invalid exact expression");
    return storage_->node(root_).operand_count;
}
exact_expr exact_expr::operand(size_t index) const{
    if(!valid()) throw std::logic_error("invalid exact expression");
    const exact_node &current = storage_->node(root_);
    if(index >= current.operand_count)
        throw std::out_of_range("exact expression operand index is out of range");
    return exact_expr(storage_, storage_->children(current)[index]);
}
size_t exact_expr::reachable_node_count() const{
    if(!valid()) throw std::logic_error("invalid exact expression");
    std::unordered_set<uint32_t> visited;
    std::vector<uint32_t> pending(1, root_);
    while(!pending.empty()){
        uint32_t id = pending.back();
        pending.pop_back();
        if(!visited.insert(id).second) continue;
        const exact_node &current = storage_->node(id);
        const uint32_t *args = storage_->children(current);
        pending.insert(pending.end(), args, args + current.operand_count);
    }
    return visited.size();
}
size_t exact_expr::depth() const{
    if(!valid()) throw std::logic_error("invalid exact expression");
    std::unordered_map<uint32_t, size_t> memo;
    auto visit = [&](auto &&self, uint32_t id) -> size_t{
        auto cached = memo.find(id);
        if(cached != memo.end()) return cached->second;
        const exact_node &current = storage_->node(id);
        size_t result = 1;
        const uint32_t *args = storage_->children(current);
        for(size_t i = 0; i < current.operand_count; ++i)
            result = std::max(result, 1 + self(self, args[i]));
        memo.emplace(id, result);
        return result;
    };
    return visit(visit, root_);
}
std::string exact_expr::debug_tree(size_t maximum_nodes) const{
    if(!valid()) return "<invalid>\n";
    if(maximum_nodes == 0) return "... node limit reached\n";
    std::string result;
    std::unordered_set<uint32_t> visited;
    size_t emitted = 0;
    auto visit = [&](auto &&self, uint32_t id, size_t indentation) -> void{
        result.append(indentation * 2, ' ');
        result += "#" + std::to_string(id) + " ";
        const exact_node &current = storage_->node(id);
        result += exact_opcode_name(current.op);
        result += " [" + std::to_string(current.operand_count) + "]";
        if(current.op == exact_opcode::value)
            result += " = " + storage_->values[current.payload].to_string();
        else if(current.op == exact_opcode::symbol)
            result += " = " + storage_->symbols[current.payload];
        if(!visited.insert(id).second){
            result += " (shared)\n";
            return;
        }
        result.push_back('\n');
        ++emitted;
        if(emitted >= maximum_nodes){
            result.append((indentation + 1) * 2, ' ');
            result += "... node limit reached\n";
            return;
        }
        const uint32_t *args = storage_->children(current);
        for(size_t i = 0; i < current.operand_count; ++i){
            if(emitted >= maximum_nodes) break;
            self(self, args[i], indentation + 1);
        }
    };
    visit(visit, root_, 0);
    return result;
}
bool exact_expr::is_value() const{
    return valid() && storage_->node(root_).op == exact_opcode::value;
}
exact_value exact_expr::value() const{
    if(!is_value()) throw std::logic_error("exact expression is not a value");
    return storage_->values[storage_->node(root_).payload];
}
std::string exact_expr::to_string() const{
    if(!valid()) return "<invalid>";
    return storage_->print(root_);
}

exact_context::exact_context() : storage_(std::make_shared<exact_storage>()){}
exact_context::exact_context(std::shared_ptr<exact_storage> storage)
    : storage_(std::move(storage)){}
exact_expr exact_context::value(const exact_value &value){
    return exact_expr(storage_, storage_->intern_value(value));
}
exact_expr exact_context::value(exact_value &&value){
    return exact_expr(storage_, storage_->intern_value(std::move(value)));
}
exact_expr exact_context::rational(const precq_t &value){ return this->value(exact_value(value)); }
exact_expr exact_context::symbol(const std::string &name){
    if(name.empty()) throw std::invalid_argument("symbol name cannot be empty");
    return exact_expr(storage_, storage_->intern_symbol(name));
}

exact_expr exact_context::add(const std::vector<exact_expr> &terms){
    std::vector<uint32_t> ids;
    ids.reserve(terms.size());
    for(const exact_expr &term : terms){
        if(!term.valid() || term.storage_ != storage_)
            throw std::invalid_argument("exact expressions belong to different contexts");
        ids.push_back(term.root_);
    }
    uint32_t result = storage_->make_add(std::move(ids));
    return exact_expr(storage_, storage_->promote_approximate(result));
}
exact_expr exact_context::add(std::initializer_list<exact_expr> terms){
    return add(std::vector<exact_expr>(terms));
}
exact_expr exact_context::subtract(const exact_expr &a, const exact_expr &b){
    if(!a.valid() || !b.valid() || a.storage_ != storage_ || b.storage_ != storage_)
        throw std::invalid_argument("exact expressions belong to different contexts");
    uint32_t negative = storage_->intern_value(exact_value(-1));
    uint32_t negated = storage_->make_multiply({negative, b.root_});
    uint32_t result = storage_->make_add({a.root_, negated});
    return exact_expr(storage_, storage_->promote_approximate(result));
}
exact_expr exact_context::multiply(const std::vector<exact_expr> &factors){
    std::vector<uint32_t> ids;
    ids.reserve(factors.size());
    for(const exact_expr &factor : factors){
        if(!factor.valid() || factor.storage_ != storage_)
            throw std::invalid_argument("exact expressions belong to different contexts");
        ids.push_back(factor.root_);
    }
    uint32_t result = storage_->make_multiply(std::move(ids));
    return exact_expr(storage_, storage_->promote_approximate(result));
}
exact_expr exact_context::multiply(std::initializer_list<exact_expr> factors){
    return multiply(std::vector<exact_expr>(factors));
}
exact_expr exact_context::divide(const exact_expr &a, const exact_expr &b){
    if(!a.valid() || !b.valid() || a.storage_ != storage_ || b.storage_ != storage_)
        throw std::invalid_argument("exact expressions belong to different contexts");
    exact_node denominator = storage_->node(b.root_);
    if(denominator.op == exact_opcode::value &&
       storage_->values[denominator.payload].is_zero()) std::abort();

    uint32_t minus_one = storage_->intern_value(exact_value(-1));
    std::vector<uint32_t> factors;
    factors.push_back(a.root_);
    if(denominator.op == exact_opcode::multiply){
        const uint32_t *child = storage_->children(denominator);
        std::vector<uint32_t> denominator_factors(child,
                                                   child + denominator.operand_count);
        for(uint32_t factor : denominator_factors)
            factors.push_back(storage_->make_power(factor, minus_one));
    }else{
        factors.push_back(storage_->make_power(b.root_, minus_one));
    }
    uint32_t result = storage_->make_multiply(std::move(factors));
    return exact_expr(storage_, storage_->promote_approximate(result));
}
exact_expr exact_context::power(const exact_expr &base, const exact_expr &exponent){
    if(!base.valid() || !exponent.valid() || base.storage_ != storage_ ||
       exponent.storage_ != storage_)
        throw std::invalid_argument("exact expressions belong to different contexts");
    uint32_t result = storage_->make_power(base.root_, exponent.root_);
    if(storage_->node(result).op == exact_opcode::power)
        return exact_expr(storage_, result);
    return exact_expr(storage_, storage_->promote_approximate(result));
}
exact_expr exact_context::square_root(const exact_expr &value){
    if(!value.valid() || value.storage_ != storage_)
        throw std::invalid_argument("exact expressions belong to different contexts");
    uint32_t result = storage_->make_sqrt(value.root_);
    return exact_expr(storage_, storage_->promote_approximate(result));
}
exact_expr exact_context::exponential(const exact_expr &value){
    if(!value.valid() || value.storage_ != storage_)
        throw std::invalid_argument("exact expression belongs to a different context");
    return exact_expr(storage_, storage_->make_function(
        exact_opcode::exponential, value.root_));
}
exact_expr exact_context::sine(const exact_expr &value){
    if(!value.valid() || value.storage_ != storage_)
        throw std::invalid_argument("exact expression belongs to a different context");
    return exact_expr(storage_, storage_->make_function(exact_opcode::sine,
                                                         value.root_));
}
exact_expr exact_context::cosine(const exact_expr &value){
    if(!value.valid() || value.storage_ != storage_)
        throw std::invalid_argument("exact expression belongs to a different context");
    return exact_expr(storage_, storage_->make_function(exact_opcode::cosine,
                                                         value.root_));
}
exact_expr exact_context::tangent(const exact_expr &value){
    if(!value.valid() || value.storage_ != storage_)
        throw std::invalid_argument("exact expression belongs to a different context");
    return exact_expr(storage_, storage_->make_function(exact_opcode::tangent,
                                                         value.root_));
}
exact_expr exact_context::hyperbolic_sine(const exact_expr &value){
    if(!value.valid() || value.storage_ != storage_)
        throw std::invalid_argument("exact expression belongs to a different context");
    return exact_expr(storage_, storage_->make_function(
        exact_opcode::hyperbolic_sine, value.root_));
}
exact_expr exact_context::hyperbolic_cosine(const exact_expr &value){
    if(!value.valid() || value.storage_ != storage_)
        throw std::invalid_argument("exact expression belongs to a different context");
    return exact_expr(storage_, storage_->make_function(
        exact_opcode::hyperbolic_cosine, value.root_));
}
exact_expr exact_context::hyperbolic_tangent(const exact_expr &value){
    if(!value.valid() || value.storage_ != storage_)
        throw std::invalid_argument("exact expression belongs to a different context");
    return exact_expr(storage_, storage_->make_function(
        exact_opcode::hyperbolic_tangent, value.root_));
}
exact_expr exact_context::bounded_sum(const exact_expr &variable,
                                      const exact_expr &lower,
                                      const exact_expr &upper,
                                      const exact_expr &body){
    if(!variable.valid() || !lower.valid() || !upper.valid() || !body.valid() ||
       variable.storage_ != storage_ || lower.storage_ != storage_ ||
       upper.storage_ != storage_ || body.storage_ != storage_)
        throw std::invalid_argument("exact expressions belong to different contexts");
    return exact_expr(storage_, storage_->make_sum(variable.root_, lower.root_,
                                                    upper.root_, body.root_));
}

namespace{

class exact_factor_simplifier{
    exact_storage &storage_;
    std::unordered_map<uint32_t, uint32_t> memo_;

    using polynomial = std::map<size_t, exact_value>;
    using multivariate_monomial = std::map<uint32_t, size_t>;
    struct multivariate_order{
        bool operator()(const multivariate_monomial &a,
                        const multivariate_monomial &b) const{
            size_t degree_a = 0, degree_b = 0;
            for(const auto &entry : a) degree_a += entry.second;
            for(const auto &entry : b) degree_b += entry.second;
            if(degree_a != degree_b) return degree_a < degree_b;
            auto ai = a.begin(), bi = b.begin();
            while(ai != a.end() || bi != b.end()){
                uint32_t symbol = ai == a.end() ? bi->first :
                    bi == b.end() ? ai->first : std::min(ai->first, bi->first);
                size_t av = ai != a.end() && ai->first == symbol ? ai->second : 0;
                size_t bv = bi != b.end() && bi->first == symbol ? bi->second : 0;
                if(av != bv) return av < bv;
                if(ai != a.end() && ai->first == symbol) ++ai;
                if(bi != b.end() && bi->first == symbol) ++bi;
            }
            return false;
        }
    };
    using multivariate_polynomial =
        std::map<multivariate_monomial, exact_value, multivariate_order>;

    static multivariate_monomial multiply_monomials(
            multivariate_monomial a, const multivariate_monomial &b){
        for(const auto &entry : b) a[entry.first] += entry.second;
        return a;
    }

    static bool divide_monomials(const multivariate_monomial &a,
                                 const multivariate_monomial &b,
                                 multivariate_monomial &quotient){
        quotient = a;
        for(const auto &entry : b){
            auto found = quotient.find(entry.first);
            if(found == quotient.end() || found->second < entry.second) return false;
            found->second -= entry.second;
            if(found->second == 0) quotient.erase(found);
        }
        return true;
    }

    static void add_coefficient(multivariate_polynomial &value,
                                multivariate_monomial monomial,
                                const exact_value &coefficient){
        auto found = value.find(monomial);
        if(found == value.end()){
            if(!coefficient.is_zero())
                value.emplace(std::move(monomial), coefficient);
            return;
        }
        found->second = found->second + coefficient;
        if(found->second.is_zero()) value.erase(found);
    }

    bool multivariate_term(uint32_t expression, multivariate_monomial &monomial,
                           exact_value &coefficient){
        exact_node current = storage_.node(expression);
        if(current.op == exact_opcode::value){
            const exact_value &value = storage_.values[current.payload];
            if(value.is_approximate()) return false;
            coefficient = coefficient * value;
            return true;
        }
        if(current.op == exact_opcode::symbol){
            ++monomial[expression];
            return true;
        }
        if(current.op == exact_opcode::power){
            const uint32_t *args = storage_.children(current);
            exact_node base = storage_.node(args[0]);
            exact_node exponent_node = storage_.node(args[1]);
            int64_t exponent = 0;
            if(base.op != exact_opcode::symbol ||
               exponent_node.op != exact_opcode::value ||
               !integer_i64(storage_.values[exponent_node.payload], exponent) ||
               exponent < 0) return false;
            monomial[args[0]] += (size_t)exponent;
            return true;
        }
        if(current.op != exact_opcode::multiply) return false;
        const uint32_t *args = storage_.children(current);
        for(size_t i = 0; i < current.operand_count; ++i)
            if(!multivariate_term(args[i], monomial, coefficient)) return false;
        return true;
    }

    bool parse_multivariate(uint32_t expression,
                            multivariate_polynomial &result){
        exact_node current = storage_.node(expression);
        if(current.op == exact_opcode::add){
            const uint32_t *args = storage_.children(current);
            for(size_t i = 0; i < current.operand_count; ++i){
                multivariate_polynomial child;
                if(!parse_multivariate(args[i], child)) return false;
                for(const auto &entry : child)
                    add_coefficient(result, entry.first, entry.second);
            }
            return !result.empty();
        }
        if(current.op == exact_opcode::multiply){
            result.emplace(multivariate_monomial(), exact_value(1));
            const uint32_t *args = storage_.children(current);
            for(size_t i = 0; i < current.operand_count; ++i){
                multivariate_polynomial factor, product;
                if(!parse_multivariate(args[i], factor) ||
                   (factor.size() && result.size() > 100000 / factor.size()))
                    return false;
                for(const auto &a : result)
                    for(const auto &b : factor)
                        add_coefficient(product,
                            multiply_monomials(a.first, b.first),
                            a.second * b.second);
                if(product.size() > 100000) return false;
                result.swap(product);
            }
            return !result.empty();
        }
        if(current.op == exact_opcode::power){
            const uint32_t *args = storage_.children(current);
            exact_node exponent_node = storage_.node(args[1]);
            int64_t exponent = 0;
            if(exponent_node.op == exact_opcode::value &&
               integer_i64(storage_.values[exponent_node.payload], exponent) &&
               exponent >= 0 && exponent <= 4096 &&
               storage_.node(args[0]).op != exact_opcode::symbol){
                multivariate_polynomial base;
                if(!parse_multivariate(args[0], base)) return false;
                result.emplace(multivariate_monomial(), exact_value(1));
                uint64_t bits = (uint64_t)exponent;
                while(bits){
                    if(bits & 1){
                        multivariate_polynomial product;
                        if(base.size() && result.size() > 100000 / base.size())
                            return false;
                        for(const auto &a : result)
                            for(const auto &b : base)
                                add_coefficient(product,
                                    multiply_monomials(a.first, b.first),
                                    a.second * b.second);
                        result.swap(product);
                    }
                    bits >>= 1;
                    if(bits){
                        multivariate_polynomial square;
                        if(base.size() && base.size() > 100000 / base.size())
                            return false;
                        for(const auto &a : base)
                            for(const auto &b : base)
                                add_coefficient(square,
                                    multiply_monomials(a.first, b.first),
                                    a.second * b.second);
                        base.swap(square);
                    }
                }
                return !result.empty();
            }
        }
        multivariate_monomial monomial;
        exact_value coefficient(1);
        if(!multivariate_term(expression, monomial, coefficient)) return false;
        add_coefficient(result, std::move(monomial), coefficient);
        return !result.empty();
    }

    uint32_t multivariate_expression(const multivariate_polynomial &value){
        std::vector<uint32_t> terms;
        terms.reserve(value.size());
        for(const auto &entry : value){
            std::vector<uint32_t> factors;
            factors.push_back(storage_.intern_value(entry.second));
            for(const auto &power : entry.first){
                factors.push_back(power.second == 1 ? power.first :
                    storage_.make_power(power.first, storage_.intern_value(
                        exact_value((uint64_t)power.second))));
            }
            terms.push_back(storage_.make_multiply(std::move(factors)));
        }
        return storage_.make_add(std::move(terms));
    }

    bool multivariate_quotient(uint32_t numerator_id, uint32_t denominator_id,
                               uint32_t &result){
        multivariate_polynomial numerator, denominator;
        if(!parse_multivariate(numerator_id, numerator) ||
           !parse_multivariate(denominator_id, denominator)) return false;
        multivariate_polynomial remainder = numerator;
        multivariate_polynomial quotient;
        const multivariate_monomial denominator_lead = denominator.rbegin()->first;
        const exact_value denominator_coefficient = denominator.rbegin()->second;
        size_t steps = 0;
        while(!remainder.empty()){
            if(++steps > 100000) return false;
            multivariate_monomial monomial;
            if(!divide_monomials(remainder.rbegin()->first, denominator_lead,
                                 monomial)) return false;
            exact_value coefficient =
                remainder.rbegin()->second / denominator_coefficient;
            add_coefficient(quotient, monomial, coefficient);
            for(const auto &entry : denominator){
                add_coefficient(remainder,
                    multiply_monomials(monomial, entry.first),
                    -(coefficient * entry.second));
            }
        }
        if(quotient.empty()) return false;
        result = multivariate_expression(quotient);
        return true;
    }

    bool multivariate_gcd_quotients(uint32_t numerator_id,
                                    uint32_t denominator_id,
                                    uint32_t &numerator_result,
                                    uint32_t &denominator_result){
        using coefficient_polynomial =
            std::map<size_t, multivariate_polynomial>;
        multivariate_polynomial numerator, denominator;
        if(!parse_multivariate(numerator_id, numerator) ||
           !parse_multivariate(denominator_id, denominator)) return false;

        auto one = []{
            multivariate_polynomial value;
            value.emplace(multivariate_monomial(), exact_value(1));
            return value;
        };
        auto is_unit = [](const multivariate_polynomial &value){
            return value.size() == 1 && value.begin()->first.empty();
        };
        auto multiply = [&](const multivariate_polynomial &a,
                            const multivariate_polynomial &b,
                            multivariate_polynomial &result){
            result.clear();
            if(a.empty() || b.empty()) return true;
            if(a.size() > 100000 / b.size()) return false;
            for(const auto &x : a)
                for(const auto &y : b)
                    add_coefficient(result,
                        multiply_monomials(x.first, y.first),
                        x.second * y.second);
            return result.size() <= 100000;
        };
        auto exact_divide = [&](const multivariate_polynomial &a,
                                const multivariate_polynomial &b,
                                multivariate_polynomial &quotient){
            if(b.empty()) return false;
            multivariate_polynomial remainder = a;
            quotient.clear();
            const multivariate_monomial lead = b.rbegin()->first;
            const exact_value lead_coefficient = b.rbegin()->second;
            size_t steps = 0;
            while(!remainder.empty()){
                if(++steps > 100000) return false;
                multivariate_monomial monomial;
                if(!divide_monomials(remainder.rbegin()->first, lead, monomial))
                    return false;
                exact_value coefficient =
                    remainder.rbegin()->second / lead_coefficient;
                add_coefficient(quotient, monomial, coefficient);
                for(const auto &entry : b)
                    add_coefficient(remainder,
                        multiply_monomials(monomial, entry.first),
                        -(coefficient * entry.second));
                if(remainder.size() > 100000) return false;
            }
            return !quotient.empty();
        };
        auto split = [&](const multivariate_polynomial &value, uint32_t variable){
            coefficient_polynomial result;
            for(const auto &entry : value){
                multivariate_monomial monomial = entry.first;
                size_t exponent = 0;
                auto found = monomial.find(variable);
                if(found != monomial.end()){
                    exponent = found->second;
                    monomial.erase(found);
                }
                add_coefficient(result[exponent], std::move(monomial),
                                entry.second);
            }
            return result;
        };
        auto join = [&](const coefficient_polynomial &coefficients,
                        uint32_t variable){
            multivariate_polynomial result;
            for(const auto &coefficient : coefficients)
                for(const auto &entry : coefficient.second){
                    multivariate_monomial monomial = entry.first;
                    if(coefficient.first) monomial[variable] += coefficient.first;
                    add_coefficient(result, std::move(monomial), entry.second);
                }
            return result;
        };
        auto monomial_content = [](const multivariate_polynomial &value){
            multivariate_monomial content;
            if(value.empty()) return content;
            content = value.begin()->first;
            for(auto term = std::next(value.begin()); term != value.end(); ++term){
                for(auto power = content.begin(); power != content.end();){
                    auto found = term->first.find(power->first);
                    if(found == term->first.end()) power = content.erase(power);
                    else{
                        power->second = std::min(power->second, found->second);
                        ++power;
                    }
                }
                if(content.empty()) break;
            }
            return content;
        };
        auto remove_monomial = [](const multivariate_polynomial &value,
                                  const multivariate_monomial &content){
            multivariate_polynomial result;
            for(const auto &entry : value){
                multivariate_monomial reduced;
                if(!divide_monomials(entry.first, content, reduced)) std::abort();
                add_coefficient(result, std::move(reduced), entry.second);
            }
            return result;
        };
        auto make_monomial = [](const multivariate_monomial &monomial){
            multivariate_polynomial result;
            result.emplace(monomial, exact_value(1));
            return result;
        };
        auto make_monic = [](multivariate_polynomial &value){
            if(value.empty()) return;
            exact_value lead = value.rbegin()->second;
            for(auto &entry : value) entry.second = entry.second / lead;
        };
        auto univariate_remainder = [&](const multivariate_polynomial &left,
                                        const multivariate_polynomial &right,
                                        multivariate_polynomial &remainder){
            if(right.empty()) return false;
            remainder = left;
            const multivariate_monomial lead = right.rbegin()->first;
            const exact_value lead_coefficient = right.rbegin()->second;
            size_t steps = 0;
            while(!remainder.empty()){
                if(++steps > 100000) return false;
                multivariate_monomial quotient_monomial;
                if(!divide_monomials(remainder.rbegin()->first, lead,
                                     quotient_monomial)) break;
                exact_value quotient_coefficient =
                    remainder.rbegin()->second / lead_coefficient;
                for(const auto &entry : right)
                    add_coefficient(remainder,
                        multiply_monomials(quotient_monomial, entry.first),
                        -(quotient_coefficient * entry.second));
                if(remainder.size() > 100000) return false;
            }
            return true;
        };

        std::function<bool(const multivariate_polynomial &,
                           const multivariate_polynomial &,
                           multivariate_polynomial &, size_t)> gcd;
        gcd = [&](const multivariate_polynomial &left,
                  const multivariate_polynomial &right,
                  multivariate_polynomial &result, size_t depth) -> bool{
            if(depth > 32) return false;
            if(left.empty()){ result = right; return true; }
            if(right.empty()){ result = left; return true; }
            multivariate_polynomial quotient;
            if(exact_divide(left, right, quotient)){ result = right; return true; }
            if(exact_divide(right, left, quotient)){ result = left; return true; }

            // Pull out x^a*y^b-style content before any coefficient
            // arithmetic. This is common in generated expressions and costs
            // only one sparse-term scan.
            multivariate_monomial left_monomial = monomial_content(left);
            multivariate_monomial right_monomial = monomial_content(right);
            multivariate_monomial common_monomial;
            for(const auto &power : left_monomial){
                auto found = right_monomial.find(power.first);
                if(found != right_monomial.end())
                    common_monomial.emplace(power.first,
                        std::min(power.second, found->second));
            }
            if(!common_monomial.empty()){
                multivariate_polynomial reduced_gcd;
                if(!gcd(remove_monomial(left, common_monomial),
                        remove_monomial(right, common_monomial),
                        reduced_gcd, depth + 1)) return false;
                return multiply(make_monomial(common_monomial), reduced_gcd,
                                result);
            }

            std::vector<uint32_t> variables;
            for(const auto &entry : left)
                for(const auto &power : entry.first) variables.push_back(power.first);
            for(const auto &entry : right)
                for(const auto &power : entry.first) variables.push_back(power.first);
            std::sort(variables.begin(), variables.end());
            variables.erase(std::unique(variables.begin(), variables.end()),
                            variables.end());
            if(variables.empty()){
                result = one();
                return true;
            }

            // Q[x] is a field polynomial ring, so ordinary monic Euclid is
            // both simpler and much less prone to coefficient growth than the
            // multivariate pseudo-remainder path below.
            if(variables.size() == 1){
                multivariate_polynomial a = left, b = right;
                make_monic(a);
                make_monic(b);
                size_t iterations = 0;
                while(!b.empty()){
                    if(++iterations > 4096) return false;
                    multivariate_polynomial remainder;
                    if(!univariate_remainder(a, b, remainder)) return false;
                    if(!remainder.empty()) make_monic(remainder);
                    a = std::move(b);
                    b = std::move(remainder);
                }
                result = std::move(a);
                return true;
            }

            // A variable must occur in both inputs to belong to a nonconstant
            // common factor. Among those candidates, minimize the maximum
            // degree first and the number of coefficient groups second.
            uint32_t variable = UINT32_MAX;
            size_t best_degree = SIZE_MAX, best_groups = SIZE_MAX;
            for(uint32_t candidate : variables){
                bool in_left = false, in_right = false;
                size_t degree = 0;
                std::vector<size_t> exponents;
                for(const auto &entry : left){
                    auto found = entry.first.find(candidate);
                    size_t exponent = found == entry.first.end() ? 0 : found->second;
                    in_left = in_left || exponent != 0;
                    degree = std::max(degree, exponent);
                    exponents.push_back(exponent);
                }
                for(const auto &entry : right){
                    auto found = entry.first.find(candidate);
                    size_t exponent = found == entry.first.end() ? 0 : found->second;
                    in_right = in_right || exponent != 0;
                    degree = std::max(degree, exponent);
                    exponents.push_back(exponent);
                }
                if(!in_left || !in_right) continue;
                std::sort(exponents.begin(), exponents.end());
                size_t groups = (size_t)std::distance(exponents.begin(),
                    std::unique(exponents.begin(), exponents.end()));
                if(degree < best_degree ||
                   (degree == best_degree && groups < best_groups)){
                    variable = candidate;
                    best_degree = degree;
                    best_groups = groups;
                }
            }
            if(variable == UINT32_MAX){
                result = one();
                return true;
            }

            std::function<bool(const multivariate_polynomial &,
                               multivariate_polynomial &,
                               multivariate_polynomial &)> primitive;
            primitive = [&](const multivariate_polynomial &value,
                            multivariate_polynomial &content,
                            multivariate_polynomial &part) -> bool{
                coefficient_polynomial coefficients = split(value, variable);
                content.clear();
                bool first = true;
                for(const auto &entry : coefficients){
                    if(first){
                        content = entry.second;
                        first = false;
                    }else{
                        multivariate_polynomial next;
                        if(!gcd(content, entry.second, next, depth + 1)) return false;
                        content.swap(next);
                    }
                    if(is_unit(content)) break;
                }
                if(first) return false;
                if(is_unit(content)){
                    part = value;
                    return true;
                }
                coefficient_polynomial reduced;
                for(const auto &entry : coefficients){
                    multivariate_polynomial coefficient;
                    if(!exact_divide(entry.second, content, coefficient)) return false;
                    reduced.emplace(entry.first, std::move(coefficient));
                }
                part = join(reduced, variable);
                return true;
            };

            multivariate_polynomial content_left, content_right;
            multivariate_polynomial a, b;
            if(!primitive(left, content_left, a) ||
               !primitive(right, content_right, b)) return false;
            multivariate_polynomial content_gcd;
            if(!gcd(content_left, content_right, content_gcd, depth + 1))
                return false;

            size_t iterations = 0;
            while(!b.empty()){
                if(++iterations > 4096) return false;
                coefficient_polynomial ac = split(a, variable);
                coefficient_polynomial bc = split(b, variable);
                if(ac.empty() || bc.empty()) return false;
                size_t degree_b = bc.rbegin()->first;
                multivariate_polynomial remainder = a;
                while(!remainder.empty()){
                    coefficient_polynomial rc = split(remainder, variable);
                    if(rc.rbegin()->first < degree_b) break;
                    size_t shift = rc.rbegin()->first - degree_b;
                    multivariate_polynomial first_product, second_product;
                    if(!multiply(bc.rbegin()->second, remainder, first_product) ||
                       !multiply(rc.rbegin()->second, b, second_product))
                        return false;
                    multivariate_polynomial shifted;
                    for(const auto &entry : second_product){
                        multivariate_monomial monomial = entry.first;
                        monomial[variable] += shift;
                        add_coefficient(shifted, std::move(monomial), entry.second);
                    }
                    remainder = std::move(first_product);
                    for(const auto &entry : shifted)
                        add_coefficient(remainder, entry.first, -entry.second);
                    if(remainder.size() > 100000) return false;
                }
                if(remainder.empty()){
                    a = std::move(b);
                    break;
                }
                multivariate_polynomial ignored_content, primitive_remainder;
                if(!primitive(remainder, ignored_content, primitive_remainder))
                    return false;
                a = std::move(b);
                b = std::move(primitive_remainder);
            }
            multivariate_polynomial product;
            if(!multiply(content_gcd, a, product)) return false;
            result = std::move(product);
            return true;
        };

        multivariate_polynomial common;
        if(!gcd(numerator, denominator, common, 0) || is_unit(common))
            return false;
        multivariate_polynomial numerator_quotient, denominator_quotient;
        if(!exact_divide(numerator, common, numerator_quotient) ||
           !exact_divide(denominator, common, denominator_quotient))
            return false;
        if(!denominator_quotient.empty() &&
           denominator_quotient.rbegin()->second.is_negative()){
            for(auto &entry : numerator_quotient) entry.second = -entry.second;
            for(auto &entry : denominator_quotient) entry.second = -entry.second;
        }
        numerator_result = multivariate_expression(numerator_quotient);
        denominator_result = multivariate_expression(denominator_quotient);
        return true;
    }

    bool monomial(uint32_t expression, uint32_t &variable,
                  size_t &degree, exact_value &coefficient){
        exact_node current = storage_.node(expression);
        if(current.op == exact_opcode::value){
            const exact_value &value = storage_.values[current.payload];
            if(value.is_approximate()) return false;
            coefficient = coefficient * value;
            return true;
        }
        if(current.op == exact_opcode::symbol){
            if(variable != UINT32_MAX && variable != expression) return false;
            variable = expression;
            ++degree;
            return true;
        }
        if(current.op == exact_opcode::power){
            const uint32_t *args = storage_.children(current);
            exact_node base = storage_.node(args[0]);
            exact_node exponent_node = storage_.node(args[1]);
            int64_t exponent = 0;
            if(base.op != exact_opcode::symbol ||
               exponent_node.op != exact_opcode::value ||
               !integer_i64(storage_.values[exponent_node.payload], exponent) ||
               exponent < 0 || (uint64_t)exponent > SIZE_MAX - degree)
                return false;
            if(variable != UINT32_MAX && variable != args[0]) return false;
            variable = args[0];
            degree += (size_t)exponent;
            return true;
        }
        if(current.op != exact_opcode::multiply) return false;
        const uint32_t *args = storage_.children(current);
        for(size_t i = 0; i < current.operand_count; ++i)
            if(!monomial(args[i], variable, degree, coefficient)) return false;
        return true;
    }

    bool parse_polynomial(uint32_t expression, uint32_t &variable,
                          polynomial &result){
        std::vector<uint32_t> terms;
        exact_node current = storage_.node(expression);
        if(current.op == exact_opcode::add){
            const uint32_t *args = storage_.children(current);
            terms.assign(args, args + current.operand_count);
        }else{
            terms.push_back(expression);
        }
        for(uint32_t term : terms){
            size_t degree = 0;
            exact_value coefficient(1);
            if(!monomial(term, variable, degree, coefficient)) return false;
            auto found = result.find(degree);
            if(found == result.end()) result.emplace(degree, coefficient);
            else found->second = found->second + coefficient;
            if(result[degree].is_zero()) result.erase(degree);
        }
        return !result.empty();
    }

    uint32_t polynomial_expression(const polynomial &value, uint32_t variable){
        std::vector<uint32_t> terms;
        terms.reserve(value.size());
        for(const auto &entry : value){
            uint32_t term = storage_.intern_value(entry.second);
            if(entry.first){
                uint32_t power = entry.first == 1 ? variable :
                    storage_.make_power(variable, storage_.intern_value(
                        exact_value((uint64_t)entry.first)));
                term = storage_.make_multiply({term, power});
            }
            terms.push_back(term);
        }
        return storage_.make_add(std::move(terms));
    }

    bool polynomial_quotient(uint32_t numerator_id, uint32_t denominator_id,
                             uint32_t &result){
        uint32_t variable = UINT32_MAX;
        polynomial numerator, denominator;
        if(!parse_polynomial(numerator_id, variable, numerator) ||
           !parse_polynomial(denominator_id, variable, denominator) ||
           variable == UINT32_MAX || denominator.empty())
            return multivariate_quotient(numerator_id, denominator_id, result);
        polynomial remainder = numerator;
        polynomial quotient;
        size_t denominator_degree = denominator.rbegin()->first;
        exact_value denominator_lead = denominator.rbegin()->second;
        size_t steps = 0;
        while(!remainder.empty() &&
              remainder.rbegin()->first >= denominator_degree){
            if(++steps > 4096) return false;
            size_t degree = remainder.rbegin()->first - denominator_degree;
            exact_value coefficient =
                remainder.rbegin()->second / denominator_lead;
            auto q = quotient.find(degree);
            if(q == quotient.end()) quotient.emplace(degree, coefficient);
            else q->second = q->second + coefficient;
            for(const auto &entry : denominator){
                size_t target = entry.first + degree;
                exact_value subtrahend = entry.second * coefficient;
                auto r = remainder.find(target);
                if(r == remainder.end())
                    remainder.emplace(target, -subtrahend);
                else
                    r->second = r->second - subtrahend;
                auto updated = remainder.find(target);
                if(updated != remainder.end() && updated->second.is_zero())
                    remainder.erase(updated);
            }
        }
        if(!remainder.empty() || quotient.empty()) return false;
        result = polynomial_expression(quotient, variable);
        return true;
    }

    void cancel_polynomial_factors(std::vector<uint32_t> &factors){
        for(size_t inverse = 0; inverse < factors.size(); ++inverse){
            exact_node power = storage_.node(factors[inverse]);
            if(power.op != exact_opcode::power) continue;
            const uint32_t *args = storage_.children(power);
            exact_node exponent_node = storage_.node(args[1]);
            int64_t exponent = 0;
            if(exponent_node.op != exact_opcode::value ||
               !integer_i64(storage_.values[exponent_node.payload], exponent) ||
               exponent != -1) continue;
            for(size_t numerator = 0; numerator < factors.size(); ++numerator){
                if(numerator == inverse) continue;
                uint32_t quotient = 0;
                if(polynomial_quotient(factors[numerator], args[0], quotient)){
                    factors[numerator] = quotient;
                    factors.erase(factors.begin() + inverse);
                    return cancel_polynomial_factors(factors);
                }
                uint32_t reduced_numerator = 0, reduced_denominator = 0;
                if(!multivariate_gcd_quotients(factors[numerator], args[0],
                                               reduced_numerator,
                                               reduced_denominator)) continue;
                factors[numerator] = reduced_numerator;
                factors[inverse] = storage_.make_power(
                    reduced_denominator,
                    storage_.intern_value(exact_value(-1)));
                return cancel_polynomial_factors(factors);
            }
        }
    }

    std::unordered_map<uint32_t, int64_t> positive_factors(uint32_t term){
        std::unordered_map<uint32_t, int64_t> result;
        std::vector<uint32_t> factors;
        exact_node term_node = storage_.node(term);
        if(term_node.op == exact_opcode::multiply){
            const uint32_t *args = storage_.children(term_node);
            factors.assign(args, args + term_node.operand_count);
        }else{
            factors.push_back(term);
        }
        for(uint32_t factor : factors){
            exact_node current = storage_.node(factor);
            if(current.op == exact_opcode::value) continue;
            uint32_t base = factor;
            int64_t exponent = 1;
            if(current.op == exact_opcode::power){
                const uint32_t *args = storage_.children(current);
                exact_node exponent_node = storage_.node(args[1]);
                if(exponent_node.op != exact_opcode::value ||
                   !integer_i64(storage_.values[exponent_node.payload], exponent) ||
                   exponent <= 0) continue;
                base = args[0];
            }
            result[base] += exponent;
        }
        return result;
    }

    bool signed_power(uint32_t term, int &sign, uint32_t &base,
                      uint64_t &exponent){
        exact_value coefficient(1);
        std::vector<uint32_t> symbolic;
        exact_node current = storage_.node(term);
        if(current.op == exact_opcode::multiply){
            const uint32_t *args = storage_.children(current);
            for(size_t i = 0; i < current.operand_count; ++i){
                exact_node factor = storage_.node(args[i]);
                if(factor.op == exact_opcode::value)
                    coefficient = coefficient * storage_.values[factor.payload];
                else
                    symbolic.push_back(args[i]);
            }
        }else if(current.op == exact_opcode::value){
            coefficient = storage_.values[current.payload];
        }else{
            symbolic.push_back(term);
        }
        if(coefficient == exact_value(1)) sign = 1;
        else if(coefficient == exact_value(-1)) sign = -1;
        else return false;
        if(symbolic.empty()){
            base = storage_.intern_value(exact_value(1));
            exponent = 1;
            return true;
        }
        if(symbolic.size() != 1) return false;
        base = symbolic[0];
        exponent = 1;
        exact_node power = storage_.node(base);
        if(power.op == exact_opcode::power){
            const uint32_t *args = storage_.children(power);
            exact_node exponent_node = storage_.node(args[1]);
            int64_t integer_exponent = 0;
            if(exponent_node.op != exact_opcode::value ||
               !integer_i64(storage_.values[exponent_node.payload],
                            integer_exponent) || integer_exponent <= 0)
                return false;
            base = args[0];
            exponent = (uint64_t)integer_exponent;
        }
        return true;
    }

    uint32_t factor_difference_of_powers(const std::vector<uint32_t> &terms){
        if(terms.size() != 2) return UINT32_MAX;
        int sign_a = 0, sign_b = 0;
        uint32_t base_a = 0, base_b = 0;
        uint64_t exponent_a = 0, exponent_b = 0;
        if(!signed_power(terms[0], sign_a, base_a, exponent_a) ||
           !signed_power(terms[1], sign_b, base_b, exponent_b) ||
           sign_a == sign_b || exponent_a != exponent_b ||
           exponent_a < 2 || exponent_a > 4096) return UINT32_MAX;
        if(sign_a < 0){
            std::swap(sign_a, sign_b);
            std::swap(base_a, base_b);
        }
        uint32_t minus_one = storage_.intern_value(exact_value(-1));
        uint32_t difference = storage_.make_add({
            base_a, storage_.make_multiply({minus_one, base_b})});
        std::vector<uint32_t> quotient_terms;
        quotient_terms.reserve((size_t)exponent_a);
        for(uint64_t i = 0; i < exponent_a; ++i){
            std::vector<uint32_t> factors;
            uint64_t power_a = exponent_a - 1 - i;
            if(power_a) factors.push_back(power_a == 1 ? base_a :
                storage_.make_power(base_a, storage_.intern_value(
                    exact_value(power_a))));
            if(i) factors.push_back(i == 1 ? base_b :
                storage_.make_power(base_b, storage_.intern_value(
                    exact_value(i))));
            quotient_terms.push_back(storage_.make_multiply(std::move(factors)));
        }
        uint32_t quotient = storage_.make_add(std::move(quotient_terms));
        return storage_.make_multiply({difference, quotient});
    }

    uint32_t factor_add(std::vector<uint32_t> terms){
        if(terms.size() < 2) return storage_.make_add(std::move(terms));
        std::unordered_map<uint32_t, int64_t> common = positive_factors(terms[0]);
        for(size_t i = 1; i < terms.size() && !common.empty(); ++i){
            std::unordered_map<uint32_t, int64_t> factors =
                positive_factors(terms[i]);
            for(auto entry = common.begin(); entry != common.end();){
                auto found = factors.find(entry->first);
                if(found == factors.end()) entry = common.erase(entry);
                else{
                    entry->second = std::min(entry->second, found->second);
                    ++entry;
                }
            }
        }
        if(common.empty()){
            uint32_t difference = factor_difference_of_powers(terms);
            if(difference != UINT32_MAX) return difference;
            return storage_.make_add(std::move(terms));
        }

        std::vector<uint32_t> common_factors;
        std::vector<uint32_t> inverse_factors;
        uint32_t minus_one = storage_.intern_value(exact_value(-1));
        for(const auto &entry : common){
            uint32_t factor = entry.second == 1 ? entry.first :
                storage_.make_power(entry.first,
                    storage_.intern_value(exact_value(entry.second)));
            common_factors.push_back(factor);
            inverse_factors.push_back(storage_.make_power(factor, minus_one));
        }
        std::vector<uint32_t> reduced;
        reduced.reserve(terms.size());
        for(uint32_t term : terms){
            std::vector<uint32_t> quotient(1, term);
            quotient.insert(quotient.end(), inverse_factors.begin(),
                            inverse_factors.end());
            reduced.push_back(storage_.make_multiply(std::move(quotient)));
        }
        common_factors.push_back(storage_.make_add(std::move(reduced)));
        return storage_.make_multiply(std::move(common_factors));
    }

    bool contains_square_root(uint32_t expression){
        exact_node current = storage_.node(expression);
        if(current.op == exact_opcode::square_root) return true;
        const uint32_t *args = storage_.children(current);
        for(size_t i = 0; i < current.operand_count; ++i)
            if(contains_square_root(args[i])) return true;
        return false;
    }

    bool contains_approximate(uint32_t expression){
        exact_node current = storage_.node(expression);
        if(current.op == exact_opcode::value)
            return storage_.values[current.payload].is_approximate();
        const uint32_t *args = storage_.children(current);
        for(size_t i = 0; i < current.operand_count; ++i)
            if(contains_approximate(args[i])) return true;
        return false;
    }

    bool expanded_product(uint32_t left, uint32_t right, uint32_t &result,
                          size_t &products){
        std::vector<uint32_t> left_terms, right_terms;
        exact_node left_node = storage_.node(left);
        exact_node right_node = storage_.node(right);
        if(left_node.op == exact_opcode::add){
            const uint32_t *args = storage_.children(left_node);
            left_terms.assign(args, args + left_node.operand_count);
        }else left_terms.push_back(left);
        if(right_node.op == exact_opcode::add){
            const uint32_t *args = storage_.children(right_node);
            right_terms.assign(args, args + right_node.operand_count);
        }else right_terms.push_back(right);
        if(right_terms.size() &&
           left_terms.size() > (1000000 - products) / right_terms.size())
            return false;
        products += left_terms.size() * right_terms.size();
        std::vector<uint32_t> terms;
        terms.reserve(left_terms.size() * right_terms.size());
        for(uint32_t a : left_terms)
            for(uint32_t b : right_terms)
                terms.push_back(storage_.make_multiply({a, b}));
        result = storage_.make_add(std::move(terms));
        exact_node combined = storage_.node(result);
        return combined.op != exact_opcode::add || combined.operand_count <= 100000;
    }

    bool expanded_power(uint32_t base, uint64_t exponent, uint32_t &result,
                        size_t &products){
        result = storage_.intern_value(exact_value(1));
        uint32_t factor = base;
        while(exponent){
            if(exponent & 1)
                if(!expanded_product(result, factor, result, products)) return false;
            exponent >>= 1;
            if(exponent)
                if(!expanded_product(factor, factor, factor, products)) return false;
        }
        return true;
    }

    bool numeric_radicand(uint32_t expression, uint64_t &radicand){
        exact_node current = storage_.node(expression);
        if(current.op == exact_opcode::square_root){
            exact_node value_node = storage_.node(storage_.children(current)[0]);
            if(value_node.op != exact_opcode::value) return false;
            const exact_value &value = storage_.values[value_node.payload];
            if(!value.is_integer() || value.is_negative() ||
               value.integer().magnitude().rsiz > 1) return false;
            const precn_t &magnitude = value.integer().magnitude();
            radicand = magnitude.rsiz ? magnitude.a[0] : 0;
            return radicand > 1;
        }
        if(current.op != exact_opcode::multiply) return false;
        const uint32_t *args = storage_.children(current);
        bool found = false;
        for(size_t i = 0; i < current.operand_count; ++i){
            exact_node factor = storage_.node(args[i]);
            if(factor.op == exact_opcode::value) continue;
            uint64_t candidate = 0;
            if(found || !numeric_radicand(args[i], candidate)) return false;
            radicand = candidate;
            found = true;
        }
        return found;
    }

    static uint64_t smallest_prime_factor(uint64_t value){
        if(value > UINT64_C(1000000000000)) return 0;
        if((value & 1) == 0) return 2;
        for(uint64_t divisor = 3; divisor <= value / divisor; divisor += 2)
            if(value % divisor == 0) return divisor;
        return value;
    }

    bool root_degree(uint32_t expression, uint64_t &degree){
        exact_node current = storage_.node(expression);
        if(current.op == exact_opcode::square_root){
            degree = 2;
            return true;
        }
        if(current.op != exact_opcode::power) return false;
        const uint32_t *args = storage_.children(current);
        exact_node exponent_node = storage_.node(args[1]);
        if(exponent_node.op != exact_opcode::value) return false;
        const exact_value &exponent = storage_.values[exponent_node.payload];
        if(exponent.is_approximate()) return false;
        precq_t rational = exponent.rational();
        if(rational.is_negative() || rational.numerator() != precn_t(1) ||
           rational.denominator().rsiz != 1) return false;
        degree = rational.denominator().a[0];
        return degree >= 2 && degree <= 16;
    }

    bool rationalize_binomial_root(uint32_t base, uint32_t inverse_exponent,
                                   uint32_t &result){
        exact_node sum = storage_.node(base);
        if(sum.op != exact_opcode::add || sum.operand_count != 2) return false;
        const uint32_t *sum_args = storage_.children(sum);
        std::vector<uint32_t> terms(sum_args, sum_args + 2);
        uint64_t degree = 0;
        size_t root_index = root_degree(terms[0], degree) ? 0 : 1;
        if(root_index == 1 && !root_degree(terms[1], degree)) return false;
        uint32_t root = terms[root_index];
        uint32_t other = terms[1 - root_index];
        uint32_t minus_one = storage_.intern_value(exact_value(-1));
        std::vector<uint32_t> quotient_terms;
        quotient_terms.reserve((size_t)degree);
        for(uint64_t k = 0; k < degree; ++k){
            std::vector<uint32_t> factors;
            uint64_t other_power = degree - 1 - k;
            if(other_power) factors.push_back(other_power == 1 ? other :
                storage_.make_power(other, storage_.intern_value(
                    exact_value(other_power))));
            if(k) factors.push_back(k == 1 ? root : storage_.make_power(
                root, storage_.intern_value(exact_value(k))));
            if(k & 1) factors.push_back(minus_one);
            quotient_terms.push_back(storage_.make_multiply(std::move(factors)));
        }
        uint32_t quotient = storage_.make_add(std::move(quotient_terms));
        uint32_t other_power = storage_.make_power(other,
            storage_.intern_value(exact_value(degree)));
        uint32_t root_power = storage_.make_power(root,
            storage_.intern_value(exact_value(degree)));
        uint32_t denominator = degree & 1
            ? storage_.make_add({other_power, root_power})
            : storage_.make_add({other_power,
                                 storage_.make_multiply({minus_one, root_power})});
        if(contains_square_root(denominator)) return false;
        result = storage_.make_multiply({
            quotient, storage_.make_power(denominator, inverse_exponent)});
        return true;
    }

    bool rationalize_two_cube_roots(uint32_t base, uint32_t inverse_exponent,
                                    uint32_t &result){
        exact_node sum = storage_.node(base);
        if(sum.op != exact_opcode::add || sum.operand_count != 3) return false;
        const uint32_t *args = storage_.children(sum);
        std::vector<uint32_t> roots;
        uint32_t other = UINT32_MAX;
        for(size_t i = 0; i < 3; ++i){
            uint64_t degree = 0;
            if(root_degree(args[i], degree) && degree == 3)
                roots.push_back(args[i]);
            else if(other == UINT32_MAX)
                other = args[i];
            else
                return false;
        }
        if(roots.size() != 2 || other == UINT32_MAX ||
           contains_square_root(other)) return false;

        uint32_t r = roots[0], s = roots[1];
        uint32_t minus_one = storage_.intern_value(exact_value(-1));
        uint32_t three = storage_.intern_value(exact_value(3));
        size_t products = 0;

        // First eliminate s from other + r + s.
        uint32_t a_sum = storage_.make_add({other, r});
        uint32_t a_square = 0, a_times_s = 0;
        if(!expanded_power(a_sum, 2, a_square, products) ||
           !expanded_product(a_sum, s, a_times_s, products)) return false;
        uint32_t s_square = storage_.make_power(
            s, storage_.intern_value(exact_value(2)));
        uint32_t first_numerator = storage_.make_add({
            a_square, storage_.make_multiply({minus_one, a_times_s}), s_square});

        uint32_t r_cube = storage_.make_power(
            r, storage_.intern_value(exact_value(3)));
        uint32_t s_cube = storage_.make_power(
            s, storage_.intern_value(exact_value(3)));
        uint32_t other_square = storage_.make_multiply({other, other});
        uint32_t other_cube = storage_.make_multiply({other_square, other});
        uint32_t c0 = storage_.make_add({other_cube, r_cube, s_cube});
        uint32_t c1 = storage_.make_multiply({three, other_square});
        uint32_t c2 = storage_.make_multiply({three, other});

        auto product = [&](uint32_t x, uint32_t y){
            return storage_.make_multiply({x, y});
        };
        auto square = [&](uint32_t x){ return product(x, x); };
        auto subtract = [&](uint32_t x, uint32_t y){
            return storage_.make_add({x, product(minus_one, y)});
        };

        // Inverse of c0+c1*r+c2*r^2 modulo r^3-r_cube.
        uint32_t q0 = subtract(square(c0), product(r_cube, product(c1, c2)));
        uint32_t q1 = subtract(product(r_cube, square(c2)), product(c0, c1));
        uint32_t q2 = subtract(square(c1), product(c0, c2));
        uint32_t r_square = storage_.make_power(
            r, storage_.intern_value(exact_value(2)));
        uint32_t second_numerator = storage_.make_add({
            q0, product(q1, r), product(q2, r_square)});

        uint32_t norm = storage_.make_add({
            product(square(c0), c0),
            product(r_cube, product(square(c1), c1)),
            product(square(r_cube), product(square(c2), c2)),
            product(storage_.intern_value(exact_value(-3)),
                    product(r_cube, product(c0, product(c1, c2))))});
        if(contains_square_root(norm)) return false;
        uint32_t numerator = 0;
        if(!expanded_product(first_numerator, second_numerator,
                             numerator, products)) return false;
        uint32_t inverse_norm = storage_.make_power(norm, inverse_exponent);
        return expanded_product(numerator, inverse_norm, result, products);
    }

    bool rationalize_square_and_cube_root(uint32_t base,
                                          uint32_t inverse_exponent,
                                          uint32_t &result){
        exact_node sum = storage_.node(base);
        if(sum.op != exact_opcode::add || sum.operand_count != 3) return false;
        const uint32_t *args = storage_.children(sum);
        uint32_t square_root = UINT32_MAX, cube_root = UINT32_MAX;
        uint32_t other = UINT32_MAX;
        for(size_t i = 0; i < 3; ++i){
            uint64_t degree = 0;
            if(root_degree(args[i], degree) && degree == 2 &&
               square_root == UINT32_MAX)
                square_root = args[i];
            else if(root_degree(args[i], degree) && degree == 3 &&
                    cube_root == UINT32_MAX)
                cube_root = args[i];
            else if(other == UINT32_MAX)
                other = args[i];
            else
                return false;
        }
        if(square_root == UINT32_MAX || cube_root == UINT32_MAX ||
           other == UINT32_MAX || contains_square_root(other)) return false;

        uint32_t minus_one = storage_.intern_value(exact_value(-1));
        uint32_t two = storage_.intern_value(exact_value(2));
        size_t products = 0;

        // First multiply by other + cube_root - square_root.
        uint32_t a = storage_.make_add({other, cube_root});
        uint32_t first_numerator = storage_.make_add({
            a, storage_.make_multiply({minus_one, square_root})});
        uint32_t square_value = storage_.make_multiply({square_root, square_root});
        uint32_t c0 = storage_.make_add({
            storage_.make_multiply({other, other}),
            storage_.make_multiply({minus_one, square_value})});
        uint32_t c1 = storage_.make_multiply({two, other});
        uint32_t c2 = storage_.intern_value(exact_value(1));
        uint32_t cube_value = storage_.make_power(
            cube_root, storage_.intern_value(exact_value(3)));

        auto product = [&](uint32_t x, uint32_t y){
            return storage_.make_multiply({x, y});
        };
        auto square = [&](uint32_t x){ return product(x, x); };
        auto subtract = [&](uint32_t x, uint32_t y){
            return storage_.make_add({x, product(minus_one, y)});
        };
        uint32_t q0 = subtract(square(c0),
                               product(cube_value, product(c1, c2)));
        uint32_t q1 = subtract(product(cube_value, square(c2)),
                               product(c0, c1));
        uint32_t q2 = subtract(square(c1), product(c0, c2));
        uint32_t cube_square = storage_.make_power(
            cube_root, storage_.intern_value(exact_value(2)));
        uint32_t second_numerator = storage_.make_add({
            q0, product(q1, cube_root), product(q2, cube_square)});
        uint32_t norm = storage_.make_add({
            product(square(c0), c0),
            product(cube_value, product(square(c1), c1)),
            product(square(cube_value), product(square(c2), c2)),
            product(storage_.intern_value(exact_value(-3)),
                    product(cube_value, product(c0, product(c1, c2))))});
        uint32_t numerator = 0;
        if(!expanded_product(first_numerator, second_numerator,
                             numerator, products)) return false;
        uint32_t inverse_norm = storage_.make_power(norm, inverse_exponent);
        return expanded_product(numerator, inverse_norm, result, products);
    }

    bool rationalize_inverse(uint32_t base, uint32_t exponent,
                             uint32_t &result){
        exact_node exponent_node = storage_.node(exponent);
        int64_t integer_exponent = 0;
        if(exponent_node.op != exact_opcode::value ||
           !integer_i64(storage_.values[exponent_node.payload],
                        integer_exponent) || integer_exponent != -1)
            return false;
        if(rationalize_binomial_root(base, exponent, result)) return true;
        if(rationalize_two_cube_roots(base, exponent, result)) return true;
        if(rationalize_square_and_cube_root(base, exponent, result)) return true;
        exact_node initial = storage_.node(base);
        if(initial.op != exact_opcode::add || initial.operand_count < 2 ||
           initial.operand_count >= 16 || !contains_square_root(base) ||
           contains_approximate(base)) return false;

        uint32_t numerator = storage_.intern_value(exact_value(1));
        uint32_t denominator = base;
        uint32_t minus_one = storage_.intern_value(exact_value(-1));
        size_t products = 0;
        std::unordered_set<uint32_t> seen;
        for(size_t round = 0; round < 15 && contains_square_root(denominator);
            ++round){
            if(!seen.insert(denominator).second) return false;
            exact_node sum = storage_.node(denominator);
            if(sum.op != exact_opcode::add) return false;
            const uint32_t *sum_args = storage_.children(sum);
            std::vector<uint32_t> terms(sum_args, sum_args + sum.operand_count);
            uint64_t generator = 0;
            for(uint32_t term : terms){
                uint64_t radicand = 0;
                if(numeric_radicand(term, radicand)){
                    generator = smallest_prime_factor(radicand);
                    break;
                }
            }
            if(generator == 0) return false;
            std::vector<uint32_t> conjugate_terms;
            conjugate_terms.reserve(terms.size());
            for(uint32_t term : terms){
                uint64_t radicand = 0;
                if(numeric_radicand(term, radicand) &&
                   radicand % generator == 0)
                    conjugate_terms.push_back(
                        storage_.make_multiply({minus_one, term}));
                else
                    conjugate_terms.push_back(term);
            }
            uint32_t conjugate = storage_.make_add(std::move(conjugate_terms));
            uint32_t next_numerator = 0, next_denominator = 0;
            if(!expanded_product(numerator, conjugate, next_numerator, products) ||
               !expanded_product(denominator, conjugate,
                                 next_denominator, products))
                return false;
            numerator = next_numerator;
            denominator = next_denominator;
        }
        if(contains_square_root(denominator)) return false;
        uint32_t inverse = storage_.make_power(denominator, exponent);
        return expanded_product(numerator, inverse, result, products);
    }

public:
    explicit exact_factor_simplifier(exact_storage &storage) : storage_(storage){}

    uint32_t simplify(uint32_t expression){
        auto cached = memo_.find(expression);
        if(cached != memo_.end()) return cached->second;
        exact_node source = storage_.node(expression);
        std::vector<uint32_t> children;
        if(source.operand_count){
            const uint32_t *args = storage_.children(source);
            children.assign(args, args + source.operand_count);
            for(uint32_t &child : children) child = simplify(child);
        }
        uint32_t result = expression;
        if(source.op == exact_opcode::add)
            result = factor_add(std::move(children));
        else if(source.op == exact_opcode::multiply){
            cancel_polynomial_factors(children);
            result = storage_.make_multiply(std::move(children));
        }
        else if(source.op == exact_opcode::power){
            if(!rationalize_inverse(children[0], children[1], result))
                result = storage_.make_power(children[0], children[1]);
        }
        else if(source.op == exact_opcode::square_root)
            result = storage_.make_sqrt(children[0]);
        else if(source.op == exact_opcode::exponential ||
                source.op == exact_opcode::sine ||
                source.op == exact_opcode::cosine ||
                source.op == exact_opcode::tangent ||
                source.op == exact_opcode::hyperbolic_sine ||
                source.op == exact_opcode::hyperbolic_cosine ||
                source.op == exact_opcode::hyperbolic_tangent)
            result = storage_.make_function(source.op, children[0]);
        else if(source.op == exact_opcode::bounded_sum)
            result = storage_.make_sum(children[0], children[1],
                                       children[2], children[3]);
        memo_.emplace(expression, result);
        return result;
    }
};

class exact_expander{
    exact_storage &storage_;
    size_t maximum_terms_;
    size_t maximum_products_;
    size_t products_;
    std::unordered_map<uint32_t, uint32_t> memo_;

    std::vector<uint32_t> terms(uint32_t expression){
        exact_node node = storage_.node(expression);
        if(node.op != exact_opcode::add) return {expression};
        const uint32_t *children = storage_.children(node);
        return std::vector<uint32_t>(children, children + node.operand_count);
    }

    uint32_t multiply(uint32_t a, uint32_t b){
        std::vector<uint32_t> left = terms(a);
        std::vector<uint32_t> right = terms(b);
        uint32_t accumulated = storage_.intern_value(exact_value(0));
        // Canonicalize each row before proceeding. A field-like product may
        // have thousands of raw pairs but only a few dozen combined radicals.
        for(uint32_t x : left){
            if(right.size() > maximum_products_ - products_)
                throw std::length_error("expansion exceeds the work limit");
            products_ += right.size();
            std::vector<uint32_t> row;
            row.reserve(right.size());
            for(uint32_t y : right)
                row.push_back(storage_.make_multiply({x, y}));
            uint32_t row_sum = storage_.make_add(std::move(row));
            accumulated = storage_.make_add({accumulated, row_sum});
            exact_node combined = storage_.node(accumulated);
            size_t count = combined.op == exact_opcode::add
                ? combined.operand_count : 1;
            if(count > maximum_terms_)
                throw std::length_error("expansion exceeds the term limit");
        }
        return accumulated;
    }

public:
    exact_expander(exact_storage &storage, size_t maximum_terms)
        : storage_(storage), maximum_terms_(maximum_terms),
          maximum_products_(0), products_(0), memo_(){
        if(maximum_terms_ == 0)
            throw std::invalid_argument("expansion term limit must be positive");
        if(maximum_terms_ > 10000000 / maximum_terms_)
            maximum_products_ = 10000000;
        else
            maximum_products_ = std::max<size_t>(4096,
                                                  maximum_terms_ * maximum_terms_);
    }

    uint32_t expand(uint32_t expression){
        auto cached = memo_.find(expression);
        if(cached != memo_.end()) return cached->second;

        exact_node source = storage_.node(expression);
        std::vector<uint32_t> children;
        if(source.operand_count){
            const uint32_t *source_children = storage_.children(source);
            children.assign(source_children,
                            source_children + source.operand_count);
        }
        uint32_t result = expression;
        if(source.op == exact_opcode::add){
            for(uint32_t &child : children) child = expand(child);
            result = storage_.make_add(std::move(children));
        }else if(source.op == exact_opcode::multiply){
            uint32_t product = storage_.intern_value(exact_value(1));
            for(uint32_t child : children) product = multiply(product, expand(child));
            result = product;
        }else if(source.op == exact_opcode::power){
            uint32_t base = expand(children[0]);
            uint32_t exponent = expand(children[1]);
            exact_node exponent_node = storage_.node(exponent);
            int64_t power = 0;
            bool integral = exponent_node.op == exact_opcode::value &&
                integer_i64(storage_.values[exponent_node.payload], power);
            if(integral && power >= 0 &&
               storage_.node(base).op == exact_opcode::add){
                uint32_t accumulated = storage_.intern_value(exact_value(1));
                uint32_t factor = base;
                uint64_t bits = (uint64_t)power;
                while(bits){
                    if(bits & 1) accumulated = multiply(accumulated, factor);
                    bits >>= 1;
                    if(bits) factor = multiply(factor, factor);
                }
                result = accumulated;
            }else{
                result = storage_.make_power(base, exponent);
            }
        }else if(source.op == exact_opcode::square_root){
            result = storage_.make_sqrt(expand(children[0]));
        }else if(source.op == exact_opcode::exponential ||
                 source.op == exact_opcode::sine ||
                 source.op == exact_opcode::cosine ||
                 source.op == exact_opcode::tangent ||
                 source.op == exact_opcode::hyperbolic_sine ||
                 source.op == exact_opcode::hyperbolic_cosine ||
                 source.op == exact_opcode::hyperbolic_tangent){
            result = storage_.make_function(source.op, expand(children[0]));
        }else if(source.op == exact_opcode::bounded_sum){
            for(uint32_t &child : children) child = expand(child);
            result = storage_.make_sum(children[0], children[1],
                                       children[2], children[3]);
        }
        memo_.emplace(expression, result);
        return result;
    }
};

} // namespace

exact_expr exact_context::expand(const exact_expr &expression,
                                 size_t maximum_terms){
    if(!expression.valid() || expression.storage_ != storage_)
        throw std::invalid_argument("exact expressions belong to different contexts");
    exact_expander expander(*storage_, maximum_terms);
    return exact_expr(storage_, expander.expand(expression.root_));
}
exact_expr exact_context::simplify(const exact_expr &expression,
                                   size_t automatic_expansion_terms){
    if(!expression.valid() || expression.storage_ != storage_)
        throw std::invalid_argument("exact expressions belong to different contexts");
    uint32_t promoted = storage_->promote_approximate(expression.root_);
    if(promoted != expression.root_) return exact_expr(storage_, promoted);
    exact_factor_simplifier factorer(*storage_);
    exact_expr factored(storage_, factorer.simplify(expression.root_));
    std::unordered_set<uint32_t> visited;
    auto has_denominator = [&](auto &&self, uint32_t id) -> bool{
        if(!visited.insert(id).second) return false;
        const exact_node &current = storage_->node(id);
        if(current.op == exact_opcode::power){
            const uint32_t *args = storage_->children(current);
            const exact_node &power = storage_->node(args[1]);
            int64_t exponent = 0;
            if(power.op == exact_opcode::value &&
               integer_i64(storage_->values[power.payload], exponent) &&
               exponent < 0) return true;
        }
        const uint32_t *args = storage_->children(current);
        for(size_t i = 0; i < current.operand_count; ++i)
            if(self(self, args[i])) return true;
        return false;
    };
    // Keep an uncancelled rational expression compact. Explicit expand() is
    // still available when distributing a denominator is actually desired.
    if(has_denominator(has_denominator, factored.root_)) return factored;
    try{
        return expand(factored, automatic_expansion_terms);
    }catch(const std::length_error &){
        // Expansion is optional during simplify. Preserve a compact expression
        // whenever the estimated intermediate form crosses the small budget.
        return factored;
    }
}

std::vector<exact_expr> exact_context::compact(
        const std::vector<exact_expr> &roots){
    for(const exact_expr &root : roots)
        if(!root.valid() || root.storage_ != storage_)
            throw std::invalid_argument("compact roots must belong to this context");

    std::shared_ptr<exact_storage> old_storage = storage_;
    std::shared_ptr<exact_storage> new_storage = std::make_shared<exact_storage>();
    std::vector<uint32_t> remap(old_storage->nodes.size(), UINT32_MAX);

    // Iterative postorder avoids consuming the C++ call stack for a deep DAG.
    std::vector<std::pair<uint32_t, bool>> pending;
    for(const exact_expr &root : roots) pending.emplace_back(root.root_, false);
    while(!pending.empty()){
        uint32_t id = pending.back().first;
        bool expanded = pending.back().second;
        pending.pop_back();
        if(remap[id] != UINT32_MAX) continue;

        const exact_node &source = old_storage->node(id);
        if(!expanded && source.operand_count){
            pending.emplace_back(id, true);
            const uint32_t *children = old_storage->children(source);
            for(size_t i = source.operand_count; i > 0; --i)
                if(remap[children[i - 1]] == UINT32_MAX)
                    pending.emplace_back(children[i - 1], false);
            continue;
        }

        if(source.op == exact_opcode::value){
            remap[id] = new_storage->intern_value(
                old_storage->values[source.payload]);
        }else if(source.op == exact_opcode::symbol){
            remap[id] = new_storage->intern_symbol(
                old_storage->symbols[source.payload]);
        }else{
            std::vector<uint32_t> children;
            children.reserve(source.operand_count);
            const uint32_t *source_children = old_storage->children(source);
            for(size_t i = 0; i < source.operand_count; ++i){
                if(remap[source_children[i]] == UINT32_MAX)
                    throw std::logic_error("invalid expression DAG order");
                children.push_back(remap[source_children[i]]);
            }
            remap[id] = new_storage->intern_compound(source.op, children);
        }
    }

    storage_ = std::move(new_storage);
    std::vector<exact_expr> result;
    result.reserve(roots.size());
    for(const exact_expr &root : roots)
        result.push_back(exact_expr(storage_, remap[root.root_]));
    return result;
}

exact_expr exact_context::compact(const exact_expr &root){
    std::vector<exact_expr> compacted = compact(std::vector<exact_expr>{root});
    return std::move(compacted[0]);
}

exact_add_builder exact_context::make_add_builder(){
    return exact_add_builder(storage_);
}
size_t exact_context::node_count() const{ return storage_->nodes.size(); }
size_t exact_context::operand_id_count() const{ return storage_->operands.size(); }
std::string exact_context::debug_dump(size_t maximum_nodes) const{
    size_t count = storage_->nodes.size();
    if(maximum_nodes && count > maximum_nodes) count = maximum_nodes;
    std::string result = "arena: " + std::to_string(storage_->nodes.size()) +
        " nodes, " + std::to_string(storage_->operands.size()) +
        " operand ids, " + std::to_string(storage_->values.size()) +
        " values, " + std::to_string(storage_->symbols.size()) + " symbols\n";
    char hash_text[32];
    for(size_t id = 0; id < count; ++id){
        const exact_node &current = storage_->node((uint32_t)id);
        std::snprintf(hash_text, sizeof(hash_text), "%016llx",
                      (unsigned long long)current.hash);
        result += "#" + std::to_string(id) + " " +
            exact_opcode_name(current.op) + " hash=0x" + hash_text +
            " operands=" + std::to_string(current.operand_begin) + ".." +
            std::to_string((size_t)current.operand_begin + current.operand_count);
        if(current.op == exact_opcode::value)
            result += " value[" + std::to_string(current.payload) + "]=" +
                storage_->values[current.payload].to_string();
        else if(current.op == exact_opcode::symbol)
            result += " symbol[" + std::to_string(current.payload) + "]=" +
                storage_->symbols[current.payload];
        if(current.operand_count){
            result += " children={";
            const uint32_t *args = storage_->children(current);
            for(size_t i = 0; i < current.operand_count; ++i){
                if(i) result.push_back(',');
                result += "#" + std::to_string(args[i]);
            }
            result.push_back('}');
        }
        result.push_back('\n');
    }
    if(count != storage_->nodes.size())
        result += "... " + std::to_string(storage_->nodes.size() - count) +
            " nodes omitted\n";
    return result;
}

exact_add_builder::exact_add_builder(std::shared_ptr<exact_storage> storage)
    : storage_(std::move(storage)), constant_(0), positive_small_(0),
      negative_small_(0), terms_(){}
void exact_add_builder::add_positive(uint64_t value){
    if(UINT64_MAX - positive_small_ < value){
        constant_ = constant_ + exact_value(positive_small_);
        positive_small_ = 0;
    }
    positive_small_ += value;
}
void exact_add_builder::add_negative(uint64_t magnitude){
    if(UINT64_MAX - negative_small_ < magnitude){
        constant_ = constant_ - exact_value(negative_small_);
        negative_small_ = 0;
    }
    negative_small_ += magnitude;
}
void exact_add_builder::flush_small(){
    if(positive_small_ >= negative_small_){
        constant_ = constant_ + exact_value(positive_small_ - negative_small_);
    }else{
        constant_ = constant_ - exact_value(negative_small_ - positive_small_);
    }
    positive_small_ = 0;
    negative_small_ = 0;
}
void exact_add_builder::add(const exact_value &value){ constant_ = constant_ + value; }
void exact_add_builder::add(exact_value &&value){ constant_ = constant_ + value; }
void exact_add_builder::add(const exact_expr &term){
    if(!term.valid() || term.storage_ != storage_)
        throw std::invalid_argument("exact expressions belong to different contexts");
    const exact_node &node = storage_->node(term.root_);
    if(node.op == exact_opcode::value) constant_ = constant_ + storage_->values[node.payload];
    else terms_.push_back(term.root_);
}
exact_expr exact_add_builder::finish(){
    flush_small();
    uint32_t result = storage_->make_add(std::move(terms_), std::move(constant_));
    terms_.clear();
    constant_ = exact_value(0);
    return exact_expr(storage_, result);
}

exact_expr operator+(const exact_expr &a, const exact_expr &b){
    if(!a.valid() || !b.valid() || a.storage_ != b.storage_)
        throw std::invalid_argument("exact expressions belong to different contexts");
    exact_context context(a.storage_);
    return context.add({a, b});
}
exact_expr operator-(const exact_expr &a){
    if(!a.valid()) throw std::logic_error("invalid exact expression");
    exact_context context(a.storage_);
    return context.multiply({context.integer(-1), a});
}
exact_expr operator-(const exact_expr &a, const exact_expr &b){ return a + (-b); }
exact_expr operator*(const exact_expr &a, const exact_expr &b){
    if(!a.valid() || !b.valid() || a.storage_ != b.storage_)
        throw std::invalid_argument("exact expressions belong to different contexts");
    exact_context context(a.storage_);
    return context.multiply({a, b});
}
exact_expr operator/(const exact_expr &a, const exact_expr &b){
    if(!a.valid() || !b.valid() || a.storage_ != b.storage_)
        throw std::invalid_argument("exact expressions belong to different contexts");
    exact_context context(a.storage_);
    return context.divide(a, b);
}
exact_expr pow(const exact_expr &base, const exact_expr &exponent){
    if(!base.valid() || !exponent.valid() || base.storage_ != exponent.storage_)
        throw std::invalid_argument("exact expressions belong to different contexts");
    exact_context context(base.storage_);
    return context.power(base, exponent);
}
exact_expr sqrt(const exact_expr &value){
    if(!value.valid()) throw std::logic_error("invalid exact expression");
    exact_context context(value.storage_);
    return context.square_root(value);
}
exact_expr exp(const exact_expr &value){
    if(!value.valid()) throw std::logic_error("invalid exact expression");
    exact_context context(value.storage_);
    return context.exponential(value);
}
exact_expr sin(const exact_expr &value){
    if(!value.valid()) throw std::logic_error("invalid exact expression");
    exact_context context(value.storage_);
    return context.sine(value);
}
exact_expr cos(const exact_expr &value){
    if(!value.valid()) throw std::logic_error("invalid exact expression");
    exact_context context(value.storage_);
    return context.cosine(value);
}
exact_expr tan(const exact_expr &value){
    if(!value.valid()) throw std::logic_error("invalid exact expression");
    exact_context context(value.storage_);
    return context.tangent(value);
}
exact_expr sinh(const exact_expr &value){
    if(!value.valid()) throw std::logic_error("invalid exact expression");
    exact_context context(value.storage_);
    return context.hyperbolic_sine(value);
}
exact_expr cosh(const exact_expr &value){
    if(!value.valid()) throw std::logic_error("invalid exact expression");
    exact_context context(value.storage_);
    return context.hyperbolic_cosine(value);
}
exact_expr tanh(const exact_expr &value){
    if(!value.valid()) throw std::logic_error("invalid exact expression");
    exact_context context(value.storage_);
    return context.hyperbolic_tangent(value);
}
bool operator==(const exact_expr &a, const exact_expr &b){
    if(!a.valid() || !b.valid()) return !a.valid() && !b.valid();
    return a.storage_ == b.storage_ && a.root_ == b.root_;
}
bool operator!=(const exact_expr &a, const exact_expr &b){ return !(a == b); }
