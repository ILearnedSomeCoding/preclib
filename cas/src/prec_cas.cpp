#include"../prec_cas.hpp"
#include"factor_integer.hpp"

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
#include<tuple>
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

static bool split_small_square_factor_u64(uint64_t remaining,
                                          uint64_t &outside,
                                          uint64_t &inside){
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

static bool split_small_square_factor(const exact_value &value,
                                      uint64_t &outside, uint64_t &inside){
    if(!value.is_integer() || value.is_negative()) return false;
    const precn_t &magnitude = value.integer().magnitude();
    if(magnitude.rsiz != 1) return false;
    return split_small_square_factor_u64(magnitude.a[0], outside, inside);
}

static size_t natural_bit_length(const precn_t &value){
    if(value.rsiz == 0) return 0;
    uint64_t top = value.a[value.rsiz - 1];
    size_t bits = (value.rsiz - 1) * 64;
    while(top){ ++bits; top >>= 1; }
    return bits;
}

static bool perfect_cube_root(const precn_t &value, precn_t &root){
    if(value.rsiz == 0){ root = precn_t(); return true; }
    size_t bits = natural_bit_length(value);
    precn_t x = precn_t(1) << ((bits + 2) / 3);
    for(;;){
        precn_t square = x * x;
        precn_t y = div_u64(mul_u64(x, 2) + value / square, 3);
        if(y >= x) break;
        x = std::move(y);
    }
    if(x * x * x != value) return false;
    root = std::move(x);
    return true;
}

static bool exact_cube_root(const exact_value &value, exact_value &root){
    if(value.is_approximate()) return false;
    precq_t rational = value.rational();
    precn_t numerator, denominator;
    if(!perfect_cube_root(rational.numerator(), numerator) ||
       !perfect_cube_root(rational.denominator(), denominator)) return false;
    precq_t result(std::move(numerator), std::move(denominator));
    if(rational.is_negative()) result = -result;
    root = normalized_rational(std::move(result));
    return true;
}

static int compare_power(const precn_t &base, uint64_t exponent,
                         const precn_t &limit){
    precn_t result(1), factor(base);
    while(exponent){
        if(exponent & 1){
            result = result * factor;
            if(result > limit) return 1;
        }
        exponent >>= 1;
        if(exponent){
            factor = factor * factor;
            if(factor > limit) factor = limit + precn_t(1);
        }
    }
    if(result < limit) return -1;
    return result == limit ? 0 : 1;
}

static bool perfect_nth_root(const precn_t &value, uint64_t degree,
                             precn_t &root){
    if(degree < 2) return false;
    if(value.rsiz == 0){ root = precn_t(); return true; }
    size_t bits = natural_bit_length(value);
    if(degree >= bits){
        if(value == precn_t(1)){ root = precn_t(1); return true; }
        return false;
    }
    size_t root_bits = (bits + (size_t)degree - 1) / (size_t)degree;
    precn_t low(1), high = precn_t(1) << root_bits;
    while(low <= high){
        precn_t middle = (low + high) >> 1;
        int comparison = compare_power(middle, degree, value);
        if(comparison == 0){ root = std::move(middle); return true; }
        if(comparison < 0) low = middle + precn_t(1);
        else{
            if(middle.rsiz == 0) break;
            high = middle - precn_t(1);
        }
    }
    return false;
}

static bool exact_nth_root(const exact_value &value, uint64_t degree,
                           exact_value &root){
    if(value.is_approximate() || value.is_negative()) return false;
    precq_t rational = value.rational();
    precn_t numerator, denominator;
    if(!perfect_nth_root(rational.numerator(), degree, numerator) ||
       !perfect_nth_root(rational.denominator(), degree, denominator))
        return false;
    root = normalized_rational(precq_t(std::move(numerator),
                                      std::move(denominator)));
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
    case exact_opcode::constant_pi: return "pi";
    case exact_opcode::constant_e: return "e";
    case exact_opcode::constant_i: return "i";
    case exact_opcode::add: return "add";
    case exact_opcode::multiply: return "multiply";
    case exact_opcode::power: return "power";
    case exact_opcode::square_root: return "sqrt";
    case exact_opcode::exponential: return "exp";
    case exact_opcode::sine: return "sin";
    case exact_opcode::cosine: return "cos";
    case exact_opcode::tangent: return "tan";
    case exact_opcode::arc_sine: return "asin";
    case exact_opcode::arc_cosine: return "acos";
    case exact_opcode::arc_tangent: return "atan";
    case exact_opcode::hyperbolic_sine: return "sinh";
    case exact_opcode::hyperbolic_cosine: return "cosh";
    case exact_opcode::hyperbolic_tangent: return "tanh";
    case exact_opcode::inverse_hyperbolic_sine: return "asinh";
    case exact_opcode::inverse_hyperbolic_cosine: return "acosh";
    case exact_opcode::inverse_hyperbolic_tangent: return "atanh";
    case exact_opcode::natural_logarithm: return "ln";
    case exact_opcode::logarithm_base_2: return "log2";
    case exact_opcode::logarithm_base_10: return "log10";
    case exact_opcode::bounded_sum: return "sum";
    case exact_opcode::expression_list: return "list";
    case exact_opcode::absolute_value: return "abs";
    case exact_opcode::sine_integral: return "Si";
    case exact_opcode::cosine_integral: return "Ci";
    case exact_opcode::exponential_integral: return "Ei";
    case exact_opcode::error_function: return "erf";
    case exact_opcode::imaginary_error_function: return "erfi";
    case exact_opcode::partial_gamma: return "partial_gamma";
    case exact_opcode::derivative: return "derivative";
    case exact_opcode::integral: return "integrate";
    case exact_opcode::rule: return "rule";
    }
    return "unknown";
}

static bool exact_unary_function(exact_opcode operation){
    switch(operation){
    case exact_opcode::exponential:
    case exact_opcode::sine:
    case exact_opcode::cosine:
    case exact_opcode::tangent:
    case exact_opcode::hyperbolic_sine:
    case exact_opcode::hyperbolic_cosine:
    case exact_opcode::hyperbolic_tangent:
    case exact_opcode::arc_sine:
    case exact_opcode::arc_cosine:
    case exact_opcode::arc_tangent:
    case exact_opcode::inverse_hyperbolic_sine:
    case exact_opcode::inverse_hyperbolic_cosine:
    case exact_opcode::inverse_hyperbolic_tangent:
    case exact_opcode::natural_logarithm:
    case exact_opcode::logarithm_base_2:
    case exact_opcode::logarithm_base_10:
    case exact_opcode::absolute_value:
    case exact_opcode::sine_integral:
    case exact_opcode::cosine_integral:
    case exact_opcode::exponential_integral:
    case exact_opcode::error_function:
    case exact_opcode::imaginary_error_function:
        return true;
    default:
        return false;
    }
}

static int constant_decimal_digits(double binary_precision){
    long double digits = std::ceil((long double)binary_precision *
                                   0.30102999566398119521L) + 10.0L;
    if(digits > (long double)std::numeric_limits<int>::max())
        throw std::length_error("constant precision is too large");
    return (int)digits;
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

bool exact_value::is_minus_one() const{
    if(is_integer()) return std::get<precz_t>(value_) == precz_t(-1);
    if(is_rational()) return std::get<precq_t>(value_) == precq_t(-1);
    return std::get<Number>(value_) == Number(-1);
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
    if(b.is_zero()) throw std::domain_error("division by zero");
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
    std::unordered_map<uint32_t, uint8_t> assumptions;

    enum : uint8_t{
        assumed_real = 1,
        assumed_nonnegative = 2,
        assumed_positive = 4
    };

    bool has_assumption(uint32_t id, uint8_t property) const{
        auto found = assumptions.find(id);
        return found != assumptions.end() && (found->second & property) != 0;
    }

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
        if(!entry.second.is_approximate() && entry.second.is_zero()) continue;
        if(!entry.second.is_approximate() && entry.second.is_one())
            combined.push_back(entry.first);
        else combined.push_back(make_multiply(
            {intern_value(std::move(entry.second)), entry.first}));
    }
    if(constant.is_approximate() || !constant.is_zero())
        combined.push_back(intern_value(std::move(constant)));
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
            if(!constant.is_approximate() && constant.is_zero())
                return intern_value(exact_value(0));
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
    if(constant.is_approximate() || !constant.is_one() || combined.empty())
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

        exact_node imaginary_base = node(base);
        if(imaginary_base.op == exact_opcode::constant_i){
            int cycle = (int)(integer_exponent % 4);
            if(cycle < 0) cycle += 4;
            if(cycle == 0) return intern_value(exact_value(1));
            if(cycle == 1) return base;
            if(cycle == 2) return intern_value(exact_value(-1));
            return make_multiply({intern_value(exact_value(-1)), base});
        }

        exact_node base_copy = node(base);
        if(base_copy.op == exact_opcode::square_root && integer_exponent > 0){
            uint32_t radicand = children(base_copy)[0];
            uint32_t half_exponent = intern_value(
                exact_value((uint64_t)integer_exponent / 2));
            uint32_t reduced = make_power(radicand, half_exponent);
            if(integer_exponent & 1) return make_multiply({reduced, base});
            return reduced;
        }
        if(base_copy.op == exact_opcode::multiply){
            const uint32_t *base_factors = children(base_copy);
            bool monomial = true;
            for(size_t i = 0; i < base_copy.operand_count; ++i){
                exact_opcode operation = node(base_factors[i]).op;
                if(operation != exact_opcode::value &&
                   operation != exact_opcode::symbol &&
                   operation != exact_opcode::power &&
                   operation != exact_opcode::constant_i){
                    monomial = false;
                    break;
                }
            }
            if(monomial){
                std::vector<uint32_t> powered;
                powered.reserve(base_copy.operand_count);
                for(size_t i = 0; i < base_copy.operand_count; ++i)
                    powered.push_back(make_power(base_factors[i], exponent));
                return make_multiply(std::move(powered));
            }
        }
        if(base_copy.op == exact_opcode::power){
            const uint32_t *base_args = children(base_copy);
            exact_node inner_exponent_node = node(base_args[1]);
            exact_node original_base = node(base_args[0]);
            bool nonnegative_numeric_base = original_base.op == exact_opcode::value &&
                !values[original_base.payload].is_negative();
            if(inner_exponent_node.op == exact_opcode::value &&
               (has_integer_exponent || nonnegative_numeric_base)){
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
        if(has_integer_exponent && base_value.is_approximate() &&
           integer_exponent >= -4096 && integer_exponent <= 4096)
            return intern_value(exact_pow(base_value, integer_exponent));
        if(has_integer_exponent && !base_value.is_approximate()){
            precq_t rational = base_value.rational();
            size_t base_bits = natural_bit_length(rational.numerator()) +
                               natural_bit_length(rational.denominator());
            uint64_t magnitude = integer_exponent < 0
                ? (uint64_t)0 - (uint64_t)integer_exponent
                : (uint64_t)integer_exponent;
            // Materialize useful exact powers while keeping hostile inputs
            // from allocating an unexpectedly enormous integer.
            const uint64_t maximum_result_bits = UINT64_C(1) << 20;
            if(base_bits == 0 || magnitude <= maximum_result_bits / base_bits)
                return intern_value(exact_pow(base_value, integer_exponent));
        }
    }
    return intern_compound(exact_opcode::power, {base, exponent});
}

uint32_t exact_storage::make_sqrt(uint32_t value){
    const exact_node &source = node(value);
    if(source.op == exact_opcode::value){
        const exact_value &exact = values[source.payload];
        if(exact.is_approximate())
            return intern_value(exact_value(::sqrt(exact.number())));
        if(exact.is_negative()){
            uint32_t positive = intern_value(-exact);
            uint32_t root = make_sqrt(positive);
            uint32_t imaginary = intern_compound(exact_opcode::constant_i, {});
            return make_multiply({root, imaginary});
        }else{
            precq_t rational = exact.rational();
            precn_t numerator = precn_sqrt(rational.numerator());
            precn_t denominator = precn_sqrt(rational.denominator());
            if(precn_sqr(numerator) == rational.numerator() &&
               precn_sqr(denominator) == rational.denominator())
                return intern_value(exact_value(
                    precq_t(std::move(numerator), std::move(denominator))));
            // Normalize sqrt(n/d) by removing square factors from both sides
            // and rationalizing the remaining square-free denominator:
            // sqrt(n_o^2*n_i / (d_o^2*d_i)) =
            // n_o*sqrt(n_i*d_i)/(d_o*d_i).
            if(rational.denominator().rsiz == 1 &&
               rational.denominator().a[0] > 1){
                uint64_t denominator_outside = 1;
                uint64_t denominator_inside = 1;
                if(split_small_square_factor_u64(
                       rational.denominator().a[0], denominator_outside,
                       denominator_inside) &&
                   denominator_outside <= UINT64_MAX / denominator_inside){
                    uint64_t numerator_outside = 1;
                    uint64_t numerator_inside = 0;
                    precn_t radicand(rational.numerator());
                    if(rational.numerator().rsiz == 1 &&
                       split_small_square_factor_u64(
                           rational.numerator().a[0], numerator_outside,
                           numerator_inside))
                        radicand = precn_t(numerator_inside);
                    radicand = mul_u64(radicand, denominator_inside);
                    uint64_t coefficient_denominator =
                        denominator_outside * denominator_inside;
                    uint32_t coefficient = intern_value(exact_value(precq_t(
                        precn_t(numerator_outside),
                        precn_t(coefficient_denominator))));
                    uint32_t radical = make_sqrt(intern_value(exact_value(
                        precz_t(std::move(radicand)))));
                    return make_multiply({coefficient, radical});
                }
            }
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
    if(source.op == exact_opcode::add && source.operand_count > 1){
        const uint32_t *term_data = children(source);
        std::vector<uint32_t> terms(
            term_data, term_data + source.operand_count);
        const size_t term_count = terms.size();
        uint64_t common = 0;
        for(size_t i = 0; i < term_count; ++i){
            uint32_t term = terms[i];
            const exact_node &term_node = node(term);
            int64_t coefficient = 1;
            bool found_coefficient = false;
            if(term_node.op == exact_opcode::value){
                found_coefficient = integer_i64(
                    values[term_node.payload], coefficient);
            }else if(term_node.op == exact_opcode::multiply){
                const uint32_t *factors = children(term_node);
                for(size_t j = 0; j < term_node.operand_count; ++j){
                    const exact_node &factor = node(factors[j]);
                    if(factor.op == exact_opcode::value && integer_i64(
                           values[factor.payload], coefficient)){
                        found_coefficient = true;
                        break;
                    }
                }
            }
            if(!found_coefficient) coefficient = 1;
            uint64_t magnitude = coefficient < 0
                ? (uint64_t)0 - (uint64_t)coefficient
                : (uint64_t)coefficient;
            if(magnitude == 0) continue;
            if(common == 0) common = magnitude;
            else{
                uint64_t a = common, b = magnitude;
                while(b){ uint64_t next = a % b; a = b; b = next; }
                common = a;
            }
            if(common == 1) break;
        }
        if(common > 1){
            uint64_t outside = (uint64_t)std::sqrt((long double)common);
            while(outside && outside > common / outside) --outside;
            while(outside + 1 <= common / (outside + 1)) ++outside;
            if(outside > 1 && outside * outside == common){
                uint32_t inverse = intern_value(exact_value(precq_t(
                    precn_t(1), precn_t(common))));
                std::vector<uint32_t> reduced;
                reduced.reserve(term_count);
                for(size_t i = 0; i < term_count; ++i)
                    reduced.push_back(make_multiply({terms[i], inverse}));
                uint32_t inner = make_add(std::move(reduced));
                return make_multiply({intern_value(exact_value(outside)),
                                      make_sqrt(inner)});
            }
        }
    }
    if(source.op == exact_opcode::power){
        const uint32_t *power_data = children(source);
        uint32_t base = power_data[0];
        uint32_t exponent = power_data[1];
        int64_t integer_exponent = 0;
        const exact_node &exponent_node = node(exponent);
        if(exponent_node.op == exact_opcode::value &&
           integer_i64(values[exponent_node.payload], integer_exponent) &&
           integer_exponent == 2 &&
           has_assumption(base, assumed_real)){
            if(has_assumption(base, assumed_nonnegative)) return base;
            return make_function(exact_opcode::absolute_value, base);
        }
    }
    return intern_compound(exact_opcode::square_root, {value});
}

uint32_t exact_storage::make_function(exact_opcode operation, uint32_t value){
    if(!exact_unary_function(operation))
        throw std::invalid_argument("invalid unary exact function");
    exact_node argument = node(value);

    if(operation == exact_opcode::absolute_value){
        if(argument.op == exact_opcode::absolute_value) return value;
        if(argument.op == exact_opcode::constant_i)
            return intern_value(exact_value(1));
        if(argument.op == exact_opcode::symbol &&
           has_assumption(value, assumed_nonnegative)) return value;
        if(argument.op == exact_opcode::multiply){
            const uint32_t *factor_data = children(argument);
            std::vector<uint32_t> factors(factor_data,
                factor_data + argument.operand_count);
            if(factors.size() > 1 && node(factors[0]).op == exact_opcode::value &&
               values[node(factors[0]).payload].is_minus_one()){
                factors.erase(factors.begin());
                return make_function(operation, make_multiply(std::move(factors)));
            }
        }
        auto rectangular_term = [&](uint32_t id, exact_value &real,
                                    exact_value &imaginary) -> bool{
            const exact_node &term = node(id);
            if(term.op == exact_opcode::value &&
               !values[term.payload].is_approximate()){
                real = real + values[term.payload];
                return true;
            }
            if(term.op == exact_opcode::constant_i){
                imaginary = imaginary + exact_value(1);
                return true;
            }
            if(term.op != exact_opcode::multiply) return false;
            exact_value coefficient(1);
            bool found_i = false;
            const uint32_t *parts = children(term);
            for(size_t i = 0; i < term.operand_count; ++i){
                const exact_node &part = node(parts[i]);
                if(part.op == exact_opcode::constant_i && !found_i){
                    found_i = true;
                }else if(part.op == exact_opcode::value &&
                         !values[part.payload].is_approximate()){
                    coefficient = coefficient * values[part.payload];
                }else return false;
            }
            if(!found_i) return false;
            imaginary = imaginary + coefficient;
            return true;
        };
        exact_value real(0), imaginary(0);
        bool rectangular = true;
        if(argument.op == exact_opcode::add){
            const uint32_t *terms = children(argument);
            for(size_t i = 0; i < argument.operand_count && rectangular; ++i)
                rectangular = rectangular_term(terms[i], real, imaginary);
        }else{
            rectangular = rectangular_term(value, real, imaginary);
        }
        if(rectangular && !imaginary.is_zero()){
            exact_value squared_norm = real * real + imaginary * imaginary;
            return make_sqrt(intern_value(std::move(squared_norm)));
        }
    }

    auto inverse_composition = [&](exact_opcode inverse, uint32_t &source){
        if(argument.op != inverse) return false;
        source = children(argument)[0];
        return true;
    };
    auto square = [&](uint32_t source){
        return make_power(source, intern_value(exact_value(2)));
    };
    auto one_plus_square = [&](uint32_t source, int sign){
        uint32_t squared = square(source);
        if(sign < 0)
            squared = make_multiply({intern_value(exact_value(-1)), squared});
        return make_add({intern_value(exact_value(1)), squared});
    };
    auto quotient = [&](uint32_t numerator, uint32_t denominator){
        return make_multiply({numerator, make_power(
            denominator, intern_value(exact_value(-1)))});
    };

    auto imaginary_pi_coefficient = [&](precq_t &coefficient) -> bool{
        coefficient = precq_t(1);
        bool found_i = false, found_pi = false;
        auto accept = [&](uint32_t factor){
            const exact_node &current = node(factor);
            if(current.op == exact_opcode::constant_i){
                if(found_i) return false;
                found_i = true;
                return true;
            }
            if(current.op == exact_opcode::constant_pi){
                if(found_pi) return false;
                found_pi = true;
                return true;
            }
            if(current.op != exact_opcode::value) return false;
            const exact_value &exact = values[current.payload];
            if(exact.is_approximate()) return false;
            coefficient = coefficient * exact.rational();
            return true;
        };
        if(argument.op == exact_opcode::multiply){
            const uint32_t *factors = children(argument);
            for(size_t i = 0; i < argument.operand_count; ++i)
                if(!accept(factors[i])) return false;
        }else if(!accept(value)){
            return false;
        }
        return found_i && found_pi;
    };

    uint32_t inverse_source = 0;
    if(operation == exact_opcode::sine){
        if(inverse_composition(exact_opcode::arc_sine, inverse_source))
            return inverse_source;
        if(inverse_composition(exact_opcode::arc_cosine, inverse_source))
            return make_sqrt(one_plus_square(inverse_source, -1));
        if(inverse_composition(exact_opcode::arc_tangent, inverse_source))
            return quotient(inverse_source,
                make_sqrt(one_plus_square(inverse_source, 1)));
    }else if(operation == exact_opcode::cosine){
        if(inverse_composition(exact_opcode::arc_cosine, inverse_source))
            return inverse_source;
        if(inverse_composition(exact_opcode::arc_sine, inverse_source))
            return make_sqrt(one_plus_square(inverse_source, -1));
        if(inverse_composition(exact_opcode::arc_tangent, inverse_source))
            return quotient(intern_value(exact_value(1)),
                make_sqrt(one_plus_square(inverse_source, 1)));
    }else if(operation == exact_opcode::tangent){
        if(inverse_composition(exact_opcode::arc_tangent, inverse_source))
            return inverse_source;
        if(inverse_composition(exact_opcode::arc_sine, inverse_source))
            return quotient(inverse_source,
                make_sqrt(one_plus_square(inverse_source, -1)));
        if(inverse_composition(exact_opcode::arc_cosine, inverse_source))
            return quotient(make_sqrt(one_plus_square(inverse_source, -1)),
                            inverse_source);
    }else if(operation == exact_opcode::hyperbolic_sine){
        if(inverse_composition(exact_opcode::inverse_hyperbolic_sine,
                               inverse_source)) return inverse_source;
        if(inverse_composition(exact_opcode::inverse_hyperbolic_cosine,
                               inverse_source))
            return make_sqrt(make_add({square(inverse_source),
                intern_value(exact_value(-1))}));
        if(inverse_composition(exact_opcode::inverse_hyperbolic_tangent,
                               inverse_source))
            return quotient(inverse_source,
                make_sqrt(one_plus_square(inverse_source, -1)));
    }else if(operation == exact_opcode::hyperbolic_cosine){
        if(inverse_composition(exact_opcode::inverse_hyperbolic_cosine,
                               inverse_source)) return inverse_source;
        if(inverse_composition(exact_opcode::inverse_hyperbolic_sine,
                               inverse_source))
            return make_sqrt(one_plus_square(inverse_source, 1));
        if(inverse_composition(exact_opcode::inverse_hyperbolic_tangent,
                               inverse_source))
            return quotient(intern_value(exact_value(1)),
                make_sqrt(one_plus_square(inverse_source, -1)));
    }else if(operation == exact_opcode::hyperbolic_tangent){
        if(inverse_composition(exact_opcode::inverse_hyperbolic_tangent,
                               inverse_source)) return inverse_source;
        if(inverse_composition(exact_opcode::inverse_hyperbolic_sine,
                               inverse_source))
            return quotient(inverse_source,
                make_sqrt(one_plus_square(inverse_source, 1)));
        if(inverse_composition(exact_opcode::inverse_hyperbolic_cosine,
                               inverse_source))
            return quotient(make_sqrt(make_add({square(inverse_source),
                    intern_value(exact_value(-1))})), inverse_source);
    }

    if(operation == exact_opcode::exponential){
        precq_t coefficient;
        if(imaginary_pi_coefficient(coefficient)){
            uint32_t coefficient_node = intern_value(exact_value(coefficient));
            uint32_t pi = intern_compound(exact_opcode::constant_pi, {});
            uint32_t angle = make_multiply({coefficient_node, pi});
            uint32_t real = make_function(exact_opcode::cosine, angle);
            uint32_t imaginary_part = make_function(exact_opcode::sine, angle);
            uint32_t imaginary = intern_compound(exact_opcode::constant_i, {});
            const exact_node &real_node = node(real);
            const exact_node &imaginary_node = node(imaginary_part);
            bool real_zero = real_node.op == exact_opcode::value &&
                values[real_node.payload].is_zero();
            if(real_zero && imaginary_node.op == exact_opcode::value){
                const exact_value &coefficient_value =
                    values[imaginary_node.payload];
                if(coefficient_value.is_one()) return imaginary;
                if(coefficient_value == exact_value(-1))
                    return make_multiply({intern_value(exact_value(-1)),
                                          imaginary});
            }
            return make_add({real, make_multiply({imaginary_part, imaginary})});
        }
        auto logarithm_argument = [&](uint32_t id, uint32_t &result){
            const exact_node &candidate = node(id);
            if(candidate.op != exact_opcode::natural_logarithm) return false;
            result = children(candidate)[0];
            const exact_node &source = node(result);
            if(source.op == exact_opcode::value){
                const exact_value &exact = values[source.payload];
                if(exact.is_zero() || exact.is_negative()) return false;
            }
            return true;
        };

        uint32_t inverse = 0;
        if(logarithm_argument(value, inverse)) return inverse;
        if(argument.op == exact_opcode::add){
            std::vector<uint32_t> factors;
            std::vector<uint32_t> remainder;
            const uint32_t *terms = children(argument);
            for(size_t i = 0; i < argument.operand_count; ++i){
                uint32_t factor = 0;
                if(logarithm_argument(terms[i], factor))
                    factors.push_back(factor);
                else
                    remainder.push_back(terms[i]);
            }
            if(!factors.empty()){
                if(!remainder.empty()){
                    uint32_t rest = make_add(std::move(remainder));
                    factors.push_back(make_function(exact_opcode::exponential,
                                                    rest));
                }
                return make_multiply(std::move(factors));
            }
        }
    }

    if(operation == exact_opcode::natural_logarithm){
        if(argument.op == exact_opcode::constant_i){
            uint32_t half = intern_value(exact_value(
                precq_t(precn_t(1), precn_t(2))));
            uint32_t pi = intern_compound(exact_opcode::constant_pi, {});
            return make_multiply({half, value, pi});
        }
        if(argument.op == exact_opcode::constant_e)
            return intern_value(exact_value(1));
        if(argument.op == exact_opcode::exponential)
            return children(argument)[0];
        if(argument.op == exact_opcode::power){
            const uint32_t *power = children(argument);
            if(node(power[0]).op == exact_opcode::constant_e) return power[1];
        }
    }

    auto pi_multiple = [&](int64_t &numerator, uint64_t &denominator){
        precq_t coefficient(1);
        bool found_pi = false;
        auto accept = [&](uint32_t factor){
            const exact_node &current = node(factor);
            if(current.op == exact_opcode::constant_pi){
                if(found_pi) return false;
                found_pi = true;
                return true;
            }
            if(current.op != exact_opcode::value) return false;
            const exact_value &exact = values[current.payload];
            if(exact.is_approximate()) return false;
            coefficient = coefficient * exact.rational();
            return true;
        };
        if(argument.op == exact_opcode::multiply){
            const uint32_t *factors = children(argument);
            for(size_t i = 0; i < argument.operand_count; ++i)
                if(!accept(factors[i])) return false;
        }else if(!accept(value)){
            return false;
        }
        if(!found_pi) return false;
        const precn_t &num = coefficient.numerator();
        const precn_t &den = coefficient.denominator();
        if(num.rsiz > 1 || den.rsiz > 1 || den.rsiz == 0) return false;
        uint64_t magnitude = num.rsiz ? num.a[0] : 0;
        denominator = den.a[0];
        if(magnitude > (uint64_t)INT64_MAX || denominator > 1000000)
            return false;
        numerator = coefficient.is_negative() ? -(int64_t)magnitude
                                              : (int64_t)magnitude;
        return true;
    };

    if(operation == exact_opcode::sine || operation == exact_opcode::cosine ||
       operation == exact_opcode::tangent){
        int64_t numerator = 0;
        uint64_t denominator = 1;
        if(pi_multiple(numerator, denominator)){
            int64_t period = (int64_t)(2 * denominator);
            numerator %= period;
            if(numerator < 0) numerator += period;
            int64_t scaled = numerator * 12;
            if(scaled % (int64_t)denominator == 0){
                unsigned angle = (unsigned)(scaled / (int64_t)denominator) % 24;
                uint32_t zero = intern_value(exact_value(0));
                uint32_t one = intern_value(exact_value(1));
                uint32_t minus_one = intern_value(exact_value(-1));
                uint32_t half = intern_value(exact_value(
                    precq_t(precn_t(1), precn_t(2))));
                auto negate = [&](uint32_t id){
                    return make_multiply({minus_one, id});
                };
                auto radical_over = [&](uint64_t radicand, uint64_t divisor){
                    uint32_t radical = make_sqrt(intern_value(exact_value(radicand)));
                    uint32_t coefficient = intern_value(exact_value(
                        precq_t(precn_t(1), precn_t(divisor))));
                    return make_multiply({coefficient, radical});
                };
                auto sine_value = [&](unsigned a) -> uint32_t{
                    switch(a % 24){
                    case 0: case 12: return zero;
                    case 2: case 10: return half;
                    case 3: case 9: return radical_over(2, 2);
                    case 4: case 8: return radical_over(3, 2);
                    case 6: return one;
                    case 14: case 22: return negate(half);
                    case 15: case 21: return negate(radical_over(2, 2));
                    case 16: case 20: return negate(radical_over(3, 2));
                    case 18: return minus_one;
                    default: return UINT32_MAX;
                    }
                };
                if(operation == exact_opcode::sine){
                    uint32_t result = sine_value(angle);
                    if(result != UINT32_MAX) return result;
                }else if(operation == exact_opcode::cosine){
                    uint32_t result = sine_value((angle + 6) % 24);
                    if(result != UINT32_MAX) return result;
                }else{
                    switch(angle){
                    case 0: case 12: return zero;
                    case 3: case 15: return one;
                    case 9: case 21: return minus_one;
                    case 2: case 14: return radical_over(3, 3);
                    case 4: case 16: return radical_over(3, 1);
                    case 8: case 20: return negate(radical_over(3, 1));
                    case 10: case 22: return negate(radical_over(3, 3));
                    case 6: case 18:
                        throw std::domain_error("tan is undefined at pi/2 + k*pi");
                    default: break;
                    }
                }
            }
        }
    }

    if(argument.op == exact_opcode::value){
        const exact_value &exact = values[argument.payload];
        // Decimal inputs carry an approximation contract even when their
        // current binary value is exactly 0 or 1.  Keep that contract until
        // promote_approximate evaluates the complete numeric expression.
        if(!exact.is_approximate() && exact.is_zero()){
            if(operation == exact_opcode::cosine ||
               operation == exact_opcode::hyperbolic_cosine ||
               operation == exact_opcode::exponential)
                return intern_value(exact_value(1));
            if(operation == exact_opcode::sine ||
               operation == exact_opcode::tangent ||
               operation == exact_opcode::arc_sine ||
               operation == exact_opcode::arc_tangent ||
               operation == exact_opcode::hyperbolic_sine ||
               operation == exact_opcode::hyperbolic_tangent ||
               operation == exact_opcode::inverse_hyperbolic_sine ||
               operation == exact_opcode::inverse_hyperbolic_tangent)
                return value;
        }
        if(!exact.is_approximate() && exact.is_one() &&
           (operation == exact_opcode::natural_logarithm ||
            operation == exact_opcode::logarithm_base_2 ||
            operation == exact_opcode::logarithm_base_10 ||
            operation == exact_opcode::inverse_hyperbolic_cosine)){
            return intern_value(exact_value(0));
        }
        if(!exact.is_approximate() && exact.is_one() &&
           operation == exact_opcode::exponential)
            return intern_compound(exact_opcode::constant_e, {});
        if(exact.is_approximate()){
            Number number = exact.number();
            if(operation == exact_opcode::absolute_value) number = ::abs(number);
            else if(operation == exact_opcode::exponential) number = ::exp(number);
            else if(operation == exact_opcode::sine) number = ::sin(number);
            else if(operation == exact_opcode::cosine) number = ::cos(number);
            else if(operation == exact_opcode::tangent) number = ::tan(number);
            else if(operation == exact_opcode::arc_sine) number = ::asin(number);
            else if(operation == exact_opcode::arc_cosine) number = ::acos(number);
            else if(operation == exact_opcode::arc_tangent) number = ::atan(number);
            else if(operation == exact_opcode::hyperbolic_sine) number = ::sinh(number);
            else if(operation == exact_opcode::hyperbolic_cosine) number = ::cosh(number);
            else if(operation == exact_opcode::hyperbolic_tangent) number = ::tanh(number);
            else if(operation == exact_opcode::inverse_hyperbolic_sine) number = ::asinh(number);
            else if(operation == exact_opcode::inverse_hyperbolic_cosine) number = ::acosh(number);
            else if(operation == exact_opcode::inverse_hyperbolic_tangent) number = ::atanh(number);
            else if(operation == exact_opcode::natural_logarithm) number = ::ln(number);
            else if(operation == exact_opcode::logarithm_base_2) number = ::log2(number);
            else if(operation == exact_opcode::sine_integral) number = ::Si(number);
            else if(operation == exact_opcode::cosine_integral) number = ::Ci(number);
            else if(operation == exact_opcode::exponential_integral) number = ::Ei(number);
            else if(operation == exact_opcode::error_function) number = ::erf(number);
            else if(operation == exact_opcode::imaginary_error_function) number = ::erfi(number);
            else number = ::log10(number);
            return intern_value(exact_value(std::move(number)));
        }
        if(operation == exact_opcode::absolute_value)
            return exact.is_negative() ? intern_value(-exact) : value;
    }
    if(argument.op == exact_opcode::constant_pi){
        if(operation == exact_opcode::sine || operation == exact_opcode::tangent)
            return intern_value(exact_value(0));
        if(operation == exact_opcode::cosine)
            return intern_value(exact_value(-1));
    }
    if(argument.op == exact_opcode::constant_e &&
       operation == exact_opcode::natural_logarithm)
        return intern_value(exact_value(1));
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
    bool saw_complex = false;
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
        if(current.op == exact_opcode::constant_i){
            saw_complex = true;
            return true;
        }
        if(current.op == exact_opcode::constant_pi ||
           current.op == exact_opcode::constant_e) return true;
        const uint32_t *args = children(current);
        for(size_t i = 0; i < current.operand_count; ++i)
            if(!self(self, args[i])) return false;
        return current.op == exact_opcode::add ||
               current.op == exact_opcode::multiply ||
               current.op == exact_opcode::power ||
               current.op == exact_opcode::square_root ||
               current.op == exact_opcode::partial_gamma ||
               exact_unary_function(current.op);
    };
    if(!numeric_tree(numeric_tree, expression) || !saw_approximate)
        return expression;
    if(!std::isfinite(precision)) precision = 64.0;

    if(saw_complex){
        std::unordered_map<uint32_t, Complex> evaluated;
        auto evaluate = [&](auto &&self, uint32_t id) -> Complex{
            auto cached = evaluated.find(id);
            if(cached != evaluated.end()) return cached->second;
            const exact_node &current = node(id);
            Complex result;
            if(current.op == exact_opcode::value){
                result = Complex(values[current.payload].to_number(precision));
            }else if(current.op == exact_opcode::constant_i){
                result = Complex(Number(0), Number(1));
            }else if(current.op == exact_opcode::constant_pi){
                result = Complex(getpi(constant_decimal_digits(precision)));
            }else if(current.op == exact_opcode::constant_e){
                result = Complex(gete(constant_decimal_digits(precision)));
            }else{
                const uint32_t *args = children(current);
                if(current.op == exact_opcode::add){
                    result = Complex(Number(0));
                    result.set_precision(precision + 32.0);
                    for(size_t i = 0; i < current.operand_count; ++i)
                        result += self(self, args[i]);
                }else if(current.op == exact_opcode::multiply){
                    result = Complex(Number(1));
                    result.set_precision(precision + 32.0);
                    for(size_t i = 0; i < current.operand_count; ++i)
                        result *= self(self, args[i]);
                }else if(current.op == exact_opcode::power){
                    result = ::pow(self(self, args[0]), self(self, args[1]));
                }else if(current.op == exact_opcode::square_root){
                    result = ::sqrt(self(self, args[0]));
                }else if(current.op == exact_opcode::absolute_value){
                    result = Complex(::abs(self(self, args[0])));
                }else if(current.op == exact_opcode::exponential){
                    result = ::exp(self(self, args[0]));
                }else if(current.op == exact_opcode::natural_logarithm){
                    result = ::ln(self(self, args[0]));
                }else if(current.op == exact_opcode::logarithm_base_2){
                    result = ::ln(self(self, args[0])) /
                             Complex(::ln(Number(2)));
                }else if(current.op == exact_opcode::logarithm_base_10){
                    result = ::ln(self(self, args[0])) /
                             Complex(::ln(Number(10)));
                }else{
                    throw std::invalid_argument(
                        "complex approximation is not implemented for this function");
                }
            }
            result.set_precision(precision);
            evaluated.emplace(id, result);
            return result;
        };
        Complex result = evaluate(evaluate, expression);
        Number real = result.real();
        Number imag = result.imag();
        Number scale = std::max(::abs(real), ::abs(imag));
        if(scale < Number(1)) scale = Number(1);
        int64_t tolerance_bits = precision > 16.0
            ? (int64_t)std::min<double>(precision * 0.5, (double)INT64_MAX) : 8;
        Number tolerance = scale >> tolerance_bits;
        if(::abs(real) < tolerance) real = Number(0);
        if(::abs(imag) < tolerance) imag = Number(0);
        if((std::string)real == "0" || (std::string)real == "-0") real = Number(0);
        if((std::string)imag == "0" || (std::string)imag == "-0") imag = Number(0);
        real.set_precision(precision);
        imag.set_precision(precision);
        bool real_zero = real.is_zero();
        uint32_t real_node = intern_value(exact_value(std::move(real)));
        if(imag.is_zero()) return real_node;
        uint32_t imag_node = intern_value(exact_value(std::move(imag)));
        uint32_t imaginary = intern_compound(exact_opcode::constant_i, {});
        uint32_t imag_term = make_multiply({imag_node, imaginary});
        return real_zero ? imag_term : make_add({real_node, imag_term});
    }

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
        }else if(current.op == exact_opcode::constant_pi){
            result = getpi(constant_decimal_digits(precision));
            result.set_precision(precision);
        }else if(current.op == exact_opcode::constant_e){
            result = gete(constant_decimal_digits(precision));
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
            }else if(current.op == exact_opcode::absolute_value){
                result = ::abs(self(self, args[0]));
            }else if(current.op == exact_opcode::exponential){
                result = ::exp(self(self, args[0]));
            }else if(current.op == exact_opcode::sine){
                result = ::sin(self(self, args[0]));
            }else if(current.op == exact_opcode::cosine){
                result = ::cos(self(self, args[0]));
            }else if(current.op == exact_opcode::tangent){
                result = ::tan(self(self, args[0]));
            }else if(current.op == exact_opcode::arc_sine){
                result = ::asin(self(self, args[0]));
            }else if(current.op == exact_opcode::arc_cosine){
                result = ::acos(self(self, args[0]));
            }else if(current.op == exact_opcode::arc_tangent){
                result = ::atan(self(self, args[0]));
            }else if(current.op == exact_opcode::hyperbolic_sine){
                result = ::sinh(self(self, args[0]));
            }else if(current.op == exact_opcode::hyperbolic_cosine){
                result = ::cosh(self(self, args[0]));
            }else if(current.op == exact_opcode::hyperbolic_tangent){
                result = ::tanh(self(self, args[0]));
            }else if(current.op == exact_opcode::inverse_hyperbolic_sine){
                result = ::asinh(self(self, args[0]));
            }else if(current.op == exact_opcode::inverse_hyperbolic_cosine){
                result = ::acosh(self(self, args[0]));
            }else if(current.op == exact_opcode::inverse_hyperbolic_tangent){
                result = ::atanh(self(self, args[0]));
            }else if(current.op == exact_opcode::sine_integral){
                result = ::Si(self(self, args[0]));
            }else if(current.op == exact_opcode::cosine_integral){
                result = ::Ci(self(self, args[0]));
            }else if(current.op == exact_opcode::exponential_integral){
                result = ::Ei(self(self, args[0]));
            }else if(current.op == exact_opcode::error_function){
                result = ::erf(self(self, args[0]));
            }else if(current.op == exact_opcode::imaginary_error_function){
                result = ::erfi(self(self, args[0]));
            }else if(current.op == exact_opcode::partial_gamma){
                result = ::partial_gamma(self(self, args[0]),
                                         self(self, args[1]));
            }else if(current.op == exact_opcode::natural_logarithm){
                result = ::ln(self(self, args[0]));
            }else if(current.op == exact_opcode::logarithm_base_2){
                result = ::log2(self(self, args[0]));
            }else{
                result = ::log10(self(self, args[0]));
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
    if(op == exact_opcode::rule) return 0;
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
    }else if(current.op == exact_opcode::constant_pi ||
             current.op == exact_opcode::constant_e ||
             current.op == exact_opcode::constant_i){
        result = exact_opcode_name(current.op);
    }else if(current.op == exact_opcode::expression_list){
        result.push_back('{');
        const uint32_t *args = children(current);
        for(size_t i = 0; i < current.operand_count; ++i){
            if(i) result += ", ";
            result += print(args[i]);
        }
        result.push_back('}');
    }else if(current.op == exact_opcode::rule){
        if(current.operand_count != 2)
            throw std::logic_error("rule node must have two operands");
        const uint32_t *args = children(current);
        result = print(args[0], 1) + " -> " + print(args[1], 0);
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
        auto polynomial_degree = [this](auto &&self, uint32_t id,
                                        uint32_t &symbol, size_t &degree) -> bool{
            const exact_node &value = node(id);
            if(value.op == exact_opcode::value){ degree = 0; return true; }
            if(value.op == exact_opcode::symbol){
                if(symbol != UINT32_MAX && symbol != id) return false;
                symbol = id;
                degree = 1;
                return true;
            }
            const uint32_t *parts = children(value);
            if(value.op == exact_opcode::add){
                degree = 0;
                for(size_t i = 0; i < value.operand_count; ++i){
                    size_t child_degree = 0;
                    if(!self(self, parts[i], symbol, child_degree)) return false;
                    degree = std::max(degree, child_degree);
                }
                return true;
            }
            if(value.op == exact_opcode::multiply){
                degree = 0;
                for(size_t i = 0; i < value.operand_count; ++i){
                    size_t child_degree = 0;
                    if(!self(self, parts[i], symbol, child_degree) ||
                       child_degree > SIZE_MAX - degree) return false;
                    degree += child_degree;
                }
                return true;
            }
            if(value.op == exact_opcode::power){
                int64_t exponent = 0;
                const exact_node &power = node(parts[1]);
                size_t base_degree = 0;
                if(power.op != exact_opcode::value ||
                   !integer_i64(values[power.payload], exponent) || exponent < 0 ||
                   !self(self, parts[0], symbol, base_degree) ||
                   (uint64_t)exponent > SIZE_MAX /
                       std::max<size_t>(base_degree, 1)) return false;
                degree = base_degree * (size_t)exponent;
                return true;
            }
            return false;
        };
        auto factor_less = [&](uint32_t a, uint32_t b){
            bool av = node(a).op == exact_opcode::value;
            bool bv = node(b).op == exact_opcode::value;
            if(av != bv) return av;
            uint32_t symbol_a = UINT32_MAX, symbol_b = UINT32_MAX;
            size_t degree_a = 0, degree_b = 0;
            bool polynomial_a = polynomial_degree(
                polynomial_degree, a, symbol_a, degree_a);
            bool polynomial_b = polynomial_degree(
                polynomial_degree, b, symbol_b, degree_b);
            if(polynomial_a && polynomial_b && symbol_a == symbol_b &&
               degree_a != degree_b) return degree_a < degree_b;
            return print(a) < print(b);
        };
        if(denominator.empty()){
            std::stable_sort(numerator.begin(), numerator.end(), factor_less);
            size_t begin = 0;
            if(numerator.size() > 1 && node(numerator[0]).op == exact_opcode::value){
                const exact_value &coefficient = values[node(numerator[0]).payload];
                if(coefficient.is_minus_one()){
                    result.push_back('-');
                    begin = 1;
                }else if(coefficient.is_one()) begin = 1;
            }
            for(size_t i = begin; i < numerator.size(); ++i){
                if(i != begin) result.push_back('*');
                result += print(numerator[i], precedence);
            }
        }else{
            std::stable_sort(numerator.begin(), numerator.end(), factor_less);
            if(numerator.empty()) result = "1";
            else{
                size_t begin = 0;
                if(numerator.size() > 1 &&
                   node(numerator[0]).op == exact_opcode::value){
                    const exact_value &coefficient =
                        values[node(numerator[0]).payload];
                    if(coefficient.is_minus_one()){
                        result.push_back('-');
                        begin = 1;
                    }else if(coefficient.is_one()) begin = 1;
                }
                for(size_t i = begin; i < numerator.size(); ++i){
                    if(i != begin) result.push_back('*');
                    result += print(numerator[i], precedence);
                }
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
    }else if(exact_unary_function(current.op)){
        result = std::string(exact_opcode_name(current.op)) + "(" +
                 print(children(current)[0]) + ")";
    }else if(current.op == exact_opcode::partial_gamma ||
             current.op == exact_opcode::derivative ||
             current.op == exact_opcode::integral){
        const uint32_t *args = children(current);
        result = std::string(exact_opcode_name(current.op)) + "(" +
                 print(args[0]) + ", " + print(args[1]) + ")";
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

exact_complex::exact_complex() : real_(), imag_(){}
exact_complex::exact_complex(const exact_expr &real) : real_(real), imag_(){
    if(real.valid()) imag_ = exact_expr(real.storage_,
        real.storage_->intern_value(exact_value(0)));
}
exact_complex::exact_complex(const exact_expr &real, const exact_expr &imag)
    : real_(real), imag_(imag){
    if(!real.valid() || !imag.valid() || real.storage_ != imag.storage_)
        throw std::invalid_argument(
            "exact complex components belong to different contexts");
}
const exact_expr &exact_complex::real() const{ return real_; }
const exact_expr &exact_complex::imag() const{ return imag_; }
bool exact_complex::valid() const{ return real_.valid() && imag_.valid(); }
exact_expr exact_complex::expression() const{
    if(!valid()) return exact_expr();
    std::shared_ptr<exact_storage> storage = real_.storage_;
    uint32_t imaginary = storage->intern_compound(exact_opcode::constant_i, {});
    uint32_t term = storage->make_multiply({imag_.root_, imaginary});
    return exact_expr(storage, storage->make_add({real_.root_, term}));
}
exact_complex operator+(const exact_complex &a, const exact_complex &b){
    return exact_complex(a.real() + b.real(), a.imag() + b.imag());
}
exact_complex operator-(const exact_complex &a, const exact_complex &b){
    return exact_complex(a.real() - b.real(), a.imag() - b.imag());
}
exact_complex operator-(const exact_complex &a){
    return exact_complex(-a.real(), -a.imag());
}
exact_complex operator*(const exact_complex &a, const exact_complex &b){
    return exact_complex(a.real() * b.real() - a.imag() * b.imag(),
                         a.real() * b.imag() + a.imag() * b.real());
}
exact_complex operator/(const exact_complex &a, const exact_complex &b){
    exact_expr denominator = b.real() * b.real() + b.imag() * b.imag();
    return exact_complex(
        (a.real() * b.real() + a.imag() * b.imag()) / denominator,
        (a.imag() * b.real() - a.real() * b.imag()) / denominator);
}
exact_complex conjugate(const exact_complex &a){
    return exact_complex(a.real(), -a.imag());
}
exact_expr norm(const exact_complex &a){
    return a.real() * a.real() + a.imag() * a.imag();
}
exact_complex &exact_complex::operator+=(const exact_complex &other){
    return *this = *this + other;
}
exact_complex &exact_complex::operator-=(const exact_complex &other){
    return *this = *this - other;
}
exact_complex &exact_complex::operator*=(const exact_complex &other){
    return *this = *this * other;
}
exact_complex &exact_complex::operator/=(const exact_complex &other){
    return *this = *this / other;
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
exact_expr exact_context::pi(){
    return exact_expr(storage_, storage_->intern_compound(
        exact_opcode::constant_pi, {}));
}
exact_expr exact_context::e(){
    return exact_expr(storage_, storage_->intern_compound(
        exact_opcode::constant_e, {}));
}
exact_expr exact_context::i(){
    return exact_expr(storage_, storage_->intern_compound(
        exact_opcode::constant_i, {}));
}
void exact_context::assume(const exact_expr &symbol,
                           const std::string &property){
    if(!symbol.valid() || symbol.storage_ != storage_ ||
       storage_->node(symbol.root_).op != exact_opcode::symbol)
        throw std::invalid_argument("assume requires a symbol");
    if(property == "none"){
        storage_->assumptions.erase(symbol.root_);
        return;
    }
    uint8_t flags = 0;
    if(property == "real") flags = exact_storage::assumed_real;
    else if(property == "nonnegative")
        flags = exact_storage::assumed_real |
                exact_storage::assumed_nonnegative;
    else if(property == "positive")
        flags = exact_storage::assumed_real |
                exact_storage::assumed_nonnegative |
                exact_storage::assumed_positive;
    else throw std::invalid_argument(
        "unknown assumption; expected none, real, nonnegative, or positive");
    storage_->assumptions[symbol.root_] |= flags;
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
       storage_->values[denominator.payload].is_zero())
        throw std::domain_error("division by zero");

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
exact_expr exact_context::absolute_value(const exact_expr &value){
    if(!value.valid() || value.storage_ != storage_)
        throw std::invalid_argument("exact expression belongs to a different context");
    uint32_t result = storage_->make_function(exact_opcode::absolute_value,
                                               value.root_);
    return exact_expr(storage_, storage_->promote_approximate(result));
}
exact_expr exact_context::exponential(const exact_expr &value){
    if(!value.valid() || value.storage_ != storage_)
        throw std::invalid_argument("exact expression belongs to a different context");
    uint32_t result = storage_->make_function(exact_opcode::exponential,
                                               value.root_);
    return exact_expr(storage_, storage_->promote_approximate(result));
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
exact_expr exact_context::arc_sine(const exact_expr &value){
    if(!value.valid() || value.storage_ != storage_)
        throw std::invalid_argument("exact expression belongs to a different context");
    return exact_expr(storage_, storage_->make_function(exact_opcode::arc_sine,
                                                         value.root_));
}
exact_expr exact_context::arc_cosine(const exact_expr &value){
    if(!value.valid() || value.storage_ != storage_)
        throw std::invalid_argument("exact expression belongs to a different context");
    return exact_expr(storage_, storage_->make_function(exact_opcode::arc_cosine,
                                                         value.root_));
}
exact_expr exact_context::arc_tangent(const exact_expr &value){
    if(!value.valid() || value.storage_ != storage_)
        throw std::invalid_argument("exact expression belongs to a different context");
    return exact_expr(storage_, storage_->make_function(exact_opcode::arc_tangent,
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
exact_expr exact_context::inverse_hyperbolic_sine(const exact_expr &value){
    if(!value.valid() || value.storage_ != storage_)
        throw std::invalid_argument("exact expression belongs to a different context");
    return exact_expr(storage_, storage_->make_function(
        exact_opcode::inverse_hyperbolic_sine, value.root_));
}
exact_expr exact_context::inverse_hyperbolic_cosine(const exact_expr &value){
    if(!value.valid() || value.storage_ != storage_)
        throw std::invalid_argument("exact expression belongs to a different context");
    return exact_expr(storage_, storage_->make_function(
        exact_opcode::inverse_hyperbolic_cosine, value.root_));
}
exact_expr exact_context::inverse_hyperbolic_tangent(const exact_expr &value){
    if(!value.valid() || value.storage_ != storage_)
        throw std::invalid_argument("exact expression belongs to a different context");
    return exact_expr(storage_, storage_->make_function(
        exact_opcode::inverse_hyperbolic_tangent, value.root_));
}
exact_expr exact_context::natural_logarithm(const exact_expr &value){
    if(!value.valid() || value.storage_ != storage_)
        throw std::invalid_argument("exact expression belongs to a different context");
    uint32_t result = storage_->make_function(exact_opcode::natural_logarithm,
                                               value.root_);
    return exact_expr(storage_, storage_->promote_approximate(result));
}
exact_expr exact_context::logarithm_base_2(const exact_expr &value){
    if(!value.valid() || value.storage_ != storage_)
        throw std::invalid_argument("exact expression belongs to a different context");
    uint32_t result = storage_->make_function(exact_opcode::logarithm_base_2,
                                               value.root_);
    return exact_expr(storage_, storage_->promote_approximate(result));
}
exact_expr exact_context::logarithm_base_10(const exact_expr &value){
    if(!value.valid() || value.storage_ != storage_)
        throw std::invalid_argument("exact expression belongs to a different context");
    uint32_t result = storage_->make_function(exact_opcode::logarithm_base_10,
                                               value.root_);
    return exact_expr(storage_, storage_->promote_approximate(result));
}
exact_expr exact_context::sine_integral(const exact_expr &value){
    if(!value.valid() || value.storage_ != storage_)
        throw std::invalid_argument("exact expression belongs to a different context");
    uint32_t result = storage_->make_function(exact_opcode::sine_integral,
                                               value.root_);
    return exact_expr(storage_, storage_->promote_approximate(result));
}
exact_expr exact_context::cosine_integral(const exact_expr &value){
    if(!value.valid() || value.storage_ != storage_)
        throw std::invalid_argument("exact expression belongs to a different context");
    uint32_t result = storage_->make_function(exact_opcode::cosine_integral,
                                               value.root_);
    return exact_expr(storage_, storage_->promote_approximate(result));
}
exact_expr exact_context::exponential_integral(const exact_expr &value){
    if(!value.valid() || value.storage_ != storage_)
        throw std::invalid_argument("exact expression belongs to a different context");
    uint32_t result = storage_->make_function(exact_opcode::exponential_integral,
                                               value.root_);
    return exact_expr(storage_, storage_->promote_approximate(result));
}
exact_expr exact_context::error_function(const exact_expr &value){
    if(!value.valid() || value.storage_ != storage_)
        throw std::invalid_argument("exact expression belongs to a different context");
    uint32_t result = storage_->make_function(exact_opcode::error_function,
                                               value.root_);
    return exact_expr(storage_, storage_->promote_approximate(result));
}
exact_expr exact_context::imaginary_error_function(const exact_expr &value){
    if(!value.valid() || value.storage_ != storage_)
        throw std::invalid_argument("exact expression belongs to a different context");
    uint32_t result = storage_->make_function(
        exact_opcode::imaginary_error_function, value.root_);
    return exact_expr(storage_, storage_->promote_approximate(result));
}
exact_expr exact_context::partial_gamma(const exact_expr &a,
                                        const exact_expr &x){
    if(!a.valid() || !x.valid() || a.storage_ != storage_ ||
       x.storage_ != storage_)
        throw std::invalid_argument("exact expressions belong to different contexts");
    uint32_t result;
    if(a.is_value() && x.is_value() &&
       (a.value().is_approximate() || x.value().is_approximate())){
        double precision = approximate_precision(a.value(), x.value());
        Number number = ::partial_gamma(a.value().to_number(precision),
                                        x.value().to_number(precision));
        number.set_precision(precision);
        result = storage_->intern_value(exact_value(std::move(number)));
    }else{
        result = storage_->intern_compound(exact_opcode::partial_gamma,
                                            {a.root_, x.root_});
    }
    return exact_expr(storage_, result);
}

exact_expr exact_context::differentiate(const exact_expr &expression,
                                        const exact_expr &variable){
    if(!expression.valid() || !variable.valid() ||
       expression.storage_ != storage_ || variable.storage_ != storage_ ||
       storage_->node(variable.root_).op != exact_opcode::symbol)
        throw std::invalid_argument(
            "differentiate requires an expression and a symbol in one context");

    std::unordered_map<uint32_t, bool> dependency_memo;
    auto depends = [&](auto &&self, uint32_t id) -> bool{
        if(id == variable.root_) return true;
        auto cached = dependency_memo.find(id);
        if(cached != dependency_memo.end()) return cached->second;
        // Building a derivative interns new nodes and may reallocate storage.
        // Copies keep recursive calls from invalidating the current operands.
        exact_node node = storage_->node(id);
        const uint32_t *child_data = storage_->children(node);
        std::vector<uint32_t> args(child_data,
                                   child_data + node.operand_count);
        bool result = false;
        for(size_t i = 0; i < node.operand_count; ++i)
            if(self(self, args[i])){ result = true; break; }
        dependency_memo.emplace(id, result);
        return result;
    };

    std::unordered_map<uint32_t, exact_expr> memo;
    std::function<exact_expr(uint32_t)> derivative = [&](uint32_t id){
        auto cached = memo.find(id);
        if(cached != memo.end()) return cached->second;
        exact_expr source(storage_, id);
        // Recursive derivatives intern nodes and can reallocate both arena
        // vectors. Never retain references or child pointers across a call.
        exact_node node = storage_->node(id);
        const uint32_t *child_data = storage_->children(node);
        std::vector<uint32_t> args(child_data,
                                   child_data + node.operand_count);
        exact_expr result;
        if(!depends(depends, id)){
            result = integer(0);
        }else if(id == variable.root_){
            result = integer(1);
        }else if(node.op == exact_opcode::add){
            std::vector<exact_expr> terms;
            terms.reserve(node.operand_count);
            for(size_t i = 0; i < node.operand_count; ++i)
                terms.push_back(derivative(args[i]));
            result = add(terms);
        }else if(node.op == exact_opcode::multiply){
            std::vector<exact_expr> terms;
            for(size_t differentiated = 0; differentiated < node.operand_count;
                ++differentiated){
                if(!depends(depends, args[differentiated])) continue;
                std::vector<exact_expr> factors;
                factors.reserve(node.operand_count);
                for(size_t i = 0; i < node.operand_count; ++i)
                    factors.push_back(i == differentiated
                        ? derivative(args[i]) : exact_expr(storage_, args[i]));
                terms.push_back(multiply(factors));
            }
            result = add(terms);
        }else if(node.op == exact_opcode::power){
            exact_expr base(storage_, args[0]), exponent(storage_, args[1]);
            exact_expr db = derivative(args[0]);
            if(!depends(depends, args[1])){
                result = exponent * power(base, exponent - integer(1)) * db;
            }else{
                exact_expr de = derivative(args[1]);
                result = power(base, exponent) *
                    (de * natural_logarithm(base) + exponent * db / base);
            }
        }else if(node.op == exact_opcode::square_root){
            exact_expr inner(storage_, args[0]);
            result = derivative(args[0]) /
                     (integer(2) * square_root(inner));
        }else if(exact_unary_function(node.op)){
            exact_expr inner(storage_, args[0]);
            exact_expr di = derivative(args[0]);
            exact_expr one = integer(1);
            if(node.op == exact_opcode::exponential)
                result = exponential(inner) * di;
            else if(node.op == exact_opcode::sine)
                result = cosine(inner) * di;
            else if(node.op == exact_opcode::cosine)
                result = -sine(inner) * di;
            else if(node.op == exact_opcode::tangent)
                result = di / power(cosine(inner), integer(2));
            else if(node.op == exact_opcode::arc_sine)
                result = di / square_root(one - power(inner, integer(2)));
            else if(node.op == exact_opcode::arc_cosine)
                result = -di / square_root(one - power(inner, integer(2)));
            else if(node.op == exact_opcode::arc_tangent)
                result = di / (one + power(inner, integer(2)));
            else if(node.op == exact_opcode::hyperbolic_sine)
                result = hyperbolic_cosine(inner) * di;
            else if(node.op == exact_opcode::hyperbolic_cosine)
                result = hyperbolic_sine(inner) * di;
            else if(node.op == exact_opcode::hyperbolic_tangent)
                result = di / power(hyperbolic_cosine(inner), integer(2));
            else if(node.op == exact_opcode::inverse_hyperbolic_sine)
                result = di / square_root(power(inner, integer(2)) + one);
            else if(node.op == exact_opcode::inverse_hyperbolic_cosine)
                result = di / (square_root(inner - one) *
                               square_root(inner + one));
            else if(node.op == exact_opcode::inverse_hyperbolic_tangent)
                result = di / (one - power(inner, integer(2)));
            else if(node.op == exact_opcode::natural_logarithm)
                result = di / inner;
            else if(node.op == exact_opcode::logarithm_base_2)
                result = di / (inner * natural_logarithm(integer(2)));
            else if(node.op == exact_opcode::logarithm_base_10)
                result = di / (inner * natural_logarithm(integer(10)));
            else if(node.op == exact_opcode::sine_integral)
                result = sine(inner) * di / inner;
            else if(node.op == exact_opcode::cosine_integral)
                result = cosine(inner) * di / inner;
            else if(node.op == exact_opcode::exponential_integral)
                result = exponential(inner) * di / inner;
            else if(node.op == exact_opcode::error_function)
                result = integer(2) * exponential(-power(inner, integer(2))) * di /
                         square_root(pi());
            else if(node.op == exact_opcode::imaginary_error_function)
                result = integer(2) * exponential(power(inner, integer(2))) * di /
                         square_root(pi());
            else
                result = exact_expr(storage_, storage_->intern_compound(
                    exact_opcode::derivative, {id, variable.root_}));
        }else if(node.op == exact_opcode::partial_gamma &&
                 !depends(depends, args[0])){
            exact_expr a(storage_, args[0]), x(storage_, args[1]);
            result = -power(x, a - integer(1)) * exponential(-x) *
                     derivative(args[1]);
        }else{
            result = exact_expr(storage_, storage_->intern_compound(
                exact_opcode::derivative, {id, variable.root_}));
        }
        memo.emplace(id, result);
        return result;
    };
    return simplify(derivative(expression.root_));
}

namespace{

using integration_poly = std::vector<exact_value>;

static void integration_trim(integration_poly &a){
    while(a.size() > 1 && a.back().is_zero()) a.pop_back();
}

static integration_poly integration_add(const integration_poly &a,
                                         const integration_poly &b){
    integration_poly r(std::max(a.size(), b.size()), exact_value(0));
    for(size_t i = 0; i < a.size(); ++i) r[i] = r[i] + a[i];
    for(size_t i = 0; i < b.size(); ++i) r[i] = r[i] + b[i];
    integration_trim(r);
    return r;
}

static integration_poly integration_mul(const integration_poly &a,
                                         const integration_poly &b){
    integration_poly r(a.size() + b.size() - 1, exact_value(0));
    for(size_t i = 0; i < a.size(); ++i)
        for(size_t j = 0; j < b.size(); ++j)
            r[i + j] = r[i + j] + a[i] * b[j];
    integration_trim(r);
    return r;
}

static bool integration_exponent(const exact_expr &value, size_t &result){
    if(!value.is_value() || !value.value().is_integer()) return false;
    exact_value exact = value.value();
    const precz_t &integer = exact.integer();
    if(integer.is_negative() || integer.magnitude().rsiz > 1) return false;
    result = integer.magnitude().rsiz ? (size_t)integer.magnitude().a[0] : 0;
    return true;
}

static bool integration_parse_poly(const exact_expr &expression,
                                   const exact_expr &variable,
                                   integration_poly &result){
    if(expression == variable){
        result = {exact_value(0), exact_value(1)};
        return true;
    }
    if(expression.is_value() && !expression.value().is_approximate()){
        result = {expression.value()};
        return true;
    }
    if(expression.operation() == exact_opcode::add){
        result = {exact_value(0)};
        for(size_t i = 0; i < expression.operand_count(); ++i){
            integration_poly term;
            if(!integration_parse_poly(expression.operand(i), variable, term))
                return false;
            result = integration_add(result, term);
        }
        return true;
    }
    if(expression.operation() == exact_opcode::multiply){
        result = {exact_value(1)};
        for(size_t i = 0; i < expression.operand_count(); ++i){
            integration_poly factor;
            if(!integration_parse_poly(expression.operand(i), variable, factor))
                return false;
            result = integration_mul(result, factor);
        }
        return true;
    }
    if(expression.operation() == exact_opcode::power){
        size_t exponent = 0;
        if(!integration_exponent(expression.operand(1), exponent) || exponent > 64)
            return false;
        integration_poly base;
        if(!integration_parse_poly(expression.operand(0), variable, base))
            return false;
        result = {exact_value(1)};
        while(exponent){
            if(exponent & 1) result = integration_mul(result, base);
            exponent >>= 1;
            if(exponent) base = integration_mul(base, base);
        }
        return true;
    }
    return false;
}

static exact_expr integration_poly_expr(exact_context &context,
                                        const integration_poly &poly,
                                        const exact_expr &variable){
    std::vector<exact_expr> terms;
    for(size_t i = 0; i < poly.size(); ++i){
        if(poly[i].is_zero()) continue;
        exact_expr term = context.value(poly[i]);
        if(i) term = term * (i == 1 ? variable :
            context.power(variable, context.integer(i)));
        terms.push_back(term);
    }
    return terms.empty() ? context.integer(0) : context.add(terms);
}

static bool integration_divide_poly(integration_poly numerator,
                                    const integration_poly &denominator,
                                    integration_poly &quotient){
    if(denominator.empty() || denominator.back().is_zero()) return false;
    quotient.assign(numerator.size() >= denominator.size()
        ? numerator.size() - denominator.size() + 1 : 1, exact_value(0));
    while(numerator.size() >= denominator.size() &&
          !(numerator.size() == 1 && numerator[0].is_zero())){
        size_t shift = numerator.size() - denominator.size();
        exact_value scale = numerator.back() / denominator.back();
        quotient[shift] = quotient[shift] + scale;
        for(size_t i = 0; i < denominator.size(); ++i)
            numerator[i + shift] = numerator[i + shift] -
                                   scale * denominator[i];
        integration_trim(numerator);
    }
    integration_trim(quotient);
    return numerator.size() == 1 && numerator[0].is_zero();
}

static bool integration_divmod_poly(integration_poly numerator,
                                    const integration_poly &denominator,
                                    integration_poly &quotient,
                                    integration_poly &remainder){
    if(denominator.empty() || denominator.back().is_zero()) return false;
    quotient.assign(numerator.size() >= denominator.size()
        ? numerator.size() - denominator.size() + 1 : 1, exact_value(0));
    while(numerator.size() >= denominator.size() &&
          !(numerator.size() == 1 && numerator[0].is_zero())){
        size_t shift = numerator.size() - denominator.size();
        exact_value scale = numerator.back() / denominator.back();
        quotient[shift] = quotient[shift] + scale;
        for(size_t i = 0; i < denominator.size(); ++i)
            numerator[i + shift] = numerator[i + shift] -
                                   scale * denominator[i];
        integration_trim(numerator);
    }
    integration_trim(quotient);
    remainder = std::move(numerator);
    return true;
}

static bool integration_signed_exponent(const exact_expr &value,
                                        int64_t &result){
    if(!value.is_value() || !value.value().is_integer()) return false;
    exact_value exact = value.value();
    const precz_t &integer = exact.integer();
    if(integer.magnitude().rsiz > 1 ||
       (integer.magnitude().rsiz &&
        integer.magnitude().a[0] > (uint64_t)INT64_MAX)) return false;
    result = integer.magnitude().rsiz ?
        (int64_t)integer.magnitude().a[0] : 0;
    if(integer.is_negative()) result = -result;
    return true;
}

static integration_poly integration_pow_poly(integration_poly base,
                                             size_t exponent){
    integration_poly result{exact_value(1)};
    while(exponent){
        if(exponent & 1) result = integration_mul(result, base);
        exponent >>= 1;
        if(exponent) base = integration_mul(base, base);
    }
    return result;
}

static bool integration_parse_rational(const exact_expr &expression,
                                       const exact_expr &variable,
                                       integration_poly &numerator,
                                       integration_poly &denominator){
    if(integration_parse_poly(expression, variable, numerator)){
        denominator = {exact_value(1)};
        return true;
    }
    if(expression.operation() == exact_opcode::multiply){
        numerator = {exact_value(1)};
        denominator = {exact_value(1)};
        for(size_t i = 0; i < expression.operand_count(); ++i){
            integration_poly child_numerator, child_denominator;
            if(!integration_parse_rational(expression.operand(i), variable,
                                           child_numerator,
                                           child_denominator)) return false;
            numerator = integration_mul(numerator, child_numerator);
            denominator = integration_mul(denominator, child_denominator);
        }
        return true;
    }
    if(expression.operation() == exact_opcode::add){
        numerator = {exact_value(0)};
        denominator = {exact_value(1)};
        for(size_t i = 0; i < expression.operand_count(); ++i){
            integration_poly child_numerator, child_denominator;
            if(!integration_parse_rational(expression.operand(i), variable,
                                           child_numerator,
                                           child_denominator)) return false;
            numerator = integration_add(
                integration_mul(numerator, child_denominator),
                integration_mul(child_numerator, denominator));
            denominator = integration_mul(denominator, child_denominator);
        }
        return true;
    }
    if(expression.operation() == exact_opcode::power){
        int64_t exponent = 0;
        integration_poly base_numerator, base_denominator;
        if(!integration_signed_exponent(expression.operand(1), exponent) ||
           exponent < -32 || exponent > 32 ||
           !integration_parse_rational(expression.operand(0), variable,
                                       base_numerator, base_denominator))
            return false;
        if(exponent == 0){
            numerator = {exact_value(1)};
            denominator = {exact_value(1)};
        }else if(exponent > 0){
            numerator = integration_pow_poly(base_numerator, (size_t)exponent);
            denominator = integration_pow_poly(base_denominator, (size_t)exponent);
        }else{
            numerator = integration_pow_poly(base_denominator, (size_t)-exponent);
            denominator = integration_pow_poly(base_numerator, (size_t)-exponent);
        }
        return true;
    }
    return false;
}

static void integration_factor_list(const exact_expr &expression,
                                    std::vector<exact_expr> &factors){
    if(expression.operation() == exact_opcode::multiply){
        for(size_t i = 0; i < expression.operand_count(); ++i)
            integration_factor_list(expression.operand(i), factors);
    }else factors.push_back(expression);
}

struct integration_factor{
    integration_poly polynomial;
    size_t multiplicity;
};

static exact_expr integration_squarefree_rational(
    exact_context &context, const integration_poly &numerator,
    const exact_expr &denominator,
    const exact_expr &variable){
    integration_poly denominator_poly;
    if(!integration_parse_poly(denominator, variable, denominator_poly) ||
       denominator_poly.size() < 2) return exact_expr();

    exact_expr factored = context.factor(denominator);
    std::vector<exact_expr> factor_exprs;
    integration_factor_list(factored, factor_exprs);
    std::vector<integration_factor> factors;
    for(const exact_expr &factor_expr : factor_exprs){
        exact_expr base = factor_expr;
        size_t multiplicity = 1;
        if(factor_expr.operation() == exact_opcode::power){
            if(!integration_exponent(factor_expr.operand(1), multiplicity) ||
               multiplicity < 2 || multiplicity > 32) return exact_expr();
            base = factor_expr.operand(0);
        }
        integration_poly factor;
        if(!integration_parse_poly(base, variable, factor))
            return exact_expr();
        if(factor.size() == 1) continue;
        if(factor.size() > 3) return exact_expr();
        factors.push_back({std::move(factor), multiplicity});
    }
    if(factors.empty()) return exact_expr();
    size_t unknowns = 0;
    for(const integration_factor &factor : factors)
        unknowns += (factor.polynomial.size() - 1) * factor.multiplicity;
    if(unknowns + 1 != denominator_poly.size()) return exact_expr();

    std::vector<std::vector<exact_value>> matrix(
        unknowns, std::vector<exact_value>(unknowns + 1, exact_value(0)));
    size_t column = 0;
    for(const integration_factor &entry : factors){
        integration_poly divisor{exact_value(1)};
        for(size_t order = 1; order <= entry.multiplicity; ++order){
            divisor = integration_mul(divisor, entry.polynomial);
            integration_poly cofactor;
            if(!integration_divide_poly(denominator_poly, divisor, cofactor))
                return exact_expr();
            for(size_t power = 0; power + 1 < entry.polynomial.size();
                ++power, ++column)
                for(size_t degree = 0; degree < cofactor.size(); ++degree)
                    matrix[degree + power][column] =
                        matrix[degree + power][column] + cofactor[degree];
        }
    }
    for(size_t degree = 0; degree < numerator.size(); ++degree)
        matrix[degree][unknowns] = numerator[degree];
    for(size_t pivot = 0; pivot < unknowns; ++pivot){
        size_t row = pivot;
        while(row < unknowns && matrix[row][pivot].is_zero()) ++row;
        if(row == unknowns) return exact_expr();
        if(row != pivot) std::swap(matrix[row], matrix[pivot]);
        exact_value divisor = matrix[pivot][pivot];
        for(size_t j = pivot; j <= unknowns; ++j)
            matrix[pivot][j] = matrix[pivot][j] / divisor;
        for(size_t i = 0; i < unknowns; ++i){
            if(i == pivot || matrix[i][pivot].is_zero()) continue;
            exact_value scale = matrix[i][pivot];
            for(size_t j = pivot; j <= unknowns; ++j)
                matrix[i][j] = matrix[i][j] - scale * matrix[pivot][j];
        }
    }

    exact_expr result = context.integer(0);
    column = 0;
    for(const integration_factor &entry : factors){
        const integration_poly &factor = entry.polynomial;
        size_t degree = factor.size() - 1;
        exact_expr factor_expression =
            integration_poly_expr(context, factor, variable);
        for(size_t order = 1; order <= entry.multiplicity; ++order){
            if(degree == 1){
                exact_value numerator = matrix[column++][unknowns];
                if(order == 1){
                    result = result + context.value(numerator / factor[1]) *
                        context.natural_logarithm(
                            context.absolute_value(factor_expression));
                }else{
                    exact_value coefficient = numerator /
                        (factor[1] * exact_value(1 - (int64_t)order));
                    result = result + context.value(coefficient) *
                        context.power(factor_expression,
                                      context.integer(1 - (int64_t)order));
                }
                continue;
            }
            exact_value constant = matrix[column++][unknowns];
            exact_value linear = matrix[column++][unknowns];
            exact_value alpha = linear / (exact_value(2) * factor[2]);
            exact_value residual = constant - alpha * factor[1];
            if(order == 1){
                result = result + context.value(alpha) *
                    context.natural_logarithm(
                        context.absolute_value(factor_expression));
            }else{
                result = result + context.value(
                    alpha / exact_value(1 - (int64_t)order)) *
                    context.power(factor_expression,
                                  context.integer(1 - (int64_t)order));
            }
            exact_value discriminant = exact_value(4) * factor[2] * factor[0] -
                                       factor[1] * factor[1];
            if(discriminant.is_zero()) return exact_expr();
            exact_expr linear_term = context.value(exact_value(2) * factor[2]) *
                                     variable + context.value(factor[1]);
            exact_expr j;
            if(!discriminant.is_negative()){
                exact_expr root = context.square_root(context.value(discriminant));
                j = context.integer(2) * context.arc_tangent(linear_term / root) /
                    root;
            }else{
                exact_expr root = context.square_root(context.value(-discriminant));
                j = context.natural_logarithm(context.absolute_value(
                    (linear_term - root) / (linear_term + root))) / root;
            }
            for(size_t k = 2; k <= order; ++k){
                exact_expr boundary = linear_term /
                    (context.value(exact_value((uint64_t)k - 1) * discriminant) *
                     context.power(factor_expression, context.integer(k - 1)));
                exact_value recurrence = exact_value(2) * factor[2] *
                    exact_value((uint64_t)(2 * k - 3)) /
                    (exact_value((uint64_t)k - 1) * discriminant);
                j = boundary + context.value(recurrence) * j;
            }
            result = result + context.value(residual) * j;
        }
    }
    return result;
}

static exact_expr integration_rational_antiderivative(
    exact_context &context, const exact_expr &expression,
    const exact_expr &variable){
    integration_poly numerator, denominator;
    if(!integration_parse_rational(expression, variable,
                                   numerator, denominator)) return exact_expr();
    integration_poly quotient, remainder;
    if(!integration_divmod_poly(numerator, denominator,
                               quotient, remainder)) return exact_expr();

    exact_expr polynomial_part = context.integer(0);
    for(size_t degree = 0; degree < quotient.size(); ++degree){
        if(quotient[degree].is_zero()) continue;
        exact_value coefficient = quotient[degree] /
                                  exact_value((uint64_t)degree + 1);
        polynomial_part = polynomial_part + context.value(coefficient) *
            context.power(variable, context.integer(degree + 1));
    }
    if(remainder.size() == 1 && remainder[0].is_zero())
        return polynomial_part;

    exact_expr denominator_expression =
        integration_poly_expr(context, denominator, variable);
    exact_expr proper = integration_squarefree_rational(
        context, remainder, denominator_expression, variable);
    if(!proper.valid()) return exact_expr();
    return polynomial_part + proper;
}

static integration_poly integration_derivative_poly(
    const integration_poly &source){
    if(source.size() <= 1) return {exact_value(0)};
    integration_poly result(source.size() - 1, exact_value(0));
    for(size_t i = 1; i < source.size(); ++i)
        result[i - 1] = source[i] * exact_value((uint64_t)i);
    integration_trim(result);
    return result;
}

static bool integration_depends_on(const exact_expr &expression,
                                   const exact_expr &variable){
    if(expression == variable) return true;
    for(size_t i = 0; i < expression.operand_count(); ++i)
        if(integration_depends_on(expression.operand(i), variable)) return true;
    return false;
}

// The polynomial solvers work over rational coefficients.  Keep arbitrary
// expressions independent of the integration variable outside that solver;
// they are constants of the differential field (pi, sqrt(pi), parameters,
// and so on).
static exact_expr integration_extract_constants(
    exact_context &context, const exact_expr &cofactor,
    const exact_expr &variable, exact_expr &constant){
    std::vector<exact_expr> constants, dependent;
    if(cofactor.operation() == exact_opcode::multiply){
        for(size_t i = 0; i < cofactor.operand_count(); ++i){
            exact_expr factor = cofactor.operand(i);
            (integration_depends_on(factor, variable) ? dependent : constants)
                .push_back(factor);
        }
    }else if(integration_depends_on(cofactor, variable)){
        dependent.push_back(cofactor);
    }else{
        constants.push_back(cofactor);
    }
    constant = constants.empty() ? context.integer(1) :
        context.multiply(constants);
    return dependent.empty() ? context.integer(1) : context.multiply(dependent);
}

static exact_expr integration_hyperexponential_polynomial(
    exact_context &context, const exact_expr &cofactor,
    const exact_expr &inner, const exact_expr &variable){
    integration_poly p, g;
    exact_expr constant;
    exact_expr polynomial_cofactor = integration_extract_constants(
        context, cofactor, variable, constant);
    if(!integration_parse_poly(polynomial_cofactor, variable, p) ||
       !integration_parse_poly(inner, variable, g)) return exact_expr();
    integration_poly dg = integration_derivative_poly(g);
    if(dg.size() == 1 && dg[0].is_zero()) return exact_expr();
    size_t degree_p = p.size() - 1;
    size_t degree_dg = dg.size() - 1;
    size_t degree_r;
    if(degree_dg == 0) degree_r = degree_p;
    else{
        if(degree_p < degree_dg) return exact_expr();
        degree_r = degree_p - degree_dg;
    }
    size_t columns = degree_r + 1;
    size_t rows = std::max(degree_r ? degree_r : 0,
                           degree_r + degree_dg) + 1;
    rows = std::max(rows, p.size());
    std::vector<std::vector<exact_value>> matrix(
        rows, std::vector<exact_value>(columns + 1, exact_value(0)));
    for(size_t column = 0; column < columns; ++column){
        if(column) matrix[column - 1][column] =
            matrix[column - 1][column] + exact_value((uint64_t)column);
        for(size_t j = 0; j < dg.size(); ++j)
            matrix[column + j][column] = matrix[column + j][column] + dg[j];
    }
    for(size_t i = 0; i < p.size(); ++i) matrix[i][columns] = p[i];

    size_t pivot_row = 0;
    std::vector<size_t> pivot_for_column(columns, SIZE_MAX);
    for(size_t column = 0; column < columns; ++column){
        size_t row = pivot_row;
        while(row < rows && matrix[row][column].is_zero()) ++row;
        if(row == rows) continue;
        if(row != pivot_row) std::swap(matrix[row], matrix[pivot_row]);
        exact_value pivot = matrix[pivot_row][column];
        for(size_t j = column; j <= columns; ++j)
            matrix[pivot_row][j] = matrix[pivot_row][j] / pivot;
        for(size_t i = 0; i < rows; ++i){
            if(i == pivot_row || matrix[i][column].is_zero()) continue;
            exact_value scale = matrix[i][column];
            for(size_t j = column; j <= columns; ++j)
                matrix[i][j] = matrix[i][j] - scale * matrix[pivot_row][j];
        }
        pivot_for_column[column] = pivot_row++;
    }
    for(size_t i = 0; i < rows; ++i){
        bool all_zero = true;
        for(size_t j = 0; j < columns; ++j)
            if(!matrix[i][j].is_zero()){ all_zero = false; break; }
        if(all_zero && !matrix[i][columns].is_zero()) return exact_expr();
    }
    integration_poly r(columns, exact_value(0));
    for(size_t column = 0; column < columns; ++column){
        if(pivot_for_column[column] == SIZE_MAX) return exact_expr();
        r[column] = matrix[pivot_for_column[column]][columns];
    }
    return constant * integration_poly_expr(context, r, variable) *
        context.exponential(inner);
}

// Hermite reduction in the quadratic exponential extension. For
// P(x)*exp(a*x^2+b*x+d), solve P = R' + (2*a*x+b)*R + k. The first two
// terms are d(R*exp(...))/dx; the one-dimensional residual k is integrated
// through erf or erfi after completing the square. This is a
// differential-algebra reduction, not a collection of power rules.
static exact_expr integration_quadratic_hyperexponential(
    exact_context &context, const exact_expr &cofactor,
    const exact_expr &inner, const exact_expr &variable){
    integration_poly p, g;
    exact_expr constant;
    exact_expr polynomial_cofactor = integration_extract_constants(
        context, cofactor, variable, constant);
    if(!integration_parse_poly(polynomial_cofactor, variable, p) ||
       !integration_parse_poly(inner, variable, g) ||
       g.size() != 3 || g[2].is_zero()) return exact_expr();

    const size_t degree_p = p.size() - 1;
    const size_t r_columns = degree_p;
    const size_t residual_column = r_columns;
    const size_t columns = r_columns + 1;
    const size_t rows = degree_p + 1;
    std::vector<std::vector<exact_value>> matrix(
        rows, std::vector<exact_value>(columns + 1, exact_value(0)));
    const exact_value twice_a = exact_value(2) * g[2];
    for(size_t column = 0; column < r_columns; ++column){
        if(column)
            matrix[column - 1][column] = matrix[column - 1][column] +
                exact_value((uint64_t)column);
        matrix[column][column] = matrix[column][column] + g[1];
        matrix[column + 1][column] = matrix[column + 1][column] + twice_a;
    }
    matrix[0][residual_column] = exact_value(1);
    for(size_t row = 0; row < p.size(); ++row)
        matrix[row][columns] = p[row];

    size_t pivot_row = 0;
    std::vector<size_t> pivot_for_column(columns, SIZE_MAX);
    for(size_t column = 0; column < columns; ++column){
        size_t row = pivot_row;
        while(row < rows && matrix[row][column].is_zero()) ++row;
        if(row == rows) continue;
        if(row != pivot_row) std::swap(matrix[row], matrix[pivot_row]);
        exact_value pivot = matrix[pivot_row][column];
        for(size_t j = column; j <= columns; ++j)
            matrix[pivot_row][j] = matrix[pivot_row][j] / pivot;
        for(size_t i = 0; i < rows; ++i){
            if(i == pivot_row || matrix[i][column].is_zero()) continue;
            exact_value scale = matrix[i][column];
            for(size_t j = column; j <= columns; ++j)
                matrix[i][j] = matrix[i][j] - scale * matrix[pivot_row][j];
        }
        pivot_for_column[column] = pivot_row++;
    }
    for(size_t row = 0; row < rows; ++row){
        bool empty = true;
        for(size_t column = 0; column < columns; ++column)
            if(!matrix[row][column].is_zero()){
                empty = false;
                break;
            }
        if(empty && !matrix[row][columns].is_zero()) return exact_expr();
    }
    for(size_t column = 0; column < columns; ++column)
        if(pivot_for_column[column] == SIZE_MAX) return exact_expr();

    integration_poly r(r_columns ? r_columns : 1, exact_value(0));
    for(size_t column = 0; column < r_columns; ++column)
        r[column] = matrix[pivot_for_column[column]][columns];
    exact_value residual = matrix[pivot_for_column[residual_column]][columns];
    exact_expr result = integration_poly_expr(context, r, variable) *
                        context.exponential(inner);
    if(residual.is_zero()) return constant * result;

    const bool negative = g[2].is_negative();
    exact_expr magnitude = context.value(negative ? -g[2] : g[2]);
    exact_expr root = context.square_root(magnitude);
    exact_expr shift = variable + context.value(g[1] /
        (exact_value(2) * g[2]));
    exact_value completed_constant = g[0] - g[1] * g[1] /
        (exact_value(4) * g[2]);
    exact_expr base = context.square_root(context.pi()) /
        (context.integer(2) * root);
    base = context.exponential(context.value(completed_constant)) * base;
    base = negative ? base * context.error_function(root * shift)
                    : base * context.imaginary_error_function(root * shift);
    return constant * (result + context.value(residual) * base);
}

// Algebraic Hermite base case for a reciprocal square root of a quadratic.
// Complete the square using L=2*a*x+b and D=4*a*c-b^2, then select a real
// inverse circular/hyperbolic primitive from the signs of a and D.
static exact_expr integration_quadratic_inverse_sqrt(
    exact_context &context, const exact_expr &radicand,
    const exact_expr &variable){
    integration_poly q;
    if(!integration_parse_poly(radicand, variable, q) || q.size() != 3 ||
       q[2].is_zero()) return exact_expr();
    const exact_value a = q[2];
    const exact_value discriminant = exact_value(4) * a * q[0] - q[1] * q[1];
    exact_expr linear = context.value(exact_value(2) * a) * variable +
        context.value(q[1]);
    if(a.is_negative()){
        if(!discriminant.is_negative()) return exact_expr();
        exact_expr root_a = context.square_root(context.value(-a));
        exact_expr root_discriminant = context.square_root(
            context.value(-discriminant));
        return context.arc_sine(-linear / root_discriminant) / root_a;
    }
    exact_expr root_a = context.square_root(context.value(a));
    if(!discriminant.is_negative() && !discriminant.is_zero()){
        exact_expr root_discriminant = context.square_root(
            context.value(discriminant));
        return context.inverse_hyperbolic_sine(linear / root_discriminant) /
            root_a;
    }
    if(discriminant.is_zero())
        return context.natural_logarithm(context.absolute_value(linear)) / root_a;
    exact_expr root_discriminant = context.square_root(context.value(-discriminant));
    return context.inverse_hyperbolic_cosine(linear / root_discriminant) /
        root_a;
}

// Hermite reduction in Q(x,sqrt(q)) for a quadratic q.  For a polynomial P,
// solve P = R'*q + R*q'/2 + k. The first two terms are the derivative of
// R*sqrt(q); k times the reciprocal-square-root primitive is the only
// remaining basis term.
static exact_expr integration_quadratic_root_polynomial(
    exact_context &context, const exact_expr &cofactor,
    const exact_expr &radicand, const exact_expr &variable){
    integration_poly p, q;
    if(!integration_parse_poly(cofactor, variable, p) ||
       !integration_parse_poly(radicand, variable, q) || q.size() != 3 ||
       q[2].is_zero()) return exact_expr();
    const size_t degree_p = p.size() - 1;
    const size_t r_columns = degree_p;
    const size_t residual_column = r_columns;
    const size_t columns = r_columns + 1;
    const size_t rows = degree_p + 1;
    std::vector<std::vector<exact_value>> matrix(
        rows, std::vector<exact_value>(columns + 1, exact_value(0)));
    for(size_t column = 0; column < r_columns; ++column){
        if(column){
            for(size_t j = 0; j < q.size(); ++j)
                matrix[column - 1 + j][column] =
                    matrix[column - 1 + j][column] +
                    exact_value((uint64_t)column) * q[j];
        }
        matrix[column][column] = matrix[column][column] + q[1] / exact_value(2);
        matrix[column + 1][column] = matrix[column + 1][column] + q[2];
    }
    matrix[0][residual_column] = exact_value(1);
    for(size_t row = 0; row < p.size(); ++row)
        matrix[row][columns] = p[row];

    size_t pivot_row = 0;
    std::vector<size_t> pivot_for_column(columns, SIZE_MAX);
    for(size_t column = 0; column < columns; ++column){
        size_t row = pivot_row;
        while(row < rows && matrix[row][column].is_zero()) ++row;
        if(row == rows) continue;
        if(row != pivot_row) std::swap(matrix[row], matrix[pivot_row]);
        exact_value pivot = matrix[pivot_row][column];
        for(size_t j = column; j <= columns; ++j)
            matrix[pivot_row][j] = matrix[pivot_row][j] / pivot;
        for(size_t i = 0; i < rows; ++i){
            if(i == pivot_row || matrix[i][column].is_zero()) continue;
            exact_value scale = matrix[i][column];
            for(size_t j = column; j <= columns; ++j)
                matrix[i][j] = matrix[i][j] - scale * matrix[pivot_row][j];
        }
        pivot_for_column[column] = pivot_row++;
    }
    for(size_t column = 0; column < columns; ++column)
        if(pivot_for_column[column] == SIZE_MAX) return exact_expr();

    integration_poly r(r_columns ? r_columns : 1, exact_value(0));
    for(size_t column = 0; column < r_columns; ++column)
        r[column] = matrix[pivot_for_column[column]][columns];
    exact_value residual = matrix[pivot_for_column[residual_column]][columns];
    exact_expr result = integration_poly_expr(context, r, variable) *
        context.square_root(radicand);
    if(residual.is_zero()) return result;
    exact_expr base = integration_quadratic_inverse_sqrt(
        context, radicand, variable);
    return base.valid() ? result + context.value(residual) * base : exact_expr();
}

// In the exponential differential fields generated by exp(+-(a*x+b)), write
// an antiderivative as A(x)*f(g) + B(x)*h(g), where (f,h) is either
// (sin,cos) or (sinh,cosh). Matching derivatives gives a finite rational
// linear system for A and B, covering every polynomial cofactor without a
// table of integration-by-parts identities.
static exact_expr integration_linear_function_polynomial(
    exact_context &context, const exact_expr &cofactor,
    const exact_expr &inner, const exact_expr &variable,
    exact_opcode operation){
    integration_poly p, g;
    if(!integration_parse_poly(cofactor, variable, p) ||
       !integration_parse_poly(inner, variable, g) || g.size() != 2 ||
       g[1].is_zero() ||
       (operation != exact_opcode::sine && operation != exact_opcode::cosine &&
        operation != exact_opcode::hyperbolic_sine &&
        operation != exact_opcode::hyperbolic_cosine)) return exact_expr();
    const bool circular = operation == exact_opcode::sine ||
                          operation == exact_opcode::cosine;
    const bool first = operation == exact_opcode::sine ||
                       operation == exact_opcode::hyperbolic_sine;
    const size_t degree = p.size() - 1;
    const size_t polynomial_size = degree + 1;
    const size_t columns = polynomial_size * 2;
    const size_t rows = columns;
    std::vector<std::vector<exact_value>> matrix(
        rows, std::vector<exact_value>(columns + 1, exact_value(0)));
    const exact_value a = g[1];
    for(size_t degree_r = 0; degree_r < polynomial_size; ++degree_r){
        const size_t a_column = degree_r;
        const size_t b_column = polynomial_size + degree_r;
        // Coefficient of sin(g) or sinh(g): A' - a*B for circular
        // functions, and A' + a*B for hyperbolic functions.
        if(degree_r)
            matrix[degree_r - 1][a_column] =
                matrix[degree_r - 1][a_column] +
                exact_value((uint64_t)degree_r);
        matrix[degree_r][b_column] = circular
            ? matrix[degree_r][b_column] - a
            : matrix[degree_r][b_column] + a;
        // Coefficient of cos(g) or cosh(g): a*A + B'.
        matrix[polynomial_size + degree_r][a_column] =
            matrix[polynomial_size + degree_r][a_column] + a;
        if(degree_r)
            matrix[polynomial_size + degree_r - 1][b_column] =
                matrix[polynomial_size + degree_r - 1][b_column] +
                exact_value((uint64_t)degree_r);
    }
    for(size_t degree_r = 0; degree_r < p.size(); ++degree_r)
        matrix[(first ? 0 : polynomial_size) + degree_r][columns] =
            p[degree_r];

    size_t pivot_row = 0;
    std::vector<size_t> pivot_for_column(columns, SIZE_MAX);
    for(size_t column = 0; column < columns; ++column){
        size_t row = pivot_row;
        while(row < rows && matrix[row][column].is_zero()) ++row;
        if(row == rows) continue;
        if(row != pivot_row) std::swap(matrix[row], matrix[pivot_row]);
        exact_value pivot = matrix[pivot_row][column];
        for(size_t j = column; j <= columns; ++j)
            matrix[pivot_row][j] = matrix[pivot_row][j] / pivot;
        for(size_t i = 0; i < rows; ++i){
            if(i == pivot_row || matrix[i][column].is_zero()) continue;
            exact_value scale = matrix[i][column];
            for(size_t j = column; j <= columns; ++j)
                matrix[i][j] = matrix[i][j] - scale * matrix[pivot_row][j];
        }
        pivot_for_column[column] = pivot_row++;
    }
    for(size_t column = 0; column < columns; ++column)
        if(pivot_for_column[column] == SIZE_MAX) return exact_expr();

    integration_poly sine_coefficient(polynomial_size, exact_value(0));
    integration_poly cosine_coefficient(polynomial_size, exact_value(0));
    for(size_t degree_r = 0; degree_r < polynomial_size; ++degree_r){
        sine_coefficient[degree_r] =
            matrix[pivot_for_column[degree_r]][columns];
        cosine_coefficient[degree_r] = matrix[pivot_for_column[
            polynomial_size + degree_r]][columns];
    }
    exact_expr first_function = circular ? context.sine(inner)
                                         : context.hyperbolic_sine(inner);
    exact_expr second_function = circular ? context.cosine(inner)
                                          : context.hyperbolic_cosine(inner);
    return integration_poly_expr(context, sine_coefficient, variable) *
               first_function +
           integration_poly_expr(context, cosine_coefficient, variable) *
               second_function;
}

// Primitive with respect to the immediate argument.  The caller verifies the
// chain-rule condition cofactor / inner' is constant, so these identities
// apply to arbitrary nested inner expressions rather than only to x.
static exact_expr integration_unary_argument_primitive(
    exact_context &context, exact_opcode operation, const exact_expr &inner){
    if(operation == exact_opcode::exponential) return context.exponential(inner);
    if(operation == exact_opcode::sine) return -context.cosine(inner);
    if(operation == exact_opcode::cosine) return context.sine(inner);
    if(operation == exact_opcode::tangent)
        return -context.natural_logarithm(context.absolute_value(
            context.cosine(inner)));
    if(operation == exact_opcode::hyperbolic_sine)
        return context.hyperbolic_cosine(inner);
    if(operation == exact_opcode::hyperbolic_cosine)
        return context.hyperbolic_sine(inner);
    if(operation == exact_opcode::hyperbolic_tangent)
        return context.natural_logarithm(context.hyperbolic_cosine(inner));
    if(operation == exact_opcode::natural_logarithm)
        return inner * context.natural_logarithm(inner) - inner;
    if(operation == exact_opcode::logarithm_base_2)
        return (inner * context.natural_logarithm(inner) - inner) /
            context.natural_logarithm(context.integer(2));
    if(operation == exact_opcode::logarithm_base_10)
        return (inner * context.natural_logarithm(inner) - inner) /
            context.natural_logarithm(context.integer(10));
    if(operation == exact_opcode::error_function)
        return inner * context.error_function(inner) +
            context.exponential(-context.power(inner, context.integer(2))) /
            context.square_root(context.pi());
    if(operation == exact_opcode::imaginary_error_function)
        return inner * context.imaginary_error_function(inner) -
            context.exponential(context.power(inner, context.integer(2))) /
            context.square_root(context.pi());
    if(operation == exact_opcode::sine_integral)
        return inner * context.sine_integral(inner) + context.cosine(inner);
    if(operation == exact_opcode::cosine_integral)
        return inner * context.cosine_integral(inner) - context.sine(inner);
    if(operation == exact_opcode::exponential_integral)
        return inner * context.exponential_integral(inner) -
            context.exponential(inner);
    return exact_expr();
}

static exact_expr integration_polynomial_primitive(
    exact_context &context, const integration_poly &polynomial,
    const exact_expr &variable){
    exact_expr result = context.integer(0);
    for(size_t degree = 0; degree < polynomial.size(); ++degree){
        if(polynomial[degree].is_zero()) continue;
        exact_value coefficient = polynomial[degree] /
                                  exact_value((uint64_t)degree + 1);
        result = result + context.value(coefficient) *
            context.power(variable, context.integer(degree + 1));
    }
    return result;
}

static exact_expr integration_logarithmic_polynomial(
    exact_context &context, const exact_expr &cofactor,
    const exact_expr &inner, const exact_expr &variable){
    integration_poly polynomial;
    if(!integration_parse_poly(cofactor, variable, polynomial))
        return exact_expr();
    integration_poly inner_polynomial;
    if(!integration_parse_poly(inner, variable, inner_polynomial))
        return exact_expr();
    exact_expr primitive = integration_polynomial_primitive(
        context, polynomial, variable);
    exact_expr derivative_inner = integration_poly_expr(
        context, integration_derivative_poly(inner_polynomial), variable);
    exact_expr remainder_integrand = primitive * derivative_inner / inner;
    exact_expr remainder = integration_rational_antiderivative(
        context, remainder_integrand, variable);
    if(!remainder.valid()) return exact_expr();
    return primitive * context.natural_logarithm(inner) - remainder;
}

// Reduction of a logarithmic monomial in a differential tower.  Integration
// by parts lowers the log exponent on every recursive call:
// int(P*L^n) = A*L^n - n*int(A*q'/q*L^(n-1)), where A'=P and L=log(q).
static exact_expr integration_logarithmic_polynomial_power(
    exact_context &context, const exact_expr &cofactor,
    const exact_expr &inner, size_t exponent, const exact_expr &variable){
    if(exponent == 0 || exponent > 64) return exact_expr();
    integration_poly polynomial, inner_polynomial;
    if(!integration_parse_poly(cofactor, variable, polynomial) ||
       !integration_parse_poly(inner, variable, inner_polynomial))
        return exact_expr();
    exact_expr primitive = integration_polynomial_primitive(
        context, polynomial, variable);
    exact_expr logarithm = context.natural_logarithm(inner);
    exact_expr lower_power = exponent == 1 ? context.integer(1) :
        context.power(logarithm, context.integer(exponent - 1));
    exact_expr derivative_inner = integration_poly_expr(
        context, integration_derivative_poly(inner_polynomial), variable);
    exact_expr remainder_integrand = context.integer(exponent) * primitive *
        derivative_inner * lower_power / inner;
    exact_expr remainder = context.integrate(remainder_integrand, variable);
    if(!remainder.valid() || remainder.operation() == exact_opcode::integral)
        return exact_expr();
    return primitive * context.power(logarithm, context.integer(exponent)) -
        remainder;
}

// A generic reduction for polynomial multiples of a known unary extension.
// If A'=P, integration by parts changes int(P*F) into A*F-int(A*F').  The
// recursive integral has one fewer occurrence of F and can be handled by the
// rational, exponential, trigonometric, or special-function layers.
static exact_expr integration_polynomial_function_by_parts(
    exact_context &context, const exact_expr &cofactor,
    const exact_expr &function, const exact_expr &variable){
    integration_poly polynomial;
    if(!integration_parse_poly(cofactor, variable, polynomial))
        return exact_expr();
    exact_expr primitive = integration_polynomial_primitive(
        context, polynomial, variable);
    exact_expr remainder = context.integrate(
        primitive * context.differentiate(function, variable), variable);
    if(!remainder.valid() || remainder.operation() == exact_opcode::integral)
        return exact_expr();
    return primitive * function - remainder;
}

} // namespace

exact_expr exact_context::integrate(const exact_expr &expression,
                                    const exact_expr &variable){
    if(!expression.valid() || !variable.valid() ||
       expression.storage_ != storage_ || variable.storage_ != storage_ ||
       storage_->node(variable.root_).op != exact_opcode::symbol)
        throw std::invalid_argument(
            "integrate requires an expression and a symbol in one context");
    std::unordered_map<uint32_t, bool> dependency_memo;
    auto depends = [&](auto &&self, uint32_t id) -> bool{
        if(id == variable.root_) return true;
        auto cached = dependency_memo.find(id);
        if(cached != dependency_memo.end()) return cached->second;
        const exact_node &node = storage_->node(id);
        const uint32_t *args = storage_->children(node);
        bool result = false;
        for(size_t i = 0; i < node.operand_count; ++i)
            if(self(self, args[i])){ result = true; break; }
        dependency_memo.emplace(id, result);
        return result;
    };
    auto unresolved = [&](uint32_t id){
        return exact_expr(storage_, storage_->intern_compound(
            exact_opcode::integral, {id, variable.root_}));
    };
    auto constant_ratio = [&](const exact_expr &numerator,
                              const exact_expr &denominator,
                              exact_expr &ratio){
        if(denominator.is_value() && denominator.value().is_zero()) return false;
        ratio = simplify(numerator / denominator);
        return !depends(depends, ratio.root_);
    };
    std::unordered_map<uint32_t, exact_expr> memo;
    std::function<exact_expr(uint32_t)> antiderivative = [&](uint32_t id){
        auto cached = memo.find(id);
        if(cached != memo.end()) return cached->second;
        // Antiderivatives also intern nodes, so storage references cannot be
        // held across recursive differentiation or integration calls.
        exact_node node = storage_->node(id);
        const uint32_t *child_data = storage_->children(node);
        std::vector<uint32_t> args(child_data,
                                   child_data + node.operand_count);
        exact_expr source(storage_, id), result;
        // Special-function kernels.  These are kept before rational
        // integration because the denominator is the integration variable,
        // while the numerator is transcendental rather than a polynomial.
        exact_expr multiplied_by_variable = simplify(source * variable);
        if(multiplied_by_variable == sine(variable)){
            result = sine_integral(variable);
        }else if(multiplied_by_variable == cosine(variable)){
            result = cosine_integral(variable);
        }else if(multiplied_by_variable == exponential(variable)){
            result = exponential_integral(variable);
        }else if(simplify(source * natural_logarithm(variable)) == integer(1)){
            // li(x) is represented through Ei(log(x)); this keeps the
            // existing special-function vocabulary instead of adding a
            // second node for the logarithmic integral.
            result = exponential_integral(natural_logarithm(variable));
        }
        if(!result.valid() && node.op == exact_opcode::exponential){
            // exp(c*x^2) is the first non-elementary hyperexponential
            // extension.  Detect it through f'/x = 2c, then verify f=c*x^2
            // before selecting erf (c<0) or erfi (otherwise).
            exact_expr inner(storage_, args[0]), slope, coefficient;
            if(constant_ratio(differentiate(inner, variable), variable, slope)){
                coefficient = simplify(slope / integer(2));
                exact_expr remainder = simplify(inner - coefficient *
                    power(variable, integer(2)));
                if(remainder == integer(0) && coefficient != integer(0)){
                    bool negative = coefficient.is_value() &&
                        coefficient.value().is_negative();
                    exact_expr magnitude = negative ? -coefficient : coefficient;
                    exact_expr root = square_root(magnitude);
                    exact_expr scale = square_root(pi()) /
                        (integer(2) * root);
                    result = negative ? scale * error_function(root * variable)
                                      : scale * imaginary_error_function(root * variable);
                }
            }
        }
        if(!result.valid()){
            // Rational functions of one elementary generator belong to a
            // simple differential extension.  For t = exp(u), tan(u), or
            // tanh(u), divide by respectively u'*t, u'*(1+t^2), or
            // u'*(1-t^2), integrate rationally, then restore t. The rational
            // parser rejects any expression with x or another generator left.
            std::vector<uint32_t> generator_nodes;
            std::unordered_map<uint32_t, bool> generator_seen;
            std::function<void(uint32_t)> find_generators = [&](uint32_t current){
                if(!generator_seen.emplace(current, true).second) return;
                exact_node current_node = storage_->node(current);
                if(current_node.op == exact_opcode::exponential ||
                   current_node.op == exact_opcode::tangent ||
                   current_node.op == exact_opcode::hyperbolic_tangent)
                    generator_nodes.push_back(current);
                const uint32_t *children = storage_->children(current_node);
                for(size_t i = 0; i < current_node.operand_count; ++i)
                    find_generators(children[i]);
            };
            find_generators(id);
            for(uint32_t generator_id : generator_nodes){
                exact_expr generator(storage_, generator_id);
                exact_expr inner = generator.operand(0);
                exact_expr derivative_inner = differentiate(inner, variable);
                if(depends(depends, derivative_inner.root_) ||
                   (derivative_inner.is_value() &&
                    derivative_inner.value().is_zero())) continue;

                exact_expr temporary;
                for(size_t suffix = 0;; ++suffix){
                    temporary = symbol("_risch_exp_" + std::to_string(suffix));
                    std::unordered_map<uint32_t, bool> contains_memo;
                    std::function<bool(uint32_t)> contains_t = [&](uint32_t current){
                        if(current == temporary.root_) return true;
                        auto cached = contains_memo.find(current);
                        if(cached != contains_memo.end()) return cached->second;
                        exact_node current_node = storage_->node(current);
                        const uint32_t *children = storage_->children(current_node);
                        bool found = false;
                        for(size_t i = 0; i < current_node.operand_count; ++i)
                            if(contains_t(children[i])){ found = true; break; }
                        contains_memo.emplace(current, found);
                        return found;
                    };
                    if(!contains_t(id)) break;
                }
                exact_expr transformed = substitute(source, generator, temporary);
                exact_expr jacobian;
                if(generator.operation() == exact_opcode::exponential)
                    jacobian = temporary;
                else if(generator.operation() == exact_opcode::tangent)
                    jacobian = integer(1) + power(temporary, integer(2));
                else jacobian = integer(1) - power(temporary, integer(2));
                exact_expr rational_primitive = integration_rational_antiderivative(
                    *this, transformed / jacobian, temporary);
                if(!rational_primitive.valid()) continue;
                result = substitute(rational_primitive, temporary, generator) /
                    derivative_inner;
                break;
            }
        }
        bool elementary_logarithmic = false;
        if(!result.valid() && node.op == exact_opcode::multiply){
            for(size_t i = 0; i < node.operand_count; ++i){
                exact_expr factor(storage_, args[i]);
                if(factor.operation() != exact_opcode::power ||
                   factor.operand(1) != integer(-1)) continue;
                exact_expr base = factor.operand(0), ratio;
                if(constant_ratio(source,
                                  differentiate(base, variable) / base, ratio)){
                    elementary_logarithmic = true;
                    break;
                }
            }
        }
        if(!result.valid() && !elementary_logarithmic &&
           node.op != exact_opcode::sine && node.op != exact_opcode::cosine){
            // Weierstrass substitution for the circular elementary
            // extension. With t = tan(u/2), sin(u)=2t/(1+t^2),
            // cos(u)=(1-t^2)/(1+t^2), and du=2dt/(1+t^2). This handles a
            // rational expression in sin(u) and cos(u) as one object.
            std::vector<uint32_t> circular_nodes;
            std::unordered_map<uint32_t, bool> circular_seen;
            std::function<void(uint32_t)> find_circular = [&](uint32_t current){
                if(!circular_seen.emplace(current, true).second) return;
                exact_node current_node = storage_->node(current);
                if(current_node.op == exact_opcode::sine ||
                   current_node.op == exact_opcode::cosine)
                    circular_nodes.push_back(current);
                const uint32_t *children = storage_->children(current_node);
                for(size_t i = 0; i < current_node.operand_count; ++i)
                    find_circular(children[i]);
            };
            find_circular(id);
            for(uint32_t circular_id : circular_nodes){
                exact_expr circular(storage_, circular_id);
                exact_expr inner = circular.operand(0);
                exact_expr derivative_inner = differentiate(inner, variable);
                if(depends(depends, derivative_inner.root_) ||
                   (derivative_inner.is_value() &&
                    derivative_inner.value().is_zero())) continue;

                exact_expr temporary;
                for(size_t suffix = 0;; ++suffix){
                    temporary = symbol("_risch_trig_" + std::to_string(suffix));
                    std::unordered_map<uint32_t, bool> contains_memo;
                    std::function<bool(uint32_t)> contains_t = [&](uint32_t current){
                        if(current == temporary.root_) return true;
                        auto cached = contains_memo.find(current);
                        if(cached != contains_memo.end()) return cached->second;
                        exact_node current_node = storage_->node(current);
                        const uint32_t *children = storage_->children(current_node);
                        bool found = false;
                        for(size_t i = 0; i < current_node.operand_count; ++i)
                            if(contains_t(children[i])){ found = true; break; }
                        contains_memo.emplace(current, found);
                        return found;
                    };
                    if(!contains_t(id)) break;
                }
                exact_expr denominator = integer(1) + power(temporary, integer(2));
                exact_expr sine_inner = sine(inner);
                exact_expr cosine_inner = cosine(inner);
                exact_expr transformed = substitute(source, sine_inner,
                    integer(2) * temporary / denominator);
                transformed = substitute(transformed, cosine_inner,
                    (integer(1) - power(temporary, integer(2))) / denominator);
                exact_expr rational_primitive = integration_rational_antiderivative(
                    *this, integer(2) * transformed / denominator, temporary);
                if(!rational_primitive.valid()) continue;
                result = substitute(rational_primitive, temporary,
                                    tangent(inner / integer(2))) /
                    derivative_inner;
                break;
            }
        }
        if(!result.valid() && !elementary_logarithmic &&
           node.op != exact_opcode::hyperbolic_sine &&
           node.op != exact_opcode::hyperbolic_cosine){
            // Hyperbolic Weierstrass substitution. With t = tanh(u/2),
            // sinh(u)=2t/(1-t^2), cosh(u)=(1+t^2)/(1-t^2), and
            // du=2dt/(1-t^2), so rational functions in one sinh/cosh pair
            // reduce to the rational integration layer as well.
            std::vector<uint32_t> hyperbolic_nodes;
            std::unordered_map<uint32_t, bool> hyperbolic_seen;
            std::function<void(uint32_t)> find_hyperbolic = [&](uint32_t current){
                if(!hyperbolic_seen.emplace(current, true).second) return;
                exact_node current_node = storage_->node(current);
                if(current_node.op == exact_opcode::hyperbolic_sine ||
                   current_node.op == exact_opcode::hyperbolic_cosine)
                    hyperbolic_nodes.push_back(current);
                const uint32_t *children = storage_->children(current_node);
                for(size_t i = 0; i < current_node.operand_count; ++i)
                    find_hyperbolic(children[i]);
            };
            find_hyperbolic(id);
            for(uint32_t hyperbolic_id : hyperbolic_nodes){
                exact_expr hyperbolic(storage_, hyperbolic_id);
                exact_expr inner = hyperbolic.operand(0);
                exact_expr derivative_inner = differentiate(inner, variable);
                if(depends(depends, derivative_inner.root_) ||
                   (derivative_inner.is_value() &&
                    derivative_inner.value().is_zero())) continue;

                exact_expr temporary;
                for(size_t suffix = 0;; ++suffix){
                    temporary = symbol("_risch_hyperbolic_" +
                                       std::to_string(suffix));
                    std::unordered_map<uint32_t, bool> contains_memo;
                    std::function<bool(uint32_t)> contains_t = [&](uint32_t current){
                        if(current == temporary.root_) return true;
                        auto cached = contains_memo.find(current);
                        if(cached != contains_memo.end()) return cached->second;
                        exact_node current_node = storage_->node(current);
                        const uint32_t *children = storage_->children(current_node);
                        bool found = false;
                        for(size_t i = 0; i < current_node.operand_count; ++i)
                            if(contains_t(children[i])){ found = true; break; }
                        contains_memo.emplace(current, found);
                        return found;
                    };
                    if(!contains_t(id)) break;
                }
                exact_expr denominator = integer(1) - power(temporary, integer(2));
                exact_expr sinh_inner = hyperbolic_sine(inner);
                exact_expr cosh_inner = hyperbolic_cosine(inner);
                exact_expr transformed = substitute(source, sinh_inner,
                    integer(2) * temporary / denominator);
                transformed = substitute(transformed, cosh_inner,
                    (integer(1) + power(temporary, integer(2))) / denominator);
                exact_expr rational_primitive = integration_rational_antiderivative(
                    *this, integer(2) * transformed / denominator, temporary);
                if(!rational_primitive.valid()) continue;
                result = substitute(rational_primitive, temporary,
                                    hyperbolic_tangent(inner / integer(2))) /
                    derivative_inner;
                break;
            }
        }
        exact_expr rational = depends(depends, id)
            ? integration_rational_antiderivative(*this, source, variable)
            : exact_expr();
        if(result.valid()){
            // A recognized special-function primitive has priority.
        }else if(!depends(depends, id)){
            result = source * variable;
        }else if(rational.valid()){
            result = rational;
        }else if(id == variable.root_){
            result = power(variable, integer(2)) / integer(2);
        }else if(node.op == exact_opcode::add){
            std::vector<exact_expr> terms;
            terms.reserve(node.operand_count);
            bool failed = false;
            for(size_t i = 0; i < node.operand_count; ++i){
                exact_expr term = antiderivative(args[i]);
                if(term.operation() == exact_opcode::integral) failed = true;
                terms.push_back(term);
            }
            result = failed ? unresolved(id) : add(terms);
        }else if(node.op == exact_opcode::multiply){
            // Risch tower kernels: c*f'*exp(f), c*f'/f, and
            // c*f'/f*ln(f)^n. The quotient test makes these structural
            // differential-field rules rather than expression templates.
            bool tower_integrated = false;
            for(size_t i = 0; i < node.operand_count && !tower_integrated; ++i){
                exact_expr factor(storage_, args[i]);
                if(factor.operation() != exact_opcode::power ||
                   factor.operand(1) != integer(-1) ||
                   factor.operand(0).operation() != exact_opcode::square_root)
                    continue;
                exact_expr radicand = factor.operand(0).operand(0);
                exact_expr cofactor = simplify(source / factor);
                exact_expr primitive = integration_quadratic_root_polynomial(
                    *this, cofactor, radicand, variable);
                if(primitive.valid()){
                    result = primitive;
                    tower_integrated = true;
                }
            }
            for(size_t i = 0; i < node.operand_count && !tower_integrated; ++i){
                exact_expr factor(storage_, args[i]);
                if(!exact_unary_function(factor.operation())) continue;
                exact_expr inner = factor.operand(0);
                exact_expr primitive = integration_unary_argument_primitive(
                    *this, factor.operation(), inner);
                if(!primitive.valid()) continue;
                exact_expr ratio;
                if(constant_ratio(source / factor,
                                  differentiate(inner, variable), ratio)){
                    result = ratio * primitive;
                    tower_integrated = true;
                }
            }
            // Liouvillian special-function extensions use the same
            // logarithmic-derivative test: f'(x)/f(x).  Thus this handles
            // Si(u), Ci(u), and Ei(u) for an arbitrary differentiable inner
            // u, rather than recognizing only the spelling u == x.
            for(size_t i = 0; i < node.operand_count && !tower_integrated; ++i){
                exact_expr factor(storage_, args[i]);
                exact_opcode operation = factor.operation();
                if(operation != exact_opcode::sine &&
                   operation != exact_opcode::cosine &&
                   operation != exact_opcode::exponential) continue;
                exact_expr inner = factor.operand(0);
                exact_expr logarithmic_derivative =
                    differentiate(inner, variable) / inner;
                exact_expr ratio;
                if(constant_ratio(source / factor, logarithmic_derivative,
                                  ratio)){
                    if(operation == exact_opcode::sine)
                        result = ratio * sine_integral(inner);
                    else if(operation == exact_opcode::cosine)
                        result = ratio * cosine_integral(inner);
                    else result = ratio * exponential_integral(inner);
                    tower_integrated = true;
                }
                for(size_t j = 0; j < node.operand_count && !tower_integrated; ++j){
                    if(operation == exact_opcode::exponential) break;
                    exact_expr denominator_factor(storage_, args[j]);
                    if(denominator_factor.operation() != exact_opcode::power ||
                       denominator_factor.operand(1) != integer(-1)) continue;
                    exact_expr denominator = denominator_factor.operand(0);
                    exact_expr shift = simplify(inner - denominator);
                    if(depends(depends, shift.root_)) continue;
                    if(!constant_ratio(source / factor,
                                       differentiate(denominator, variable) /
                                       denominator, ratio)) continue;
                    if(operation == exact_opcode::sine){
                        result = ratio * (cosine(shift) *
                            sine_integral(denominator) + sine(shift) *
                            cosine_integral(denominator));
                    }else{
                        result = ratio * (cosine(shift) *
                            cosine_integral(denominator) - sine(shift) *
                            sine_integral(denominator));
                    }
                    tower_integrated = true;
                }
            }
            for(size_t i = 0; i < node.operand_count && !tower_integrated; ++i){
                exact_expr factor(storage_, args[i]);
                if(factor.operation() != exact_opcode::sine &&
                   factor.operation() != exact_opcode::cosine &&
                   factor.operation() != exact_opcode::hyperbolic_sine &&
                   factor.operation() != exact_opcode::hyperbolic_cosine)
                    continue;
                exact_expr solution = integration_linear_function_polynomial(
                    *this, simplify(source / factor), factor.operand(0),
                    variable, factor.operation());
                if(solution.valid()){
                    result = solution;
                    tower_integrated = true;
                }
            }
            for(size_t i = 0; i < node.operand_count && !tower_integrated; ++i){
                exact_expr factor(storage_, args[i]);
                exact_expr inner, exponential_factor;
                if(factor.operation() == exact_opcode::exponential){
                    inner = factor.operand(0);
                    exponential_factor = factor;
                }else if(factor.operation() == exact_opcode::power &&
                         factor.operand(0).operation() == exact_opcode::constant_e){
                    // The parser stores e^u as a power node, but it is the
                    // same exponential differential generator as exp(u).
                    inner = factor.operand(1);
                    exponential_factor = exponential(inner);
                }else continue;
                exact_expr derivative_inner = differentiate(inner, variable);
                exact_expr ratio;
                if(!depends(depends, derivative_inner.root_) &&
                   !derivative_inner.is_value()) continue;
                for(size_t j = 0; j < node.operand_count && !tower_integrated; ++j){
                    exact_expr denominator_factor(storage_, args[j]);
                    if(denominator_factor.operation() != exact_opcode::power ||
                       denominator_factor.operand(1) != integer(-1)) continue;
                    exact_expr denominator = denominator_factor.operand(0);
                    exact_expr shift = simplify(inner - denominator);
                    if(depends(depends, shift.root_)) continue;
                    if(constant_ratio(source / factor,
                                      differentiate(denominator, variable) /
                                      denominator, ratio)){
                        // exp(inner)/denominator has an Ei primitive when
                        // inner = denominator + constant.
                        result = ratio * exponential(shift) *
                            exponential_integral(denominator);
                        tower_integrated = true;
                    }
                }
                if(tower_integrated) break;
                if(constant_ratio(source / factor, derivative_inner, ratio)){
                    result = ratio * factor;
                    tower_integrated = true;
                }else{
                    exact_expr polynomial_solution =
                        integration_hyperexponential_polynomial(
                            *this, simplify(source / factor), inner, variable);
                    if(polynomial_solution.valid()){
                        result = substitute(polynomial_solution,
                                            exponential_factor, factor);
                        tower_integrated = true;
                    }else{
                        exact_expr reduced_solution =
                            integration_quadratic_hyperexponential(
                                *this, simplify(source / factor), inner,
                                variable);
                        if(reduced_solution.valid()){
                            result = substitute(reduced_solution,
                                                exponential_factor, factor);
                            tower_integrated = true;
                        }
                    }
                }
            }
            for(size_t i = 0; i < node.operand_count && !tower_integrated; ++i){
                exact_expr factor(storage_, args[i]);
                if(factor.operation() != exact_opcode::power ||
                   factor.operand(1) != integer(-1)) continue;
                exact_expr base = factor.operand(0);
                exact_expr derivative_base = differentiate(base, variable);
                exact_expr ratio;
                if(constant_ratio(source, derivative_base / base, ratio)){
                    result = ratio * natural_logarithm(absolute_value(base));
                    tower_integrated = true;
                }
            }
            for(size_t i = 0; i < node.operand_count && !tower_integrated; ++i){
                exact_expr factor(storage_, args[i]), logarithm, exponent;
                if(factor.operation() == exact_opcode::natural_logarithm){
                    logarithm = factor;
                    exponent = integer(1);
                }else if(factor.operation() == exact_opcode::power &&
                         factor.operand(0).operation() ==
                             exact_opcode::natural_logarithm &&
                         !depends(depends, factor.operand(1).root_)){
                    logarithm = factor.operand(0);
                    exponent = factor.operand(1);
                }else continue;
                exact_expr base = logarithm.operand(0);
                exact_expr derivative_base = differentiate(base, variable);
                exact_expr ratio;
                if(constant_ratio(source / factor,
                                  derivative_base / base, ratio)){
                    exact_expr next = exponent + integer(1);
                    if(next != integer(0)){
                        result = ratio * power(logarithm, next) / next;
                        tower_integrated = true;
                    }
                }else{
                    size_t logarithm_power = 0;
                    if(!integration_exponent(exponent, logarithm_power) ||
                       logarithm_power == 0) continue;
                    exact_expr next = exponent + integer(1);
                    if(constant_ratio(source / factor, derivative_base, ratio) &&
                       next != integer(0)){
                        result = ratio * power(logarithm, next) / next;
                        tower_integrated = true;
                    }else{
                        exact_expr by_parts =
                            integration_logarithmic_polynomial_power(
                                *this, simplify(source / factor), base,
                                logarithm_power, variable);
                        if(by_parts.valid()){
                            result = by_parts;
                            tower_integrated = true;
                        }
                    }
                }
            }
            for(size_t i = 0; i < node.operand_count && !tower_integrated; ++i){
                exact_expr factor(storage_, args[i]);
                switch(factor.operation()){
                case exact_opcode::arc_sine:
                case exact_opcode::arc_cosine:
                case exact_opcode::arc_tangent:
                case exact_opcode::inverse_hyperbolic_sine:
                case exact_opcode::inverse_hyperbolic_cosine:
                case exact_opcode::inverse_hyperbolic_tangent:
                case exact_opcode::sine_integral:
                case exact_opcode::cosine_integral:
                case exact_opcode::exponential_integral:
                case exact_opcode::error_function:
                case exact_opcode::imaginary_error_function:
                    break;
                default:
                    continue;
                }
                exact_expr by_parts = integration_polynomial_function_by_parts(
                    *this, simplify(source / factor), factor, variable);
                if(by_parts.valid()){
                    result = by_parts;
                    tower_integrated = true;
                }
            }
            if(tower_integrated){
                memo.emplace(id, result);
                return result;
            }
            std::vector<exact_expr> constants, dependent;
            for(size_t i = 0; i < node.operand_count; ++i)
                (depends(depends, args[i]) ? dependent : constants)
                    .push_back(exact_expr(storage_, args[i]));
            if(dependent.size() == 1){
                exact_expr inner = antiderivative(dependent[0].root_);
                result = inner.operation() == exact_opcode::integral
                    ? unresolved(id) : multiply(constants) * inner;
            }else result = unresolved(id);
        }else if(node.op == exact_opcode::power){
            exact_expr base(storage_, args[0]), exponent(storage_, args[1]);
            if(exponent == integer(-1) &&
               base.operation() == exact_opcode::square_root)
                result = integration_quadratic_inverse_sqrt(
                    *this, base.operand(0), variable);
            else if(exponent == integer(-1) / integer(2))
                result = integration_quadratic_inverse_sqrt(
                    *this, base, variable);
            if(!result.valid() && !depends(depends, args[1])){
                exact_expr db = differentiate(base, variable);
                if(!depends(depends, db.root_)){
                    if(exponent == integer(-1))
                        result = natural_logarithm(absolute_value(base)) / db;
                    else{
                        exact_expr next = exponent + integer(1);
                        result = power(base, next) / (next * db);
                    }
                }else result = unresolved(id);
            }else if(!result.valid() && !depends(depends, args[0])){
                exact_expr de = differentiate(exponent, variable);
                result = depends(depends, de.root_)
                    ? unresolved(id)
                    : power(base, exponent) /
                      (de * natural_logarithm(base));
            }else if(!result.valid()){
                result = unresolved(id);
            }
        }else if(exact_unary_function(node.op)){
            exact_expr inner(storage_, args[0]);
            exact_expr di = differentiate(inner, variable);
            exact_expr logarithmic_by_parts;
            if(node.op == exact_opcode::natural_logarithm)
                logarithmic_by_parts = integration_logarithmic_polynomial(
                    *this, integer(1), inner, variable);
            if(logarithmic_by_parts.valid()){
                result = logarithmic_by_parts;
            }else if(depends(depends, di.root_)){
                result = unresolved(id);
            }else if(node.op == exact_opcode::exponential)
                result = exponential(inner) / di;
            else if(node.op == exact_opcode::sine)
                result = -cosine(inner) / di;
            else if(node.op == exact_opcode::cosine)
                result = sine(inner) / di;
            else if(node.op == exact_opcode::tangent)
                result = -natural_logarithm(absolute_value(cosine(inner))) / di;
            else if(node.op == exact_opcode::hyperbolic_sine)
                result = hyperbolic_cosine(inner) / di;
            else if(node.op == exact_opcode::hyperbolic_cosine)
                result = hyperbolic_sine(inner) / di;
            else if(node.op == exact_opcode::hyperbolic_tangent)
                result = natural_logarithm(hyperbolic_cosine(inner)) / di;
            else if(node.op == exact_opcode::natural_logarithm)
                result = (inner * natural_logarithm(inner) - inner) / di;
            else if(node.op == exact_opcode::logarithm_base_2)
                result = (inner * natural_logarithm(inner) - inner) /
                         (di * natural_logarithm(integer(2)));
            else if(node.op == exact_opcode::logarithm_base_10)
                result = (inner * natural_logarithm(inner) - inner) /
                         (di * natural_logarithm(integer(10)));
            else if(node.op == exact_opcode::arc_sine)
                result = (inner * arc_sine(inner) +
                          square_root(integer(1) - power(inner, integer(2)))) / di;
            else if(node.op == exact_opcode::arc_cosine)
                result = (inner * arc_cosine(inner) -
                          square_root(integer(1) - power(inner, integer(2)))) / di;
            else if(node.op == exact_opcode::arc_tangent)
                result = (inner * arc_tangent(inner) -
                          natural_logarithm(integer(1) + power(inner, integer(2))) /
                          integer(2)) / di;
            else if(node.op == exact_opcode::inverse_hyperbolic_sine)
                result = (inner * inverse_hyperbolic_sine(inner) -
                          square_root(power(inner, integer(2)) + integer(1))) / di;
            else if(node.op == exact_opcode::inverse_hyperbolic_cosine)
                result = (inner * inverse_hyperbolic_cosine(inner) -
                          square_root(inner - integer(1)) *
                          square_root(inner + integer(1))) / di;
            else if(node.op == exact_opcode::inverse_hyperbolic_tangent)
                result = (inner * inverse_hyperbolic_tangent(inner) +
                          natural_logarithm(integer(1) - power(inner, integer(2))) /
                          integer(2)) / di;
            else if(node.op == exact_opcode::sine_integral)
                result = (inner * sine_integral(inner) + cosine(inner)) / di;
            else if(node.op == exact_opcode::cosine_integral)
                result = (inner * cosine_integral(inner) - sine(inner)) / di;
            else if(node.op == exact_opcode::exponential_integral)
                result = (inner * exponential_integral(inner) -
                          exponential(inner)) / di;
            else if(node.op == exact_opcode::error_function)
                result = (inner * error_function(inner) +
                          exponential(-power(inner, integer(2))) /
                          square_root(pi())) / di;
            else if(node.op == exact_opcode::imaginary_error_function)
                result = (inner * imaginary_error_function(inner) -
                          exponential(power(inner, integer(2))) /
                          square_root(pi())) / di;
            else result = unresolved(id);
        }else result = unresolved(id);
        memo.emplace(id, result);
        return result;
    };
    exact_expr expanded = expand(expression, 100000);
    return simplify(antiderivative(expanded.root_));
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
    bool full_factorization_;
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
                                    uint32_t &denominator_result,
                                    uint32_t *common_result = nullptr){
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
        if(!gcd(numerator, denominator, common, 0)) return false;
        make_monic(common);
        if(common_result) *common_result = multivariate_expression(common);
        if(is_unit(common)) return common_result != nullptr;
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

    void combine_double_angle_product(std::vector<uint32_t> &factors){
        size_t coefficient = SIZE_MAX;
        int coefficient_sign = 0;
        for(size_t i = 0; i < factors.size(); ++i){
            exact_node current = storage_.node(factors[i]);
            if(current.op != exact_opcode::value) continue;
            const exact_value &value = storage_.values[current.payload];
            if(value == exact_value(2)){
                coefficient = i;
                coefficient_sign = 1;
            }else if(value == exact_value(-2)){
                coefficient = i;
                coefficient_sign = -1;
            }
            break;
        }
        if(coefficient == SIZE_MAX) return;

        for(size_t sine = 0; sine < factors.size(); ++sine){
            exact_node sine_node = storage_.node(factors[sine]);
            if(sine_node.op != exact_opcode::sine) continue;
            for(size_t cosine = 0; cosine < factors.size(); ++cosine){
                exact_node cosine_node = storage_.node(factors[cosine]);
                if(cosine_node.op != exact_opcode::cosine ||
                   storage_.children(sine_node)[0] !=
                   storage_.children(cosine_node)[0]) continue;
                uint32_t argument = storage_.children(sine_node)[0];
                uint32_t doubled = storage_.make_multiply({
                    storage_.intern_value(exact_value(2)), argument});
                uint32_t replacement = storage_.make_function(
                    exact_opcode::sine, doubled);
                std::vector<uint32_t> reduced;
                reduced.reserve(factors.size() - 1);
                for(size_t i = 0; i < factors.size(); ++i)
                    if(i != coefficient && i != sine && i != cosine)
                        reduced.push_back(factors[i]);
                if(coefficient_sign < 0)
                    reduced.push_back(storage_.intern_value(exact_value(-1)));
                reduced.push_back(replacement);
                factors = std::move(reduced);
                return;
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
        if(symbolic.empty()){
            base = storage_.intern_value(exact_value(1));
            exponent = 1;
        }else{
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
        }
        sign = coefficient.is_negative() ? -1 : 1;
        if(sign < 0) coefficient = -coefficient;
        if(coefficient == exact_value(1)) return true;

        // Absorb any exact nth-power coefficient into the symbolic base, so
        // one rule handles scaled differences of squares, cubes, fifths, etc.
        exact_value root_value;
        if(!exact_nth_root(coefficient, exponent, root_value)) return false;
        uint32_t root = storage_.intern_value(std::move(root_value));
        base = storage_.make_multiply({root, base});
        return true;
    }

    uint32_t factor_difference_of_powers(const std::vector<uint32_t> &terms){
        if(terms.size() != 2) return UINT32_MAX;
        int sign_a = 0, sign_b = 0;
        uint32_t base_a = 0, base_b = 0;
        uint64_t exponent_a = 0, exponent_b = 0;
        if(!signed_power(terms[0], sign_a, base_a, exponent_a) ||
           !signed_power(terms[1], sign_b, base_b, exponent_b) ||
           sign_a == sign_b) return UINT32_MAX;
        bool a_is_one = storage_.node(base_a).op == exact_opcode::value &&
            storage_.values[storage_.node(base_a).payload].is_one();
        bool b_is_one = storage_.node(base_b).op == exact_opcode::value &&
            storage_.values[storage_.node(base_b).payload].is_one();
        if(a_is_one && exponent_a == 1) exponent_a = exponent_b;
        if(b_is_one && exponent_b == 1) exponent_b = exponent_a;
        if(exponent_a != exponent_b || exponent_a < 2 ||
           exponent_a > 4096) return UINT32_MAX;
        if(sign_a < 0){
            std::swap(sign_a, sign_b);
            std::swap(base_a, base_b);
            std::swap(a_is_one, b_is_one);
        }
        if(b_is_one && storage_.node(base_a).op == exact_opcode::symbol){
            using integer_polynomial = std::vector<precz_t>;
            std::unordered_map<uint64_t, integer_polynomial> cyclotomic_cache;
            auto cyclotomic = [&](auto &&self, uint64_t n) -> integer_polynomial{
                auto cached = cyclotomic_cache.find(n);
                if(cached != cyclotomic_cache.end()) return cached->second;
                integer_polynomial result((size_t)n + 1, precz_t(0));
                result[0] = precz_t(-1);
                result[(size_t)n] = precz_t(1);
                for(uint64_t divisor = 1; divisor < n; ++divisor){
                    if(n % divisor) continue;
                    integer_polynomial factor = self(self, divisor);
                    integer_polynomial dividend = std::move(result);
                    integer_polynomial quotient(
                        dividend.size() - factor.size() + 1, precz_t(0));
                    while(dividend.size() >= factor.size()){
                        size_t degree = dividend.size() - factor.size();
                        precz_t coefficient = dividend.back() / factor.back();
                        quotient[degree] += coefficient;
                        for(size_t i = 0; i < factor.size(); ++i)
                            dividend[i + degree] -= coefficient * factor[i];
                        while(!dividend.empty() && dividend.back().is_zero())
                            dividend.pop_back();
                    }
                    if(!dividend.empty())
                        throw std::logic_error("inexact cyclotomic division");
                    result = std::move(quotient);
                }
                cyclotomic_cache.emplace(n, result);
                return result;
            };
            std::vector<uint32_t> cyclotomic_factors;
            for(uint64_t divisor = 1; divisor <= exponent_a; ++divisor){
                if(exponent_a % divisor) continue;
                integer_polynomial coefficients = cyclotomic(cyclotomic, divisor);
                polynomial expression;
                for(size_t degree = 0; degree < coefficients.size(); ++degree)
                    if(!coefficients[degree].is_zero())
                        expression.emplace(degree,
                                           exact_value(coefficients[degree]));
                cyclotomic_factors.push_back(
                    polynomial_expression(expression, base_a));
            }
            return storage_.make_multiply(std::move(cyclotomic_factors));
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

    uint32_t trigonometric_power_identity(const std::vector<uint32_t> &terms){
        if(terms.size() != 2) return UINT32_MAX;
        uint32_t base_a = 0, base_b = 0;
        uint64_t exponent_a = 0, exponent_b = 0;
        exact_value coefficient_a(1), coefficient_b(1);
        auto coefficient_power = [&](uint32_t term, exact_value &coefficient,
                                     uint32_t &base, uint64_t &exponent){
            std::vector<uint32_t> symbolic;
            exact_node current = storage_.node(term);
            if(current.op == exact_opcode::multiply){
                const uint32_t *args = storage_.children(current);
                for(size_t i = 0; i < current.operand_count; ++i){
                    exact_node factor = storage_.node(args[i]);
                    if(factor.op == exact_opcode::value)
                        coefficient = coefficient *
                            storage_.values[factor.payload];
                    else
                        symbolic.push_back(args[i]);
                }
            }else{
                symbolic.push_back(term);
            }
            if(symbolic.size() != 1) return false;
            base = symbolic[0];
            exponent = 1;
            exact_node power = storage_.node(base);
            if(power.op != exact_opcode::power) return true;
            const uint32_t *args = storage_.children(power);
            exact_node exponent_node = storage_.node(args[1]);
            int64_t integer_exponent = 0;
            if(exponent_node.op != exact_opcode::value ||
               !integer_i64(storage_.values[exponent_node.payload],
                            integer_exponent) || integer_exponent <= 0)
                return false;
            base = args[0];
            exponent = (uint64_t)integer_exponent;
            return true;
        };
        if(!coefficient_power(terms[0], coefficient_a, base_a, exponent_a) ||
           !coefficient_power(terms[1], coefficient_b, base_b, exponent_b) ||
           exponent_a != exponent_b) return UINT32_MAX;

        exact_node function_a = storage_.node(base_a);
        exact_node function_b = storage_.node(base_b);
        bool sine_cosine =
            function_a.op == exact_opcode::sine &&
            function_b.op == exact_opcode::cosine;
        bool cosine_sine =
            function_a.op == exact_opcode::cosine &&
            function_b.op == exact_opcode::sine;
        if((!sine_cosine && !cosine_sine) ||
           storage_.children(function_a)[0] != storage_.children(function_b)[0])
            return UINT32_MAX;

        // sin(u)^2 + cos(u)^2 = 1.  For fourth powers, factor through
        // (sin(u)^2 + cos(u)^2) before normal expansion can undo the gain.
        if(exponent_a == 2 && coefficient_a == coefficient_b)
            return storage_.intern_value(std::move(coefficient_a));
        if(exponent_a == 4 && coefficient_a == -coefficient_b){
            uint32_t two = storage_.intern_value(exact_value(2));
            uint32_t square_a = storage_.make_power(base_a, two);
            uint32_t square_b = storage_.make_power(base_b, two);
            uint32_t minus_one = storage_.intern_value(exact_value(-1));
            uint32_t difference = storage_.make_add({
                square_a, storage_.make_multiply({minus_one, square_b})});
            return storage_.make_multiply({
                storage_.intern_value(std::move(coefficient_a)), difference});
        }
        return UINT32_MAX;
    }

    uint32_t factor_rational_roots(uint32_t expression){
        uint32_t variable = UINT32_MAX;
        polynomial source;
        if(!parse_polynomial(expression, variable, source) ||
           variable == UINT32_MAX || source.empty() ||
           source.rbegin()->first < 2) return UINT32_MAX;

        size_t degree = source.rbegin()->first;
        std::vector<exact_value> coefficients(degree + 1, exact_value(0));
        for(const auto &entry : source){
            if(!entry.second.is_integer()) return UINT32_MAX;
            coefficients[entry.first] = entry.second;
        }
        int64_t leading = 0, constant = 0;
        if(!integer_i64(coefficients.back(), leading) ||
           !integer_i64(coefficients.front(), constant) || leading == 0)
            return UINT32_MAX;
        uint64_t leading_abs = leading < 0
            ? (uint64_t)0 - (uint64_t)leading : (uint64_t)leading;
        uint64_t constant_abs = constant < 0
            ? (uint64_t)0 - (uint64_t)constant : (uint64_t)constant;
        // Divisor enumeration is a fast path. Large endpoint coefficients are
        // left for the modular/Hensel stage instead of causing a long scan.
        if(leading_abs > 1000000 || constant_abs > 1000000)
            return UINT32_MAX;

        auto divisors = [](uint64_t value){
            std::vector<uint64_t> result;
            if(value == 0){ result.push_back(0); return result; }
            for(uint64_t divisor = 1; divisor <= value / divisor; ++divisor){
                if(value % divisor) continue;
                result.push_back(divisor);
                if(divisor != value / divisor) result.push_back(value / divisor);
            }
            std::sort(result.begin(), result.end());
            return result;
        };
        std::vector<uint64_t> numerators = divisors(constant_abs);
        std::vector<uint64_t> denominators = divisors(leading_abs);
        std::vector<uint32_t> factors;

        auto divide_at_root = [&](const exact_value &root) -> bool{
            size_t n = coefficients.size() - 1;
            std::vector<exact_value> quotient(n, exact_value(0));
            quotient[n - 1] = coefficients[n];
            for(size_t index = n - 1; index > 0; --index)
                quotient[index - 1] = coefficients[index] +
                                      root * quotient[index];
            exact_value remainder = coefficients[0] + root * quotient[0];
            if(!remainder.is_zero()) return false;
            coefficients = std::move(quotient);
            while(coefficients.size() > 1 && coefficients.back().is_zero())
                coefficients.pop_back();
            return true;
        };

        for(uint64_t numerator : numerators){
            for(uint64_t denominator : denominators){
                if(denominator == 0) continue;
                precq_t positive{precn_t(numerator), precn_t(denominator)};
                const exact_value candidates[] = {
                    exact_value(positive), exact_value(-positive)};
                for(const exact_value &root : candidates){
                    while(coefficients.size() > 1 && divide_at_root(root)){
                        uint32_t negative_root = storage_.intern_value(-root);
                        factors.push_back(storage_.make_add({variable,
                                                            negative_root}));
                    }
                }
            }
        }
        if(factors.empty()) return UINT32_MAX;
        polynomial remainder;
        for(size_t exponent = 0; exponent < coefficients.size(); ++exponent)
            if(!coefficients[exponent].is_zero())
                remainder.emplace(exponent, coefficients[exponent]);
        if(remainder.size() != 1 || remainder.begin()->first != 0 ||
           !remainder.begin()->second.is_one())
            factors.push_back(polynomial_expression(remainder, variable));
        return storage_.make_multiply(std::move(factors));
    }

    uint32_t factor_square_free(uint32_t expression){
        uint32_t variable = UINT32_MAX;
        polynomial parsed;
        if(!parse_polynomial(expression, variable, parsed) ||
           variable == UINT32_MAX || parsed.empty() ||
           parsed.rbegin()->first < 2) return UINT32_MAX;
        using dense_polynomial = std::vector<exact_value>;
        dense_polynomial source(parsed.rbegin()->first + 1, exact_value(0));
        for(const auto &entry : parsed){
            if(entry.second.is_approximate()) return UINT32_MAX;
            int64_t small_coefficient = 0;
            if(!integer_i64(entry.second, small_coefficient) ||
               small_coefficient < -32 || small_coefficient > 32)
                return UINT32_MAX;
            source[entry.first] = entry.second;
        }
        auto trim = [](dense_polynomial &value){
            while(value.size() > 1 && value.back().is_zero()) value.pop_back();
        };
        auto is_one = [](const dense_polynomial &value){
            return value.size() == 1 && value[0].is_one();
        };
        auto monic = [&](dense_polynomial value){
            trim(value);
            exact_value lead = value.back();
            for(exact_value &coefficient : value)
                coefficient = coefficient / lead;
            return value;
        };
        auto divmod = [&](dense_polynomial dividend,
                          const dense_polynomial &divisor,
                          dense_polynomial &quotient,
                          dense_polynomial &remainder){
            trim(dividend);
            if(divisor.empty() || divisor.back().is_zero()) return false;
            if(dividend.size() < divisor.size()){
                quotient.assign(1, exact_value(0));
                remainder = std::move(dividend);
                return true;
            }
            quotient.assign(dividend.size() - divisor.size() + 1,
                            exact_value(0));
            while(dividend.size() >= divisor.size() &&
                  !(dividend.size() == 1 && dividend[0].is_zero())){
                size_t degree = dividend.size() - divisor.size();
                exact_value coefficient = dividend.back() / divisor.back();
                quotient[degree] = quotient[degree] + coefficient;
                for(size_t i = 0; i < divisor.size(); ++i)
                    dividend[i + degree] = dividend[i + degree] -
                                           coefficient * divisor[i];
                trim(dividend);
            }
            trim(quotient);
            remainder = std::move(dividend);
            return true;
        };
        auto exact_quotient = [&](const dense_polynomial &a,
                                  const dense_polynomial &b,
                                  dense_polynomial &quotient){
            dense_polynomial remainder;
            if(!divmod(a, b, quotient, remainder)) return false;
            return remainder.size() == 1 && remainder[0].is_zero();
        };
        auto polynomial_gcd = [&](dense_polynomial a, dense_polynomial b){
            trim(a);
            trim(b);
            while(!(b.size() == 1 && b[0].is_zero())){
                dense_polynomial quotient, remainder;
                divmod(a, b, quotient, remainder);
                a = std::move(b);
                b = std::move(remainder);
            }
            return monic(std::move(a));
        };
        dense_polynomial derivative(source.size() - 1, exact_value(0));
        for(size_t exponent = 1; exponent < source.size(); ++exponent)
            derivative[exponent - 1] = source[exponent] *
                                       exact_value((uint64_t)exponent);
        dense_polynomial repeated = polynomial_gcd(source, derivative);
        if(is_one(repeated)) return UINT32_MAX;
        dense_polynomial remaining;
        if(!exact_quotient(source, repeated, remaining)) return UINT32_MAX;
        std::vector<uint32_t> factors;
        for(uint64_t multiplicity = 1; !is_one(remaining); ++multiplicity){
            if(multiplicity > source.size()) return UINT32_MAX;
            dense_polynomial shared = polynomial_gcd(remaining, repeated);
            dense_polynomial factor;
            if(!exact_quotient(remaining, shared, factor)) return UINT32_MAX;
            if(!is_one(factor)){
                polynomial sparse;
                for(size_t exponent = 0; exponent < factor.size(); ++exponent)
                    if(!factor[exponent].is_zero())
                        sparse.emplace(exponent, factor[exponent]);
                uint32_t factor_id = polynomial_expression(sparse, variable);
                uint32_t rational = factor_rational_roots(factor_id);
                if(rational != UINT32_MAX) factor_id = rational;
                // Square-free decomposition can leave a repeated composite
                // factor behind.  Factor that component as well; otherwise a
                // product such as (x + 1)^2*(x^2 + 1)^2 stops at the quartic.
                uint32_t quartic = factor_monic_quartic(factor_id);
                if(quartic != UINT32_MAX) factor_id = quartic;
                if(multiplicity != 1)
                    factor_id = storage_.make_power(factor_id,
                        storage_.intern_value(exact_value(multiplicity)));
                factors.push_back(factor_id);
            }
            remaining = std::move(shared);
            dense_polynomial next_repeated;
            if(!exact_quotient(repeated, remaining, next_repeated))
                return UINT32_MAX;
            repeated = std::move(next_repeated);
        }
        if(factors.empty()) return UINT32_MAX;
        return storage_.make_multiply(std::move(factors));
    }

    uint32_t factor_monic_quartic(uint32_t expression){
        uint32_t variable = UINT32_MAX;
        polynomial parsed;
        if(!parse_polynomial(expression, variable, parsed) ||
           variable == UINT32_MAX || parsed.empty() ||
           parsed.rbegin()->first != 4) return UINT32_MAX;
        int64_t coefficient[5] = {0, 0, 0, 0, 0};
        for(const auto &entry : parsed)
            if(!integer_i64(entry.second, coefficient[entry.first]))
                return UINT32_MAX;
        if(coefficient[4] != 1) return UINT32_MAX;

        auto signed_divisors = [](int64_t value){
            std::vector<int64_t> result;
            uint64_t magnitude = value < 0
                ? (uint64_t)0 - (uint64_t)value : (uint64_t)value;
            if(magnitude == 0){ result.push_back(0); return result; }
            for(uint64_t divisor = 1; divisor <= magnitude / divisor; ++divisor){
                if(magnitude % divisor) continue;
                uint64_t pair = magnitude / divisor;
                if(divisor <= (uint64_t)INT64_MAX){
                    result.push_back((int64_t)divisor);
                    result.push_back(-(int64_t)divisor);
                }
                if(pair != divisor && pair <= (uint64_t)INT64_MAX){
                    result.push_back((int64_t)pair);
                    result.push_back(-(int64_t)pair);
                }
            }
            return result;
        };
        auto make_quadratic = [&](int64_t linear, int64_t constant){
            std::vector<uint32_t> terms;
            terms.push_back(storage_.make_power(variable,
                storage_.intern_value(exact_value(2))));
            if(linear)
                terms.push_back(storage_.make_multiply({
                    storage_.intern_value(exact_value(linear)), variable}));
            if(constant)
                terms.push_back(storage_.intern_value(exact_value(constant)));
            return storage_.make_add(std::move(terms));
        };
        auto accept = [&](int64_t a, int64_t b, int64_t c, int64_t d){
            if(a + c != coefficient[3] ||
               a * c + b + d != coefficient[2] ||
               a * d + b * c != coefficient[1] ||
               b * d != coefficient[0]) return UINT32_MAX;
            return storage_.make_multiply({make_quadratic(a, b),
                                           make_quadratic(c, d)});
        };

        std::vector<int64_t> constants = signed_divisors(coefficient[0]);
        for(int64_t b : constants){
            if(b == 0 && coefficient[0] != 0) continue;
            int64_t d = b == 0 ? 0 : coefficient[0] / b;
            if(b != 0 && b * d != coefficient[0]) continue;
            if(d != b){
                int64_t numerator = coefficient[1] - coefficient[3] * b;
                int64_t denominator = d - b;
                if(numerator % denominator) continue;
                int64_t a = numerator / denominator;
                uint32_t result = accept(a, b, coefficient[3] - a, d);
                if(result != UINT32_MAX) return result;
                continue;
            }
            if(coefficient[1] != coefficient[3] * b) continue;
            int64_t product = coefficient[2] - b - d;
            int64_t discriminant = coefficient[3] * coefficient[3] -
                                   4 * product;
            if(discriminant < 0) continue;
            uint64_t root = (uint64_t)std::sqrt((long double)discriminant);
            while((root + 1) <= (uint64_t)INT64_MAX /
                                  std::max<uint64_t>(root + 1, 1) &&
                  (root + 1) * (root + 1) <= (uint64_t)discriminant) ++root;
            while(root * root > (uint64_t)discriminant) --root;
            if(root * root != (uint64_t)discriminant ||
               ((coefficient[3] + (int64_t)root) & 1)) continue;
            int64_t a = (coefficient[3] + (int64_t)root) / 2;
            uint32_t result = accept(a, b, coefficient[3] - a, d);
            if(result != UINT32_MAX) return result;
        }
        return UINT32_MAX;
    }

    uint32_t factor_modular_search(uint32_t expression){
        uint32_t variable = UINT32_MAX;
        polynomial parsed;
        if(!parse_polynomial(expression, variable, parsed) ||
           variable == UINT32_MAX || parsed.empty()) return UINT32_MAX;
        size_t degree = parsed.rbegin()->first;
        if(degree < 4 || degree > 24) return UINT32_MAX;
        std::vector<int64_t> source(degree + 1, 0);
        int64_t bound = 1;
        for(const auto &entry : parsed){
            if(!integer_i64(entry.second, source[entry.first]))
                return UINT32_MAX;
            uint64_t magnitude = source[entry.first] < 0
                ? (uint64_t)0 - (uint64_t)source[entry.first]
                : (uint64_t)source[entry.first];
            if(magnitude > 256) return UINT32_MAX;
            bound = std::max<int64_t>(bound, (int64_t)magnitude);
        }
        if(source.back() != 1) return UINT32_MAX;

        auto mod = [](int64_t value, int prime){
            int result = (int)(value % prime);
            return result < 0 ? result + prime : result;
        };
        auto trim_mod = [](std::vector<int> &value){
            while(value.size() > 1 && value.back() == 0) value.pop_back();
        };
        auto inverse_mod = [](int value, int prime){
            for(int inverse = 1; inverse < prime; ++inverse)
                if(value * inverse % prime == 1) return inverse;
            return 0;
        };
        auto divides_mod = [&](const std::vector<int> &divisor, int prime){
            std::vector<int> remainder(source.size());
            for(size_t i = 0; i < source.size(); ++i)
                remainder[i] = mod(source[i], prime);
            trim_mod(remainder);
            int inverse = inverse_mod(divisor.back(), prime);
            while(remainder.size() >= divisor.size()){
                size_t shift = remainder.size() - divisor.size();
                int coefficient = remainder.back() * inverse % prime;
                for(size_t i = 0; i < divisor.size(); ++i)
                    remainder[i + shift] = mod(remainder[i + shift] -
                                               coefficient * divisor[i], prime);
                trim_mod(remainder);
            }
            return remainder.size() == 1 && remainder[0] == 0;
        };
        auto divmod_mod = [&](std::vector<int> dividend,
                              const std::vector<int> &divisor, int prime,
                              std::vector<int> &quotient,
                              std::vector<int> &remainder){
            trim_mod(dividend);
            quotient.assign(dividend.size() >= divisor.size()
                ? dividend.size() - divisor.size() + 1 : 1, 0);
            int inverse = inverse_mod(divisor.back(), prime);
            while(dividend.size() >= divisor.size() &&
                  !(dividend.size() == 1 && dividend[0] == 0)){
                size_t shift = dividend.size() - divisor.size();
                int coefficient = dividend.back() * inverse % prime;
                quotient[shift] = mod(quotient[shift] + coefficient, prime);
                for(size_t i = 0; i < divisor.size(); ++i)
                    dividend[i + shift] = mod(dividend[i + shift] -
                                              coefficient * divisor[i], prime);
                trim_mod(dividend);
            }
            trim_mod(quotient);
            remainder = std::move(dividend);
        };
        auto multiply_mod = [&](const std::vector<int> &a,
                                const std::vector<int> &b, int prime){
            std::vector<int> result(a.size() + b.size() - 1, 0);
            for(size_t i = 0; i < a.size(); ++i)
                for(size_t j = 0; j < b.size(); ++j)
                    result[i + j] = mod(result[i + j] + a[i] * b[j], prime);
            trim_mod(result);
            return result;
        };
        auto subtract_mod = [&](std::vector<int> a,
                                const std::vector<int> &b, int prime){
            if(a.size() < b.size()) a.resize(b.size(), 0);
            for(size_t i = 0; i < b.size(); ++i)
                a[i] = mod(a[i] - b[i], prime);
            trim_mod(a);
            return a;
        };
        auto remainder_mod = [&](const std::vector<int> &value,
                                 const std::vector<int> &divisor, int prime){
            std::vector<int> quotient, remainder;
            divmod_mod(value, divisor, prime, quotient, remainder);
            return remainder;
        };
        auto exact_divide = [&](const std::vector<int64_t> &divisor,
                                std::vector<int64_t> &quotient){
            std::vector<int64_t> remainder = source;
            quotient.assign(source.size() - divisor.size() + 1, 0);
            while(remainder.size() >= divisor.size()){
                size_t shift = remainder.size() - divisor.size();
                int64_t coefficient = remainder.back();
                quotient[shift] = coefficient;
                for(size_t i = 0; i < divisor.size(); ++i)
                    remainder[i + shift] -= coefficient * divisor[i];
                while(remainder.size() > 1 && remainder.back() == 0)
                    remainder.pop_back();
            }
            return remainder.size() == 1 && remainder[0] == 0;
        };
        auto expression_from = [&](const std::vector<int64_t> &coefficients){
            polynomial sparse;
            for(size_t i = 0; i < coefficients.size(); ++i)
                if(coefficients[i]) sparse.emplace(i, exact_value(coefficients[i]));
            return polynomial_expression(sparse, variable);
        };
        auto hensel_lift = [&](const std::vector<int> &g_mod, int prime,
                               std::vector<int64_t> &integer_factor){
            std::vector<int> f_mod(source.size());
            for(size_t i = 0; i < source.size(); ++i)
                f_mod[i] = mod(source[i], prime);
            std::vector<int> h_mod, remainder;
            divmod_mod(f_mod, g_mod, prime, h_mod, remainder);
            if(!(remainder.size() == 1 && remainder[0] == 0)) return false;

            using egcd_result = std::tuple<std::vector<int>,
                                           std::vector<int>,
                                           std::vector<int>>;
            std::function<egcd_result(std::vector<int>, std::vector<int>)> egcd;
            egcd = [&](std::vector<int> a, std::vector<int> b) -> egcd_result{
                trim_mod(a);
                trim_mod(b);
                if(b.size() == 1 && b[0] == 0)
                    return {a, std::vector<int>{1}, std::vector<int>{0}};
                std::vector<int> quotient, rem;
                divmod_mod(a, b, prime, quotient, rem);
                auto [gcd_value, s1, t1] = egcd(b, rem);
                std::vector<int> product = multiply_mod(quotient, t1, prime);
                return {gcd_value, t1, subtract_mod(s1, product, prime)};
            };
            auto [gcd_value, s, t] = egcd(g_mod, h_mod);
            if(gcd_value.size() != 1 || gcd_value[0] == 0) return false;
            int normalization = inverse_mod(gcd_value[0], prime);
            for(int &value : s) value = value * normalization % prime;
            for(int &value : t) value = value * normalization % prime;

            long double norm = 0;
            for(int64_t value : source) norm += (long double)value * value;
            long double estimate = std::ldexp(std::sqrt(norm), (int)degree);
            if(!std::isfinite((double)estimate) || estimate > 100000000.0L)
                return false;
            int64_t target = (int64_t)std::ceil(2 * estimate) + 1;
            std::vector<int64_t> g(g_mod.begin(), g_mod.end());
            std::vector<int64_t> h(h_mod.begin(), h_mod.end());
            int64_t modulus = prime;
            while(modulus <= target){
                std::vector<int64_t> product(g.size() + h.size() - 1, 0);
                for(size_t i = 0; i < g.size(); ++i)
                    for(size_t j = 0; j < h.size(); ++j)
                        product[i + j] += g[i] * h[j];
                std::vector<int> error(source.size(), 0);
                for(size_t i = 0; i < source.size(); ++i){
                    int64_t difference = source[i] - product[i];
                    if(difference % modulus) return false;
                    error[i] = mod(difference / modulus, prime);
                }
                std::vector<int> correction_g = remainder_mod(
                    multiply_mod(error, t, prime), g_mod, prime);
                std::vector<int> correction_h = remainder_mod(
                    multiply_mod(error, s, prime), h_mod, prime);
                g.resize(g_mod.size(), 0);
                h.resize(h_mod.size(), 0);
                for(size_t i = 0; i < correction_g.size(); ++i)
                    g[i] += modulus * correction_g[i];
                for(size_t i = 0; i < correction_h.size(); ++i)
                    h[i] += modulus * correction_h[i];
                if(modulus > INT64_MAX / prime) return false;
                modulus *= prime;
            }
            integer_factor = std::move(g);
            for(size_t i = 0; i + 1 < integer_factor.size(); ++i)
                if(integer_factor[i] > modulus / 2)
                    integer_factor[i] -= modulus;
            integer_factor.back() = 1;
            return true;
        };

        auto is_zero_mod = [](const std::vector<int> &value){
            return value.size() == 1 && value[0] == 0;
        };
        auto monic_mod = [&](std::vector<int> value, int prime){
            trim_mod(value);
            if(is_zero_mod(value)) return value;
            int inverse = inverse_mod(value.back(), prime);
            for(int &coefficient : value)
                coefficient = coefficient * inverse % prime;
            return value;
        };
        auto quotient_mod = [&](const std::vector<int> &dividend,
                                const std::vector<int> &divisor, int prime){
            std::vector<int> quotient, remainder;
            divmod_mod(dividend, divisor, prime, quotient, remainder);
            return quotient;
        };
        auto gcd_mod = [&](std::vector<int> a, std::vector<int> b, int prime){
            while(!is_zero_mod(b)){
                std::vector<int> quotient, remainder;
                divmod_mod(a, b, prime, quotient, remainder);
                a = std::move(b);
                b = std::move(remainder);
            }
            return monic_mod(std::move(a), prime);
        };
        auto pow_mod = [&](std::vector<int> base, uint64_t exponent,
                           const std::vector<int> &modulus, int prime){
            std::vector<int> result{1};
            base = remainder_mod(base, modulus, prime);
            while(exponent){
                if(exponent & 1)
                    result = remainder_mod(multiply_mod(result, base, prime),
                                           modulus, prime);
                exponent >>= 1;
                if(exponent)
                    base = remainder_mod(multiply_mod(base, base, prime),
                                         modulus, prime);
            }
            return result;
        };

        // Split a square-free polynomial into products whose irreducible
        // factors all have the same degree.
        auto distinct_degree = [&](const std::vector<int> &input, int prime){
            std::vector<std::pair<std::vector<int>, size_t>> result;
            std::vector<int> remaining = monic_mod(input, prime);
            std::vector<int> x{0, 1};
            std::vector<int> frobenius = x;
            for(size_t d = 1; remaining.size() > 1 &&
                2 * d <= remaining.size() - 1; ++d){
                frobenius = pow_mod(frobenius, (uint64_t)prime,
                                    remaining, prime);
                std::vector<int> difference = subtract_mod(frobenius, x, prime);
                std::vector<int> factor = gcd_mod(remaining, difference, prime);
                if(factor.size() <= 1) continue;
                if(factor.size() == remaining.size()){
                    result.push_back({remaining, d});
                    remaining = {1};
                    break;
                }
                result.push_back({factor, d});
                remaining = monic_mod(quotient_mod(remaining, factor, prime),
                                      prime);
                frobenius = remainder_mod(frobenius, remaining, prime);
            }
            if(remaining.size() > 1)
                result.push_back({remaining, remaining.size() - 1});
            return result;
        };

        // Cantor-Zassenhaus equal-degree splitting for odd prime fields.
        std::function<bool(const std::vector<int> &, size_t, int,
                           std::vector<std::vector<int>> &)> equal_degree;
        equal_degree = [&](const std::vector<int> &input, size_t factor_degree,
                           int prime, std::vector<std::vector<int>> &result){
            size_t input_degree = input.size() - 1;
            if(input_degree == factor_degree){
                result.push_back(monic_mod(input, prime));
                return true;
            }
            uint64_t field_size = 1;
            for(size_t i = 0; i < factor_degree; ++i){
                if(field_size > UINT64_MAX / (uint64_t)prime) return false;
                field_size *= (uint64_t)prime;
            }
            uint64_t exponent = (field_size - 1) / 2;
            for(uint64_t trial = 1; trial <= 128; ++trial){
                std::vector<int> probe(input_degree, 0);
                uint64_t state = trial * 6364136223846793005ULL +
                                 1442695040888963407ULL;
                for(int &coefficient : probe){
                    state = state * 6364136223846793005ULL +
                            1442695040888963407ULL;
                    coefficient = (int)(state % (uint64_t)prime);
                }
                trim_mod(probe);
                std::vector<int> powered = pow_mod(probe, exponent, input, prime);
                powered = subtract_mod(powered, std::vector<int>{1}, prime);
                std::vector<int> factor = gcd_mod(input, powered, prime);
                if(factor.size() <= 1 || factor.size() == input.size()) continue;
                std::vector<int> other = monic_mod(
                    quotient_mod(input, factor, prime), prime);
                size_t old_size = result.size();
                if(equal_degree(factor, factor_degree, prime, result) &&
                   equal_degree(other, factor_degree, prime, result)) return true;
                result.resize(old_size);
            }
            return false;
        };

        // Obtain actual modular irreducible factors, then lift only their
        // products. This replaces the p^degree blind candidate search for
        // polynomials with larger coefficients.
        const int ddf_primes[] = {3, 5, 7, 11};
        if(bound > 32) for(int prime : ddf_primes){
            std::vector<int> f_mod(source.size());
            for(size_t i = 0; i < source.size(); ++i)
                f_mod[i] = mod(source[i], prime);
            trim_mod(f_mod);
            if(f_mod.size() != source.size()) continue;

            std::vector<int> derivative(f_mod.size() - 1, 0);
            for(size_t i = 1; i < f_mod.size(); ++i)
                derivative[i - 1] = (int)(i % (size_t)prime) * f_mod[i] % prime;
            trim_mod(derivative);
            if(gcd_mod(f_mod, derivative, prime).size() != 1) continue;

            std::vector<std::vector<int>> irreducible;
            bool split_ok = true;
            for(auto &group : distinct_degree(f_mod, prime)){
                if(!equal_degree(group.first, group.second, prime, irreducible)){
                    split_ok = false;
                    break;
                }
            }
            if(!split_ok || irreducible.size() < 2 || irreducible.size() > 18)
                continue;

            uint64_t subset_count = 1ULL << irreducible.size();
            size_t attempts = 0;
            for(uint64_t mask = 1; mask + 1 < subset_count && attempts < 256;
                ++mask){
                if(mask & 1ULL) continue; // Try one of each complementary pair.
                std::vector<int> modular{1};
                for(size_t i = 0; i < irreducible.size(); ++i)
                    if(mask & (1ULL << i))
                        modular = multiply_mod(modular, irreducible[i], prime);
                size_t factor_degree = modular.size() - 1;
                if(factor_degree == 0 || factor_degree * 2 > degree) continue;
                ++attempts;
                std::vector<int64_t> lifted, lifted_quotient;
                bool lifted_ok = hensel_lift(modular, prime, lifted);
                bool divides = lifted_ok && exact_divide(lifted, lifted_quotient);
                if(divides){
                    uint32_t left = simplify(expression_from(lifted));
                    uint32_t right = simplify(expression_from(lifted_quotient));
                    return storage_.make_multiply({left, right});
                }
            }
        }
        if(bound > 32) return UINT32_MAX;

        const int primes[] = {2, 3, 5, 7};
        size_t hensel_attempts = 0;
        for(int prime : primes){
            for(size_t factor_degree = 2; factor_degree * 2 <= degree;
                ++factor_degree){
                uint64_t combinations = 1;
                for(size_t i = 0; i < factor_degree; ++i)
                    combinations *= (uint64_t)prime;
                if(combinations > 1000000) continue;
                for(uint64_t code = 0; code < combinations; ++code){
                    uint64_t digits = code;
                    std::vector<int> modular(factor_degree + 1, 0);
                    modular.back() = 1;
                    for(size_t i = 0; i < factor_degree; ++i){
                        modular[i] = (int)(digits % (uint64_t)prime);
                        digits /= (uint64_t)prime;
                    }
                    if(!divides_mod(modular, prime)) continue;
                    std::vector<int64_t> lifted, lifted_quotient;
                    if(bound > 32 && hensel_attempts++ < 2 &&
                       hensel_lift(modular, prime, lifted) &&
                       exact_divide(lifted, lifted_quotient)){
                        uint32_t left = simplify(expression_from(lifted));
                        uint32_t right = simplify(expression_from(lifted_quotient));
                        return storage_.make_multiply({left, right});
                    }
                    if(bound > 32) continue;
                    std::vector<std::vector<int64_t>> choices(factor_degree);
                    uint64_t lifts = 1;
                    for(size_t i = 0; i < factor_degree; ++i){
                        for(int64_t value = -bound; value <= bound; ++value)
                            if(mod(value, prime) == modular[i])
                                choices[i].push_back(value);
                        lifts *= choices[i].size();
                        if(lifts > 1000000) break;
                    }
                    if(lifts == 0 || lifts > 1000000) continue;
                    for(uint64_t lift = 0; lift < lifts; ++lift){
                        uint64_t index = lift;
                        std::vector<int64_t> candidate(factor_degree + 1, 0);
                        candidate.back() = 1;
                        for(size_t i = 0; i < factor_degree; ++i){
                            candidate[i] = choices[i][index % choices[i].size()];
                            index /= choices[i].size();
                        }
                        std::vector<int64_t> quotient;
                        if(!exact_divide(candidate, quotient)) continue;
                        uint32_t left = expression_from(candidate);
                        uint32_t right = expression_from(quotient);
                        left = simplify(left);
                        right = simplify(right);
                        return storage_.make_multiply({left, right});
                    }
                }
            }
        }
        return UINT32_MAX;
    }

    uint32_t factor_add(std::vector<uint32_t> terms){
        if(terms.size() < 2) return storage_.make_add(std::move(terms));
        uint32_t trigonometric = trigonometric_power_identity(terms);
        if(trigonometric != UINT32_MAX) return trigonometric;

        precz_t integer_content;
        bool have_integer_content = false;
        for(uint32_t term : terms){
            exact_value coefficient(1);
            exact_node current = storage_.node(term);
            if(current.op == exact_opcode::value){
                coefficient = storage_.values[current.payload];
            }else if(current.op == exact_opcode::multiply){
                const uint32_t *args = storage_.children(current);
                for(size_t i = 0; i < current.operand_count; ++i){
                    exact_node factor = storage_.node(args[i]);
                    if(factor.op == exact_opcode::value)
                        coefficient = coefficient *
                            storage_.values[factor.payload];
                }
            }
            if(!coefficient.is_integer()){
                have_integer_content = false;
                break;
            }
            precz_t magnitude(coefficient.integer().magnitude());
            integer_content = have_integer_content
                ? ::gcd(integer_content, magnitude) : std::move(magnitude);
            have_integer_content = true;
        }
        if(have_integer_content && integer_content > precz_t(1)){
            exact_value content(integer_content);
            uint32_t inverse = storage_.intern_value(exact_value(1) / content);
            std::vector<uint32_t> reduced;
            reduced.reserve(terms.size());
            for(uint32_t term : terms)
                reduced.push_back(storage_.make_multiply({term, inverse}));
            return storage_.make_multiply({storage_.intern_value(content),
                                           factor_add(std::move(reduced))});
        }
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
            uint32_t expression = storage_.make_add(terms);
            if(!full_factorization_) return expression;
            auto refactor_product = [&](uint32_t candidate){
                exact_node product = storage_.node(candidate);
                if(product.op != exact_opcode::multiply) return candidate;
                const uint32_t *parts = storage_.children(product);
                std::vector<uint32_t> result;
                result.reserve(product.operand_count);
                for(size_t i = 0; i < product.operand_count; ++i){
                    exact_node part = storage_.node(parts[i]);
                    if(part.op == exact_opcode::add){
                        const uint32_t *args = storage_.children(part);
                        result.push_back(factor_add(std::vector<uint32_t>(
                            args, args + part.operand_count)));
                    }else result.push_back(parts[i]);
                }
                return storage_.make_multiply(std::move(result));
            };
            uint32_t rational_roots = factor_rational_roots(expression);
            if(rational_roots != UINT32_MAX)
                return refactor_product(rational_roots);
            uint32_t quartic = factor_monic_quartic(expression);
            if(quartic != UINT32_MAX) return quartic;
            uint32_t modular = factor_modular_search(expression);
            if(modular != UINT32_MAX) return refactor_product(modular);
            uint32_t square_free = factor_square_free(expression);
            if(square_free != UINT32_MAX) return square_free;
            uint32_t variable = UINT32_MAX;
            polynomial quadratic;
            if(parse_polynomial(expression, variable, quadratic) &&
               variable != UINT32_MAX && !quadratic.empty() &&
               quadratic.rbegin()->first == 2){
                exact_value a = quadratic.count(2) ? quadratic[2] : exact_value(0);
                exact_value b = quadratic.count(1) ? quadratic[1] : exact_value(0);
                exact_value c = quadratic.count(0) ? quadratic[0] : exact_value(0);
                exact_value discriminant = b * b - exact_value(4) * a * c;
                uint32_t radical = storage_.make_sqrt(
                    storage_.intern_value(discriminant));
                exact_node radical_node = storage_.node(radical);
                if(radical_node.op == exact_opcode::value){
                    exact_value root = storage_.values[radical_node.payload];
                    exact_value denominator = exact_value(2) * a;
                    exact_value root_a = (-b + root) / denominator;
                    exact_value root_b = (-b - root) / denominator;
                    uint32_t minus_root_a = storage_.intern_value(-root_a);
                    uint32_t minus_root_b = storage_.intern_value(-root_b);
                    uint32_t factor_a = storage_.make_add({variable, minus_root_a});
                    uint32_t factor_b = storage_.make_add({variable, minus_root_b});
                    return storage_.make_multiply({
                        storage_.intern_value(a), factor_a, factor_b});
                }
            }
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
            // Normalize the quotient before recursing.  Without this step the
            // inverse common factors hide the polynomial structure from the
            // next factoring pass (for example, (x + 1)^2*(x^2 + 1)^2).
            reduced.push_back(simplify(storage_.make_multiply(
                std::move(quotient))));
        }
        common_factors.push_back(factor_add(std::move(reduced)));
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
    explicit exact_factor_simplifier(exact_storage &storage,
                                     bool full_factorization = false)
        : storage_(storage), full_factorization_(full_factorization){}

    uint32_t polynomial_gcd(uint32_t left, uint32_t right){
        const exact_node &left_node = storage_.node(left);
        const exact_node &right_node = storage_.node(right);
        if(left_node.op == exact_opcode::value &&
           right_node.op == exact_opcode::value){
            const exact_value &a = storage_.values[left_node.payload];
            const exact_value &b = storage_.values[right_node.payload];
            if(!a.is_integer() || !b.is_integer())
                throw std::invalid_argument(
                    "gcd numeric arguments must be exact integers");
            return storage_.intern_value(exact_value(::gcd(a.integer(),
                                                            b.integer())));
        }
        uint32_t ignored_left = 0, ignored_right = 0, common = 0;
        if(!multivariate_gcd_quotients(left, right, ignored_left,
                                      ignored_right, &common))
            throw std::invalid_argument(
                "gcd requires exact polynomial arguments");
        return common;
    }

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
            combine_double_angle_product(children);
            result = storage_.make_multiply(std::move(children));
        }
        else if(source.op == exact_opcode::power){
            if(!rationalize_inverse(children[0], children[1], result))
                result = storage_.make_power(children[0], children[1]);
        }
        else if(source.op == exact_opcode::square_root)
            result = storage_.make_sqrt(children[0]);
        else if(exact_unary_function(source.op))
            result = storage_.make_function(source.op, children[0]);
        else if(source.op == exact_opcode::partial_gamma ||
                source.op == exact_opcode::derivative ||
                source.op == exact_opcode::integral)
            result = storage_.intern_compound(source.op, children);
        else if(source.op == exact_opcode::bounded_sum)
            result = storage_.make_sum(children[0], children[1],
                                       children[2], children[3]);
        else if(source.op == exact_opcode::expression_list ||
                source.op == exact_opcode::rule)
            result = storage_.intern_compound(source.op, children);
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
            exact_node base_node = storage_.node(base);
            if(integral && power >= 0 && base_node.op == exact_opcode::add){
                uint32_t accumulated = storage_.intern_value(exact_value(1));
                uint32_t factor = base;
                uint64_t bits = (uint64_t)power;
                while(bits){
                    if(bits & 1) accumulated = multiply(accumulated, factor);
                    bits >>= 1;
                    if(bits) factor = multiply(factor, factor);
                }
                result = accumulated;
            }else if(integral && power > 0 &&
                     base_node.op == exact_opcode::multiply){
                const uint32_t *factors = storage_.children(base_node);
                std::vector<uint32_t> powered;
                powered.reserve(base_node.operand_count);
                for(size_t i = 0; i < base_node.operand_count; ++i)
                    powered.push_back(storage_.make_power(factors[i], exponent));
                result = storage_.make_multiply(std::move(powered));
            }else{
                result = storage_.make_power(base, exponent);
            }
        }else if(source.op == exact_opcode::square_root){
            result = storage_.make_sqrt(expand(children[0]));
        }else if(exact_unary_function(source.op)){
            result = storage_.make_function(source.op, expand(children[0]));
        }else if(source.op == exact_opcode::partial_gamma ||
                 source.op == exact_opcode::derivative ||
                 source.op == exact_opcode::integral){
            for(uint32_t &child : children) child = expand(child);
            result = storage_.intern_compound(source.op, children);
        }else if(source.op == exact_opcode::bounded_sum){
            for(uint32_t &child : children) child = expand(child);
            result = storage_.make_sum(children[0], children[1],
                                       children[2], children[3]);
        }else if(source.op == exact_opcode::expression_list ||
                 source.op == exact_opcode::rule){
            for(uint32_t &child : children) child = expand(child);
            result = storage_.intern_compound(source.op, children);
        }
        memo_.emplace(expression, result);
        return result;
    }
};

class exact_trig_rewriter{
    exact_storage &storage_;
    bool expand_;
    std::unordered_map<uint32_t, uint32_t> memo_;

    uint32_t value(int64_t number){
        return storage_.intern_value(exact_value(number));
    }

    uint32_t function(exact_opcode operation, uint32_t argument){
        return storage_.make_function(operation, argument);
    }

    bool integer_multiple_argument(uint32_t argument, int64_t &multiple,
                                   uint32_t &unit){
        exact_node product = storage_.node(argument);
        if(product.op != exact_opcode::multiply) return false;
        const uint32_t *args = storage_.children(product);
        std::vector<uint32_t> remaining;
        remaining.reserve(product.operand_count);
        bool removed_coefficient = false;
        for(size_t i = 0; i < product.operand_count; ++i){
            exact_node factor = storage_.node(args[i]);
            if(!removed_coefficient && factor.op == exact_opcode::value){
                int64_t candidate = 0;
                if(integer_i64(storage_.values[factor.payload], candidate) &&
                   (candidate >= 2 && candidate <= 32)){
                    multiple = candidate;
                    removed_coefficient = true;
                    continue;
                }
            }
            remaining.push_back(args[i]);
        }
        if(!removed_coefficient || remaining.empty()) return false;
        unit = storage_.make_multiply(std::move(remaining));
        return true;
    }

    uint32_t expand_integer_multiple(exact_opcode operation, int64_t multiple,
                                     uint32_t unit){
        uint32_t sine = expand_function(exact_opcode::sine, unit);
        uint32_t cosine = expand_function(exact_opcode::cosine, unit);
        auto chebyshev_t = [&](uint32_t variable, int64_t degree){
            uint32_t previous = value(1);
            if(degree == 0) return previous;
            uint32_t current = variable;
            for(int64_t i = 2; i <= degree; ++i){
                uint32_t next = storage_.make_add({
                    storage_.make_multiply({value(2), variable, current}),
                    storage_.make_multiply({value(-1), previous})});
                previous = current;
                current = next;
            }
            return current;
        };
        auto chebyshev_u = [&](uint32_t variable, int64_t degree){
            uint32_t previous = value(1);
            if(degree == 0) return previous;
            uint32_t current = storage_.make_multiply({value(2), variable});
            for(int64_t i = 2; i <= degree; ++i){
                uint32_t next = storage_.make_add({
                    storage_.make_multiply({value(2), variable, current}),
                    storage_.make_multiply({value(-1), previous})});
                previous = current;
                current = next;
            }
            return current;
        };

        uint32_t result = 0;
        if(operation == exact_opcode::cosine){
            result = chebyshev_t(cosine, multiple);
        }else if(multiple & 1){
            result = chebyshev_t(sine, multiple);
            if(((multiple - 1) / 2) & 1)
                result = storage_.make_multiply({value(-1), result});
        }else{
            result = storage_.make_multiply({
                sine, chebyshev_u(cosine, multiple - 1)});
        }
        exact_expander polynomial(storage_, 100000);
        return polynomial.expand(result);
    }

    uint32_t expand_function(exact_opcode operation, uint32_t argument){
        if(operation != exact_opcode::sine && operation != exact_opcode::cosine)
            return function(operation, argument);

        int64_t multiple = 0;
        uint32_t unit = 0;
        if(integer_multiple_argument(argument, multiple, unit))
            return expand_integer_multiple(operation, multiple, unit);

        exact_node sum = storage_.node(argument);
        if(sum.op == exact_opcode::add && sum.operand_count >= 2){
            const uint32_t *args = storage_.children(sum);
            uint32_t left = args[0];
            std::vector<uint32_t> rest(args + 1, args + sum.operand_count);
            uint32_t right = storage_.make_add(std::move(rest));
            uint32_t sin_left = expand_function(exact_opcode::sine, left);
            uint32_t cos_left = expand_function(exact_opcode::cosine, left);
            uint32_t sin_right = expand_function(exact_opcode::sine, right);
            uint32_t cos_right = expand_function(exact_opcode::cosine, right);
            if(operation == exact_opcode::sine)
                return storage_.make_add({
                    storage_.make_multiply({sin_left, cos_right}),
                    storage_.make_multiply({cos_left, sin_right})});
            return storage_.make_add({
                storage_.make_multiply({cos_left, cos_right}),
                storage_.make_multiply({
                    value(-1), sin_left, sin_right})});
        }
        return function(operation, argument);
    }

    uint32_t reduce_power(uint32_t base, uint32_t exponent){
        exact_node exponent_node = storage_.node(exponent);
        int64_t power = 0;
        if(exponent_node.op != exact_opcode::value ||
           !integer_i64(storage_.values[exponent_node.payload], power) ||
           power != 2)
            return storage_.make_power(base, exponent);
        exact_node function_node = storage_.node(base);
        if(function_node.op != exact_opcode::sine &&
           function_node.op != exact_opcode::cosine)
            return storage_.make_power(base, exponent);

        uint32_t argument = storage_.children(function_node)[0];
        uint32_t doubled = storage_.make_multiply({value(2), argument});
        uint32_t cosine = function(exact_opcode::cosine, doubled);
        uint32_t half = storage_.intern_value(exact_value(
            precq_t(precn_t(1), precn_t(2))));
        uint32_t cosine_half = storage_.make_multiply({half, cosine});
        return function_node.op == exact_opcode::sine
            ? storage_.make_add({half,
                                 storage_.make_multiply({value(-1), cosine_half})})
            : storage_.make_add({half, cosine_half});
    }

    uint32_t reduce_product(std::vector<uint32_t> factors){
        for(size_t sine = 0; sine < factors.size(); ++sine){
            exact_node sine_node = storage_.node(factors[sine]);
            if(sine_node.op != exact_opcode::sine) continue;
            for(size_t cosine = 0; cosine < factors.size(); ++cosine){
                exact_node cosine_node = storage_.node(factors[cosine]);
                if(cosine_node.op != exact_opcode::cosine ||
                   storage_.children(sine_node)[0] !=
                   storage_.children(cosine_node)[0]) continue;
                uint32_t argument = storage_.children(sine_node)[0];
                uint32_t doubled = storage_.make_multiply({value(2), argument});
                std::vector<uint32_t> reduced;
                reduced.reserve(factors.size() - 1);
                for(size_t i = 0; i < factors.size(); ++i)
                    if(i != sine && i != cosine) reduced.push_back(factors[i]);
                reduced.push_back(storage_.intern_value(exact_value(
                    precq_t(precn_t(1), precn_t(2)))));
                reduced.push_back(function(exact_opcode::sine, doubled));
                return storage_.make_multiply(std::move(reduced));
            }
        }
        return storage_.make_multiply(std::move(factors));
    }

public:
    exact_trig_rewriter(exact_storage &storage, bool expand)
        : storage_(storage), expand_(expand), memo_(){}

    uint32_t rewrite(uint32_t expression){
        auto cached = memo_.find(expression);
        if(cached != memo_.end()) return cached->second;
        exact_node source = storage_.node(expression);
        std::vector<uint32_t> children;
        const uint32_t *args = storage_.children(source);
        children.reserve(source.operand_count);
        for(size_t i = 0; i < source.operand_count; ++i)
            children.push_back(rewrite(args[i]));

        uint32_t result = expression;
        if(source.op == exact_opcode::add)
            result = storage_.make_add(std::move(children));
        else if(source.op == exact_opcode::multiply)
            result = expand_ ? storage_.make_multiply(std::move(children))
                             : reduce_product(std::move(children));
        else if(source.op == exact_opcode::power)
            result = expand_ ? storage_.make_power(children[0], children[1])
                             : reduce_power(children[0], children[1]);
        else if(source.op == exact_opcode::square_root)
            result = storage_.make_sqrt(children[0]);
        else if(exact_unary_function(source.op))
            result = expand_ ? expand_function(source.op, children[0])
                             : function(source.op, children[0]);
        else if(source.op == exact_opcode::partial_gamma ||
                source.op == exact_opcode::derivative ||
                source.op == exact_opcode::integral)
            result = storage_.intern_compound(source.op, children);
        else if(source.op == exact_opcode::bounded_sum)
            result = storage_.make_sum(children[0], children[1],
                                       children[2], children[3]);
        else if(source.op == exact_opcode::expression_list ||
                source.op == exact_opcode::rule)
            result = storage_.intern_compound(source.op, children);
        memo_.emplace(expression, result);
        return result;
    }
};

class exact_substituter{
    exact_storage &storage_;
    uint32_t target_;
    uint32_t replacement_;
    std::unordered_map<uint32_t, uint32_t> memo_;

    bool contains(uint32_t expression, uint32_t target){
        std::unordered_set<uint32_t> visited;
        std::vector<uint32_t> pending(1, expression);
        while(!pending.empty()){
            uint32_t id = pending.back();
            pending.pop_back();
            if(id == target) return true;
            if(!visited.insert(id).second) continue;
            const exact_node &current = storage_.node(id);
            const uint32_t *args = storage_.children(current);
            pending.insert(pending.end(), args, args + current.operand_count);
        }
        return false;
    }

public:
    exact_substituter(exact_storage &storage, uint32_t target,
                      uint32_t replacement)
        : storage_(storage), target_(target), replacement_(replacement), memo_(){}

    uint32_t rewrite(uint32_t expression){
        if(expression == target_) return replacement_;
        auto cached = memo_.find(expression);
        if(cached != memo_.end()) return cached->second;
        exact_node source = storage_.node(expression);
        const uint32_t *args = storage_.children(source);

        uint32_t result = expression;
        if(source.op == exact_opcode::bounded_sum){
            uint32_t variable = args[0];
            uint32_t lower = rewrite(args[1]);
            uint32_t upper = rewrite(args[2]);
            uint32_t body = args[3];
            if(target_ != variable){
                if(contains(body, target_) && contains(replacement_, variable))
                    throw std::invalid_argument(
                        "substitution would capture a bounded-sum variable");
                body = rewrite(body);
            }
            result = storage_.make_sum(variable, lower, upper, body);
        }else if(source.op == exact_opcode::rule){
            if(source.operand_count != 2)
                throw std::logic_error("rule node must have two operands");
            result = storage_.intern_compound(
                exact_opcode::rule, {args[0], rewrite(args[1])});
        }else if(source.operand_count){
            std::vector<uint32_t> children;
            children.reserve(source.operand_count);
            for(size_t i = 0; i < source.operand_count; ++i)
                children.push_back(rewrite(args[i]));
            if(source.op == exact_opcode::add)
                result = storage_.make_add(std::move(children));
            else if(source.op == exact_opcode::multiply)
                result = storage_.make_multiply(std::move(children));
            else if(source.op == exact_opcode::power)
                result = storage_.make_power(children[0], children[1]);
            else if(source.op == exact_opcode::square_root)
                result = storage_.make_sqrt(children[0]);
            else if(exact_unary_function(source.op))
                result = storage_.make_function(source.op, children[0]);
            else if(source.op == exact_opcode::partial_gamma ||
                    source.op == exact_opcode::derivative ||
                    source.op == exact_opcode::integral)
                result = storage_.intern_compound(source.op, children);
            else if(source.op == exact_opcode::expression_list ||
                    source.op == exact_opcode::rule)
                result = storage_.intern_compound(source.op, children);
        }
        memo_.emplace(expression, result);
        return result;
    }
};

class exact_polynomial_checker{
    const exact_storage &storage_;
    std::unordered_set<uint32_t> variables_;
    bool selected_variables_;
    std::unordered_map<uint32_t, bool> contains_memo_;
    std::unordered_map<uint32_t, bool> symbol_memo_;
    std::unordered_map<uint32_t, bool> polynomial_memo_;

    bool contains_selected_variable(uint32_t expression){
        auto cached = contains_memo_.find(expression);
        if(cached != contains_memo_.end()) return cached->second;
        if(variables_.find(expression) != variables_.end()){
            contains_memo_.emplace(expression, true);
            return true;
        }
        const exact_node &current = storage_.node(expression);
        const uint32_t *args = storage_.children(current);
        for(size_t i = 0; i < current.operand_count; ++i){
            if(contains_selected_variable(args[i])){
                contains_memo_.emplace(expression, true);
                return true;
            }
        }
        contains_memo_.emplace(expression, false);
        return false;
    }

    bool contains_symbol(uint32_t expression){
        auto cached = symbol_memo_.find(expression);
        if(cached != symbol_memo_.end()) return cached->second;
        const exact_node &current = storage_.node(expression);
        if(current.op == exact_opcode::symbol){
            symbol_memo_.emplace(expression, true);
            return true;
        }
        const uint32_t *args = storage_.children(current);
        for(size_t i = 0; i < current.operand_count; ++i){
            if(contains_symbol(args[i])){
                symbol_memo_.emplace(expression, true);
                return true;
            }
        }
        symbol_memo_.emplace(expression, false);
        return false;
    }

public:
    exact_polynomial_checker(const exact_storage &storage,
                             const std::vector<uint32_t> &variables)
        : storage_(storage), variables_(variables.begin(), variables.end()),
          selected_variables_(!variables.empty()), contains_memo_(),
          symbol_memo_(), polynomial_memo_(){}

    bool check(uint32_t expression){
        if(selected_variables_ && !contains_selected_variable(expression))
            return true;
        if(!selected_variables_ && !contains_symbol(expression)) return true;
        auto cached = polynomial_memo_.find(expression);
        if(cached != polynomial_memo_.end()) return cached->second;

        const exact_node &current = storage_.node(expression);
        bool result = false;
        if(current.op == exact_opcode::value ||
           current.op == exact_opcode::constant_pi ||
           current.op == exact_opcode::constant_e ||
           current.op == exact_opcode::constant_i ||
           current.op == exact_opcode::symbol){
            result = true;
        }else if(current.op == exact_opcode::add ||
                 current.op == exact_opcode::multiply){
            result = true;
            const uint32_t *args = storage_.children(current);
            for(size_t i = 0; i < current.operand_count; ++i)
                if(!check(args[i])){ result = false; break; }
        }else if(current.op == exact_opcode::power){
            const uint32_t *args = storage_.children(current);
            const exact_node &exponent = storage_.node(args[1]);
            int64_t integer_exponent = -1;
            result = exponent.op == exact_opcode::value &&
                integer_i64(storage_.values[exponent.payload], integer_exponent) &&
                integer_exponent >= 0 && check(args[0]);
        }
        polynomial_memo_.emplace(expression, result);
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
exact_expr exact_context::factor(const exact_expr &expression){
    if(!expression.valid() || expression.storage_ != storage_)
        throw std::invalid_argument("exact expression belongs to a different context");
    exact_factor_simplifier factorer(*storage_, true);
    return exact_expr(storage_, factorer.simplify(expression.root_));
}
exact_expr exact_context::factor_integer(const exact_expr &expression){
    if(!expression.valid() || expression.storage_ != storage_)
        throw std::invalid_argument(
            "exact expression belongs to a different context");
    const exact_node &node = storage_->node(expression.root_);
    if(node.op != exact_opcode::value ||
       !storage_->values[node.payload].is_integer())
        throw std::invalid_argument("factorint requires an exact integer");
    const precz_t &integer = storage_->values[node.payload].integer();
    bool negative = integer.is_negative();
    precn_t magnitude(integer.magnitude());
    if(magnitude.rsiz == 0)
        throw std::domain_error("factorint is undefined for zero");
    std::vector<uint32_t> result;
    if(negative)
        result.push_back(storage_->intern_value(exact_value(-1)));
    std::vector<precn_t> factors;
    if(!cas_factor_big(magnitude, factors)){
        throw std::runtime_error(
            "ECM and quadratic sieve did not find a factor");
    }
    std::sort(factors.begin(), factors.end());
    for(size_t begin = 0; begin < factors.size();){
        size_t end = begin + 1;
        while(end < factors.size() && factors[end] == factors[begin]) ++end;
        uint32_t prime = storage_->intern_value(exact_value(
            precz_t(factors[begin])));
        size_t exponent = end - begin;
        result.push_back(exponent == 1 ? prime : storage_->intern_compound(
            exact_opcode::power, {prime, storage_->intern_value(
                exact_value((uint64_t)exponent))}));
        begin = end;
    }
    return exact_expr(storage_, storage_->intern_compound(
        exact_opcode::expression_list, result));
}
exact_expr exact_context::gcd(const exact_expr &left, const exact_expr &right){
    if(!left.valid() || !right.valid() || left.storage_ != storage_ ||
       right.storage_ != storage_)
        throw std::invalid_argument(
            "exact expressions belong to different contexts");
    exact_factor_simplifier factorer(*storage_);
    uint32_t left_expanded = exact_expander(*storage_, 100000).expand(left.root_);
    uint32_t right_expanded = exact_expander(*storage_, 100000).expand(right.root_);
    return exact_expr(storage_, factorer.polynomial_gcd(left_expanded,
                                                        right_expanded));
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

exact_expr exact_context::trig_expand(const exact_expr &expression){
    if(!expression.valid() || expression.storage_ != storage_)
        throw std::invalid_argument("exact expression belongs to a different context");
    exact_trig_rewriter rewriter(*storage_, true);
    return exact_expr(storage_, rewriter.rewrite(expression.root_));
}

exact_expr exact_context::trig_reduce(const exact_expr &expression){
    if(!expression.valid() || expression.storage_ != storage_)
        throw std::invalid_argument("exact expression belongs to a different context");
    exact_trig_rewriter rewriter(*storage_, false);
    return exact_expr(storage_, rewriter.rewrite(expression.root_));
}

exact_expr exact_context::groebner(
        const std::vector<exact_expr> &polynomials,
        const std::vector<exact_expr> &variables){
    if(polynomials.empty() || variables.empty())
        throw std::invalid_argument("groebner requires polynomials and variables");
    std::vector<uint32_t> ids;
    for(const exact_expr &v : variables){
        if(!v.valid() || v.storage_ != storage_ ||
           storage_->node(v.root_).op != exact_opcode::symbol)
            throw std::invalid_argument("groebner variables must be symbols");
        ids.push_back(v.root_);
    }
    using monomial = std::vector<uint16_t>;
    using polynomial = std::map<monomial, exact_expr>;
    exact_expr zero = integer(0), one = integer(1);
    auto is_zero = [&](const exact_expr &v){
        exact_expr s = simplify(v);
        const exact_node &n = storage_->node(s.root_);
        return n.op == exact_opcode::value &&
            storage_->values[n.payload].is_zero();
    };
    auto add_term = [&](polynomial &p, const monomial &m,
                        const exact_expr &c){
        if(is_zero(c)) return;
        auto it = p.find(m);
        if(it == p.end()) p.emplace(m, c);
        else{
            it->second = simplify(it->second + c);
            if(is_zero(it->second)) p.erase(it);
        }
    };
    std::unordered_map<uint32_t, bool> has_variable;
    auto contains = [&](auto &&self, uint32_t id) -> bool{
        auto it = has_variable.find(id);
        if(it != has_variable.end()) return it->second;
        if(std::find(ids.begin(), ids.end(), id) != ids.end()){
            has_variable[id] = true; return true;
        }
        const exact_node &n = storage_->node(id);
        const uint32_t *a = storage_->children(n);
        bool result = false;
        for(size_t i = 0; i < n.operand_count; ++i)
            if(self(self, a[i])){ result = true; break; }
        has_variable[id] = result;
        return result;
    };
    std::unordered_set<uint32_t> failed;
    auto parse = [&](auto &&self, uint32_t id, polynomial &out) -> bool{
        if(failed.count(id)) return false;
        if(!contains(contains, id)){ out.clear(); add_term(out, monomial(ids.size()),
            exact_expr(storage_, id)); return true; }
        auto found = std::find(ids.begin(), ids.end(), id);
        if(found != ids.end()){
            out.clear(); monomial m(ids.size());
            m[(size_t)(found - ids.begin())] = 1;
            out.emplace(std::move(m), one); return true;
        }
        const exact_node &n = storage_->node(id);
        const uint32_t *a = storage_->children(n);
        if(n.op == exact_opcode::add){
            out.clear();
            for(size_t i = 0; i < n.operand_count; ++i){
                polynomial q; if(!self(self, a[i], q)){ failed.insert(id); return false; }
                for(auto &t : q) add_term(out, t.first, t.second);
            }
            return true;
        }
        if(n.op == exact_opcode::multiply){
            out.clear(); add_term(out, monomial(ids.size()), one);
            for(size_t i = 0; i < n.operand_count; ++i){
                polynomial q; if(!self(self, a[i], q)){ failed.insert(id); return false; }
                polynomial next;
                for(const auto &x : out) for(const auto &y : q){
                    monomial m(ids.size());
                    for(size_t k = 0; k < m.size(); ++k){
                        uint32_t e = (uint32_t)x.first[k] + y.first[k];
                        if(e > UINT16_MAX){ failed.insert(id); return false; }
                        m[k] = (uint16_t)e;
                    }
                    add_term(next, m, x.second * y.second);
                }
                out = std::move(next);
            }
            return true;
        }
        if(n.op == exact_opcode::power){
            exact_node e = storage_->node(a[1]); int64_t power = -1;
            if(e.op != exact_opcode::value ||
               !integer_i64(storage_->values[e.payload], power) || power < 0 || power > 32){
                failed.insert(id); return false;
            }
            polynomial base; if(!self(self, a[0], base)){ failed.insert(id); return false; }
            out.clear(); add_term(out, monomial(ids.size()), one);
            for(int64_t i = 0; i < power; ++i){
                polynomial next;
                for(const auto &x : out) for(const auto &y : base){
                    monomial m(ids.size());
                    for(size_t k = 0; k < m.size(); ++k){
                        uint32_t e2 = (uint32_t)x.first[k] + y.first[k];
                        if(e2 > UINT16_MAX){ failed.insert(id); return false; }
                        m[k] = (uint16_t)e2;
                    }
                    add_term(next, m, x.second * y.second);
                }
                out = std::move(next);
            }
            return true;
        }
        failed.insert(id); return false;
    };
    std::vector<polynomial> basis;
    for(const exact_expr &f : polynomials){
        polynomial p;
        if(!parse(parse, f.root_, p))
            throw std::invalid_argument("groebner requires polynomial expressions");
        if(!p.empty()) basis.push_back(std::move(p));
    }
    auto divides = [](const monomial &a, const monomial &b){
        for(size_t i = 0; i < a.size(); ++i) if(a[i] > b[i]) return false;
        return true;
    };
    auto sub = [](const monomial &a, const monomial &b){
        monomial r(a.size()); for(size_t i = 0; i < r.size(); ++i) r[i] = a[i] - b[i]; return r;
    };
    auto scale_add = [&](polynomial &p, const polynomial &q,
                         const monomial &shift, const exact_expr &scale){
        for(const auto &t : q){ monomial m(t.first.size());
            for(size_t i = 0; i < m.size(); ++i) m[i] = t.first[i] + shift[i];
            add_term(p, m, t.second * scale); }
    };
    auto reduce = [&](polynomial p, const std::vector<polynomial> &bs){
        polynomial r;
        while(!p.empty()){
            auto lead = std::prev(p.end()); bool changed = false;
            for(const polynomial &q : bs) if(!q.empty() && divides(q.rbegin()->first, lead->first)){
                scale_add(p, q, sub(lead->first, q.rbegin()->first),
                          -(lead->second / q.rbegin()->second));
                changed = true; break;
            }
            if(!changed){ add_term(r, lead->first, lead->second); p.erase(lead); }
        }
        return r;
    };
    std::vector<std::pair<size_t,size_t>> pairs;
    for(size_t i=0;i<basis.size();++i) for(size_t j=0;j<i;++j) pairs.emplace_back(j,i);
    for(size_t pi=0; pi<pairs.size(); ++pi){
        size_t i=pairs[pi].first,j=pairs[pi].second; monomial l(basis[i].rbegin()->first.size());
        for(size_t k=0;k<l.size();++k) l[k]=std::max(basis[i].rbegin()->first[k],basis[j].rbegin()->first[k]);
        polynomial s;
        scale_add(s,basis[i],sub(l,basis[i].rbegin()->first),one/basis[i].rbegin()->second);
        scale_add(s,basis[j],sub(l,basis[j].rbegin()->first),-one/basis[j].rbegin()->second);
        s=reduce(std::move(s),basis); if(s.empty()) continue;
        size_t n=basis.size(); basis.push_back(std::move(s));
        for(size_t k=0;k<n;++k) pairs.emplace_back(k,n);
    }
    std::vector<uint32_t> result;
    for(const polynomial &p : basis){ std::vector<uint32_t> terms;
        for(const auto &t:p){ std::vector<uint32_t> factors{t.second.root_};
            for(size_t i=0;i<ids.size();++i) if(t.first[i]) factors.push_back(
                t.first[i]==1?ids[i]:storage_->make_power(ids[i],integer(t.first[i]).root_));
            terms.push_back(storage_->make_multiply(std::move(factors))); }
        result.push_back(storage_->make_add(std::move(terms)));
    }
    return exact_expr(storage_, storage_->intern_compound(exact_opcode::expression_list,result));
}

exact_expr exact_context::substitute(const exact_expr &expression,
                                     const exact_expr &target,
                                     const exact_expr &replacement){
    if(!expression.valid() || !target.valid() || !replacement.valid() ||
       expression.storage_ != storage_ || target.storage_ != storage_ ||
       replacement.storage_ != storage_)
        throw std::invalid_argument("exact expressions belong to different contexts");
    exact_substituter substituter(*storage_, target.root_, replacement.root_);
    uint32_t result = substituter.rewrite(expression.root_);
    return exact_expr(storage_, storage_->promote_approximate(result));
}

bool exact_context::is_polynomial(const exact_expr &expression) const{
    return is_polynomial(expression, {});
}

bool exact_context::is_polynomial(
        const exact_expr &expression,
        const std::vector<exact_expr> &variables) const{
    if(!expression.valid() || expression.storage_ != storage_)
        throw std::invalid_argument("exact expression belongs to a different context");
    std::vector<uint32_t> ids;
    ids.reserve(variables.size());
    for(const exact_expr &variable : variables){
        if(!variable.valid() || variable.storage_ != storage_)
            throw std::invalid_argument(
                "polynomial variables belong to a different context");
        if(storage_->node(variable.root_).op != exact_opcode::symbol)
            throw std::invalid_argument("polynomial variables must be symbols");
        ids.push_back(variable.root_);
    }
    exact_polynomial_checker checker(*storage_, ids);
    return checker.check(expression.root_);
}

exact_expr exact_context::solve_polynomial_impl(
        const exact_expr &expression,
        const std::vector<exact_expr> &variables,
        bool require_exact_coefficients){
    if(!expression.valid() || expression.storage_ != storage_)
        throw std::invalid_argument("exact expression belongs to a different context");
    if(variables.size() != 1)
        throw std::invalid_argument("solve currently requires exactly one variable");
    const exact_expr &variable_expression = variables[0];
    if(!variable_expression.valid() || variable_expression.storage_ != storage_ ||
       storage_->node(variable_expression.root_).op != exact_opcode::symbol)
        throw std::invalid_argument("solve variable must be a symbol");
    uint32_t variable = variable_expression.root_;
    uint32_t zero = storage_->intern_value(exact_value(0));
    uint32_t one = storage_->intern_value(exact_value(1));

    std::unordered_map<uint32_t, bool> contains_memo;
    auto contains_variable = [&](auto &&self, uint32_t id) -> bool{
        auto cached = contains_memo.find(id);
        if(cached != contains_memo.end()) return cached->second;
        if(id == variable){ contains_memo.emplace(id, true); return true; }
        const exact_node &current = storage_->node(id);
        const uint32_t *args = storage_->children(current);
        for(size_t i = 0; i < current.operand_count; ++i)
            if(self(self, args[i])){
                contains_memo.emplace(id, true);
                return true;
            }
        contains_memo.emplace(id, false);
        return false;
    };
    auto is_zero = [&](uint32_t id){
        const exact_node &current = storage_->node(id);
        return current.op == exact_opcode::value &&
               storage_->values[current.payload].is_zero();
    };
    using coefficients_t = std::vector<uint32_t>;
    auto trim = [&](coefficients_t &coefficients){
        while(!coefficients.empty() && is_zero(coefficients.back()))
            coefficients.pop_back();
    };
    auto add_coefficients = [&](coefficients_t &target,
                                const coefficients_t &source){
        if(target.size() < source.size()) target.resize(source.size(), zero);
        for(size_t i = 0; i < source.size(); ++i)
            target[i] = storage_->make_add({target[i], source[i]});
        trim(target);
    };
    auto multiply_coefficients = [&](const coefficients_t &left,
                                     const coefficients_t &right,
                                     coefficients_t &result){
        if(left.empty() || right.empty()){ result.clear(); return true; }
        result.assign(std::min<size_t>(5, left.size() + right.size() - 1), zero);
        for(size_t i = 0; i < left.size(); ++i){
            for(size_t j = 0; j < right.size(); ++j){
                uint32_t product = storage_->make_multiply({left[i], right[j]});
                if(i + j > 4){
                    if(!is_zero(product)) return false;
                    continue;
                }
                result[i + j] = storage_->make_add({result[i + j], product});
            }
        }
        trim(result);
        return true;
    };

    std::unordered_map<uint32_t, coefficients_t> parsed_memo;
    std::unordered_set<uint32_t> failed;
    auto parse = [&](auto &&self, uint32_t id, coefficients_t &result) -> bool{
        auto cached = parsed_memo.find(id);
        if(cached != parsed_memo.end()){ result = cached->second; return true; }
        if(failed.find(id) != failed.end()) return false;
        if(!contains_variable(contains_variable, id)){
            result = {id};
            parsed_memo.emplace(id, result);
            return true;
        }
        if(id == variable){
            result = {zero, one};
            parsed_memo.emplace(id, result);
            return true;
        }
        exact_node current = storage_->node(id);
        const uint32_t *args = storage_->children(current);
        bool ok = true;
        if(current.op == exact_opcode::add){
            result.clear();
            for(size_t i = 0; i < current.operand_count && ok; ++i){
                coefficients_t term;
                ok = self(self, args[i], term);
                if(ok) add_coefficients(result, term);
            }
        }else if(current.op == exact_opcode::multiply){
            result = {one};
            for(size_t i = 0; i < current.operand_count && ok; ++i){
                coefficients_t factor, product;
                ok = self(self, args[i], factor) &&
                     multiply_coefficients(result, factor, product);
                if(ok) result = std::move(product);
            }
        }else if(current.op == exact_opcode::power){
            exact_node exponent = storage_->node(args[1]);
            int64_t power = -1;
            ok = exponent.op == exact_opcode::value &&
                 integer_i64(storage_->values[exponent.payload], power) &&
                 power >= 0 && power <= 4;
            coefficients_t base;
            if(ok) ok = self(self, args[0], base);
            result = {one};
            for(int64_t i = 0; i < power && ok; ++i){
                coefficients_t product;
                ok = multiply_coefficients(result, base, product);
                if(ok) result = std::move(product);
            }
        }else{
            ok = false;
        }
        if(!ok){ failed.insert(id); return false; }
        trim(result);
        parsed_memo.emplace(id, result);
        return true;
    };

    coefficients_t coefficients;
    if(!parse(parse, expression.root_, coefficients))
        throw std::invalid_argument(
            "solve currently supports polynomials of degree at most four");
    trim(coefficients);
    if(require_exact_coefficients){
        for(uint32_t coefficient : coefficients){
            bool approximate = false;
            std::unordered_set<uint32_t> visited;
            std::vector<uint32_t> pending(1, coefficient);
            while(!pending.empty() && !approximate){
                uint32_t id = pending.back();
                pending.pop_back();
                if(!visited.insert(id).second) continue;
                const exact_node &current = storage_->node(id);
                if(current.op == exact_opcode::value &&
                   storage_->values[current.payload].is_approximate()){
                    approximate = true;
                    break;
                }
                const uint32_t *args = storage_->children(current);
                pending.insert(pending.end(), args,
                               args + current.operand_count);
            }
            if(approximate)
                throw std::invalid_argument(
                    "exact_solve requires exact polynomial coefficients");
        }
    }
    if(coefficients.empty())
        throw std::domain_error("equation has infinitely many solutions");
    if(coefficients.size() == 1)
        return exact_expr(storage_, storage_->intern_compound(
            exact_opcode::expression_list, {}));

    // Before invoking Cardano or Ferrari, remove an easy integer linear
    // factor.  This keeps reducible quartics such as
    // x^4+2*x^3-2*x-4 = (x+2)(x^3-2) out of the much larger quartic formula.
    if(coefficients.size() >= 4){
        std::vector<int64_t> integer_coefficients;
        integer_coefficients.reserve(coefficients.size());
        bool integer_polynomial = true;
        for(uint32_t coefficient : coefficients){
            const exact_node &node = storage_->node(coefficient);
            int64_t value = 0;
            if(node.op != exact_opcode::value ||
               !integer_i64(storage_->values[node.payload], value)){
                integer_polynomial = false;
                break;
            }
            integer_coefficients.push_back(value);
        }
        int64_t leading = integer_polynomial
            ? integer_coefficients.back() : 0;
        uint64_t constant_magnitude = integer_polynomial
            ? (integer_coefficients[0] < 0
                ? (uint64_t)0 - (uint64_t)integer_coefficients[0]
                : (uint64_t)integer_coefficients[0]) : 0;
        if((leading == 1 || leading == -1) &&
           constant_magnitude > 0 && constant_magnitude <= 1000000){
            std::vector<int64_t> candidates;
            for(uint64_t divisor = 1;
                divisor <= constant_magnitude / divisor; ++divisor){
                if(constant_magnitude % divisor) continue;
                candidates.push_back((int64_t)divisor);
                candidates.push_back(-(int64_t)divisor);
                uint64_t paired = constant_magnitude / divisor;
                if(paired != divisor){
                    candidates.push_back((int64_t)paired);
                    candidates.push_back(-(int64_t)paired);
                }
            }
            for(int64_t candidate : candidates){
                exact_value evaluation(0);
                for(size_t i = integer_coefficients.size(); i-- > 0;)
                    evaluation = evaluation * exact_value(candidate) +
                                 exact_value(integer_coefficients[i]);
                if(!evaluation.is_zero()) continue;

                size_t degree = integer_coefficients.size() - 1;
                std::vector<exact_value> quotient(degree, exact_value(0));
                quotient[degree - 1] = exact_value(integer_coefficients[degree]);
                for(size_t i = degree - 1; i > 0; --i)
                    quotient[i - 1] = exact_value(integer_coefficients[i]) +
                        exact_value(candidate) * quotient[i];
                std::vector<uint32_t> quotient_terms;
                for(size_t i = 0; i < quotient.size(); ++i){
                    if(quotient[i].is_zero()) continue;
                    uint32_t coefficient = storage_->intern_value(quotient[i]);
                    if(i == 0) quotient_terms.push_back(coefficient);
                    else quotient_terms.push_back(storage_->make_multiply({
                        coefficient, i == 1 ? variable : storage_->make_power(
                            variable, storage_->intern_value(
                                exact_value((uint64_t)i)))}));
                }
                exact_expr remaining = solve_polynomial_impl(
                    exact_expr(storage_, storage_->make_add(
                        std::move(quotient_terms))), variables,
                    require_exact_coefficients);
                const exact_node &remaining_list = storage_->node(remaining.root_);
                const uint32_t *remaining_data = storage_->children(remaining_list);
                std::vector<uint32_t> remaining_roots(
                    remaining_data,
                    remaining_data + remaining_list.operand_count);
                std::vector<uint32_t> roots;
                roots.push_back(storage_->intern_value(exact_value(candidate)));
                roots.insert(roots.end(), remaining_roots.begin(),
                             remaining_roots.end());
                return exact_expr(storage_, storage_->intern_compound(
                    exact_opcode::expression_list, roots));
            }
        }
    }

    uint32_t minus_one = storage_->intern_value(exact_value(-1));
    auto integer = [&](int64_t value){
        return storage_->intern_value(exact_value(value));
    };
    auto divide = [&](uint32_t numerator, uint32_t denominator){
        return storage_->make_multiply({numerator, storage_->make_power(
            denominator, minus_one)});
    };
    auto negate = [&](uint32_t value){
        const exact_node &node = storage_->node(value);
        if(node.op == exact_opcode::add){
            const uint32_t *data = storage_->children(node);
            std::vector<uint32_t> terms(data, data + node.operand_count);
            for(uint32_t &term : terms)
                term = storage_->make_multiply({minus_one, term});
            return storage_->make_add(std::move(terms));
        }
        return storage_->make_multiply({minus_one, value});
    };
    auto square = [&](uint32_t value){
        return storage_->make_power(value, integer(2));
    };
    auto cube = [&](uint32_t value){
        return storage_->make_power(value, integer(3));
    };
    auto rational_power = [&](uint32_t value, uint64_t numerator,
                              uint64_t denominator){
        return storage_->make_power(value, storage_->intern_value(exact_value(
            precq_t(precn_t(numerator), precn_t(denominator)))));
    };
    auto cube_root = [&](uint32_t value){
        const exact_node &node = storage_->node(value);
        if(node.op == exact_opcode::value){
            exact_value root;
            if(exact_cube_root(storage_->values[node.payload], root))
                return storage_->intern_value(std::move(root));
        }
        return rational_power(value, 1, 3);
    };
    auto append_unique = [&](std::vector<uint32_t> &roots, uint32_t root){
        if(std::find(roots.begin(), roots.end(), root) == roots.end())
            roots.push_back(root);
    };
    uint32_t c = coefficients[0];
    uint32_t b = coefficients[1];
    std::vector<uint32_t> solutions;
    if(coefficients.size() == 2){
        solutions.push_back(divide(negate(c), b));
    }else if(coefficients.size() == 3){
        uint32_t a = coefficients[2];
        uint32_t discriminant = storage_->make_add({
            storage_->make_multiply({b, b}),
            storage_->make_multiply({
                storage_->intern_value(exact_value(-4)), a, c})});
        exact_expander discriminant_expander(*storage_, 100000);
        discriminant = discriminant_expander.expand(discriminant);
        uint32_t root = storage_->make_sqrt(discriminant);
        uint32_t negative_b = storage_->make_multiply({minus_one, b});
        uint32_t denominator = storage_->make_multiply({
            storage_->intern_value(exact_value(2)), a});
        uint32_t first = divide(storage_->make_add({
            negative_b, storage_->make_multiply({minus_one, root})}), denominator);
        solutions.push_back(first);
        if(!is_zero(discriminant))
            solutions.push_back(divide(storage_->make_add({negative_b, root}),
                                       denominator));
    }else if(coefficients.size() == 4){
        // Cardano in discriminant form.  The two non-real cube roots of unity
        // are represented exactly with i*sqrt(3), so all three roots remain
        // ordinary exact_expr DAGs.
        uint32_t A = coefficients[3];
        uint32_t B = coefficients[2];
        uint32_t Ccoef = coefficients[1];
        uint32_t D = coefficients[0];
        if(is_zero(B) && is_zero(Ccoef)){
            uint32_t radicand = divide(negate(D), A);
            uint32_t root;
            const exact_node &radicand_node = storage_->node(radicand);
            if(radicand_node.op == exact_opcode::value &&
               storage_->values[radicand_node.payload].is_negative())
                root = negate(cube_root(negate(radicand)));
            else root = cube_root(radicand);
            if(is_zero(radicand)){
                solutions.push_back(root);
            }else{
                uint32_t sqrt_three_i = storage_->make_sqrt(integer(-3));
                uint32_t omega = divide(
                    storage_->make_add({minus_one, sqrt_three_i}), integer(2));
                uint32_t omega2 = divide(
                    storage_->make_add({minus_one, negate(sqrt_three_i)}),
                    integer(2));
                solutions.push_back(root);
                solutions.push_back(storage_->make_multiply({root, omega}));
                solutions.push_back(storage_->make_multiply({root, omega2}));
            }
        }else{
        uint32_t delta0 = storage_->make_add({square(B),
            negate(storage_->make_multiply({integer(3), A, Ccoef}))});
        uint32_t delta1 = storage_->make_add({
            storage_->make_multiply({integer(2), cube(B)}),
            negate(storage_->make_multiply({integer(9), A, B, Ccoef})),
            storage_->make_multiply({integer(27), square(A), D})});
        uint32_t radical = storage_->make_sqrt(storage_->make_add({
            square(delta1),
            negate(storage_->make_multiply({integer(4), cube(delta0)}))}));
        uint32_t carg = divide(storage_->make_add({delta1, radical}), integer(2));
        if(is_zero(carg))
            carg = divide(storage_->make_add({delta1, negate(radical)}), integer(2));
        uint32_t C = cube_root(carg);
        uint32_t denominator = storage_->make_multiply({integer(3), A});
        if(is_zero(carg) && is_zero(delta0)){
            solutions.push_back(divide(negate(B), denominator));
        }else{
            uint32_t sqrt_three_i = storage_->make_sqrt(integer(-3));
            uint32_t omega = divide(storage_->make_add({minus_one, sqrt_three_i}),
                                    integer(2));
            uint32_t omega2 = divide(storage_->make_add({minus_one,
                                      negate(sqrt_three_i)}), integer(2));
            const uint32_t units[] = {one, omega, omega2};
            for(uint32_t unit : units){
                uint32_t uC = storage_->make_multiply({unit, C});
                uint32_t correction = is_zero(delta0) ? zero : divide(delta0, uC);
                uint32_t numerator = negate(storage_->make_add({B, uC, correction}));
                append_unique(solutions, divide(numerator, denominator));
            }
        }
        }
    }else{
        // Ferrari after shifting x = y-b/(4a).  beta==0 is solved as a
        // quadratic in y^2, avoiding the otherwise singular beta/W term.
        uint32_t A = coefficients[4];
        uint32_t B = coefficients[3];
        uint32_t Ccoef = coefficients[2];
        uint32_t D = coefficients[1];
        uint32_t E = coefficients[0];
        uint32_t a2 = square(A);
        uint32_t a3 = cube(A);
        uint32_t a4 = square(a2);
        uint32_t b2 = square(B);
        uint32_t b3 = cube(B);
        uint32_t b4 = square(b2);
        uint32_t alpha = storage_->make_add({
            negate(divide(storage_->make_multiply({integer(3), b2}),
                          storage_->make_multiply({integer(8), a2}))),
            divide(Ccoef, A)});
        uint32_t beta = storage_->make_add({
            divide(b3, storage_->make_multiply({integer(8), a3})),
            negate(divide(storage_->make_multiply({B, Ccoef}),
                          storage_->make_multiply({integer(2), a2}))),
            divide(D, A)});
        uint32_t gamma = storage_->make_add({
            negate(divide(storage_->make_multiply({integer(3), b4}),
                          storage_->make_multiply({integer(256), a4}))),
            divide(storage_->make_multiply({b2, Ccoef}),
                   storage_->make_multiply({integer(16), a3})),
            negate(divide(storage_->make_multiply({B, D}),
                          storage_->make_multiply({integer(4), a2}))),
            divide(E, A)});
        uint32_t shift = negate(divide(B,
            storage_->make_multiply({integer(4), A})));

        if(is_zero(beta)){
            uint32_t inner = storage_->make_sqrt(storage_->make_add({
                square(alpha), negate(storage_->make_multiply({integer(4), gamma}))}));
            const uint32_t signs[] = {one, minus_one};
            for(uint32_t inner_sign : signs){
                uint32_t radicand = divide(storage_->make_add({negate(alpha),
                    storage_->make_multiply({inner_sign, inner})}), integer(2));
                uint32_t root = storage_->make_sqrt(radicand);
                append_unique(solutions, storage_->make_add({shift, root}));
                if(!is_zero(root))
                    append_unique(solutions, storage_->make_add({shift, negate(root)}));
            }
        }else{
            uint32_t P = storage_->make_add({
                negate(divide(square(alpha), integer(12))), negate(gamma)});
            uint32_t Q = storage_->make_add({
                negate(divide(cube(alpha), integer(108))),
                divide(storage_->make_multiply({alpha, gamma}), integer(3)),
                negate(divide(square(beta), integer(8)))});
            uint32_t R = storage_->make_add({negate(divide(Q, integer(2))),
                storage_->make_sqrt(storage_->make_add({
                    divide(square(Q), integer(4)),
                    divide(cube(P), integer(27))}))});
            uint32_t U = cube_root(R);
            uint32_t y;
            if(is_zero(R)){
                y = storage_->make_add({
                    negate(divide(storage_->make_multiply({integer(5), alpha}),
                                  integer(6))),
                    negate(cube_root(Q))});
            }else{
                y = storage_->make_add({
                    negate(divide(storage_->make_multiply({integer(5), alpha}),
                                  integer(6))), U,
                    negate(divide(P, storage_->make_multiply({integer(3), U})))});
            }
            uint32_t W = storage_->make_sqrt(storage_->make_add({alpha,
                storage_->make_multiply({integer(2), y})}));
            const int signs[] = {1, -1};
            for(int sign : signs){
                uint32_t signed_w = sign > 0 ? W : negate(W);
                uint32_t beta_term = divide(
                    storage_->make_multiply({integer(2 * sign), beta}), W);
                uint32_t inner = storage_->make_sqrt(negate(storage_->make_add({
                    storage_->make_multiply({integer(3), alpha}),
                    storage_->make_multiply({integer(2), y}), beta_term})));
                append_unique(solutions, storage_->make_add({shift,
                    divide(storage_->make_add({signed_w, inner}), integer(2))}));
                append_unique(solutions, storage_->make_add({shift,
                    divide(storage_->make_add({signed_w, negate(inner)}), integer(2))}));
            }
        }
    }
    return exact_expr(storage_, storage_->intern_compound(
        exact_opcode::expression_list, solutions));
}

exact_expr exact_context::solve_system_impl(
        const std::vector<exact_expr> &equations,
        const std::vector<exact_expr> &variables,
        bool require_exact_coefficients){
    if(equations.empty())
        throw std::invalid_argument("solve requires at least one equation");
    if(variables.empty())
        throw std::invalid_argument("solve requires at least one variable");
    for(const exact_expr &equation : equations)
        if(!equation.valid() || equation.storage_ != storage_)
            throw std::invalid_argument("equations belong to a different context");
    std::vector<uint32_t> variable_ids;
    variable_ids.reserve(variables.size());
    for(const exact_expr &variable : variables){
        if(!variable.valid() || variable.storage_ != storage_ ||
           storage_->node(variable.root_).op != exact_opcode::symbol)
            throw std::invalid_argument("solve variables must be symbols");
        if(std::find(variable_ids.begin(), variable_ids.end(), variable.root_) !=
           variable_ids.end())
            throw std::invalid_argument("solve variables must be distinct");
        variable_ids.push_back(variable.root_);
    }

    // A linear system can have symbolic exact coefficients (for example
    // x + y - a = 0).  The Groebner-style path below intentionally requires
    // rational coefficients, so handle this common case with symbolic
    // Gaussian elimination first.
    if(equations.size() == variables.size() && variables.size() > 1){
        const exact_expr zero_expr = integer(0);
        auto is_zero_expr = [&](const exact_expr &value){
            exact_expr reduced = simplify(value);
            const exact_node &node = storage_->node(reduced.root_);
            return node.op == exact_opcode::value &&
                storage_->values[node.payload].is_zero();
        };
        std::vector<std::vector<exact_expr>> matrix(
            equations.size(), std::vector<exact_expr>(variables.size() + 1,
                                                       zero_expr));
        bool linear = true;
        for(size_t row = 0; row < equations.size() && linear; ++row){
            exact_expr constant = equations[row];
            for(const exact_expr &variable : variables)
                constant = substitute(constant, variable, zero_expr);
            matrix[row].back() = simplify(constant);
            for(size_t column = 0; column < variables.size(); ++column){
                exact_expr coefficient = differentiate(
                    equations[row], variables[column]);
                for(const exact_expr &variable : variables)
                    coefficient = substitute(coefficient, variable, zero_expr);
                coefficient = simplify(coefficient);
                matrix[row][column] = coefficient;
            }
        }
        if(linear){
            bool solved = true;
            for(size_t column = 0; column < variables.size(); ++column){
                size_t pivot = column;
                while(pivot < equations.size() &&
                      is_zero_expr(matrix[pivot][column])) ++pivot;
                if(pivot == equations.size()) { solved = false; break; }
                std::swap(matrix[pivot], matrix[column]);
                exact_expr divisor = matrix[column][column];
                for(size_t j = column; j <= variables.size(); ++j)
                    matrix[column][j] = simplify(matrix[column][j] / divisor);
                for(size_t row = 0; row < equations.size(); ++row){
                    if(row == column) continue;
                    exact_expr factor = matrix[row][column];
                    if(is_zero_expr(factor)) continue;
                    for(size_t j = column; j <= variables.size(); ++j)
                        matrix[row][j] = simplify(
                            matrix[row][j] - factor * matrix[column][j]);
                }
            }
            if(solved){
                std::vector<uint32_t> rules;
                for(size_t i = 0; i < variables.size(); ++i){
                    if(!is_zero_expr(matrix[i][i] - integer(1))){
                        solved = false;
                        break;
                    }
                    exact_expr solution = simplify(-matrix[i].back());
                    rules.push_back(storage_->intern_compound(
                        exact_opcode::rule,
                        {variable_ids[i], solution.root_}));
                }
                if(solved){
                    uint32_t row = storage_->intern_compound(
                        exact_opcode::expression_list, rules);
                    return exact_expr(storage_, storage_->intern_compound(
                        exact_opcode::expression_list, {row}));
                }
            }
        }
    }
    if(variables.size() == 1 && equations.size() == 1){
        exact_expr roots = solve_polynomial_impl(
            equations[0], variables, require_exact_coefficients);
        const exact_node &root_list = storage_->node(roots.root_);
        const uint32_t *root_data = storage_->children(root_list);
        std::vector<uint32_t> root_ids(
            root_data, root_data + root_list.operand_count);
        std::vector<uint32_t> solutions;
        solutions.reserve(root_ids.size());
        for(uint32_t root : root_ids){
            uint32_t rule = storage_->intern_compound(
                exact_opcode::rule, {variable_ids[0], root});
            solutions.push_back(storage_->intern_compound(
                exact_opcode::expression_list, {rule}));
        }
        return exact_expr(storage_, storage_->intern_compound(
            exact_opcode::expression_list, solutions));
    }
    const std::vector<uint32_t> requested_variable_ids = variable_ids;
    std::vector<exact_expr> solver_variables = variables;
    std::reverse(variable_ids.begin(), variable_ids.end());
    std::reverse(solver_variables.begin(), solver_variables.end());

    using monomial = std::vector<uint16_t>;
    struct lex_order{
        bool operator()(const monomial &a, const monomial &b) const{
            return std::lexicographical_compare(a.begin(), a.end(),
                                                b.begin(), b.end());
        }
    };
    using polynomial = std::map<monomial, exact_value, lex_order>;
    const size_t maximum_terms = 20000;
    auto add_term = [](polynomial &p, const monomial &m, const exact_value &c){
        if(c.is_zero()) return;
        auto found = p.find(m);
        if(found == p.end()) p.emplace(m, c);
        else{
            found->second = found->second + c;
            if(found->second.is_zero()) p.erase(found);
        }
    };
    auto multiply = [&](const polynomial &a, const polynomial &b,
                        polynomial &out){
        out.clear();
        if(a.empty() || b.empty()) return true;
        if(a.size() > maximum_terms / b.size()) return false;
        for(const auto &left : a) for(const auto &right : b){
            monomial m(variables.size());
            for(size_t i = 0; i < m.size(); ++i){
                uint32_t exponent = (uint32_t)left.first[i] + right.first[i];
                if(exponent > UINT16_MAX) return false;
                m[i] = (uint16_t)exponent;
            }
            add_term(out, m, left.second * right.second);
            if(out.size() > maximum_terms) return false;
        }
        return true;
    };
    std::unordered_map<uint32_t, polynomial> parse_memo;
    std::unordered_set<uint32_t> parse_failed;
    auto parse = [&](auto &&self, uint32_t id, polynomial &out) -> bool{
        auto cached = parse_memo.find(id);
        if(cached != parse_memo.end()){ out = cached->second; return true; }
        if(parse_failed.count(id)) return false;
        exact_node node = storage_->node(id);
        const uint32_t *args = storage_->children(node);
        bool ok = true;
        out.clear();
        if(node.op == exact_opcode::value){
            const exact_value &coefficient = storage_->values[node.payload];
            ok = !coefficient.is_approximate() || !require_exact_coefficients;
            if(ok)
                add_term(out, monomial(variables.size()), coefficient);
        }else if(node.op == exact_opcode::symbol){
            auto found = std::find(variable_ids.begin(), variable_ids.end(), id);
            if(found == variable_ids.end()) ok = false;
            else{
                monomial m(variables.size());
                m[(size_t)(found - variable_ids.begin())] = 1;
                add_term(out, m, exact_value(1));
            }
        }else if(node.op == exact_opcode::add){
            for(size_t i = 0; i < node.operand_count && ok; ++i){
                polynomial child;
                ok = self(self, args[i], child);
                if(ok) for(const auto &term : child)
                    add_term(out, term.first, term.second);
            }
        }else if(node.op == exact_opcode::multiply){
            out.emplace(monomial(variables.size()), exact_value(1));
            for(size_t i = 0; i < node.operand_count && ok; ++i){
                polynomial child, product;
                ok = self(self, args[i], child) && multiply(out, child, product);
                if(ok) out.swap(product);
            }
        }else if(node.op == exact_opcode::power){
            exact_node exponent_node = storage_->node(args[1]);
            int64_t exponent = -1;
            ok = exponent_node.op == exact_opcode::value &&
                 integer_i64(storage_->values[exponent_node.payload], exponent) &&
                 exponent >= 0 && exponent <= 4096;
            polynomial base;
            if(ok) ok = self(self, args[0], base);
            out.emplace(monomial(variables.size()), exact_value(1));
            uint64_t bits = (uint64_t)std::max<int64_t>(exponent, 0);
            while(bits && ok){
                if(bits & 1){
                    polynomial product;
                    ok = multiply(out, base, product);
                    if(ok) out.swap(product);
                }
                bits >>= 1;
                if(bits){
                    polynomial square;
                    ok = multiply(base, base, square);
                    if(ok) base.swap(square);
                }
            }
        }else ok = false;
        if(!ok){ parse_failed.insert(id); return false; }
        parse_memo.emplace(id, out);
        return true;
    };

    std::vector<polynomial> input;
    for(const exact_expr &equation : equations){
        polynomial p;
        if(!parse(parse, equation.root_, p)){
            if(!require_exact_coefficients)
                throw std::invalid_argument(
                    "system solving requires polynomial expressions");

            // Symbolic coefficient fallback: compute a Groebner basis over
            // exact_expr coefficients, then solve its triangular univariate
            // members and substitute the roots into the remaining equations.
            exact_expr basis_expr = groebner(equations, variables);
            std::vector<exact_expr> basis;
            for(size_t i = 0; i < basis_expr.operand_count(); ++i)
                basis.push_back(basis_expr.operand(i));
            struct candidate{ std::vector<exact_expr> values; };
            std::vector<candidate> candidates(1);
            for(size_t column = 0; column < variables.size(); ++column){
                std::vector<candidate> next;
                for(const candidate &state : candidates){
                    exact_expr relation;
                    for(const exact_expr &raw : basis){
                        exact_expr reduced = raw;
                        for(size_t k = 0; k < state.values.size(); ++k)
                            reduced = substitute(reduced, variables[k],
                                                 state.values[k]);
                        if(!is_polynomial(reduced, {variables[column]})) continue;
                        exact_expr derivative = simplify(differentiate(
                            reduced, variables[column]));
                        const exact_node &dn = storage_->node(derivative.root_);
                        bool nonconstant = !(dn.op == exact_opcode::value &&
                            storage_->values[dn.payload].is_zero());
                        if(nonconstant){ relation = reduced; break; }
                    }
                    if(!relation.valid()) continue;
                    exact_expr roots = solve_polynomial_impl(
                        relation, {variables[column]}, true);
                    for(size_t r = 0; r < roots.operand_count(); ++r){
                        candidate child = state;
                        child.values.push_back(roots.operand(r));
                        next.push_back(std::move(child));
                    }
                }
                candidates = std::move(next);
                if(candidates.empty()) break;
            }
            std::vector<uint32_t> maps;
            for(const candidate &state : candidates){
                if(state.values.size() != variables.size()) continue;
                bool valid_solution = true;
                for(const exact_expr &original : equations){
                    exact_expr value = original;
                    for(size_t k = 0; k < variables.size(); ++k)
                        value = substitute(value, variables[k], state.values[k]);
                    exact_expr reduced = simplify(value);
                    const exact_node &node = storage_->node(reduced.root_);
                    if(node.op != exact_opcode::value ||
                       !storage_->values[node.payload].is_zero()){
                        valid_solution = false; break;
                    }
                }
                if(!valid_solution) continue;
                std::vector<uint32_t> rules;
                for(size_t k = 0; k < variables.size(); ++k)
                    rules.push_back(storage_->intern_compound(
                        exact_opcode::rule,
                        {requested_variable_ids[k], state.values[k].root_}));
                maps.push_back(storage_->intern_compound(
                    exact_opcode::expression_list, rules));
            }
            return exact_expr(storage_, storage_->intern_compound(
                exact_opcode::expression_list, maps));
        }
        if(!p.empty()) input.push_back(std::move(p));
    }
    auto make_list = [&](const std::vector<uint32_t> &items){
        return storage_->intern_compound(exact_opcode::expression_list, items);
    };
    auto make_solution_map = [&](const std::vector<uint32_t> &values){
        if(values.size() != variable_ids.size())
            throw std::logic_error("solution has the wrong number of values");
        std::vector<uint32_t> rules;
        rules.reserve(values.size());
        for(size_t i = 0; i < requested_variable_ids.size(); ++i){
            auto found = std::find(variable_ids.begin(), variable_ids.end(),
                                   requested_variable_ids[i]);
            size_t value_index = (size_t)(found - variable_ids.begin());
            rules.push_back(storage_->intern_compound(
                exact_opcode::rule,
                {requested_variable_ids[i], values[value_index]}));
        }
        return make_list(rules);
    };
    if(input.empty())
        throw std::domain_error("equation system has infinitely many solutions");

    // Linear systems are both common and much cheaper to solve directly than
    // through Buchberger.  RREF also gives useful parametric solutions.
    bool linear = true;
    bool approximate_coefficients = false;
    for(const polynomial &p : input) for(const auto &term : p){
        if(term.second.is_approximate()) approximate_coefficients = true;
        size_t degree = 0;
        for(uint16_t e : term.first) degree += e;
        if(degree > 1) linear = false;
    }
    if(linear){
        const size_t rows = input.size(), columns = variables.size();
        std::vector<std::vector<exact_value>> matrix(
            rows, std::vector<exact_value>(columns + 1, exact_value(0)));
        monomial constant(columns);
        for(size_t r = 0; r < rows; ++r) for(const auto &term : input[r]){
            if(term.first == constant) matrix[r][columns] = -term.second;
            else for(size_t c = 0; c < columns; ++c)
                if(term.first[c] == 1) matrix[r][c] = term.second;
        }
        std::vector<int> pivot_column(rows, -1);
        size_t pivot_row = 0;
        for(size_t column = 0; column < columns && pivot_row < rows; ++column){
            size_t selected = pivot_row;
            while(selected < rows && matrix[selected][column].is_zero()) ++selected;
            if(selected == rows) continue;
            std::swap(matrix[selected], matrix[pivot_row]);
            exact_value pivot = matrix[pivot_row][column];
            for(size_t c = column; c <= columns; ++c)
                matrix[pivot_row][c] = matrix[pivot_row][c] / pivot;
            for(size_t r = 0; r < rows; ++r){
                if(r == pivot_row || matrix[r][column].is_zero()) continue;
                exact_value factor = matrix[r][column];
                for(size_t c = column; c <= columns; ++c)
                    matrix[r][c] = matrix[r][c] - factor * matrix[pivot_row][c];
            }
            pivot_column[pivot_row++] = (int)column;
        }
        for(size_t r = pivot_row; r < rows; ++r){
            bool all_zero = true;
            for(size_t c = 0; c < columns; ++c)
                if(!matrix[r][c].is_zero()) all_zero = false;
            if(all_zero && !matrix[r][columns].is_zero())
                return exact_expr(storage_, make_list({}));
        }
        std::vector<bool> pivoted(columns, false);
        for(size_t r = 0; r < pivot_row; ++r)
            pivoted[(size_t)pivot_column[r]] = true;

        // Free variables become fresh, parseable symbols instead of mapping
        // back to themselves.  Only names reachable from this system matter
        // for capture; unrelated symbols elsewhere in the arena are harmless.
        std::unordered_set<std::string> occupied_names;
        std::unordered_set<uint32_t> visited_symbols;
        std::vector<uint32_t> pending_symbols;
        for(const exact_expr &equation : equations)
            pending_symbols.push_back(equation.root_);
        pending_symbols.insert(pending_symbols.end(), variable_ids.begin(),
                               variable_ids.end());
        while(!pending_symbols.empty()){
            uint32_t id = pending_symbols.back();
            pending_symbols.pop_back();
            if(!visited_symbols.insert(id).second) continue;
            const exact_node &node = storage_->node(id);
            if(node.op == exact_opcode::symbol)
                occupied_names.insert(storage_->symbols[node.payload]);
            const uint32_t *children = storage_->children(node);
            pending_symbols.insert(pending_symbols.end(), children,
                                   children + node.operand_count);
        }
        std::vector<uint32_t> values(columns, UINT32_MAX);
        size_t parameter_index = 1;
        for(size_t column = 0; column < columns; ++column){
            if(pivoted[column]) continue;
            std::string name;
            do{
                name = "_solve_t" + std::to_string(parameter_index++);
            }while(occupied_names.count(name));
            occupied_names.insert(name);
            values[column] = storage_->intern_symbol(name);
        }
        for(size_t r = pivot_row; r-- > 0;){
            size_t pivot = (size_t)pivot_column[r];
            std::vector<uint32_t> terms;
            terms.push_back(storage_->intern_value(matrix[r][columns]));
            for(size_t c = pivot + 1; c < columns; ++c){
                if(matrix[r][c].is_zero()) continue;
                terms.push_back(storage_->make_multiply({
                    storage_->intern_value(-matrix[r][c]), values[c]}));
            }
            values[pivot] = storage_->make_add(std::move(terms));
        }
        return exact_expr(storage_, make_list({make_solution_map(values)}));
    }
    if(approximate_coefficients)
        throw std::invalid_argument(
            "nonlinear approximate systems require a numerical solver");

    auto monomial_divides = [](const monomial &a, const monomial &b){
        for(size_t i = 0; i < a.size(); ++i) if(a[i] > b[i]) return false;
        return true;
    };
    auto monomial_difference = [](const monomial &a, const monomial &b){
        monomial result(a.size());
        for(size_t i = 0; i < a.size(); ++i) result[i] = a[i] - b[i];
        return result;
    };
    auto scaled_add = [&](polynomial &target, const polynomial &source,
                          const monomial &shift, const exact_value &scale){
        for(const auto &term : source){
            monomial m(term.first.size());
            for(size_t i = 0; i < m.size(); ++i)
                m[i] = term.first[i] + shift[i];
            add_term(target, m, term.second * scale);
        }
    };
    auto make_monic = [](polynomial &p){
        exact_value lead = p.rbegin()->second;
        for(auto &term : p) term.second = term.second / lead;
    };
    auto reduce = [&](polynomial p, const std::vector<polynomial> &basis){
        polynomial remainder;
        size_t steps = 0;
        while(!p.empty()){
            if(++steps > 200000)
                throw std::runtime_error("Groebner reduction budget exceeded");
            bool reduced = false;
            auto lead = std::prev(p.end());
            for(const polynomial &divisor : basis){
                if(divisor.empty() ||
                   !monomial_divides(divisor.rbegin()->first, lead->first)) continue;
                monomial shift = monomial_difference(
                    lead->first, divisor.rbegin()->first);
                exact_value scale = -(lead->second / divisor.rbegin()->second);
                scaled_add(p, divisor, shift, scale);
                reduced = true;
                break;
            }
            if(!reduced){
                add_term(remainder, lead->first, lead->second);
                p.erase(lead);
            }
        }
        return remainder;
    };
    std::vector<polynomial> basis;
    for(polynomial p : input){
        p = reduce(std::move(p), basis);
        if(!p.empty()){ make_monic(p); basis.push_back(std::move(p)); }
    }
    std::vector<std::pair<size_t, size_t>> pairs;
    for(size_t i = 0; i < basis.size(); ++i)
        for(size_t j = 0; j < i; ++j) pairs.emplace_back(j, i);
    size_t pair_index = 0;
    while(pair_index < pairs.size()){
        if(pairs.size() > 50000 || basis.size() > 256)
            throw std::runtime_error("Groebner basis budget exceeded");
        size_t i = pairs[pair_index].first, j = pairs[pair_index++].second;
        const monomial &a = basis[i].rbegin()->first;
        const monomial &b = basis[j].rbegin()->first;
        monomial lcm(a.size());
        bool relatively_prime = true;
        for(size_t k = 0; k < a.size(); ++k){
            lcm[k] = std::max(a[k], b[k]);
            if(a[k] && b[k]) relatively_prime = false;
        }
        if(relatively_prime) continue;
        polynomial s;
        scaled_add(s, basis[i], monomial_difference(lcm, a),
                   exact_value(1) / basis[i].rbegin()->second);
        scaled_add(s, basis[j], monomial_difference(lcm, b),
                   exact_value(-1) / basis[j].rbegin()->second);
        s = reduce(std::move(s), basis);
        if(s.empty()) continue;
        make_monic(s);
        size_t next = basis.size();
        for(size_t k = 0; k < next; ++k) pairs.emplace_back(k, next);
        basis.push_back(std::move(s));
    }
    for(const polynomial &p : basis)
        if(p.size() == 1 && p.begin()->first == monomial(variables.size()))
            return exact_expr(storage_, make_list({}));

    auto polynomial_expression = [&](const polynomial &p){
        std::vector<uint32_t> terms;
        for(const auto &term : p){
            std::vector<uint32_t> factors;
            factors.push_back(storage_->intern_value(term.second));
            for(size_t i = 0; i < variables.size(); ++i) if(term.first[i])
                factors.push_back(term.first[i] == 1 ? variable_ids[i] :
                    storage_->make_power(variable_ids[i], storage_->intern_value(
                        exact_value((uint64_t)term.first[i]))));
            terms.push_back(storage_->make_multiply(std::move(factors)));
        }
        return storage_->make_add(std::move(terms));
    };
    std::vector<uint32_t> basis_expressions;
    for(const polynomial &p : basis)
        basis_expressions.push_back(polynomial_expression(p));
    std::vector<std::vector<uint32_t>> solutions;
    std::vector<uint32_t> assignment(variables.size(), UINT32_MAX);
    auto triangular_solve = [&](auto &&self, int index) -> void{
        if(index < 0){ solutions.push_back(assignment); return; }
        const polynomial *selected = nullptr;
        size_t selected_degree = SIZE_MAX;
        for(const polynomial &p : basis){
            size_t degree = 0;
            bool suitable = true;
            for(const auto &term : p){
                for(int i = 0; i < index; ++i)
                    if(term.first[(size_t)i]) suitable = false;
                degree = std::max<size_t>(degree, term.first[(size_t)index]);
            }
            if(suitable && degree > 0 && degree <= 4 && degree < selected_degree){
                selected = &p;
                selected_degree = degree;
            }
        }
        if(!selected)
            throw std::domain_error(
                "Groebner basis is not a zero-dimensional triangular system of degree <= 4");
        uint32_t equation_id = polynomial_expression(*selected);
        exact_expr equation(storage_, equation_id);
        for(size_t i = (size_t)index + 1; i < variables.size(); ++i)
            equation = substitute(equation, solver_variables[i],
                                  exact_expr(storage_, assignment[i]));
        exact_expr roots = solve_polynomial_impl(
            equation, {solver_variables[(size_t)index]},
            require_exact_coefficients);
        exact_node root_list = storage_->node(roots.root_);
        const uint32_t *data = storage_->children(root_list);
        std::vector<uint32_t> root_ids(data, data + root_list.operand_count);
        for(uint32_t root : root_ids){
            assignment[(size_t)index] = root;
            self(self, index - 1);
        }
        assignment[(size_t)index] = UINT32_MAX;
    };
    triangular_solve(triangular_solve, (int)variables.size() - 1);
    std::vector<uint32_t> rows;
    for(const auto &solution : solutions)
        rows.push_back(make_solution_map(solution));
    return exact_expr(storage_, make_list(rows));
}

exact_expr exact_context::exact_solve(
        const exact_expr &expression,
        const std::vector<exact_expr> &variables){
    if(variables.size() == 1 && expression.valid() &&
       expression.storage_ == storage_ &&
       storage_->node(expression.root_).operand_count == 1){
        exact_opcode operation = storage_->node(expression.root_).op;
        if((operation == exact_opcode::sine ||
            operation == exact_opcode::cosine ||
            operation == exact_opcode::tangent) &&
           storage_->children(storage_->node(expression.root_))[0] ==
               variables[0].root_){
            std::string parameter_name = "n";
            size_t parameter_suffix = 1;
            while(std::find(storage_->symbols.begin(), storage_->symbols.end(),
                            parameter_name) != storage_->symbols.end())
                parameter_name = "n" + std::to_string(parameter_suffix++);
            exact_expr parameter = symbol(parameter_name);
            exact_expr family;
            if(operation == exact_opcode::cosine){
                family = divide(
                    (integer(2) * parameter + integer(1)) * pi(),
                    integer(2));
            }else{
                family = parameter * pi();
            }
            exact_expr rule = exact_expr(storage_, storage_->intern_compound(
                exact_opcode::rule, {variables[0].root_, family.root_}));
            exact_expr row = exact_expr(storage_, storage_->intern_compound(
                exact_opcode::expression_list, {rule.root_}));
            return exact_expr(storage_, storage_->intern_compound(
                exact_opcode::expression_list, {row.root_}));
        }
    }
    return solve_polynomial_impl(expression, variables, true);
}

exact_expr exact_context::solve_numeric_system_impl(
        const std::vector<exact_expr> &equations,
        const std::vector<exact_expr> &variables,
        double precision_bits){
    if(equations.empty() || variables.empty())
        throw std::invalid_argument("numerical solve requires equations and variables");
    if(equations.size() != variables.size())
        throw std::invalid_argument(
            "numerical nonlinear solve currently requires a square system");
    for(const exact_expr &equation : equations)
        if(!equation.valid() || equation.storage_ != storage_)
            throw std::invalid_argument("equations belong to a different context");
    for(const exact_expr &variable : variables)
        if(!variable.valid() || variable.storage_ != storage_ ||
           storage_->node(variable.root_).op != exact_opcode::symbol)
            throw std::invalid_argument("solve variables must be symbols");

    const size_t n = variables.size();
    // Newton must converge to the requested output precision, not merely to
    // a coarse residual threshold.  Keep a small guard margin for the finite
    // difference Jacobian and rounded intermediate operations.
    const int64_t guard_bits = precision_bits > 32.0
        ? std::max<int64_t>(16, (int64_t)precision_bits - 16)
        : std::max<int64_t>(8, (int64_t)(precision_bits * 0.75));
    Number tolerance = Number(1) >> guard_bits;
    Number step_size = Number(1) >> std::max<int64_t>(16, guard_bits / 2);

    auto evaluate = [&](const exact_expr &equation,
                        const std::vector<Number> &point){
        exact_expr value = equation;
        for(size_t i = 0; i < n; ++i){
            Number copy = point[i];
            copy.set_precision(precision_bits + 32.0);
            value = substitute(value, variables[i],
                exact_expr(storage_, storage_->intern_value(
                    exact_value(std::move(copy)))));
        }
        uint32_t numeric_id = storage_->promote_approximate(value.root_);
        exact_node numeric_node = storage_->node(numeric_id);
        if(numeric_node.op != exact_opcode::value ||
           !storage_->values[numeric_node.payload].is_approximate())
            throw std::invalid_argument(
                "numerical solve cannot evaluate this expression");
        return storage_->values[numeric_node.payload].number();
    };
    auto converged = [&](const std::vector<Number> &values){
        for(const Number &value : values)
            if(::abs(value) > tolerance) return false;
        return true;
    };
    auto make_solution = [&](const std::vector<Number> &point){
        std::vector<uint32_t> rules;
        for(size_t i = 0; i < n; ++i){
            Number value = point[i];
            value.set_precision(precision_bits);
            uint32_t value_id = storage_->intern_value(
                exact_value(std::move(value)));
            rules.push_back(storage_->intern_compound(
                exact_opcode::rule, {variables[i].root_, value_id}));
        }
        return storage_->intern_compound(exact_opcode::expression_list, rules);
    };

    std::vector<std::vector<int>> seeds;
    std::vector<int> seed_values = {-2, -1, 0, 1, 2};
    if(n <= 3){
        std::vector<int> current(n);
        auto generate = [&](auto &&self, size_t index) -> void{
            if(index == n){ seeds.push_back(current); return; }
            for(int value : seed_values){
                current[index] = value;
                self(self, index + 1);
            }
        };
        generate(generate, 0);
    }else{
        seeds.push_back(std::vector<int>(n, 0));
        seeds.push_back(std::vector<int>(n, 1));
        seeds.push_back(std::vector<int>(n, -1));
    }

    std::vector<uint32_t> solutions;
    std::vector<std::vector<Number>> unique_points;
    std::unordered_set<std::string> seen;
    for(const std::vector<int> &seed : seeds){
        std::vector<Number> point;
        point.reserve(n);
        for(int value : seed){
            Number number(value);
            number.set_precision(precision_bits + 32.0);
            point.push_back(std::move(number));
        }
        bool converged_solution = false;
        for(size_t iteration = 0; iteration < 128; ++iteration){
            std::vector<Number> residual(n);
            for(size_t i = 0; i < n; ++i) residual[i] = evaluate(equations[i], point);
            if(converged(residual)){ converged_solution = true; break; }

            std::vector<std::vector<Number>> matrix(
                n, std::vector<Number>(n + 1, Number(0)));
            for(size_t row = 0; row < n; ++row){
                for(size_t column = 0; column < n; ++column){
                    std::vector<Number> plus = point, minus = point;
                    plus[column] += step_size;
                    minus[column] -= step_size;
                    matrix[row][column] =
                        (evaluate(equations[row], plus) -
                         evaluate(equations[row], minus)) /
                        (step_size * Number(2));
                }
                matrix[row][n] = -residual[row];
            }
            bool singular = false;
            for(size_t column = 0; column < n; ++column){
                size_t pivot = column;
                while(pivot < n && matrix[pivot][column].is_zero()) ++pivot;
                if(pivot == n){ singular = true; break; }
                std::swap(matrix[pivot], matrix[column]);
                Number divisor = matrix[column][column];
                for(size_t j = column; j <= n; ++j)
                    matrix[column][j] /= divisor;
                for(size_t row = 0; row < n; ++row){
                    if(row == column) continue;
                    Number factor = matrix[row][column];
                    if(factor.is_zero()) continue;
                    for(size_t j = column; j <= n; ++j)
                        matrix[row][j] -= factor * matrix[column][j];
                }
            }
            if(singular) break;
            for(size_t i = 0; i < n; ++i) point[i] += matrix[i][n];
        }
        if(!converged_solution) continue;
        for(Number &value : point)
            if(!(::abs(value) > tolerance)) value = Number(0);
        bool duplicate = false;
        for(const std::vector<Number> &previous : unique_points){
            bool same = true;
            for(size_t i = 0; i < point.size(); ++i){
                Number scale = std::max(::abs(point[i]), ::abs(previous[i]));
                if(scale < Number(1)) scale = Number(1);
                Number local_tolerance = scale >> guard_bits;
                if(::abs(point[i] - previous[i]) > local_tolerance){
                    same = false;
                    break;
                }
            }
            if(same){ duplicate = true; break; }
        }
        if(duplicate) continue;
        unique_points.push_back(point);
        std::string key;
        for(const Number &value : point) key += (std::string)value + ";";
        if(seen.insert(key).second) solutions.push_back(make_solution(point));
    }
    return exact_expr(storage_, storage_->intern_compound(
        exact_opcode::expression_list, solutions));
}

exact_expr exact_context::exact_solve(
        const std::vector<exact_expr> &equations,
        const std::vector<exact_expr> &variables){
    return solve_system_impl(equations, variables, true);
}

exact_expr exact_context::solve(
        const exact_expr &expression,
        const std::vector<exact_expr> &variables,
        double precision_bits){
    if(!(precision_bits > 0.0) || !std::isfinite(precision_bits))
        throw std::invalid_argument("solve precision must be finite and positive");
    if(variables.size() == 1 && expression.valid() &&
       expression.storage_ == storage_ &&
       storage_->node(expression.root_).operand_count == 1){
        exact_opcode operation = storage_->node(expression.root_).op;
        if((operation == exact_opcode::sine ||
            operation == exact_opcode::cosine ||
            operation == exact_opcode::tangent) &&
           storage_->children(storage_->node(expression.root_))[0] ==
               variables[0].root_)
            return exact_solve(expression, variables);
    }
    if(!is_polynomial(expression, variables))
        return solve_numeric_system_impl({expression}, variables, precision_bits);
    exact_expr symbolic = solve_polynomial_impl(expression, variables, false);
    const exact_node &list = storage_->node(symbolic.root_);
    const uint32_t *root_data = storage_->children(list);
    // Approximating each root interns new values and may reallocate the arena's
    // operand vector.  Keep IDs by value instead of retaining an arena pointer.
    std::vector<uint32_t> roots(root_data, root_data + list.operand_count);
    std::vector<uint32_t> results;
    results.reserve(roots.size());
    uint8_t variable_assumptions = 0;
    auto assumed = storage_->assumptions.find(variables[0].root_);
    if(assumed != storage_->assumptions.end())
        variable_assumptions = assumed->second;
    std::unordered_map<uint32_t, Complex> complex_values;
    auto evaluate_complex = [&](auto &&self, uint32_t id) -> Complex{
        auto cached = complex_values.find(id);
        if(cached != complex_values.end()) return cached->second;
        const exact_node &current = storage_->node(id);
        Complex result;
        if(current.op == exact_opcode::value){
            result = Complex(storage_->values[current.payload]
                                 .to_number(precision_bits + 32.0));
        }else if(current.op == exact_opcode::constant_i){
            result = Complex(Number(0), Number(1));
        }else if(current.op == exact_opcode::constant_pi){
            result = Complex(getpi(constant_decimal_digits(precision_bits + 32.0)));
        }else if(current.op == exact_opcode::constant_e){
            result = Complex(gete(constant_decimal_digits(precision_bits + 32.0)));
        }else{
            const uint32_t *args = storage_->children(current);
            if(current.op == exact_opcode::add){
                result = Complex(Number(0));
                result.set_precision(precision_bits + 32.0);
                for(size_t j = 0; j < current.operand_count; ++j)
                    result += self(self, args[j]);
            }else if(current.op == exact_opcode::multiply){
                result = Complex(Number(1));
                result.set_precision(precision_bits + 32.0);
                for(size_t j = 0; j < current.operand_count; ++j)
                    result *= self(self, args[j]);
            }else if(current.op == exact_opcode::power){
                result = ::pow(self(self, args[0]), self(self, args[1]));
            }else if(current.op == exact_opcode::square_root){
                result = ::sqrt(self(self, args[0]));
            }else{
                throw std::invalid_argument(
                    "solve cannot approximate this complex root expression");
            }
        }
        result.set_precision(precision_bits);
        complex_values.emplace(id, result);
        return result;
    };
    for(size_t i = 0; i < roots.size(); ++i){
        bool has_symbol = false;
        std::unordered_set<uint32_t> visited;
        std::vector<uint32_t> pending(1, roots[i]);
        while(!pending.empty() && !has_symbol){
            uint32_t id = pending.back();
            pending.pop_back();
            if(!visited.insert(id).second) continue;
            const exact_node &current = storage_->node(id);
            if(current.op == exact_opcode::symbol ||
               current.op == exact_opcode::bounded_sum){
                has_symbol = true;
                break;
            }
            const uint32_t *args = storage_->children(current);
            pending.insert(pending.end(), args, args + current.operand_count);
        }
        if(has_symbol){
            results.push_back(roots[i]);
            continue;
        }
        Complex numeric = evaluate_complex(evaluate_complex, roots[i]);
        Number real = numeric.real();
        Number imag = numeric.imag();
        Number scale = std::max(::abs(real), ::abs(imag));
        if(scale < Number(1)) scale = Number(1);
        int64_t tolerance_bits = precision_bits > 16.0
            ? (int64_t)std::min<double>(precision_bits * 0.5,
                                        (double)INT64_MAX) : 8;
        Number tolerance = scale >> tolerance_bits;
        if(::abs(real) < tolerance) real = Number(0);
        if(::abs(imag) < tolerance) imag = Number(0);
        if((std::string)real == "0" || (std::string)real == "-0") real = Number(0);
        if((std::string)imag == "0" || (std::string)imag == "-0") imag = Number(0);
        real.set_precision(precision_bits);
        imag.set_precision(precision_bits);
        if((variable_assumptions & exact_storage::assumed_real) &&
           !imag.is_zero()) continue;
        if((variable_assumptions & exact_storage::assumed_positive) &&
           (real.is_zero() || real.is_negative())) continue;
        if((variable_assumptions & exact_storage::assumed_nonnegative) &&
           real.is_negative()) continue;
        bool real_zero = real.is_zero();
        uint32_t real_node = storage_->intern_value(exact_value(std::move(real)));
        if(imag.is_zero()){
            results.push_back(real_node);
        }else{
            uint32_t imag_node = storage_->intern_value(exact_value(std::move(imag)));
            uint32_t imaginary = storage_->intern_compound(
                exact_opcode::constant_i, {});
            uint32_t imag_term = storage_->make_multiply({imag_node, imaginary});
            results.push_back(real_zero ? imag_term :
                              storage_->make_add({real_node, imag_term}));
        }
    }
    return exact_expr(storage_, storage_->intern_compound(
        exact_opcode::expression_list, results));
}

exact_expr exact_context::solve(
        const std::vector<exact_expr> &equations,
        const std::vector<exact_expr> &variables,
        double precision_bits){
    return solve_numeric_system_impl(equations, variables, precision_bits);
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
            auto assumption = old_storage->assumptions.find(id);
            if(assumption != old_storage->assumptions.end())
                new_storage->assumptions[remap[id]] = assumption->second;
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
exact_expr abs(const exact_expr &value){
    if(!value.valid()) throw std::logic_error("invalid exact expression");
    exact_context context(value.storage_);
    return context.absolute_value(value);
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
exact_expr asin(const exact_expr &value){
    if(!value.valid()) throw std::logic_error("invalid exact expression");
    exact_context context(value.storage_);
    return context.arc_sine(value);
}
exact_expr acos(const exact_expr &value){
    if(!value.valid()) throw std::logic_error("invalid exact expression");
    exact_context context(value.storage_);
    return context.arc_cosine(value);
}
exact_expr atan(const exact_expr &value){
    if(!value.valid()) throw std::logic_error("invalid exact expression");
    exact_context context(value.storage_);
    return context.arc_tangent(value);
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
exact_expr asinh(const exact_expr &value){
    if(!value.valid()) throw std::logic_error("invalid exact expression");
    exact_context context(value.storage_);
    return context.inverse_hyperbolic_sine(value);
}
exact_expr acosh(const exact_expr &value){
    if(!value.valid()) throw std::logic_error("invalid exact expression");
    exact_context context(value.storage_);
    return context.inverse_hyperbolic_cosine(value);
}
exact_expr atanh(const exact_expr &value){
    if(!value.valid()) throw std::logic_error("invalid exact expression");
    exact_context context(value.storage_);
    return context.inverse_hyperbolic_tangent(value);
}
exact_expr ln(const exact_expr &value){
    if(!value.valid()) throw std::logic_error("invalid exact expression");
    exact_context context(value.storage_);
    return context.natural_logarithm(value);
}
exact_expr log2(const exact_expr &value){
    if(!value.valid()) throw std::logic_error("invalid exact expression");
    exact_context context(value.storage_);
    return context.logarithm_base_2(value);
}
exact_expr log10(const exact_expr &value){
    if(!value.valid()) throw std::logic_error("invalid exact expression");
    exact_context context(value.storage_);
    return context.logarithm_base_10(value);
}
exact_expr Si(const exact_expr &value){
    if(!value.valid()) throw std::logic_error("invalid exact expression");
    exact_context context(value.storage_);
    return context.sine_integral(value);
}
exact_expr Ci(const exact_expr &value){
    if(!value.valid()) throw std::logic_error("invalid exact expression");
    exact_context context(value.storage_);
    return context.cosine_integral(value);
}
exact_expr Ei(const exact_expr &value){
    if(!value.valid()) throw std::logic_error("invalid exact expression");
    exact_context context(value.storage_);
    return context.exponential_integral(value);
}
exact_expr erf(const exact_expr &value){
    if(!value.valid()) throw std::logic_error("invalid exact expression");
    exact_context context(value.storage_);
    return context.error_function(value);
}
exact_expr erfi(const exact_expr &value){
    if(!value.valid()) throw std::logic_error("invalid exact expression");
    exact_context context(value.storage_);
    return context.imaginary_error_function(value);
}
exact_expr partial_gamma(const exact_expr &a, const exact_expr &x){
    if(!a.valid() || !x.valid() || a.storage_ != x.storage_)
        throw std::invalid_argument("exact expressions belong to different contexts");
    exact_context context(a.storage_);
    return context.partial_gamma(a, x);
}
exact_expr diff(const exact_expr &expression, const exact_expr &variable){
    if(!expression.valid() || !variable.valid() ||
       expression.storage_ != variable.storage_)
        throw std::invalid_argument("exact expressions belong to different contexts");
    exact_context context(expression.storage_);
    return context.differentiate(expression, variable);
}
exact_expr integrate(const exact_expr &expression, const exact_expr &variable){
    if(!expression.valid() || !variable.valid() ||
       expression.storage_ != variable.storage_)
        throw std::invalid_argument("exact expressions belong to different contexts");
    exact_context context(expression.storage_);
    return context.integrate(expression, variable);
}
bool operator==(const exact_expr &a, const exact_expr &b){
    if(!a.valid() || !b.valid()) return !a.valid() && !b.valid();
    return a.storage_ == b.storage_ && a.root_ == b.root_;
}
bool operator!=(const exact_expr &a, const exact_expr &b){ return !(a == b); }
