#include"../prec_num.hpp"

#include<cctype>
#include<cmath>
#include<cstdint>
#include<cstdlib>
#include<iostream>
#include<limits>
#include<stdexcept>
#include<string>
#include<utility>

static unsigned int requested_bits = 256;
static size_t requested_digits = 0;
static bool fixed_output_digits = false;
static const unsigned int guard_bits = 32;

static unsigned int bits_for_fractional_digits(size_t digits){
    long double bits = std::ceil(((long double)digits + 2.0L) *
                                 3.32192809488736234787L);
    if(bits > 1000000000.0L)
        throw std::runtime_error("requested output requires too much precision");
    return (unsigned int)bits;
}

static unsigned int effective_precision(){
    unsigned int bits = requested_bits;
    if(fixed_output_digits)
        bits = std::max(bits, bits_for_fractional_digits(requested_digits));
    return bits;
}

static unsigned int working_precision(){
    unsigned int bits = effective_precision();
    if(bits > std::numeric_limits<unsigned int>::max() - guard_bits)
        throw std::runtime_error("precision is too large");
    return bits + guard_bits;
}

static precn_t pow10(size_t exponent){
    precn_t result(1);
    precn_t base(10);
    while(exponent){
        if(exponent & 1) result = result * base;
        exponent >>= 1;
        if(exponent) base = base * base;
    }
    return result;
}

static size_t integer_bit_length(const precn_t &value){
    if(value.rsiz == 0) return 0;
    uint64_t top = value.a[value.rsiz - 1];
#if defined(__clang__) || defined(__GNUC__)
    return (value.rsiz - 1) * 64 + 64 - (size_t)__builtin_clzll(top);
#else
    size_t bits = (value.rsiz - 1) * 64;
    while(top){ ++bits; top >>= 1; }
    return bits;
#endif
}

static Number rounded_decimal_fraction(precn_t numerator, const precn_t &denominator){
    unsigned int precision = working_precision();
    size_t target = (size_t)precision + 128;
    size_t numerator_bits = integer_bit_length(numerator);
    size_t denominator_bits = integer_bit_length(denominator);
    size_t scale_bits;
    if(denominator_bits >= numerator_bits){
        size_t difference = denominator_bits - numerator_bits;
        if(difference > SIZE_MAX - target)
            throw std::runtime_error("decimal literal is too small");
        scale_bits = target + difference;
    }else{
        size_t difference = numerator_bits - denominator_bits;
        scale_bits = target > difference ? target - difference : 0;
    }
    if(scale_bits > SIZE_MAX - 63)
        throw std::runtime_error("decimal literal is too small");
    size_t radix_point = (scale_bits + 63) / 64;
    if(radix_point > (size_t)INT64_MAX || radix_point > SIZE_MAX / 64)
        throw std::runtime_error("decimal literal is too small");

    numerator = numerator << (radix_point * 64);
    precn_t quotient, remainder;
    divmod_into(quotient, remainder, numerator, denominator);
    if((remainder + remainder) >= denominator)
        quotient = add_u64(quotient, 1);
    return Number::from_raw(precz_t(std::move(quotient)), (int64_t)radix_point,
                            precision);
}

static Number approximate(Number value){
    if(value.is_exact()) value.set_precision(working_precision());
    return value;
}

static Number divide_numbers(Number a, Number b){
    if(b.is_zero()) throw std::runtime_error("division by zero");
    return approximate(a) / approximate(b);
}

static Number sqrt_number(const Number &value){
    if(value.is_negative())
        throw std::runtime_error("square root of a negative number");
    Number root = sqrt(value);
    if(value.is_exact() && !root.is_exact())
        root = sqrt(approximate(value));
    return root;
}

static Number pow_number(Number base, int64_t exponent){
    bool reciprocal = exponent < 0;
    uint64_t n = reciprocal ? (uint64_t)0 - (uint64_t)exponent
                            : (uint64_t)exponent;
    Number result(1);
    while(n){
        if(n & 1) result *= base;
        n >>= 1;
        if(n) base *= base;
    }
    return reciprocal ? divide_numbers(Number(1), result) : result;
}

static void increment_decimal(std::string &text, size_t from){
    for(size_t i = from + 1; i > 0;){
        --i;
        if(text[i] == '.' || text[i] == '-') continue;
        if(text[i] < '9'){
            ++text[i];
            return;
        }
        text[i] = '0';
    }
    text.insert(text[0] == '-' ? 1 : 0, 1, '1');
}

static void trim_fraction(std::string &text){
    size_t dot = text.find('.');
    if(dot == std::string::npos) return;
    while(text.size() > dot + 1 && text.back() == '0') text.pop_back();
    if(text.back() == '.') text.pop_back();
}

static std::string round_fixed(const Number &value, size_t fractional){
    if(fractional == SIZE_MAX) throw std::runtime_error("digit count is too large");
    std::string text = value.to_string(fractional + 1);
    size_t dot = text.find('.');
    if(dot == std::string::npos){
        text.push_back('.');
        dot = text.size() - 1;
    }
    while(text.size() < dot + fractional + 2) text.push_back('0');
    size_t next = dot + fractional + 1;
    bool up = text[next] >= '5';
    text.erase(next);
    if(up) increment_decimal(text, next - 1);
    trim_fraction(text);
    return text;
}

static std::string round_significant(const Number &value, size_t significant){
    std::string text = (std::string)value;
    size_t first = text.find_first_of("123456789");
    if(first == std::string::npos) return "0";

    size_t kept = 0;
    size_t last = first;
    size_t next = std::string::npos;
    for(size_t i = first; i < text.size(); ++i){
        if(!std::isdigit((unsigned char)text[i])) continue;
        if(kept < significant){
            ++kept;
            last = i;
        }else{
            next = i;
            break;
        }
    }
    if(next == std::string::npos) return text;

    bool up = text[next] >= '5';
    size_t dot = text.find('.');
    if(dot == std::string::npos || next < dot){
        size_t end = dot == std::string::npos ? text.size() : dot;
        for(size_t i = next; i < end; ++i)
            if(std::isdigit((unsigned char)text[i])) text[i] = '0';
        if(dot != std::string::npos) text.erase(dot);
    }else{
        text.erase(next);
    }
    if(up) increment_decimal(text, last);
    trim_fraction(text);
    return text;
}

static std::string compact_scientific(const std::string &text,
                                      size_t significant){
    size_t sign = !text.empty() && text[0] == '-' ? 1 : 0;
    size_t dot = text.find('.');
    size_t integer_end = dot == std::string::npos ? text.size() : dot;
    size_t first = text.find_first_of("123456789", sign);
    if(first == std::string::npos) return "0";

    bool negative_exponent = first > integer_end;
    size_t exponent = negative_exponent ? first - integer_end
                                        : integer_end - first - 1;
    if(!negative_exponent && exponent < significant) return text;
    if(negative_exponent && exponent < 4) return text;

    std::string digits;
    for(size_t i = first; i < text.size() && digits.size() < significant; ++i)
        if(std::isdigit((unsigned char)text[i])) digits.push_back(text[i]);
    while(digits.size() > 1 && digits.back() == '0') digits.pop_back();

    std::string result;
    if(sign) result.push_back('-');
    result.push_back(digits[0]);
    if(digits.size() > 1){
        result.push_back('.');
        result.append(digits, 1, std::string::npos);
    }
    result += negative_exponent ? "e-" : "e+";
    result += std::to_string(exponent);
    return result;
}

static std::string format_result(const Number &value){
    if(fixed_output_digits) return round_fixed(value, requested_digits);
    if(value.is_exact()) return (std::string)value;
    size_t significant = (size_t)((double)requested_bits * 0.3010299956639812);
    if(significant > 2) significant -= 2;
    significant = std::max<size_t>(significant, 1);
    return compact_scientific(round_significant(value, significant), significant);
}

class Parser{
    const std::string &text_;
    size_t pos_;
    const Number &answer_;

    void skip_space(){
        while(pos_ < text_.size() && std::isspace((unsigned char)text_[pos_]))
            ++pos_;
    }

    bool take(char c){
        skip_space();
        if(pos_ < text_.size() && text_[pos_] == c){
            ++pos_;
            return true;
        }
        return false;
    }

    void require(char c){
        if(!take(c))
            throw std::runtime_error(std::string("expected '") + c + "'");
    }

    std::string identifier(){
        skip_space();
        size_t begin = pos_;
        while(pos_ < text_.size() &&
              (std::isalnum((unsigned char)text_[pos_]) || text_[pos_] == '_'))
            ++pos_;
        return text_.substr(begin, pos_ - begin);
    }

    Number number(){
        skip_space();
        std::string digits;
        size_t fractional = 0;
        bool any = false;

        while(pos_ < text_.size() && std::isdigit((unsigned char)text_[pos_])){
            digits.push_back(text_[pos_++]);
            any = true;
        }
        if(pos_ < text_.size() && text_[pos_] == '.'){
            ++pos_;
            while(pos_ < text_.size() && std::isdigit((unsigned char)text_[pos_])){
                digits.push_back(text_[pos_++]);
                ++fractional;
                any = true;
            }
        }
        if(!any) throw std::runtime_error("expected a number");

        int64_t exponent = 0;
        if(pos_ < text_.size() && (text_[pos_] == 'e' || text_[pos_] == 'E')){
            ++pos_;
            bool negative = false;
            if(pos_ < text_.size() && (text_[pos_] == '+' || text_[pos_] == '-'))
                negative = text_[pos_++] == '-';
            if(pos_ == text_.size() || !std::isdigit((unsigned char)text_[pos_]))
                throw std::runtime_error("expected an exponent");
            while(pos_ < text_.size() && std::isdigit((unsigned char)text_[pos_])){
                unsigned digit = (unsigned)(text_[pos_++] - '0');
                if(exponent > 1000000) throw std::runtime_error("decimal exponent is too large");
                exponent = exponent * 10 + digit;
            }
            if(exponent > 1000000) throw std::runtime_error("decimal exponent is too large");
            if(negative) exponent = -exponent;
        }

        while(fractional && !digits.empty() && digits.back() == '0'){
            digits.pop_back();
            --fractional;
        }
        size_t first = digits.find_first_not_of('0');
        if(first == std::string::npos) return Number(0);
        digits.erase(0, first);

        if(fractional > (size_t)INT64_MAX)
            throw std::runtime_error("decimal literal is too long");
        int64_t decimal_shift = exponent - (int64_t)fractional;
        Number value((precz_t(digits)));
        if(decimal_shift >= 0)
            return value * Number(pow10((size_t)decimal_shift));
        if(decimal_shift == INT64_MIN || (uint64_t)-decimal_shift > (uint64_t)SIZE_MAX)
            throw std::runtime_error("decimal exponent is too small");
        return rounded_decimal_fraction(precn_t(digits),
                                        pow10((size_t)-decimal_shift));
    }

    int64_t integer_exponent(const Number &value){
        precz_t integer = value.to_integer();
        if(value != Number(integer))
            throw std::runtime_error("the exponent must be an integer");
        const precn_t &mag = integer.magnitude();
        if(mag.rsiz > 1 || (mag.rsiz && mag.a[0] > 1000000))
            throw std::runtime_error("the exponent magnitude must not exceed 1000000");
        int64_t result = mag.rsiz ? (int64_t)mag.a[0] : 0;
        return integer.is_negative() ? -result : result;
    }

    Number primary(){
        skip_space();
        if(take('(')){
            Number value = expression();
            require(')');
            return value;
        }
        if(pos_ < text_.size() &&
           (std::isdigit((unsigned char)text_[pos_]) || text_[pos_] == '.'))
            return number();
        if(pos_ < text_.size() && std::isalpha((unsigned char)text_[pos_])){
            std::string name = identifier();
            if(name == "ans") return answer_;
            require('(');
            Number value = expression();
            require(')');
            if(name == "abs") return abs(value);
            if(name == "sqrt") return sqrt_number(value);
            if(name == "exp") return exp(approximate(value));
            if(name == "expm1") return expm1(approximate(value));
            if(name == "ln"){
                if(value.is_zero() || value.is_negative())
                    throw std::runtime_error("logarithm requires a positive number");
                return ln(approximate(value));
            }
            if(name == "log10"){
                if(value.is_zero() || value.is_negative())
                    throw std::runtime_error("logarithm requires a positive number");
                return log10(approximate(value));
            }
            if(name == "log2"){
                if(value.is_zero() || value.is_negative())
                    throw std::runtime_error("logarithm requires a positive number");
                return log2(approximate(value));
            }
            if(name == "sin") return sin(approximate(value));
            if(name == "cos") return cos(approximate(value));
            if(name == "tan") return tan(approximate(value));
            if(name == "asin") return asin(approximate(value));
            if(name == "acos") return acos(approximate(value));
            if(name == "atan") return atan(approximate(value));
            if(name == "sinh") return sinh(approximate(value));
            if(name == "cosh") return cosh(approximate(value));
            if(name == "tanh") return tanh(approximate(value));
            if(name == "asinh") return asinh(approximate(value));
            if(name == "acosh") return acosh(approximate(value));
            if(name == "atanh") return atanh(approximate(value));
            throw std::runtime_error("unknown function: " + name);
        }
        throw std::runtime_error("expected a number, function, or '(' at column " +
                                 std::to_string(pos_ + 1));
    }

    Number power(){
        Number left = primary();
        if(take('^')){
            Number right = unary();
            precz_t integer = right.to_integer();
            if(right == Number(integer))
                return pow_number(left, integer_exponent(right));
            return pow(approximate(left), approximate(right));
        }
        return left;
    }

    Number unary(){
        if(take('+')) return unary();
        if(take('-')) return -unary();
        return power();
    }

    Number product(){
        Number value = unary();
        for(;;){
            if(take('*')) value *= unary();
            else if(take('/')) value = divide_numbers(value, unary());
            else return value;
        }
    }

    Number expression(){
        Number value = product();
        for(;;){
            if(take('+')) value += product();
            else if(take('-')) value -= product();
            else return value;
        }
    }

public:
    Parser(const std::string &text, const Number &answer)
        : text_(text), pos_(0), answer_(answer){}

    Number parse(){
        Number value = expression();
        skip_space();
        if(pos_ != text_.size())
            throw std::runtime_error("unexpected input at column " +
                                     std::to_string(pos_ + 1));
        return value;
    }
};

static void print_help(){
    std::cout
        << "operators: +  -  *  /  ^  and parentheses\n"
        << "functions: sqrt(x), abs(x), exp(x), expm1(x), ln(x), log10(x), log2(x),\n"
        << "           sin(x), cos(x), tan(x), asin(x), acos(x), atan(x)\n"
        << "           sinh(x), cosh(x), tanh(x), asinh(x), acosh(x), atanh(x)\n"
        << "literals:  123, 0.125, 1.2e-30\n"
        << "variable:  ans\n"
        << "commands:  !precision BITS, !digits N, !auto, !help, !quit\n";
}

static bool command(const std::string &line){
    if(line == "!quit" || line == "!q") return false;
    if(line == "!help"){
        print_help();
        return true;
    }
    if(line == "!auto"){
        fixed_output_digits = false;
        std::cout << "automatic output digits\n";
        return true;
    }
    const std::string precision = "!precision ";
    const std::string digits = "!digits ";
    try{
        if(line.compare(0, precision.size(), precision) == 0){
            unsigned long value = std::stoul(line.substr(precision.size()));
            if(value == 0 || value > 1000000000UL)
                throw std::runtime_error("precision must be between 1 and 1000000000");
            requested_bits = (unsigned int)value;
            std::cout << "precision " << requested_bits << " bits\n";
            return true;
        }
        if(line.compare(0, digits.size(), digits) == 0){
            unsigned long long value = std::stoull(line.substr(digits.size()));
            if(value > (unsigned long long)SIZE_MAX)
                throw std::runtime_error("digit count is too large");
            size_t output_digits = (size_t)value;
            unsigned int output_bits = bits_for_fractional_digits(output_digits);
            requested_digits = output_digits;
            fixed_output_digits = true;
            std::cout << "output " << requested_digits << " fractional digits; "
                      << "effective precision "
                      << std::max(requested_bits, output_bits) << " bits\n";
            return true;
        }
    }catch(const std::exception &error){
        std::cerr << "error: " << error.what() << '\n';
        return true;
    }
    std::cerr << "error: unknown command; use !help\n";
    return true;
}

int main(int argc, char **argv){
    for(int i = 1; i < argc; ++i){
        std::string arg(argv[i]);
        if(arg == "--help"){
            print_help();
            return 0;
        }
        if(arg == "--bits" && i + 1 < argc){
            requested_bits = (unsigned int)std::stoul(argv[++i]);
            if(requested_bits == 0) throw std::runtime_error("precision must be positive");
            continue;
        }
        if(arg == "--digits" && i + 1 < argc){
            requested_digits = (size_t)std::stoull(argv[++i]);
            bits_for_fractional_digits(requested_digits);
            fixed_output_digits = true;
            continue;
        }
        std::cerr << "unknown option: " << arg << '\n';
        return 1;
    }

    std::cout << "Number calculator (" << requested_bits
              << " bits); use !help for help\n";
    Number answer(0);
    std::string line;
    while(std::cout << "> " && std::getline(std::cin, line)){
        while(!line.empty() && std::isspace((unsigned char)line.back()))
            line.pop_back();
        if(line.size() >= 3 && (unsigned char)line[0] == 0xef &&
           (unsigned char)line[1] == 0xbb && (unsigned char)line[2] == 0xbf)
            line.erase(0, 3);
        if(line.empty()) continue;
        if(line[0] == '!'){
            if(!command(line)) break;
            continue;
        }
        try{
            answer = Parser(line, answer).parse();
            std::cout << format_result(answer) << '\n';
        }catch(const std::exception &error){
            std::cerr << "error: " << error.what() << '\n';
        }
    }
    return 0;
}
