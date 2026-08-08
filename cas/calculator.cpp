#include"prec_cas.hpp"

#include<cctype>
#include<chrono>
#include<cstdint>
#include<cstdlib>
#include<iostream>
#include<stdexcept>
#include<string>

namespace{

static precn_t calculator_pow10(size_t exponent){
    precn_t result(1), base(10);
    while(exponent){
        if(exponent & 1) result = result * base;
        exponent >>= 1;
        if(exponent) base = base * base;
    }
    return result;
}

struct calculator_state{
    exact_context context;
    exact_expr answer;
    double precision = 256.0;
};

static void collect_garbage(calculator_state &state, bool force){
    if(!state.answer.valid()){
        if(force) std::cout << "nothing to collect\n";
        return;
    }
    size_t total = state.context.node_count();
    size_t live = state.answer.reachable_node_count();
    bool worthwhile = total >= 65536 &&
        (live <= (SIZE_MAX - 4096) / 4) && total > live * 4 + 4096;
    if(!force && !worthwhile) return;

    state.answer = state.context.compact(state.answer);
    if(force)
        std::cout << "collected " << total << " -> "
                  << state.context.node_count() << " nodes\n";
}

class parser{
    const std::string &text_;
    size_t position_;
    calculator_state &state_;

    void skip_space(){
        while(position_ < text_.size() &&
              std::isspace((unsigned char)text_[position_])) ++position_;
    }

    bool take(char token){
        skip_space();
        if(position_ < text_.size() && text_[position_] == token){
            ++position_;
            return true;
        }
        return false;
    }

    void require(char token){
        if(!take(token))
            throw std::runtime_error(std::string("expected '") + token + "'");
    }

    std::string identifier(){
        skip_space();
        size_t begin = position_;
        if(position_ >= text_.size() ||
           !(std::isalpha((unsigned char)text_[position_]) ||
             text_[position_] == '_'))
            throw std::runtime_error("expected an identifier");
        ++position_;
        while(position_ < text_.size() &&
              (std::isalnum((unsigned char)text_[position_]) ||
               text_[position_] == '_')) ++position_;
        return text_.substr(begin, position_ - begin);
    }

    int64_t decimal_exponent(){
        bool negative = false;
        if(position_ < text_.size() &&
           (text_[position_] == '+' || text_[position_] == '-'))
            negative = text_[position_++] == '-';
        if(position_ >= text_.size() ||
           !std::isdigit((unsigned char)text_[position_]))
            throw std::runtime_error("decimal exponent has no digits");
        uint64_t value = 0;
        while(position_ < text_.size() &&
              std::isdigit((unsigned char)text_[position_])){
            unsigned digit = (unsigned)(text_[position_++] - '0');
            if(value > 1000000 || value * 10 + digit > 1000000)
                throw std::runtime_error("decimal exponent is too large");
            value = value * 10 + digit;
        }
        return negative ? -(int64_t)value : (int64_t)value;
    }

    exact_expr number(){
        skip_space();
        std::string digits;
        size_t fractional_digits = 0;
        bool decimal = false;
        bool saw_digit = false;
        while(position_ < text_.size() &&
              std::isdigit((unsigned char)text_[position_])){
            saw_digit = true;
            digits.push_back(text_[position_++]);
        }
        if(position_ < text_.size() && text_[position_] == '.'){
            decimal = true;
            ++position_;
            while(position_ < text_.size() &&
                  std::isdigit((unsigned char)text_[position_])){
                saw_digit = true;
                digits.push_back(text_[position_++]);
                ++fractional_digits;
            }
        }
        if(!saw_digit) throw std::runtime_error("expected a number");

        int64_t exponent = 0;
        if(position_ < text_.size() &&
           (text_[position_] == 'e' || text_[position_] == 'E')){
            decimal = true;
            ++position_;
            exponent = decimal_exponent();
        }
        if(!decimal) return state_.context.value(exact_value(precz_t(digits)));

        int64_t scale = exponent - (int64_t)fractional_digits;
        precn_t numerator(digits);
        precn_t denominator(1);
        if(scale >= 0){
            numerator = numerator * calculator_pow10((size_t)scale);
        }else{
            if(scale == INT64_MIN) throw std::runtime_error("decimal scale is too large");
            denominator = calculator_pow10((size_t)-scale);
        }
        exact_value rational(precq_t(std::move(numerator), std::move(denominator)));
        Number approximate = rational.to_number(state_.precision);
        approximate.set_precision(state_.precision);
        return state_.context.value(exact_value(std::move(approximate)));
    }

    exact_expr function(const std::string &name, const exact_expr &argument){
        if(name == "sqrt") return state_.context.square_root(argument);
        if(name == "expand") return state_.context.expand(argument);
        if(name == "simplify") return state_.context.simplify(argument);
        if(name == "approx"){
            if(!argument.is_value())
                throw std::runtime_error("approx requires a numeric value");
            Number approximate = argument.value().to_number(state_.precision);
            approximate.set_precision(state_.precision);
            return state_.context.value(exact_value(std::move(approximate)));
        }
        if(!argument.is_value()){
            if(name == "exp") return state_.context.exponential(argument);
            if(name == "sin") return state_.context.sine(argument);
            if(name == "cos") return state_.context.cosine(argument);
            if(name == "tan") return state_.context.tangent(argument);
            if(name == "sinh") return state_.context.hyperbolic_sine(argument);
            if(name == "cosh") return state_.context.hyperbolic_cosine(argument);
            if(name == "tanh") return state_.context.hyperbolic_tangent(argument);
            throw std::runtime_error(name + " requires a numeric value");
        }
        Number value = argument.value().to_number(state_.precision);
        value.set_precision(state_.precision);
        Number result;
        if(name == "exp") result = exp(value);
        else if(name == "expm1") result = expm1(value);
        else if(name == "ln") result = ln(value);
        else if(name == "log10") result = log10(value);
        else if(name == "log2") result = log2(value);
        else if(name == "sin") result = sin(value);
        else if(name == "cos") result = cos(value);
        else if(name == "tan") result = tan(value);
        else if(name == "asin") result = asin(value);
        else if(name == "acos") result = acos(value);
        else if(name == "atan") result = atan(value);
        else if(name == "sinh") result = sinh(value);
        else if(name == "cosh") result = cosh(value);
        else if(name == "tanh") result = tanh(value);
        else if(name == "asinh") result = asinh(value);
        else if(name == "acosh") result = acosh(value);
        else if(name == "atanh") result = atanh(value);
        else throw std::runtime_error("unknown function: " + name);
        return state_.context.value(exact_value(std::move(result)));
    }

    exact_expr primary(){
        skip_space();
        if(take('(')){
            exact_expr result = expression();
            require(')');
            return result;
        }
        if(position_ < text_.size() &&
           (std::isdigit((unsigned char)text_[position_]) ||
            text_[position_] == '.')) return number();
        if(position_ < text_.size() &&
           (std::isalpha((unsigned char)text_[position_]) ||
            text_[position_] == '_')){
            std::string name = identifier();
            if(name == "ans"){
                if(!state_.answer.valid()) throw std::runtime_error("ans is not set");
                return state_.answer;
            }
            if(take('(')){
                exact_expr argument = expression();
                require(')');
                return function(name, argument);
            }
            return state_.context.symbol(name);
        }
        throw std::runtime_error("expected a value, symbol, function, or '(' at column " +
                                 std::to_string(position_ + 1));
    }

    exact_expr power(){
        exact_expr left = primary();
        if(take('^')) return state_.context.power(left, unary());
        return left;
    }

    exact_expr unary(){
        if(take('+')) return unary();
        if(take('-')) return -unary();
        return power();
    }

    exact_expr product(){
        exact_expr result = unary();
        for(;;){
            if(take('*')) result = result * unary();
            else if(take('/')) result = result / unary();
            else return result;
        }
    }

    exact_expr expression(){
        exact_expr result = product();
        for(;;){
            if(take('+')) result = result + product();
            else if(take('-')) result = result - product();
            else return result;
        }
    }

public:
    parser(const std::string &text, calculator_state &state)
        : text_(text), position_(0), state_(state){}

    exact_expr parse(){
        exact_expr result = expression();
        skip_space();
        if(position_ != text_.size())
            throw std::runtime_error("unexpected input at column " +
                                     std::to_string(position_ + 1));
        return result;
    }
};

static void help(){
    std::cout
        << "operators: +  -  *  /  ^  and parentheses\n"
        << "exact: integer literals, integer fractions, symbols, sqrt(integer)\n"
        << "approximate: decimal literals, approx(x), and numeric functions\n"
        << "functions: sqrt, expand, simplify, approx, exp, expm1, ln, log10, log2,\n"
        << "           sin, cos, tan, asin, acos, atan,\n"
        << "           sinh, cosh, tanh, asinh, acosh, atanh\n"
        << "commands: !precision BITS, !nodes, !gc, !dump [LIMIT], !info [EXPR],\n"
        << "          !tree [EXPR], !time EXPR, !clear, !help, !quit\n";
}

static exact_expr debug_argument(const std::string &line, size_t command_size,
                                 calculator_state &state){
    if(line.size() == command_size){
        if(!state.answer.valid()) throw std::runtime_error("ans is not set");
        return state.answer;
    }
    if(line[command_size] != ' ')
        throw std::runtime_error("expected a space after the command");
    std::string expression = line.substr(command_size + 1);
    if(expression.empty()) throw std::runtime_error("missing expression");
    return parser(expression, state).parse();
}

static void print_info(const exact_expr &expression,
                       const calculator_state &state){
    std::cout << "root #" << expression.id() << ' '
              << exact_opcode_name(expression.operation()) << ", "
              << expression.operand_count() << " operands, "
              << expression.reachable_node_count() << " reachable nodes, depth "
              << expression.depth() << '\n'
              << "arena " << state.context.node_count() << " nodes, "
              << state.context.operand_id_count() << " operand ids\n";
}

static bool command(const std::string &line, calculator_state &state){
    if(line == "!quit" || line == "!q") return false;
    if(line == "!help") help();
    else if(line == "!nodes")
        std::cout << state.context.node_count() << " nodes, "
                  << state.context.operand_id_count() << " operand ids\n";
    else if(line == "!gc") collect_garbage(state, true);
    else if(line == "!dump")
        std::cout << state.context.debug_dump();
    else if(line.compare(0, 6, "!dump ") == 0){
        std::string limit_text = line.substr(6);
        size_t used = 0;
        unsigned long long limit = std::stoull(limit_text, &used);
        if(used != limit_text.size() || limit == 0 || limit > SIZE_MAX)
            throw std::runtime_error("invalid dump limit");
        std::cout << state.context.debug_dump((size_t)limit);
    }
    else if(line == "!info" || line.compare(0, 6, "!info ") == 0)
        print_info(debug_argument(line, 5, state), state);
    else if(line == "!tree" || line.compare(0, 6, "!tree ") == 0)
        std::cout << debug_argument(line, 5, state).debug_tree();
    else if(line.compare(0, 6, "!time ") == 0){
        std::string expression = line.substr(6);
        if(expression.empty()) throw std::runtime_error("missing expression");
        auto begin = std::chrono::steady_clock::now();
        state.answer = parser(expression, state).parse();
        auto end = std::chrono::steady_clock::now();
        std::chrono::duration<double> elapsed = end - begin;
        collect_garbage(state, false);
        std::cout << state.answer.to_string() << '\n'
                  << "time " << elapsed.count() << " sec\n";
    }
    else if(line == "!clear"){
        state.context = exact_context();
        state.answer = exact_expr();
        std::cout << "cleared\n";
    }else if(line.compare(0, 11, "!precision ") == 0){
        std::string bits_text = line.substr(11);
        size_t used = 0;
        double bits = std::stod(bits_text, &used);
        if(used != bits_text.size() || !(bits > 0.0) || bits > 1000000000.0)
            throw std::runtime_error("invalid precision");
        state.precision = bits;
        std::cout << "precision " << bits << " bits\n";
    }else{
        throw std::runtime_error("unknown command");
    }
    return true;
}

} // namespace

int main(){
    calculator_state state;
    std::cout << "Exact CAS calculator (256-bit approximations); use !help for help\n";
    std::string line;
    while(std::cout << "> " && std::getline(std::cin, line)){
        try{
            while(!line.empty() && std::isspace((unsigned char)line.back()))
                line.pop_back();
            if(line.empty()) continue;
            if(line[0] == '!'){
                if(!command(line, state)) break;
                continue;
            }
            state.answer = parser(line, state).parse();
            collect_garbage(state, false);
            std::cout << state.answer.to_string() << '\n';
        }catch(const std::exception &error){
            std::cerr << "error: " << error.what() << '\n';
        }
    }
    return 0;
}
