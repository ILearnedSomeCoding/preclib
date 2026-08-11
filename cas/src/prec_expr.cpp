#include"../prec_cas.hpp"

#include<cmath>
#include<limits>
#include<stdexcept>
#include<utility>

struct expr_state{
    exact_context context;
    double precision;

    explicit expr_state(double bits) : context(), precision(bits){}
};

namespace{

static void require_state(const expr &value){
    if(!value.valid()) throw std::logic_error("invalid expression");
}

static void require_same_state(const expr &a, const expr &b){
    require_state(a);
    require_state(b);
    if(!a.same_context(b))
        throw std::invalid_argument("expressions belong to different contexts");
}

static int constant_digits(double binary_precision){
    long double digits = std::ceil((long double)binary_precision *
                                   0.30102999566398119521L) + 10.0L;
    if(digits > (long double)std::numeric_limits<int>::max())
        throw std::length_error("constant precision is too large");
    return (int)digits;
}

template<class Function>
static Number numeric_function(const expr &value, Function function,
                               const char *name){
    require_state(value);
    if(!value.is_number())
        throw std::invalid_argument(std::string(name) +
                                    " requires a numeric expression");
    Number argument = value.number();
    if(argument.is_exact()) argument.set_precision(value.context_precision());
    return function(argument);
}

} // namespace

expr::expr(std::shared_ptr<expr_state> state, exact_expr node)
    : state_(std::move(state)), node_(std::move(node)){}
expr::expr() : state_(), node_(){}
bool expr::valid() const{ return (bool)state_ && node_.valid(); }
bool expr::is_number() const{ return valid() && node_.is_value(); }
bool expr::is_approximate() const{
    return is_number() && node_.value().is_approximate();
}
bool expr::same_context(const expr &other) const{
    return state_ && state_ == other.state_;
}
double expr::context_precision() const{
    if(!valid()) throw std::logic_error("invalid expression");
    return state_->precision;
}
Number expr::number() const{
    if(!is_number()) throw std::logic_error("expression is not numeric");
    return node_.value().to_number(state_->precision);
}
exact_expr expr::exact_expression() const{ return node_; }
std::string expr::to_string() const{ return node_.to_string(); }

expr_context::expr_context(double precision_bits)
    : state_(std::make_shared<expr_state>(precision_bits)){
    if(!(precision_bits > 0.0) || !std::isfinite(precision_bits))
        throw std::invalid_argument("expression precision must be finite and positive");
}
double expr_context::precision() const{ return state_->precision; }
void expr_context::set_precision(double bits){
    if(!(bits > 0.0) || !std::isfinite(bits))
        throw std::invalid_argument("expression precision must be finite and positive");
    state_->precision = bits;
}
expr expr_context::number(const Number &value){
    return expr(state_, state_->context.value(exact_value(value)));
}
expr expr_context::number(Number &&value){
    return expr(state_, state_->context.value(exact_value(std::move(value))));
}
expr expr_context::floating(float value){ return number(Number(value)); }
expr expr_context::floating(double value){ return number(Number(value)); }
expr expr_context::exact_integer(const precz_t &value){
    return expr(state_, state_->context.value(exact_value(value)));
}
expr expr_context::symbol(const std::string &name){
    return expr(state_, state_->context.symbol(name));
}
expr expr_context::pi(){
    Number value = getpi(constant_digits(state_->precision));
    value.set_precision(state_->precision);
    return number(std::move(value));
}
expr expr_context::e(){
    Number value = gete(constant_digits(state_->precision));
    value.set_precision(state_->precision);
    return number(std::move(value));
}
expr expr_context::add(const std::vector<expr> &terms){
    std::vector<exact_expr> nodes;
    nodes.reserve(terms.size());
    for(const expr &term : terms){
        require_state(term);
        if(term.state_ != state_)
            throw std::invalid_argument("expressions belong to different contexts");
        nodes.push_back(term.node_);
    }
    return expr(state_, state_->context.add(nodes));
}
expr expr_context::multiply(const std::vector<expr> &factors){
    std::vector<exact_expr> nodes;
    nodes.reserve(factors.size());
    for(const expr &factor : factors){
        require_state(factor);
        if(factor.state_ != state_)
            throw std::invalid_argument("expressions belong to different contexts");
        nodes.push_back(factor.node_);
    }
    return expr(state_, state_->context.multiply(nodes));
}
expr expr_context::power(const expr &base, const expr &exponent){
    require_same_state(base, exponent);
    if(base.state_ != state_)
        throw std::invalid_argument("expressions belong to different contexts");
    return expr(state_, state_->context.power(base.node_, exponent.node_));
}
expr expr_context::square_root(const expr &value){
    require_state(value);
    if(value.state_ != state_)
        throw std::invalid_argument("expression belongs to a different context");
    return expr(state_, state_->context.square_root(value.node_));
}
expr expr_context::absolute_value(const expr &value){
    require_state(value);
    if(value.state_ != state_)
        throw std::invalid_argument("expression belongs to a different context");
    return expr(state_, state_->context.absolute_value(value.node_));
}
expr expr_context::simplify(const expr &value, size_t maximum_terms){
    require_state(value);
    if(value.state_ != state_)
        throw std::invalid_argument("expression belongs to a different context");
    return expr(state_, state_->context.simplify(value.node_, maximum_terms));
}
expr expr_context::expand(const expr &value, size_t maximum_terms){
    require_state(value);
    if(value.state_ != state_)
        throw std::invalid_argument("expression belongs to a different context");
    return expr(state_, state_->context.expand(value.node_, maximum_terms));
}
expr expr_context::factor(const expr &value){
    require_state(value);
    if(value.state_ != state_)
        throw std::invalid_argument("expression belongs to a different context");
    return expr(state_, state_->context.factor(value.node_));
}

expr operator+(const expr &a, const expr &b){
    require_same_state(a, b);
    return expr(a.state_, a.node_ + b.node_);
}
expr operator-(const expr &a, const expr &b){
    require_same_state(a, b);
    return expr(a.state_, a.node_ - b.node_);
}
expr operator-(const expr &a){
    require_state(a);
    return expr(a.state_, -a.node_);
}
expr operator*(const expr &a, const expr &b){
    require_same_state(a, b);
    return expr(a.state_, a.node_ * b.node_);
}
expr operator/(const expr &a, const expr &b){
    require_same_state(a, b);
    return expr(a.state_, a.node_ / b.node_);
}
expr pow(const expr &base, const expr &exponent){
    require_same_state(base, exponent);
    return expr(base.state_, ::pow(base.node_, exponent.node_));
}
expr sqrt(const expr &value){
    require_state(value);
    return expr(value.state_, ::sqrt(value.node_));
}
expr abs(const expr &value){
    require_state(value);
    if(!value.is_number()) return expr(value.state_, ::abs(value.node_));
    Number result = numeric_function(
        value, [](const Number &x){ return ::abs(x); }, "abs");
    return expr(value.state_, value.state_->context.value(
        exact_value(std::move(result))));
}
expr exp(const expr &value){
    require_state(value);
    if(!value.is_number()) return expr(value.state_, ::exp(value.node_));
    Number result = numeric_function(
        value, [](const Number &x){ return ::exp(x); }, "exp");
    return expr(value.state_, value.state_->context.value(
        exact_value(std::move(result))));
}
expr ln(const expr &value){
    require_state(value);
    if(!value.is_number()) return expr(value.state_, ::ln(value.node_));
    Number result = numeric_function(
        value, [](const Number &x){ return ::ln(x); }, "ln");
    return expr(value.state_, value.state_->context.value(
        exact_value(std::move(result))));
}
expr sin(const expr &value){
    require_state(value);
    if(!value.is_number()) return expr(value.state_, ::sin(value.node_));
    Number result = numeric_function(
        value, [](const Number &x){ return ::sin(x); }, "sin");
    return expr(value.state_, value.state_->context.value(
        exact_value(std::move(result))));
}
expr cos(const expr &value){
    require_state(value);
    if(!value.is_number()) return expr(value.state_, ::cos(value.node_));
    Number result = numeric_function(
        value, [](const Number &x){ return ::cos(x); }, "cos");
    return expr(value.state_, value.state_->context.value(
        exact_value(std::move(result))));
}
expr tan(const expr &value){
    require_state(value);
    if(!value.is_number()) return expr(value.state_, ::tan(value.node_));
    Number result = numeric_function(
        value, [](const Number &x){ return ::tan(x); }, "tan");
    return expr(value.state_, value.state_->context.value(
        exact_value(std::move(result))));
}
expr asin(const expr &value){
    require_state(value);
    if(!value.is_number()) return expr(value.state_, ::asin(value.node_));
    Number result = numeric_function(
        value, [](const Number &x){ return ::asin(x); }, "asin");
    return expr(value.state_, value.state_->context.value(
        exact_value(std::move(result))));
}
expr acos(const expr &value){
    require_state(value);
    if(!value.is_number()) return expr(value.state_, ::acos(value.node_));
    Number result = numeric_function(
        value, [](const Number &x){ return ::acos(x); }, "acos");
    return expr(value.state_, value.state_->context.value(
        exact_value(std::move(result))));
}
expr atan(const expr &value){
    require_state(value);
    if(!value.is_number()) return expr(value.state_, ::atan(value.node_));
    Number result = numeric_function(
        value, [](const Number &x){ return ::atan(x); }, "atan");
    return expr(value.state_, value.state_->context.value(
        exact_value(std::move(result))));
}
expr sinh(const expr &value){
    require_state(value);
    if(!value.is_number()) return expr(value.state_, ::sinh(value.node_));
    Number result = numeric_function(
        value, [](const Number &x){ return ::sinh(x); }, "sinh");
    return expr(value.state_, value.state_->context.value(
        exact_value(std::move(result))));
}
expr cosh(const expr &value){
    require_state(value);
    if(!value.is_number()) return expr(value.state_, ::cosh(value.node_));
    Number result = numeric_function(
        value, [](const Number &x){ return ::cosh(x); }, "cosh");
    return expr(value.state_, value.state_->context.value(
        exact_value(std::move(result))));
}
expr tanh(const expr &value){
    require_state(value);
    if(!value.is_number()) return expr(value.state_, ::tanh(value.node_));
    Number result = numeric_function(
        value, [](const Number &x){ return ::tanh(x); }, "tanh");
    return expr(value.state_, value.state_->context.value(
        exact_value(std::move(result))));
}
expr asinh(const expr &value){
    require_state(value);
    if(!value.is_number()) return expr(value.state_, ::asinh(value.node_));
    Number result = numeric_function(
        value, [](const Number &x){ return ::asinh(x); }, "asinh");
    return expr(value.state_, value.state_->context.value(
        exact_value(std::move(result))));
}
expr acosh(const expr &value){
    require_state(value);
    if(!value.is_number()) return expr(value.state_, ::acosh(value.node_));
    Number result = numeric_function(
        value, [](const Number &x){ return ::acosh(x); }, "acosh");
    return expr(value.state_, value.state_->context.value(
        exact_value(std::move(result))));
}
expr atanh(const expr &value){
    require_state(value);
    if(!value.is_number()) return expr(value.state_, ::atanh(value.node_));
    Number result = numeric_function(
        value, [](const Number &x){ return ::atanh(x); }, "atanh");
    return expr(value.state_, value.state_->context.value(
        exact_value(std::move(result))));
}
expr log2(const expr &value){
    require_state(value);
    if(!value.is_number()) return expr(value.state_, ::log2(value.node_));
    Number result = numeric_function(
        value, [](const Number &x){ return ::log2(x); }, "log2");
    return expr(value.state_, value.state_->context.value(
        exact_value(std::move(result))));
}
expr log10(const expr &value){
    require_state(value);
    if(!value.is_number()) return expr(value.state_, ::log10(value.node_));
    Number result = numeric_function(
        value, [](const Number &x){ return ::log10(x); }, "log10");
    return expr(value.state_, value.state_->context.value(
        exact_value(std::move(result))));
}
bool operator==(const expr &a, const expr &b){
    if(!a.valid() || !b.valid()) return !a.valid() && !b.valid();
    return a.state_ == b.state_ && a.node_ == b.node_;
}
bool operator!=(const expr &a, const expr &b){ return !(a == b); }
