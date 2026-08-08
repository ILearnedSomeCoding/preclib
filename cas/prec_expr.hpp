#pragma once

#include"prec_cas.hpp"

#include<memory>
#include<string>
#include<type_traits>
#include<vector>

struct expr_state;
class expr_context;

// General symbolic expression. Unlike exact_expr, numeric leaves may contain
// an arbitrary-precision approximate Number.
class expr{
    std::shared_ptr<expr_state> state_;
    exact_expr node_;

    expr(std::shared_ptr<expr_state> state, exact_expr node);

public:
    expr();

    bool valid() const;
    bool is_number() const;
    bool is_approximate() const;
    bool same_context(const expr &other) const;
    double context_precision() const;
    Number number() const;
    exact_expr exact_expression() const;
    std::string to_string() const;

    friend class expr_context;
    friend expr operator+(const expr &a, const expr &b);
    friend expr operator-(const expr &a, const expr &b);
    friend expr operator-(const expr &a);
    friend expr operator*(const expr &a, const expr &b);
    friend expr operator/(const expr &a, const expr &b);
    friend expr pow(const expr &base, const expr &exponent);
    friend expr sqrt(const expr &value);
    friend expr exp(const expr &value);
    friend expr ln(const expr &value);
    friend expr sin(const expr &value);
    friend expr cos(const expr &value);
    friend expr tan(const expr &value);
    friend expr sinh(const expr &value);
    friend expr cosh(const expr &value);
    friend expr tanh(const expr &value);
    friend bool operator==(const expr &a, const expr &b);
};

class expr_context{
    std::shared_ptr<expr_state> state_;

public:
    explicit expr_context(double precision_bits = 256.0);

    double precision() const;
    void set_precision(double bits);

    expr number(const Number &value);
    expr number(Number &&value);
    expr floating(float value);
    expr floating(double value);
    expr exact_integer(const precz_t &value);
    template<class T,
             typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
    expr integer(T value);
    expr symbol(const std::string &name);

    expr add(const std::vector<expr> &terms);
    expr multiply(const std::vector<expr> &factors);
    expr power(const expr &base, const expr &exponent);
    expr square_root(const expr &value);
    expr simplify(const expr &value, size_t automatic_expansion_terms = 64);
    expr expand(const expr &value, size_t maximum_terms = 100000);
};

template<class T, typename std::enable_if<std::is_integral<T>::value, int>::type>
expr expr_context::integer(T value){
    return exact_integer(precz_t(value));
}

expr operator+(const expr &a, const expr &b);
expr operator-(const expr &a, const expr &b);
expr operator-(const expr &a);
expr operator*(const expr &a, const expr &b);
expr operator/(const expr &a, const expr &b);
expr pow(const expr &base, const expr &exponent);
expr sqrt(const expr &value);
expr exp(const expr &value);
expr ln(const expr &value);
expr sin(const expr &value);
expr cos(const expr &value);
expr tan(const expr &value);
expr sinh(const expr &value);
expr cosh(const expr &value);
expr tanh(const expr &value);
bool operator==(const expr &a, const expr &b);
bool operator!=(const expr &a, const expr &b);
