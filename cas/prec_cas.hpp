#pragma once

#include"../prec_num.hpp"

#include<cstddef>
#include<cstdint>
#include<initializer_list>
#include<memory>
#include<string>
#include<type_traits>
#include<variant>
#include<vector>

enum class exact_opcode : uint8_t{
    value = 0,
    symbol = 1,
    add = 2,
    multiply = 3,
    power = 4,
    square_root = 5,
    exponential = 6,
    sine = 7,
    cosine = 8,
    tangent = 9,
    hyperbolic_sine = 10,
    hyperbolic_cosine = 11,
    hyperbolic_tangent = 12,
    bounded_sum = 13,
    constant_pi = 14,
    constant_e = 15,
    arc_sine = 16,
    arc_cosine = 17,
    arc_tangent = 18,
    inverse_hyperbolic_sine = 19,
    inverse_hyperbolic_cosine = 20,
    inverse_hyperbolic_tangent = 21,
    natural_logarithm = 22,
    logarithm_base_2 = 23,
    logarithm_base_10 = 24,
    constant_i = 25,
    expression_list = 26,
    absolute_value = 27,
    sine_integral = 28,
    cosine_integral = 29,
    exponential_integral = 30,
    error_function = 31,
    imaginary_error_function = 32,
    partial_gamma = 33,
    derivative = 34,
    integral = 35,
    rule = 36
};

const char *exact_opcode_name(exact_opcode operation);

class exact_value{
    std::variant<precz_t, precq_t, Number> value_;

public:
    exact_value();
    template<class T, typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
    exact_value(T value) : value_(precz_t(value)){}
    exact_value(const precz_t &value);
    exact_value(precz_t &&value);
    exact_value(const precq_t &value);
    exact_value(precq_t &&value);
    exact_value(const Number &value);
    exact_value(Number &&value);

    bool is_integer() const;
    bool is_rational() const;
    bool is_approximate() const;
    bool is_zero() const;
    bool is_one() const;
    bool is_minus_one() const;
    bool is_negative() const;
    const precz_t &integer() const;
    precq_t rational() const;
    const Number &number() const;
    Number to_number(double precision_bits = 64.0) const;
    std::string to_string() const;

    friend exact_value operator+(const exact_value &a, const exact_value &b);
    friend exact_value operator-(const exact_value &a, const exact_value &b);
    friend exact_value operator-(const exact_value &a);
    friend exact_value operator*(const exact_value &a, const exact_value &b);
    friend exact_value operator/(const exact_value &a, const exact_value &b);
    friend bool operator==(const exact_value &a, const exact_value &b);
};

exact_value operator+(const exact_value &a, const exact_value &b);
exact_value operator-(const exact_value &a, const exact_value &b);
exact_value operator-(const exact_value &a);
exact_value operator*(const exact_value &a, const exact_value &b);
exact_value operator/(const exact_value &a, const exact_value &b);
bool operator==(const exact_value &a, const exact_value &b);
bool operator!=(const exact_value &a, const exact_value &b);

struct exact_storage;
class exact_context;
class exact_add_builder;
class exact_complex;

class exact_expr{
    std::shared_ptr<exact_storage> storage_;
    uint32_t root_;

    exact_expr(std::shared_ptr<exact_storage> storage, uint32_t root);

public:
    exact_expr();

    bool valid() const;
    uint32_t id() const;
    exact_opcode operation() const;
    size_t operand_count() const;
    exact_expr operand(size_t index) const;
    size_t reachable_node_count() const;
    size_t depth() const;
    std::string debug_tree(size_t maximum_nodes = 256) const;
    bool is_value() const;
    exact_value value() const;
    std::string to_string() const;

    friend class exact_context;
    friend class exact_add_builder;
    friend exact_expr operator+(const exact_expr &a, const exact_expr &b);
    friend exact_expr operator-(const exact_expr &a, const exact_expr &b);
    friend exact_expr operator-(const exact_expr &a);
    friend exact_expr operator*(const exact_expr &a, const exact_expr &b);
    friend exact_expr operator/(const exact_expr &a, const exact_expr &b);
    friend exact_expr pow(const exact_expr &base, const exact_expr &exponent);
    friend exact_expr sqrt(const exact_expr &value);
    friend exact_expr abs(const exact_expr &value);
    friend exact_expr exp(const exact_expr &value);
    friend exact_expr sin(const exact_expr &value);
    friend exact_expr cos(const exact_expr &value);
    friend exact_expr tan(const exact_expr &value);
    friend exact_expr asin(const exact_expr &value);
    friend exact_expr acos(const exact_expr &value);
    friend exact_expr atan(const exact_expr &value);
    friend exact_expr sinh(const exact_expr &value);
    friend exact_expr cosh(const exact_expr &value);
    friend exact_expr tanh(const exact_expr &value);
    friend exact_expr asinh(const exact_expr &value);
    friend exact_expr acosh(const exact_expr &value);
    friend exact_expr atanh(const exact_expr &value);
    friend exact_expr ln(const exact_expr &value);
    friend exact_expr log2(const exact_expr &value);
    friend exact_expr log10(const exact_expr &value);
    friend exact_expr Si(const exact_expr &value);
    friend exact_expr Ci(const exact_expr &value);
    friend exact_expr Ei(const exact_expr &value);
    friend exact_expr erf(const exact_expr &value);
    friend exact_expr erfi(const exact_expr &value);
    friend exact_expr partial_gamma(const exact_expr &a, const exact_expr &x);
    friend exact_expr diff(const exact_expr &expression,
                           const exact_expr &variable);
    friend exact_expr integrate(const exact_expr &expression,
                                const exact_expr &variable);
    friend bool operator==(const exact_expr &a, const exact_expr &b);
    friend class exact_complex;
};

class exact_complex{
    exact_expr real_;
    exact_expr imag_;

public:
    exact_complex();
    explicit exact_complex(const exact_expr &real);
    exact_complex(const exact_expr &real, const exact_expr &imag);

    const exact_expr &real() const;
    const exact_expr &imag() const;
    exact_expr expression() const;
    bool valid() const;

    exact_complex &operator+=(const exact_complex &other);
    exact_complex &operator-=(const exact_complex &other);
    exact_complex &operator*=(const exact_complex &other);
    exact_complex &operator/=(const exact_complex &other);
};

exact_complex operator+(const exact_complex &a, const exact_complex &b);
exact_complex operator-(const exact_complex &a, const exact_complex &b);
exact_complex operator-(const exact_complex &a);
exact_complex operator*(const exact_complex &a, const exact_complex &b);
exact_complex operator/(const exact_complex &a, const exact_complex &b);
exact_complex conjugate(const exact_complex &a);
exact_expr norm(const exact_complex &a);

class exact_context{
    std::shared_ptr<exact_storage> storage_;

    friend exact_expr erfi(const exact_expr &value);
    explicit exact_context(std::shared_ptr<exact_storage> storage);
    exact_expr solve_polynomial_impl(
        const exact_expr &expression,
        const std::vector<exact_expr> &variables,
        bool require_exact_coefficients);
    exact_expr solve_system_impl(
        const std::vector<exact_expr> &equations,
        const std::vector<exact_expr> &variables,
        bool require_exact_coefficients);
    exact_expr solve_numeric_system_impl(
        const std::vector<exact_expr> &equations,
        const std::vector<exact_expr> &variables,
        double precision_bits);

public:
    exact_context();

    exact_expr value(const exact_value &value);
    exact_expr value(exact_value &&value);
    template<class T, typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
    exact_expr integer(T value){ return this->value(exact_value(value)); }
    exact_expr rational(const precq_t &value);
    exact_expr symbol(const std::string &name);
    exact_expr pi();
    exact_expr e();
    exact_expr i();
    void assume(const exact_expr &symbol, const std::string &property);

    exact_expr add(const std::vector<exact_expr> &terms);
    exact_expr add(std::initializer_list<exact_expr> terms);
    exact_expr subtract(const exact_expr &a, const exact_expr &b);
    exact_expr multiply(const std::vector<exact_expr> &factors);
    exact_expr multiply(std::initializer_list<exact_expr> factors);
    exact_expr divide(const exact_expr &a, const exact_expr &b);
    exact_expr power(const exact_expr &base, const exact_expr &exponent);
    exact_expr square_root(const exact_expr &value);
    exact_expr absolute_value(const exact_expr &value);
    exact_expr exponential(const exact_expr &value);
    exact_expr sine(const exact_expr &value);
    exact_expr cosine(const exact_expr &value);
    exact_expr tangent(const exact_expr &value);
    exact_expr arc_sine(const exact_expr &value);
    exact_expr arc_cosine(const exact_expr &value);
    exact_expr arc_tangent(const exact_expr &value);
    exact_expr hyperbolic_sine(const exact_expr &value);
    exact_expr hyperbolic_cosine(const exact_expr &value);
    exact_expr hyperbolic_tangent(const exact_expr &value);
    exact_expr inverse_hyperbolic_sine(const exact_expr &value);
    exact_expr inverse_hyperbolic_cosine(const exact_expr &value);
    exact_expr inverse_hyperbolic_tangent(const exact_expr &value);
    exact_expr natural_logarithm(const exact_expr &value);
    exact_expr logarithm_base_2(const exact_expr &value);
    exact_expr logarithm_base_10(const exact_expr &value);
    exact_expr sine_integral(const exact_expr &value);
    exact_expr cosine_integral(const exact_expr &value);
    exact_expr exponential_integral(const exact_expr &value);
    exact_expr error_function(const exact_expr &value);
    exact_expr imaginary_error_function(const exact_expr &value);
    exact_expr partial_gamma(const exact_expr &a, const exact_expr &x);
    exact_expr formal_derivative(const exact_expr &expression,
                                 const exact_expr &variable);
    exact_expr differentiate(const exact_expr &expression,
                             const exact_expr &variable);
    exact_expr integrate(const exact_expr &expression,
                         const exact_expr &variable);
    exact_expr dsolve(const exact_expr &equation,
                      const exact_expr &dependent,
                      const exact_expr &independent);
    exact_expr bounded_sum(const exact_expr &variable, const exact_expr &lower,
                           const exact_expr &upper, const exact_expr &body);
    exact_expr expand(const exact_expr &expression,
                      size_t maximum_terms = 100000);
    exact_expr factor(const exact_expr &expression);
    exact_expr groebner(const std::vector<exact_expr> &polynomials,
                        const std::vector<exact_expr> &variables);
    exact_expr factor_integer(const exact_expr &expression);
    exact_expr gcd(const exact_expr &left, const exact_expr &right);
    exact_expr simplify(const exact_expr &expression,
                        size_t automatic_expansion_terms = 64);
    exact_expr trig_expand(const exact_expr &expression);
    exact_expr trig_reduce(const exact_expr &expression);
    exact_expr substitute(const exact_expr &expression,
                          const exact_expr &target,
                          const exact_expr &replacement);
    bool is_polynomial(const exact_expr &expression) const;
    bool is_polynomial(const exact_expr &expression,
                       const std::vector<exact_expr> &variables) const;
    exact_expr exact_solve(const exact_expr &expression,
                           const std::vector<exact_expr> &variables);
    exact_expr exact_solve(const std::vector<exact_expr> &equations,
                           const std::vector<exact_expr> &variables);
    exact_expr exact_solve(std::initializer_list<exact_expr> equations,
                           const std::vector<exact_expr> &variables){
        return exact_solve(std::vector<exact_expr>(equations), variables);
    }
    exact_expr solve(const exact_expr &expression,
                     const std::vector<exact_expr> &variables,
                     double precision_bits = 256.0);
    exact_expr solve(const std::vector<exact_expr> &equations,
                     const std::vector<exact_expr> &variables,
                     double precision_bits = 256.0);
    exact_expr solve(std::initializer_list<exact_expr> equations,
                     const std::vector<exact_expr> &variables,
                     double precision_bits = 256.0){
        return solve(std::vector<exact_expr>(equations), variables,
                     precision_bits);
    }

    // Copy only nodes reachable from the supplied roots into a fresh arena.
    // Old handles remain valid and keep the old arena alive until destroyed.
    std::vector<exact_expr> compact(const std::vector<exact_expr> &roots);
    exact_expr compact(const exact_expr &root);

    exact_add_builder make_add_builder();
    size_t node_count() const;
    size_t operand_id_count() const;
    std::string debug_dump(size_t maximum_nodes = 0) const;

    friend class exact_add_builder;
    friend exact_expr operator+(const exact_expr &a, const exact_expr &b);
    friend exact_expr operator-(const exact_expr &a, const exact_expr &b);
    friend exact_expr operator-(const exact_expr &a);
    friend exact_expr operator*(const exact_expr &a, const exact_expr &b);
    friend exact_expr operator/(const exact_expr &a, const exact_expr &b);
    friend exact_expr pow(const exact_expr &base, const exact_expr &exponent);
    friend exact_expr sqrt(const exact_expr &value);
    friend exact_expr abs(const exact_expr &value);
    friend exact_expr exp(const exact_expr &value);
    friend exact_expr sin(const exact_expr &value);
    friend exact_expr cos(const exact_expr &value);
    friend exact_expr tan(const exact_expr &value);
    friend exact_expr asin(const exact_expr &value);
    friend exact_expr acos(const exact_expr &value);
    friend exact_expr atan(const exact_expr &value);
    friend exact_expr sinh(const exact_expr &value);
    friend exact_expr cosh(const exact_expr &value);
    friend exact_expr tanh(const exact_expr &value);
    friend exact_expr asinh(const exact_expr &value);
    friend exact_expr acosh(const exact_expr &value);
    friend exact_expr atanh(const exact_expr &value);
    friend exact_expr ln(const exact_expr &value);
    friend exact_expr log2(const exact_expr &value);
    friend exact_expr log10(const exact_expr &value);
    friend exact_expr Si(const exact_expr &value);
    friend exact_expr Ci(const exact_expr &value);
    friend exact_expr Ei(const exact_expr &value);
    friend exact_expr erf(const exact_expr &value);
    friend exact_expr partial_gamma(const exact_expr &a, const exact_expr &x);
    friend exact_expr diff(const exact_expr &expression,
                           const exact_expr &variable);
    friend exact_expr integrate(const exact_expr &expression,
                                const exact_expr &variable);
};

class exact_add_builder{
    std::shared_ptr<exact_storage> storage_;
    exact_value constant_;
    uint64_t positive_small_;
    uint64_t negative_small_;
    std::vector<uint32_t> terms_;

    explicit exact_add_builder(std::shared_ptr<exact_storage> storage);
    void add_positive(uint64_t value);
    void add_negative(uint64_t magnitude);
    void flush_small();

public:
    void add(const exact_value &value);
    void add(exact_value &&value);
    void add(const exact_expr &term);
    template<class T, typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
    void add_integer(T value){
        uint64_t bits = (uint64_t)value;
        if(std::is_signed<T>::value && value < 0) add_negative((uint64_t)0 - bits);
        else add_positive(bits);
    }
    exact_expr finish();

    friend class exact_context;
};

exact_expr operator+(const exact_expr &a, const exact_expr &b);
exact_expr operator-(const exact_expr &a, const exact_expr &b);
exact_expr operator-(const exact_expr &a);
exact_expr operator*(const exact_expr &a, const exact_expr &b);
exact_expr operator/(const exact_expr &a, const exact_expr &b);
exact_expr pow(const exact_expr &base, const exact_expr &exponent);
exact_expr sqrt(const exact_expr &value);
exact_expr abs(const exact_expr &value);
exact_expr exp(const exact_expr &value);
exact_expr sin(const exact_expr &value);
exact_expr cos(const exact_expr &value);
exact_expr tan(const exact_expr &value);
exact_expr asin(const exact_expr &value);
exact_expr acos(const exact_expr &value);
exact_expr atan(const exact_expr &value);
exact_expr sinh(const exact_expr &value);
exact_expr cosh(const exact_expr &value);
exact_expr tanh(const exact_expr &value);
exact_expr asinh(const exact_expr &value);
exact_expr acosh(const exact_expr &value);
exact_expr atanh(const exact_expr &value);
exact_expr ln(const exact_expr &value);
exact_expr log2(const exact_expr &value);
exact_expr log10(const exact_expr &value);
exact_expr Si(const exact_expr &value);
exact_expr Ci(const exact_expr &value);
exact_expr Ei(const exact_expr &value);
exact_expr erf(const exact_expr &value);
exact_expr erfi(const exact_expr &value);
exact_expr partial_gamma(const exact_expr &a, const exact_expr &x);
exact_expr diff(const exact_expr &expression, const exact_expr &variable);
exact_expr integrate(const exact_expr &expression, const exact_expr &variable);
bool operator==(const exact_expr &a, const exact_expr &b);
bool operator!=(const exact_expr &a, const exact_expr &b);

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
    friend expr abs(const expr &value);
    friend expr exp(const expr &value);
    friend expr ln(const expr &value);
    friend expr sin(const expr &value);
    friend expr cos(const expr &value);
    friend expr tan(const expr &value);
    friend expr asin(const expr &value);
    friend expr acos(const expr &value);
    friend expr atan(const expr &value);
    friend expr sinh(const expr &value);
    friend expr cosh(const expr &value);
    friend expr tanh(const expr &value);
    friend expr asinh(const expr &value);
    friend expr acosh(const expr &value);
    friend expr atanh(const expr &value);
    friend expr log2(const expr &value);
    friend expr log10(const expr &value);
    friend expr Si(const expr &value);
    friend expr Ci(const expr &value);
    friend expr Ei(const expr &value);
    friend expr erf(const expr &value);
    friend expr erfi(const expr &value);
    friend expr partial_gamma(const expr &a, const expr &x);
    friend expr diff(const expr &expression, const expr &variable);
    friend expr integrate(const expr &expression, const expr &variable);
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
    expr pi();
    expr e();

    expr add(const std::vector<expr> &terms);
    expr multiply(const std::vector<expr> &factors);
    expr power(const expr &base, const expr &exponent);
    expr square_root(const expr &value);
    expr absolute_value(const expr &value);
    expr simplify(const expr &value, size_t automatic_expansion_terms = 64);
    expr expand(const expr &value, size_t maximum_terms = 100000);
    expr factor(const expr &value);
    expr factor_integer(const expr &value);
    expr gcd(const expr &left, const expr &right);
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
expr abs(const expr &value);
expr exp(const expr &value);
expr ln(const expr &value);
expr sin(const expr &value);
expr cos(const expr &value);
expr tan(const expr &value);
expr asin(const expr &value);
expr acos(const expr &value);
expr atan(const expr &value);
expr sinh(const expr &value);
expr cosh(const expr &value);
expr tanh(const expr &value);
expr asinh(const expr &value);
expr acosh(const expr &value);
expr atanh(const expr &value);
expr log2(const expr &value);
expr log10(const expr &value);
expr Si(const expr &value);
expr Ci(const expr &value);
expr Ei(const expr &value);
expr erf(const expr &value);
expr erfi(const expr &value);
expr partial_gamma(const expr &a, const expr &x);
expr diff(const expr &expression, const expr &variable);
expr integrate(const expr &expression, const expr &variable);
bool operator==(const expr &a, const expr &b);
bool operator!=(const expr &a, const expr &b);
