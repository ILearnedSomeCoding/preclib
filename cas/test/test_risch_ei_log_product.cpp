#include"../prec_cas.hpp"

#include<cassert>
#include<cstdio>

static void check_ei_reduction(exact_context &context,
        const exact_expr &variable, const exact_expr &inner,
        const exact_expr &scale){
    exact_expr integrand = scale * context.exponential(inner) *
        context.natural_logarithm(inner);
    exact_expr primitive = context.integrate(integrand, variable);
    assert(primitive.valid());
    assert(primitive.operation() != exact_opcode::integral);
    assert(context.simplify(context.expand(
        context.differentiate(primitive, variable) - integrand,
        100000)) == context.integer(0));

    risch_result strict = context.integrate_elementary(integrand, variable);
    if(strict.status != risch_status::proven_nonelementary)
        std::fprintf(stderr, "strict status %d: %s\n", (int)strict.status,
            strict.diagnostic.c_str());
    assert(strict.status == risch_status::proven_nonelementary);
}

static void check_logarithmic_rde_obstruction(exact_context &context,
        const exact_expr &variable, const exact_expr &inner,
        const exact_expr &cofactor){
    exact_expr integrand = context.exponential(inner) * cofactor;
    risch_result strict = context.integrate_elementary(integrand, variable);
    if(strict.status != risch_status::proven_nonelementary)
        std::fprintf(stderr, "logarithmic RDE status %d: %s\n",
            (int)strict.status, strict.diagnostic.c_str());
    assert(strict.status == risch_status::proven_nonelementary);
    assert(strict.remainder != context.integer(0));
    assert(context.simplify(context.expand(
        context.differentiate(strict.elementary_part, variable) +
        strict.remainder - integrand, 100000)) == context.integer(0));
}

int main(){
    exact_context context;
    exact_expr x = context.symbol("x");
    check_ei_reduction(context, x, x, context.integer(1));
    check_ei_reduction(context, x,
        context.integer(2) * x + context.integer(1), context.integer(1));
    check_ei_reduction(context, x,
        context.integer(3) * x - context.integer(2), context.integer(7));
    exact_expr log_x = context.natural_logarithm(x);
    check_logarithmic_rde_obstruction(context, x, x,
        context.power(log_x, context.integer(2)));
    check_logarithmic_rde_obstruction(context, x,
        context.integer(2) * x + context.integer(1),
        context.power(log_x, context.integer(3)) +
            context.integer(3) * log_x + context.integer(2));
    exact_expr affine_inner = context.integer(2) * x + context.integer(1);
    exact_expr affine_log_polynomial = context.power(log_x, context.integer(3)) +
        context.integer(3) * log_x + context.integer(2);
    risch_result split_constant = context.integrate_elementary(
        context.exponential(affine_inner) * affine_log_polynomial, x);
    assert(split_constant.status == risch_status::proven_nonelementary);
    assert(split_constant.elementary_part == context.exponential(affine_inner));
    std::puts("logarithmic hyperexponential Risch reductions ok");
}
