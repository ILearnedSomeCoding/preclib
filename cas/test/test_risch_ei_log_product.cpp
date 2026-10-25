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

int main(){
    exact_context context;
    exact_expr x = context.symbol("x");
    check_ei_reduction(context, x, x, context.integer(1));
    check_ei_reduction(context, x,
        context.integer(2) * x + context.integer(1), context.integer(1));
    check_ei_reduction(context, x,
        context.integer(3) * x - context.integer(2), context.integer(7));
    std::puts("Ei logarithmic-product reduction ok");
}
