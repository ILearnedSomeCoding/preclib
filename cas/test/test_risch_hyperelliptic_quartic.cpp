#include"../src/prec_cas.cpp"

#include<cassert>
#include<cstdio>

int main(){
    exact_context context;
    exact_expr x=context.symbol("x");
    exact_expr radicand=context.power(x,context.integer(4))+context.integer(1);
    exact_expr root=context.square_root(radicand);

    risch_result elliptic=context.integrate_elementary(
        context.integer(1)/root,x);
    assert(elliptic.status==risch_status::proven_nonelementary);
    assert(elliptic.remainder!=context.integer(0));

    exact_expr elementary_integrand=x/root;
    risch_result elementary=context.integrate_elementary(
        elementary_integrand,x);
    if(elementary.status!=risch_status::elementary)
        std::fprintf(stderr,"positive case: status=%d diagnostic=%s part=%s remainder=%s\n",
            (int)elementary.status,elementary.diagnostic.c_str(),
            elementary.elementary_part.to_string().c_str(),
            elementary.remainder.to_string().c_str());
    assert(elementary.status==risch_status::elementary);
    assert(elementary.remainder==context.integer(0));
    exact_expr expected=context.natural_logarithm(
        context.power(x,context.integer(2))+root)/context.integer(2);
    assert(elementary.elementary_part==expected);

    std::puts("risch hyperelliptic quartic ok");
}
