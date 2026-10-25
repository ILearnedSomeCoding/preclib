#include"../src/prec_cas.cpp"

#include<cassert>
#include<cstdio>

int main(){
    exact_context context;
    exact_expr x=context.symbol("x");
    exact_expr radicand=context.power(x,context.integer(4))+context.integer(1);
    exact_expr root=context.square_root(radicand);
    auto verifies_decomposition=[&](const exact_expr &primitive,
                                   const exact_expr &remainder,
                                   const exact_expr &integrand,
                                   const exact_expr &curve_radicand,
                                   const exact_expr &curve_root){
        exact_expr y=context.symbol("_verify_y");
        integration_expr_poly modulus{
            -curve_radicand,context.integer(0),context.integer(1)};
        exact_expr error=context.differentiate(primitive,x)+remainder-integrand;
        error=context.substitute(error,curve_root,y);
        integration_expr_poly reduced;
        if(!integration_parse_algebraic_quotient(context,error,y,modulus,x,
                risch_options(),reduced)) return false;
        for(const exact_expr &coefficient : reduced)
            if(!integration_expr_zero(context,coefficient)) return false;
        return true;
    };
    auto verifies_derivative=[&](const exact_expr &primitive,
                                 const exact_expr &integrand,
                                 const exact_expr &curve_radicand,
                                 const exact_expr &curve_root){
        return verifies_decomposition(primitive,context.integer(0),integrand,
                                      curve_radicand,curve_root);
    };

    risch_result elliptic=context.integrate_elementary(
        context.integer(1)/root,x);
    assert(elliptic.status==risch_status::proven_nonelementary);
    assert(elliptic.remainder!=context.integer(0));

    exact_expr second_kind_integrand=context.power(x,context.integer(2))/root;
    risch_result second_kind=context.integrate_elementary(
        second_kind_integrand,x);
    assert(second_kind.status==risch_status::proven_nonelementary);
    assert(second_kind.remainder!=context.integer(0));
    exact_expr mixed_kind_integrand=(context.integer(1)+
        context.power(x,context.integer(2)))/root;
    risch_result mixed_kind=context.integrate_elementary(
        mixed_kind_integrand,x);
    assert(mixed_kind.status==risch_status::proven_nonelementary);
    assert(mixed_kind.remainder!=context.integer(0));

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
    assert(verifies_derivative(elementary.elementary_part,elementary_integrand,
                               radicand,root));

    exact_expr cubic_integrand=context.power(x,context.integer(3))/root;
    risch_result cubic=context.integrate_elementary(cubic_integrand,x);
    if(cubic.status!=risch_status::elementary)
        std::fprintf(stderr,"cubic case: status=%d diagnostic=%s remainder=%s\n",
            (int)cubic.status,cubic.diagnostic.c_str(),
            cubic.remainder.to_string().c_str());
    assert(cubic.status==risch_status::elementary);
    assert(cubic.remainder==context.integer(0));
    assert(verifies_derivative(cubic.elementary_part,cubic_integrand,radicand,root));

    exact_expr quintic_integrand=context.power(x,context.integer(5))/root;
    risch_result quintic=context.integrate_elementary(quintic_integrand,x);
    if(quintic.status!=risch_status::elementary)
        std::fprintf(stderr,"quintic case: status=%d diagnostic=%s remainder=%s\n",
            (int)quintic.status,quintic.diagnostic.c_str(),
            quintic.remainder.to_string().c_str());
    assert(quintic.status==risch_status::elementary);
    assert(quintic.remainder==context.integer(0));
    assert(verifies_derivative(quintic.elementary_part,quintic_integrand,radicand,root));

    exact_expr septic_integrand=context.power(x,context.integer(7))/root;
    risch_result septic=context.integrate_elementary(septic_integrand,x);
    if(septic.status!=risch_status::elementary)
        std::fprintf(stderr,"septic case: status=%d diagnostic=%s remainder=%s\n",
            (int)septic.status,septic.diagnostic.c_str(),
            septic.remainder.to_string().c_str());
    assert(septic.status==risch_status::elementary);
    assert(septic.remainder==context.integer(0));
    assert(verifies_derivative(septic.elementary_part,septic_integrand,radicand,root));

    exact_expr nonic_integrand=context.power(x,context.integer(9))/root;
    risch_result nonic=context.integrate_elementary(nonic_integrand,x);
    if(nonic.status!=risch_status::elementary)
        std::fprintf(stderr,"nonic case: status=%d diagnostic=%s remainder=%s\n",
            (int)nonic.status,nonic.diagnostic.c_str(),
            nonic.remainder.to_string().c_str());
    assert(nonic.status==risch_status::elementary);
    assert(nonic.remainder==context.integer(0));
    assert(verifies_derivative(nonic.elementary_part,nonic_integrand,radicand,root));

    exact_expr other_radicand=context.power(x,context.integer(4))+
        context.integer(2)*context.power(x,context.integer(2))+context.integer(2);
    exact_expr other_root=context.square_root(other_radicand);
    exact_expr other_second_kind_integrand=context.power(x,context.integer(2))/other_root;
    risch_result other_second_kind=context.integrate_elementary(
        other_second_kind_integrand,x);
    assert(other_second_kind.status==risch_status::proven_nonelementary);
    exact_expr other_elementary_integrand=x/other_root;
    risch_result other_elementary=context.integrate_elementary(
        other_elementary_integrand,x);
    assert(other_elementary.status==risch_status::elementary);
    assert(other_elementary.remainder==context.integer(0));
    assert(verifies_derivative(other_elementary.elementary_part,
        other_elementary_integrand,other_radicand,other_root));

    exact_expr translated_radicand=context.power(x,context.integer(4))+
        context.integer(4)*context.power(x,context.integer(3))+
        context.integer(8)*context.power(x,context.integer(2))+
        context.integer(8)*x+context.integer(5);
    exact_expr translated_root=context.square_root(translated_radicand);
    exact_expr translated_second_kind=context.power(x+context.integer(1),
        context.integer(2))/translated_root;
    risch_result translated_non_elementary=context.integrate_elementary(
        translated_second_kind,x);
    assert(translated_non_elementary.status==risch_status::proven_nonelementary);
    exact_expr translated_partial=x/translated_root;
    risch_result translated_mixed=context.integrate_elementary(
        translated_partial,x);
    if(translated_mixed.status!=risch_status::proven_nonelementary)
        std::fprintf(stderr,"translated mixed: status=%d diagnostic=%s part=%s remainder=%s\n",
            (int)translated_mixed.status,translated_mixed.diagnostic.c_str(),
            translated_mixed.elementary_part.to_string().c_str(),
            translated_mixed.remainder.to_string().c_str());
    assert(translated_mixed.status==risch_status::proven_nonelementary);
    assert(translated_mixed.elementary_part!=context.integer(0));
    assert(translated_mixed.remainder!=context.integer(0));
    assert(verifies_decomposition(translated_mixed.elementary_part,
        translated_mixed.remainder,translated_partial,translated_radicand,
        translated_root));
    exact_expr translated_elementary=(x+context.integer(1))/translated_root;
    risch_result translated_integral=context.integrate_elementary(
        translated_elementary,x);
    assert(translated_integral.status==risch_status::elementary);
    assert(translated_integral.remainder==context.integer(0));
    assert(verifies_derivative(translated_integral.elementary_part,
        translated_elementary,translated_radicand,translated_root));

    exact_expr affine_coordinate=context.integer(2)*x+context.integer(3);
    exact_expr affine_radicand=context.power(affine_coordinate,context.integer(4))+
        context.integer(2)*context.power(affine_coordinate,context.integer(2))+
        context.integer(2);
    exact_expr affine_root=context.square_root(affine_radicand);
    exact_expr affine_second_kind=context.power(affine_coordinate,context.integer(2)) /
        affine_root;
    risch_result affine_non_elementary=context.integrate_elementary(
        affine_second_kind,x);
    assert(affine_non_elementary.status==risch_status::proven_nonelementary);
    assert(affine_non_elementary.remainder!=context.integer(0));

    std::puts("risch hyperelliptic quartic ok");
}
