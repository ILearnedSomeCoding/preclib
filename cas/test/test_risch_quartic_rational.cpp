#include"../src/prec_cas.cpp"

#include<cassert>
#include<cstdio>

int main(){
    exact_context context;
    exact_expr x = context.symbol("x");
    for(const exact_expr &denominator : {
            context.power(x,context.integer(4))+context.integer(1),
            context.power(x,context.integer(4))+context.power(x,context.integer(2))+
                context.integer(1),
            context.power(x,context.integer(4))+context.power(x,context.integer(2))+
                x+context.integer(1)}){
        exact_expr integrand=context.integer(1)/denominator;
        exact_expr compact=context.integrate(integrand,x);
        exact_expr expanded=context.expand(compact);
        std::string text=expanded.to_string();
        assert(text.find("LogRootSum(")==std::string::npos);
        assert(text.find("i") == std::string::npos);
        risch_result strict=context.integrate_elementary(integrand,x);
        assert(strict.status==risch_status::elementary);
        assert(strict.remainder==context.integer(0));
    }
    std::puts("risch real quartic rational ok");
}
