#include"../src/prec_cas.cpp"

#include<cassert>
#include<cstdio>

int main(){
    exact_context context;
    exact_expr x = context.symbol("x");
    exact_expr general_quartic=context.power(x,context.integer(4))+
        context.power(x,context.integer(2))+x+context.integer(1);
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
    for(unsigned numerator_degree=0;numerator_degree<4;++numerator_degree){
        exact_expr numerator=context.power(x,context.integer(numerator_degree));
        exact_expr integrand=numerator/general_quartic;
        exact_expr expanded=context.expand(context.integrate(integrand,x));
        std::string text=expanded.to_string();
        assert(text.find("LogRootSum(")==std::string::npos);
        assert(text.find("i")==std::string::npos);
        exact_expr expanded_derivative=context.differentiate(expanded,x);
        for(int point=-2;point<=2;++point){
            long long point_power=1;
            for(unsigned i=0;i<numerator_degree;++i) point_power*=point;
            long long denominator_value=(long long)point*point*point*point+
                (long long)point*point+point+1;
            exact_expr sample=context.substitute(expanded_derivative,x,
                context.integer(point));
            Number seed(1.0);
            seed.set_precision(192);
            exact_expr approximate=context.simplify(
                context.value(numeric_value(std::move(seed)))*sample);
            assert(approximate.is_value() &&
                   approximate.value().is_approximate());
            Number actual=approximate.value().to_number(192);
            Number expected=Number(point_power)/Number(denominator_value);
            expected.set_precision(192);
            Number tolerance=Number(1)>>150;
            assert(abs(actual-expected)<tolerance);
        }
        risch_result strict=context.integrate_elementary(integrand,x);
        assert(strict.status==risch_status::elementary);
        assert(strict.remainder==context.integer(0));
    }
    std::puts("risch real quartic rational ok");
}
