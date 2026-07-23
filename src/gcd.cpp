#include"../prec.hpp"

#include<utility>

precn_t gcd(const precn_t &a, const precn_t &b){
    precn_t x(a);
    precn_t y(b);

    while(y.rsiz != 0){
        precn_t r;
        mod_into(r, x, y);
        x = std::move(y);
        y = std::move(r);
    }

    return x;
}
