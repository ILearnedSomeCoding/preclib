#include"../prec.hpp"
precn_t::precn_t(){
    a = (uint32_t*) malloc(4);
    asiz = 1;
    rsiz = 0;
    *a = 0;
}
precn_t::precn_t(const precn_t &o){
    asiz = o.asiz;
    rsiz = o.rsiz;
    a = (uint32_t*) malloc(asiz * 4);
    memcpy(a, o.a, rsiz * 4);
}
precn_t::precn_t(precn_t &&o){
    asiz = o.asiz;
    rsiz = o.rsiz;
    a = o.a;
    o.a = nullptr; // shouldnt you free it? no, because it is moved, not copied
}
precn_t::precn_t(std::string o){
    // TODO: Switch to faster stuff after I implemented fast division
    a = (uint32_t*) malloc(4);
    asiz = 1;
    rsiz = 0;
    *a = 0;

    for(size_t i = 0; i < o.size(); ++i){
        if(o[i] < '0' || o[i] > '9') continue;
        *this = mul_u32(*this, 10) + precn_t((uint32_t)(o[i] - '0'));
    }
}

precn_t &precn_t::operator=(const precn_t &o){
    if(this == &o) return *this;
    asiz = o.asiz;
    rsiz = o.rsiz;
    a = (uint32_t*) realloc(a, asiz * 4);
    memcpy(a, o.a, rsiz * 4);
    return *this;
}
precn_t &precn_t::operator=(precn_t &&o){
    if(this == &o) return *this;
    asiz = o.asiz;
    rsiz = o.rsiz;
    a = o.a;
    o.a = nullptr; // shouldnt you free it? no, because it is moved, not copied
    return *this;
}

precn_t::~precn_t(){
    free(a);
}
