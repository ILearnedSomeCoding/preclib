#include"../src/factor_integer.hpp"

#include<chrono>
#include<cstdlib>
#include<cstdio>
#include<string>

int main(int argc, char **argv){
    const char *text = argc > 1 ? argv[1]
        : "3275698819458552334773298987025285875460883388189256110657795199";
    size_t polynomials = argc > 2 ? (size_t)std::strtoull(argv[2], nullptr, 10)
                                  : 60000;
    size_t interval = argc > 3 ? (size_t)std::strtoull(argv[3], nullptr, 10)
                               : 44072;
    precn_t value(text);
    auto begin = std::chrono::steady_clock::now();
    precn_t factor = cas_siqs_factor(value, polynomials, interval);
    double seconds = std::chrono::duration<double>(
        std::chrono::steady_clock::now() - begin).count();
    if(factor.rsiz){
        std::printf("factor %s\n", ((std::string)factor).c_str());
        std::printf("cofactor %s\n", ((std::string)(value / factor)).c_str());
        std::printf("valid %s\n", (value % factor).rsiz ? "no" : "yes");
    }else{
        std::puts("factor not found");
    }
    std::printf("time %.9f sec\n", seconds);
    return factor.rsiz && (value % factor).rsiz == 0 ? 0 : 1;
}
