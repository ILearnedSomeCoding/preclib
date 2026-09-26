#include "../ntheory/factor_integer.hpp"
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <string>

int main(int argc, char **argv){
    precn_t n(argc > 1 ? argv[1] :
        "481194872507456405092204386031886283731237528681273399132383");
    unsigned curves = argc > 2 ? (unsigned)std::strtoul(argv[2], nullptr, 10) : 16;
    uint32_t b1 = argc > 3 ? (uint32_t)std::strtoul(argv[3], nullptr, 10) : 10000;
    uint32_t b2 = argc > 4 ? (uint32_t)std::strtoul(argv[4], nullptr, 10) : 300000;
    auto start = std::chrono::steady_clock::now();
    precn_t factor = cas_ecm_factor(n, curves, b1, b2);
    double elapsed = std::chrono::duration<double>(
        std::chrono::steady_clock::now() - start).count();
    std::printf("curves %u B1 %u B2 %u\ntime %.9f sec\n", curves, b1, b2, elapsed);
    if(!factor.rsiz){
        std::puts("budget exhausted; factor not found");
        return 1;
    }
    if(factor <= precn_t(1) || factor >= n || (n % factor).rsiz){
        std::puts("invalid factor");
        return 2;
    }
    std::printf("factor %s\ncofactor %s\n", ((std::string)factor).c_str(),
                ((std::string)(n / factor)).c_str());
    return 0;
}
