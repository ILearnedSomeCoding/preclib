#include"../prec.hpp"

#include<chrono>
#include<cstdio>
#include<string>

int main(int argc, char **argv){
    size_t digits = argc > 1 ? (size_t)strtoull(argv[1], nullptr, 10) : 1000000;
    size_t reps = argc > 2 ? (size_t)strtoull(argv[2], nullptr, 10) : 10;
    size_t bits = (size_t)((double)digits * 3.32192809488736234787) + 1;
    precn_t value = (precn_t(1) << bits) - precn_t(1);

    size_t total = 0;
    std::string text;
    auto begin = std::chrono::steady_clock::now();
    for(size_t i = 0; i < reps; ++i){
        text = precn_to_decimal(value);
        total += text.size();
    }
    auto end = std::chrono::steady_clock::now();
    double elapsed = std::chrono::duration<double>(end - begin).count();
    printf("digits %zu reps %zu average %.9f sec result_digits %zu check %zu\n",
           digits, reps, elapsed / (double)reps, text.size(), total);
    return 0;
}
