#include"../prec.hpp"

#include<cassert>
#include<cstdio>

int main(){
    precn_set_ntt_threads(1);
    assert(precn_ntt_threads() == 1);
    assert(!precn_ntt_thread_parallel_enabled());

    precn_set_ntt_thread_parallel(true);
    assert(!precn_ntt_thread_parallel_enabled());

    precn_t a = (precn_t(1) << 8192) - 1;
    precn_t b = (precn_t(1) << 4096) + 1;
    assert(mul_vst(a, b) == mul_basic(a, b));
    puts("vst threads ok");
    return 0;
}
