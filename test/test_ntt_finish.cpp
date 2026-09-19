// White-box test of the residue representation at the NTT boundary.
// Link src/*.cpp EXCEPT mul_ntt.cpp, which is included here.
#include "../src/mul_ntt.cpp"
#include <cstdio>

static void check(bool ok){ if(!ok) std::abort(); }

int main(){
    precn_set_ntt_threads(1);
    precn_set_ntt_thread_parallel(false);
    uint64_t seed = 713;
    for(const auto &ctx : NTT_CTX){
        for(size_t n : {1u, 2u, 4u, 8u, 16u, 32u, 64u, 256u}){
            ntt_mod_plan_t p = ntt_make_mod_plan(n, ctx.mod, ctx.root);
            for(unsigned kind = 0; kind < 3; ++kind){
                std::vector<uint32_t> a(n), b(n);
                for(size_t i = 0; i < n; ++i){
                    seed = seed * 6364136223846793005ULL + 1;
                    a[i] = kind == 0 ? ctx.mod - 1 :
                           kind == 1 ? (i & 1 ? 0 : ctx.mod - 1) : seed % ctx.mod;
                    seed = seed * 6364136223846793005ULL + 1;
                    b[i] = kind == 0 ? ctx.mod - 1 :
                           kind == 1 ? (i == n - 1 ? 1 : 0) : seed % ctx.mod;
                }
                for(bool square : {false, true}){
                    const auto &right = square ? a : b;
                    std::vector<uint32_t> want(n, 0), x(n), y(n);
                    // Independent cyclic convolution in ordinary residues.
                    for(size_t i = 0; i < n; ++i)
                        for(size_t j = 0; j < n; ++j){
                            size_t k = (i + j) % n;
                            want[k] = (want[k] + uint64_t(a[i]) * right[j]) % ctx.mod;
                        }
                    for(size_t i = 0; i < n; ++i){
                        x[i] = mont_in(p.c, a[i]);
                        y[i] = mont_in(p.c, right[i]);
                    }
                    ntt_forward(x, p);
                    ntt_forward(y, p);
                    std::vector<uint32_t> saved_right = y;
                    ntt_finish_convolution(x, square ? x : y, p);
                    check(x == want);
                    check(y == saved_right);
                    // Reuse the same transformed right side for another left.
                    if(!square){
                        for(size_t i = 0; i < n; ++i) x[i] = mont_in(p.c, a[i]);
                        ntt_forward(x, p);
                        ntt_finish_convolution(x, y, p);
                        check(x == want && y == saved_right);
                    }
                }
            }
        }
    }
    puts("NTT finish: naive convolution, square, and shared-right checks passed");
}
