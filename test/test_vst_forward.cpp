#define VST_DOUBLE_INVERSE_RADIX4 1
#include "../src/mul_vst.cpp"
#include <cstdio>

// White-box comparison before the fused length-2 product. Both transforms
// must produce exactly the same canonical residues, including padded zeros.
int main(){
#if PRECN_VST_HAVE_AVX2
    for(size_t n = 2; n <= (size_t(1) << 19); n <<= 1){
        const auto &plan = vst_get_plan(n, true);
        for(unsigned pattern = 0; pattern < 3; ++pattern){
            std::vector<vst_word_t> reference(n / 2), actual(n / 2);
            std::vector<vst_packed_word_t> compact(n / 2);
            uint64_t seed = 713;
            for(size_t i = 0; i < n / 2; ++i){
                for(size_t lane = 0; lane < 4; ++lane){
                    seed = seed * 6364136223846793005ULL + 1;
                    uint32_t mod = VST_PACKED_MODS[lane & 1];
                    uint32_t value = pattern == 0 ? mod - 1 :
                        pattern == 1 && i > n / 8 ? 0 : uint32_t(seed % mod);
                    reference[i].v[lane] = actual[i].v[lane] = value;
                    compact[i].v[lane] = value;
                }
            }
            vst_forward2_radix2_outer(reference, plan);
            vst_forward2_outer(actual, plan);
            vst_forward2_outer(compact, plan);
            for(size_t i = 0; i < n / 2; ++i)
                for(size_t lane = 0; lane < 4; ++lane)
                    if(reference[i].v[lane] != actual[i].v[lane] ||
                       reference[i].v[lane] != compact[i].v[lane]){
                        fprintf(stderr, "forward mismatch n=%zu pattern=%u\n", n, pattern);
                        return 1;
                    }
            vst_inverse2_radix2_outer(reference, plan);
            vst_inverse2_outer(actual, plan);
            vst_inverse2_outer(compact, plan);
            for(size_t i = 0; i < n / 2; ++i)
                for(size_t lane = 0; lane < 4; ++lane)
                    if(reference[i].v[lane] != actual[i].v[lane] ||
                       reference[i].v[lane] != compact[i].v[lane]){
                        fprintf(stderr, "inverse mismatch n=%zu pattern=%u\n", n, pattern);
                        return 2;
                    }
        }
    }
    puts("VST forward/inverse: double and compact radix-4 match radix-2");
#else
    puts("VST forward: AVX2 comparison skipped");
#endif
}
