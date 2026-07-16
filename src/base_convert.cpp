#include"../prec.hpp"

#include<vector>

#define BC_MULINV_THRESHOLD 32768

static int bc_cmp(const precn_t &a, const precn_t &b){
    if(a.rsiz != b.rsiz) return a.rsiz < b.rsiz ? -1 : 1;
    for(size_t i = a.rsiz; i > 0; --i){
        if(a.a[i - 1] != b.a[i - 1]) return a.a[i - 1] < b.a[i - 1] ? -1 : 1;
    }
    return 0;
}

static uint64_t bc_low_u64(const precn_t &a){
    return a.rsiz == 0 ? 0 : a.a[0];
}

static unsigned bc_pow2_bits(uint32_t base){
    if(base < 2 || (base & (base - 1))) return 0;
    unsigned bits = 0;
    while(base > 1){
        ++bits;
        base >>= 1;
    }
    return bits;
}

static size_t bc_bit_length(const precn_t &a){
    if(a.rsiz == 0) return 0;
#if defined(__clang__) || defined(__GNUC__)
    return (a.rsiz - 1) * 64 + 64 - (size_t)__builtin_clzll(a.a[a.rsiz - 1]);
#else
    size_t bits = (a.rsiz - 1) * 64;
    uint64_t top = a.a[a.rsiz - 1];
    while(top){
        ++bits;
        top >>= 1;
    }
    return bits;
#endif
}

static void bc_split(const precn_t &a, const precn_t &p, precn_t &q, precn_t &r){
    // Conversion repeatedly divides by the same large powers.  At this
    // aspect ratio reciprocal division wins earlier than the general division
    // dispatcher, whose threshold also has to serve short-lived operands.
    if(p.rsiz >= BC_MULINV_THRESHOLD){
        q = div_mulinv(a, p);
        r = a - q * p;
        return;
    }
    divmod_into(q, r, a, p);
}

static void bc_make_powers(uint64_t chunk_base, const precn_t &a, std::vector<precn_t> &pow2){
    // pow2[i] = chunk_base^(2^i).  These are the split points for the
    // divide-and-conquer conversion tree.
    pow2.push_back(precn_t(chunk_base));
    while(bc_cmp(a, pow2.back()) >= 0){
        pow2.push_back(pow2.back() * pow2.back());
    }
}

static void bc_emit_fixed_chunks(const precn_t &a, size_t level,
                                 const std::vector<precn_t> &pow2,
                                 std::vector<uint64_t> &chunks){
    // Emit exactly 2^level chunks, padding high zero chunks if needed.  This is
    // required for the low half of a split so middle zero chunks are preserved.
    if(a.rsiz == 0){
        chunks.insert(chunks.end(), (size_t)1 << level, 0);
        return;
    }
    if(level == 0){
        chunks.push_back(bc_low_u64(a));
        return;
    }

    precn_t q, r;
    bc_split(a, pow2[level - 1], q, r);
    bc_emit_fixed_chunks(r, level - 1, pow2, chunks);
    bc_emit_fixed_chunks(q, level - 1, pow2, chunks);
}

static void bc_emit_chunks(const precn_t &a, size_t level,
                           const std::vector<precn_t> &pow2,
                           std::vector<uint64_t> &chunks){
    // Emit the top-level chunk list with leading zero chunks trimmed.  Each
    // recursion splits by chunk_base^(2^(level-1)), so operand sizes roughly
    // halve at every level instead of shrinking by one chunk per division.
    if(a.rsiz == 0) return;
    if(level == 0){
        chunks.push_back(bc_low_u64(a));
        return;
    }

    precn_t q, r;
    bc_split(a, pow2[level - 1], q, r);
    if(q.rsiz == 0){
        bc_emit_chunks(r, level - 1, pow2, chunks);
    }else{
        bc_emit_fixed_chunks(r, level - 1, pow2, chunks);
        bc_emit_chunks(q, level - 1, pow2, chunks);
    }
}

void precn_base_convert(const precn_t &a, uint32_t base, uint32_t *out, size_t &out_siz){
    out_siz = 0;
    if(a.rsiz == 0 || base < 2) return;

    unsigned pow2_bits = bc_pow2_bits(base);
    if(pow2_bits){
        out_siz = (bc_bit_length(a) + pow2_bits - 1) / pow2_bits;
        if(!out) return;

        uint64_t mask = ((uint64_t)1 << pow2_bits) - 1;
        for(size_t i = 0; i < out_siz; ++i){
            size_t bit = i * pow2_bits;
            size_t limb = bit / 64;
            unsigned offset = (unsigned)(bit % 64);
            uint64_t digit = a.a[limb] >> offset;
            if(offset + pow2_bits > 64 && limb + 1 < a.rsiz){
                digit |= a.a[limb + 1] << (64 - offset);
            }
            out[i] = (uint32_t)(digit & mask);
        }
        return;
    }

    uint64_t power64 = base;
    size_t chunk_digits = 1;
    while(power64 <= UINT64_MAX / base){
        power64 *= base;
        ++chunk_digits;
    }

    // First convert to large chunks in base power=base^chunk_digits, then
    // expand each chunk into ordinary base digits.
    std::vector<precn_t> pow2;
    bc_make_powers(power64, a, pow2);

    std::vector<uint64_t> chunks;
    // A maximal uint64_t chunk always contains at least 32 useful bits for
    // every non-power-of-two uint32_t base.
    chunks.reserve((bc_bit_length(a) + 31) / 32);
    bc_emit_chunks(a, pow2.size() - 1, pow2, chunks);

    std::vector<uint32_t> digits;
    digits.reserve(chunks.size() * chunk_digits);
    for(size_t ci = 0; ci < chunks.size(); ++ci){
        uint64_t rem = chunks[ci];
        if(base == 10){
            // Constant division lets clang turn /10 and %10 into a multiply
            // and shift instead of a hardware divide for every digit.
            for(size_t i = 0; i < chunk_digits; ++i){
                digits.push_back((uint32_t)(rem % 10));
                rem /= 10;
            }
        }else{
            for(size_t i = 0; i < chunk_digits; ++i){
                digits.push_back((uint32_t)(rem % base));
                rem /= base;
            }
        }
    }

    while(!digits.empty() && digits.back() == 0) digits.pop_back();
    out_siz = digits.size();
    if(out){
        for(size_t i = 0; i < out_siz; ++i) out[i] = digits[i];
    }
}
