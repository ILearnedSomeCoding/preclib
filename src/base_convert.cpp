#include"../prec.hpp"

#include<vector>

static int bc_cmp(const precn_t &a, const precn_t &b){
    if(a.rsiz != b.rsiz) return a.rsiz < b.rsiz ? -1 : 1;
    for(size_t i = a.rsiz; i > 0; --i){
        if(a.a[i - 1] != b.a[i - 1]) return a.a[i - 1] < b.a[i - 1] ? -1 : 1;
    }
    return 0;
}

static uint32_t bc_low_u32(const precn_t &a){
    return a.rsiz == 0 ? 0 : a.a[0];
}

static void bc_split(const precn_t &a, const precn_t &p, precn_t &q, precn_t &r){
    q = a / p;
    r = a - q * p;
}

static void bc_make_powers(uint32_t chunk_base, const precn_t &a, std::vector<precn_t> &pow2){
    // pow2[i] = chunk_base^(2^i).  These are the split points for the
    // divide-and-conquer conversion tree.
    pow2.push_back(precn_t(chunk_base));
    while(bc_cmp(a, pow2.back()) >= 0){
        pow2.push_back(pow2.back() * pow2.back());
    }
}

static void bc_emit_fixed_chunks(const precn_t &a, size_t level,
                                 const std::vector<precn_t> &pow2,
                                 std::vector<uint32_t> &chunks){
    // Emit exactly 2^level chunks, padding high zero chunks if needed.  This is
    // required for the low half of a split so middle zero chunks are preserved.
    if(level == 0){
        chunks.push_back(bc_low_u32(a));
        return;
    }

    precn_t q, r;
    bc_split(a, pow2[level - 1], q, r);
    bc_emit_fixed_chunks(r, level - 1, pow2, chunks);
    bc_emit_fixed_chunks(q, level - 1, pow2, chunks);
}

static void bc_emit_chunks(const precn_t &a, size_t level,
                           const std::vector<precn_t> &pow2,
                           std::vector<uint32_t> &chunks){
    // Emit the top-level chunk list with leading zero chunks trimmed.  Each
    // recursion splits by chunk_base^(2^(level-1)), so operand sizes roughly
    // halve at every level instead of shrinking by one chunk per division.
    if(a.rsiz == 0) return;
    if(level == 0){
        chunks.push_back(bc_low_u32(a));
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

    uint64_t power64 = base;
    size_t chunk_digits = 1;
    while(power64 * base <= 0xFFFFFFFFULL){
        power64 *= base;
        ++chunk_digits;
    }
    uint32_t power = (uint32_t)power64;

    // First convert to large chunks in base power=base^chunk_digits, then
    // expand each chunk into ordinary base digits.
    std::vector<precn_t> pow2;
    bc_make_powers(power, a, pow2);

    std::vector<uint32_t> chunks;
    bc_emit_chunks(a, pow2.size() - 1, pow2, chunks);

    std::vector<uint32_t> digits;
    for(size_t ci = 0; ci < chunks.size(); ++ci){
        uint64_t rem = chunks[ci];
        for(size_t i = 0; i < chunk_digits; ++i){
            digits.push_back((uint32_t)(rem % base));
            rem /= base;
        }
    }

    while(!digits.empty() && digits.back() == 0) digits.pop_back();
    out_siz = digits.size();
    if(out){
        for(size_t i = 0; i < out_siz; ++i) out[i] = digits[i];
    }
}
