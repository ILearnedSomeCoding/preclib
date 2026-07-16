#include"../prec.hpp"
#include<vector>

#define DEC_CHUNK_BASE 1000000000u
#define DEC_CHUNK_DIGITS 9

static precn_t dec_pow_chunks(size_t n, std::vector<precn_t> &pow2){
    if(n == 0) return precn_t(1);

    size_t bit = 0;
    size_t t = n;
    while(t >>= 1){
        ++bit;
        while(pow2.size() <= bit) pow2.push_back(pow2.back() * pow2.back());
    }

    precn_t r(1);
    bit = 0;
    while(n){
        if(n & 1) r = r * pow2[bit];
        n >>= 1;
        ++bit;
    }
    return r;
}

static precn_t dec_chunks_to_prec(const std::vector<uint32_t> &chunks,
                                  size_t l, size_t r,
                                  std::vector<precn_t> &pow2){
    size_t n = r - l;
    if(n == 0) return precn_t();

    if(n <= 16){
        precn_t out;
        for(size_t i = r; i > l; --i){
            out = mul_u32(out, DEC_CHUNK_BASE) + precn_t(chunks[i - 1]);
        }
        return out;
    }

    size_t m = l + n / 2;
    precn_t lo = dec_chunks_to_prec(chunks, l, m, pow2);
    precn_t hi = dec_chunks_to_prec(chunks, m, r, pow2);
    return hi * dec_pow_chunks(m - l, pow2) + lo;
}

precn_t::precn_t(){
    a = (uint64_t*) malloc(sizeof(uint64_t));
    asiz = 1;
    rsiz = 0;
    *a = 0;
}
precn_t::precn_t(const precn_t &o){
    asiz = std::max<size_t>(o.rsiz, 1);
    rsiz = o.rsiz;
    a = (uint64_t*) malloc(asiz * sizeof(uint64_t));
    if(rsiz) memcpy(a, o.a, rsiz * sizeof(uint64_t));
    else a[0] = 0;
}
precn_t::precn_t(precn_t &&o){
    asiz = o.asiz;
    rsiz = o.rsiz;
    a = o.a;
    o.a = nullptr; // shouldnt you free it? no, because it is moved, not copied
}
precn_t::precn_t(std::string o){
    a = (uint64_t*) malloc(sizeof(uint64_t));
    asiz = 1;
    rsiz = 0;
    *a = 0;

    std::string digits;
    for(size_t i = 0; i < o.size(); ++i){
        if(o[i] >= '0' && o[i] <= '9') digits.push_back(o[i]);
    }
    if(digits.empty()) return;

    std::vector<uint32_t> chunks;
    for(size_t pos = digits.size(); pos > 0;){
        size_t start = pos > DEC_CHUNK_DIGITS ? pos - DEC_CHUNK_DIGITS : 0;
        uint32_t x = 0;
        for(size_t i = start; i < pos; ++i) x = x * 10 + (uint32_t)(digits[i] - '0');
        chunks.push_back(x);
        pos = start;
    }
    while(!chunks.empty() && chunks.back() == 0) chunks.pop_back();
    if(chunks.empty()) return;

    std::vector<precn_t> pow2;
    pow2.push_back(precn_t(DEC_CHUNK_BASE));
    *this = dec_chunks_to_prec(chunks, 0, chunks.size(), pow2);
}

precn_t::operator std::string() const{
    if(rsiz == 0) return std::string("0");

    uint64_t top = a[rsiz - 1];
    size_t bits = (rsiz - 1) * 64;
    while(top){
        ++bits;
        top >>= 1;
    }
    // 30103 / 100000 is a strict upper approximation of log10(2).
    std::vector<uint32_t> digits(bits * 30103 / 100000 + 2);
    size_t n = 0;
    precn_base_convert(*this, 10, digits.data(), n);

    std::string s;
    s.reserve(n);
    for(size_t i = n; i > 0; --i) s.push_back((char)('0' + digits[i - 1]));
    return s;
}

precn_t &precn_t::operator=(const precn_t &o){
    if(this == &o) return *this;
    asiz = std::max<size_t>(o.rsiz, 1);
    rsiz = o.rsiz;
    a = (uint64_t*) realloc(a, asiz * sizeof(uint64_t));
    if(rsiz) memcpy(a, o.a, rsiz * sizeof(uint64_t));
    else a[0] = 0;
    return *this;
}
precn_t &precn_t::operator=(precn_t &&o){
    if(this == &o) return *this;
    free(a);
    asiz = o.asiz;
    rsiz = o.rsiz;
    a = o.a;
    o.a = nullptr;
    return *this;
}

precn_t::~precn_t(){
    free(a);
}
