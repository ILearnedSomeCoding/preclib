#ifndef PREC_CAS_FACTOR_INTEGER_HPP
#define PREC_CAS_FACTOR_INTEGER_HPP

#include"../../prec.hpp"

#include<vector>
#include<functional>
#include<mutex>

using cas_factor_progress_callback =
    std::function<void(const char *stage, size_t completed, size_t total)>;

// Notifications are serialized across workers. total == 0 means indeterminate.
// Callbacks must not start another factorization; exceptions are ignored.
class cas_factor_progress_scope{
    cas_factor_progress_callback callback_;
    std::mutex mutex_;
    cas_factor_progress_scope *previous_;
public:
    explicit cas_factor_progress_scope(cas_factor_progress_callback callback);
    ~cas_factor_progress_scope();
    cas_factor_progress_scope(const cas_factor_progress_scope &) = delete;
    cas_factor_progress_scope &operator=(const cas_factor_progress_scope &) = delete;
    void report(const char *stage, size_t completed = 0, size_t total = 0) noexcept;
    static cas_factor_progress_scope *current();
};

bool cas_probable_prime(const precn_t &value);
precn_t cas_pollard_rho_factor(const precn_t &value,
                               size_t iteration_limit = 1000000);
precn_t cas_ecm_factor(const precn_t &value, unsigned curves = 64,
                       uint32_t stage1_bound = 10000,
                       uint32_t stage2_bound = 50000);
precn_t cas_siqs_factor(const precn_t &value, size_t polynomials = 96,
                        size_t interval = 384);
precn_t cas_qs_factor(const precn_t &value, size_t maximum_relations = 4096);
bool cas_factor_big(const precn_t &value, std::vector<precn_t> &factors);
bool cas_factor_big_progress(const precn_t &value, std::vector<precn_t> &factors,
                            cas_factor_progress_callback callback);
precn_t cas_ecm_factor_progress(const precn_t &value,
    cas_factor_progress_callback callback, unsigned curves = 64,
    uint32_t stage1_bound = 10000, uint32_t stage2_bound = 50000);
precn_t cas_siqs_factor_progress(const precn_t &value,
    cas_factor_progress_callback callback, size_t polynomials = 96,
    size_t interval = 384);

#endif
