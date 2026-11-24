// Fast exact-integer polynomial enumerator v2:
// - Zero floats (exact BigInt Sturm + exact dyadic interval isolation)
// - Parallelizes early (split_k = 4) across all cores
// - Optional P_{n, e} mod 2^e pruning at k = 3..7 for odd n (certified by hitting proved 2^(C(e-2,2)+1) bound)
// - Optional max_k for tree-size benchmarking
#include "bigint.hpp"
#include "poly_exact.hpp"
#include <array>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <mutex>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <thread>
#include <vector>

static std::vector<std::vector<BigInt>> binom_table(int max_n) {
    std::vector<std::vector<BigInt>> C(max_n + 1, std::vector<BigInt>(max_n + 1, BigInt(0)));
    for (int i = 0; i <= max_n; ++i) {
        C[i][0] = BigInt(1);
        for (int j = 1; j <= i; ++j) C[i][j] = C[i - 1][j - 1] + C[i - 1][j];
    }
    return C;
}

static std::array<uint8_t, 8> charpoly_top8_mod128(int n, const std::vector<uint8_t>& M) {
    std::array<uint8_t, 8> p{};
    p[0] = 1;
    for (int k = 0; k < n; ++k) {
        uint8_t a = M[k * n + k];
        std::array<uint8_t, 8> v{};
        v[0] = 1;
        v[1] = static_cast<uint8_t>((128 - a) & 127);
        if (k > 0) {
            std::vector<uint8_t> vec(k);
            for (int i = 0; i < k; ++i) vec[i] = M[i * n + k];
            for (int j = 2; j < 8; ++j) {
                uint32_t dot = 0;
                for (int i = 0; i < k; ++i) dot += static_cast<uint32_t>(M[k * n + i]) * vec[i];
                v[j] = static_cast<uint8_t>((128 - (dot & 127)) & 127);
                if (j + 1 < 8) {
                    std::vector<uint8_t> next_vec(k, 0);
                    for (int r = 0; r < k; ++r) {
                        uint32_t s = 0;
                        for (int c = 0; c < k; ++c) s += static_cast<uint32_t>(M[r * n + c]) * vec[c];
                        next_vec[r] = static_cast<uint8_t>(s & 127);
                    }
                    vec = std::move(next_vec);
                }
            }
        }
        std::array<uint8_t, 8> np{};
        for (int i = 0; i < 8; ++i) {
            uint32_t s = 0;
            for (int j = 0; j <= i; ++j) s += static_cast<uint32_t>(v[j]) * p[i - j];
            np[i] = static_cast<uint8_t>(s & 127);
        }
        p = np;
    }
    return p;
}

struct Mod2Filter {
    bool enabled = false;
    int d = 0, n = 0, c = 0;
    bool n_even = false;
    // Exact sets of allowed top (e+1) coeffs mod 2^e for e = 3, 4, 5, 6, 7!
    // Stored as 64-bit packed keys (up to 8 bytes!)
    std::set<uint64_t> P_sets[8]; // indices 3..7
    std::array<uint8_t, 8> factor4{};
    std::vector<std::array<uint8_t, 8>> pow_2s; // pow_2s[e] = (1 - 2s*t)^e mod (t^8, 128)

    static uint64_t pack_mod(const std::array<uint8_t, 8>& sig, int e) {
        uint8_t mask = static_cast<uint8_t>((1 << e) - 1);
        uint64_t key = 0;
        for (int i = 0; i <= e; ++i) {
            key |= static_cast<uint64_t>(sig[i] & mask) << (8 * i);
        }
        return key;
    }

    void init(int d_, int n_, int c_) {
        d = d_; n = n_; c = c_;
        n_even = (n % 2 == 0);
        enabled = true;
        int s = (c + 1) / 2;
        auto mul8 = [](const std::array<uint8_t, 8>& A, const std::array<uint8_t, 8>& B) {
            std::array<uint8_t, 8> R{};
            for (int i = 0; i < 8; ++i) {
                uint32_t acc = 0;
                for (int j = 0; j <= i; ++j) acc += static_cast<uint32_t>(A[j]) * B[i - j];
                R[i] = static_cast<uint8_t>(acc & 127);
            }
            return R;
        };
        auto pow8 = [&](int64_t alpha, int e) {
            std::array<uint8_t, 8> res{}, base{};
            res[0] = 1; base[0] = 1;
            base[1] = static_cast<uint8_t>((alpha % 128 + 128) % 128);
            while (e > 0) {
                if (e & 1) res = mul8(res, base);
                base = mul8(base, base);
                e >>= 1;
            }
            return res;
        };
        factor4 = pow8(4, n - d);
        pow_2s.resize(d + 1);
        for (int e = 0; e <= d; ++e) pow_2s[e] = pow8(-2 * s, e);

        size_t target7 = n_even ? 1024 : 2048;
        std::mt19937_64 rng(777777ULL + n);
        std::set<std::array<uint8_t, 8>> P7;
        std::vector<uint8_t> M(n * n);
        for (int it = 0; it < 150000; ++it) {
            for (int i = 0; i < n; ++i) M[i * n + i] = 1;
            for (int j = 1; j < n; ++j) M[j] = M[j * n] = 1;
            for (int i = 1; i < n; ++i) {
                for (int j = i + 1; j < n; ++j) {
                    uint8_t val = (rng() & 1) ? 1 : 127;
                    M[i * n + j] = M[j * n + i] = val;
                }
            }
            P7.insert(charpoly_top8_mod128(n, M));
            if (P7.size() == target7) break;
        }
        if (P7.size() != target7) {
            std::cerr << "Error: P_{" << n << ",7} only reached " << P7.size() << " != " << target7 << "\n";
            enabled = false;
            return;
        }
        for (const auto& sig : P7) {
            for (int e = 3; e <= 7; ++e) {
                P_sets[e].insert(pack_mod(sig, e));
            }
        }
        std::cout << "Mod2Filter certified for n=" << n << ": |P_3..7| = ";
        for (int e = 3; e <= 7; ++e) std::cout << P_sets[e].size() << (e < 7 ? "," : "\n");
    }

    // Check partial b[0..k] at depth k:
    // For odd n: b[0..e] uniquely determines charpoly(S+I) mod 2^e (since j >= e+1 has 2^(j-1) == 0 mod 2^e)!
    // For even n: b[0..e-1] uniquely determines charpoly(S+I) mod 2^e!
    bool check_prefix(int k, const std::vector<BigInt>& b) const {
        if (!enabled) return true;
        int e = n_even ? (k + 1) : k;
        if (e < 3 || e > 7) return true;
        int max_j = n_even ? (e - 1) : e;
        uint8_t mask = static_cast<uint8_t>((1 << e) - 1);
        std::array<uint8_t, 8> f_rev{};
        for (int j = 0; j <= max_j && j < static_cast<int>(b.size()); ++j) {
            int64_t bj_mod = 0;
            {
                BigInt r = b[j] % BigInt(128);
                if (!r.is_zero()) bj_mod = std::stoll(r.to_string());
                bj_mod = (bj_mod % 128 + 128) % 128;
            }
            int64_t cj = n_even ? (bj_mod * ((1LL << j) & 127))
                                : (j == 0 ? 1 : (bj_mod * ((1LL << (j - 1)) & 127)));
            cj &= 127;
            const auto& term = pow_2s[d - j];
            for (int m = 0; m + j <= e; ++m) {
                f_rev[j + m] = static_cast<uint8_t>((f_rev[j + m] + cj * term[m]) & mask);
            }
        }
        std::array<uint8_t, 8> full_sig{};
        for (int i = 0; i <= e; ++i) {
            uint32_t acc = 0;
            for (int j = 0; j <= i; ++j) acc += static_cast<uint32_t>(factor4[j]) * f_rev[i - j];
            full_sig[i] = static_cast<uint8_t>(acc & mask);
        }
        return P_sets[e].count(pack_mod(full_sig, e)) > 0;
    }
};

struct TaskConfig {
    int d, n, c, d_eff;
    int max_k;
    int64_t M;
    bool n_even;
    BigInt b0, b1, b2;
    std::vector<std::vector<BigInt>> C;
    Mod2Filter mod_filter;
};

static int required_bk_parity(const TaskConfig& cfg, int k, const std::vector<BigInt>& b) {
    int s = (cfg.c + 1) / 2;
    if ((s & 1) == 0) return 0;
    int par = 0;
    for (int j = 1; j < k; ++j) {
        if (!b[j].is_even()) {
            int top = cfg.d - j;
            int bot = k - j;
            if ((top & bot) == bot) par ^= 1;
        }
    }
    return par;
}

static Poly build_Fk_base(const TaskConfig& cfg, int k, const std::vector<BigInt>& b) {
    std::vector<BigInt> coeffs(k + 1, BigInt(0));
    for (int j = 0; j < k; ++j) coeffs[k - j] = cfg.C[cfg.d_eff - j][k - j] * b[j];
    return Poly(std::move(coeffs));
}

static void expand_one_level(
    const TaskConfig& cfg,
    int k,
    const std::vector<BigInt>& b,
    std::vector<std::vector<BigInt>>& out_children,
    std::atomic<uint64_t>& sturm_calls
) {
    Poly F_prev = build_Fk_base(cfg, k - 1, b);
    F_prev.c[0] = b[k - 1];
    F_prev.trim();

    std::vector<DyadicRoot> roots = isolate_all_real_roots(F_prev, cfg.M, 14);
    Poly Fk_base = build_Fk_base(cfg, k, b);

    bool has_lo = false, has_hi = false;
    BigInt lo(0), hi(0);
    bool has_ilo = false, has_ihi = false;
    BigInt ilo(0), ihi(0);
    bool all_simple = true;

    int pos = k - 1;
    for (size_t idx = roots.size(); idx-- > 0;) {
        const auto& rt = roots[idx];
        if (rt.multiplicity > 1) all_simple = false;
        BigInt r_lo, r_hi;
        uint32_t r_shift = 0;
        eval_interval_dyadic(Fk_base, rt.lo, rt.hi, rt.shift, r_lo, r_hi, r_shift);
        BigInt cur_lb = ceil_div_pow2(-r_hi, r_shift);
        BigInt cur_ub = floor_div_pow2(-r_lo, r_shift);
        BigInt cur_slb = floor_div_pow2(-r_lo, r_shift) + BigInt(1);
        BigInt cur_sub = ceil_div_pow2(-r_hi, r_shift) - BigInt(1);

        bool need_ub = false, need_lb = false;
        for (int p = pos; p > pos - rt.multiplicity; --p) {
            if (((k - 1 - p) & 1) == 0) need_ub = true;
            else need_lb = true;
        }
        if (need_ub) {
            if (!has_hi || cur_ub < hi) { hi = cur_ub; has_hi = true; }
            if (!has_ihi || cur_sub < ihi) { ihi = cur_sub; has_ihi = true; }
        }
        if (need_lb) {
            if (!has_lo || cur_lb > lo) { lo = cur_lb; has_lo = true; }
            if (!has_ilo || cur_slb > ilo) { ilo = cur_slb; has_ilo = true; }
        }
        pos -= rt.multiplicity;
    }

    if (!has_lo || !has_hi || lo > hi) return;

    int req_par = (!cfg.n_even && (k % 2 == 0)) ? required_bk_parity(cfg, k, b) : -1;

    Poly Fk = Fk_base;
    Fk.c.resize(k + 1, BigInt(0));
    std::vector<BigInt> nb = b;
    nb.push_back(BigInt(0));
    for (BigInt bk = lo; bk <= hi; bk = bk + BigInt(1)) {
        if (req_par != -1 && ((bk.is_even() ? 0 : 1) != req_par)) continue;
        nb.back() = bk;
        if (!cfg.mod_filter.check_prefix(k, nb)) continue;

        bool ok = false;
        if (all_simple && has_ilo && has_ihi && bk >= ilo && bk <= ihi) {
            ok = true;
        } else {
            Fk.c[0] = bk;
            sturm_calls.fetch_add(1, std::memory_order_relaxed);
            ok = SturmChain::build(Fk).all_roots_real();
        }
        if (ok) out_children.push_back(nb);
    }
}

static bool verify_leaf(const TaskConfig& cfg, const std::vector<BigInt>& b_eff) {
    std::vector<BigInt> b = b_eff;
    b.resize(cfg.d + 1, BigInt(0));
    if (!cfg.n_even) {
        for (int k = cfg.d_eff + 1; k <= cfg.d; ++k) {
            if (k % 2 == 0 && required_bk_parity(cfg, k, b) != 0) return false;
        }
    }
    int64_t w_min_int = (-5 - cfg.c) / 2;
    std::vector<BigInt> r_coeffs(cfg.d_eff + 1);
    for (int j = 0; j <= cfg.d_eff; ++j) r_coeffs[cfg.d_eff - j] = b[j];
    Poly R(std::move(r_coeffs));
    SturmChain sc = SturmChain::build(R);
    if (!sc.all_roots_real()) return false;
    int roots_le = sc.var_at_neg_inf() - sc.var_at_dyadic(BigInt(w_min_int), 0);
    int on_boundary = (R.eval_dyadic_sign(BigInt(w_min_int), 0) == 0) ? 1 : 0;
    return (roots_le - on_boundary) == 0;
}

static void dfs_worker(
    const TaskConfig& cfg,
    int k,
    const std::vector<BigInt>& b,
    std::vector<std::vector<BigInt>>& results,
    std::atomic<uint64_t>& node_count,
    std::atomic<uint64_t>& sturm_calls
) {
    node_count.fetch_add(1, std::memory_order_relaxed);
    if (k > cfg.max_k) {
        if (cfg.max_k == cfg.d_eff) {
            if (verify_leaf(cfg, b)) results.push_back(b);
        } else {
            results.push_back(b);
        }
        return;
    }
    std::vector<std::vector<BigInt>> children;
    expand_one_level(cfg, k, b, children, sturm_calls);
    for (auto& ch : children) dfs_worker(cfg, k + 1, ch, results, node_count, sturm_calls);
}

int main(int argc, char** argv) {
    if (argc < 3) {
        std::cerr << "Usage: " << argv[0] << " <d> <n> [c_odd] [threads] [out_file] [use_mod128=1] [max_k=-1]\n";
        return 1;
    }
    int d = std::stoi(argv[1]);
    int n = std::stoi(argv[2]);
    int c = 0;
    if (argc >= 4 && std::stoi(argv[3]) > 0) {
        c = std::stoi(argv[3]);
    } else {
        int64_t sum_lam = 5LL * (n - d);
        int64_t sum_lam2 = static_cast<int64_t>(n) * (n - 1) - 25LL * (n - d);
        int64_t best_s2 = -1;
        for (int cc = 1; cc <= 35; cc += 2) {
            int64_t s2 = sum_lam2 - 2LL * cc * sum_lam + static_cast<int64_t>(d) * cc * cc;
            if (best_s2 < 0 || s2 < best_s2) { best_s2 = s2; c = cc; }
        }
    }
    int threads = (argc >= 5) ? std::stoi(argv[4]) : 10;
    std::string out_file = (argc >= 6) ? argv[5] : "";
    bool use_mod128 = (argc >= 7) ? (std::stoi(argv[6]) != 0) : true;
    int max_k_arg = (argc >= 8) ? std::stoi(argv[7]) : -1;

    auto t0 = std::chrono::steady_clock::now();
    TaskConfig cfg;
    cfg.d = d; cfg.n = n; cfg.c = c;
    cfg.n_even = (n % 2 == 0);
    cfg.C = binom_table(d + 2);

    int64_t sum_lam = 5LL * (n - d);
    int64_t sum_lam2 = static_cast<int64_t>(n) * (n - 1) - 25LL * (n - d);
    int64_t S1 = sum_lam - static_cast<int64_t>(d) * c;
    int64_t S2 = sum_lam2 - 2LL * c * sum_lam + static_cast<int64_t>(d) * c * c;

    if (cfg.n_even) {
        int64_t sum_w = S1 / 2, sum_w2 = S2 / 4;
        cfg.b0 = BigInt(1);
        cfg.b1 = BigInt(-sum_w);
        cfg.b2 = BigInt((sum_w * sum_w - sum_w2) / 2);
        cfg.d_eff = static_cast<int>(std::min<int64_t>(d, sum_w2));
        int64_t r = 0; while (r * r <= sum_w2) ++r;
        cfg.M = r + 2;
    } else {
        cfg.b0 = BigInt(2);
        cfg.b1 = BigInt(-S1);
        cfg.b2 = BigInt((S1 * S1 - S2) / 4);
        int r_max = 0;
        for (int r = 1; r <= d; ++r) {
            BigInt lhs(1), rhs(1), bS2(S2), bR(r);
            for (int i = 0; i < r; ++i) { lhs = lhs * bS2; rhs = rhs * bR; }
            for (int i = 0; i < r - 1; ++i) rhs = rhs * BigInt(4);
            if (lhs >= rhs) r_max = r;
        }
        cfg.d_eff = r_max;
        int64_t r = 0; while (4 * r * r <= S2) ++r;
        cfg.M = r + 2;
    }
    cfg.max_k = (max_k_arg > 0 && max_k_arg < cfg.d_eff) ? max_k_arg : cfg.d_eff;

    if (use_mod128) cfg.mod_filter.init(d, n, c);

    std::cout << "Config (d=" << d << ", n=" << n << "), c=" << c
              << ", n_even=" << cfg.n_even << ", d_eff=" << cfg.d_eff
              << ", max_k=" << cfg.max_k << ", M=" << cfg.M << "\n";

    std::vector<BigInt> root_b = {cfg.b0, cfg.b1, cfg.b2};
    int split_k = std::min(cfg.max_k, 4);
    std::vector<std::vector<BigInt>> frontier = {root_b};
    std::atomic<uint64_t> sturm_calls{0};
    for (int k = 3; k <= split_k; ++k) {
        std::vector<std::vector<BigInt>> next_f;
        for (const auto& node : frontier) expand_one_level(cfg, k, node, next_f, sturm_calls);
        frontier = std::move(next_f);
        double dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
        std::cout << "  k=" << std::setw(2) << k << ": " << frontier.size() << " nodes (" << dt << "s)\n";
        if (frontier.empty()) break;
    }

    std::vector<std::vector<BigInt>> final_polys;
    std::atomic<uint64_t> node_count{0};
    if (!frontier.empty()) {
        if (split_k == cfg.max_k) {
            for (const auto& node : frontier) {
                if (cfg.max_k < cfg.d_eff || verify_leaf(cfg, node)) final_polys.push_back(node);
            }
        } else {
            std::atomic<size_t> next_idx{0};
            std::mutex res_mtx;
            std::vector<std::thread> pool;
            int actual_threads = std::min<int>(threads, static_cast<int>(frontier.size()));
            for (int t = 0; t < actual_threads; ++t) {
                pool.emplace_back([&]() {
                    std::vector<std::vector<BigInt>> local_res;
                    while (true) {
                        size_t i = next_idx.fetch_add(1, std::memory_order_relaxed);
                        if (i >= frontier.size()) break;
                        dfs_worker(cfg, split_k + 1, frontier[i], local_res, node_count, sturm_calls);
                    }
                    std::lock_guard<std::mutex> lk(res_mtx);
                    final_polys.insert(final_polys.end(), local_res.begin(), local_res.end());
                });
            }
            for (auto& th : pool) th.join();
        }
    }

    double elapsed = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    std::cout << "DONE in " << std::fixed << std::setprecision(4) << elapsed << "s"
              << " | DFS nodes=" << node_count.load()
              << " | Sturm calls=" << sturm_calls.load()
              << " | Surviving=" << final_polys.size() << "\n";

    if (!out_file.empty() && cfg.max_k == cfg.d_eff) {
        std::ofstream ofs(out_file);
        ofs << "{\n  \"d\": " << d << ", \"n\": " << n << ", \"c\": " << c
            << ", \"n_even\": " << (cfg.n_even ? "true" : "false")
            << ", \"d_eff\": " << cfg.d_eff << ", \"mod128_pruned\": " << (use_mod128 ? "true" : "false")
            << ", \"elapsed_s\": " << elapsed << ", \"count\": " << final_polys.size() << ",\n  \"polys\": [\n";
        for (size_t i = 0; i < final_polys.size(); ++i) {
            auto full = final_polys[i];
            full.resize(d + 1, BigInt(0));
            ofs << "    [";
            for (size_t j = 0; j < full.size(); ++j)
                ofs << full[j].to_string() << (j + 1 < full.size() ? ", " : "");
            ofs << "]" << (i + 1 < final_polys.size() ? "," : "") << "\n";
        }
        ofs << "  ]\n}\n";
    }
    return 0;
}
