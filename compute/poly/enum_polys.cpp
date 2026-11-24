#include "bigint.hpp"
#include "poly_exact.hpp"
#include <atomic>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <mutex>
#include <sstream>
#include <string>
#include <thread>
#include <vector>

static std::vector<std::vector<BigInt>> binom_table(int max_n) {
    std::vector<std::vector<BigInt>> C(max_n + 1, std::vector<BigInt>(max_n + 1, BigInt(0)));
    for (int i = 0; i <= max_n; ++i) {
        C[i][0] = BigInt(1);
        for (int j = 1; j <= i; ++j) {
            C[i][j] = C[i - 1][j - 1] + C[i - 1][j];
        }
    }
    return C;
}

struct TaskConfig {
    int d;
    int n;
    int c;          // odd shift: lambda = 2*w + c
    int d_eff;      // effective degree after factoring w^(d - d_eff)
    int64_t M;      // strict root bound: all roots in (-M, M)
    bool n_even;
    BigInt b0, b1, b2;
    std::vector<std::vector<BigInt>> C;
};

static int required_bk_parity(const TaskConfig& cfg, int k, const std::vector<BigInt>& b) {
    // Only for n odd and k even:
    // b_k === sum_{j=1}^{k-1} b_j * C(d - j, k - j) * s^(k - j) (mod 2)
    // where s = (c + 1) / 2.
    int s = (cfg.c + 1) / 2;
    if ((s & 1) == 0) return 0; // s even => all terms j < k have s^(k-j) even!
    int par = 0;
    for (int j = 1; j < k; ++j) {
        if (!b[j].is_even()) {
            // Check C(d - j, k - j) mod 2 via Lucas: ((d-j) & (k-j)) == (k-j)
            int top = cfg.d - j;
            int bot = k - j;
            if ((top & bot) == bot) {
                par ^= 1;
            }
        }
    }
    return par;
}

static Poly build_Fk_base(const TaskConfig& cfg, int k, const std::vector<BigInt>& b) {
    // F_k(w) = sum_{j=0}^{k-1} C(d_eff - j, k - j) * b[j] * w^(k - j)
    std::vector<BigInt> coeffs(k + 1, BigInt(0));
    for (int j = 0; j < k; ++j) {
        coeffs[k - j] = cfg.C[cfg.d_eff - j][k - j] * b[j];
    }
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

    std::vector<DyadicRoot> roots = isolate_all_real_roots(F_prev, cfg.M, 16);
    Poly Fk_base = build_Fk_base(cfg, k, b);

    bool has_lo = false, has_hi = false;
    BigInt lo(0), hi(0);
    bool has_inner_lo = false, has_inner_hi = false;
    BigInt inner_lo(0), inner_hi(0);
    bool all_simple = true;

    int pos = k - 1; // 1-indexed from left; k-1 is rightmost root (local min)
    for (size_t idx = roots.size(); idx-- > 0;) {
        const auto& rt = roots[idx];
        if (rt.multiplicity > 1) all_simple = false;
        BigInt r_lo, r_hi;
        uint32_t r_shift = 0;
        eval_interval_dyadic(Fk_base, rt.lo, rt.hi, rt.shift, r_lo, r_hi, r_shift);
        // -Fk_base(xi) in [-r_hi, -r_lo] / 2^r_shift
        BigInt cur_lb = ceil_div_pow2(-r_hi, r_shift);
        BigInt cur_ub = floor_div_pow2(-r_lo, r_shift);
        // Strict interior bounds guaranteeing F_k(xi) < 0 at min and > 0 at max:
        BigInt cur_strict_lb = floor_div_pow2(-r_lo, r_shift) + BigInt(1);
        BigInt cur_strict_ub = ceil_div_pow2(-r_hi, r_shift) - BigInt(1);

        // Occupies positions pos, pos-1, ..., pos - rt.multiplicity + 1
        bool need_ub = false, need_lb = false;
        for (int p = pos; p > pos - rt.multiplicity; --p) {
            if (((k - 1 - p) & 1) == 0) need_ub = true;
            else need_lb = true;
        }
        if (need_ub) {
            if (!has_hi || cur_ub < hi) { hi = cur_ub; has_hi = true; }
            if (!has_inner_hi || cur_strict_ub < inner_hi) { inner_hi = cur_strict_ub; has_inner_hi = true; }
        }
        if (need_lb) {
            if (!has_lo || cur_lb > lo) { lo = cur_lb; has_lo = true; }
            if (!has_inner_lo || cur_strict_lb > inner_lo) { inner_lo = cur_strict_lb; has_inner_lo = true; }
        }
        pos -= rt.multiplicity;
    }

    if (!has_lo || !has_hi || lo > hi) return;

    int req_par = (!cfg.n_even && (k % 2 == 0)) ? required_bk_parity(cfg, k, b) : -1;

    Poly Fk = Fk_base;
    Fk.c.resize(k + 1, BigInt(0));
    for (BigInt bk = lo; bk <= hi; bk = bk + BigInt(1)) {
        if (req_par != -1) {
            int p = bk.is_even() ? 0 : 1;
            if (p != req_par) continue;
        }
        if (all_simple && has_inner_lo && has_inner_hi && bk >= inner_lo && bk <= inner_hi) {
            auto nb = b;
            nb.push_back(bk);
            out_children.push_back(std::move(nb));
            continue;
        }
        Fk.c[0] = bk;
        // Note Fk has c[k] = C(d_eff, k)*b0 > 0, so lead never trims
        sturm_calls.fetch_add(1, std::memory_order_relaxed);
        SturmChain sc = SturmChain::build(Fk);
        if (sc.all_roots_real()) {
            auto nb = b;
            nb.push_back(bk);
            out_children.push_back(std::move(nb));
        }
    }
}

// Verify root lower bound w >= (-5 - c)/2 and full 2-adic congruence on original degree d
static bool verify_leaf(const TaskConfig& cfg, const std::vector<BigInt>& b_eff) {
    // Pad with zeros up to degree d
    std::vector<BigInt> b = b_eff;
    b.resize(cfg.d + 1, BigInt(0));

    // Check odd-n 2-adic congruence for k = d_eff + 1 .. d as well!
    if (!cfg.n_even) {
        for (int k = cfg.d_eff + 1; k <= cfg.d; ++k) {
            if (k % 2 == 0) {
                int req = required_bk_parity(cfg, k, b);
                if (req != 0) return false; // since b[k] == 0
            }
        }
    }

    // Check all roots of R(w) satisfy 2w + c >= -5  <=>  w >= (-5 - c)/2.
    // Note (-5 - c) is even because c is odd! So w_min_bound = (-5 - c) / 2 is an INTEGER!
    int64_t w_min_int = (-5 - cfg.c) / 2;
    std::vector<BigInt> r_coeffs(cfg.d_eff + 1);
    for (int j = 0; j <= cfg.d_eff; ++j) {
        r_coeffs[cfg.d_eff - j] = b[j];
    }
    Poly R(std::move(r_coeffs));
    SturmChain sc = SturmChain::build(R);
    if (!sc.all_roots_real()) return false;
    // Count distinct roots in (-inf, w_min_int) = var_at_neg_inf() - var_at(w_min_int - 0)?
    // Wait: SturmChain counts (-inf, a], so evaluate at w_min_int and check R(w_min_int)!
    // Specifically: if w_min_int is a root, that's >= w_min_int (valid! lambda = -5).
    // Roots strictly < w_min_int = var(-inf) - var(w_min_int) + (1 if R(w_min_int) == 0 ? 0? wait):
    // Wait: var(a) - var(b) counts distinct roots in (a, b].
    // So var(-inf) - var(w_min_int) counts distinct roots in (-inf, w_min_int]!
    // If R(w_min_int) == 0, then w_min_int is counted in (-inf, w_min_int] (which is allowed!).
    // Otherwise (R(w_min_int) != 0), (-inf, w_min_int] == (-inf, w_min_int), so count must be 0!
    int roots_le = sc.var_at_neg_inf() - sc.var_at_dyadic(BigInt(w_min_int), 0);
    int on_boundary = (R.eval_dyadic_sign(BigInt(w_min_int), 0) == 0) ? 1 : 0;
    if (roots_le - on_boundary != 0) return false;
    return true;
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
    if (k > cfg.d_eff) {
        if (verify_leaf(cfg, b)) {
            results.push_back(b);
        }
        return;
    }
    std::vector<std::vector<BigInt>> children;
    expand_one_level(cfg, k, b, children, sturm_calls);
    for (auto& ch : children) {
        dfs_worker(cfg, k + 1, ch, results, node_count, sturm_calls);
    }
}

int main(int argc, char** argv) {
    if (argc < 3) {
        std::cerr << "Usage: " << argv[0] << " <d> <n> [c_odd] [threads] [out_file]\n";
        return 1;
    }
    int d = std::stoi(argv[1]);
    int n = std::stoi(argv[2]);
    int c = 0;
    if (argc >= 4) {
        c = std::stoi(argv[3]);
    } else {
        // Pick optimal odd c minimizing sum (lambda - c)^2
        int64_t sum_lam = 5LL * (n - d);
        int64_t sum_lam2 = static_cast<int64_t>(n) * (n - 1) - 25LL * (n - d);
        int64_t best_s2 = -1;
        for (int cc = 1; cc <= 35; cc += 2) {
            int64_t s2 = sum_lam2 - 2LL * cc * sum_lam + static_cast<int64_t>(d) * cc * cc;
            if (best_s2 < 0 || s2 < best_s2) { best_s2 = s2; c = cc; }
        }
    }
    int threads = (argc >= 5) ? std::stoi(argv[4]) : 8;
    std::string out_file = (argc >= 6) ? argv[5] : "";

    auto t0 = std::chrono::steady_clock::now();

    TaskConfig cfg;
    cfg.d = d;
    cfg.n = n;
    cfg.c = c;
    cfg.n_even = (n % 2 == 0);
    cfg.C = binom_table(d + 2);

    int64_t sum_lam = 5LL * (n - d);
    int64_t sum_lam2 = static_cast<int64_t>(n) * (n - 1) - 25LL * (n - d);
    int64_t S1 = sum_lam - static_cast<int64_t>(d) * c;                 // 2 * sum w_i
    int64_t S2 = sum_lam2 - 2LL * c * sum_lam + static_cast<int64_t>(d) * c * c; // 4 * sum w_i^2

    if (cfg.n_even) {
        if (S1 % 2 != 0 || S2 % 4 != 0) {
            std::cerr << "Error: S1/S2 divisibility failed for even n!\n";
            return 1;
        }
        int64_t sum_w = S1 / 2;
        int64_t sum_w2 = S2 / 4;
        if ((sum_w * sum_w - sum_w2) % 2 != 0) {
            std::cerr << "Error: b2 not integer!\n";
            return 1;
        }
        cfg.b0 = BigInt(1);
        cfg.b1 = BigInt(-sum_w);
        cfg.b2 = BigInt((sum_w * sum_w - sum_w2) / 2);
        cfg.d_eff = static_cast<int>(std::min<int64_t>(d, sum_w2));
        int64_t r = 0;
        while (r * r <= sum_w2) ++r;
        cfg.M = r + 2;
    } else {
        if ((S1 * S1 - S2) % 4 != 0) {
            std::cerr << "Error: b2 not integer for odd n!\n";
            return 1;
        }
        cfg.b0 = BigInt(2);
        cfg.b1 = BigInt(-S1);
        cfg.b2 = BigInt((S1 * S1 - S2) / 4);
        // Find max r <= d such that S2^r >= 4^(r-1) * r^r
        int r_max = 0;
        for (int r = 1; r <= d; ++r) {
            BigInt lhs(1), rhs(1);
            BigInt bS2(S2), bR(r);
            for (int i = 0; i < r; ++i) {
                lhs = lhs * bS2;
                rhs = rhs * bR;
            }
            for (int i = 0; i < r - 1; ++i) rhs = rhs * BigInt(4);
            if (lhs >= rhs) r_max = r;
        }
        cfg.d_eff = r_max;
        int64_t r = 0;
        while (4 * r * r <= S2) ++r;
        cfg.M = r + 2;
    }

    std::cout << "Config (d=" << d << ", n=" << n << "), c=" << c
              << ", n_even=" << cfg.n_even << ", d_eff=" << cfg.d_eff
              << ", M=" << cfg.M << ", b0=" << cfg.b0.to_string()
              << ", b1=" << cfg.b1.to_string() << ", b2=" << cfg.b2.to_string() << "\n";

    std::vector<BigInt> root_b = {cfg.b0, cfg.b1, cfg.b2};
    // Verify F_2 has real roots
    {
        Poly F2 = build_Fk_base(cfg, 2, root_b);
        F2.c[0] = cfg.b2;
        F2.trim();
        if (!SturmChain::build(F2).all_roots_real()) {
            std::cout << "F_2 failed all_roots_real! 0 candidates.\n";
            return 0;
        }
    }

    // BFS up to depth split_k to get parallel work items
    int split_k = std::min(cfg.d_eff, 6);
    std::vector<std::vector<BigInt>> frontier = {root_b};
    std::atomic<uint64_t> sturm_calls{0};
    for (int k = 3; k <= split_k; ++k) {
        std::vector<std::vector<BigInt>> next_f;
        for (const auto& node : frontier) {
            expand_one_level(cfg, k, node, next_f, sturm_calls);
        }
        frontier = std::move(next_f);
        auto t_now = std::chrono::steady_clock::now();
        double dt = std::chrono::duration<double>(t_now - t0).count();
        std::cout << "  k=" << std::setw(2) << k << ": " << frontier.size()
                  << " nodes (" << std::fixed << std::setprecision(3) << dt << "s)\n";
        if (frontier.empty()) break;
    }

    std::vector<std::vector<BigInt>> final_polys;
    std::atomic<uint64_t> node_count{0};

    if (!frontier.empty()) {
        if (split_k == cfg.d_eff) {
            for (const auto& node : frontier) {
                if (verify_leaf(cfg, node)) final_polys.push_back(node);
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

    auto t1 = std::chrono::steady_clock::now();
    double elapsed = std::chrono::duration<double>(t1 - t0).count();
    std::cout << "DONE in " << std::fixed << std::setprecision(4) << elapsed << "s"
              << " | DFS nodes=" << node_count.load()
              << " | Sturm calls=" << sturm_calls.load()
              << " | Surviving=" << final_polys.size() << "\n";

    if (!out_file.empty()) {
        std::ofstream ofs(out_file);
        ofs << "{\n";
        ofs << "  \"d\": " << d << ", \"n\": " << n << ", \"c\": " << c
            << ", \"n_even\": " << (cfg.n_even ? "true" : "false")
            << ", \"d_eff\": " << cfg.d_eff
            << ", \"elapsed_s\": " << elapsed
            << ", \"dfs_nodes\": " << node_count.load()
            << ", \"sturm_calls\": " << sturm_calls.load()
            << ", \"count\": " << final_polys.size() << ",\n";
        ofs << "  \"polys\": [\n";
        for (size_t i = 0; i < final_polys.size(); ++i) {
            auto full = final_polys[i];
            full.resize(d + 1, BigInt(0));
            ofs << "    [";
            for (size_t j = 0; j < full.size(); ++j) {
                ofs << full[j].to_string() << (j + 1 < full.size() ? ", " : "");
            }
            ofs << "]" << (i + 1 < final_polys.size() ? "," : "") << "\n";
        }
        ofs << "  ]\n}\n";
    }
    return 0;
}
