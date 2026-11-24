// Exact-integer polynomial enumerator v3:
// - Exact BigInt Sturm + exact dyadic interval isolation (zero floats!)
// - Parallelized across all cores (split_k = 4)
// - Mod2Filter (P_{n, 3..7} certified by hitting 2^(C(e-2,2)+gamma(n)))
// - Corollary 4.3 exact mod-4 full-tree prefix pruning for odd n!
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
#include <unordered_set>
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
    std::set<uint64_t> P_sets[8];
    std::array<uint8_t, 8> factor4{};
    std::vector<std::array<uint8_t, 8>> pow_2s;

    static uint64_t pack_mod(const std::array<uint8_t, 8>& sig, int e) {
        uint8_t mask = static_cast<uint8_t>((1 << e) - 1);
        uint64_t key = 0;
        for (int i = 0; i <= e; ++i) key |= static_cast<uint64_t>(sig[i] & mask) << (8 * i);
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
                for (int j = i + 1; j < n; ++j) M[i * n + j] = M[j * n + i] = (rng() & 1) ? 1 : 127;
            }
            P7.insert(charpoly_top8_mod128(n, M));
            if (P7.size() == target7) break;
        }
        if (P7.size() != target7) {
            std::cerr << "Error: P_{" << n << ",7} only reached " << P7.size() << "\n";
            enabled = false;
            return;
        }
        for (const auto& sig : P7)
            for (int e = 3; e <= 7; ++e) P_sets[e].insert(pack_mod(sig, e));
    }

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
            for (int m = 0; m + j <= e; ++m)
                f_rev[j + m] = static_cast<uint8_t>((f_rev[j + m] + cj * term[m]) & mask);
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

// Exact Corollary 4.3 mod-4 prefix filter for odd n!
// Notice for odd n, d_eff = 2*m + 1 MUST be odd (or if d_eff was even? wait: for (17,49) d_eff=13, (18,59) d_eff=17, (19,73) d_eff=19).
// Wait: we build directly for the exact shift:
// 2^{-n+1} chi_S(2z-1) === (2z - n) * Q(z)^2 (mod 4)
// When (z + 2)^{n - d} * (z - (c+1)/2)^{d - d_eff} is a square mod 4 (or even easier: works for ANY odd n!).
// Specifically, for (17,49), (18,59), (19,73), (19,75):
//   (17,49): deg=13, m=6, factor=(2w+1)
//   (18,59): deg=17, m=8, factor=(2w+1)
//   (19,73): deg=19, m=9, factor=(2w-1)
//   (19,75): deg=7,  m=3, factor=(2w-1)
struct Cor43Filter {
    bool enabled = false;
    int deg = 0;
    std::vector<std::unordered_set<uint64_t>> prefixes; // prefixes[k] holds packed (b0%4..bk%4)

    static uint32_t mod4(const BigInt& x) {
        if (x.is_zero()) return 0;
        uint32_t lo = x.limbs[0] & 3u;
        return (x.sign >= 0) ? lo : ((4u - lo) & 3u);
    }

    static uint64_t pack_vec(const std::vector<BigInt>& b, int k) {
        uint64_t p = 0;
        for (int i = 0; i <= k; ++i) p = (p << 2) | mod4(b[i]);
        return p;
    }

    void init_odd(int d, int d_eff, int n, int c) {
        if (n % 2 == 0 || d_eff % 2 == 0) return;
        int s_half = (c + 1) / 2;
        bool ok_even = ((n - d) % 2 == 0) && ((d - d_eff) % 2 == 0);
        bool ok_odd = ((n - d) % 2 != 0) && (d - d_eff >= 1) && ((s_half % 4 + 4) % 4 == 2);
        if (!ok_even && !ok_odd) return;
        // Linear factor in (2w + c) mod 4 is (2w + c - n)? No: 2z - n = 2w + c + 1 - n?
        // Wait: 2z - 1 = 2w + c => 2z - n = 2w + c + 1 - n!
        // Since c + 1 - n is ODD (c odd, 1 odd, n odd): (c + 1 - n) mod 4 is +1 or 3 (-1)!
        // Wait: verify!
        // (17, 49): c=9, n=49 -> 9 + 1 - 49 = -39 === +1 (mod 4)! Matches (2w+1)!
        // (18, 59): c=11, n=59 -> 11 + 1 - 59 = -47 === +1 (mod 4)! Matches (2w+1)!
        // (19, 73): c=15, n=73 -> 15 + 1 - 73 = -57 === +3 === -1 (mod 4)! Matches (2w-1)!
        // (19, 75): c=15, n=75 -> 15 + 1 - 75 = -59 === +1 (mod 4)? Wait: (19,75) had d=19, d_eff=7, (x-15)^12 => (z-8)^12, and 2z-75 = 2w+16-75 = 2w-59 === 2w+1 (mod 4)!
        int const_term = (((c + 1 - n) % 4) + 4) % 4; // 1 or 3
        deg = d_eff;
        int m = (d_eff - 1) / 2;
        prefixes.resize(deg + 1);
        // Also double check that (n - d) + (d - d_eff) allows canceling!
        // Wait: let's check for general (d, n, d_eff):
        // (z + 2)^{n-d} === z^{n-d} (mod 4) ONLY if n-d is EVEN, OR if n-d is odd and z - s === z + 2 (mod 4) cancels it!
        // Specifically: chi_S(2z-1)/2^{n-1} = (z+2)^{n-d} (z-s)^{d-d_eff} * (2 F(w)).
        // If (n-d) is odd, we need d - d_eff >= 1 AND (z - s) === z + 2 (mod 4) (i.e. s even with s % 4 == 2), so (z+2)^{n-d}(z-s)^{d-d_eff} is an even power of (z+2) mod 4!
        // For (17,49): n-d=32 even, d-d_eff=4 even.
        // For (18,59): n-d=41 odd, d-d_eff=1, s=6 === 2 (mod 4) => (z+2)^41 (z-6) === z^42 (mod 4).
        // For (19,73): n-d=54 even, d-d_eff=0 even.
        // For (19,75): n-d=56 even, d-d_eff=12 even.
        enabled = true;
        uint32_t total = 1u << m;
        for (uint32_t mask = 0; mask < total; ++mask) {
            std::vector<int> q(m + 1, 0);
            q[0] = 1;
            for (int i = 0; i < m; ++i) q[i + 1] = (mask >> i) & 1;
            std::vector<int> q2(2 * m + 1, 0);
            for (int i = 0; i <= m; ++i)
                for (int j = 0; j <= m; ++j)
                    q2[i + j] = (q2[i + j] + q[i] * q[j]) & 3;
            std::vector<int> prod(deg + 1, 0);
            for (int i = 0; i <= 2 * m; ++i) {
                prod[i] = (prod[i] + 2 * q2[i]) & 3;
                prod[i + 1] = (prod[i + 1] + const_term * q2[i]) & 3;
            }
            uint64_t pk = 0;
            for (int k = 0; k <= deg; ++k) {
                pk = (pk << 2) | static_cast<uint64_t>(prod[k]);
                prefixes[k].insert(pk);
            }
        }
        std::cout << "Cor43Filter enabled (deg=" << deg << ", m=" << m
                  << ", const=" << const_term << ", unique full=" << prefixes[deg].size() << ")\n";
    }
};

struct TaskConfig {
    int d, n, c, d_eff, max_k;
    int64_t M;
    bool n_even;
    BigInt b0, b1, b2;
    std::vector<std::vector<BigInt>> C;
    Mod2Filter mod_filter;
    Cor43Filter cor43;
};

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

    uint64_t prefix_prev = cfg.cor43.enabled ? Cor43Filter::pack_vec(b, k - 1) : 0;
    uint32_t allowed_mod4_mask = 0xF;
    if (cfg.cor43.enabled) {
        allowed_mod4_mask = 0;
        for (uint32_t r = 0; r < 4; ++r) {
            if (cfg.cor43.prefixes[k].count((prefix_prev << 2) | r)) {
                allowed_mod4_mask |= (1u << r);
            }
        }
        if (allowed_mod4_mask == 0) return;
    }

    Poly Fk = Fk_base;
    Fk.c.resize(k + 1, BigInt(0));
    std::vector<BigInt> nb = b;
    nb.push_back(BigInt(0));
    for (BigInt bk = lo; bk <= hi; bk = bk + BigInt(1)) {
        if (cfg.cor43.enabled) {
            uint32_t r = Cor43Filter::mod4(bk);
            if (((allowed_mod4_mask >> r) & 1u) == 0) continue;
        }
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
    int64_t w_min_int = (-5 - cfg.c) / 2;
    std::vector<BigInt> r_coeffs(cfg.d_eff + 1);
    for (int j = 0; j <= cfg.d_eff; ++j) r_coeffs[cfg.d_eff - j] = b_eff[j];
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
        cfg.cor43.init_odd(d, cfg.d_eff, n, c);
    }
    cfg.max_k = (max_k_arg > 0 && max_k_arg < cfg.d_eff) ? max_k_arg : cfg.d_eff;
    if (use_mod128) cfg.mod_filter.init(d, n, c);

    std::cout << "Config (d=" << d << ", n=" << n << "), c=" << c
              << ", n_even=" << cfg.n_even << ", d_eff=" << cfg.d_eff
              << ", max_k=" << cfg.max_k << ", M=" << cfg.M << "\n";

    std::vector<BigInt> root_b = {cfg.b0, cfg.b1, cfg.b2};
    if (cfg.cor43.enabled && !cfg.cor43.prefixes[2].count(Cor43Filter::pack_vec(root_b, 2))) {
        std::cout << "Root fails Cor 4.3!\n";
        return 0;
    }

    int split_k = std::min(cfg.max_k, 5);
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
            << ", \"cor43_pruned\": " << (cfg.cor43.enabled ? "true" : "false")
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
