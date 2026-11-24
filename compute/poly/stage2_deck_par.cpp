// Stage 2 (parallelized): Enumerate Deck(p) for even-n candidates p(x) = (x+5)^(n-d) f(x)
#include "bigint.hpp"
#include "poly_exact.hpp"
#include <array>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <fstream>
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

static Poly poly_mul(const Poly& A, const Poly& B) {
    if (A.is_zero() || B.is_zero()) return Poly{};
    std::vector<BigInt> c(A.deg() + B.deg() + 1, BigInt(0));
    for (int i = 0; i <= A.deg(); ++i)
        for (int j = 0; j <= B.deg(); ++j)
            c[i + j] = c[i + j] + A.c[i] * B.c[j];
    return Poly(std::move(c));
}

static Poly poly_pow(Poly base, int e) {
    Poly res({BigInt(1)});
    while (e > 0) {
        if (e & 1) res = poly_mul(res, base);
        base = poly_mul(base, base);
        e >>= 1;
    }
    return res;
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

static std::set<std::array<uint8_t, 8>> build_P_odd_7(int n_sub) {
    std::mt19937_64 rng(99887766ULL + n_sub);
    std::set<std::array<uint8_t, 8>> P_set;
    std::vector<uint8_t> M(n_sub * n_sub);
    for (int it = 0; it < 150000; ++it) {
        for (int i = 0; i < n_sub; ++i) M[i * n_sub + i] = 1;
        for (int j = 1; j < n_sub; ++j) M[j] = M[j * n_sub] = 1;
        for (int i = 1; i < n_sub; ++i) {
            for (int j = i + 1; j < n_sub; ++j) {
                uint8_t val = (rng() & 1) ? 1 : 127;
                M[i * n_sub + j] = M[j * n_sub + i] = val;
            }
        }
        P_set.insert(charpoly_top8_mod128(n_sub, M));
        if (P_set.size() == 2048) break;
    }
    return P_set;
}

int main(int argc, char** argv) {
    if (argc < 6) {
        std::cerr << "Usage: " << argv[0] << " <d> <n> <c_shift> <in_json> <out_deck_json> [threads]\n";
        return 1;
    }
    int d = std::stoi(argv[1]);
    int n = std::stoi(argv[2]);
    int c_shift = std::stoi(argv[3]);
    std::string in_json = argv[4];
    std::string out_json = argv[5];
    int threads = (argc >= 7) ? std::stoi(argv[6]) : 10;

    if (n % 2 != 0) {
        std::cerr << "Only even n supported in this Deck enumerator.\n";
        return 1;
    }

    int n_sub = n - 1;
    auto P_sub_set = build_P_odd_7(n_sub);
    std::cout << "|P_{" << n_sub << ",7}| = " << P_sub_set.size() << "\n";
    if (P_sub_set.size() != 2048) return 1;

    std::ifstream ifs(in_json);
    std::string content((std::istreambuf_iterator<char>(ifs)), std::istreambuf_iterator<char>());
    auto pos = content.find("\"polys\":");
    std::vector<std::vector<int64_t>> cand_polys;
    size_t cur = pos;
    while (true) {
        auto lb = content.find('[', cur);
        if (lb == std::string::npos) break;
        if (lb == content.find('[', pos)) { cur = lb + 1; continue; }
        auto rb = content.find(']', lb);
        if (rb == std::string::npos) break;
        std::string row = content.substr(lb + 1, rb - lb - 1);
        cur = rb + 1;
        std::vector<int64_t> b;
        std::stringstream ss(row);
        std::string tok;
        while (std::getline(ss, tok, ',')) b.push_back(std::stoll(tok));
        if (static_cast<int>(b.size()) == d + 1) cand_polys.push_back(std::move(b));
    }
    std::cout << "Loaded " << cand_polys.size() << " candidates from " << in_json << "\n";

    auto C_tbl = binom_table(n + 2);
    int w0 = (-5 - c_shift) / 2;
    int s_shift = (c_shift + 1) / 2;
    Poly w_minus_w0({BigInt(-w0), BigInt(1)});
    Poly factor_w0 = poly_pow(w_minus_w0, n - d);

    struct CandResult {
        int s = 0;
        std::vector<int64_t> b;
        std::vector<std::string> Hw_asc;
        std::vector<std::vector<std::string>> deck;
    };
    std::vector<CandResult> results(cand_polys.size());
    std::atomic<size_t> next_idx{0};
    std::atomic<size_t> done_cnt{0};
    std::mutex io_mtx;
    auto t0 = std::chrono::steady_clock::now();

    auto worker = [&]() {
        while (true) {
            size_t idx = next_idx.fetch_add(1);
            if (idx >= cand_polys.size()) break;
            const auto& b_in = cand_polys[idx];
            std::vector<BigInt> pw_c(d + 1);
            for (int j = 0; j <= d; ++j) pw_c[d - j] = BigInt(b_in[j]);
            Poly Pw(std::move(pw_c));
            Poly Full_w = poly_mul(factor_w0, Pw);
            Poly Dw = Poly::gcd(Full_w, Full_w.derivative());
            if (Dw.lead().sign < 0) Dw = -Dw;
            Poly Hw = Poly::exact_div(Full_w, Dw);
            if (Hw.lead().sign < 0) Hw = -Hw;

            int s = Hw.deg();
            int deg_psi = s - 1;
            int64_t M = 16;
            while (true) {
                SturmChain sc_H = SturmChain::build(Hw);
                if (sc_H.roots_in_half_open(BigInt(-M), BigInt(M), 0) == s) break;
                M *= 2;
            }
            std::vector<DyadicRoot> H_roots = isolate_all_real_roots(Hw, M, 28);

            BigInt h1 = (s - 1 >= 0) ? Hw.c[s - 1] : BigInt(0);
            BigInt h2 = (s - 2 >= 0) ? Hw.c[s - 2] : BigInt(0);
            BigInt sum_wr2 = h1 * h1 - BigInt(2) * h2;
            BigInt b0(2);
            BigInt b1 = BigInt(2) * h1 - BigInt(c_shift);
            BigInt four_sum_mu2 = BigInt(4) * sum_wr2 - BigInt(static_cast<int64_t>(c_shift) * c_shift) - BigInt(2 * (n - 1));
            BigInt b2 = (b1 * b1 - four_sum_mu2) / BigInt(4);

            int degD = Dw.deg();
            std::vector<int> Dw_shifted_mod2(degD + 1, 0);
            for (int j = 0; j <= degD; ++j) {
                if (Dw.c[j].is_even()) continue;
                if ((s_shift & 1) == 0) Dw_shifted_mod2[j] ^= 1;
                else {
                    for (int r = 0; r <= j; ++r)
                        if ((j & r) == r) Dw_shifted_mod2[r] ^= 1;
                }
            }

            auto mul_poly8 = [](const std::array<uint8_t, 8>& A, const std::array<uint8_t, 8>& B) {
                std::array<uint8_t, 8> R{};
                for (int i = 0; i < 8; ++i) {
                    uint32_t acc = 0;
                    for (int j = 0; j <= i; ++j) acc += static_cast<uint32_t>(A[j]) * B[i - j];
                    R[i] = static_cast<uint8_t>(acc & 127);
                }
                return R;
            };
            auto pow_linear8 = [&](int64_t alpha, int e) {
                std::array<uint8_t, 8> res{}, base{};
                res[0] = 1; base[0] = 1;
                base[1] = static_cast<uint8_t>((alpha % 128 + 128) % 128);
                while (e > 0) {
                    if (e & 1) res = mul_poly8(res, base);
                    base = mul_poly8(base, base);
                    e >>= 1;
                }
                return res;
            };
            std::array<uint8_t, 8> D_rev{};
            for (int j = 0; j < 8 && j <= degD; ++j) {
                int64_t mod_c = std::stoll((Dw.c[degD - j] % BigInt(128)).to_string());
                mod_c = ((mod_c % 128 + 128) % 128) * ((1LL << j) % 128) % 128;
                auto term = pow_linear8(-2 * s_shift, degD - j);
                for (int k = 0; k + j < 8; ++k)
                    D_rev[j + k] = static_cast<uint8_t>((D_rev[j + k] + mod_c * term[k]) & 127);
            }

            // Also compute exact required parity for b_psi[k] at step k!
            // In Dw(t - s_shift) * Psi(t - s_shift) mod 2:
            // Wait: top coeff of Dw(t - s_shift) is 1 * t^degD.
            // Psi(t - s_shift) = sum_{j=1}^{deg_psi} b_psi[j] * (t - s_shift)^(deg_psi - j) (mod 2).
            // Top coeff of prod is t^(degD + deg_psi - 1) = t^(n - 2) (even since n is even!).
            // So coeff of t^(n - 1 - k) for k EVEN (k=2, 4, ...) MUST be 0 mod 2!
            // That coeff is sum_{a=0..degD} Dw_shifted_mod2[degD - a] * [t^(deg_psi - (k - a))] Psi(t - s_shift).
            // For a=0: Dw_shifted_mod2[degD] = 1, and [t^(deg_psi - k)] Psi(t - s_shift) = b_psi[k] + sum_{j=1}^{k-1} ...
            auto req_psi_parity = [&](int k, const std::vector<BigInt>& bp) -> int {
                // Coeff of t^(degD + deg_psi - k) in Dw(t-s) * Psi(t-s) mod 2 must be 0 when k is even!
                // Note: for a = 0..min(k, degD), we need coeff of t^(deg_psi - (k - a)) in Psi(t - s) mod 2.
                int par = 0;
                for (int a = 0; a <= std::min(k, degD); ++a) {
                    if (!Dw_shifted_mod2[degD - a]) continue;
                    int target_deg = deg_psi - (k - a); // = deg_psi - m where m = k - a
                    int m = k - a;
                    for (int j = 1; j <= m; ++j) {
                        if (a == 0 && j == k) continue; // this is b_psi[k] itself!
                        if (bp[j].is_even()) continue;
                        if ((s_shift & 1) == 0) {
                            if (j == m) par ^= 1;
                        } else {
                            // C(deg_psi - j, deg_psi - m) = C(deg_psi - j, m - j) mod 2
                            int top = deg_psi - j;
                            int bot = m - j;
                            if ((top & bot) == bot) par ^= 1;
                        }
                    }
                }
                return par;
            };

            std::vector<std::vector<BigInt>> valid_psis;
            auto check_leaf = [&](const std::vector<BigInt>& b_psi) -> bool {
                std::vector<BigInt> pc(deg_psi + 1);
                for (int j = 0; j <= deg_psi; ++j) pc[deg_psi - j] = b_psi[j];
                Poly Psi(std::move(pc));

                for (int r = 0; r < s; ++r) {
                    BigInt r_lo, r_hi;
                    uint32_t r_shift = 0;
                    eval_interval_dyadic(Psi, H_roots[r].lo, H_roots[r].hi, H_roots[r].shift, r_lo, r_hi, r_shift);
                    int want_sign = ((s - 1 - r) % 2 == 0) ? +1 : -1;
                    if (want_sign > 0 && r_hi.sign < 0) return false;
                    if (want_sign < 0 && r_lo.sign > 0) return false;
                    if ((want_sign > 0 && r_lo.sign < 0 && r_hi.sign >= 0) ||
                        (want_sign < 0 && r_lo.sign <= 0 && r_hi.sign > 0)) {
                        Poly G = Poly::gcd(Hw, Psi);
                        SturmChain sc_G = SturmChain::build(G);
                        if (sc_G.roots_in_half_open(H_roots[r].lo, H_roots[r].hi, H_roots[r].shift) > 0) continue;
                        DyadicRoot cur_rt = H_roots[r];
                        int s_hi_H = Hw.eval_dyadic_sign(cur_rt.hi, cur_rt.shift);
                        while (true) {
                            BigInt lo2 = cur_rt.lo << 1;
                            BigInt hi2 = cur_rt.hi << 1;
                            BigInt mid = cur_rt.lo + cur_rt.hi;
                            uint32_t s2 = cur_rt.shift + 1;
                            int s_mid_H = Hw.eval_dyadic_sign(mid, s2);
                            if (s_mid_H == 0) {
                                cur_rt.lo = cur_rt.hi = mid; cur_rt.shift = s2;
                            } else if (s_mid_H == s_hi_H) {
                                cur_rt.lo = lo2; cur_rt.hi = mid; s_hi_H = s_mid_H; cur_rt.shift = s2;
                            } else {
                                cur_rt.lo = mid; cur_rt.hi = hi2; cur_rt.shift = s2;
                            }
                            eval_interval_dyadic(Psi, cur_rt.lo, cur_rt.hi, cur_rt.shift, r_lo, r_hi, r_shift);
                            if (r_lo.sign > 0 || r_hi.sign < 0 || cur_rt.lo == cur_rt.hi) break;
                        }
                        if (want_sign > 0 && r_hi.sign < 0) return false;
                        if (want_sign < 0 && r_lo.sign > 0) return false;
                    }
                }

                // Mod-2 odd-power check
                std::vector<int> Psi_shifted_mod2(deg_psi + 1, 0);
                for (int j = 0; j <= deg_psi; ++j) {
                    if (Psi.c[j].is_even()) continue;
                    if ((s_shift & 1) == 0) Psi_shifted_mod2[j] ^= 1;
                    else {
                        for (int r = 0; r <= j; ++r)
                            if ((j & r) == r) Psi_shifted_mod2[r] ^= 1;
                    }
                }
                std::vector<int> prod_mod2(degD + deg_psi + 1, 0);
                for (int i = 0; i <= degD; ++i) {
                    if (!Dw_shifted_mod2[i]) continue;
                    for (int j = 0; j <= deg_psi; ++j)
                        if (Psi_shifted_mod2[j]) prod_mod2[i + j] ^= 1;
                }
                for (size_t p = 1; p < prod_mod2.size(); p += 2)
                    if (prod_mod2[p]) return false;

                // P_{n-1, 7}
                std::array<uint8_t, 8> Psi_rev{};
                for (int j = 0; j < 8 && j <= deg_psi; ++j) {
                    int64_t mod_c = std::stoll((b_psi[j] % BigInt(128)).to_string());
                    int64_t cj = (j == 0) ? 1 : ((mod_c % 128 + 128) % 128) * ((1LL << (j - 1)) % 128);
                    cj %= 128;
                    auto term = pow_linear8(-2 * s_shift, deg_psi - j);
                    for (int k = 0; k + j < 8; ++k)
                        Psi_rev[j + k] = static_cast<uint8_t>((Psi_rev[j + k] + cj * term[k]) & 127);
                }
                auto full_sig = mul_poly8(D_rev, Psi_rev);
                return P_sub_set.count(full_sig) > 0;
            };

            auto dfs = [&](auto& self, int k, const std::vector<BigInt>& b_psi) -> void {
                if (k > deg_psi) {
                    if (check_leaf(b_psi)) valid_psis.push_back(b_psi);
                    return;
                }
                auto build_Fk = [&](int kk, const std::vector<BigInt>& bp) {
                    std::vector<BigInt> cs(kk + 1, BigInt(0));
                    for (int j = 0; j < kk; ++j) cs[kk - j] = C_tbl[deg_psi - j][kk - j] * bp[j];
                    return Poly(std::move(cs));
                };
                Poly F_prev = build_Fk(k - 1, b_psi);
                F_prev.c[0] = b_psi[k - 1];
                F_prev.trim();
                std::vector<DyadicRoot> roots = isolate_all_real_roots(F_prev, M, 14);
                Poly Fk_base = build_Fk(k, b_psi);

                bool has_lo = false, has_hi = false;
                BigInt lo(0), hi(0);
                bool has_ilo = false, has_ihi = false;
                BigInt ilo(0), ihi(0);
                bool all_simple = true;
                int pos_r = k - 1;
                for (size_t ri = roots.size(); ri-- > 0;) {
                    const auto& rt = roots[ri];
                    if (rt.multiplicity > 1) all_simple = false;
                    BigInt r_lo, r_hi;
                    uint32_t r_shift = 0;
                    eval_interval_dyadic(Fk_base, rt.lo, rt.hi, rt.shift, r_lo, r_hi, r_shift);
                    BigInt clb = ceil_div_pow2(-r_hi, r_shift);
                    BigInt cub = floor_div_pow2(-r_lo, r_shift);
                    BigInt cslb = floor_div_pow2(-r_lo, r_shift) + BigInt(1);
                    BigInt csub = ceil_div_pow2(-r_hi, r_shift) - BigInt(1);
                    bool need_ub = false, need_lb = false;
                    for (int p = pos_r; p > pos_r - rt.multiplicity; --p) {
                        if (((k - 1 - p) & 1) == 0) need_ub = true;
                        else need_lb = true;
                    }
                    if (need_ub) {
                        if (!has_hi || cub < hi) { hi = cub; has_hi = true; }
                        if (!has_ihi || csub < ihi) { ihi = csub; has_ihi = true; }
                    }
                    if (need_lb) {
                        if (!has_lo || clb > lo) { lo = clb; has_lo = true; }
                        if (!has_ilo || cslb > ilo) { ilo = cslb; has_ilo = true; }
                    }
                    pos_r -= rt.multiplicity;
                }
                if (!has_lo || !has_hi || lo > hi) return;

                int req_p = (k % 2 == 0) ? req_psi_parity(k, b_psi) : -1;
                Poly Fk = Fk_base;
                Fk.c.resize(k + 1, BigInt(0));
                for (BigInt bk = lo; bk <= hi; bk = bk + BigInt(1)) {
                    if (req_p != -1 && ((bk.is_even() ? 0 : 1) != req_p)) continue;
                    bool ok = false;
                    if (all_simple && has_ilo && has_ihi && bk >= ilo && bk <= ihi) ok = true;
                    else {
                        Fk.c[0] = bk;
                        ok = SturmChain::build(Fk).all_roots_real();
                    }
                    if (ok) {
                        auto nb = b_psi;
                        nb.push_back(bk);
                        self(self, k + 1, nb);
                    }
                }
            };

            std::vector<BigInt> init_b = {b0, b1, b2};
            if (deg_psi <= 2) {
                if (deg_psi == 2) {
                    Poly F2({b2, b1, b0});
                    if (SturmChain::build(F2).all_roots_real() && check_leaf(init_b)) valid_psis.push_back(init_b);
                }
            } else {
                Poly F2 = [&]() {
                    std::vector<BigInt> cs(3, BigInt(0));
                    for (int j = 0; j < 2; ++j) cs[2 - j] = C_tbl[deg_psi - j][2 - j] * init_b[j];
                    cs[0] = b2;
                    return Poly(std::move(cs));
                }();
                if (SturmChain::build(F2).all_roots_real()) dfs(dfs, 3, init_b);
            }

            CandResult res;
            res.s = s;
            res.b = b_in;
            for (int j = 0; j <= Hw.deg(); ++j) res.Hw_asc.push_back(Hw.c[j].to_string());
            for (const auto& vp : valid_psis) {
                std::vector<std::string> row;
                for (const auto& x : vp) row.push_back(x.to_string());
                res.deck.push_back(std::move(row));
            }
            results[idx] = std::move(res);
            size_t dc = done_cnt.fetch_add(1) + 1;
            if (dc % 25 == 0 || dc == cand_polys.size()) {
                std::lock_guard<std::mutex> lk(io_mtx);
                double dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
                std::cout << "  Done " << dc << "/" << cand_polys.size() << " (" << dt << "s)\n" << std::flush;
            }
        }
    };

    std::vector<std::thread> pool;
    for (int t = 0; t < threads; ++t) pool.emplace_back(worker);
    for (auto& th : pool) th.join();

    std::ofstream ofs(out_json);
    ofs << "{\n  \"d\": " << d << ", \"n\": " << n << ", \"c\": " << c_shift
        << ", \"candidates\": [\n";
    for (size_t idx = 0; idx < results.size(); ++idx) {
        const auto& r = results[idx];
        ofs << "    {\"index\": " << idx << ", \"s\": " << r.s << ", \"deck_size\": " << r.deck.size()
            << ", \"b\": [";
        for (size_t j = 0; j < r.b.size(); ++j) ofs << r.b[j] << (j + 1 < r.b.size() ? ", " : "");
        ofs << "], \"Hw_asc\": [";
        for (size_t j = 0; j < r.Hw_asc.size(); ++j) ofs << r.Hw_asc[j] << (j + 1 < r.Hw_asc.size() ? ", " : "");
        ofs << "], \"deck\": [\n";
        for (size_t di = 0; di < r.deck.size(); ++di) {
            ofs << "      [";
            for (size_t j = 0; j < r.deck[di].size(); ++j)
                ofs << r.deck[di][j] << (j + 1 < r.deck[di].size() ? ", " : "");
            ofs << "]" << (di + 1 < r.deck.size() ? "," : "") << "\n";
        }
        ofs << "    ]}" << (idx + 1 < results.size() ? "," : "") << "\n";
    }
    ofs << "  ]\n}\n";
    return 0;
}
