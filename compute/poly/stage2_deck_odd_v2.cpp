// Stage 2 (odd n -> even n-1): Enumerate monic Deck(p) for odd-n candidates
// Uses exact Dyadic Sturm + exact Bareiss Hankel PSD + exact interlacing + P_{n-1, 7} mod 128.
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

static bool is_matrix_psd_exact(std::vector<std::vector<BigInt>>& M) {
    int m = static_cast<int>(M.size());
    BigInt prev_piv(1);
    for (int r = 0; r < m; ++r) {
        int piv_idx = -1;
        for (int i = r; i < m; ++i) {
            if (M[i][i].sign < 0) return false;
            if (piv_idx == -1 && M[i][i].sign > 0) piv_idx = i;
        }
        if (piv_idx == -1) {
            for (int i = r; i < m; ++i)
                for (int j = i + 1; j < m; ++j)
                    if (!M[i][j].is_zero()) return false;
            return true;
        }
        if (piv_idx != r) {
            std::swap(M[r], M[piv_idx]);
            for (int i = 0; i < m; ++i) std::swap(M[i][r], M[i][piv_idx]);
        }
        const BigInt& piv = M[r][r];
        for (int i = r + 1; i < m; ++i) {
            for (int j = i; j < m; ++j) {
                BigInt val = (piv * M[i][j] - M[i][r] * M[j][r]) / prev_piv;
                M[i][j] = val;
                M[j][i] = val;
            }
        }
        prev_piv = piv;
    }
    return true;
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

static std::set<std::array<uint8_t, 8>> build_P_even_7(int n_sub) {
    std::mt19937_64 rng(55443322ULL + n_sub);
    std::set<std::array<uint8_t, 8>> P_set;
    std::vector<uint8_t> M(n_sub * n_sub);
    for (int it = 0; it < 100000; ++it) {
        for (int i = 0; i < n_sub; ++i) M[i * n_sub + i] = 1;
        for (int j = 1; j < n_sub; ++j) M[j] = M[j * n_sub] = 1;
        for (int i = 1; i < n_sub; ++i)
            for (int j = i + 1; j < n_sub; ++j)
                M[i * n_sub + j] = M[j * n_sub + i] = (rng() & 1) ? 1 : 127;
        P_set.insert(charpoly_top8_mod128(n_sub, M));
        if (P_set.size() == 1024) break;
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

    if (n % 2 == 0) {
        std::cerr << "Only odd n supported in stage2_deck_odd.\n";
        return 1;
    }

    int n_sub = n - 1;
    auto P_sub_set = build_P_even_7(n_sub);
    std::cout << "|P_{" << n_sub << ",7}| = " << P_sub_set.size() << "\n";
    if (P_sub_set.size() != 1024) return 1;

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
            // Note Dw is MONIC because LC(Full_w) = 2 (prime)!
            if (Dw.lead() != BigInt(1)) {
                std::cerr << "Unexpected non-monic Dw at idx " << idx << "\n";
                std::abort();
            }
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
            std::vector<DyadicRoot> H_roots = isolate_all_real_roots(Hw, M, 24);

            // Hw(w) = 2*w^s + h1*w^(s-1) + h2*w^(s-2) + ...
            BigInt h1 = (s - 1 >= 0) ? Hw.c[s - 1] : BigInt(0);
            BigInt h2 = (s - 2 >= 0) ? Hw.c[s - 2] : BigInt(0);
            BigInt four_sum_wr2 = h1 * h1 - BigInt(4) * h2;
            BigInt b0(1);
            BigInt b1 = (h1 - BigInt(c_shift)) / BigInt(2);
            BigInt four_sum_mu2 = four_sum_wr2 - BigInt(static_cast<int64_t>(c_shift) * c_shift) - BigInt(2 * (n - 1));
            BigInt sum_mu2 = four_sum_mu2 / BigInt(4);
            BigInt b2 = (b1 * b1 - sum_mu2) / BigInt(2);

            // Root bounds [A, B] for Psi(w) roots:
            // Since roots of Psi interlace roots of Hw, EVERY root of Psi lies in [w_min(Hw), w_max(Hw)]!
            // H_roots[0].lo / 2^shift <= mu_j <= H_roots.back().hi / 2^shift!
            // Choose integer A_int <= floor(H_roots[0]), B_int >= ceil(H_roots.back())!
            BigInt A_int = floor_div_pow2(H_roots[0].lo, H_roots[0].shift);
            BigInt B_int = ceil_div_pow2(H_roots.back().hi, H_roots.back().shift);

            // Note: even-order S_{-i} does NOT have odd-n mod-2 vanishing, and P_{n-1, 7} is already captured by monic Psi!
            // Wait: we STILL check P_{n-1, 7} just in case (and check if any non-real/interlacing issue).
            int degD = Dw.deg();
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

            auto check_hankel_psi = [&](int k, const std::vector<BigInt>& b_psi) -> bool {
                std::vector<BigInt> p(k + 1, BigInt(0));
                p[0] = BigInt(deg_psi);
                for (int m = 1; m <= k; ++m) {
                    BigInt sm = -BigInt(m) * b_psi[m];
                    for (int j = 1; j < m; ++j) sm = sm - b_psi[j] * p[m - j];
                    p[m] = sm;
                }
                int m1 = k / 2 + 1;
                std::vector<std::vector<BigInt>> H1(m1, std::vector<BigInt>(m1));
                for (int i = 0; i < m1; ++i)
                    for (int j = 0; j < m1; ++j) H1[i][j] = p[i + j];
                if (!is_matrix_psd_exact(H1)) return false;
                if (k >= 1) {
                    int m2 = (k - 1) / 2 + 1;
                    std::vector<std::vector<BigInt>> H2a(m2, std::vector<BigInt>(m2)), H2b(m2, std::vector<BigInt>(m2));
                    for (int i = 0; i < m2; ++i)
                        for (int j = 0; j < m2; ++j) {
                            H2a[i][j] = p[i + j + 1] - A_int * p[i + j];
                            H2b[i][j] = B_int * p[i + j] - p[i + j + 1];
                        }
                    if (!is_matrix_psd_exact(H2a) || !is_matrix_psd_exact(H2b)) return false;
                }
                if (k >= 2) {
                    int m3 = (k - 2) / 2 + 1;
                    BigInt AB = A_int * B_int, ApB = A_int + B_int;
                    std::vector<std::vector<BigInt>> H3(m3, std::vector<BigInt>(m3));
                    for (int i = 0; i < m3; ++i)
                        for (int j = 0; j < m3; ++j)
                            H3[i][j] = -p[i + j + 2] + ApB * p[i + j + 1] - AB * p[i + j];
                    if (!is_matrix_psd_exact(H3)) return false;
                }
                return true;
            };

            auto cmp_dyadic = [](const BigInt& a, uint32_t sa, const BigInt& b, uint32_t sb) -> int {
                if (sa == sb) return (a < b) ? -1 : ((a > b) ? 1 : 0);
                if (sa < sb) {
                    BigInt a2 = a << (sb - sa);
                    return (a2 < b) ? -1 : ((a2 > b) ? 1 : 0);
                } else {
                    BigInt b2 = b << (sa - sb);
                    return (a < b2) ? -1 : ((a > b2) ? 1 : 0);
                }
            };

            std::vector<std::vector<BigInt>> valid_psis;
            auto check_leaf = [&](const std::vector<BigInt>& b_psi) -> bool {
                std::array<uint8_t, 8> Psi_rev{};
                for (int j = 0; j < 8 && j <= deg_psi; ++j) {
                    int64_t mod_c = std::stoll((b_psi[j] % BigInt(128)).to_string());
                    int64_t cj = ((mod_c % 128 + 128) % 128) * ((1LL << j) % 128);
                    cj %= 128;
                    auto term = pow_linear8(-2 * s_shift, deg_psi - j);
                    for (int k = 0; k + j < 8; ++k)
                        Psi_rev[j + k] = static_cast<uint8_t>((Psi_rev[j + k] + cj * term[k]) & 127);
                }
                auto full_sig = mul_poly8(D_rev, Psi_rev);
                if (P_sub_set.count(full_sig) == 0) return false;

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
                return true;
            };

            auto dfs = [&](auto& self, int k, const std::vector<BigInt>& b_psi) -> void {
                if (k > deg_psi) {
                    if (check_leaf(b_psi)) valid_psis.push_back(b_psi);
                    return;
                }
                if (k == 8 && deg_psi >= 8) {
                    std::array<uint8_t, 8> Psi_rev{};
                    for (int j = 0; j < 8; ++j) {
                        int64_t mod_c = std::stoll((b_psi[j] % BigInt(128)).to_string());
                        int64_t cj = ((mod_c % 128 + 128) % 128) * ((1LL << j) % 128);
                        cj %= 128;
                        auto term = pow_linear8(-2 * s_shift, deg_psi - j);
                        for (int m = 0; m + j < 8; ++m)
                            Psi_rev[j + m] = static_cast<uint8_t>((Psi_rev[j + m] + cj * term[m]) & 127);
                    }
                    if (P_sub_set.count(mul_poly8(D_rev, Psi_rev)) == 0) return;
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

                // Exact Rolle-interlacing bounds from H_roots: alpha_j <= r_j(F_k) <= alpha_{j + s - k}
                std::vector<BigInt> z_lo, z_hi;
                std::vector<uint32_t> z_sh;
                bool z_disjoint = true;
                for (size_t ri = 0; ri < roots.size(); ++ri) {
                    if (ri > 0 && cmp_dyadic(roots[ri - 1].hi, roots[ri - 1].shift, roots[ri].lo, roots[ri].shift) >= 0)
                        z_disjoint = false;
                    for (int m = 0; m < roots[ri].multiplicity; ++m) {
                        z_lo.push_back(roots[ri].lo);
                        z_hi.push_back(roots[ri].hi);
                        z_sh.push_back(roots[ri].shift);
                    }
                }
                if (z_disjoint && static_cast<int>(z_lo.size()) == k - 1) {
                    for (int j = 0; j < k; ++j) {
                        // Lower bound r_j >= L_j
                        if (j < k - 1 && cmp_dyadic(H_roots[j].lo, H_roots[j].shift, z_hi[j], z_sh[j]) > 0)
                            return;
                        if (j == 0 || cmp_dyadic(H_roots[j].lo, H_roots[j].shift, z_hi[j - 1], z_sh[j - 1]) > 0) {
                            BigInt v_lo, v_hi;
                            uint32_t v_sh = 0;
                            eval_interval_dyadic(Fk_base, H_roots[j].lo, H_roots[j].lo, H_roots[j].shift, v_lo, v_hi, v_sh);
                            if (((k - j) & 1) == 0) {
                                BigInt lb = ceil_div_pow2(-v_hi, v_sh);
                                if (lb > lo) lo = lb;
                            } else {
                                BigInt ub = floor_div_pow2(-v_lo, v_sh);
                                if (ub < hi) hi = ub;
                            }
                            if (lo > hi) return;
                        }
                        // Upper bound r_j <= U_{j + s - k}
                        int uidx = j + s - k;
                        if (j > 0 && cmp_dyadic(H_roots[uidx].hi, H_roots[uidx].shift, z_lo[j - 1], z_sh[j - 1]) < 0)
                            return;
                        if (j == k - 1 || cmp_dyadic(H_roots[uidx].hi, H_roots[uidx].shift, z_lo[j], z_sh[j]) < 0) {
                            BigInt v_lo, v_hi;
                            uint32_t v_sh = 0;
                            eval_interval_dyadic(Fk_base, H_roots[uidx].hi, H_roots[uidx].hi, H_roots[uidx].shift, v_lo, v_hi, v_sh);
                            if (((k - j - 1) & 1) == 0) {
                                BigInt lb = ceil_div_pow2(-v_hi, v_sh);
                                if (lb > lo) lo = lb;
                            } else {
                                BigInt ub = floor_div_pow2(-v_lo, v_sh);
                                if (ub < hi) hi = ub;
                            }
                            if (lo > hi) return;
                        }
                    }
                }
                if (k == deg_psi) {
                    for (int r = 0; r < s; ++r) {
                        BigInt r_lo, r_hi;
                        uint32_t r_shift = 0;
                        eval_interval_dyadic(Fk_base, H_roots[r].lo, H_roots[r].hi, H_roots[r].shift, r_lo, r_hi, r_shift);
                        if (((s - 1 - r) & 1) == 0) {
                            BigInt lb = ceil_div_pow2(-r_hi, r_shift);
                            if (lb > lo) lo = lb;
                        } else {
                            BigInt ub = floor_div_pow2(-r_lo, r_shift);
                            if (ub < hi) hi = ub;
                        }
                        if (lo > hi) return;
                    }
                }

                Poly Fk = Fk_base;
                Fk.c.resize(k + 1, BigInt(0));
                std::vector<BigInt> nb = b_psi;
                nb.push_back(BigInt(0));
                for (BigInt bk = lo; bk <= hi; bk = bk + BigInt(1)) {
                    nb.back() = bk;
                    if (!check_hankel_psi(k, nb)) continue;
                    bool ok = false;
                    if (all_simple && has_ilo && has_ihi && bk >= ilo && bk <= ihi) ok = true;
                    else {
                        Fk.c[0] = bk;
                        ok = SturmChain::build(Fk).all_roots_real();
                    }
                    if (ok) self(self, k + 1, nb);
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
                if (SturmChain::build(F2).all_roots_real() && check_hankel_psi(2, init_b)) dfs(dfs, 3, init_b);
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
            if (dc % 100 == 0 || dc == cand_polys.size()) {
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
