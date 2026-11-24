// Stage 2: Enumerate Deck(p) for even-n candidates p(x) = (x+5)^(n-d) f(x)
// and output integer coefficient vectors of psi(x) (and/or f_i(x)) for Farkas LP check.
#include "bigint.hpp"
#include "poly_exact.hpp"
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <set>
#include <sstream>
#include <string>
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

// Compute top 8 coeffs of charpoly(S+I) mod 128 for odd n_sub = n - 1
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
        std::cerr << "Usage: " << argv[0] << " <d> <n> <c_shift> <in_json> <out_deck_json>\n";
        return 1;
    }
    int d = std::stoi(argv[1]);
    int n = std::stoi(argv[2]);
    int c_shift = std::stoi(argv[3]);
    std::string in_json = argv[4];
    std::string out_json = argv[5];

    if (n % 2 != 0) {
        std::cerr << "Only even n supported in this Deck enumerator.\n";
        return 1;
    }

    int n_sub = n - 1;
    auto P_sub_set = build_P_odd_7(n_sub);
    std::cout << "|P_{" << n_sub << ",7}| = " << P_sub_set.size() << "\n";
    if (P_sub_set.size() != 2048) {
        std::cerr << "Warning: P_{n-1,7} did not reach 2048!\n";
    }

    // Read input polys
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

    std::ofstream ofs(out_json);
    ofs << "{\n  \"d\": " << d << ", \"n\": " << n << ", \"c\": " << c_shift
        << ", \"candidates\": [\n";

    for (size_t idx = 0; idx < cand_polys.size(); ++idx) {
        const auto& b_in = cand_polys[idx];
        // P_w(w) = sum b_in[j] * w^(d-j)
        std::vector<BigInt> pw_c(d + 1);
        for (int j = 0; j <= d; ++j) pw_c[d - j] = BigInt(b_in[j]);
        Poly Pw(std::move(pw_c));
        Poly Full_w = poly_mul(factor_w0, Pw);
        Poly Dw = Poly::gcd(Full_w, Full_w.derivative());
        if (Dw.lead().sign < 0) Dw = -Dw;
        Poly Hw = Poly::exact_div(Full_w, Dw);
        if (Hw.lead().sign < 0) Hw = -Hw;

        int s = Hw.deg(); // distinct roots of Full_w
        int deg_psi = s - 1;
        // Isolate roots of Hw (all simple!) to high precision (target_bits = 28)
        int64_t M = 15;
        {
            // Strict Cauchy bound on Hw: 1 + max |c_i|
            // Actually w0 is around -8..-10, max w_i <= 6, so M = 15 is plenty, let's check dynamically!
            std::vector<DyadicRoot> check_r;
            while (true) {
                SturmChain sc_H = SturmChain::build(Hw);
                if (sc_H.roots_in_half_open(BigInt(-M), BigInt(M), 0) == s) break;
                M *= 2;
            }
        }
        std::vector<DyadicRoot> H_roots = isolate_all_real_roots(Hw, M, 28);
        if (static_cast<int>(H_roots.size()) != s) {
            std::cerr << "Error: Hw roots count mismatch!\n";
            return 1;
        }

        // Compute b1, b2 of Psi(w) = 2*w^(s-1) + b1*w^(s-2) + b2*w^(s-3) + ...
        // Hw(w) = w^s + h1*w^(s-1) + h2*w^(s-2) + ...
        BigInt h1 = (s - 1 >= 0) ? Hw.c[s - 1] : BigInt(0);
        BigInt h2 = (s - 2 >= 0) ? Hw.c[s - 2] : BigInt(0);
        BigInt sum_wr = -h1;
        BigInt sum_wr2 = h1 * h1 - BigInt(2) * h2;
        BigInt b0(2);
        BigInt b1 = BigInt(2) * h1 - BigInt(c_shift);
        // 4 * sum mu^2 = 4 * sum wr^2 - c^2 - 2*(n - 1)
        BigInt four_sum_mu2 = BigInt(4) * sum_wr2 - BigInt(static_cast<int64_t>(c_shift) * c_shift) - BigInt(2 * (n - 1));
        BigInt b2 = (b1 * b1 - four_sum_mu2) / BigInt(4);

        // Precompute Dw(t - s_shift) mod 2 for odd-n parity check:
        // Actually we need Full_sub(t) = Dw(t - s_shift) * Psi(t - s_shift) mod 2 to have ONLY even powers of t!
        // Compute Dw(t - s_shift) mod 2 as bitmask/vector of length deg(Dw)+1
        int degD = Dw.deg();
        std::vector<int> Dw_shifted_mod2(degD + 1, 0);
        for (int j = 0; j <= degD; ++j) {
            if (Dw.c[j].is_even()) continue;
            // (t - s_shift)^j mod 2
            if ((s_shift & 1) == 0) {
                Dw_shifted_mod2[j] ^= 1;
            } else {
                for (int r = 0; r <= j; ++r) {
                    if ((j & r) == r) Dw_shifted_mod2[r] ^= 1;
                }
            }
        }

        // Precompute Dw_rev(t) mod (t^8, 128) for P_{n-1, 7} check!
        // Wait: D(z - 1) = 2^degD * Dw((z - 2*s_shift)/2) = sum_{j=0}^degD Dw.c[degD-j] * 2^j * (z - 2*s_shift)^(degD - j)
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
            BigInt coeff_b = Dw.c[degD - j];
            int64_t mod_c = (coeff_b % BigInt(128)).to_string().empty() ? 0 : std::stoll((coeff_b % BigInt(128)).to_string());
            mod_c = ((mod_c % 128 + 128) % 128) * ((1LL << j) % 128) % 128;
            auto term = pow_linear8(-2 * s_shift, degD - j);
            for (int k = 0; k + j < 8; ++k) {
                D_rev[j + k] = static_cast<uint8_t>((D_rev[j + k] + mod_c * term[k]) & 127);
            }
        }

        // Enumerate Psi(w) via Rolle tree on degree deg_psi = s - 1
        std::vector<std::vector<BigInt>> valid_psis;
        auto check_leaf = [&](const std::vector<BigInt>& b_psi) -> bool {
            // 1. Build Psi(w)
            std::vector<BigInt> pc(deg_psi + 1);
            for (int j = 0; j <= deg_psi; ++j) pc[deg_psi - j] = b_psi[j];
            Poly Psi(std::move(pc));

            // 2. Check interlacing: (-1)^(s - 1 - r) * Psi(w_r) >= 0 for r = 0 .. s-1 (0-indexed!)
            // Wait: 1-indexed r=1..s: (-1)^(s - r) Psi(w_r) >= 0.
            // At rightmost root r=s (0-indexed s-1): (-1)^0 * Psi(w_{s-1}) >= 0 (since lead(Psi)>0 and Psi(w) -> +inf).
            for (int r = 0; r < s; ++r) {
                BigInt r_lo, r_hi;
                uint32_t r_shift = 0;
                eval_interval_dyadic(Psi, H_roots[r].lo, H_roots[r].hi, H_roots[r].shift, r_lo, r_hi, r_shift);
                int want_sign = ((s - 1 - r) % 2 == 0) ? +1 : -1;
                if (want_sign > 0) {
                    if (r_hi.sign < 0) return false; // strictly < 0
                } else {
                    if (r_lo.sign > 0) return false; // strictly > 0
                }
                // Check ambiguous interval straddling 0 (excluding exact root):
                if ((want_sign > 0 && r_lo.sign < 0 && r_hi.sign >= 0) ||
                    (want_sign < 0 && r_lo.sign <= 0 && r_hi.sign > 0)) {
                    // Check if gcd(Hw, Psi) or refine root!
                    // Actually Hw is irreducible? Not necessarily, Hw can have deg > 1 factor!
                    // Refine H_roots[r] using Sturm/sign on Hw until Psi doesn't straddle 0 OR gcd(Hw, Psi) shares that root!
                    Poly G = Poly::gcd(Hw, Psi);
                    SturmChain sc_G = SturmChain::build(G);
                    if (sc_G.roots_in_half_open(H_roots[r].lo, H_roots[r].hi, H_roots[r].shift) > 0) {
                        // Exact shared root => Psi(w_r) == 0, which satisfies >= 0 and <= 0!
                        continue;
                    }
                    // Otherwise Psi(w_r) != 0, so refine H_roots[r] until r_lo and r_hi have same sign!
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

            // 3. Check odd-n mod-2 parity: Dw(t - s_shift) * Psi(t - s_shift) mod 2 has only EVEN powers of t
            std::vector<int> Psi_shifted_mod2(deg_psi + 1, 0);
            for (int j = 0; j <= deg_psi; ++j) {
                if (Psi.c[j].is_even()) continue;
                if ((s_shift & 1) == 0) {
                    Psi_shifted_mod2[j] ^= 1;
                } else {
                    for (int r = 0; r <= j; ++r) {
                        if ((j & r) == r) Psi_shifted_mod2[r] ^= 1;
                    }
                }
            }
            std::vector<int> prod_mod2(degD + deg_psi + 1, 0);
            for (int i = 0; i <= degD; ++i) {
                if (!Dw_shifted_mod2[i]) continue;
                for (int j = 0; j <= deg_psi; ++j) {
                    if (Psi_shifted_mod2[j]) prod_mod2[i + j] ^= 1;
                }
            }
            for (size_t p = 1; p < prod_mod2.size(); p += 2) {
                if (prod_mod2[p]) return false;
            }

            // 4. Check P_{n-1, 7} mod 128!
            std::array<uint8_t, 8> Psi_rev{};
            for (int j = 0; j < 8 && j <= deg_psi; ++j) {
                int64_t mod_c = std::stoll((b_psi[j] % BigInt(128)).to_string());
                int64_t cj = (j == 0) ? 1 : ((mod_c % 128 + 128) % 128) * ((1LL << (j - 1)) % 128);
                cj %= 128;
                auto term = pow_linear8(-2 * s_shift, deg_psi - j);
                for (int k = 0; k + j < 8; ++k) {
                    Psi_rev[j + k] = static_cast<uint8_t>((Psi_rev[j + k] + cj * term[k]) & 127);
                }
            }
            auto full_sig = mul_poly8(D_rev, Psi_rev);
            if (!P_sub_set.count(full_sig)) return false;

            return true;
        };

        // Recursive Rolle DFS on deg_psi
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
            std::vector<DyadicRoot> roots = isolate_all_real_roots(F_prev, M, 16);
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

            Poly Fk = Fk_base;
            Fk.c.resize(k + 1, BigInt(0));
            for (BigInt bk = lo; bk <= hi; bk = bk + BigInt(1)) {
                bool ok = false;
                if (all_simple && has_ilo && has_ihi && bk >= ilo && bk <= ihi) {
                    ok = true;
                } else {
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
                if (SturmChain::build(F2).all_roots_real() && check_leaf(init_b)) {
                    valid_psis.push_back(init_b);
                }
            }
        } else {
            Poly F2 = [&]() {
                std::vector<BigInt> cs(3, BigInt(0));
                for (int j = 0; j < 2; ++j) cs[2 - j] = C_tbl[deg_psi - j][2 - j] * init_b[j];
                cs[0] = b2;
                return Poly(std::move(cs));
            }();
            if (SturmChain::build(F2).all_roots_real()) {
                dfs(dfs, 3, init_b);
            }
        }

        // Write candidate + Deck(p) to JSON
        ofs << "    {\"index\": " << idx << ", \"s\": " << s << ", \"deck_size\": " << valid_psis.size()
            << ", \"b\": [";
        for (size_t j = 0; j < b_in.size(); ++j) ofs << b_in[j] << (j + 1 < b_in.size() ? ", " : "");
        ofs << "], \"Hw_asc\": [";
        for (int j = 0; j <= Hw.deg(); ++j) ofs << Hw.c[j].to_string() << (j < Hw.deg() ? ", " : "");
        ofs << "], \"deck\": [\n";
        for (size_t di = 0; di < valid_psis.size(); ++di) {
            ofs << "      [";
            for (size_t j = 0; j < valid_psis[di].size(); ++j)
                ofs << valid_psis[di][j].to_string() << (j + 1 < valid_psis[di].size() ? ", " : "");
            ofs << "]" << (di + 1 < valid_psis.size() ? "," : "") << "\n";
        }
        ofs << "    ]}" << (idx + 1 < cand_polys.size() ? "," : "") << "\n";
        if ((idx + 1) % 20 == 0 || idx + 1 == cand_polys.size()) {
            std::cout << "  Candidate " << (idx + 1) << "/" << cand_polys.size()
                      << " (s=" << s << ", |Deck|=" << valid_psis.size() << ")\n";
        }
    }
    ofs << "  ]\n}\n";
    return 0;
}
