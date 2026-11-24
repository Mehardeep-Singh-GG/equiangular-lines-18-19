#pragma once
#include "bigint.hpp"
#include <algorithm>
#include <stdexcept>
#include <utility>
#include <vector>

// Polynomial p(w) = sum_{i=0}^{deg} c[i] * w^i, c.back() != 0 unless p == 0 (c empty).
struct Poly {
    std::vector<BigInt> c;

    Poly() = default;
    explicit Poly(std::vector<BigInt> coeffs) : c(std::move(coeffs)) { trim(); }

    void trim() {
        while (!c.empty() && c.back().is_zero()) c.pop_back();
    }

    bool is_zero() const { return c.empty(); }
    int deg() const { return static_cast<int>(c.size()) - 1; }
    const BigInt& lead() const { return c.back(); }

    Poly operator-() const {
        Poly r = *this;
        for (auto& x : r.c) x = -x;
        return r;
    }

    Poly derivative() const {
        if (c.size() <= 1) return Poly{};
        std::vector<BigInt> d(c.size() - 1);
        for (size_t i = 1; i < c.size(); ++i) {
            d[i - 1] = c[i] * BigInt(static_cast<int64_t>(i));
        }
        return Poly(std::move(d));
    }

    // Divide all coeffs by positive GCD of coeffs (preserves signs!)
    Poly primitive_pos() const {
        if (is_zero()) return *this;
        BigInt g(0);
        for (const auto& x : c) {
            if (!x.is_zero()) {
                g = g.is_zero() ? x.abs() : BigInt::gcd(g, x);
                if (g == BigInt(1)) break;
            }
        }
        if (g.is_zero() || g == BigInt(1)) return *this;
        Poly r = *this;
        for (auto& x : r.c) x = x / g;
        return r;
    }

    // Positive-multiplier pseudo-remainder: M * A = Q * B + R with M > 0
    static Poly prem_pos(const Poly& A_in, const Poly& B) {
        if (B.is_zero()) throw std::runtime_error("poly div by zero");
        Poly A = A_in;
        int dB = B.deg();
        const BigInt& b = B.lead();
        BigInt abs_b = b.abs();
        int sgn_b = b.sign; // +1 or -1
        while (!A.is_zero() && A.deg() >= dB) {
            int dA = A.deg();
            int shift = dA - dB;
            BigInt a = A.lead();
            // A = abs_b * A - sgn_b * a * x^shift * B
            for (int i = 0; i < dA; ++i) {
                A.c[i] = A.c[i] * abs_b;
            }
            A.c[dA] = BigInt(0);
            BigInt factor = (sgn_b > 0) ? a : -a;
            for (int i = 0; i < dB; ++i) {
                A.c[i + shift] = A.c[i + shift] - factor * B.c[i];
            }
            A.trim();
        }
        return A;
    }

    // Exact polynomial division assuming B | A in Q[x], returning primitive_pos?
    // Actually for p / gcd(p, p'), in Z[x] if B is primitive, B | A in Z[x]!
    static Poly exact_div(Poly A, const Poly& B) {
        if (B.is_zero()) throw std::runtime_error("exact_div by zero");
        if (A.is_zero()) return Poly{};
        int dA = A.deg();
        int dB = B.deg();
        if (dA < dB) throw std::runtime_error("exact_div deg error");
        std::vector<BigInt> q(dA - dB + 1, BigInt(0));
        const BigInt& b = B.lead();
        for (int i = dA; i >= dB; --i) {
            if (static_cast<int>(A.c.size()) <= i || A.c[i].is_zero()) continue;
            BigInt quo, rem;
            BigInt::divmod(A.c[i], b, quo, rem);
            if (!rem.is_zero()) {
                throw std::runtime_error("exact_div non-zero remainder");
            }
            q[i - dB] = quo;
            for (int j = 0; j <= dB; ++j) {
                A.c[i - dB + j] = A.c[i - dB + j] - quo * B.c[j];
            }
        }
        A.trim();
        if (!A.is_zero()) throw std::runtime_error("exact_div leftover remainder");
        return Poly(std::move(q));
    }

    // Primitive GCD with positive leading coefficient
    static Poly gcd(Poly A, Poly B) {
        if (A.is_zero()) {
            if (B.is_zero()) return Poly{};
            B = B.primitive_pos();
            return B.lead().sign < 0 ? -B : B;
        }
        if (B.is_zero()) {
            A = A.primitive_pos();
            return A.lead().sign < 0 ? -A : A;
        }
        A = A.primitive_pos();
        B = B.primitive_pos();
        while (!B.is_zero()) {
            Poly R = prem_pos(A, B).primitive_pos();
            A = std::move(B);
            B = std::move(R);
        }
        return A.lead().sign < 0 ? -A : A;
    }

    // Evaluate sign of p(num / 2^shift)
    int eval_dyadic_sign(const BigInt& num, uint32_t shift) const {
        if (is_zero()) return 0;
        int d = deg();
        BigInt val = c[d];
        BigInt p2(1);
        for (int i = d - 1; i >= 0; --i) {
            p2 = p2 << shift;
            val = val * num + c[i] * p2;
        }
        return val.sign;
    }
};

struct SturmChain {
    std::vector<Poly> chain;
    int sqfree_deg = 0;

    static SturmChain build(const Poly& p) {
        SturmChain sc;
        if (p.is_zero() || p.deg() <= 0) return sc;
        Poly dp = p.derivative();
        Poly g = Poly::gcd(p, dp);
        Poly sq = Poly::exact_div(p, g).primitive_pos();
        if (sq.lead().sign < 0) sq = -sq;
        sc.sqfree_deg = sq.deg();
        if (sc.sqfree_deg == 0) return sc;

        sc.chain.push_back(sq);
        sc.chain.push_back(sq.derivative().primitive_pos());
        while (sc.chain.back().deg() > 0) {
            Poly r = Poly::prem_pos(sc.chain[sc.chain.size() - 2], sc.chain.back());
            if (r.is_zero()) break;
            sc.chain.push_back((-r).primitive_pos());
        }
        return sc;
    }

    static int count_variations(const std::vector<int>& signs) {
        int v = 0;
        int prev = 0;
        for (int s : signs) {
            if (s == 0) continue;
            if (prev != 0 && s != prev) ++v;
            prev = s;
        }
        return v;
    }

    int var_at_neg_inf() const {
        std::vector<int> signs;
        signs.reserve(chain.size());
        for (const auto& s : chain) {
            int lsig = s.lead().sign;
            if (s.deg() % 2 != 0) lsig = -lsig;
            signs.push_back(lsig);
        }
        return count_variations(signs);
    }

    int var_at_pos_inf() const {
        std::vector<int> signs;
        signs.reserve(chain.size());
        for (const auto& s : chain) {
            signs.push_back(s.lead().sign);
        }
        return count_variations(signs);
    }

    int var_at_dyadic(const BigInt& num, uint32_t shift) const {
        std::vector<int> signs;
        signs.reserve(chain.size());
        for (const auto& s : chain) {
            signs.push_back(s.eval_dyadic_sign(num, shift));
        }
        return count_variations(signs);
    }

    bool all_roots_real() const {
        if (sqfree_deg == 0) return true;
        return (var_at_neg_inf() - var_at_pos_inf()) == sqfree_deg;
    }

    // Number of distinct real roots in (a / 2^shift, b / 2^shift]
    int roots_in_half_open(const BigInt& a, const BigInt& b, uint32_t shift) const {
        return var_at_dyadic(a, shift) - var_at_dyadic(b, shift);
    }
};

// Exact dyadic interval [num_lo / 2^shift, num_hi / 2^shift]
struct DyadicRoot {
    BigInt lo, hi;
    uint32_t shift;
    int multiplicity;
};

// Isolate all real roots of p (assumed all roots real, in (-M, M]) to width <= 2^(-target_bits)
// Returns roots in strictly increasing order with exact multiplicities!
inline std::vector<DyadicRoot> isolate_all_real_roots(const Poly& p, int64_t M, uint32_t target_bits) {
    // First compute squarefree factorization multiplicities via gcd(p, p') iteratively (Yun-style simple loop)
    // Wait: simpler! Build SturmChain on sq = p / gcd(p, p'), isolate distinct roots of sq,
    // and determine multiplicity of each root interval by checking derivatives or squarefree factors!
    // Even simpler: compute squarefree decomposition p = prod_{m} f_m^m!
    // f_1 * f_2^2 * ... :
    struct SqFactor { Poly f; SturmChain sc; int mult; };
    std::vector<SqFactor> factors;
    {
        Poly cur = p.primitive_pos();
        if (cur.lead().sign < 0) cur = -cur;
        // Standard Yun / repeated gcd decomposition:
        // g_0 = cur; while deg(g) > 0: d = gcd(g, g'); sq = g / d; next = d;
        // Actually sq_i = g_{i-1}/g_i has all roots of mult >= i!
        // So exact multiplicity i roots are roots of (sq_i / sq_{i+1})!
        std::vector<Poly> sq_ge; // sq_ge[i-1] has simple roots at all roots of mult >= i
        Poly g = cur;
        while (g.deg() > 0) {
            Poly next_g = Poly::gcd(g, g.derivative());
            Poly sq_i = Poly::exact_div(g, next_g).primitive_pos();
            if (sq_i.lead().sign < 0) sq_i = -sq_i;
            sq_ge.push_back(std::move(sq_i));
            g = std::move(next_g);
        }
        for (size_t i = 0; i < sq_ge.size(); ++i) {
            Poly exact_m = (i + 1 < sq_ge.size())
                ? Poly::exact_div(sq_ge[i], sq_ge[i + 1]).primitive_pos()
                : sq_ge[i];
            if (exact_m.lead().sign < 0) exact_m = -exact_m;
            if (exact_m.deg() > 0) {
                SturmChain sc = SturmChain::build(exact_m);
                factors.push_back({std::move(exact_m), std::move(sc), static_cast<int>(i + 1)});
            }
        }
    }

    std::vector<DyadicRoot> all_roots;
    for (const auto& fac : factors) {
        // Isolate distinct roots of fac.f in (-M, M]
        struct Box { BigInt lo, hi; uint32_t shift; int count; };
        std::vector<Box> stack;
        stack.push_back({BigInt(-M), BigInt(M), 0, fac.sc.roots_in_half_open(BigInt(-M), BigInt(M), 0)});
        std::vector<DyadicRoot> fac_roots;
        while (!stack.empty()) {
            Box b = std::move(stack.back());
            stack.pop_back();
            if (b.count == 0) continue;
            if (b.count == 1) {
                // Refine by sign bisection (fast!) to target_bits
                int s_hi = fac.f.eval_dyadic_sign(b.hi, b.shift);
                if (s_hi == 0) {
                    // Exact root at b.hi!
                    if (b.shift < target_bits) {
                        BigInt pt = b.hi << (target_bits - b.shift);
                        fac_roots.push_back({pt, pt, target_bits, fac.mult});
                    } else {
                        fac_roots.push_back({b.hi, b.hi, b.shift, fac.mult});
                    }
                    continue;
                }
                while (b.shift < target_bits) {
                    BigInt lo2 = b.lo << 1;
                    BigInt hi2 = b.hi << 1;
                    BigInt mid = lo2 + b.hi - b.lo; // = b.lo + b.hi
                    uint32_t s2 = b.shift + 1;
                    int s_mid = fac.f.eval_dyadic_sign(mid, s2);
                    if (s_mid == 0) {
                        if (s2 < target_bits) {
                            BigInt pt = mid << (target_bits - s2);
                            b = {pt, pt, target_bits, fac.mult};
                        } else {
                            b = {mid, mid, s2, fac.mult};
                        }
                        break;
                    }
                    // Root is in (lo2, hi2], s_hi != 0, and fac.f is simple here so signs at lo2 and hi2 differ
                    // Check if s_mid == s_hi -> root is in (lo2, mid], else in (mid, hi2]
                    if (s_mid == s_hi) {
                        b.lo = lo2;
                        b.hi = mid;
                        s_hi = s_mid;
                    } else {
                        b.lo = mid;
                        b.hi = hi2;
                    }
                    b.shift = s2;
                }
                fac_roots.push_back({b.lo, b.hi, b.shift, fac.mult});
                continue;
            }
            // count >= 2: split using Sturm
            BigInt lo2 = b.lo << 1;
            BigInt hi2 = b.hi << 1;
            BigInt mid = lo2 + BigInt(1); // wait: (lo2 + hi2)/2! Careful: hi - lo might be > 1 at shift 0!
            // Wait: at shift 0, b.hi - b.lo = 2M, so lo2 + hi2 = 2*(lo + hi), wait:
            // mid in units of 2^{-(shift+1)} is (lo*2 + hi*2) / 2 = lo + hi!
            mid = b.lo + b.hi;
            uint32_t s2 = b.shift + 1;
            int v_lo = fac.sc.var_at_dyadic(lo2, s2);
            int v_mid = fac.sc.var_at_dyadic(mid, s2);
            int v_hi = fac.sc.var_at_dyadic(hi2, s2);
            int c_left = v_lo - v_mid;
            int c_right = v_mid - v_hi;
            if (c_right > 0) stack.push_back({mid, hi2, s2, c_right});
            if (c_left > 0) stack.push_back({lo2, mid, s2, c_left});
        }
        all_roots.insert(all_roots.end(), fac_roots.begin(), fac_roots.end());
    }

    std::sort(all_roots.begin(), all_roots.end(), [](const DyadicRoot& a, const DyadicRoot& b) {
        // Compare midpoints (or lo): since distinct roots are disjoint, comparing a.hi <= b.lo or midpoints works
        // Normalize to max shift
        uint32_t ms = std::max(a.shift, b.shift);
        BigInt alo = a.lo << (ms - a.shift);
        BigInt ahi = a.hi << (ms - a.shift);
        BigInt blo = b.lo << (ms - b.shift);
        BigInt bhi = b.hi << (ms - b.shift);
        return (alo + ahi) < (blo + bhi);
    });
    return all_roots;
}

// Compute conservative dyadic enclosure [res_lo, res_hi] / 2^(deg*shift) of p([a_lo, a_hi] / 2^shift)
inline void eval_interval_dyadic(const Poly& p, const BigInt& a_lo, const BigInt& a_hi, uint32_t shift,
                                 BigInt& res_lo, BigInt& res_hi, uint32_t& res_shift) {
    if (p.is_zero()) { res_lo = BigInt(0); res_hi = BigInt(0); res_shift = 0; return; }
    int d = p.deg();
    BigInt L = p.c[d], U = p.c[d];
    uint32_t cur_shift = 0;
    for (int i = d - 1; i >= 0; --i) {
        // Multiply [L, U] / 2^cur_shift by [a_lo, a_hi] / 2^shift
        BigInt p1 = L * a_lo;
        BigInt p2 = L * a_hi;
        BigInt p3 = U * a_lo;
        BigInt p4 = U * a_hi;
        L = std::min({p1, p2, p3, p4});
        U = std::max({p1, p2, p3, p4});
        cur_shift += shift;
        if (!p.c[i].is_zero()) {
            BigInt ci = p.c[i] << cur_shift;
            L = L + ci;
            U = U + ci;
        }
    }
    res_lo = L;
    res_hi = U;
    res_shift = cur_shift;
}

inline BigInt floor_div_pow2(const BigInt& x, uint32_t s) {
    if (s == 0) return x;
    if (x.sign >= 0) return x >> s;
    // For negative x, floor(x / 2^s) = -ceil(|x| / 2^s) = -((|x| + 2^s - 1) >> s)
    BigInt abs_x = x.abs();
    BigInt mask = (BigInt(1) << s) - BigInt(1);
    return -((abs_x + mask) >> s);
}

inline BigInt ceil_div_pow2(const BigInt& x, uint32_t s) {
    return -floor_div_pow2(-x, s);
}
