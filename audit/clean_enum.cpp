// Independent clean-room exact enumerator in shifted coordinates y = 2*(z + c).
// Enumerates ALL polynomials g(y) = sum_{j=0}^d a_j y^{d-j} in Z[y] satisfying:
//   - a_0 = 1, a_1 = -5*n, a_2 = 12*n*(n-1)
//   - exact 2-adic Seidel divisibility on a_k (even n: 2^k | a_k; odd n: 2^{k-1} | a_k & 2^k | a_{2m})
//   - all d roots real and >= 0 (checked conservatively via certified interval Rolle bounds;
//     final exact square-free + QQ Sturm verification is performed by audit/verify_polys.py).
//
// Zero heuristic pruning, zero floating-point trust: outward-rounded interval enclosures
// guarantee ZERO false negatives (no valid candidate can ever be discarded).

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <limits>
#include <string>
#include <vector>

using i128 = __int128_t;
using u128 = __uint128_t;

static std::string to_str(i128 x) {
    if (x == 0) return "0";
    bool neg = x < 0;
    u128 v = neg ? (u128)(-x) : (u128)x;
    std::string s;
    while (v > 0) {
        s.push_back('0' + (int)(v % 10));
        v /= 10;
    }
    if (neg) s.push_back('-');
    std::reverse(s.begin(), s.end());
    return s;
}

struct Interval {
    double lo;
    double hi;
    static Interval exact(double x) { return {x, x}; }
    static Interval from_i128(i128 x) {
        double d = (double)x;
        i128 absx = x < 0 ? -x : x;
        if (absx <= (((i128)1) << 52)) {
            return {d, d};
        }
        return {std::nextafter(d, -std::numeric_limits<double>::infinity()),
                std::nextafter(d, std::numeric_limits<double>::infinity())};
    }
    Interval operator+(const Interval& o) const {
        double l = lo + o.lo;
        double h = hi + o.hi;
        return {std::nextafter(l, -std::numeric_limits<double>::infinity()),
                std::nextafter(h, std::numeric_limits<double>::infinity())};
    }
    Interval operator*(const Interval& o) const {
        double p1 = lo * o.lo, p2 = lo * o.hi, p3 = hi * o.lo, p4 = hi * o.hi;
        double l = std::min({p1, p2, p3, p4});
        double h = std::max({p1, p2, p3, p4});
        return {std::nextafter(l, -std::numeric_limits<double>::infinity()),
                std::nextafter(h, std::numeric_limits<double>::infinity())};
    }
};

static Interval eval_poly_iv(const std::vector<i128>& desc, const Interval& x) {
    Interval acc = Interval::from_i128(desc[0]);
    for (size_t i = 1; i < desc.size(); ++i) {
        acc = acc * x + Interval::from_i128(desc[i]);
    }
    return acc;
}

static int cert_sign(const std::vector<i128>& desc, double x) {
    // Strip exact trailing zeros (factor out x^m) to eliminate flatness near x = 0!
    size_t len = desc.size();
    size_t m = 0;
    while (len - m > 1 && desc[len - 1 - m] == 0) {
        m++;
    }
    if (m > 0) {
        if (x == 0.0) return 0;
        std::vector<i128> stripped(desc.begin(), desc.end() - m);
        Interval iv = eval_poly_iv(stripped, Interval::exact(x));
        int s = 0;
        if (iv.lo > 0.0) s = 1;
        else if (iv.hi < 0.0) s = -1;
        if (s == 0) return 0;
        if (x < 0.0 && (m % 2 == 1)) s = -s;
        return s;
    }
    Interval iv = eval_poly_iv(desc, Interval::exact(x));
    if (iv.lo > 0.0) return 1;
    if (iv.hi < 0.0) return -1;
    return 0;
}

struct ShiftedEnumerator {
    int d;
    int n;
    int c;
    double z_min;
    double z_max;
    std::vector<std::vector<i128>> comb;
    std::vector<i128> c_pows;
    uint64_t total_nodes = 0;
    uint64_t max_nodes = 0;
    uint64_t fallback_count = 0;
    std::vector<uint64_t> nodes;
    std::vector<std::vector<i128>> survivors_c; // c_list in h(w) or 2*h(w)

    ShiftedEnumerator(int d_, int n_, uint64_t max_nodes_ = 0)
        : d(d_), n(n_), max_nodes(max_nodes_), nodes(d_ + 1, 0) {
        c = (5 * n + d) / (2 * d);
        z_min = -(double)c;
        // Exact upper bound on z_i = mu_i/2 - c:
        // sum(mu_i) = 5n, sum(mu_i^2) = n(n+24) => mu_max <= (5n + sqrt((d-1)(d*n*(n+24) - 25n^2)))/d
        double s1 = 5.0 * n;
        double s2 = (double)n * (n + 24);
        double mu_max = (s1 + std::sqrt((double)(d - 1) * (d * s2 - s1 * s1))) / d;
        z_max = (mu_max / 2.0 - (double)c) + 1.0;

        comb.assign(d + 1, std::vector<i128>(d + 1, 0));
        for (int i = 0; i <= d; ++i) {
            comb[i][0] = comb[i][i] = 1;
            for (int j = 1; j < i; ++j) {
                comb[i][j] = comb[i - 1][j - 1] + comb[i - 1][j];
            }
        }
        c_pows.assign(d + 1, 1);
        for (int i = 1; i <= d; ++i) c_pows[i] = c_pows[i - 1] * c;
    }

    // Isolate k roots of P_k(z) in [z_min, z_max] given critical root intervals crit_ivs of P_{k-1}.
    // Conservative: only prunes when certified interval evaluation at a critical interval
    // strictly contradicts sign alternation (or endpoint z_min / z_max strictly contradicts sign).
    bool isolate_roots(int k, const std::vector<i128>& P_desc,
                       const std::vector<std::pair<double, double>>& crit_ivs,
                       std::vector<std::pair<double, double>>& out_ivs) {
        out_ivs.clear();
        for (int j = 0; j < k; ++j) {
            double L = (j == 0) ? z_min : crit_ivs[j - 1].first;
            double R = (j == k - 1) ? z_max : crit_ivs[j].second;
            int exp_sign_L = ((k - j) % 2 == 0) ? 1 : -1;
            int exp_sign_R = ((k - 1 - j) % 2 == 0) ? 1 : -1;

            int sL = 0;
            if (j == 0) {
                sL = cert_sign(P_desc, z_min);
            } else {
                Interval iv_c = eval_poly_iv(P_desc, {crit_ivs[j - 1].first, crit_ivs[j - 1].second});
                if (iv_c.lo > 0.0) sL = 1;
                else if (iv_c.hi < 0.0) sL = -1;
            }

            int sR = 0;
            if (j == k - 1) {
                sR = cert_sign(P_desc, z_max);
            } else {
                Interval iv_c = eval_poly_iv(P_desc, {crit_ivs[j].first, crit_ivs[j].second});
                if (iv_c.lo > 0.0) sR = 1;
                else if (iv_c.hi < 0.0) sR = -1;
            }

            if (sL == -exp_sign_L) return false;
            if (sR == -exp_sign_R) return false;

            double cL_lo = (j == 0) ? z_min : crit_ivs[j - 1].first;
            double cL_hi = (j == 0) ? z_min : crit_ivs[j - 1].second;
            double cR_lo = (j == k - 1) ? z_max : crit_ivs[j].first;
            double cR_hi = (j == k - 1) ? z_max : crit_ivs[j].second;

            double a = cL_lo;
            double b = cR_hi;
            // On [cL_hi, cR_lo], P_k is strictly monotone from exp_sign_L to exp_sign_R.
            // Any point x in [cL_hi, cR_lo] with cert_sign == exp_sign_L satisfies r_j > x;
            // any point x in [cL_hi, cR_lo] with cert_sign == exp_sign_R satisfies r_j < x.
            if (cL_hi < cR_lo) {
                double lo = cL_hi, hi = cR_lo;
                if (cert_sign(P_desc, lo) == exp_sign_L) a = lo;
                if (cert_sign(P_desc, hi) == exp_sign_R) b = hi;
                for (int it = 0; it < 54; ++it) {
                    double mid = 0.5 * (lo + hi);
                    if (mid == lo || mid == hi) break;
                    int sm = cert_sign(P_desc, mid);
                    if (sm == exp_sign_L) {
                        lo = mid;
                        if (mid > a) a = mid;
                    } else if (sm == exp_sign_R) {
                        hi = mid;
                        if (mid < b) b = mid;
                    } else {
                        // In uncertain zone near root: check quarter points to advance whichever side is monotone
                        double q1 = 0.5 * (lo + mid);
                        double q3 = 0.5 * (mid + hi);
                        int s1 = cert_sign(P_desc, q1);
                        int s3 = cert_sign(P_desc, q3);
                        bool moved = false;
                        if (s1 == exp_sign_L && q1 > a) { lo = q1; a = q1; moved = true; }
                        if (s3 == exp_sign_R && q3 < b) { hi = q3; b = q3; moved = true; }
                        if (!moved) break;
                    }
                }
            }
            if (b - a > 1e-4) {
                fallback_count++;
            }
            out_ivs.push_back({a, b});
        }
        return true;
    }

    void dfs(int k, std::vector<i128>& b_list, std::vector<i128>& c_list,
             const std::vector<std::pair<double, double>>& root_ivs) {
        nodes[k]++;
        total_nodes++;
        if (max_nodes > 0 && total_nodes > max_nodes) return;
        if (k == d) {
            survivors_c.push_back(c_list);
            return;
        }
        // Build Q_{k+1}(z) = sum_{j=0}^k C(d-j, k+1-j) b_j z^{k+1-j}
        std::vector<i128> Q_desc(k + 2, 0);
        for (int j = 0; j <= k; ++j) {
            Q_desc[j] = comb[d - j][k + 1 - j] * b_list[j];
        }

        // Endpoint constraint at z = z_min (-c): (-1)^(k+1) * (Q(-c) + b_{k+1}) >= 0
        Interval q_mc = eval_poly_iv(Q_desc, Interval::exact(z_min));
        bool has_L = false, has_U = false;
        double L_d = 0.0, U_d = 0.0;
        if ((k + 1) % 2 == 0) {
            has_L = true;
            L_d = -q_mc.hi;
        } else {
            has_U = true;
            U_d = -q_mc.lo;
        }

        for (int idx = 0; idx < k; ++idx) {
            Interval r_iv{root_ivs[idx].first, root_ivs[idx].second};
            Interval q_iv = eval_poly_iv(Q_desc, r_iv);
            int dist = (k - 1) - idx;
            if (dist % 2 == 0) {
                double u = -q_iv.lo;
                if (!has_U || u < U_d) { U_d = u; has_U = true; }
            } else {
                double l = -q_iv.hi;
                if (!has_L || l > L_d) { L_d = l; has_L = true; }
            }
        }

        if (has_L && has_U && L_d > U_d) return;

        // Compute offset = sum_{j=0}^k C(d-j, k+1-j) c^{k+1-j} c_j
        i128 off = 0;
        for (int j = 0; j <= k; ++j) {
            off += comb[d - j][k + 1 - j] * c_pows[k + 1 - j] * c_list[j];
        }
        i128 step = (n % 2 == 1 && (k + 1) % 2 == 0) ? 2 : 1;

        i128 L_int = (i128)std::ceil(L_d);
        i128 U_int = (i128)std::floor(U_d);

        if (step == 2) {
            i128 rem = (L_int - off) % 2;
            if (rem != 0) L_int += 1;
        }
        if (L_int > U_int) return;

        std::vector<i128> P_next = Q_desc;
        std::vector<std::pair<double, double>> next_ivs;
        for (i128 b_next = L_int; b_next <= U_int; b_next += step) {
            P_next[k + 1] = b_next;
            if (isolate_roots(k + 1, P_next, root_ivs, next_ivs)) {
                b_list.push_back(b_next);
                c_list.push_back(b_next - off);
                dfs(k + 1, b_list, c_list, next_ivs);
                b_list.pop_back();
                c_list.pop_back();
            }
        }
    }

    void run() {
        // Compute c_0, c_1, c_2 in h(w) (if n even) or 2*h(w) (if n odd)
        // Original g(y) has a_0 = 1, a_1 = -5n, a_2 = 12*n*(n-1).
        // Under y = 2w:
        //   even n: c_k = a_k / 2^k => c_0 = 1, c_1 = -5n/2, c_2 = 3*n*(n-1)
        //   odd  n: c_k = a_k / 2^{k-1} => c_0 = 2, c_1 = -5n, c_2 = 6*n*(n-1)
        i128 c0, c1, c2;
        if (n % 2 == 0) {
            c0 = 1;
            c1 = -(5 * n) / 2;
            c2 = (i128)3 * n * (n - 1);
        } else {
            c0 = 2;
            c1 = -5 * n;
            c2 = (i128)6 * n * (n - 1);
        }
        // b_list = shift w = z + c:
        i128 b0 = c0;
        i128 b1 = c1 + (i128)d * c * c0;
        i128 b2 = c2 + (i128)(d - 1) * c * c1 + comb[d][2] * c_pows[2] * c0;

        std::vector<i128> b_list = {b0, b1, b2};
        std::vector<i128> c_list = {c0, c1, c2};

        // P_2(z) = C(d,2) b0 z^2 + C(d-1,1) b1 z + b2
        std::vector<i128> P2 = {comb[d][2] * b0, comb[d - 1][1] * b1, b2};
        double crit = -(double)P2[1] / (2.0 * (double)P2[0]);
        std::vector<std::pair<double, double>> crit2 = {{crit - 1e-9, crit + 1e-9}};
        std::vector<std::pair<double, double>> r2_ivs;
        if (!isolate_roots(2, P2, crit2, r2_ivs)) {
            std::cerr << "P2 failed root isolation!\n";
            return;
        }
        dfs(2, b_list, c_list, r2_ivs);
    }
};

int main(int argc, char** argv) {
    if (argc < 3) {
        std::cerr << "Usage: clean_enum <d> <n>\n";
        return 1;
    }
    int d = std::stoi(argv[1]);
    int n = std::stoi(argv[2]);
    uint64_t max_nodes = (argc >= 4) ? std::stoull(argv[3]) : 0;
    ShiftedEnumerator en(d, n, max_nodes);
    en.run();
    std::cerr << "(d=" << d << ", n=" << n << ", c=" << en.c << ") fallbacks=" << en.fallback_count << " nodes:";
    uint64_t tot = 0;
    for (int k = 2; k <= d; ++k) {
        std::cerr << " " << en.nodes[k];
        tot += en.nodes[k];
    }
    std::cerr << " | total=" << tot << " | raw_survivors=" << en.survivors_c.size() << "\n";
    // Print g(y) coefficients a_k from c_k:
    //   even n: a_k = c_k * 2^k
    //   odd  n: a_0 = 1, a_k = c_k * 2^{k-1} for k >= 1
    for (const auto& clist : en.survivors_c) {
        for (int k = 0; k <= d; ++k) {
            i128 ak;
            if (n % 2 == 0) {
                ak = clist[k] * (((i128)1) << k);
            } else {
                ak = (k == 0) ? 1 : (clist[k] * (((i128)1) << (k - 1)));
            }
            if (k) std::cout << ",";
            std::cout << to_str(ak);
        }
        std::cout << "\n";
    }
    return 0;
}
