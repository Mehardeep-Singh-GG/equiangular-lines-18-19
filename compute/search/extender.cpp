// Exact integer 1-vertex extender for equiangular line systems (alpha = 1/5).
// Uses __int128 arithmetic with Gray-code iteration over {+1} x {-1, +1}^{r-1}.
// ZERO floating-point operations.
//
// Input format on stdin (whitespace-separated integers, repeated for each query):
//   n r L
//   M (r x r integers, where M = L * G_{B,B}^{-1})
//   C ((n-r) x r integers, where C = L * G_{B^c, B} * G_{B,B}^{-1})
// Terminate with n = 0 (or EOF).
//
// Output format on stdout per query:
//   QUERY_BEGIN <idx> <n> <r>
//   HIT <q> <L> <x_B[0..r-1]> <x_Bc[0..n-r-1]>   (for every valid x with q <= 5*L)
//   QUERY_END <num_colspace_pm1> <num_le_5L> <num_eq_5L>

#include <algorithm>
#include <cstdint>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

using i128 = __int128_t;

static i128 parse_i128(const std::string& s) {
    if (s.empty()) return 0;
    size_t i = 0;
    bool neg = false;
    if (s[0] == '-') {
        neg = true;
        i = 1;
    } else if (s[0] == '+') {
        i = 1;
    }
    i128 val = 0;
    for (; i < s.size(); ++i) {
        val = val * 10 + (s[i] - '0');
    }
    return neg ? -val : val;
}

static std::string to_str(i128 v) {
    if (v == 0) return "0";
    bool neg = v < 0;
    if (neg) v = -v;
    std::string s;
    while (v > 0) {
        s.push_back(char('0' + int(v % 10)));
        v /= 10;
    }
    if (neg) s.push_back('-');
    std::reverse(s.begin(), s.end());
    return s;
}

static bool read_i128(i128& out) {
    std::string tok;
    if (!(std::cin >> tok)) return false;
    out = parse_i128(tok);
    return true;
}

int main() {
    std::ios::sync_with_stdio(false);
    std::cin.tie(nullptr);

    int query_idx = 0;
    while (true) {
        int n = 0, r = 0;
        if (!(std::cin >> n)) break;
        if (n == 0) break;
        if (!(std::cin >> r)) break;
        i128 L = 0;
        if (!read_i128(L)) break;
        if (r < 1 || r > 28 || n < r) {
            std::cerr << "Invalid dimensions n=" << n << " r=" << r << "\n";
            return 1;
        }
        int m = n - r;

        std::vector<i128> M(r * r);
        for (int i = 0; i < r * r; ++i) {
            if (!read_i128(M[i])) return 1;
        }
        std::vector<i128> C(m * r);
        for (int i = 0; i < m * r; ++i) {
            if (!read_i128(C[i])) return 1;
        }
        // Transpose C into column-major for fast Gray-code column updates: Ccol[k * m + i]
        std::vector<i128> Ccol(r * m);
        for (int i = 0; i < m; ++i) {
            for (int k = 0; k < r; ++k) {
                Ccol[k * m + i] = C[i * r + k];
            }
        }

        std::cout << "QUERY_BEGIN " << query_idx << " " << n << " " << r << "\n";

        std::vector<int> xB(r, 1);
        std::vector<i128> y(m, 0);
        for (int i = 0; i < m; ++i) {
            i128 sum = 0;
            for (int k = 0; k < r; ++k) {
                sum += C[i * r + k];
            }
            y[i] = sum;
        }

        uint64_t total_iters = uint64_t(1) << (r - 1);
        uint64_t num_colspace = 0;
        uint64_t num_le_5L = 0;
        uint64_t num_eq_5L = 0;
        i128 fiveL = 5 * L;

        auto check_current = [&]() {
            for (int i = 0; i < m; ++i) {
                if (y[i] != L && y[i] != -L) return;
            }
            ++num_colspace;
            i128 q = 0;
            for (int a = 0; a < r; ++a) {
                i128 row_sum = 0;
                int xa = xB[a];
                const i128* Ma = &M[a * r];
                for (int b = 0; b < r; ++b) {
                    row_sum += Ma[b] * xB[b];
                }
                q += xa * row_sum;
            }
            if (q <= fiveL) {
                ++num_le_5L;
                if (q == fiveL) ++num_eq_5L;
                std::cout << "HIT " << to_str(q) << " " << to_str(L);
                for (int a = 0; a < r; ++a) std::cout << " " << xB[a];
                for (int i = 0; i < m; ++i) {
                    int xi = (y[i] == L) ? 1 : -1;
                    std::cout << " " << xi;
                }
                std::cout << "\n";
            }
        };

        check_current();
        for (uint64_t t = 1; t < total_iters; ++t) {
            int bit = __builtin_ctzll(t);
            int k = bit + 1;  // flip xB[k], k in 1..r-1
            xB[k] = -xB[k];
            i128 delta_sign = 2 * xB[k];  // +2 if became +1, -2 if became -1
            const i128* ck = &Ccol[k * m];
            if (delta_sign == 2) {
                for (int i = 0; i < m; ++i) y[i] += 2 * ck[i];
            } else {
                for (int i = 0; i < m; ++i) y[i] -= 2 * ck[i];
            }
            check_current();
        }

        std::cout << "QUERY_END " << num_colspace << " " << num_le_5L << " " << num_eq_5L << "\n";
        ++query_idx;
    }
    return 0;
}
