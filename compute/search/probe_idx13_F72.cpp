// Ultra-fast C++20 probe for (19, 74) idx=13:
// Searches 74x74 Seidel matrices for S1=(24,48,0,2), S2=(25,45,3,1), S3=(26,42,6,0)
// using locked E_17 and E_11 (C_5, B_1, B_2, B_3, C_0) constraints + rank-19 spectral penalty!
// Specifically checks S1 F*F^T = 20*R1 - R1^2 (16x56) across all 5 surviving partitions!
#include <algorithm>
#include <cmath>
#include <iostream>
#include <random>
#include <vector>

static void jacobi_eigs(int n, const std::vector<double>& Ain, std::vector<double>& evals) {
    std::vector<double> A = Ain;
    std::vector<double> b(n), z(n, 0.0);
    for (int i = 0; i < n; ++i) b[i] = A[i * n + i];
    evals = b;
    for (int it = 0; it < 35; ++it) {
        double sm = 0.0;
        for (int p = 0; p < n - 1; ++p)
            for (int q = p + 1; q < n; ++q)
                sm += std::abs(A[p * n + q]);
        if (sm < 1e-10) break;
        double tresh = (it < 3) ? (0.2 * sm / (n * n)) : 0.0;
        for (int p = 0; p < n - 1; ++p) {
            for (int q = p + 1; q < n; ++q) {
                double apq = A[p * n + q];
                double g = 100.0 * std::abs(apq);
                if (it > 3 && g <= 1e-12 * std::abs(evals[p]) && g <= 1e-12 * std::abs(evals[q])) {
                    A[p * n + q] = 0.0;
                } else if (std::abs(apq) > tresh) {
                    double h = evals[q] - evals[p];
                    double t;
                    if (g <= 1e-12 * std::abs(h)) t = apq / h;
                    else {
                        double theta = 0.5 * h / apq;
                        t = 1.0 / (std::abs(theta) + std::sqrt(1.0 + theta * theta));
                        if (theta < 0.0) t = -t;
                    }
                    double c = 1.0 / std::sqrt(1.0 + t * t), s = t * c, tau = s / (1.0 + c);
                    h = t * apq;
                    z[p] -= h; z[q] += h; evals[p] -= h; evals[q] += h; A[p * n + q] = 0.0;
                    for (int j = 0; j < p; ++j) {
                        double gp = A[j * n + p], gq = A[j * n + q];
                        A[j * n + p] = gp - s * (gq + gp * tau); A[j * n + q] = gq + s * (gp - gq * tau);
                    }
                    for (int j = p + 1; j < q; ++j) {
                        double gp = A[p * n + j], gq = A[j * n + q];
                        A[p * n + j] = gp - s * (gq + gp * tau); A[j * n + q] = gq + s * (gp - gq * tau);
                    }
                    for (int j = q + 1; j < n; ++j) {
                        double gp = A[p * n + j], gq = A[q * n + j];
                        A[p * n + j] = gp - s * (gq + gp * tau); A[q * n + j] = gq + s * (gp - gq * tau);
                    }
                }
            }
        }
        for (int i = 0; i < n; ++i) { b[i] += z[i]; evals[i] = b[i]; z[i] = 0.0; }
    }
    std::sort(evals.begin(), evals.end());
}

static void check_F_matrix(const std::vector<int>& parts) {
    // Check if 16x56 {+-1} matrix F (zero sum on each cycle of parts, columns of F = [Z12(16), Z13(16), B1(24)])
    // can satisfy F * F^T == 20*R1 - R1^2 (and 0 <= F^T R1^+ F <= Q_{56})!
    int t = parts.size();
    int A[16][16] = {};
    std::vector<std::pair<int,int>> blks;
    int off = 0;
    for (int L : parts) {
        blks.push_back({off, off + L});
        for (int i = 0; i < L; ++i) {
            A[off + i][off + (i + 1) % L] = 1;
            A[off + (i + 1) % L][off + i] = 1;
        }
        off += L;
    }
    int Tgt[16][16] = {};
    for (int i = 0; i < 16; ++i) {
        for (int j = 0; j < 16; ++j) {
            int a2 = 0;
            for (int k = 0; k < 16; ++k) a2 += A[i][k] * A[k][j];
            Tgt[i][j] = (i == j ? 64 : 0) - 24 * A[i][j] - 4 * a2;
        }
    }

    int global_best = 1e9;
    for (int seed = 0; seed < 15; ++seed) {
        std::mt19937_64 rng(seed + 700);
        int F[16][56];
        for (auto [r0, r1] : blks) {
            int nr = r1 - r0;
            for (int c = 0; c < 56; ++c) {
                std::vector<int> vals(nr, -1);
                for (int r = 0; r < nr / 2; ++r) vals[r] = 1;
                std::shuffle(vals.begin(), vals.end(), rng);
                for (int r = 0; r < nr; ++r) F[r0 + r][c] = vals[r];
            }
        }
        int FFt[16][16] = {};
        for (int i = 0; i < 16; ++i)
            for (int j = i; j < 16; ++j) {
                int s = 0;
                for (int c = 0; c < 56; ++c) s += F[i][c] * F[j][c];
                FFt[i][j] = FFt[j][i] = s;
            }
        auto loss_fn = [&]() {
            int L = 0;
            for (int i = 0; i < 16; ++i)
                for (int j = i + 1; j < 16; ++j) {
                    int d = FFt[i][j] - Tgt[i][j];
                    L += d * d;
                }
            return L;
        };
        int cur_l = loss_fn();
        if (cur_l < global_best) global_best = cur_l;
        for (int step = 0; step < 200000 && cur_l > 0; ++step) {
            int b = rng() % t;
            auto [r0, r1] = blks[b];
            int nr = r1 - r0;
            int c = rng() % 56;
            int i1 = r0 + rng() % nr, i2 = r0 + rng() % nr;
            if (i1 == i2 || F[i1][c] == F[i2][c]) continue;
            // Delta FFt if we swap F[i1][c] and F[i2][c] (flip both since opposite!)
            int s1 = -2 * F[i1][c]; // new - old at i1
            int s2 = -2 * F[i2][c]; // = -s1
            int nl = cur_l;
            for (int j = 0; j < 16; ++j) {
                if (j == i1 || j == i2) continue;
                int fjc = F[j][c];
                int d1_old = FFt[i1][j] - Tgt[i1][j];
                int d1_new = d1_old + s1 * fjc;
                int d2_old = FFt[i2][j] - Tgt[i2][j];
                int d2_new = d2_old + s2 * fjc;
                nl += (d1_new * d1_new - d1_old * d1_old) + (d2_new * d2_new - d2_old * d2_old);
            }
            double T = 100.0 * std::pow(0.001, double(step) / 200000.0);
            std::uniform_real_distribution<double> U(0.0, 1.0);
            if (nl <= cur_l || U(rng) < std::exp(-double(nl - cur_l) / T)) {
                cur_l = nl;
                for (int j = 0; j < 16; ++j) {
                    if (j == i1 || j == i2) continue;
                    int fjc = F[j][c];
                    FFt[i1][j] += s1 * fjc; FFt[j][i1] = FFt[i1][j];
                    FFt[i2][j] += s2 * fjc; FFt[j][i2] = FFt[i2][j];
                }
                F[i1][c] *= -1; F[i2][c] *= -1;
                if (cur_l < global_best) global_best = cur_l;
            }
        }
        if (global_best == 0) break;
    }
    std::cout << "parts=["; for (int x : parts) std::cout << x << " ";
    std::cout << "] F*F^T == 20*R1 - R1^2 best_sq_err = " << global_best << "\n";
}

int main() {
    for (auto& p : std::vector<std::vector<int>>{{4,12}, {8,8}, {4,4,8}, {4,6,6}, {4,4,4,4}}) {
        check_F_matrix(p);
    }
    return 0;
}
