// Fast C++20 probe for (19, 74) idx=13:
// 1. Search 8-regular graphs A on 24 vertices minimizing sum_{i: lam_i > 2} (lam_i - 2)^2 + top8-to-2 gap.
// 2. Search S1=(24,48,0,2) full 74x74 Seidel matrix with exact block locks minimizing sum_{i=0}^{54} (lam_i + 5)^2.
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <random>
#include <vector>

static void jacobi_eigs(int n, const std::vector<double>& Ain, std::vector<double>& evals) {
    std::vector<double> A = Ain;
    std::vector<double> b(n), z(n, 0.0);
    for (int i = 0; i < n; ++i) b[i] = A[i * n + i];
    evals = b;
    for (int it = 0; it < 50; ++it) {
        double sm = 0.0;
        for (int p = 0; p < n - 1; ++p)
            for (int q = p + 1; q < n; ++q)
                sm += std::abs(A[p * n + q]);
        if (sm < 1e-11) break;
        double tresh = (it < 3) ? (0.2 * sm / (n * n)) : 0.0;
        for (int p = 0; p < n - 1; ++p) {
            for (int q = p + 1; q < n; ++q) {
                double g = 100.0 * std::abs(A[p * n + q]);
                if (it > 3 && g <= 1e-13 * std::abs(evals[p]) && g <= 1e-13 * std::abs(evals[q])) {
                    A[p * n + q] = 0.0;
                } else if (std::abs(A[p * n + q]) > tresh) {
                    double h = evals[q] - evals[p];
                    double t;
                    if (g <= 1e-13 * std::abs(h)) {
                        t = A[p * n + q] / h;
                    } else {
                        double theta = 0.5 * h / A[p * n + q];
                        t = 1.0 / (std::abs(theta) + std::sqrt(1.0 + theta * theta));
                        if (theta < 0.0) t = -t;
                    }
                    double c = 1.0 / std::sqrt(1.0 + t * t);
                    double s = t * c;
                    double tau = s / (1.0 + c);
                    h = t * A[p * n + q];
                    z[p] -= h;
                    z[q] += h;
                    evals[p] -= h;
                    evals[q] += h;
                    A[p * n + q] = 0.0;
                    for (int j = 0; j < p; ++j) {
                        double gp = A[j * n + p], gq = A[j * n + q];
                        A[j * n + p] = gp - s * (gq + gp * tau);
                        A[j * n + q] = gq + s * (gp - gq * tau);
                    }
                    for (int j = p + 1; j < q; ++j) {
                        double gp = A[p * n + j], gq = A[j * n + q];
                        A[p * n + j] = gp - s * (gq + gp * tau);
                        A[j * n + q] = gq + s * (gp - gq * tau);
                    }
                    for (int j = q + 1; j < n; ++j) {
                        double gp = A[p * n + j], gq = A[q * n + j];
                        A[p * n + j] = gp - s * (gq + gp * tau);
                        A[q * n + j] = gq + s * (gp - gq * tau);
                    }
                }
            }
        }
        for (int i = 0; i < n; ++i) {
            b[i] += z[i];
            evals[i] = b[i];
            z[i] = 0.0;
        }
    }
    std::sort(evals.begin(), evals.end());
}

static double eval_24(const int A[24][24], std::vector<double>& ev) {
    std::vector<double> M(24 * 24);
    for (int i = 0; i < 24; ++i)
        for (int j = 0; j < 24; ++j)
            M[i * 24 + j] = A[i][j];
    jacobi_eigs(24, M, ev);
    double loss = 0.0;
    // ev[23] is 8.0. Check ev[0..22] <= 2.0 and ev[15..22] == 2.0
    for (int i = 0; i < 23; ++i) {
        if (ev[i] > 2.0) loss += 10.0 * (ev[i] - 2.0) * (ev[i] - 2.0);
    }
    for (int i = 15; i < 23; ++i) {
        loss += (ev[i] - 2.0) * (ev[i] - 2.0);
    }
    return loss;
}

int main() {
    std::cout << "=== C++ search for 24-vertex 8-reg graph A with lam_2<=2, mult(2)>=8 ===\n";
    double global_best = 1e9;
    std::vector<double> best_ev;
    int best_A[24][24];
    for (int seed = 0; seed < 40; ++seed) {
        std::mt19937_64 rng(seed + 100);
        int A[24][24] = {};
        std::vector<std::pair<int, int>> edges;
        while (true) {
            std::vector<int> stubs;
            for (int v = 0; v < 24; ++v)
                for (int k = 0; k < 8; ++k) stubs.push_back(v);
            std::shuffle(stubs.begin(), stubs.end(), rng);
            std::fill(&A[0][0], &A[0][0] + 576, 0);
            edges.clear();
            bool ok = true;
            for (size_t k = 0; k < stubs.size(); k += 2) {
                int u = stubs[k], v = stubs[k + 1];
                if (u == v || A[u][v]) { ok = false; break; }
                A[u][v] = A[v][u] = 1;
                edges.push_back({u, v});
            }
            if (ok) break;
        }
        std::vector<double> ev;
        double cur_loss = eval_24(A, ev);
        double seed_best = cur_loss;
        std::vector<double> seed_ev = ev;
        for (int step = 0; step < 50000; ++step) {
            int i1 = rng() % edges.size();
            int i2 = rng() % edges.size();
            if (i1 == i2) continue;
            auto [u1, v1] = edges[i1];
            auto [u2, v2] = edges[i2];
            if (u1 == u2 || u1 == v2 || v1 == u2 || v1 == v2) continue;
            int a1 = u1, b1 = (rng() & 1) ? u2 : v2;
            int a2 = v1, b2 = (b1 == u2) ? v2 : u2;
            if (A[a1][b1] || A[a2][b2]) continue;
            A[u1][v1] = A[v1][u1] = 0;
            A[u2][v2] = A[v2][u2] = 0;
            A[a1][b1] = A[b1][a1] = 1;
            A[a2][b2] = A[b2][a2] = 1;
            double nl = eval_24(A, ev);
            double T = 0.25 * std::pow(0.01, double(step) / 50000.0);
            std::uniform_real_distribution<double> U(0.0, 1.0);
            if (nl <= cur_loss || U(rng) < std::exp(-(nl - cur_loss) / T)) {
                cur_loss = nl;
                edges[i1] = {a1, b1};
                edges[i2] = {a2, b2};
                if (nl < seed_best) {
                    seed_best = nl;
                    seed_ev = ev;
                    if (nl < global_best) {
                        global_best = nl;
                        best_ev = ev;
                        std::copy(&A[0][0], &A[0][0] + 576, &best_A[0][0]);
                    }
                    if (nl < 1e-8) break;
                }
            } else {
                A[a1][b1] = A[b1][a1] = 0;
                A[a2][b2] = A[b2][a2] = 0;
                A[u1][v1] = A[v1][u1] = 1;
                A[u2][v2] = A[v2][u2] = 1;
            }
        }
        if (global_best < 1e-8) break;
    }
    std::cout << "Best 24-vertex 8-reg loss = " << global_best << "\nTop 12 eigs:";
    for (int i = 12; i < 24; ++i) std::cout << " " << best_ev[i];
    std::cout << "\n";
    if (global_best < 1e-6) {
        std::cout << "FOUND EXACT 24-vertex 8-reg graph! Checking B*B^T:\n";
        for (int i = 0; i < 24; ++i) {
            for (int j = 0; j < 24; ++j) std::cout << best_A[i][j];
            std::cout << "\n";
        }
    }
    return 0;
}
