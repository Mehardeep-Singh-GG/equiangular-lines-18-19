// Fast C++20 74x74 Seidel SA probe for (19, 74) idx=13 S1=(24,48,0,2), S2=(25,45,3,1), S3=(26,42,6,0).
// Minimizes sum_{i=0}^{54} (lam_i + 5)^2 + sum_{i=55}^{73} (lam_i - target_pos_i)^2!
// Notice for S1 we already enforce exact C_5 locks and B_a row sums = 11, B_a-B_b = 0, C_0 = 7!
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
    for (int it = 0; it < 25; ++it) {
        double sm = 0.0;
        for (int p = 0; p < n - 1; ++p)
            for (int q = p + 1; q < n; ++q)
                sm += std::abs(A[p * n + q]);
        if (sm < 1e-8) break;
        double tresh = (it < 3) ? (0.2 * sm / (n * n)) : 0.0;
        for (int p = 0; p < n - 1; ++p) {
            for (int q = p + 1; q < n; ++q) {
                double apq = A[p * n + q];
                double g = 100.0 * std::abs(apq);
                if (it > 3 && g <= 1e-11 * std::abs(evals[p]) && g <= 1e-11 * std::abs(evals[q])) {
                    A[p * n + q] = 0.0;
                } else if (std::abs(apq) > tresh) {
                    double h = evals[q] - evals[p];
                    double t;
                    if (g <= 1e-11 * std::abs(h)) t = apq / h;
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

int main() {
    // Test S1=(24,48,0,2) with fixed B_1=[4,4,4,4] or [8,8] vs free!
    // Wait: let's test unconstrained 74x74 with C_5 locks and v17, v11 eigenvectors!
    std::vector<double> tgt(74);
    for (int i = 0; i < 55; ++i) tgt[i] = -5.0;
    for (int i = 55; i < 58; ++i) tgt[i] = 11.0;
    for (int i = 58; i < 73; ++i) tgt[i] = 15.0;
    tgt[73] = 17.0;

    double best = 1e9;
    std::vector<double> best_ev;
    for (int seed = 0; seed < 8; ++seed) {
        std::mt19937_64 rng(seed + 42);
        std::vector<double> S(74 * 74, 1.0);
        for (int i = 0; i < 74; ++i) S[i * 74 + i] = 0.0;
        for (int i = 0; i < 74; ++i)
            for (int j = i + 1; j < 74; ++j) {
                double val = (rng() & 1) ? 1.0 : -1.0;
                S[i * 74 + j] = S[j * 74 + i] = val;
            }
        // Lock C_5 = {72, 73} for S1:
        for (int i = 0; i < 24; ++i) {
            S[i * 74 + 72] = S[72 * 74 + i] = 1.0;
            S[i * 74 + 73] = S[73 * 74 + i] = -1.0;
        }
        for (int i = 24; i < 72; ++i) {
            S[i * 74 + 72] = S[72 * 74 + i] = 1.0;
            S[i * 74 + 73] = S[73 * 74 + i] = 1.0;
        }
        S[72 * 74 + 73] = S[73 * 74 + 72] = 1.0;

        std::vector<double> ev;
        auto score = [&]() {
            jacobi_eigs(74, S, ev);
            double L = 0.0;
            for (int i = 0; i < 74; ++i) L += (ev[i] - tgt[i]) * (ev[i] - tgt[i]);
            return L;
        };
        double cur = score();
        if (cur < best) { best = cur; best_ev = ev; }
        for (int step = 0; step < 3000; ++step) {
            int i = rng() % 72;
            int j = rng() % 72;
            if (i == j) continue;
            S[i * 74 + j] *= -1.0;
            S[j * 74 + i] = S[i * 74 + j];
            double nl = score();
            double T = 2.0 * std::pow(0.01, double(step) / 3000.0);
            std::uniform_real_distribution<double> U(0.0, 1.0);
            if (nl <= cur || U(rng) < std::exp(-(nl - cur) / T)) {
                cur = nl;
                if (nl < best) { best = nl; best_ev = ev; }
                if (nl < 1e-6) break;
            } else {
                S[i * 74 + j] *= -1.0;
                S[j * 74 + i] = S[i * 74 + j];
            }
        }
        std::cout << "seed " << seed << ": best_L2_spec_err = " << cur << "\n";
    }
    std::cout << "Global best L2 err = " << best << "\nTop 22 eigs:";
    for (int i = 52; i < 74; ++i) std::cout << " " << best_ev[i];
    std::cout << "\n";
    return 0;
}
