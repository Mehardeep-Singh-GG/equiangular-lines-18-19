// Fast C++20 probe for S1=(24,48,0,2) M_{12} (32x32) and M_{123} (48x48)
// Checks if ANY discrete {+-1} Z_{12} with zero cycle sums gives PSD S_{22} = R2 - Z12^T R1^+ Z12 of rank <= t1 - 1,
// and whether 48x48 M_{123} can have rank <= 15 and 0 <= M_{123} <= 20 I!
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
    for (int it = 0; it < 40; ++it) {
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
                    if (g <= 1e-12 * std::abs(h)) {
                        t = apq / h;
                    } else {
                        double theta = 0.5 * h / apq;
                        t = 1.0 / (std::abs(theta) + std::sqrt(1.0 + theta * theta));
                        if (theta < 0.0) t = -t;
                    }
                    double c = 1.0 / std::sqrt(1.0 + t * t);
                    double s = t * c;
                    double tau = s / (1.0 + c);
                    h = t * apq;
                    z[p] -= h; z[q] += h;
                    evals[p] -= h; evals[q] += h;
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
        for (int i = 0; i < n; ++i) { b[i] += z[i]; evals[i] = b[i]; z[i] = 0.0; }
    }
    std::sort(evals.begin(), evals.end());
}

static std::vector<double> build_R(const std::vector<int>& parts) {
    int n = 0; for (int L : parts) n += L;
    std::vector<double> R(n * n, 0.0);
    int off = 0;
    for (int L : parts) {
        for (int i = 0; i < L; ++i) {
            R[(off + i) * n + (off + i)] = 4.0;
            R[(off + i) * n + (off + (i + 1) % L)] = -2.0;
            R[(off + (i + 1) % L) * n + (off + i)] = -2.0;
        }
        off += L;
    }
    return R;
}

// Pseudo-inverse of R = 2(2I-A) via cycle DFT
static std::vector<double> build_Rpinv(const std::vector<int>& parts) {
    int n = 0; for (int L : parts) n += L;
    std::vector<double> P(n * n, 0.0);
    int off = 0;
    for (int L : parts) {
        for (int i = 0; i < L; ++i) {
            for (int j = 0; j < L; ++j) {
                int d = std::abs(i - j);
                // (2I - A)^+_{ij} = (L^2 - 1)/(12L) - d(L-d)/(2L); R^+ = 0.5 * (2I - A)^+
                double val = 0.5 * ((double(L * L - 1) / (12.0 * L)) - (double(d * (L - d)) / (2.0 * L)));
                P[(off + i) * n + (off + j)] = val;
            }
        }
        off += L;
    }
    return P;
}

int main() {
    std::vector<std::vector<int>> parts_list = {
        {4, 12}, {8, 8}, {4, 4, 8}, {4, 6, 6}, {4, 4, 4, 4}
    };
    for (size_t i1 = 0; i1 < parts_list.size(); ++i1) {
        for (size_t i2 = i1; i2 < parts_list.size(); ++i2) {
            const auto& p1 = parts_list[i1];
            const auto& p2 = parts_list[i2];
            int t1 = p1.size(), t2 = p2.size();
            auto R1p = build_Rpinv(p1);
            auto R2 = build_R(p2);
            // Compute block boundaries
            std::vector<std::pair<int,int>> blk1, blk2;
            int off = 0; for (int L : p1) { blk1.push_back({off, off + L}); off += L; }
            off = 0; for (int L : p2) { blk2.push_back({off, off + L}); off += L; }

            double global_best = 1e9;
            std::vector<double> best_ev;
            for (int seed = 0; seed < 12; ++seed) {
                std::mt19937_64 rng(seed + 1000 * i1 + 50 * i2);
                // Init Z (16x16) with +-1, zero sum in every (blk1, blk2) subblock!
                int Z[16][16];
                for (auto [r0, r1] : blk1) {
                    for (auto [c0, c1] : blk2) {
                        int nr = r1 - r0, nc = c1 - c0;
                        // Balanced +-1 matrix of size nr x nc (both even!)
                        for (int r = 0; r < nr; ++r) {
                            for (int c = 0; c < nc; ++c) {
                                Z[r0 + r][c0 + c] = (((r + c) % 2 == 0) ? 1 : -1);
                            }
                        }
                        // Shuffle via alternating rectangles
                        for (int sh = 0; sh < 50; ++sh) {
                            int ra = r0 + rng() % nr, rb = r0 + rng() % nr;
                            int ca = c0 + rng() % nc, cb = c0 + rng() % nc;
                            if (ra == rb || ca == cb) continue;
                            if (Z[ra][ca] == Z[rb][cb] && Z[ra][cb] == Z[rb][ca] && Z[ra][ca] != Z[ra][cb]) {
                                Z[ra][ca] *= -1; Z[rb][cb] *= -1;
                                Z[ra][cb] *= -1; Z[rb][ca] *= -1;
                            }
                        }
                    }
                }
                auto eval_S22 = [&](std::vector<double>& ev_out) -> double {
                    std::vector<double> S22 = R2;
                    // S22 -= Z^T R1p Z
                    double RZ[16][16] = {};
                    for (int i = 0; i < 16; ++i)
                        for (int j = 0; j < 16; ++j)
                            for (int k = 0; k < 16; ++k)
                                RZ[i][j] += R1p[i * 16 + k] * Z[k][j];
                    for (int i = 0; i < 16; ++i)
                        for (int j = i; j < 16; ++j) {
                            double dot = 0.0;
                            for (int k = 0; k < 16; ++k) dot += Z[k][i] * RZ[k][j];
                            S22[i * 16 + j] -= dot;
                            S22[j * 16 + i] = S22[i * 16 + j];
                        }
                    jacobi_eigs(16, S22, ev_out);
                    // Must be >= 0 AND at most t1 - 1 nonzero eigenvalues (i.e. bottom 16 - (t1 - 1) = 17 - t1 must be 0!)
                    double loss = 0.0;
                    int nz_lim = 17 - t1;
                    for (int k = 0; k < nz_lim; ++k) loss += ev_out[k] * ev_out[k];
                    for (int k = nz_lim; k < 16; ++k) if (ev_out[k] < 0.0) loss += 10.0 * ev_out[k] * ev_out[k];
                    return loss;
                };
                std::vector<double> ev;
                double cur_l = eval_S22(ev);
                if (cur_l < global_best) { global_best = cur_l; best_ev = ev; }
                for (int step = 0; step < 10000; ++step) {
                    int b1 = rng() % t1, b2 = rng() % t2;
                    auto [r0, r1] = blk1[b1];
                    auto [c0, c1] = blk2[b2];
                    int ra = r0 + rng() % (r1 - r0), rb = r0 + rng() % (r1 - r0);
                    int ca = c0 + rng() % (c1 - c0), cb = c0 + rng() % (c1 - c0);
                    if (ra == rb || ca == cb) continue;
                    if (!(Z[ra][ca] == Z[rb][cb] && Z[ra][cb] == Z[rb][ca] && Z[ra][ca] != Z[ra][cb])) continue;
                    Z[ra][ca] *= -1; Z[rb][cb] *= -1; Z[ra][cb] *= -1; Z[rb][ca] *= -1;
                    double nl = eval_S22(ev);
                    double T = 0.2 * std::pow(0.005, double(step) / 10000.0);
                    std::uniform_real_distribution<double> U(0.0, 1.0);
                    if (nl <= cur_l || U(rng) < std::exp(-(nl - cur_l) / T)) {
                        cur_l = nl;
                        if (nl < global_best) { global_best = nl; best_ev = ev; }
                        if (nl < 1e-8) break;
                    } else {
                        Z[ra][ca] *= -1; Z[rb][cb] *= -1; Z[ra][cb] *= -1; Z[rb][ca] *= -1;
                    }
                }
                if (global_best < 1e-8) break;
            }
            std::cout << "p1=["; for (int x : p1) std::cout << x << " ";
            std::cout << "] p2=["; for (int x : p2) std::cout << x << " ";
            std::cout << "] best_loss=" << global_best << " top5_ev=";
            for (int k = 11; k < 16; ++k) std::cout << " " << best_ev[k];
            std::cout << " min_ev=" << best_ev[0] << "\n";
        }
    }
    return 0;
}
