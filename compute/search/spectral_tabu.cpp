// Multi-threaded Spectral-Energy Tabu / Simulated Annealing Search for Seidel matrices S
// with rank(5I + S) <= d and 5I + S >= 0.
//
// Energy E(S) = sum_{i=1}^{n-d} mu_i^2 + sum_{i > n-d, mu_i < 0} mu_i^2,
// where mu_1 <= ... <= mu_n are eigenvalues of G = 5I + S (via Accelerate dsyevd_).
// Note E(S) = 0 iff 5I + S >= 0 and rank(5I + S) <= d.
//
// Uses first-order eigenvector perturbation to rank all n*(n-1)/2 single-entry flips,
// then evaluates top-K candidates via exact dsyevd_.

#include <algorithm>
#include <atomic>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <mutex>
#include <numeric>
#include <random>
#include <string>
#include <thread>
#include <vector>

#ifdef __APPLE__
#include <Accelerate/Accelerate.h>
#endif

struct Workspace {
    int n;
    std::vector<double> A;
    std::vector<double> W;
    std::vector<double> work_v;
    std::vector<int> iwork_v;
    std::vector<double> work_n;
    std::vector<int> iwork_n;
    int lwork_v, liwork_v, lwork_n, liwork_n;

    Workspace(int n_) : n(n_), A(n_ * n_), W(n_) {
        char jobz_v = 'V', jobz_n = 'N', uplo = 'U';
        int info = 0;
        double wk = 0;
        int iwk = 0;
        lwork_v = -1; liwork_v = -1;
        dsyevd_(&jobz_v, &uplo, &n, A.data(), &n, W.data(), &wk, &lwork_v, &iwk, &liwork_v, &info);
        lwork_v = int(wk) + 16;
        liwork_v = iwk + 16;
        work_v.resize(lwork_v);
        iwork_v.resize(liwork_v);

        lwork_n = -1; liwork_n = -1;
        dsyevd_(&jobz_n, &uplo, &n, A.data(), &n, W.data(), &wk, &lwork_n, &iwk, &liwork_n, &info);
        lwork_n = int(wk) + 16;
        liwork_n = iwk + 16;
        work_n.resize(lwork_n);
        iwork_n.resize(liwork_n);
    }

    double eval_energy_only(const std::vector<int8_t>& S, int d) {
        for (int i = 0; i < n; ++i) {
            for (int j = i; j < n; ++j) {
                A[j * n + i] = (i == j) ? 5.0 : double(S[i * n + j]);
            }
        }
        char jobz = 'N', uplo = 'U';
        int info = 0;
        dsyevd_(&jobz, &uplo, &n, A.data(), &n, W.data(), work_n.data(), &lwork_n, iwork_n.data(), &liwork_n, &info);
        double e = 0.0;
        int k_null = n - d;
        for (int i = 0; i < n; ++i) {
            if (i < k_null || W[i] < 0.0) e += W[i] * W[i];
        }
        return e;
    }

    double eval_full(const std::vector<int8_t>& S, int d) {
        for (int i = 0; i < n; ++i) {
            for (int j = i; j < n; ++j) {
                A[j * n + i] = (i == j) ? 5.0 : double(S[i * n + j]);
            }
        }
        char jobz = 'V', uplo = 'U';
        int info = 0;
        dsyevd_(&jobz, &uplo, &n, A.data(), &n, W.data(), work_v.data(), &lwork_v, iwork_v.data(), &liwork_v, &info);
        double e = 0.0;
        int k_null = n - d;
        for (int i = 0; i < n; ++i) {
            if (i < k_null || W[i] < 0.0) e += W[i] * W[i];
        }
        return e;
    }
};

static bool load_seed_matrix(const std::string& path, int& n_out, std::vector<int8_t>& S_out) {
    std::ifstream fin(path);
    if (!fin) return false;
    fin >> n_out;
    S_out.resize(n_out * n_out);
    for (int i = 0; i < n_out * n_out; ++i) {
        int v = 0;
        fin >> v;
        S_out[i] = int8_t(v);
    }
    return true;
}

int main(int argc, char** argv) {
    if (argc < 5) {
        std::cerr << "Usage: " << argv[0] << " <d> <n> <num_restarts> <max_steps_per_restart> [threads=8] [seed=42] [seed_matrix.txt]\n";
        return 1;
    }
    int d = std::stoi(argv[1]);
    int n = std::stoi(argv[2]);
    int num_restarts = std::stoi(argv[3]);
    int max_steps = std::stoi(argv[4]);
    int num_threads = (argc >= 6) ? std::stoi(argv[5]) : 8;
    uint64_t base_seed = (argc >= 7) ? std::stoull(argv[6]) : 42ULL;
    std::string seed_path = (argc >= 8) ? argv[7] : "";

    std::vector<int8_t> seed_S;
    int seed_n = 0;
    if (!seed_path.empty()) {
        if (!load_seed_matrix(seed_path, seed_n, seed_S)) {
            std::cerr << "Failed to load seed matrix " << seed_path << "\n";
            return 1;
        }
    }

    std::atomic<int> next_restart{0};
    std::atomic<double> global_best_E{1e18};
    std::atomic<int> solved_count{0};
    std::mutex io_mtx;

    auto worker = [&](int tid) {
        Workspace ws(n);
        int k_null = n - d;
        std::vector<int8_t> S(n * n, 0);
        std::vector<int> tabu_until(n * n, -1);
        std::vector<std::pair<int, int>> pairs;
        pairs.reserve(n * (n - 1) / 2);
        for (int i = 0; i < n; ++i)
            for (int j = i + 1; j < n; ++j)
                pairs.push_back({i, j});
        std::vector<std::pair<double, int>> scored(pairs.size());

        while (true) {
            int r_id = next_restart.fetch_add(1);
            if (r_id >= num_restarts) break;
            if (solved_count.load() > 0) break;

            std::mt19937_64 rng(base_seed + 1000003ULL * uint64_t(r_id + 1));
            std::fill(S.begin(), S.end(), 0);
            std::fill(tabu_until.begin(), tabu_until.end(), -1);

            if (!seed_S.empty() && seed_n == n - 1) {
                // Start from (n-1)x(n-1) seed + random last row/col (+ occasional random perturbation)
                for (int i = 0; i < seed_n; ++i)
                    for (int j = 0; j < seed_n; ++j)
                        S[i * n + j] = seed_S[i * seed_n + j];
                for (int i = 0; i < seed_n; ++i) {
                    int8_t v = (rng() & 1) ? 1 : -1;
                    S[i * n + (n - 1)] = S[(n - 1) * n + i] = v;
                }
                // Optional small perturbation on interior if r_id % 3 != 0
                if (r_id % 3 == 1) {
                    for (int p = 0; p < 5; ++p) {
                        int i = rng() % seed_n, j = rng() % seed_n;
                        if (i != j) { S[i * n + j] = -S[i * n + j]; S[j * n + i] = S[i * n + j]; }
                    }
                }
            } else {
                for (auto [i, j] : pairs) {
                    int8_t v = (rng() & 1) ? 1 : -1;
                    S[i * n + j] = S[j * n + i] = v;
                }
            }

            double cur_E = ws.eval_full(S, d);
            double best_local_E = cur_E;
            int no_improve = 0;
            const int K_EVAL = 20;

            for (int step = 0; step < max_steps; ++step) {
                if (cur_E < 1e-8) {
                    ++solved_count;
                    std::lock_guard<std::mutex> lk(io_mtx);
                    std::cout << "SOLVED_ZERO_ENERGY d=" << d << " n=" << n << " restart=" << r_id << " step=" << step << " E=" << cur_E << "\n";
                    std::cout << n << "\n";
                    for (int i = 0; i < n; ++i) {
                        for (int j = 0; j < n; ++j) {
                            std::cout << (j ? " " : "") << int(S[i * n + j]);
                        }
                        std::cout << "\n";
                    }
                    std::cout.flush();
                    break;
                }

                // Rank all flips using first-order spectral perturbation:
                // A[:, k] holds eigenvector k (column-major!)
                // Delta mu_k ~ 2 * (-2 * S[i,j]) * U[i,k] * U[j,k] = -4 * S[i,j] * U[i,k] * U[j,k]
                // Wait: dE ~ sum_{active k} 2 * mu_k * Delta_mu_k = -8 * S[i,j] * sum_{active k} mu_k * U[i,k] * U[j,k]
                std::vector<int> active_k;
                for (int k = 0; k < n; ++k) {
                    if (k < k_null || ws.W[k] < 0.0) active_k.push_back(k);
                }
                // Build weighted vector row-wise: R[i, idx] = ws.W[k] * U[i, k]
                // Actually compute M_grad = sum_{k in active} mu_k u_k u_k^T (symmetric n x n)
                std::vector<double> Ggrad(n * n, 0.0);
                for (int k : active_k) {
                    double wk = ws.W[k];
                    const double* uk = &ws.A[k * n];
                    for (int i = 0; i < n; ++i) {
                        double wuki = wk * uk[i];
                        for (int j = i + 1; j < n; ++j) {
                            Ggrad[i * n + j] += wuki * uk[j];
                        }
                    }
                }

                for (size_t idx = 0; idx < pairs.size(); ++idx) {
                    int i = pairs[idx].first, j = pairs[idx].second;
                    double dE_est = -8.0 * double(S[i * n + j]) * Ggrad[i * n + j];
                    scored[idx] = {dE_est, int(idx)};
                }
                std::partial_sort(scored.begin(), scored.begin() + std::min<int>(K_EVAL + 15, scored.size()), scored.end());

                // Evaluate top non-tabu (or aspiration) candidates with exact dsyevd_
                int best_idx = -1;
                double best_cand_E = 1e18;
                int evaled = 0;
                for (size_t pos = 0; pos < scored.size() && evaled < K_EVAL; ++pos) {
                    int p_idx = scored[pos].second;
                    int i = pairs[p_idx].first, j = pairs[p_idx].second;
                    bool is_tabu = (tabu_until[i * n + j] > step);
                    S[i * n + j] = S[j * n + i] = -S[i * n + j];
                    double cand_E = ws.eval_energy_only(S, d);
                    S[i * n + j] = S[j * n + i] = -S[i * n + j];
                    ++evaled;
                    if (!is_tabu || cand_E < best_local_E - 1e-9) {
                        if (cand_E < best_cand_E) {
                            best_cand_E = cand_E;
                            best_idx = p_idx;
                        }
                    }
                }
                if (best_idx < 0) {
                    // Fallback: random flip
                    best_idx = rng() % pairs.size();
                    int i = pairs[best_idx].first, j = pairs[best_idx].second;
                    S[i * n + j] = S[j * n + i] = -S[i * n + j];
                    cur_E = ws.eval_full(S, d);
                } else {
                    int i = pairs[best_idx].first, j = pairs[best_idx].second;
                    S[i * n + j] = S[j * n + i] = -S[i * n + j];
                    tabu_until[i * n + j] = step + 12 + int(rng() % 10);
                    cur_E = ws.eval_full(S, d);
                }

                if (cur_E < best_local_E - 1e-9) {
                    best_local_E = cur_E;
                    no_improve = 0;
                    double prev = global_best_E.load();
                    while (best_local_E < prev && !global_best_E.compare_exchange_weak(prev, best_local_E)) {}
                } else {
                    ++no_improve;
                    if (no_improve > 150) {
                        // Perturb 8 random entries to escape basin
                        for (int p = 0; p < 8; ++p) {
                            int idx = rng() % pairs.size();
                            int i = pairs[idx].first, j = pairs[idx].second;
                            S[i * n + j] = S[j * n + i] = -S[i * n + j];
                        }
                        cur_E = ws.eval_full(S, d);
                        no_improve = 0;
                    }
                }
            }

            if (r_id % 10 == 0 || best_local_E < 5.0) {
                std::lock_guard<std::mutex> lk(io_mtx);
                std::cout << "[restart " << r_id << "] best_local_E=" << best_local_E
                          << " global_best_E=" << global_best_E.load() << "\n";
            }
        }
    };

    std::vector<std::thread> threads;
    for (int t = 0; t < num_threads; ++t) threads.emplace_back(worker, t);
    for (auto& th : threads) th.join();

    std::cout << "DONE d=" << d << " n=" << n << " restarts=" << num_restarts
              << " global_best_E=" << global_best_E.load()
              << " solved=" << solved_count.load() << "\n";
    return 0;
}
