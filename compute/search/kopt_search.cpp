// Multi-threaded exact __int128 k-deletion + 1-vertex extension + clique replacement search
// for equiangular line systems (alpha = 1/5) in R^d.
//
// ZERO floating-point trust in any elimination, rank, or extension check:
//   - Bareiss exact integer elimination over __int128 computes det and adjugate of G_{B,B}
//   - Exact __int128 verification of G_{B^c, B^c} * L == C * G_{B, B^c} proves exact rank r
//   - Gray-code __int128 enumeration over {+1} x {-1, +1}^{r-1} finds ALL extensions in R^d
//   - Bron-Kerbosch finds maximum clique in exact compatibility graph

#include <algorithm>
#include <atomic>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <mutex>
#include <numeric>
#include <random>
#include <sstream>
#include <string>
#include <thread>
#include <vector>

using i128 = __int128_t;

static i128 i128_abs(i128 x) { return x < 0 ? -x : x; }

static i128 i128_gcd(i128 a, i128 b) {
    a = i128_abs(a);
    b = i128_abs(b);
    while (b != 0) {
        i128 t = a % b;
        a = b;
        b = t;
    }
    return a;
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

// Compute exact integer basis B of size <= d for symmetric integer matrix G (m x m),
// along with L > 0, M = L * G_{B,B}^{-1}, C = L * G_{Bc,B} * G_{B,B}^{-1}.
// Returns true iff rank(G) == target_r and all __int128 checks succeed without overflow.
struct ExactDecomp {
    int m = 0;
    int r = 0;
    i128 L = 0;
    std::vector<int> B;
    std::vector<int> Bc;
    std::vector<i128> M;     // r x r
    std::vector<i128> Ccol;  // r x (m - r), column-major
};

static bool compute_exact_decomp(const std::vector<int>& G, int m, int target_r, ExactDecomp& out) {
    // 1. Use double RREF only as a fast pivot-index oracle, then verify 100% in __int128!
    std::vector<double> A(m * m);
    for (int i = 0; i < m * m; ++i) A[i] = double(G[i]);

    std::vector<int> pivots;
    pivots.reserve(target_r + 1);
    int row = 0;
    for (int col = 0; col < m && row < m; ++col) {
        int best = row;
        double best_abs = std::abs(A[row * m + col]);
        for (int r2 = row + 1; r2 < m; ++r2) {
            double v = std::abs(A[r2 * m + col]);
            if (v > best_abs) {
                best_abs = v;
                best = r2;
            }
        }
        if (best_abs < 1e-6) continue;
        if (best != row) {
            for (int c2 = col; c2 < m; ++c2) std::swap(A[row * m + c2], A[best * m + c2]);
        }
        double inv_p = 1.0 / A[row * m + col];
        for (int r2 = row + 1; r2 < m; ++r2) {
            double factor = A[r2 * m + col] * inv_p;
            if (std::abs(factor) < 1e-12) continue;
            for (int c2 = col; c2 < m; ++c2) {
                A[r2 * m + c2] -= factor * A[row * m + c2];
            }
        }
        pivots.push_back(col);
        ++row;
    }

    int r = int(pivots.size());
    if (r != target_r) return false;

    std::vector<bool> inB(m, false);
    for (int b : pivots) inB[b] = true;
    std::vector<int> Bc;
    Bc.reserve(m - r);
    for (int i = 0; i < m; ++i) {
        if (!inB[i]) Bc.push_back(i);
    }

    // 2. Exact __int128 Bareiss-style Gauss-Jordan on [G_{B,B} | I_r]
    // Actually standard fraction-free Gauss-Jordan (Bareiss) on r x (2r):
    std::vector<i128> W(r * 2 * r, 0);
    for (int i = 0; i < r; ++i) {
        for (int j = 0; j < r; ++j) {
            W[i * (2 * r) + j] = G[pivots[i] * m + pivots[j]];
        }
        W[i * (2 * r) + (r + i)] = 1;
    }

    i128 prev_pivot = 1;
    for (int k = 0; k < r; ++k) {
        i128 piv = W[k * (2 * r) + k];
        if (piv == 0) {
            // Try row swap among remaining rows
            int sw = -1;
            for (int i = k + 1; i < r; ++i) {
                if (W[i * (2 * r) + k] != 0) {
                    sw = i;
                    break;
                }
            }
            if (sw < 0) return false;
            for (int j = 0; j < 2 * r; ++j) std::swap(W[k * (2 * r) + j], W[sw * (2 * r) + j]);
            piv = W[k * (2 * r) + k];
        }
        for (int i = 0; i < r; ++i) {
            if (i == k) continue;
            i128 mik = W[i * (2 * r) + k];
            for (int j = 0; j < 2 * r; ++j) {
                if (j == k) continue;
                i128 num = W[i * (2 * r) + j] * piv - mik * W[k * (2 * r) + j];
                W[i * (2 * r) + j] = num / prev_pivot;
            }
            W[i * (2 * r) + k] = 0;
        }
        prev_pivot = piv;
    }

    // Now diagonal W[i, i] == prev_pivot == det(G_{B,B}) (with sign from swaps, make positive)
    i128 L = prev_pivot;
    if (L == 0) return false;
    int sign_L = (L < 0) ? -1 : 1;
    L = i128_abs(L);

    std::vector<i128> M(r * r);
    i128 g = L;
    for (int i = 0; i < r; ++i) {
        for (int j = 0; j < r; ++j) {
            i128 val = sign_L * W[i * (2 * r) + (r + j)];
            M[i * r + j] = val;
            if (val != 0) g = i128_gcd(g, val);
        }
    }
    if (g > 1) {
        L /= g;
        for (i128& v : M) v /= g;
    }
    const i128 SAFE_BOUND = i128(100000000000000000LL); // 10^17
    if (L <= 0 || L >= SAFE_BOUND) return false;
    for (const i128& v : M) if (i128_abs(v) >= SAFE_BOUND) return false;

    // Exact check 1: G_{B,B} * M == L * I_r
    for (int i = 0; i < r; ++i) {
        for (int j = 0; j < r; ++j) {
            i128 s = 0;
            for (int k = 0; k < r; ++k) {
                s += i128(G[pivots[i] * m + pivots[k]]) * M[k * r + j];
            }
            if (s != (i == j ? L : i128(0))) return false;
        }
    }

    // Compute C = G_{Bc, B} * M  (dimensions (m-r) x r)
    int bc_sz = m - r;
    std::vector<i128> C(bc_sz * r, 0);
    for (int i = 0; i < bc_sz; ++i) {
        int gi = Bc[i];
        for (int j = 0; j < r; ++j) {
            i128 s = 0;
            for (int k = 0; k < r; ++k) {
                s += i128(G[gi * m + pivots[k]]) * M[k * r + j];
            }
            C[i * r + j] = s;
        }
    }

    // Exact check 2: C * G_{B, Bc} == L * G_{Bc, Bc} (proves rank(G) == r exactly!)
    for (int i = 0; i < bc_sz; ++i) {
        int gi = Bc[i];
        for (int j = i; j < bc_sz; ++j) {
            int gj = Bc[j];
            i128 s = 0;
            for (int k = 0; k < r; ++k) {
                s += C[i * r + k] * i128(G[pivots[k] * m + gj]);
            }
            if (s != L * i128(G[gi * m + gj])) return false;
        }
    }

    out.m = m;
    out.r = r;
    out.L = L;
    out.B = std::move(pivots);
    out.Bc = std::move(Bc);
    out.M = std::move(M);
    out.Ccol.resize(r * bc_sz);
    for (int i = 0; i < bc_sz; ++i) {
        for (int k = 0; k < r; ++k) {
            out.Ccol[k * bc_sz + i] = C[i * r + k];
        }
    }
    return true;
}

struct ExtCandidate {
    std::vector<int> xB;
    std::vector<int> x;  // full length m in {-1, +1}
};

static std::vector<ExtCandidate> find_all_extensions_eq5(const ExactDecomp& dec) {
    int m = dec.m;
    int r = dec.r;
    int bc_sz = m - r;
    i128 L = dec.L;
    i128 fiveL = 5 * L;

    std::vector<ExtCandidate> cands;
    std::vector<int> xB(r, 1);
    std::vector<i128> y(bc_sz, 0);
    for (int i = 0; i < bc_sz; ++i) {
        i128 s = 0;
        for (int k = 0; k < r; ++k) s += dec.Ccol[k * bc_sz + i];
        y[i] = s;
    }

    auto check = [&]() {
        for (int i = 0; i < bc_sz; ++i) {
            if (y[i] != L && y[i] != -L) return;
        }
        i128 q = 0;
        for (int a = 0; a < r; ++a) {
            i128 row_s = 0;
            const i128* Ma = &dec.M[a * r];
            for (int b = 0; b < r; ++b) row_s += Ma[b] * xB[b];
            q += xB[a] * row_s;
        }
        if (q == fiveL) {
            ExtCandidate ec;
            ec.xB = xB;
            ec.x.assign(m, 0);
            for (int a = 0; a < r; ++a) ec.x[dec.B[a]] = xB[a];
            for (int i = 0; i < bc_sz; ++i) ec.x[dec.Bc[i]] = (y[i] == L) ? 1 : -1;
            cands.push_back(std::move(ec));
        }
    };

    check();
    uint64_t total_iters = uint64_t(1) << (r - 1);
    for (uint64_t t = 1; t < total_iters; ++t) {
        int k = __builtin_ctzll(t) + 1;
        xB[k] = -xB[k];
        const i128* ck = &dec.Ccol[k * bc_sz];
        if (xB[k] == 1) {
            for (int i = 0; i < bc_sz; ++i) y[i] += 2 * ck[i];
        } else {
            for (int i = 0; i < bc_sz; ++i) y[i] -= 2 * ck[i];
        }
        check();
    }
    return cands;
}

static int max_clique_size(const std::vector<std::vector<int>>& adj, std::vector<int>& best_clique) {
    int n = int(adj.size());
    best_clique.clear();
    if (n == 0) return 0;

    std::vector<int> cur;
    std::vector<int> P(n);
    std::iota(P.begin(), P.end(), 0);

    auto bk = [&](auto& self, std::vector<int>& R, std::vector<int> Pset) -> void {
        if (R.size() + Pset.size() <= best_clique.size()) return;
        if (Pset.empty()) {
            if (R.size() > best_clique.size()) best_clique = R;
            return;
        }
        // Pivot u in Pset maximizing degree in Pset
        int pivot = Pset[0];
        int max_deg = -1;
        for (int u : Pset) {
            int deg = 0;
            for (int v : Pset) deg += adj[u][v];
            if (deg > max_deg) {
                max_deg = deg;
                pivot = u;
            }
        }
        std::vector<int> candidates;
        for (int v : Pset) {
            if (!adj[pivot][v]) candidates.push_back(v);
        }
        for (int v : candidates) {
            R.push_back(v);
            std::vector<int> nextP;
            for (int w : Pset) {
                if (adj[v][w]) nextP.push_back(w);
            }
            self(self, R, std::move(nextP));
            R.pop_back();
            Pset.erase(std::remove(Pset.begin(), Pset.end(), v), Pset.end());
        }
    };

    bk(bk, cur, P);
    return int(best_clique.size());
}

int main(int argc, char** argv) {
    if (argc < 4) {
        std::cerr << "Usage: " << argv[0] << " <matrix_file.txt> <d> <mode: all1|all2|rand> [k] [num_samples] [threads] [seed]\n";
        return 1;
    }
    std::string path = argv[1];
    int d = std::stoi(argv[2]);
    std::string mode = argv[3];
    int k_param = (argc >= 5) ? std::stoi(argv[4]) : 2;
    int num_samples = (argc >= 6) ? std::stoi(argv[5]) : 1000;
    int num_threads = (argc >= 7) ? std::stoi(argv[6]) : 8;
    uint64_t seed = (argc >= 8) ? std::stoull(argv[7]) : 42ULL;

    std::ifstream fin(path);
    if (!fin) {
        std::cerr << "Cannot open " << path << "\n";
        return 1;
    }
    int n = 0;
    fin >> n;
    std::vector<int> S(n * n);
    for (int i = 0; i < n * n; ++i) fin >> S[i];

    // Build deletion subsets
    std::vector<std::vector<int>> deletions;
    if (mode == "all1") {
        for (int i = 0; i < n; ++i) deletions.push_back({i});
    } else if (mode == "all2") {
        for (int i = 0; i < n; ++i)
            for (int j = i + 1; j < n; ++j)
                deletions.push_back({i, j});
    } else if (mode == "all3") {
        for (int i = 0; i < n; ++i)
            for (int j = i + 1; j < n; ++j)
                for (int l = j + 1; l < n; ++l)
                    deletions.push_back({i, j, l});
    } else if (mode == "rand") {
        std::mt19937_64 rng(seed);
        std::vector<int> idx(n);
        std::iota(idx.begin(), idx.end(), 0);
        for (int s = 0; s < num_samples; ++s) {
            std::shuffle(idx.begin(), idx.end(), rng);
            std::vector<int> del(idx.begin(), idx.begin() + k_param);
            std::sort(del.begin(), del.end());
            deletions.push_back(std::move(del));
        }
    } else {
        std::cerr << "Unknown mode: " << mode << "\n";
        return 1;
    }

    std::atomic<size_t> next_job{0};
    std::atomic<size_t> rank_d_count{0};
    std::atomic<size_t> rank_lt_d_count{0};
    std::atomic<size_t> total_cands{0};
    std::atomic<size_t> alt_k_count{0};
    std::atomic<size_t> win_count{0};
    std::mutex io_mtx;

    auto worker = [&]() {
        while (true) {
            size_t j = next_job.fetch_add(1);
            if (j >= deletions.size()) break;
            const auto& del = deletions[j];
            int k = int(del.size());
            std::vector<bool> is_del(n, false);
            for (int x : del) is_del[x] = true;
            std::vector<int> keep;
            keep.reserve(n - k);
            for (int i = 0; i < n; ++i) if (!is_del[i]) keep.push_back(i);

            int m = n - k;
            std::vector<int> Gsub(m * m);
            for (int a = 0; a < m; ++a) {
                for (int b = 0; b < m; ++b) {
                    int val = S[keep[a] * n + keep[b]];
                    Gsub[a * m + b] = (a == b) ? 5 : val;
                }
            }

            ExactDecomp dec;
            if (!compute_exact_decomp(Gsub, m, d, dec)) {
                ++rank_lt_d_count;
                continue;
            }
            ++rank_d_count;

            auto cands = find_all_extensions_eq5(dec);
            total_cands += cands.size();
            if (int(cands.size()) <= k) continue;

            // Build compatibility graph on cands
            int nc = int(cands.size());
            std::vector<std::vector<int>> adj(nc, std::vector<int>(nc, 0));
            for (int u = 0; u < nc; ++u) {
                // Compute M * xB_u once
                std::vector<i128> Mxu(d, 0);
                for (int a = 0; a < d; ++a) {
                    i128 s = 0;
                    const i128* Ma = &dec.M[a * d];
                    for (int b = 0; b < d; ++b) s += Ma[b] * cands[u].xB[b];
                    Mxu[a] = s;
                }
                for (int v = u + 1; v < nc; ++v) {
                    i128 ip = 0;
                    for (int a = 0; a < d; ++a) ip += cands[v].xB[a] * Mxu[a];
                    if (ip == dec.L || ip == -dec.L) {
                        adj[u][v] = adj[v][u] = 1;
                    }
                }
            }

            std::vector<int> best_clq;
            int omega = max_clique_size(adj, best_clq);
            if (omega > k) {
                ++win_count;
                std::lock_guard<std::mutex> lk(io_mtx);
                std::cout << "WIN_EXTENSION! deleted=";
                for (int x : del) std::cout << x << ",";
                std::cout << " omega=" << omega << " new_n=" << (m + omega) << "\n";
                for (int idx_c : best_clq) {
                    std::cout << "VEC";
                    for (int val : cands[idx_c].x) std::cout << " " << val;
                    std::cout << "\n";
                }
                std::cout.flush();
            } else if (omega == k && nc > k) {
                ++alt_k_count;
            }
        }
    };

    std::vector<std::thread> threads;
    for (int t = 0; t < num_threads; ++t) threads.emplace_back(worker);
    for (auto& th : threads) th.join();

    std::cout << "SUMMARY mode=" << mode << " k=" << k_param
              << " jobs=" << deletions.size()
              << " rank_d=" << rank_d_count.load()
              << " rank_lt_d=" << rank_lt_d_count.load()
              << " total_cands=" << total_cands.load()
              << " jobs_with_extra_cands=" << alt_k_count.load()
              << " wins(omega>k)=" << win_count.load() << "\n";
    return 0;
}
