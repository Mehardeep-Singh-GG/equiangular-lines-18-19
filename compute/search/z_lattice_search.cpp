// Multi-threaded C++20 norm-10 integer lattice search in Z^d (d=18, 19).
// Searches for sets of vectors v in Z^d with ||v||^2 = 10 and v_i . v_j in {-2, +2}.
// Any found clique >= 57 (d=18) or >= 72 (d=19) is printed for exact SymPy verification.

#include <algorithm>
#include <array>
#include <atomic>
#include <cstdint>
#include <iostream>
#include <mutex>
#include <numeric>
#include <random>
#include <thread>
#include <vector>

struct Vec {
    std::array<int8_t, 20> x{};
};

static inline int dot_vec(const Vec& a, const Vec& b, int d) {
    int s = 0;
    for (int i = 0; i < d; ++i) s += int(a.x[i]) * int(b.x[i]);
    return s;
}

// Generate all canonical-half vectors (first nonzero > 0) of norm^2 = 10 in Z^d
// filtered by |v . v1| == 2, for v1 = (2, 2, 1, 1, 0^{d-4}).
static std::vector<Vec> generate_L1_for_2211(int d, const Vec& v1) {
    std::vector<Vec> out;
    out.reserve(8000000);

    auto push_if_compat = [&](const Vec& v) {
        // Canonical sign: first nonzero entry > 0
        for (int i = 0; i < d; ++i) {
            if (v.x[i] != 0) {
                if (v.x[i] < 0) return;
                break;
            }
        }
        int dp = dot_vec(v, v1, d);
        if (dp == 2 || dp == -2) out.push_back(v);
    };

    // Shape 1: (3, 1, 0...)
    for (int i = 0; i < d; ++i) {
        for (int j = 0; j < d; ++j) {
            if (i == j) continue;
            for (int si : {-3, 3}) {
                for (int sj : {-1, 1}) {
                    Vec v{};
                    v.x[i] = si;
                    v.x[j] = sj;
                    push_if_compat(v);
                }
            }
        }
    }

    // Shape 2: (2, 2, 1, 1, 0...)
    for (int i = 0; i < d; ++i) {
        for (int j = i + 1; j < d; ++j) {
            for (int a = 0; a < d; ++a) {
                if (a == i || a == j) continue;
                for (int b = a + 1; b < d; ++b) {
                    if (b == i || b == j) continue;
                    for (int mask = 0; mask < 16; ++mask) {
                        Vec v{};
                        v.x[i] = (mask & 1) ? 2 : -2;
                        v.x[j] = (mask & 2) ? 2 : -2;
                        v.x[a] = (mask & 4) ? 1 : -1;
                        v.x[b] = (mask & 8) ? 1 : -1;
                        push_if_compat(v);
                    }
                }
            }
        }
    }

    // Shape 3: (2, 1^6, 0...)
    std::vector<int> idx(d - 1);
    for (int p2 = 0; p2 < d; ++p2) {
        int pos = 0;
        for (int k = 0; k < d; ++k) if (k != p2) idx[pos++] = k;
        std::vector<int> sel(d - 1, 0);
        std::fill(sel.end() - 6, sel.end(), 1);
        do {
            int p_idx[6], c = 0;
            for (int k = 0; k < d - 1; ++k) if (sel[k]) p_idx[c++] = idx[k];
            // Quick bound on |v . v1| before inner loop? Skip for simplicity, only ~18*C(18,6)=334k combos
            for (int s2 : {-2, 2}) {
                for (int mask = 0; mask < 64; ++mask) {
                    Vec v{};
                    v.x[p2] = s2;
                    for (int t = 0; t < 6; ++t) v.x[p_idx[t]] = ((mask >> t) & 1) ? 1 : -1;
                    push_if_compat(v);
                }
            }
        } while (std::next_permutation(sel.begin(), sel.end()));
    }

    // Shape 4: (1^10, 0^{d-10}) - only those where |v . v1| == 2!
    // Note v1 has support {0,1,2,3} with (2,2,1,1): dot product with v in {0,+-1}^d depends ONLY on v[0..3]!
    // So just check v[0..3] in {0,+-1}^4 giving |dp|==2, and fill remaining (10 - popcount) ones in 4..d-1!
    for (int m0 = 0; m0 < 81; ++m0) {
        int v04[4];
        int t = m0, nz = 0;
        for (int k = 0; k < 4; ++k) {
            int rem = t % 3; t /= 3;
            v04[k] = (rem == 0) ? 0 : (rem == 1 ? 1 : -1);
            if (v04[k] != 0) ++nz;
        }
        int dp = 2 * v04[0] + 2 * v04[1] + v04[2] + v04[3];
        if (dp != 2 && dp != -2) continue;
        int need = 10 - nz;
        if (need < 0 || need > d - 4) continue;
        std::vector<int> sel(d - 4, 0);
        std::fill(sel.end() - need, sel.end(), 1);
        do {
            int p_idx[10], c = 0;
            for (int k = 0; k < d - 4; ++k) if (sel[k]) p_idx[c++] = 4 + k;
            int total_masks = 1 << need;
            for (int mask = 0; mask < total_masks; ++mask) {
                Vec v{};
                for (int k = 0; k < 4; ++k) v.x[k] = v04[k];
                for (int k = 0; k < need; ++k) v.x[p_idx[k]] = ((mask >> k) & 1) ? 1 : -1;
                push_if_compat(v);
            }
        } while (std::next_permutation(sel.begin(), sel.end()));
    }

    return out;
}

static int greedy_plus_bk_clique(const std::vector<Vec>& pool, int d, std::mt19937_64& rng, std::vector<int>& out_clq) {
    int m = int(pool.size());
    out_clq.clear();
    if (m == 0) return 0;

    // Build adjacency using 64-bit bitsets
    int words = (m + 63) / 64;
    std::vector<uint64_t> adj(m * words, 0ULL);
    std::vector<int> deg(m, 0);
    for (int i = 0; i < m; ++i) {
        for (int j = i + 1; j < m; ++j) {
            int dp = dot_vec(pool[i], pool[j], d);
            if (dp == 2 || dp == -2) {
                adj[i * words + (j >> 6)] |= (1ULL << (j & 63));
                adj[j * words + (i >> 6)] |= (1ULL << (i & 63));
                ++deg[i];
                ++deg[j];
            }
        }
    }

    // If m <= 350, exact Bron-Kerbosch with time/node cap; else multi-start randomized greedy + 1-opt
    if (m <= 350) {
        std::vector<int> best;
        std::vector<int> P(m);
        std::iota(P.begin(), P.end(), 0);
        uint64_t nodes = 0;
        auto bk = [&](auto& self, std::vector<int>& R, std::vector<int> Pset) -> void {
            if (++nodes > 2000000ULL) return;
            if (R.size() + Pset.size() <= best.size()) return;
            if (Pset.empty()) {
                if (R.size() > best.size()) best = R;
                return;
            }
            int piv = Pset[0], md = -1;
            for (int u : Pset) {
                int c = 0;
                for (int v : Pset) if ((adj[u * words + (v >> 6)] >> (v & 63)) & 1) ++c;
                if (c > md) { md = c; piv = u; }
            }
            std::vector<int> cands;
            for (int v : Pset) if (!((adj[piv * words + (v >> 6)] >> (v & 63)) & 1)) cands.push_back(v);
            for (int v : cands) {
                R.push_back(v);
                std::vector<int> nP;
                for (int w : Pset) if ((adj[v * words + (w >> 6)] >> (w & 63)) & 1) nP.push_back(w);
                self(self, R, std::move(nP));
                R.pop_back();
                Pset.erase(std::remove(Pset.begin(), Pset.end(), v), Pset.end());
            }
        };
        std::vector<int> R;
        bk(bk, R, P);
        out_clq = std::move(best);
        return int(out_clq.size());
    }

    std::vector<int> best;
    std::vector<uint64_t> cands(words);
    for (int trial = 0; trial < 40; ++trial) {
        int start = (trial == 0) ? int(std::max_element(deg.begin(), deg.end()) - deg.begin()) : int(rng() % m);
        std::vector<int> clq = {start};
        for (int w = 0; w < words; ++w) cands[w] = adj[start * words + w];
        while (true) {
            std::vector<int> rem;
            for (int w = 0; w < words; ++w) {
                uint64_t x = cands[w];
                while (x) {
                    int b = __builtin_ctzll(x);
                    rem.push_back((w << 6) + b);
                    x &= x - 1;
                }
            }
            if (rem.empty()) break;
            int nxt = rem[rng() % rem.size()];
            if (trial < 10) {
                // Pick high-degree inside rem
                int best_u = rem[0], best_sc = -1;
                for (size_t idx = 0; idx < std::min<size_t>(rem.size(), 64); ++idx) {
                    int u = rem[(idx * 131 + trial) % rem.size()];
                    int sc = 0;
                    for (int w = 0; w < words; ++w) sc += __builtin_popcountll(adj[u * words + w] & cands[w]);
                    if (sc > best_sc) { best_sc = sc; best_u = u; }
                }
                nxt = best_u;
            }
            clq.push_back(nxt);
            for (int w = 0; w < words; ++w) cands[w] &= adj[nxt * words + w];
        }
        if (clq.size() > best.size()) best = std::move(clq);
    }
    out_clq = std::move(best);
    return int(out_clq.size());
}

int main(int argc, char** argv) {
    if (argc < 3) {
        std::cerr << "Usage: " << argv[0] << " <d> <num_chains> [threads=8] [seed=42]\n";
        return 1;
    }
    int d = std::stoi(argv[1]);
    int num_chains = std::stoi(argv[2]);
    int num_threads = (argc >= 4) ? std::stoi(argv[3]) : 8;
    uint64_t seed = (argc >= 5) ? std::stoull(argv[4]) : 42ULL;

    Vec v1{};
    v1.x[0] = 2; v1.x[1] = 2; v1.x[2] = 1; v1.x[3] = 1;
    auto L1 = generate_L1_for_2211(d, v1);
    std::cout << "d=" << d << " |L1(2,2,1,1)|=" << L1.size() << "\n";

    std::atomic<int> next_chain{0};
    std::atomic<int> best_total{0};
    std::mutex io_mtx;

    auto worker = [&](int tid) {
        std::mt19937_64 rng(seed + 999983ULL * uint64_t(tid + 1));
        std::vector<Vec> cur_pool;
        std::vector<Vec> nxt_pool;
        while (true) {
            int cid = next_chain.fetch_add(1);
            if (cid >= num_chains) break;

            // Random chain starting from v1
            std::vector<Vec> chain = {v1};
            // Filter from L1 first
            int target_k = (d == 18) ? 14 : 15;
            const std::vector<Vec>* src = &L1;
            cur_pool.clear();
            for (int step = 1; step < target_k; ++step) {
                if (src->empty()) break;
                Vec pick = (*src)[rng() % src->size()];
                chain.push_back(pick);
                nxt_pool.clear();
                for (const auto& v : *src) {
                    int dp = dot_vec(v, pick, d);
                    if (dp == 2 || dp == -2) nxt_pool.push_back(v);
                }
                cur_pool.swap(nxt_pool);
                src = &cur_pool;
                if (cur_pool.size() <= 300) break;
            }
            if (cur_pool.size() > 2500) continue;
            std::vector<int> clq;
            int k_clq = greedy_plus_bk_clique(cur_pool, d, rng, clq);
            int total = int(chain.size()) + k_clq;
            int prev = best_total.load();
            if (total > prev) {
                while (total > prev && !best_total.compare_exchange_weak(prev, total)) {}
                std::lock_guard<std::mutex> lk(io_mtx);
                std::cout << "[chain " << cid << "] pool=" << cur_pool.size()
                          << " chain=" << chain.size() << " + clq=" << k_clq
                          << " => total=" << total << "\n";
                if ((d == 18 && total >= 58) || (d == 19 && total >= 72)) {
                    std::cout << "FOUND_CANDIDATE d=" << d << " total=" << total << "\n";
                    for (const auto& v : chain) {
                        for (int i = 0; i < d; ++i) std::cout << (i ? " " : "") << int(v.x[i]);
                        std::cout << "\n";
                    }
                    for (int idx : clq) {
                        for (int i = 0; i < d; ++i) std::cout << (i ? " " : "") << int(cur_pool[idx].x[i]);
                        std::cout << "\n";
                    }
                    std::cout.flush();
                }
            }
        }
    };

    std::vector<std::thread> threads;
    for (int t = 0; t < num_threads; ++t) threads.emplace_back(worker, t);
    for (auto& th : threads) th.join();
    std::cout << "DONE d=" << d << " chains=" << num_chains << " best_total=" << best_total.load() << "\n";
    return 0;
}
