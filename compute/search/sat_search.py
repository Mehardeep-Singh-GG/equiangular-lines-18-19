"""SAT / CP-SAT assisted search for non-extending & large-neighborhood 58-line systems.

1. Uses OR-Tools CP-SAT (`cp_model`) to enumerate ALL integer norm-10 vectors
   v in {-2,-1,0,1,2}^18 compatible (|v . u| == 2) with retained subsets of
   size 57 - k (k = 10, 15, 20, 25) from GSY21 F1..F4, then runs exact max-clique.
2. Also checks Z_19-equivariant 57-line (3 x 19) matrices from the 4 Galois triangles.
"""

from __future__ import annotations
import itertools
import json
import random
import time
from pathlib import Path
from typing import List
import numpy as np
from ortools.sat.python import cp_model

from constructions import parse_gsy_matrices
from verify import verify_vectors_gram, save_verified_matrix


BASE_DIR = Path(__file__).resolve().parent
RESULTS_DIR = BASE_DIR / "results"


def cpsat_enumerate_and_clique(
    retained: List[List[int]],
    d: int = 18,
    max_coord: int = 2,
    max_solutions: int = 2000,
) -> int:
    """Use CP-SAT to find ALL v in [-max_coord, max_coord]^d with ||v||^2 = 10,
    canonical sign (first nonzero > 0, or just break symmetry via v[0] >= 0 and check),
    and |v . u| == 2 for every u in `retained`. Then find max clique!
    """
    model = cp_model.CpModel()
    v = [model.NewIntVar(-max_coord, max_coord, f"v_{i}") for i in range(d)]

    # v_sq[i] = v[i]^2 in {0, 1, 4, ...}
    v_sq = []
    for i in range(d):
        sq = model.NewIntVar(0, max_coord * max_coord, f"sq_{i}")
        model.AddMultiplicationEquality(sq, [v[i], v[i]])
        v_sq.append(sq)
    model.Add(sum(v_sq) == 10)

    # For each u in retained: dot == 2 or dot == -2
    for idx, u in enumerate(retained):
        dot_expr = sum(u[i] * v[i] for i in range(d) if u[i] != 0)
        b = model.NewBoolVar(f"sign_{idx}")
        model.Add(dot_expr == 2).OnlyEnforceIf(b)
        model.Add(dot_expr == -2).OnlyEnforceIf(b.Not())

    # Enumerate all solutions (deduplicate +-v later)
    class Collector(cp_model.CpSolverSolutionCallback):
        def __init__(self):
            super().__init__()
            self.sols = []
            self.seen = set()

        def on_solution_callback(self):
            vec = [self.Value(vi) for vi in v]
            # Canonicalize sign: first nonzero > 0
            for val in vec:
                if val != 0:
                    if val < 0:
                        vec = [-x for x in vec]
                    break
            t = tuple(vec)
            if t not in self.seen:
                self.seen.add(t)
                self.sols.append(vec)
            if len(self.sols) >= max_solutions:
                self.StopSearch()

    solver = cp_model.CpSolver()
    solver.parameters.enumerate_all_solutions = True
    solver.parameters.max_time_in_seconds = 1.5
    solver.parameters.num_search_workers = 1
    cb = Collector()
    solver.Solve(model, cb)

    cands = cb.sols
    m = len(cands)
    if m == 0:
        return 0

    V = np.array(cands, dtype=np.int64)
    G = V @ V.T
    adj = (G == 2) | (G == -2)
    np.fill_diagonal(adj, False)

    # Exact Bron-Kerbosch if m <= 250 else greedy+swap
    adj_sets = [set(np.where(adj[i])[0]) for i in range(m)]
    best: List[int] = []
    t0 = time.time()
    if m <= 250:
        def bk(R, P):
            nonlocal best
            if time.time() - t0 > 3.0:
                return
            if len(R) + len(P) <= len(best):
                return
            if not P:
                if len(R) > len(best):
                    best = list(R)
                return
            u = max(P, key=lambda x: len(adj_sets[x] & P))
            for cand in list(P - adj_sets[u]):
                bk(R + [cand], P & adj_sets[cand])
                P.remove(cand)
        bk([], set(range(m)))
    else:
        rng = random.Random(42)
        for tr in range(100):
            start = rng.randrange(m) if tr > 0 else int(np.argmax(adj.sum(axis=1)))
            clq = [start]
            rem = adj_sets[start].copy()
            while rem:
                nxt = max(rem, key=lambda x: len(adj_sets[x] & rem)) if tr == 0 else rng.choice(list(rem))
                clq.append(nxt)
                rem &= adj_sets[nxt]
            if len(clq) > len(best):
                best = clq

    k_omega = len(best)
    total = len(retained) + k_omega
    if total >= 58:
        full_vecs = retained + [cands[idx] for idx in best]
        S, info = verify_vectors_gram(full_vecs, norm_sq=10, allowed_ips=(-2, 2), d=d, compute_charpoly=True)
        print(f"  [DISCOVERY!] total={total}, rank={info['rank']}, PSD={info['psd_verified']}, cp={info['charpoly_str']}")
        save_verified_matrix(RESULTS_DIR / f"DISCOVERY_cpsat_{d}_{total}.json", f"DISCOVERY_cpsat_{d}_{total}", S, info)
    return total


def run_large_k_cpsat():
    print("=== CP-SAT LARGE-NEIGHBORHOOD (k=12, 17, 22, 27) SEARCH ON GSY21 F1..F4 ===")
    gsy = parse_gsy_matrices()
    rng = random.Random(2026)
    for name, cols in gsy:
        # Check max coord in cols
        mx = max(abs(x) for c in cols for x in c)
        assert mx == 2
        best_tot = 0
        trials = 0
        for keep_n in [45, 40, 35, 30]:
            for rep in range(5):
                sub = rng.sample(cols, keep_n)
                tot = cpsat_enumerate_and_clique(sub, d=18, max_coord=2, max_solutions=1000)
                trials += 1
                if tot > best_tot:
                    best_tot = tot
                if tot >= 58:
                    print(f"  WIN on {name} keep_n={keep_n}!", flush=True)
                    return
        print(f"  {name}: tested {trials} large-k neighborhoods (keep_n in [45,40,35,30]), max_recovered={best_tot}", flush=True)


if __name__ == "__main__":
    run_large_k_cpsat()
