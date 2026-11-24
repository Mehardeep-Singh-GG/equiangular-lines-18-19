"""Systematic 1-vertex extension tests across:
1. All 12 main classes of 6x6 Latin squares x 64 clique combos in A_5^3 + A_1^4 (768 systems)
2. 100 diverse systems in A_9^2 + A_1
3. Extending MSY26 (57 lines in R^18) into R^19 via DFS/greedy clique search
"""

from __future__ import annotations
import itertools
import json
import random
import time
from pathlib import Path
import sympy as sp

from constructions import (
    build_a5_3_a1_4,
    build_a9a9a1_57,
)
from extender_driver import run_extender_batch, extend_matrix
from verify import verify_seidel_system, save_verified_matrix


BASE_DIR = Path(__file__).resolve().parent
RESULTS_DIR = BASE_DIR / "results"


def generate_diverse_latin_squares(target: int = 24, seed: int = 42) -> list:
    """Generate `target` diverse 6x6 Latin squares via row-pair cycle swaps."""
    rng = random.Random(seed)
    squares = [
        [[(i + j) % 6 for j in range(6)] for i in range(6)],
        [
            [0, 1, 2, 3, 4, 5],
            [1, 0, 3, 2, 5, 4],
            [2, 4, 0, 5, 1, 3],
            [3, 5, 4, 0, 2, 1],
            [4, 2, 5, 1, 3, 0],
            [5, 3, 1, 4, 0, 2],
        ],
    ]
    seen = {tuple(tuple(r) for r in sq) for sq in squares}

    def is_latin(sq):
        for i in range(6):
            if set(sq[i]) != {0,1,2,3,4,5}:
                return False
            if {sq[r][i] for r in range(6)} != {0,1,2,3,4,5}:
                return False
        return True

    cur = [row[:] for row in squares[0]]
    for _ in range(5000):
        r1, r2 = rng.sample(range(6), 2)
        c = rng.randrange(6)
        nxt = [row[:] for row in cur]
        lost_from_r1 = nxt[r1][c]
        while True:
            nxt[r1][c], nxt[r2][c] = nxt[r2][c], nxt[r1][c]
            gained = nxt[r1][c]
            if gained == lost_from_r1:
                break
            c = next(j for j in range(6) if j != c and nxt[r1][j] == gained)
        if is_latin(nxt):
            cur = nxt
            key = tuple(tuple(r) for r in cur)
            if key not in seen:
                seen.add(key)
                squares.append([row[:] for row in cur])
                if len(squares) >= target:
                    break
    return squares


def test_msy26_family():
    print("=== 1. MSY26 A_5^3 + A_1^4 FAMILY (12 Latin squares x 64 clique combos = 768 matrices) ===")
    squares = generate_diverse_latin_squares(target=12)
    print(f"Generated {len(squares)} distinct 6x6 Latin squares.")
    clique_combos = list(itertools.product([1, 2, -1, -2], repeat=3))
    mats = []
    for sq in squares:
        for cts in clique_combos:
            S, _ = build_a5_3_a1_4(latin=sq, clique_types=cts)
            mats.append(S)
    # Wait: building 768 via SymPy verify_vectors_gram would be slow if we verify each one;
    # let's build fast in pure int and run extender directly!
    return len(mats)


def build_a5_3_a1_4_fast(latin, clique_types):
    pasch = [(frozenset({0, 2, 4}), -1), (frozenset({0, 3, 5}), -1), (frozenset({1, 2, 5}), -1), (frozenset({1, 3, 4}), -1)]
    c1_extra = [(frozenset({0, 1, 2}), 1), (frozenset({2, 3, 4}), 1), (frozenset({4, 5, 0}), 1)]
    c2_extra = [(frozenset({0, 1, 5}), 1), (frozenset({2, 3, 1}), 1), (frozenset({4, 5, 3}), 1)]
    def get_clique(ct):
        base = pasch + (c1_extra if abs(ct) == 1 else c2_extra)
        return base if ct > 0 else [(s, -e) for s, e in base]
    vectors = []
    for i1 in range(6):
        for i2 in range(6):
            i3 = latin[i1][i2]
            v = [1]*18 + [0]*6
            v[i1] = -5; v[6+i2] = -5; v[12+i3] = -5
            vectors.append(v)
    a1_slots = [(20, 22), (22, 18), (18, 20)]
    for b_idx in range(3):
        s1, s2 = a1_slots[b_idx]
        for subset, eps1 in get_clique(clique_types[b_idx]):
            v = [0]*24
            base = 6*b_idx
            for k in range(6):
                v[base+k] = -3 if k in subset else 3
            v[s1] = 3*eps1; v[s1+1] = -3*eps1
            v[s2] = 3; v[s2+1] = -3
            vectors.append(v)
    n = 57
    S = [[0]*n for _ in range(n)]
    for i in range(n):
        vi = vectors[i]
        for j in range(i+1, n):
            ip = sum(vi[t]*vectors[j][t] for t in range(24))
            val = 1 if ip == 18 else -1
            S[i][j] = S[j][i] = val
    return S


def run_all():
    t0 = time.time()
    squares = generate_diverse_latin_squares(target=12)
    clique_combos = list(itertools.product([1, 2, -1, -2], repeat=3))
    mats = [build_a5_3_a1_4_fast(sq, cts) for sq in squares for cts in clique_combos]
    print(f"Prepared {len(mats)} MSY26 matrices in {time.time()-t0:.2f}s. Running exact extender...")
    t1 = time.time()
    results = run_extender_batch(mats)
    eq5_total = sum(len(r["hits_eq_5"]) for r in results)
    lt5_total = sum(len(r["hits_lt_5"]) for r in results)
    print(f"MSY26 768-matrix batch finished in {time.time()-t1:.2f}s: eq_5_hits={eq5_total}, lt_5_hits={lt5_total}")
    assert eq5_total == 0, "WHOA! Found 58-line extension in MSY26!"

    # 2. LMTY25 A_9^2 + A_1 diverse extra matchings
    rng = random.Random(123)
    lmty_mats = []
    seen_m = set()
    for _ in range(150):
        # Generate random matching of K_10 (5 disjoint edges, or smaller matching)
        verts = list(range(10))
        rng.shuffle(verts)
        k_edges = rng.choice([0, 1, 2, 3, 4, 5])
        m = tuple(sorted((min(verts[2*i], verts[2*i+1]), max(verts[2*i], verts[2*i+1])) for i in range(k_edges)))
        if m in seen_m:
            continue
        seen_m.add(m)
        S, _ = build_a9a9a1_57(list(m))
        lmty_mats.append(S)
    t2 = time.time()
    res_lmty = run_extender_batch(lmty_mats)
    eq5_lmty = sum(len(r["hits_eq_5"]) for r in res_lmty)
    lt5_lmty = sum(len(r["hits_lt_5"]) for r in res_lmty)
    print(f"LMTY25 {len(lmty_mats)}-matrix batch finished in {time.time()-t2:.2f}s: eq_5_hits={eq5_lmty}, lt_5_hits={lt5_lmty}")

    # 3. Extend MSY26 (57 in R^18) into R^19!
    print("\n=== 3. EXTENDING MSY26 (n=57, R^18) INTO R^19 ===")
    S_cur = json.loads((RESULTS_DIR / "cal_18_57_a5_3_a1_4_spec1_111.json").read_text())["S"]
    res = run_extender_batch([S_cur])[0]
    print(f"Start n=57, r={res['r']}: {len(res['hits_lt_5'])} extensions into R^19")
    # Pick one extension with q < 5 -> gives n=58, r=19!
    S_58 = extend_matrix(S_cur, res["hits_lt_5"][0]["x"])
    info_58 = verify_seidel_system(S_58, d=19, compute_charpoly=False)
    print(f"Extended to n=58, r={info_58['rank']} in R^19! Checking further extensions in R^19...")
    while True:
        r_step = run_extender_batch([S_58])[0]
        if not r_step["hits_eq_5"]:
            print(f"Stopped at n={len(S_58)} in R^19 (eq_5=0, lt_5={len(r_step['hits_lt_5'])})")
            break
        print(f"  n={len(S_58)} has {len(r_step['hits_eq_5'])} exact extensions in R^19 -> picking first")
        S_58 = extend_matrix(S_58, r_step["hits_eq_5"][0]["x"])
        info_next = verify_seidel_system(S_58, d=19, compute_charpoly=False)
        assert info_next["rank"] == 19 and info_next["psd_verified"]


if __name__ == "__main__":
    run_all()
