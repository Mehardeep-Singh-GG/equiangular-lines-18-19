"""Explore extending MSY26 (A_5^3 + A_1^4, 57 lines in R^18) and Netto/MSY26 (48 in R^17)
into R^19 and R^18 respectively using exact 1-vertex extension + max-clique.
"""

from __future__ import annotations
import json
from pathlib import Path
import sympy as sp

from extender_driver import prepare_query, run_extender_batch, extend_matrix
from verify import verify_seidel_system


BASE_DIR = Path(__file__).resolve().parent
RESULTS_DIR = BASE_DIR / "results"


def max_clique_on_cands(S: list, hits: list, B: list, G_BB_inv: sp.Matrix) -> tuple[int, list]:
    """Given S of rank d and exact hits with q=5, build compatibility graph and find max clique."""
    if not hits:
        return 0, []
    m = len(hits)
    # Build exact inner products xB_i^T G_BB_inv xB_j
    M = G_BB_inv
    xBs = [sp.Matrix(h["xB"]) for h in hits]
    M_xBs = [M * xb for xb in xBs]
    adj = [[False] * m for _ in range(m)]
    for i in range(m):
        for j in range(i + 1, m):
            ip = (xBs[i].T * M_xBs[j])[0, 0]
            if ip == 1 or ip == -1:
                adj[i][j] = adj[j][i] = True

    best = []
    def bk(R, P):
        nonlocal best
        if len(R) + len(P) <= len(best):
            return
        if not P:
            if len(R) > len(best):
                best = list(R)
            return
        # Pivot
        u = max(P, key=lambda v: sum(1 for w in P if adj[v][w]))
        cands = [v for v in P if not adj[u][v]]
        P_cur = list(P)
        for v in cands:
            bk(R + [v], [w for w in P_cur if adj[v][w]])
            P_cur.remove(v)

    bk([], list(range(m)))
    return len(best), best


def explore_msy26_to_19():
    for name in ["cal_18_57_a5_3_a1_4_spec1_111.json", "cal_18_57_a5_3_a1_4_spec2_11m1.json"]:
        data = json.loads((RESULTS_DIR / name).read_text())
        S57 = data["S"]
        r57 = run_extender_batch([S57])[0]
        print(f"\n=== {data['name']} -> R^19 ===")
        print(f"57-line lt_5 hits: {len(r57['hits_lt_5'])}")
        best_n = 57
        # Test each of the 18 initial R^19 lifts (up to sign, actually each lift gives a 58-line rank-19 system)
        # Note: how many distinct S58 up to switching/isometry? Let's test all 18 (takes ~0.5s total for 18 batch runs!)
        s58_list = [extend_matrix(S57, h["x"]) for h in r57["hits_lt_5"]]
        r58_list = run_extender_batch(s58_list)
        for idx, (s58, r58) in enumerate(zip(s58_list, r58_list)):
            omega, clq = max_clique_on_cands(s58, r58["hits_eq_5"], r58["B"], r58["G_BB_inv"])
            total_n = 58 + omega
            if total_n > best_n:
                best_n = total_n
            if idx < 5 or total_n >= 70:
                print(f"  lift[{idx:2d}] q={r57['hits_lt_5'][idx]['q']}/{r57['L']}: S58 has {len(r58['hits_eq_5'])} eq_5 cands -> max_clique={omega} -> total_n={total_n}")
        print(f"Best total_n in R^19 from {data['name']}: {best_n}")


def explore_48_to_18():
    data = json.loads((RESULTS_DIR / "cal_17_48_a5_3_a1_4.json").read_text())
    S48 = data["S"]
    r48 = run_extender_batch([S48])[0]
    print(f"\n=== {data['name']} (48 in R^17) -> R^18 ===")
    print(f"48-line lt_5 hits: {len(r48['hits_lt_5'])}")
    s49_list = [extend_matrix(S48, h["x"]) for h in r48["hits_lt_5"][:6]]
    r49_list = run_extender_batch(s49_list)
    for idx, (s49, r49) in enumerate(zip(s49_list, r49_list)):
        omega, _ = max_clique_on_cands(s49, r49["hits_eq_5"], r49["B"], r49["G_BB_inv"])
        print(f"  lift[{idx}] q={r48['hits_lt_5'][idx]['q']}/{r48['L']}: S49 has {len(r49['hits_eq_5'])} eq_5 cands -> max_clique={omega} -> total_n={49 + omega}")


if __name__ == "__main__":
    explore_msy26_to_19()
    explore_48_to_18()
