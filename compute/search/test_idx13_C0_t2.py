"""Check C_0 (24-clique) feasibility for S1 t1=2 ([4,12], [8,8]) with EXACT constraints:
  sum_{u in C_0} v_u^2 <= 20  (i.e. sum q_u >= 176),
  sum_{u in C_0} v_u = 0,
  W_{00} * 1 = 7 * 1 (15 +1s and 8 -1s per vertex in C_0),
  AND check compatibility of any found W_{00} (Spec(W_{00} | 1^perp) subset [-5, 15], mult(-5) >= 8)!
"""
from __future__ import annotations
import numpy as np
from ortools.sat.python import cp_model
from test_idx13_S1_S2_S3_cycles import cycle_union_adj, zero_sum_vecs_on_parts


def check_C0_t2(parts):
    print(f"\n=== Checking C_0 24-clique for p1={parts} ===")
    A1 = cycle_union_adj(parts).astype(np.float64)
    ev1, evec1 = np.linalg.eigh(2.0 * np.eye(16) - A1)
    nz1 = np.where(ev1 > 1e-8)[0]
    P1 = (evec1[:, nz1] / ev1[nz1]) @ evec1[:, nz1].T

    B_cand = zero_sum_vecs_on_parts(parts)
    qvals = np.sum((B_cand @ P1) * B_cand, axis=1)
    idx9 = np.where(qvals <= 9.0 + 1e-7)[0]
    B_ok = B_cand[idx9]
    q_ok = qvals[idx9]
    v_mag = np.sqrt(np.maximum(0.0, (9.0 - q_ok) / 2.0))
    G = B_ok @ P1 @ B_ok.T

    nodes_v = []; nodes_b = []
    for i in range(len(idx9)):
        if v_mag[i] < 1e-6:
            nodes_v.append(0.0); nodes_b.append(i)
        else:
            nodes_v.append(+v_mag[i]); nodes_b.append(i)
            nodes_v.append(-v_mag[i]); nodes_b.append(i)
    nodes_v = np.array(nodes_v); nodes_b = np.array(nodes_b)
    G_full = G[np.ix_(nodes_b, nodes_b)] + 2.0 * np.outer(nodes_v, nodes_v)
    is_p1 = np.abs(G_full - 1.0) < 1e-6
    is_m3 = np.abs(G_full + 3.0) < 1e-6
    np.fill_diagonal(is_p1, False); np.fill_diagonal(is_m3, False)

    alive = np.ones(len(nodes_v), dtype=bool)
    while True:
        dp = is_p1[np.ix_(alive, alive)].sum(axis=1)
        dm = is_m3[np.ix_(alive, alive)].sum(axis=1)
        bad = (dp < 15) | (dm < 8)
        if not np.any(bad): break
        ia = np.where(alive)[0]
        alive[ia[bad]] = False
        if alive.sum() == 0: break
    print(f"  Surviving (15p1, 8m3)-core: {alive.sum()} / {len(nodes_v)}")
    if alive.sum() < 24:
        return
    ia = np.where(alive)[0]
    sub_p1 = is_p1[np.ix_(ia, ia)]
    sub_m3 = is_m3[np.ix_(ia, ia)]
    m = len(ia)
    print("  Unique qvals in core:", np.unique(np.round(q_ok[nodes_b[ia]], 4)))
    print("  Unique |v_u|^2 in core:", np.unique(np.round(nodes_v[ia]**2, 4)))
    # Note: for [8, 8], v_u^2 in {0.5, 0.75, 1.0, 1.5, 1.75, 2.5}! Wait: v_u = +-sqrt(...) must sum to 0!
    # Notice irrational v_u's (sqrt(0.5), sqrt(0.75), sqrt(1.5), sqrt(1.75), sqrt(2.5)) can only cancel within their own square-free class,
    # AND sum_{u} v_u^2 <= 20 => sum (9 - q_u) <= 40 => sum q_u >= 176!
    model = cp_model.CpModel()
    xv = [model.NewBoolVar(f"x_{k}") for k in range(m)]
    model.Add(sum(xv) == 24)
    # sum 24*v_u^2 <= 24*20
    v2_24 = [int(round(24 * (nodes_v[ia[k]] ** 2))) for k in range(m)]
    model.Add(sum(v2_24[k] * xv[k] for k in range(m)) <= 20 * 24)
    # Also sum v_u == 0 grouped by sqrt(sqfree) class!
    import math
    # Quantize v_u^2 * 48 to int, find squarefree part
    classes = {}
    for k in range(m):
        v = nodes_v[ia[k]]
        if abs(v) < 1e-6: continue
        val48 = int(round(48 * v * v))
        # Factor out square
        sf = 1
        rem = val48
        d = 2
        while d * d <= rem:
            cnt = 0
            while rem % d == 0:
                rem //= d; cnt += 1
            if cnt % 2 == 1: sf *= d
            d += 1
        if rem > 1: sf *= rem
        mult = int(round(math.sqrt(val48 / sf)))
        if v < 0: mult = -mult
        classes.setdefault(sf, []).append((k, mult))
    for sf, terms in classes.items():
        model.Add(sum(c * xv[k] for k, c in terms) == 0)

    # Compatibility + (15 p1, 8 m3) degrees
    for i in range(m):
        for j in range(i + 1, m):
            if not (sub_p1[i, j] or sub_m3[i, j]):
                model.Add(xv[i] + xv[j] <= 1)
        p1_nb = [xv[j] for j in range(m) if sub_p1[i, j]]
        m3_nb = [xv[j] for j in range(m) if sub_m3[i, j]]
        model.Add(sum(p1_nb) >= 15 - 24 * (1 - xv[i]))
        model.Add(sum(p1_nb) <= 15 + 24 * (1 - xv[i]))
        model.Add(sum(m3_nb) >= 8 - 24 * (1 - xv[i]))
        model.Add(sum(m3_nb) <= 8 + 24 * (1 - xv[i]))

    sv = cp_model.CpSolver()
    sv.parameters.max_time_in_seconds = 15.0
    st = sv.Solve(model)
    print(f"  CP-SAT C_0 24-clique status: {sv.StatusName(st)}")
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        sel = [ia[k] for k in range(m) if sv.Value(xv[k])]
        B1_24 = B_ok[nodes_b[sel]].T  # 16 x 24
        W00 = np.where(is_p1[np.ix_(sel, sel)], 1, np.where(is_m3[np.ix_(sel, sel)], -1, 0))
        ev_w = np.sort(np.linalg.eigvalsh(W00.astype(float)))
        print("  FOUND W00!! Spec(W00) =", np.round(ev_w, 4))
        print("  ||v||^2 =", np.sum(nodes_v[sel]**2))


if __name__ == "__main__":
    check_C0_t2([4, 12])
    check_C0_t2([8, 8])
