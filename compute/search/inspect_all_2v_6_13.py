"""Compute all 2v-Jacobi pairs on active cones of idx=6 ({0,2,4,8}) and idx=13 ({0,1,2,5}),
and check Stage-3 linear feasibility around each active vertex class!
"""
from __future__ import annotations
import json
import math
from pathlib import Path
import sympy as sp
from ortools.sat.python import cp_model

from attack_861_and_47 import load_candidate, reconstruct_polys_x
from audit_861_and_47_proofs import brute_2v_jacobi

x = sp.Symbol("x")


def analyze_candidate(idx: int, active_classes: list[int], stage2_sols: list[dict[int, int]]):
    print(f"\n==========================================")
    print(f"ANALYZING (19, 74) idx={idx}, classes={active_classes}")
    print(f"==========================================")
    d, n, c, cand = load_candidate("deck_19_74.json", idx)
    chi_S, f_x, Gcd_x, H_x, quo_x, deck_x = reconstruct_polys_x(d, n, c, cand)
    Gcd_2 = sp.gcd(Gcd_x, Gcd_x.diff())

    pair_sols = {}
    for a_idx, i in enumerate(active_classes):
        for j in active_classes[a_idx:]:
            sols = brute_2v_jacobi(chi_S, Gcd_x, H_x, deck_x[i][0], deck_x[j][0], n, 18, x)
            s_ratios = sorted(set((sd["s_uv"], sd["S2_uv"]) for sd in sols))
            print(f"  Pair ({i},{j}): {len(sols)} sols, (s, S2)={s_ratios}")
            pair_sols[(i, j)] = sols
            pair_sols[(j, i)] = sols

    # For each vertex class u_cls in active_classes, check Stage-3 linear feasibility!
    for u_cls in active_classes:
        g_u, chi_u = deck_x[u_cls]
        Gcd_u = sp.gcd(chi_u, chi_u.diff())
        H_u, _ = sp.div(chi_u, Gcd_u)
        quo_u, rem_u = sp.div(chi_u.diff(), Gcd_u)
        assert rem_u.is_zero
        s_u = H_u.degree()
        rhs_u = [int(v) for v in quo_u.all_coeffs()]
        rhs_u = [0] * (s_u - len(rhs_u)) + rhs_u

        # Build g_{u,v} columns
        items = []
        for j in active_classes:
            for sd in pair_sols[(u_cls, j)]:
                q_poly = sp.Poly(sp.sympify(sd["q_uv"]), x, domain=sp.ZZ)
                chi_uv = Gcd_2 * q_poly
                g_uv, rem = sp.div(chi_uv, Gcd_u)
                assert rem.is_zero
                cs = [int(v) for v in g_uv.all_coeffs()]
                cs = [0] * (s_u - len(cs)) + cs
                items.append((j, sd["s_uv"], sd["S2_uv"], cs))

        surviving_s2 = []
        for sol2 in stage2_sols:
            if sol2.get(u_cls, 0) == 0:
                continue
            model = cp_model.CpModel()
            mv = [model.NewIntVar(0, n - 1, f"m_{k}") for k in range(len(items))]
            for j in active_classes:
                cnt = sol2.get(j, 0) - (1 if j == u_cls else 0)
                model.Add(sum(mv[k] for k, it in enumerate(items) if it[0] == j) == cnt)
            for r in range(s_u):
                model.Add(sum(items[k][3][r] * mv[k] for k in range(len(items))) == rhs_u[r])
            solver = cp_model.CpSolver()
            status = solver.Solve(model)
            if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
                surviving_s2.append(sol2)
        print(f"  Stage-3 at u in deck[{u_cls}] (H_u={sp.factor(H_u.as_expr())}): {len(surviving_s2)}/{sum(1 for s in stage2_sols if s.get(u_cls,0)>0)} Stage-2 sols feasible")


def main():
    # idx=6: cone [2, 0, 4, 8] -> 5 sols t=0..4
    sols6 = [{0: 20 - t, 2: 42 + 3 * t, 4: 12 - 3 * t, 8: t} for t in range(5)]
    analyze_candidate(6, [0, 2, 4, 8], sols6)

    # idx=13: cone [0, 1, 2, 5] -> solve Stage-2 with E11 filters
    d, n, c, cand13 = load_candidate("deck_19_74.json", 13)
    chi_S, f_x, Gcd_x, H_x, quo_x, deck_x = reconstruct_polys_x(d, n, c, cand13)
    s = H_x.degree()
    rhs = [int(v) for v in quo_x.all_coeffs()]
    rhs = [0] * (s - len(rhs)) + rhs
    cols = []
    for i in (0, 1, 2, 5):
        cs = [int(v) for v in deck_x[i][0].all_coeffs()]
        cs = [0] * (s - len(cs)) + cs
        cols.append(cs)
    model = cp_model.CpModel()
    vars13 = [model.NewIntVar(0, n, f"n_{i}") for i in (0, 1, 2, 5)]
    model.Add(sum(vars13) == n)
    for r in range(s):
        model.Add(sum(cols[k][r] * vars13[k] for k in range(4)) == rhs[r])
    sols13_raw = []
    class Col(cp_model.CpSolverSolutionCallback):
        def on_solution_callback(self):
            sols13_raw.append([self.Value(v) for v in vars13])
    solver = cp_model.CpSolver()
    solver.parameters.enumerate_all_solutions = True
    solver.Solve(model, Col())
    print(f"\nidx=13 cone [0,1,2,5] Stage-2 sols: {len(sols13_raw)}")
    sols13 = []
    for c0, c1, c2, c5 in sols13_raw:
        if c5 <= 2 and math.ceil(c0 / 32) + math.ceil(c1 / 24) <= 3:
            sols13.append({0: c0, 1: c1, 2: c2, 5: c5})
    print(f"idx=13 after E11 filter: {len(sols13)} sols: {sols13}")
    analyze_candidate(13, [0, 1, 2, 5], sols13)


if __name__ == "__main__":
    main()
