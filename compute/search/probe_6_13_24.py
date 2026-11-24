"""Probe remaining (19, 74) survivors idx=6, idx=13, idx=24 in exact integer/QQ arithmetic."""
from __future__ import annotations
import json
import math
from pathlib import Path
import sympy as sp

from attack_861_and_47 import load_candidate, reconstruct_polys_x
from audit_861_and_47_proofs import brute_2v_jacobi

x = sp.Symbol("x")


def solve_stage2(d: int, n: int, c_shift: int, cand: dict):
    chi_S, f_x, Gcd_x, H_x, quo_x, deck_x = reconstruct_polys_x(d, n, c_shift, cand)
    s = H_x.degree()
    m = len(deck_x)
    # Solve sum_i n_i g_i(x) = quo_x(x) with n_i >= 0, sum n_i = n
    # using SymPy ILP or exact RREF + bounded search
    cols = []
    for gv, _ in deck_x:
        cs = [int(c) for c in gv.all_coeffs()]
        cs = [0] * (s - len(cs)) + cs
        cols.append(cs)
    rhs = [int(c) for c in quo_x.all_coeffs()]
    rhs = [0] * (s - len(rhs)) + rhs

    # Note: let's use exact SymPy RREF + recursive branch-and-bound on free vars, or OR-Tools CP-SAT verified in ZZ
    from ortools.sat.python import cp_model
    model = cp_model.CpModel()
    vars_n = [model.NewIntVar(0, n, f"n_{i}") for i in range(m)]
    model.Add(sum(vars_n) == n)
    for r in range(s):
        model.Add(sum(cols[i][r] * vars_n[i] for i in range(m)) == rhs[r])

    sols = []
    class Collect(cp_model.CpSolverSolutionCallback):
        def __init__(self):
            super().__init__()
        def on_solution_callback(self):
            sol = tuple(self.Value(v) for v in vars_n)
            # Exact integer check
            assert sum(sol) == n
            for r in range(s):
                assert sum(cols[i][r] * sol[i] for i in range(m)) == rhs[r]
            sols.append(sol)

    solver = cp_model.CpSolver()
    solver.parameters.enumerate_all_solutions = True
    status = solver.Solve(model, Collect())
    assert status in (cp_model.OPTIMAL, cp_model.INFEASIBLE)
    return chi_S, f_x, Gcd_x, H_x, quo_x, deck_x, sorted(sols)


def check_idx6_stage3():
    print("==========================================")
    print("PROBING (19, 74) idx=6 Stage-3 around u in deck[0]")
    print("==========================================")
    d, n, c, cand = load_candidate("deck_19_74.json", 6)
    chi_S, f_x, Gcd_x, H_x, quo_x, deck_x, sols2 = solve_stage2(d, n, c, cand)
    print(f"Stage-2 solutions ({len(sols2)}):")
    for sol in sols2:
        nz = [(i, v) for i, v in enumerate(sol) if v > 0]
        print(" ", nz)

    # Filter to cone [2, 0, 4, 8] (we already proved [2, 1, 6] has 0 2v-Jacobi sols on (1,2))
    g0, chi_0 = deck_x[0]
    Gcd_0 = sp.gcd(chi_0, chi_0.diff())
    H_0, _ = sp.div(chi_0, Gcd_0)
    quo_0, rem_0 = sp.div(chi_0.diff(), Gcd_0)
    assert rem_0.is_zero
    print("chi_0 =", sp.factor(chi_0.as_expr()))
    print("H_0   =", sp.factor(H_0.as_expr()))
    print("Gcd_0 =", sp.factor(Gcd_0.as_expr()))
    print("H_0'(9) =", H_0.diff().eval(9), "H_0'(12) =", H_0.diff().eval(12))

    # Compute exact 2v-Jacobi sols for (0, j) j in {0, 2, 4, 8}
    Gcd_2 = sp.gcd(Gcd_x, Gcd_x.diff())
    all_2v = {}
    for j in (0, 2, 4, 8):
        sols_0j = brute_2v_jacobi(chi_S, Gcd_x, H_x, deck_x[0][0], deck_x[j][0], n, 18, x)
        print(f"Pair (0, {j}): {len(sols_0j)} 2v-Jacobi sols")
        # chi_{S_{u,v}} = Gcd_2 * q_uv = Gcd_0 * g_{u,v}
        g_list = []
        for sd in sols_0j:
            q_poly = sp.Poly(sp.sympify(sd["q_uv"]), x, domain=sp.ZZ)
            chi_uv = Gcd_2 * q_poly
            g_uv, rem = sp.div(chi_uv, Gcd_0)
            assert rem.is_zero
            # Check value at 9 and 12
            v9 = int(g_uv.eval(9))
            v12 = int(g_uv.eval(12))
            e9 = sp.Rational(v9, int(quo_0.eval(9)))
            e12 = sp.Rational(v12, int(quo_0.eval(12)))
            print(f"  s={sd['s_uv']:+d} S2={sd['S2_uv']:+3d} E9[w,w]={e9} E12[w,w]={e12}")
            g_list.append((j, sd["s_uv"], sd["S2_uv"], e9, e12, g_uv))
        all_2v[j] = g_list

    # Now check Stage-3 linear feasibility around u in C_0 for t=0..4!
    from ortools.sat.python import cp_model
    s0 = H_0.degree()
    rhs0 = [int(c) for c in quo_0.all_coeffs()]
    rhs0 = [0] * (s0 - len(rhs0)) + rhs0

    items = [item for j in (0, 2, 4, 8) for item in all_2v[j]]
    cols0 = []
    for (_, _, _, _, _, g_uv) in items:
        cs = [int(c) for c in g_uv.all_coeffs()]
        cs = [0] * (s0 - len(cs)) + cs
        cols0.append(cs)

    for t in range(5):
        targets = {0: 20 - t - 1, 2: 42 + 3 * t, 4: 12 - 3 * t, 8: t}
        model = cp_model.CpModel()
        m_vars = [model.NewIntVar(0, 73, f"m_{k}") for k in range(len(items))]
        for j, cnt in targets.items():
            model.Add(sum(m_vars[k] for k, it in enumerate(items) if it[0] == j) == cnt)
        for r in range(s0):
            model.Add(sum(cols0[k][r] * m_vars[k] for k in range(len(items))) == rhs0[r])
        sols_t = []
        class Col(cp_model.CpSolverSolutionCallback):
            def on_solution_callback(self):
                sols_t.append(tuple(self.Value(v) for v in m_vars))
        solver = cp_model.CpSolver()
        solver.parameters.enumerate_all_solutions = True
        solver.Solve(model, Col())
        print(f"  idx=6 t={t} ({targets}): Stage-3 linear sols at u in C_0 = {len(sols_t)}")
        for sol in sols_t[:5]:
            desc = [(items[k][0], items[k][1], items[k][2], str(items[k][3]), sol[k]) for k in range(len(items)) if sol[k] > 0]
            print("    ", desc)


def check_idx13_and_idx24():
    print("\n==========================================")
    print("PROBING (19, 74) idx=13")
    print("==========================================")
    d, n, c, cand = load_candidate("deck_19_74.json", 13)
    chi_S, f_x, Gcd_x, H_x, quo_x, deck_x, sols2 = solve_stage2(d, n, c, cand)
    print(f"idx=13 Stage-2 solutions ({len(sols2)})")
    # Filter by t<=2 and rank(U0)+rank(U1) <= 3
    surv13 = [s for s in sols2 if s[5] <= 2 and math.ceil(s[0]/32) + math.ceil(s[1]/24) <= 3]
    print(f"idx=13 after E11 bounds: {len(surv13)}")
    for s in surv13:
        print(" ", [(i, v) for i, v in enumerate(s) if v > 0])

    print("\n==========================================")
    print("PROBING (19, 74) idx=24")
    print("==========================================")
    d, n, c, cand = load_candidate("deck_19_74.json", 24)
    chi_S, f_x, Gcd_x, H_x, quo_x, deck_x, sols2 = solve_stage2(d, n, c, cand)
    print(f"idx=24 Stage-2 solutions ({len(sols2)}):")
    for s in sols2:
        print(" ", [(i, v) for i, v in enumerate(s) if v > 0])
    # Exact E_{14 +- sqrt(5)} diagonals on idx=24
    fac = sp.Poly(x**2 - 28*x + 191, x, domain=sp.ZZ)
    num_base, _ = sp.div(chi_S, fac**3)
    denom_poly = sp.Poly((num_base * fac.diff()).as_expr(), x, domain=sp.QQ)
    inv_d = sp.invert(denom_poly, sp.Poly(fac.as_expr(), x, domain=sp.QQ))
    r = sp.Symbol("r")
    print("Exact E_{14+-sqrt(5)} diagonals:")
    for i, (_, chiv) in enumerate(deck_x):
        q, rem = sp.div(chiv, fac**2)
        assert rem.is_zero
        rem_f = sp.rem(sp.Poly(q.as_expr(), x, domain=sp.QQ) * inv_d, sp.Poly(fac.as_expr(), x, domain=sp.QQ))
        c1 = rem_f.coeff_monomial(x) if rem_f.degree() >= 1 else sp.Integer(0)
        c0 = rem_f.eval(0)
        val_p = sp.simplify(c0 + c1*(14 + sp.sqrt(5)))
        val_m = sp.simplify(c0 + c1*(14 - sp.sqrt(5)))
        print(f"  deck[{i}]: +: {val_p} (~{float(val_p):.6f}), -: {val_m} (~{float(val_m):.6f}), sum={sp.simplify(val_p+val_m)}")


if __name__ == "__main__":
    check_idx6_stage3()
    check_idx13_and_idx24()
