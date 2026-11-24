"""Inspect Stage-3 solutions, Galois/M_blk/E9/E12 on the 3 survivors of idx=13,
and inspect the 4 solutions of idx=24 (plus Stage-3 / Prop 6.1 on idx=24).
"""
from __future__ import annotations
import sympy as sp
from ortools.sat.python import cp_model

from attack_861_and_47 import load_candidate, reconstruct_polys_x
from audit_861_and_47_proofs import brute_2v_jacobi

x = sp.Symbol("x")


def inspect_idx13_survivors():
    print("=== IDX=13 3 STAGE-3 SURVIVORS DEEP DIVE ===")
    d, n, c, cand = load_candidate("deck_19_74.json", 13)
    chi_S, f_x, Gcd_x, H_x, quo_x, deck_x = reconstruct_polys_x(d, n, c, cand)
    Gcd_2 = sp.gcd(Gcd_x, Gcd_x.diff())
    active = [0, 1, 2, 5]
    pair_sols = {}
    for ai, i in enumerate(active):
        for j in active[ai:]:
            pair_sols[(i, j)] = pair_sols[(j, i)] = brute_2v_jacobi(
                chi_S, Gcd_x, H_x, deck_x[i][0], deck_x[j][0], n, 18, x
            )

    survs = [
        {0: 24, 1: 48, 2: 0, 5: 2},
        {0: 25, 1: 45, 2: 3, 5: 1},
        {0: 26, 1: 42, 2: 6, 5: 0},
    ]

    for u_cls in active:
        g_u, chi_u = deck_x[u_cls]
        Gcd_u = sp.gcd(chi_u, chi_u.diff())
        H_u, _ = sp.div(chi_u, Gcd_u)
        quo_u, _ = sp.div(chi_u.diff(), Gcd_u)
        s_u = H_u.degree()
        rhs_u = [int(v) for v in quo_u.all_coeffs()]
        rhs_u = [0] * (s_u - len(rhs_u)) + rhs_u
        print(f"\n--- Around u in deck[{u_cls}] (H_u={sp.factor(H_u.as_expr())}) ---")

        # Also check simple eigenvalues of chi_u
        facs_u = sp.factor_list(chi_u.as_expr())[1]
        sim_roots = []
        for fac_e, mult in facs_u:
            fac_p = sp.Poly(fac_e, x, domain=sp.ZZ)
            if mult == 1 and fac_p.degree() == 1:
                lam = int(-fac_p.coeff_monomial(1) // fac_p.LC())
                if lam != -5:
                    sim_roots.append(lam)
        print(f"  Simple roots of chi_{u_cls} (excl -5): {sim_roots}")

        items = []
        for j in active:
            for sd in pair_sols[(u_cls, j)]:
                q_poly = sp.Poly(sp.sympify(sd["q_uv"]), x, domain=sp.ZZ)
                g_uv, rem = sp.div(Gcd_2 * q_poly, Gcd_u)
                assert rem.is_zero
                cs = [int(v) for v in g_uv.all_coeffs()]
                cs = [0] * (s_u - len(cs)) + cs
                proj = {lam: sp.Rational(int(g_uv.eval(lam)), int(quo_u.eval(lam))) for lam in sim_roots}
                items.append((j, sd["s_uv"], sd["S2_uv"], cs, proj))

        for it in items:
            print(f"  j={it[0]} s={it[1]:+d} S2={it[2]:+3d} proj={ {k: str(v) for k,v in it[4].items()} }")

        for sol2 in survs:
            if sol2[u_cls] == 0:
                continue
            model = cp_model.CpModel()
            mv = [model.NewIntVar(0, n - 1, f"m_{k}") for k in range(len(items))]
            for j in active:
                model.Add(sum(mv[k] for k, it in enumerate(items) if it[0] == j) == sol2[j] - (1 if j == u_cls else 0))
            for r in range(s_u):
                model.Add(sum(items[k][3][r] * mv[k] for k in range(len(items))) == rhs_u[r])
            all_s3 = []
            class Col(cp_model.CpSolverSolutionCallback):
                def on_solution_callback(self):
                    all_s3.append(tuple(self.Value(v) for v in mv))
            sv = cp_model.CpSolver()
            sv.parameters.enumerate_all_solutions = True
            sv.Solve(model, Col())
            # Also filter by 1-line simple root square-class compatibility!
            # Wait: for each simple root lam of chi_u, all nonzero proj[lam] across chosen items must be in same Q^x square class!
            def sq_class(rat: sp.Rational):
                if rat == 0: return 0
                val = rat.p * rat.q
                return sp.core.numbers.Integer(val).factors() if False else sp.factorint(val)
            def sqfree(rat: sp.Rational):
                if rat == 0: return 0
                num = abs(rat.p * rat.q)
                res = 1
                for p, e in sp.factorint(num).items():
                    if e % 2 == 1: res *= p
                return res if rat > 0 else -res

            compat_s3 = []
            for s3 in all_s3:
                ok = True
                for lam in sim_roots:
                    scs = {sqfree(items[k][4][lam]) for k in range(len(items)) if s3[k] > 0} - {0}
                    if len(scs) > 1:
                        ok = False
                        break
                if ok:
                    compat_s3.append(s3)
            print(f"  Sol {sol2}: raw Stage-3={len(all_s3)}, after K^x={len(compat_s3)}")
            for s3 in compat_s3[:10]:
                desc = [(items[k][0], items[k][1], items[k][2], s3[k]) for k in range(len(items)) if s3[k] > 0]
                print("    ", desc)


def inspect_idx24():
    print("\n=== IDX=24 CONE [0, 1, 2, 4, 6] & STAGE-3 CHECK ===")
    d, n, c, cand = load_candidate("deck_19_74.json", 24)
    chi_S, f_x, Gcd_x, H_x, quo_x, deck_x = reconstruct_polys_x(d, n, c, cand)
    sols24 = [
        {0: 24, 1: 36, 2: 0, 4: 12, 6: 2},
        {0: 24, 1: 36, 2: 3, 4: 8,  6: 3},
        {0: 24, 1: 36, 2: 6, 4: 4,  6: 4},
        {0: 24, 1: 36, 2: 9, 4: 0,  6: 5},
    ]
    for i, (gv, chiv) in enumerate(deck_x):
        if i in (0, 1, 2, 4, 6):
            Gcd_u = sp.gcd(chiv, chiv.diff())
            H_u, _ = sp.div(chiv, Gcd_u)
            print(f"  deck[{i}]: H_u = {sp.factor(H_u.as_expr())}, deg(H_u)={H_u.degree()}")
            # Check Prop 6.1 on deck[0] (size 24): chi_0 preserves (x^2-28x+191)^3!
            # Check exact spectral projectors E_17, E_15, E_13, E_{14+-sqrt(5)} traces on the 4 sols!
    # Check 2-adic of chi_u or S_u
    for sol in sols24:
        # Check E_15 trace: [(0, 3/20), (1, 3/20), (2, 0), (4, 0), (6, 0)] -> (24+36)*3/20 = 9.
        # Check E_13 trace: [(0, 1/12), (1, 0), (2, 1/9), (4, 1/12), (6, 0)] -> 24/12 + c2/9 + c4/12 = 2 + u/3 + (12-4u)/12 = 3!
        # Check E_{14+-sqrt(5)} sum trace: [(0, 0), (1, 19/178), (2, 13/89), (4, 27/178), (6, 15/89)]
        # Wait: 36*(19/178) + (3u)*(13/89) + (12-4u)*(27/178) + (2+u)*(15/89) = 6!
        # Check E_17: [(0, 1/44), (1, 0), (2, 0), (4, 1/44), (6, 1/11)] -> 24/44 + (12-4u)/44 + (2+u)/11 = 1.
        print("  sol", sol)
        # Wait: look at E_15[i,i] = 3/20 on C_0 and C_1, and 0 on C_2, C_4, C_6!
        # And E_{14+-sqrt(5)} = 0 on C_0!
        # Wait: let's check deck[4] vs Prop 6.1 or Stage-3 on deck[0] (which has 24 vertices preserving (x^2-28x+191)^3!)
    # Notice deck[0] has chi_0 = (x-15)^8 (x-13)^2 (x+5)^54 (x^2-28x+191)^3 (x^3-40x^2+519x-2172)!
    # Wait: what is chi_0'(x) / Gcd_0(x)? Wait: C_0 has 24 vertices, and deck[0] preserves (x^2-28x+191)^3!
    # So E_{14+sqrt(5)} and E_{14-sqrt(5)} are BOTH supported ONLY on C_0^c = C_1 U C_2 U C_4 U C_6 (50 vertices)!


if __name__ == "__main__":
    inspect_idx13_survivors()
    inspect_idx24()
