"""Attack the last 3 solutions of (19, 74) idx=13:
  S1: (24, 48, 0, 2)
  S2: (25, 45, 3, 1)
  S3: (26, 42, 6, 0)
using exact Stage-3 at u in C_0 with R[C_0,C_0] = J (since rank(E_11[C_0])=1),
exact E_17 eigenvector constraints, and Stage-3 at C_1, C_2, C_5!
"""
from __future__ import annotations
import sympy as sp
from ortools.sat.python import cp_model

from attack_861_and_47 import load_candidate, reconstruct_polys_x
from audit_861_and_47_proofs import brute_2v_jacobi

x = sp.Symbol("x")


def main():
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

    # Check Stage-3 at u in C_0 WITH R[C_0, C_0] = J_{|C_0|}!
    # Remember: R_{uw} = 1/2 (10 s_{uw} - S2_{uw}) for u, w in C_0!
    # Switching C_0 by z makes R[C_0, C_0] = +1 everywhere, so 10*s - S2 == 2!
    # Also check E_9 and E_12 on chi_0!
    g0, chi_0 = deck_x[0]
    Gcd_0 = sp.gcd(chi_0, chi_0.diff())
    H_0, _ = sp.div(chi_0, Gcd_0)
    quo_0, _ = sp.div(chi_0.diff(), Gcd_0)
    s0 = H_0.degree()
    rhs0 = [int(v) for v in quo_0.all_coeffs()]
    rhs0 = [0] * (s0 - len(rhs0)) + rhs0

    print("=== Stage-3 at u in C_0 (after switching z so R[C_0,C_0] = J) ===")
    items0 = []
    for j in active:
        for sd in pair_sols[(0, j)]:
            s_uv, S2_uv = sd["s_uv"], sd["S2_uv"]
            if j == 0 and (10 * s_uv - S2_uv) != 2:
                continue
            q_poly = sp.Poly(sp.sympify(sd["q_uv"]), x, domain=sp.ZZ)
            g_uv, rem = sp.div(Gcd_2 * q_poly, Gcd_0)
            assert rem.is_zero
            cs = [int(v) for v in g_uv.all_coeffs()]
            cs = [0] * (s0 - len(cs)) + cs
            e9 = sp.Rational(int(g_uv.eval(9)), int(quo_0.eval(9)))
            e12 = sp.Rational(int(g_uv.eval(12)), int(quo_0.eval(12)))
            items0.append((j, s_uv, S2_uv, cs, e9, e12))
            print(f"  item j={j} s={s_uv:+d} S2={S2_uv:+3d} E9={e9} E12={e12}")

    for sol2 in survs:
        model = cp_model.CpModel()
        mv = [model.NewIntVar(0, n - 1, f"m_{k}") for k in range(len(items0))]
        for j in active:
            model.Add(sum(mv[k] for k, it in enumerate(items0) if it[0] == j) == sol2[j] - (1 if j == 0 else 0))
        for r in range(s0):
            model.Add(sum(items0[k][3][r] * mv[k] for k in range(len(items0))) == rhs0[r])

        # Also check E_17[u, :] * v_17 == 0 => sum_{v in C_1} s_{uv} + 2 sum_{y in C_2} s_{uy} + 3 sum_{w in C_5} s_{uw} == 0!
        # WAIT A SECOND! After switching by v_{17} (which does NOT change C_0 since v_17=0 on C_0!),
        # (S v_17)_u = 0 MUST hold for EVERY u in C_0!!
        # Let's check BOTH with and without (S v_17)_u = 0!
        for with_v17 in (False, True):
            m2 = cp_model.CpModel()
            mv2 = [m2.NewIntVar(0, n - 1, f"m_{k}") for k in range(len(items0))]
            for j in active:
                m2.Add(sum(mv2[k] for k, it in enumerate(items0) if it[0] == j) == sol2[j] - (1 if j == 0 else 0))
            for r in range(s0):
                m2.Add(sum(items0[k][3][r] * mv2[k] for k in range(len(items0))) == rhs0[r])
            if with_v17:
                wt = {0: 0, 1: 1, 2: 2, 5: 3}
                m2.Add(sum(wt[it[0]] * it[1] * mv2[k] for k, it in enumerate(items0)) == 0)
            all_s = []
            class Col(cp_model.CpSolverSolutionCallback):
                def on_solution_callback(self):
                    all_s.append(tuple(self.Value(v) for v in mv2))
            sv = cp_model.CpSolver()
            sv.parameters.enumerate_all_solutions = True
            sv.Solve(m2, Col())
            print(f"  sol={sol2} with_v17={with_v17}: {len(all_s)} sols")
            for s3 in all_s[:5]:
                print("   ", [(items0[k][0], items0[k][1], items0[k][2], s3[k]) for k in range(len(items0)) if s3[k] > 0])


if __name__ == "__main__":
    main()
