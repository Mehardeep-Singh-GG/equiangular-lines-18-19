"""Exact float-free Galois (ZERO poly_sig!) + K^x square-class + Stage-3 attack
on the last 3 survivors of (19, 74) idx=13:
  S1: (24, 48, 0, 2)
  S2: (25, 45, 3, 1)
  S3: (26, 42, 6, 0)
"""
from __future__ import annotations
import math
import sympy as sp
from ortools.sat.python import cp_model

from attack_861_and_47 import load_candidate, reconstruct_polys_x
from audit_861_and_47_proofs import brute_2v_jacobi

x = sp.Symbol("x")


def is_square_in_numfield(elem_poly: sp.Poly, mod_poly: sp.Poly) -> bool:
    """Exact check whether elem_poly (mod mod_poly) is a square in K = QQ[x]/(mod_poly).
    Zero poly_sig! Uses SymPy exact factorization of T^2 - elem over QQ(alpha) or norm + rational solver.
    """
    rem = sp.rem(sp.Poly(elem_poly.as_expr(), x, domain=sp.QQ), mod_poly)
    if rem.is_zero:
        return True
    deg = mod_poly.degree()
    if deg == 1:
        r = sp.Rational(-mod_poly.coeff_monomial(1), mod_poly.LC())
        val = sp.Rational(rem.eval(r))
        if val < 0:
            return False
        return math.isqrt(val.p) ** 2 == val.p and math.isqrt(val.q) ** 2 == val.q
    # For deg 2 or 3: check using sp.solve for (c0 + c1*x + ...)^2 === rem (mod mod_poly)
    cs = sp.symbols(f"c_0:{deg}")
    u = sp.Poly(sum(cs[i] * x**i for i in range(deg)), x)
    sq = sp.rem(u * u, mod_poly)
    eqs = [sp.expand((sq - rem).coeff_monomial(x**k)) for k in range(deg)]
    sols = sp.solve(eqs, cs, dict=True)
    for sd in sols:
        if all(sp.sympify(sd[c]).is_Rational for c in cs):
            return True
    return False


def square_classes_exact(items_evals: list[sp.Poly], mod_poly: sp.Poly) -> list[int]:
    """Assign exact K^x / (K^x)^2 class IDs (0 = zero element, 1,2,... = nonzero classes)
    using exact is_square_in_numfield(a * b, mod_poly). Zero hashing / zero poly_sig!
    """
    reps: list[sp.Poly] = []
    labels: list[int] = []
    # Deduplicate identical remainders first for speed
    cache: dict[tuple, int] = {}
    for p in items_evals:
        rem = sp.rem(sp.Poly(p.as_expr(), x, domain=sp.QQ), mod_poly)
        if rem.is_zero:
            labels.append(0)
            continue
        key = tuple(rem.all_coeffs())
        if key in cache:
            labels.append(cache[key])
            continue
        found = None
        for cid, rep in enumerate(reps, start=1):
            if is_square_in_numfield(rem * rep, mod_poly):
                found = cid
                break
        if found is None:
            reps.append(rem)
            found = len(reps)
        cache[key] = found
        labels.append(found)
    return labels


def check_stage3_galois(u_cls: int, survs: list[tuple[str, dict[int, int]]]):
    d, n, c, cand = load_candidate("deck_19_74.json", 13)
    chi_S, f_x, Gcd_x, H_x, quo_x, deck_x = reconstruct_polys_x(d, n, c, cand)
    Gcd_2 = sp.gcd(Gcd_x, Gcd_x.diff())
    active = [0, 1, 2, 5]

    g_u, chi_u = deck_x[u_cls]
    Gcd_u = sp.gcd(chi_u, chi_u.diff())
    H_u, _ = sp.div(chi_u, Gcd_u)
    quo_u, _ = sp.div(chi_u.diff(), Gcd_u)
    s_u = H_u.degree()
    rhs_u = [int(v) for v in quo_u.all_coeffs()]
    rhs_u = [0] * (s_u - len(rhs_u)) + rhs_u

    # Simple factors of chi_u (excluding x+5)
    facs_u = sp.factor_list(chi_u.as_expr())[1]
    sim_facs = []
    for fac_e, mult in facs_u:
        fp = sp.Poly(fac_e, x, domain=sp.QQ)
        if mult == 1 and fp != sp.Poly(x + 5, x, domain=sp.QQ):
            sim_facs.append(fp)
    print(f"\n=== u in deck[{u_cls}] | sim_facs={[str(f.as_expr()) for f in sim_facs]} ===")

    items = []
    for j in active:
        sols = brute_2v_jacobi(chi_S, Gcd_x, H_x, deck_x[u_cls][0], deck_x[j][0], n, 18, x)
        for sd in sols:
            q_poly = sp.Poly(sp.sympify(sd["q_uv"]), x, domain=sp.ZZ)
            g_uv, rem = sp.div(Gcd_2 * q_poly, Gcd_u)
            assert rem.is_zero
            cs = [int(v) for v in g_uv.all_coeffs()]
            cs = [0] * (s_u - len(cs)) + cs
            items.append((j, sd["s_uv"], sd["S2_uv"], cs, g_uv))

    # Compute exact K^x square classes for every factor in sim_facs!
    # Wait: E_theta[w,w] = g_uv(theta) / quo_u(theta), so square class is g_uv(theta) * quo_u(theta) mod fp!
    cls_by_fac = []
    for fp in sim_facs:
        evals = [sp.Poly(it[4].as_expr() * quo_u.as_expr(), x, domain=sp.QQ) for it in items]
        labs = square_classes_exact(evals, fp)
        print(f"  Factor {fp.as_expr()} square classes: {labs}")
        cls_by_fac.append((fp, labs))

    # Iterate over all combinations of nonzero square-class cones (1 choice per factor)
    import itertools
    nz_sets = [sorted(set(labs) - {0}) for _, labs in cls_by_fac]
    cone_choices = list(itertools.product(*nz_sets))
    print(f"  Total K^x cone combinations: {len(cone_choices)}")

    wt = {0: 0, 1: 1, 2: 2, 5: 3}
    for name, sol2 in survs:
        if sol2[u_cls] == 0:
            continue
        feasible_cones = 0
        for choice in cone_choices:
            # Allowed items: for every factor f_idx, lab in {0, choice[f_idx]}
            allowed = [
                k for k in range(len(items))
                if all(cls_by_fac[fi][1][k] in (0, choice[fi]) for fi in range(len(sim_facs)))
            ]
            if not allowed:
                continue
            model = cp_model.CpModel()
            mv = {k: model.NewIntVar(0, n - 1, f"m_{k}") for k in allowed}
            for j in active:
                model.Add(sum(mv[k] for k in allowed if items[k][0] == j) == sol2[j] - (1 if j == u_cls else 0))
            for r in range(s_u):
                model.Add(sum(items[k][3][r] * mv[k] for k in allowed) == rhs_u[r])
            # S v_17 = 17 v_17
            model.Add(sum(wt[items[k][0]] * items[k][1] * mv[k] for k in allowed) == 17 * wt[u_cls])
            # Structural locks we proved for S1 and S2:
            if name.startswith("S1") and u_cls == 5:
                model.Add(sum(mv[k] for k in allowed if items[k][0] == 1 and items[k][1] == -1) == 0)
                model.Add(sum(mv[k] for k in allowed if items[k][0] == 5 and items[k][1] == -1) == 0)
            if name.startswith("S1") and u_cls == 1:
                model.Add(sum(mv[k] for k in allowed if items[k][0] == 5 and items[k][1] == -1) == 0)
                model.Add(sum(items[k][1] * mv[k] for k in allowed if items[k][0] == 0) == 0)
            if name.startswith("S2") and u_cls == 5:
                model.Add(sum(mv[k] for k in allowed if items[k][0] in (1, 2) and items[k][1] == -1) == 0)
            if name.startswith("S2") and u_cls in (1, 2):
                model.Add(sum(mv[k] for k in allowed if items[k][0] == 5 and items[k][1] == -1) == 0)
            # Also for u_cls == 0: R[C_0, C_0] = J => 10*s - S2 == 2 on j == 0
            if u_cls == 0:
                model.Add(sum(mv[k] for k in allowed if items[k][0] == 0 and (10 * items[k][1] - items[k][2]) != 2) == 0)
            if name.startswith("S1") and u_cls == 0:
                model.Add(sum(mv[k] for k in allowed if items[k][0] == 5 and items[k][1] == 1) == 1)

            sv = cp_model.CpSolver()
            status = sv.Solve(model)
            if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
                feasible_cones += 1
                sol_desc = [(items[k][0], items[k][1], items[k][2], sv.Value(mv[k])) for k in allowed if sv.Value(mv[k]) > 0]
                print(f"  [{name}] FEASIBLE cone {choice}: sample={sol_desc}")
        print(f"  [{name}] at deck[{u_cls}]: {feasible_cones}/{len(cone_choices)} K^x cones feasible")


def main():
    survs = [
        ("S1(24,48,0,2)", {0: 24, 1: 48, 2: 0, 5: 2}),
        ("S2(25,45,3,1)", {0: 25, 1: 45, 2: 3, 5: 1}),
        ("S3(26,42,6,0)", {0: 26, 1: 42, 2: 6, 5: 0}),
    ]
    for u_cls in (1, 2, 5, 0):
        check_stage3_galois(u_cls, survs)


if __name__ == "__main__":
    main()
