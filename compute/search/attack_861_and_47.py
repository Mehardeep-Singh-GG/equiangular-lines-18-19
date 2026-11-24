"""Independent exact SymPy verification & attack on:
  1. (18, 59) idx=861 (30 + 1 + 28 equitable partition)
  2. (19, 74) idx=47  (52 + 16 + 6 with 2-regular 16-block C_1)
"""

from __future__ import annotations
import json
import math
from pathlib import Path
from typing import Dict, List, Tuple
import sympy as sp
import sys

_COMP_DIR = Path(__file__).resolve().parent.parent
if str(_COMP_DIR) not in sys.path:
    sys.path.insert(0, str(_COMP_DIR))
from _io import POLY_RESULTS_DIR, SEARCH_RESULTS_DIR, load_json_auto

POLY_RESULTS = POLY_RESULTS_DIR
OUT_DIR = SEARCH_RESULTS_DIR


def load_candidate(deck_file: str, target_idx: int) -> Tuple[int, int, int, dict]:
    data = load_json_auto(deck_file, POLY_RESULTS)
    d, n, c_shift = data["d"], data["n"], data["c"]
    for cand in data["candidates"]:
        if cand["index"] == target_idx:
            return d, n, c_shift, cand
    raise KeyError(target_idx)


def reconstruct_polys_x(d: int, n: int, c_shift: int, cand: dict):
    """Reconstruct exact chi_S(x), f(x), Gcd_x(x), Sim_x(x), and deck chi_{S_v}(x) in ZZ[x]."""
    w, x = sp.symbols("w x")
    b = cand["b"]
    s = cand["s"]
    Pw = sp.Poly(sum(b[j] * w ** (d - j) for j in range(d + 1)), w, domain=sp.ZZ)
    w0 = (-5 - c_shift) // 2
    Full_w = sp.Poly((w - w0) ** (n - d), w, domain=sp.ZZ) * Pw
    Dw = sp.gcd(Full_w, Full_w.diff())
    Hw, _ = sp.div(Full_w, Dw)
    assert Hw.degree() == s

    # Convert to x via w = (x - c_shift)/2, multiplying by 2^deg so monic in ZZ[x]
    def w_poly_to_x_monic(p_w: sp.Poly, deg_expected: int = None) -> sp.Poly:
        deg = p_w.degree() if deg_expected is None else deg_expected
        expr = (2 ** deg) * p_w.as_expr().subs(w, (x - c_shift) / 2)
        poly = sp.Poly(sp.expand(expr), x, domain=sp.ZZ)
        if poly.LC() != 1:
            assert poly.LC() > 0 and all(int(c) % int(poly.LC()) == 0 for c in poly.all_coeffs())
            poly = sp.Poly(poly.as_expr() / poly.LC(), x, domain=sp.ZZ)
        return poly

    chi_S = w_poly_to_x_monic(Full_w, n)
    f_x = w_poly_to_x_monic(Pw, d)
    Gcd_x = w_poly_to_x_monic(Dw, n - s)
    H_x = w_poly_to_x_monic(Hw, s)

    # Note: in deck_t42 / deck, each row represents the reduced numerator P_v(w) of degree s-1
    # such that sum n_v P_v(w) == 2 * Full_w'(w) / Dw(w).
    # In x: Full_x'(x) = 1/2 * 2^n * Full_w'(w)|_{w=(x-c)/2} ... wait:
    # Let's check exact scaling! d/dx [(2w+c) ...] = (1/2) d/dw.
    # Full_w(w) = 2^{-n} chi_S(2w + c). So d/dw Full_w(w) = 2^{-(n-1)} chi_S'(2w+c).
    # Since Dw(w) = 2^{-(n-s)} Gcd_x(2w+c), 2 * Full_w'(w) / Dw(w) = 2 * 2^{-(s-1)} chi_S'(x)/Gcd_x(x)?
    # Let's check directly: deck_x[j] = sum row[k] * ((x-c)/2)^{s-1-k} * 2^{s-1}!
    deck_x = []
    for row in cand["deck"]:
        Pw_v = sp.Poly(sum(int(row[k]) * w ** (s - 1 - k) for k in range(s)), w, domain=sp.ZZ)
        g_v = w_poly_to_x_monic(Pw_v, s - 1)
        chi_v = Gcd_x * g_v
        assert chi_v.LC() == 1, f"Non-monic deck poly LC={chi_v.LC()}"
        deck_x.append((g_v, chi_v))

    # Verify sum rule scaling: 2 * quo in w == chi_S'(x) / Gcd_x(x) in x!
    quo_x, rem_x = sp.div(chi_S.diff(), Gcd_x)
    assert rem_x.is_zero
    return chi_S, f_x, Gcd_x, H_x, quo_x, deck_x


def attack_861():
    print("============================================================")
    print("ATTACK 1: (18, 59) idx=861")
    print("============================================================")
    d, n, c_shift, cand = load_candidate("deck_18_59.json", 861)
    x = sp.Symbol("x")
    chi_S, f_x, Gcd_x, H_x, quo_x, deck_x = reconstruct_polys_x(d, n, c_shift, cand)
    print("chi_S(x) =", sp.factor(chi_S.as_expr()))
    print("Gcd_x(x) =", sp.factor(Gcd_x.as_expr()))
    print("H_x(x)   =", sp.factor(H_x.as_expr()))

    # 1. Check exact linear solutions to sum n_j g_j(x) = quo_x(x) (using K^x compatibility too!)
    s = H_x.degree()
    A_cols = []
    for g_v, _ in deck_x:
        cs = g_v.all_coeffs()
        cs = [0] * (s - len(cs)) + [int(v) for v in cs]
        A_cols.append(cs)
    rhs = [int(v) for v in quo_x.all_coeffs()]
    rhs = [0] * (s - len(rhs)) + rhs

    # Factor H_x into Sim_x and Mult_rad
    facs = sp.factor_list(chi_S.as_expr())[1]
    Sim_expr = sp.Integer(1)
    for fac, mult in facs:
        if mult == 1:
            Sim_expr *= fac
    Sim_x = sp.Poly(Sim_expr, x, domain=sp.ZZ)
    print("Sim_x(x) =", sp.factor(Sim_x.as_expr()))

    # Filter deck by Theorem 4.2 on n-1 = 58 (even -> 2^58 | chi_{S_v}(2t-1))
    t = sp.Symbol("t")
    valid_idx = []
    for j, (g_v, chi_v) in enumerate(deck_x):
        p_t = sp.Poly(sp.expand(chi_v.as_expr().subs(x, 2 * t - 1)), t, domain=sp.ZZ)
        if all(int(c) % (1 << 58) == 0 for c in p_t.all_coeffs()):
            valid_idx.append(j)
    print(f"Deck indices passing 2^58 | chi_{{S_v}}(2t-1): {valid_idx} (out of {len(deck_x)})")

    # Solve exact RREF over valid_idx + square-class cones on Sim_x = x^2 - 19x + 82
    def is_sq_in_K(P_poly: sp.Poly, q_poly: sp.Poly) -> bool:
        rem = sp.rem(sp.Poly(P_poly.as_expr(), x, domain=sp.QQ), q_poly)
        if rem.is_zero:
            return True
        alpha = sp.RootOf(q_poly.as_expr(), 0)
        ts = sp.Symbol("_ts")
        pt = sp.Poly(ts**2 - rem.as_expr().subs(x, alpha), ts, domain=sp.QQ.algebraic_field(alpha))
        fl = pt.factor_list()[1]
        return len(fl) > 1 or fl[0][1] == 2

    # Group valid_idx by square class mod Sim_x
    zero_cls = [j for j in valid_idx if sp.rem(deck_x[j][0], Sim_x).is_zero]
    nz_cls = [j for j in valid_idx if j not in zero_cls]
    cones = []
    used = []
    for j in nz_cls:
        placed = False
        for c_rep, c_members in cones:
            if is_sq_in_K(deck_x[j][0] * deck_x[c_rep][0], Sim_x):
                c_members.append(j)
                placed = True
                break
        if not placed:
            cones.append((j, [j]))
    print(f"Square classes mod Sim_x: zero={zero_cls}, nonzero cones={[c[1] for c in cones]}")

    all_sols = []
    for _, members in cones:
        sub_idx = zero_cls + members
        m_sub = len(sub_idx)
        A_mat = sp.Matrix([[sp.Rational(A_cols[j][r]) for j in sub_idx] for r in range(s)])
        rhs_vec = sp.Matrix([sp.Rational(v) for v in rhs])
        rref_mat, pivots = A_mat.row_join(rhs_vec).rref()
        if any(all(rref_mat[r, j] == 0 for j in range(m_sub)) and rref_mat[r, m_sub] != 0 for r in range(rref_mat.rows)):
            continue
        free_v = [j for j in range(m_sub) if j not in set(pivots)]
        print(f"  Cone {members}: rank={len(pivots)}, free_vars={[sub_idx[f] for f in free_v]}")
        if not free_v:
            sol = [(sub_idx[pivots[r]], rref_mat[r, m_sub]) for r in range(len(pivots))]
            if all(val >= 0 and val.is_integer for _, val in sol):
                all_sols.append([(j, int(val)) for j, val in sol if val > 0])
        else:
            # Enumerate bounded free variables up to 59
            assert len(free_v) <= 2
            ranges = [range(60)] * len(free_v)
            import itertools
            for fvals in itertools.product(*ranges):
                if sum(fvals) > 59:
                    continue
                ok = True
                sol_map = {sub_idx[free_v[k]]: fvals[k] for k in range(len(free_v))}
                for r, pcol in enumerate(pivots):
                    val = rref_mat[r, m_sub] - sum(rref_mat[r, free_v[k]] * fvals[k] for k in range(len(free_v)))
                    if val < 0 or not val.is_integer:
                        ok = False
                        break
                    sol_map[sub_idx[pcol]] = int(val)
                if ok and sum(sol_map.values()) == 59:
                    all_sols.append(sorted((j, v) for j, v in sol_map.items() if v > 0))

    print("ALL valid nonneg integer Stage-2 solutions for idx=861:", all_sols)
    for sol in all_sols:
        print("  Solution details:")
        for j, mult in sol:
            print(f"    deck[{j}] x {mult}: chi = {sp.factor(deck_x[j][1].as_expr())}")

    # 2. Check the unique vertex deck[5] (mult=1) and its 30+28 decomposition!
    # Wait: let's verify Eulerian gauge degree of deck[5] and the 2-vertex Jacobi constraint between deck[4] (30) and deck[9] (28)!
    # In chi_{S_{u_1}}(x) = chi_5(x), check if 5 is an eigenvalue of S_{u_1}, and check the unique quotient K and XY+YZ = 8Y!
    g4, chi4 = deck_x[4]
    g5, chi5 = deck_x[5]
    g9, chi9 = deck_x[9]
    print("\nChecking 2-vertex Jacobi between deck[4] (mult 30) and deck[9] (mult 28):")
    # Wait: by Corollary 5.2(2), g_4(x) * g_9(x) - Sim_x(x) * q_{uv}(x) = h_{uv}(x)^2!
    # Here deg(g_4) = deg(g_9) = 5, deg(Sim_x) = 2, deg(h_{uv}) = 4, deg(q_{uv}) = 8?
    # Wait: chi_S / Gcd_x = Sim_x * Mult_rad has degree 6, so s = 6.
    # Let's factor H_x: H_x = (x+5)(x-13)(x-11)(x-9)(x^2-19x+82), deg 6!
    # So Sim_x = x^2 - 19x + 82 (deg 2), Mult_rad = (x+5)(x-13)(x-11)(x-9) (deg 4).
    # deg(g_a) = 5, deg(h_{uv}) = 4, deg(q_{uv}) = 8.
    # Let's solve h_{uv}(x)^2 === g_4(x) * g_9(x) (mod Sim_x(x))!
    # Notice: what is Gcd_x(x)?
    # Gcd_x(x) = (x+5)^40 (x-13)^7 (x-11)^4 (x-9)^2!
    # Wait: in chi_{S_4}(x) = Gcd_x * g_4, let's see what g_4, g_5, g_9 are!
    print("  g4(x) =", g4.as_expr())
    print("  g5(x) =", g5.as_expr())
    print("  g9(x) =", g9.as_expr())

    # Solve M * k_u = N for (deck[4], deck[5], deck[9]) using Theorem 7.1!
    Mult_x_poly, _ = sp.div(chi_S, Gcd_x * Sim_x)
    # Wait: Mult_x = chi_S / Sim_x! (deg 57!)
    Mult_full, rem_m = sp.div(chi_S, Sim_x)
    assert rem_m.is_zero
    xMult_full = sp.Poly(x * Mult_full.as_expr(), x, domain=sp.ZZ)

    def diag_entry(P_poly: sp.Poly, g_v: sp.Poly) -> int:
        roots = [sp.RootOf(Sim_x.as_expr(), k) for k in range(Sim_x.degree())]
        total = sp.Integer(0)
        for r in roots:
            val = sp.simplify(P_poly.as_expr().subs(x, r) * Gcd_x.as_expr().subs(x, r) * g_v.as_expr().subs(x, r) / chi_S.diff().as_expr().subs(x, r))
            total += val
        val_int = sp.simplify(total)
        assert val_int.is_Integer, f"Non-integer trace {val_int}"
        return int(val_int)

    for idx_v in [4, 5, 9]:
        M_uu = diag_entry(Mult_full, deck_x[idx_v][0])
        N_uu = diag_entry(xMult_full, deck_x[idx_v][0])
        print(f"  deck[{idx_v}]: M_uu = {M_uu}, N_uu = {N_uu}")


def attack_47():
    print("\n============================================================")
    print("ATTACK 2: (19, 74) idx=47")
    print("============================================================")
    d, n, c_shift, cand = load_candidate("deck_19_74.json", 47)
    x = sp.Symbol("x")
    chi_S, f_x, Gcd_x, H_x, quo_x, deck_x = reconstruct_polys_x(d, n, c_shift, cand)
    print("chi_S(x) =", sp.factor(chi_S.as_expr()))
    print("Gcd_x(x) =", sp.factor(Gcd_x.as_expr()))
    print("H_x(x)   =", sp.factor(H_x.as_expr()))
    for j, (gv, chiv) in enumerate(deck_x):
        print(f"  deck[{j}]: g={gv.as_expr()} | chi={sp.factor(chiv.as_expr())}")

    # Solve sum n_j g_j = quo_x
    s = H_x.degree()
    A_mat = sp.Matrix([[sp.Rational(v) for v in ([0]*(s-len(gv.all_coeffs())) + [int(c) for c in gv.all_coeffs()])] for gv, _ in deck_x]).T
    rhs = [int(c) for c in quo_x.all_coeffs()]
    rhs = [0]*(s-len(rhs)) + rhs
    rhs_vec = sp.Matrix([sp.Rational(v) for v in rhs])
    rref_mat, pivots = A_mat.row_join(rhs_vec).rref()
    print("RREF pivots:", pivots, "sol:", [int(rref_mat[r, 3]) for r in range(len(pivots))])


if __name__ == "__main__":
    attack_861()
    attack_47()
