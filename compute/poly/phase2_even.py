"""
Exact Phase-2 Stage-2/3 elimination pipeline for even-n candidates.
Every elimination is 100% certified in exact integer / Fraction arithmetic (ZERO floating-point trust):
  1. Theorem 4.2 exact mod-4 congruence filter on odd-(n-1) Deck(p) polynomials.
  2. Exact integer Farkas certificates (via HiGHS guess + exact int verification).
  3. Exact K^x / (K^x)^2 compatibility in Q[w]/(q(w)) for every simple irreducible factor q | f,
     plus exact Fraction-certified infeasibility (exact Farkas OR exact RREF + dual-bounded integer search).
  4. Exact Proposition 6.1 strengthened submatrix extraction (mult_lambda(S_v) >= m)
     with exact integer LP dual certificates for [k_min, k_max].
"""
import json
import math
import sys
from fractions import Fraction
import sympy as sp
import numpy as np
from scipy.optimize import linprog


def verify_farkas_exact(A_int, rhs_int, c_int):
    for row in A_int:
        if sum(ci * ri for ci, ri in zip(c_int, row)) < 0:
            return False
    return sum(ci * ri for ci, ri in zip(c_int, rhs_int)) < 0


def find_exact_farkas_rational(A_int, rhs_int):
    """Pure-Fraction Bland's-rule Phase-I Simplex returning an exact integer Farkas cert."""
    m = len(A_int)
    s = len(rhs_int)
    if m == 0:
        c_int = [-1] + [0] * (s - 1)
        return (True, c_int) if verify_farkas_exact(A_int, rhs_int, c_int) else (False, None)
    row_sgn = [1 if rhs_int[r] >= 0 else -1 for r in range(s)]
    T = [[Fraction(0)] * (m + s + 1) for _ in range(s + 1)]
    for r in range(s):
        sg = row_sgn[r]
        for j in range(m):
            T[r][j] = Fraction(sg * A_int[j][r])
        T[r][m + r] = Fraction(1)
        T[r][-1] = Fraction(sg * rhs_int[r])
    for r in range(s):
        T[s][m + r] = Fraction(1)
    for r in range(s):
        for col in range(m + s + 1):
            T[s][col] -= T[r][col]
    basis = [m + r for r in range(s)]
    while True:
        enter = -1
        for col in range(m + s):
            if T[s][col] < 0:
                enter = col
                break
        if enter == -1:
            break
        leave = -1
        best_ratio = None
        for r in range(s):
            a = T[r][enter]
            if a > 0:
                ratio = T[r][-1] / a
                if leave == -1 or ratio < best_ratio or (ratio == best_ratio and basis[r] < basis[leave]):
                    leave = r
                    best_ratio = ratio
        if leave == -1:
            return False, None
        piv = T[leave][enter]
        for col in range(m + s + 1):
            T[leave][col] /= piv
        for r in range(s + 1):
            if r != leave and T[r][enter] != 0:
                fac = T[r][enter]
                for col in range(m + s + 1):
                    T[r][col] -= fac * T[leave][col]
        basis[leave] = enter

    if -T[s][-1] <= 0:
        return False, None
    c_rat = [-(Fraction(1) - T[s][m + r]) * row_sgn[r] for r in range(s)]
    lcm_d = 1
    for v in c_rat:
        lcm_d = math.lcm(lcm_d, v.denominator)
    c_int = [int(v * lcm_d) for v in c_rat]
    if verify_farkas_exact(A_int, rhs_int, c_int):
        return True, c_int
    return False, None


def find_exact_farkas(A_int, rhs_int):
    m = len(A_int)
    s = len(rhs_int)
    if m == 0:
        c_int = [-1] + [0] * (s - 1)
        if verify_farkas_exact(A_int, rhs_int, c_int):
            return True, c_int
        return False, None
    A = np.array(A_int, dtype=np.float64)
    rhs = np.array(rhs_int, dtype=np.float64)
    res_p = linprog(np.zeros(m), A_eq=A.T, b_eq=rhs, bounds=(0, None), method="highs")
    if res_p.success:
        return False, None
    for obj, A_ub, b_ub, A_eq, b_eq, bnd in [
        (rhs, -A, np.zeros(m), None, None, (-1.0, 1.0)),
        (np.zeros(s), -A, np.zeros(m), [rhs], [-1.0], (-1e4, 1e4)),
    ]:
        res_d = linprog(obj, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=bnd, method="highs")
        if res_d.success:
            c_flt = res_d.x
            for scale in [10**4, 10**6, 10**9, 10**12, 10**15]:
                c_int = [int(round(v * scale)) for v in c_flt]
                if verify_farkas_exact(A_int, rhs_int, c_int):
                    return True, c_int
    return find_exact_farkas_rational(A_int, rhs_int)


def exact_lp_bound(A_cols_int, rhs_int, obj_int, sense="min", n_max=100):
    """
    Certify an exact rational bound on sum(obj_int[j] * n[j]) subject to
    sum(A_cols_int[j] * n[j]) == rhs_int, n >= 0.
    For sense=='min': find y in Z^s, D > 0 such that y^T A_j <= D * obj_j for all j,
    giving sum(obj * n) >= (y^T rhs) / D!
    For sense=='max': find y in Z^s, D > 0 such that y^T A_j >= D * obj_j for all j,
    giving sum(obj * n) <= (y^T rhs) / D!
    """
    m = len(A_cols_int)
    s = len(rhs_int)
    A = np.array(A_cols_int, dtype=np.float64)  # m x s
    rhs = np.array(rhs_int, dtype=np.float64)
    c = np.array(obj_int, dtype=np.float64)
    if sense == "min":
        res = linprog(c, A_eq=A.T, b_eq=rhs, bounds=(0, None), method="highs")
        if not res.success:
            return None, None  # infeasible
        # Dual: max y^T rhs s.t. A y <= c
        res_d = linprog(-rhs, A_ub=A, b_ub=c, bounds=(None, None), method="highs")
        if res_d.success:
            y_flt = res_d.x
            for scale in [10**6, 10**9, 10**12]:
                y_int = [int(round(v * scale)) for v in y_flt]
                # Exact check: slack = max_j (y^T A_j - scale * obj_j)
                max_excess = max(
                    sum(y_int[r] * A_cols_int[j][r] for r in range(s)) - scale * obj_int[j]
                    for j in range(m)
                )
                # Remember sum n_j = n_max (implicit in row 0 = 2*1^T n = 2*n_max!)
                # Wait: if max_excess > 0, shift by adding (max_excess / 2) to y_int[0]?
                # Better: row 0 of A_cols_int is ALWAYS 2 (leading coeff of Psi is 2!), so adding k to y_int[0] adds 2*k to y^T A_j for all j!
                # Actually even simpler: only accept if max_excess <= 0, OR adjust y_int[0] when all A[j][0] == 2!
                if max_excess > 0 and all(A_cols_int[j][0] == 2 for j in range(m)):
                    shift0 = (max_excess + 1) // 2
                    y_int[0] -= shift0
                    max_excess = max(
                        sum(y_int[r] * A_cols_int[j][r] for r in range(s)) - scale * obj_int[j]
                        for j in range(m)
                    )
                if max_excess <= 0:
                    val = Fraction(sum(y_int[r] * rhs_int[r] for r in range(s)), scale)
                    return val, (y_int, scale)
        return Fraction(0), None
    else:
        res = linprog(-c, A_eq=A.T, b_eq=rhs, bounds=(0, None), method="highs")
        if not res.success:
            return None, None
        # Dual: min y^T rhs s.t. A y >= c  <=> -A y <= -c
        res_d = linprog(rhs, A_ub=-A, b_ub=-c, bounds=(None, None), method="highs")
        if res_d.success:
            y_flt = res_d.x
            for scale in [10**6, 10**9, 10**12]:
                y_int = [int(round(v * scale)) for v in y_flt]
                min_slack = min(
                    sum(y_int[r] * A_cols_int[j][r] for r in range(s)) - scale * obj_int[j]
                    for j in range(m)
                )
                if min_slack < 0 and all(A_cols_int[j][0] == 2 for j in range(m)):
                    shift0 = (-min_slack + 1) // 2
                    y_int[0] += shift0
                    min_slack = min(
                        sum(y_int[r] * A_cols_int[j][r] for r in range(s)) - scale * obj_int[j]
                        for j in range(m)
                    )
                if min_slack >= 0:
                    val = Fraction(sum(y_int[r] * rhs_int[r] for r in range(s)), scale)
                    return val, (y_int, scale)
        return Fraction(n_max), None


def certify_no_nonneg_int_solution_exact(A_cols_int, rhs_int, n_max):
    """
    100% exact Fraction proof that A^T n = rhs has NO solution n in Z_{>= 0}^m.
    First checks exact Farkas; if LP-feasible, computes exact RREF in QQ and
    exact dual-certified upper bounds on every free variable, then exhaustively
    tests all integer tuples in the exact box.
    """
    ok_f, cert_f = find_exact_farkas(A_cols_int, rhs_int)
    if ok_f:
        return True, {"method": "exact_farkas", "cert": cert_f}

    m = len(A_cols_int)
    s = len(rhs_int)
    # Build exact sympy Matrix in QQ: A_mat * n = rhs_vec
    A_mat = sp.Matrix([[sp.Rational(A_cols_int[j][r]) for j in range(m)] for r in range(s)])
    rhs_vec = sp.Matrix([sp.Rational(v) for v in rhs_int])
    aug = A_mat.row_join(rhs_vec)
    rref_mat, pivots = aug.rref()

    # Check inconsistency in RREF
    for r in range(rref_mat.rows):
        if all(rref_mat[r, j] == 0 for j in range(m)) and rref_mat[r, m] != 0:
            return True, {"method": "exact_rref_inconsistent"}

    piv_set = set(pivots)
    free_vars = [j for j in range(m) if j not in piv_set]

    # Convert RREF rows into Fraction equations: n[piv] = c0 - sum c_f * n[f]
    eqs = []
    for row_idx, pcol in enumerate(pivots):
        c0 = Fraction(int(rref_mat[row_idx, m].p), int(rref_mat[row_idx, m].q))
        coeffs = {}
        for fv in free_vars:
            val = rref_mat[row_idx, fv]
            if val != 0:
                coeffs[fv] = Fraction(int(val.p), int(val.q))
        eqs.append((pcol, c0, coeffs))

    if not free_vars:
        # Unique solution! Check in exact Fraction if all >= 0 and integer
        for pcol, c0, _ in eqs:
            if c0 < 0 or c0.denominator != 1:
                return True, {"method": "unique_rref_non_z_ge_0", "bad_var": pcol, "val": str(c0)}
        return False, None

    # Exact dual-certified bounds [lo_f, hi_f] on each free variable
    bounds = []
    for fv in free_vars:
        obj = [1 if j == fv else 0 for j in range(m)]
        lb_frac, _ = exact_lp_bound(A_cols_int, rhs_int, obj, sense="min", n_max=n_max)
        ub_frac, _ = exact_lp_bound(A_cols_int, rhs_int, obj, sense="max", n_max=n_max)
        if lb_frac is None or ub_frac is None:
            ok_fr, cert_fr = find_exact_farkas_rational(A_cols_int, rhs_int)
            if ok_fr:
                return True, {"method": "exact_farkas_rational", "cert": cert_fr}
            return False, None
        lo = max(0, math.ceil(lb_frac))
        hi = min(n_max, math.floor(ub_frac))
        if lo > hi:
            return True, {"method": "exact_dual_bound_empty", "fv": fv, "lo": lo, "hi": hi}
        bounds.append((fv, lo, hi))

    # Sort smallest range first and enumerate recursively in exact Fraction arithmetic
    bounds.sort(key=lambda t: t[2] - t[1])
    total_box = 1
    for _, lo, hi in bounds:
        total_box *= (hi - lo + 1)
    if total_box > 2_000_000:
        # Conservative fallback: do NOT claim elimination if box is huge
        return False, None

    assign = {}
    def search(idx):
        if idx == len(bounds):
            for pcol, c0, coeffs in eqs:
                val = c0 - sum(cf * assign[fv] for fv, cf in coeffs.items())
                if val < 0 or val.denominator != 1:
                    return False
            return True
        fv, lo, hi = bounds[idx]
        for v in range(lo, hi + 1):
            assign[fv] = v
            if search(idx + 1):
                return True
        return False

    if search(0):
        return False, None
    return True, {"method": "exact_rref_exhaustive_box", "free_vars": [b[0] for b in bounds], "box_size": total_box}


def passes_t42_sub(Dw_poly, Psi_poly, n_sub, s_shift, z, w):
    p_z = sp.Poly((Dw_poly.as_expr() * Psi_poly.as_expr()).subs(w, z - s_shift), z, domain=sp.ZZ)
    cs = [int(c) % 4 for c in p_z.all_coeffs()]
    if len(cs) < n_sub + 1:
        cs = [0] * (n_sub + 1 - len(cs)) + cs
    m = (n_sub - 1) // 2
    q_mod2 = [cs[2 * k + 1] % 2 for k in range(m + 1)]
    q2 = [0] * n_sub
    for i in range(m + 1):
        for j in range(m + 1):
            q2[i + j] = (q2[i + j] + q_mod2[i] * q_mod2[j]) % 4
    neg_n_mod4 = (-n_sub) % 4
    rhs = [0] * (n_sub + 1)
    for i in range(n_sub):
        rhs[i] = (rhs[i] + 2 * q2[i]) % 4
        rhs[i + 1] = (rhs[i + 1] + neg_n_mod4 * q2[i]) % 4
    return cs == rhs


def is_square_in_field_exact(A_expr, q_poly, var):
    A_rem = sp.rem(sp.Poly(A_expr, var, domain=sp.QQ), q_poly)
    if A_rem.is_zero:
        return True
    if q_poly.degree() == 1:
        r = sp.Rational(-q_poly.coeff_monomial(1), q_poly.LC())
        val = sp.Rational(A_rem.eval(r))
        if val < 0:
            return False
        return math.isqrt(val.p) ** 2 == val.p and math.isqrt(val.q) ** 2 == val.q
    t_sym = sp.Symbol("_tsym")
    alpha = sp.RootOf(q_poly.as_expr(), 0)
    expr_in_alpha = A_rem.as_expr().subs(var, alpha)
    p_t = sp.Poly(t_sym**2 - expr_in_alpha, t_sym, domain=sp.QQ.algebraic_field(alpha))
    fl = p_t.factor_list()[1]
    return len(fl) > 1 or fl[0][1] == 2


def prop61_kills_exact(Pw, deck_t42, n, d, c_shift, w, x):
    facs = sp.factor_list(Pw.as_expr())[1]
    roots_info = [(sp.Poly(fac, w), mult) for fac, mult in facs]
    RHS_poly_full = sp.Poly((w - (-5 - c_shift) // 2) ** (n - d), w, domain=sp.ZZ) * Pw
    Dw = sp.gcd(RHS_poly_full, RHS_poly_full.diff())
    Hw, _ = sp.div(RHS_poly_full, Dw)
    s = Hw.degree()
    quo, _ = sp.div(RHS_poly_full.diff(), Dw)
    RHS_poly = sp.Poly(2 * quo, w, domain=sp.ZZ)
    rhs = [int(v) for v in RHS_poly.all_coeffs()]
    while len(rhs) < s:
        rhs = [0] + rhs
    m_d = len(deck_t42)

    for fac, mf in roots_info:
        div_idx = [j for j, row in enumerate(deck_t42) if sp.rem(sp.Poly(row, w), fac).is_zero]
        if not div_idx:
            continue
        obj = [1 if j in div_idx else 0 for j in range(m_d)]
        lb_frac, lb_cert = exact_lp_bound(deck_t42, rhs, obj, sense="min", n_max=n)
        ub_frac, ub_cert = exact_lp_bound(deck_t42, rhs, obj, sense="max", n_max=n)
        if lb_frac is None or ub_frac is None or lb_cert is None or ub_cert is None:
            continue
        k_min = math.ceil(lb_frac)
        k_max = math.floor(ub_frac)
        if k_min < 1:
            continue
        all_k_fail = True
        for k in range(k_min, min(n, k_max) + 1):
            sz = n - k
            tr2_ub = sz * (sz - 1)
            tr2_lb = max(0, (n - d) - k) * 25
            for f2, m2 in roots_info:
                kept = m2 if f2 == fac else max(0, m2 - k)
                if kept > 0:
                    fx = sp.Poly(f2.as_expr().subs(w, (x - c_shift) / 2), x)
                    deg2 = fx.degree()
                    c1 = fx.coeff_monomial(x ** (deg2 - 1)) / fx.LC()
                    c2 = fx.coeff_monomial(x ** (deg2 - 2)) / fx.LC() if deg2 >= 2 else 0
                    tr2_lb += kept * int(c1**2 - 2 * c2)
            if tr2_lb <= tr2_ub:
                all_k_fail = False
                break
        if all_k_fail:
            return True, {"fac": sp.sstr(fac.as_expr()), "k_min": k_min, "k_max": k_max,
                          "lb_cert": lb_cert, "ub_cert": ub_cert}
    return False, None


def run_pipeline(in_deck, out_json):
    data = json.load(open(in_deck))
    d, n, c_shift = data["d"], data["n"], data["c"]
    w0 = (-5 - c_shift) // 2
    s_shift = (c_shift + 1) // 2
    z, w, x = sp.symbols("z w x")
    factor_w0 = sp.Poly((w - w0) ** (n - d), w, domain=sp.ZZ)

    stage_farkas1 = 0
    stage_t42_farkas = 0
    stage_kx = 0
    stage_prop61 = 0
    survivors = []
    certificates = []

    for cand in data["candidates"]:
        idx = cand["index"]
        s = cand["s"]
        b_in = cand["b"]
        deck = [[int(v) for v in row] for row in cand["deck"]]

        Pw = sp.Poly(sum(b_in[j] * w ** (d - j) for j in range(d + 1)), w, domain=sp.ZZ)
        Full_w = factor_w0 * Pw
        Dw = sp.gcd(Full_w, Full_w.diff())
        quo, rem = sp.div(Full_w.diff(), Dw)
        assert rem.is_zero
        RHS_poly = sp.Poly(2 * quo, w, domain=sp.ZZ)
        rhs = [int(v) for v in RHS_poly.all_coeffs()]
        while len(rhs) < s:
            rhs = [0] + rhs

        ok1, cert1 = find_exact_farkas(deck, rhs)
        if ok1:
            stage_farkas1 += 1
            certificates.append({"index": idx, "stage": "1-vertex_farkas", "rhs": rhs, "cert": cert1})
            continue

        deck_t42 = [row for row in deck if passes_t42_sub(Dw, sp.Poly(row, w, domain=sp.ZZ), n - 1, s_shift, z, w)]
        ok2, cert2 = find_exact_farkas(deck_t42, rhs)
        if ok2:
            stage_t42_farkas += 1
            certificates.append({"index": idx, "stage": "t42_farkas", "rhs": rhs, "cert": cert2})
            continue

        facs = sp.factor_list(Pw.as_expr())[1]
        simple_facs = [sp.Poly(fac, w) for fac, mult in facs if mult == 1]
        m_d = len(deck_t42)
        compat = [[True] * m_d for _ in range(m_d)]
        if simple_facs:
            def sqfree_int(val):
                if val == 0: return 0
                sgn = 1 if val > 0 else -1
                res = 1
                for pr, ex in sp.factorint(abs(val)).items():
                    if ex % 2 == 1: res *= pr
                return sgn * res
            Psi_list = [sum(deck_t42[i][k] * w ** (s - 1 - k) for k in range(s)) for i in range(m_d)]
            for q in simple_facs:
                # Group by (is_zero, sqfree(resultant)) first, then refine by exact field square check against class reps!
                norm_sf = [None if sp.rem(sp.Poly(P, w, domain=sp.QQ), q).is_zero
                           else sqfree_int(int(sp.resultant(q, sp.Poly(P, w, domain=sp.ZZ), w)))
                           for P in Psi_list]
                # For each norm_sf bucket, find exact square classes using representatives
                class_id = [None] * m_d
                buckets = {}
                for i, nsf in enumerate(norm_sf):
                    if nsf is None:
                        class_id[i] = -1  # 0 in K: compatible with all!
                        continue
                    reps = buckets.setdefault(nsf, [])
                    assigned = None
                    for rep_cid, rep_idx in reps:
                        if is_square_in_field_exact(Psi_list[i] * Psi_list[rep_idx], q, w):
                            assigned = rep_cid
                            break
                    if assigned is None:
                        assigned = len(reps) + sum(len(v) for k2, v in buckets.items() if k2 != nsf)
                        reps.append((assigned, i))
                    class_id[i] = assigned
                for i in range(m_d):
                    if class_id[i] == -1: continue
                    for j in range(i + 1, m_d):
                        if class_id[j] != -1 and class_id[i] != class_id[j]:
                            compat[i][j] = compat[j][i] = False

        cliques = []
        def bk(R, P):
            if not P:
                cliques.append(R)
                return
            u = P[0]
            for v in list(P):
                if compat[u][v] and v != u:
                    continue
                bk(R + [v], [xi for xi in P if xi != v and compat[v][xi]])
                P.remove(v)
        bk([], list(range(m_d)))

        any_clique_ok = False
        clique_proofs = []
        for cl in cliques:
            sub_cols = [deck_t42[j] for j in cl]
            no_sol, proof = certify_no_nonneg_int_solution_exact(sub_cols, rhs, n)
            if not no_sol:
                any_clique_ok = True
                break
            clique_proofs.append({"clique": cl, "proof": proof})
        if not any_clique_ok:
            stage_kx += 1
            certificates.append({"index": idx, "stage": "kx_rref_exact", "clique_proofs": clique_proofs})
            continue

        killed_p61, p61_cert = prop61_kills_exact(Pw, deck_t42, n, d, c_shift, w, x)
        if killed_p61:
            stage_prop61 += 1
            certificates.append({"index": idx, "stage": "prop61_exact", "cert": p61_cert})
            continue

        f_x = sp.factor(2**d * Pw.as_expr().subs(w, (x - c_shift) / 2))
        survivors.append({
            "index": idx,
            "s": s,
            "deck_t42_size": m_d,
            "b": b_in,
            "f_x_factored": sp.sstr(f_x),
        })

    out = {
        "d": d, "n": n, "total_stage1": len(data["candidates"]),
        "killed_farkas1": stage_farkas1,
        "killed_t42_farkas": stage_t42_farkas,
        "killed_kx_exact": stage_kx,
        "killed_prop61": stage_prop61,
        "survivors_count": len(survivors),
        "survivors": survivors,
        "certificates": certificates,
    }
    with open(out_json, "w") as f:
        json.dump(out, f, indent=2)
    print(f"({d},{n}): {len(data['candidates'])} -> -{stage_farkas1} (Farkas1) -> -{stage_t42_farkas} (T4.2+Farkas) -> -{stage_kx} (K^x+ExactRREF) -> -{stage_prop61} (Prop6.1Exact) => {len(survivors)} survivors")


if __name__ == "__main__":
    run_pipeline(sys.argv[1], sys.argv[2])
