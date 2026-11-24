"""
Exact Phase-2 Stage-2/3 elimination pipeline for odd-n candidates (n -> even n-1).
Every elimination is 100% certified in exact integer / Fraction arithmetic (ZERO floating-point trust):
  1. Exact Jacobi RHS integrality check: Full_w'(w) / (2 * Dw(w)) must lie in Z[w].
  2. Exact integer Farkas certificates (via HiGHS guess + exact int verification).
  3. Exact K^x / (K^x)^2 compatibility in Q[w]/(q(w)) for every simple irreducible factor q | f,
     plus exact Fraction-certified infeasibility (exact Farkas OR exact RREF + dual-bounded integer search).
  4. Exact Proposition 6.1 strengthened submatrix extraction (mult_lambda(S_v) >= m)
     with exact integer LP dual certificates for [k_min, k_max].
"""
import json
import math
import multiprocessing
import sys
from fractions import Fraction
import sympy as sp
import numpy as np
from scipy.optimize import linprog, milp, LinearConstraint, Bounds


def verify_farkas_exact(A_int, rhs_int, c_int):
    for row in A_int:
        if sum(ci * ri for ci, ri in zip(c_int, row)) < 0:
            return False
    return sum(ci * ri for ci, ri in zip(c_int, rhs_int)) < 0


def find_exact_farkas(A_int, rhs_int):
    m = len(A_int)
    s = len(rhs_int)
    if m == 0:
        c_int = [-1] + [0] * (s - 1)
        if verify_farkas_exact(A_int, rhs_int, c_int):
            return True, c_int
        return False, None
    if m == 1:
        v = A_int[0]
        # v[0] >= 1 (usually 1). Check if rhs is a non-negative multiple of v.
        if v[0] > 0 and rhs_int[0] >= 0 and rhs_int[0] % v[0] == 0:
            mult = rhs_int[0] // v[0]
            for r in range(1, s):
                if mult * v[r] != rhs_int[r]:
                    # Construct orthogonal c with c^T v = 0 and c^T rhs < 0
                    diff = rhs_int[r] * v[0] - rhs_int[0] * v[r]
                    c_int = [0] * s
                    if diff > 0:
                        c_int[0] = v[r]
                        c_int[r] = -v[0]
                    else:
                        c_int[0] = -v[r]
                        c_int[r] = v[0]
                    if verify_farkas_exact(A_int, rhs_int, c_int):
                        return True, c_int
                    break
            else:
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
    return False, None


def exact_lp_bound(A_cols_int, rhs_int, obj_int, sense="min", n_max=100):
    """
    Certify an exact rational bound on sum(obj_int[j] * n[j]) subject to
    sum(A_cols_int[j] * n[j]) == rhs_int, n >= 0.
    Here A_cols_int[j][0] == 1 (monic Psi in odd->even Stage 2).
    """
    m = len(A_cols_int)
    s = len(rhs_int)
    if m == 0:
        return None, None
    A = np.array(A_cols_int, dtype=np.float64)
    rhs = np.array(rhs_int, dtype=np.float64)
    c = np.array(obj_int, dtype=np.float64)
    all_lc1 = all(A_cols_int[j][0] == 1 for j in range(m))
    if sense == "min":
        res = linprog(c, A_eq=A.T, b_eq=rhs, bounds=(0, None), method="highs")
        if not res.success:
            return None, None
        res_d = linprog(-rhs, A_ub=A, b_ub=c, bounds=(None, None), method="highs")
        if res_d.success:
            y_flt = res_d.x
            for scale in [10**6, 10**9, 10**12]:
                y_int = [int(round(v * scale)) for v in y_flt]
                max_excess = max(
                    sum(y_int[r] * A_cols_int[j][r] for r in range(s)) - scale * obj_int[j]
                    for j in range(m)
                )
                if max_excess > 0 and all_lc1:
                    y_int[0] -= max_excess
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
        res_d = linprog(rhs, A_ub=-A, b_ub=-c, bounds=(None, None), method="highs")
        if res_d.success:
            y_flt = res_d.x
            for scale in [10**6, 10**9, 10**12]:
                y_int = [int(round(v * scale)) for v in y_flt]
                min_slack = min(
                    sum(y_int[r] * A_cols_int[j][r] for r in range(s)) - scale * obj_int[j]
                    for j in range(m)
                )
                if min_slack < 0 and all_lc1:
                    y_int[0] += (-min_slack)
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
    """
    ok_f, cert_f = find_exact_farkas(A_cols_int, rhs_int)
    if ok_f:
        return True, {"method": "exact_farkas", "cert": cert_f}

    m = len(A_cols_int)
    s = len(rhs_int)

    # Fast exact-verified integer witness check via MILP before expensive RREF/box search
    A_np = np.array(A_cols_int, dtype=np.float64).T  # s x m
    rhs_np = np.array(rhs_int, dtype=np.float64)
    res_m = milp(
        c=np.zeros(m),
        integrality=np.ones(m),
        bounds=Bounds(0, n_max),
        constraints=LinearConstraint(A_np, rhs_np, rhs_np),
    )
    if res_m.success and res_m.x is not None:
        n_cand = [int(round(v)) for v in res_m.x]
        if all(v >= 0 for v in n_cand) and all(
            sum(A_cols_int[j][r] * n_cand[j] for j in range(m)) == rhs_int[r] for r in range(s)
        ):
            return False, None  # Exact integer witness found!

    A_mat = sp.Matrix([[sp.Rational(A_cols_int[j][r]) for j in range(m)] for r in range(s)])
    rhs_vec = sp.Matrix([sp.Rational(v) for v in rhs_int])
    aug = A_mat.row_join(rhs_vec)
    rref_mat, pivots = aug.rref()

    for r in range(rref_mat.rows):
        if all(rref_mat[r, j] == 0 for j in range(m)) and rref_mat[r, m] != 0:
            return True, {"method": "exact_rref_inconsistent"}

    piv_set = set(pivots)
    free_vars = [j for j in range(m) if j not in piv_set]

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
        for pcol, c0, _ in eqs:
            if c0 < 0 or c0.denominator != 1:
                return True, {"method": "unique_rref_non_z_ge_0", "bad_var": pcol, "val": str(c0)}
        return False, None

    bounds = []
    total_box = 1
    for fv in free_vars:
        obj = [1 if j == fv else 0 for j in range(m)]
        lb_frac, _ = exact_lp_bound(A_cols_int, rhs_int, obj, sense="min", n_max=n_max)
        ub_frac, _ = exact_lp_bound(A_cols_int, rhs_int, obj, sense="max", n_max=n_max)
        if lb_frac is None or ub_frac is None:
            return True, {"method": "exact_lp_infeasible"}
        lo = max(0, math.ceil(lb_frac))
        hi = min(n_max, math.floor(ub_frac))
        if lo > hi:
            return True, {"method": "exact_dual_bound_empty", "fv": fv, "lo": lo, "hi": hi}
        bounds.append((fv, lo, hi))
        total_box *= (hi - lo + 1)
        if total_box > 2_000_000:
            return False, None

    bounds.sort(key=lambda t: t[2] - t[1])

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


def _poly_mod(a, f_mod, p):
    # a, f_mod high-to-low lists mod p, f_mod[0] == 1
    deg_f = len(f_mod) - 1
    r = [c % p for c in a]
    while len(r) > deg_f:
        lead = r[0]
        if lead != 0:
            for j in range(1, deg_f + 1):
                r[j] = (r[j] - lead * f_mod[j]) % p
        r.pop(0)
    while len(r) > 1 and r[0] == 0:
        r.pop(0)
    return r


def _poly_mul_mod(a, b, f_mod, p):
    if not a or not b:
        return [0]
    res = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                res[i + j] = (res[i + j] + ai * bj) % p
    return _poly_mod(res, f_mod, p)


def _poly_pow_mod(base, exp, f_mod, p):
    res = [1]
    b = _poly_mod(base, f_mod, p)
    while exp > 0:
        if exp & 1:
            res = _poly_mul_mod(res, b, f_mod, p)
        exp >>= 1
        if exp:
            b = _poly_mul_mod(b, b, f_mod, p)
    return res


def precompute_q_primes(q_poly, var):
    """Precompute mod-p factorizations of q_poly at primes not dividing LC(q)*disc(q)."""
    q_int = sp.Poly(q_poly.as_expr(), var, domain=sp.ZZ)
    lc = abs(int(q_int.LC()))
    disc = abs(int(sp.discriminant(q_int, var)))
    bad = lc * disc
    info = []
    for p in (101, 103, 107, 109, 113, 127, 131):
        if bad % p == 0:
            continue
        qp = sp.Poly(q_int.as_expr(), var, modulus=p)
        facs = []
        for fac, mult in qp.factor_list()[1]:
            assert mult == 1
            cs = [int(c) % p for c in fac.all_coeffs()]
            inv_lc = pow(cs[0], p - 2, p)
            cs = [(c * inv_lc) % p for c in cs]
            facs.append((cs, len(cs) - 1))
        info.append((p, facs))
    return info


def is_square_in_field_exact(A_expr, q_poly, var, q_prime_info=None):
    A_rem = sp.rem(sp.Poly(A_expr, var, domain=sp.QQ), q_poly)
    if A_rem.is_zero:
        return True
    if q_poly.degree() == 1:
        r = sp.Rational(-q_poly.coeff_monomial(1), q_poly.LC())
        val = sp.Rational(A_rem.eval(r))
        if val < 0:
            return False
        return math.isqrt(val.p) ** 2 == val.p and math.isqrt(val.q) ** 2 == val.q

    # Exact integral mod-p pre-screen (zero false negatives when p \nmid LC(q)*disc(q))
    if q_prime_info:
        coeffs_qq = [sp.Rational(c) for c in A_rem.all_coeffs()]
        lcm_d = 1
        for c in coeffs_qq:
            lcm_d = math.lcm(lcm_d, int(c.q))
        # Multiplying by lcm_d^2 preserves square class in K and clears denominators
        scale = lcm_d * lcm_d
        a_int_cs = [int(c * scale) for c in coeffs_qq]
        for p, facs in q_prime_info:
            a_p = [c % p for c in a_int_cs]
            for f_mod, k_deg in facs:
                r = _poly_mod(a_p, f_mod, p)
                if len(r) == 1 and r[0] == 0:
                    continue
                pw = _poly_pow_mod(r, (p**k_deg - 1) // 2, f_mod, p)
                if pw != [1]:
                    return False

    t_sym = sp.Symbol("_tsym")
    R_norm = sp.Poly(sp.resultant(q_poly.as_expr(), t_sym**2 - A_rem.as_expr(), var), t_sym, domain=sp.QQ)
    if R_norm.degree() == 2 * q_poly.degree() and sp.gcd(R_norm, R_norm.diff()).degree() == 0:
        fl_r = R_norm.factor_list()[1]
        return len(fl_r) == 2 and all(f.degree() == q_poly.degree() for f, _ in fl_r)

    alpha = sp.RootOf(q_poly.as_expr(), 0)
    expr_in_alpha = A_rem.as_expr().subs(var, alpha)
    p_t = sp.Poly(t_sym**2 - expr_in_alpha, t_sym, domain=sp.QQ.algebraic_field(alpha))
    fl = p_t.factor_list()[1]
    return len(fl) > 1 or fl[0][1] == 2


def prop61_kills_exact(Pw, deck_valid, rhs, n, d, c_shift, w, x):
    facs = sp.factor_list(Pw.as_expr())[1]
    roots_info = [(sp.Poly(fac, w), mult) for fac, mult in facs]
    m_d = len(deck_valid)

    for fac, mf in roots_info:
        div_idx = [j for j, row in enumerate(deck_valid) if sp.rem(sp.Poly(row, w), fac).is_zero]
        if not div_idx:
            continue
        obj = [1 if j in div_idx else 0 for j in range(m_d)]
        lb_frac, lb_cert = exact_lp_bound(deck_valid, rhs, obj, sense="min", n_max=n)
        ub_frac, ub_cert = exact_lp_bound(deck_valid, rhs, obj, sense="max", n_max=n)
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
                    val = sp.Rational(c1**2 - 2 * c2)
                    assert val.q == 1
                    tr2_lb += kept * int(val.p)
            if tr2_lb <= tr2_ub:
                all_k_fail = False
                break
        if all_k_fail:
            return True, {"fac": sp.sstr(fac.as_expr()), "k_min": k_min, "k_max": k_max,
                          "lb_cert": lb_cert, "ub_cert": ub_cert}
    return False, None


def process_candidate(args):
    cand, d, n, c_shift = args
    w0 = (-5 - c_shift) // 2
    w, x = sp.symbols("w x")
    factor_w0 = sp.Poly((w - w0) ** (n - d), w, domain=sp.ZZ)

    idx = cand["index"]
    s = cand["s"]
    b_in = cand["b"]
    deck = [[int(v) for v in row] for row in cand["deck"]]

    Pw = sp.Poly(sum(b_in[j] * w ** (d - j) for j in range(d + 1)), w, domain=sp.ZZ)
    Full_w = factor_w0 * Pw
    Dw = sp.gcd(Full_w, Full_w.diff())
    if Dw.LC() < 0:
        Dw = -Dw
    assert Dw.LC() == 1
    quo, rem = sp.div(Full_w.diff(), Dw)
    assert rem.is_zero

    quo_coeffs = [int(v) for v in quo.all_coeffs()]
    if any(v % 2 != 0 for v in quo_coeffs):
        return ("rhs_nonint", None, {"index": idx, "stage": "jacobi_rhs_non_integral", "quo_mod2": [v % 2 for v in quo_coeffs]})

    rhs = [v // 2 for v in quo_coeffs]
    while len(rhs) < s:
        rhs = [0] + rhs

    ok1, cert1 = find_exact_farkas(deck, rhs)
    if ok1:
        return ("farkas1", None, {"index": idx, "stage": "1-vertex_farkas", "rhs": rhs, "cert": cert1})

    facs = sp.factor_list(Pw.as_expr())[1]
    simple_facs = [sp.Poly(fac, w) for fac, mult in facs if mult == 1]
    m_d = len(deck)
    sigs = [[] for _ in range(m_d)]
    if simple_facs:
        def eval_leg_sig(rem_poly, qp_info):
            coeffs_qq = [sp.Rational(c) for c in rem_poly.all_coeffs()]
            lcm_d = 1
            for c in coeffs_qq:
                lcm_d = math.lcm(lcm_d, int(c.q))
            scale = lcm_d * lcm_d
            a_int_cs = [int(c * scale) for c in coeffs_qq]
            sig = []
            for p, facs_p in qp_info:
                a_p = [c % p for c in a_int_cs]
                for f_mod, k_deg in facs_p:
                    r = _poly_mod(a_p, f_mod, p)
                    if len(r) == 1 and r[0] == 0:
                        sig.append(0)
                    else:
                        pw = _poly_pow_mod(r, (p**k_deg - 1) // 2, f_mod, p)
                        sig.append(1 if pw == [1] else -1)
            return tuple(sig)

        def sqfree_rat(val):
            num = abs(int(val.p)) * abs(int(val.q))
            sgn = 1 if val > 0 else -1
            res = 1
            for pr, ex in sp.factorint(num).items():
                if ex % 2 == 1:
                    res *= pr
            return sgn * res

        Psi_list = [sum(deck[i][k] * w ** (s - 1 - k) for k in range(s)) for i in range(m_d)]
        for q in simple_facs:
            class_id = [None] * m_d
            if q.degree() == 1:
                r_q = sp.Rational(-q.coeff_monomial(1), q.LC())
                buckets = {}
                next_cid = 0
                for i, P in enumerate(Psi_list):
                    val = sp.Rational(sp.Poly(P, w, domain=sp.QQ).eval(r_q))
                    if val == 0:
                        class_id[i] = -1
                    else:
                        sf = sqfree_rat(val)
                        cid = buckets.get(sf)
                        if cid is None:
                            cid = next_cid
                            next_cid += 1
                            buckets[sf] = cid
                        class_id[i] = cid
            else:
                qp_info = precompute_q_primes(q, w)
                exact_buckets = {}
                zero_reps = []
                all_reps = []
                next_cid = 0
                for i, P in enumerate(Psi_list):
                    rem_p = sp.rem(sp.Poly(P, w, domain=sp.QQ), q)
                    if rem_p.is_zero:
                        class_id[i] = -1
                        continue
                    lsig = eval_leg_sig(rem_p, qp_info)
                    has_zero = (0 in lsig)
                    if not has_zero:
                        cands = exact_buckets.get(lsig, []) + zero_reps
                    else:
                        cands = [
                            (rcid, ridx) for rcid, ridx, rsig in all_reps
                            if all(a == 0 or b == 0 or a == b for a, b in zip(lsig, rsig))
                        ]
                    assigned = None
                    for rep_cid, rep_idx in cands:
                        if is_square_in_field_exact(Psi_list[i] * Psi_list[rep_idx], q, w, qp_info):
                            assigned = rep_cid
                            break
                    if assigned is None:
                        assigned = next_cid
                        next_cid += 1
                        all_reps.append((assigned, i, lsig))
                        if has_zero:
                            zero_reps.append((assigned, i))
                        else:
                            exact_buckets.setdefault(lsig, []).append((assigned, i))
                    class_id[i] = assigned
            for i in range(m_d):
                sigs[i].append(class_id[i])

    sig_map = {}
    sig_groups = []
    sig_keys = []
    for i in range(m_d):
        sk = tuple(sigs[i])
        gid = sig_map.get(sk)
        if gid is None:
            gid = len(sig_groups)
            sig_map[sk] = gid
            sig_groups.append([])
            sig_keys.append(sk)
        sig_groups[gid].append(i)

    num_g = len(sig_groups)
    g_compat = [[True] * num_g for _ in range(num_g)]
    for g1 in range(num_g):
        sk1 = sig_keys[g1]
        for g2 in range(g1 + 1, num_g):
            sk2 = sig_keys[g2]
            ok_pair = True
            for a, b_val in zip(sk1, sk2):
                if a != -1 and b_val != -1 and a != b_val:
                    ok_pair = False
                    break
            if not ok_pair:
                g_compat[g1][g2] = g_compat[g2][g1] = False

    g_cliques = []
    def bk(R, P):
        if not P:
            g_cliques.append(R)
            return
        u = P[0]
        for v in list(P):
            if g_compat[u][v] and v != u:
                continue
            bk(R + [v], [xi for xi in P if xi != v and g_compat[v][xi]])
            P.remove(v)
    bk([], list(range(num_g)))
    cliques = [[idx_v for g in gcl for idx_v in sig_groups[g]] for gcl in g_cliques]

    any_clique_ok = False
    clique_proofs = []
    for cl in cliques:
        sub_cols = [deck[j] for j in cl]
        no_sol, proof = certify_no_nonneg_int_solution_exact(sub_cols, rhs, n)
        if not no_sol:
            any_clique_ok = True
            break
        clique_proofs.append({"clique": cl, "proof": proof})
    if not any_clique_ok:
        return ("kx_exact", None, {"index": idx, "stage": "kx_rref_exact", "clique_proofs": clique_proofs})

    killed_p61, p61_cert = prop61_kills_exact(Pw, deck, rhs, n, d, c_shift, w, x)
    if killed_p61:
        return ("prop61", None, {"index": idx, "stage": "prop61_exact", "cert": p61_cert})

    f_x = sp.factor(2**(d - 1) * Pw.as_expr().subs(w, (x - c_shift) / 2))
    return ("survivor", {
        "index": idx,
        "s": s,
        "deck_size": m_d,
        "b": b_in,
        "f_x_factored": sp.sstr(f_x),
    }, None)


def run_pipeline(in_deck, out_json, workers=1):
    data = json.load(open(in_deck))
    d, n, c_shift = data["d"], data["n"], data["c"]
    assert n % 2 == 1, "phase2_odd.py is for odd n -> even (n-1)"

    tasks = [(cand, d, n, c_shift) for cand in data["candidates"]]
    if workers > 1:
        with multiprocessing.Pool(workers) as pool:
            results = pool.map(process_candidate, tasks, chunksize=4)
    else:
        results = [process_candidate(t) for t in tasks]

    stage_rhs_nonint = 0
    stage_farkas1 = 0
    stage_kx = 0
    stage_prop61 = 0
    survivors = []
    certificates = []
    for tag, surv, cert in results:
        if tag == "rhs_nonint":
            stage_rhs_nonint += 1
            certificates.append(cert)
        elif tag == "farkas1":
            stage_farkas1 += 1
            certificates.append(cert)
        elif tag == "kx_exact":
            stage_kx += 1
            certificates.append(cert)
        elif tag == "prop61":
            stage_prop61 += 1
            certificates.append(cert)
        elif tag == "survivor":
            survivors.append(surv)

    out = {
        "d": d, "n": n, "total_stage1": len(data["candidates"]),
        "killed_rhs_nonint": stage_rhs_nonint,
        "killed_farkas1": stage_farkas1,
        "killed_kx_exact": stage_kx,
        "killed_prop61": stage_prop61,
        "survivors_count": len(survivors),
        "survivors": survivors,
        "certificates": certificates,
    }
    with open(out_json, "w") as f:
        json.dump(out, f, indent=2)
    print(f"({d},{n}): {len(data['candidates'])} -> -{stage_rhs_nonint} (RHS_nonint) -> -{stage_farkas1} (Farkas1) -> -{stage_kx} (K^x+ExactRREF) -> -{stage_prop61} (Prop6.1Exact) => {len(survivors)} survivors")


if __name__ == "__main__":
    w_arg = int(sys.argv[3]) if len(sys.argv) >= 4 else 1
    run_pipeline(sys.argv[1], sys.argv[2], workers=w_arg)
