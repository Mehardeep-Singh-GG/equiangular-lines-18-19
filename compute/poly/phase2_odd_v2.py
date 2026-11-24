"""
Fast exact Phase-2 Stage-2/3 elimination pipeline for odd-n candidates (n -> even n-1).
Every elimination is 100% certified in exact integer / Fraction arithmetic (ZERO floating-point trust):
  1. Exact Jacobi RHS integrality check: Full_w'(w) / (2 * Dw(w)) in Z[w].
  2. Exact integer Farkas certificates (via HiGHS guess + exact int verification).
  3. Hierarchical exact K^x / (K^x)^2 compatibility in Q[w]/(q(w)) for simple factors q | f,
     using exact pseudo-remainder mod-p Legendre superset pruning before R_norm / QQ(alpha) refinement,
     plus exact Fraction RREF + dual-bounded exhaustive integer search.
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


def find_exact_farkas_rational(A_int, rhs_int):
    """Pure-Fraction Bland's-rule Phase-I Simplex returning an exact integer Farkas cert."""
    m = len(A_int)
    s = len(rhs_int)
    if m == 0:
        c_int = [-1] + [0] * (s - 1)
        return (True, c_int) if verify_farkas_exact(A_int, rhs_int, c_int) else (False, None)
    row_sgn = [1 if rhs_int[r] >= 0 else -1 for r in range(s)]
    # Tableau T of shape (s + 1) x (m + s + 1)
    T = [[Fraction(0)] * (m + s + 1) for _ in range(s + 1)]
    for r in range(s):
        sg = row_sgn[r]
        for j in range(m):
            T[r][j] = Fraction(sg * A_int[j][r])
        T[r][m + r] = Fraction(1)
        T[r][-1] = Fraction(sg * rhs_int[r])
    # Initial Phase-I objective row: -z + sum_r u_r = 0 => eliminate basic u_r by subtracting rows
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

    # Optimal Phase-I obj is -T[s][-1]
    if -T[s][-1] <= 0:
        return False, None
    # T[s][m+r] = 1 - y_r => y_r = 1 - T[s][m+r]; (-y)^T A_j >= 0, (-y)^T rhs < 0
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
    if m == 1:
        v = A_int[0]
        if v[0] > 0 and rhs_int[0] >= 0 and rhs_int[0] % v[0] == 0:
            mult = rhs_int[0] // v[0]
            for r in range(1, s):
                if mult * v[r] != rhs_int[r]:
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
    return find_exact_farkas_rational(A_int, rhs_int)


def exact_lp_bound(A_cols_int, rhs_int, obj_int, sense="min", n_max=100):
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
    ok_f, cert_f = find_exact_farkas(A_cols_int, rhs_int)
    if ok_f:
        return True, {"method": "exact_farkas", "cert": cert_f}

    m = len(A_cols_int)
    s = len(rhs_int)

    A_np = np.array(A_cols_int, dtype=np.float64).T
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
            return False, None

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
            ok_fr, cert_fr = find_exact_farkas_rational(A_cols_int, rhs_int)
            if ok_fr:
                return True, {"method": "exact_farkas_rational", "cert": cert_fr}
            return False, None
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


def _poly_mod_p(a, f_mod, p):
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


def _poly_mul_mod_p(a, b, f_mod, p):
    res = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                res[i + j] = (res[i + j] + ai * bj) % p
    return _poly_mod_p(res, f_mod, p)


def _poly_pow_mod_p(base, exp, f_mod, p):
    res = [1]
    b = _poly_mod_p(base, f_mod, p)
    while exp > 0:
        if exp & 1:
            res = _poly_mul_mod_p(res, b, f_mod, p)
        exp >>= 1
        if exp:
            b = _poly_mul_mod_p(b, b, f_mod, p)
    return res


def _pseudo_rem_sq_int(P_cs, q_cs):
    """
    Pure-integer pseudo-remainder of P(w) mod q(w), scaled by an EVEN power of q_cs[0]
    so the result lies in Z[w] and represents the EXACT SAME square class in Q[w]/(q(w)).
    """
    deg_q = len(q_cs) - 1
    q0 = q_cs[0]
    r = list(P_cs)
    steps = 0
    while len(r) > deg_q:
        lead = r[0]
        if lead != 0:
            for j in range(1, len(r)):
                r[j] *= q0
            for j in range(1, deg_q + 1):
                r[j] -= lead * q_cs[j]
            steps += 1
        r.pop(0)
    while len(r) > 1 and r[0] == 0:
        r.pop(0)
    if len(r) == 1 and r[0] == 0:
        return [0]
    if (steps & 1) == 1 and q0 != 1:
        r = [v * q0 for v in r]
    return r


def _eval_rat_sq_int(P_cs, a, b):
    """
    Evaluate P(a/b) * b^(2m) in pure Python int arithmetic (preserving Q^x/(Q^x)^2 class).
    P_cs is descending: P_cs[0]*w^deg + ... + P_cs[deg].
    """
    deg = len(P_cs) - 1
    even_deg = deg + (deg & 1)
    # b^even_deg * P(a/b) = sum_{k=0..deg} P_cs[k] * a^(deg-k) * b^(even_deg - deg + k)
    acc = 0
    b_pow = 1 if even_deg == deg else b
    a_pows = [1] * (deg + 1)
    for k in range(1, deg + 1):
        a_pows[k] = a_pows[k - 1] * a
    for k in range(deg + 1):
        acc += P_cs[k] * a_pows[deg - k] * b_pow
        b_pow *= b
    return acc


def precompute_q_primes(q_poly, var):
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


def is_square_in_field_int_rems(r1_cs, r2_cs, q_cs, q_poly, var, q_prime_info):
    """Exact check whether r1 * r2 is a square in Q[w]/(q(w)), given integer remainders."""
    if (len(r1_cs) == 1 and r1_cs[0] == 0) or (len(r2_cs) == 1 and r2_cs[0] == 0):
        return True
    # Product polynomial in Z[w], then pseudo-reduce mod q
    prod = [0] * (len(r1_cs) + len(r2_cs) - 1)
    for i, a in enumerate(r1_cs):
        if a:
            for j, b in enumerate(r2_cs):
                prod[i + j] += a * b
    rem_cs = _pseudo_rem_sq_int(prod, q_cs)
    if len(rem_cs) == 1 and rem_cs[0] == 0:
        return True

    if q_prime_info:
        for p, facs in q_prime_info:
            a_p = [c % p for c in rem_cs]
            for f_mod, k_deg in facs:
                r = _poly_mod_p(a_p, f_mod, p)
                if len(r) == 1 and r[0] == 0:
                    continue
                pw = _poly_pow_mod_p(r, (p**k_deg - 1) // 2, f_mod, p)
                if pw != [1]:
                    return False

    t_sym = sp.Symbol("_tsym")
    deg_r = len(rem_cs) - 1
    rem_expr = sum(rem_cs[k] * var ** (deg_r - k) for k in range(len(rem_cs)))
    R_norm = sp.Poly(sp.resultant(q_poly.as_expr(), t_sym**2 - rem_expr, var), t_sym, domain=sp.QQ)
    if R_norm.degree() == 2 * q_poly.degree() and sp.gcd(R_norm, R_norm.diff()).degree() == 0:
        fl_r = R_norm.factor_list()[1]
        return len(fl_r) == 2 and all(f.degree() == q_poly.degree() for f, _ in fl_r)

    alpha = sp.RootOf(q_poly.as_expr(), 0)
    expr_in_alpha = rem_expr.subs(var, alpha)
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
    simple_facs = sorted(
        [sp.Poly(fac, w, domain=sp.ZZ) for fac, mult in facs if mult == 1],
        key=lambda qp: qp.degree()
    )
    m_d = len(deck)

    def sqfree_int_fast(val):
        if val == 0:
            return 0
        sgn = 1 if val > 0 else -1
        num = abs(val)
        # Strip powers of 2 fast before SymPy factorint
        tz = (num & -num).bit_length() - 1
        num >>= tz
        res = 2 if (tz & 1) else 1
        if num > 1:
            for pr, ex in sp.factorint(num).items():
                if ex & 1:
                    res *= pr
        return sgn * res

    def eval_leg_sig_int(rem_cs, qp_info):
        sig = []
        for p, facs_p in qp_info:
            a_p = [c % p for c in rem_cs]
            for f_mod, k_deg in facs_p:
                r = _poly_mod_p(a_p, f_mod, p)
                if len(r) == 1 and r[0] == 0:
                    sig.append(0)
                else:
                    pw = _poly_pow_mod_p(r, (p**k_deg - 1) // 2, f_mod, p)
                    sig.append(1 if pw == [1] else -1)
        return tuple(sig)

    # Hierarchical K^x/(K^x)^2 pruning: smallest-degree factors first, LP/Farkas-prune supersets immediately!
    active_sets = [list(range(m_d))]
    proofs_collected = []

    for q in simple_facs:
        if not active_sets:
            break
        q_cs = [int(v) for v in q.all_coeffs()]
        if q_cs[0] < 0:
            q_cs = [-v for v in q_cs]
        deg_q = q.degree()

        next_sets = []
        if deg_q == 1:
            a_rt = -q_cs[1]
            b_rt = q_cs[0]
            for S in active_sets:
                zeros = []
                buckets = {}
                for idx_v in S:
                    val = _eval_rat_sq_int(deck[idx_v], a_rt, b_rt)
                    if val == 0:
                        zeros.append(idx_v)
                    else:
                        sf = sqfree_int_fast(val)
                        buckets.setdefault(sf, []).append(idx_v)
                cands_S = [b_list + zeros for b_list in buckets.values()] if buckets else ([zeros] if zeros else [])
                for sub in cands_S:
                    ok_f, cert_f = find_exact_farkas([deck[j] for j in sub], rhs)
                    if ok_f:
                        proofs_collected.append({"q": sp.sstr(q.as_expr()), "clique": sub, "proof": {"method": "exact_farkas", "cert": cert_f}})
                    else:
                        next_sets.append(sub)
        else:
            qp_info = precompute_q_primes(q, w)
            for S in active_sets:
                rems_S = {}
                zeros_exact = []
                zero_sig_list = []
                lsig_buckets = {}
                for idx_v in S:
                    r_cs = _pseudo_rem_sq_int(deck[idx_v], q_cs)
                    if len(r_cs) == 1 and r_cs[0] == 0:
                        zeros_exact.append(idx_v)
                    else:
                        rems_S[idx_v] = r_cs
                        lsig = eval_leg_sig_int(r_cs, qp_info)
                        if 0 in lsig:
                            zero_sig_list.append((idx_v, lsig))
                        else:
                            lsig_buckets.setdefault(lsig, []).append(idx_v)

                # First test zero-free lsig supersets (exact superset of any true class inside lsig_buckets[lsig] + compatible zero_sig + zeros_exact)
                z_all = [iv for iv, _ in zero_sig_list] + zeros_exact
                cands_S = []
                if lsig_buckets:
                    for lsig, b_list in lsig_buckets.items():
                        compat_zs = [iv for iv, zsig in zero_sig_list if all(a == 0 or a == b for a, b in zip(zsig, lsig))]
                        sup = b_list + compat_zs + zeros_exact
                        ok_f, cert_f = find_exact_farkas([deck[j] for j in sup], rhs)
                        if ok_f:
                            proofs_collected.append({"q": sp.sstr(q.as_expr()), "superset_clique": sup, "proof": {"method": "exact_farkas", "cert": cert_f}})
                        else:
                            cands_S.append((b_list, compat_zs))
                    # Also check if z_all alone could hold a solution when not covered by any b_list
                    if z_all:
                        ok_fz, cert_fz = find_exact_farkas([deck[j] for j in z_all], rhs)
                        if ok_fz:
                            proofs_collected.append({"q": sp.sstr(q.as_expr()), "superset_clique": z_all, "proof": {"method": "exact_farkas", "cert": cert_fz}})
                        else:
                            cands_S.append(([], [iv for iv, _ in zero_sig_list]))
                elif z_all:
                    ok_fz, cert_fz = find_exact_farkas([deck[j] for j in z_all], rhs)
                    if ok_fz:
                        proofs_collected.append({"q": sp.sstr(q.as_expr()), "superset_clique": z_all, "proof": {"method": "exact_farkas", "cert": cert_fz}})
                    else:
                        cands_S.append(([], [iv for iv, _ in zero_sig_list]))

                # Refine only the surviving LP-feasible buckets using exact R_norm / QQ(alpha)!
                for b_list, compat_zs in cands_S:
                    pool_nz = b_list + compat_zs
                    if not pool_nz:
                        if zeros_exact:
                            next_sets.append(zeros_exact)
                        continue
                    reps = []
                    classes = {}
                    next_cid = 0
                    for idx_v in pool_nz:
                        r_cs = rems_S[idx_v]
                        assigned = None
                        for rep_cid, rep_idx in reps:
                            if is_square_in_field_int_rems(r_cs, rems_S[rep_idx], q_cs, q, w, qp_info):
                                assigned = rep_cid
                                break
                        if assigned is None:
                            assigned = next_cid
                            next_cid += 1
                            reps.append((assigned, idx_v))
                            classes[assigned] = []
                        classes[assigned].append(idx_v)
                    for cid, cls_list in classes.items():
                        sub = cls_list + zeros_exact
                        ok_f, cert_f = find_exact_farkas([deck[j] for j in sub], rhs)
                        if ok_f:
                            proofs_collected.append({"q": sp.sstr(q.as_expr()), "clique": sub, "proof": {"method": "exact_farkas", "cert": cert_f}})
                        else:
                            next_sets.append(sub)
        active_sets = next_sets

    # Final exact RREF / dual-bounded integer check on any surviving active_sets
    if not active_sets:
        return ("kx_exact", None, {"index": idx, "stage": "kx_rref_exact", "clique_proofs": proofs_collected})

    any_ok = False
    for sub in active_sets:
        no_sol, proof = certify_no_nonneg_int_solution_exact([deck[j] for j in sub], rhs, n)
        if not no_sol:
            any_ok = True
            break
        proofs_collected.append({"clique": sub, "proof": proof})

    if not any_ok:
        return ("kx_exact", None, {"index": idx, "stage": "kx_rref_exact", "clique_proofs": proofs_collected})

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
    assert n % 2 == 1, "phase2_odd_v2.py is for odd n -> even (n-1)"

    tasks = [(cand, d, n, c_shift) for cand in data["candidates"]]
    if workers > 1:
        results = []
        with multiprocessing.Pool(workers) as pool:
            for k, res in enumerate(pool.imap(process_candidate, tasks, chunksize=4), 1):
                results.append(res)
                if k % 100 == 0 or k == len(tasks):
                    print(f"  Done {k}/{len(tasks)}", flush=True)
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
