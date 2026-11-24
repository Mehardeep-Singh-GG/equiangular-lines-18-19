"""
Exact, float-free, pure square-class Stage-2 (K^x + Theorem 7.2 Galois + Prop 6.1)
and Stage-3 (59 -> 58 -> 57 2v-Jacobi + 1v derivative Farkas/RREF) solver
for the 19 remaining (18, 59) candidates.
"""

import hashlib
import json
import math
import sys
import time
from fractions import Fraction
import sympy as sp

from phase2_even import (
    exact_lp_bound,
    find_exact_farkas_rational,
    is_square_in_field_exact,
)
from stage3_solver import (
    check_stage3_for_counts,
    solve_2v_jacobi_pair,
    strict_upper_bound_roots,
    _poly_coeffs_fixed_len,
    _is_rat_square,
)


def sqfree_rat(q_frac):
    """Exact squarefree integer signature of a nonzero rational a/b = sqfree(a*b)."""
    num = q_frac.numerator * q_frac.denominator
    if num == 0:
        return 0
    sgn = 1 if num > 0 else -1
    val = abs(num)
    tz = (val & -val).bit_length() - 1
    val >>= tz
    res = 2 if (tz & 1) else 1
    if val > 1:
        for pr, ex in sp.factorint(val).items():
            if ex & 1:
                res *= pr
    return sgn * res


def norm_in_field_qq(rem_poly, q_monic, w_sym):
    """Exact N_{K/Q}(rem_poly) = Res_w(q_monic, rem_poly) in Fraction."""
    if rem_poly.is_zero:
        return Fraction(0)
    res = sp.resultant(q_monic, sp.Poly(rem_poly, w_sym, domain=sp.QQ), w_sym)
    r_q = sp.Rational(res)
    return Fraction(r_q.p, r_q.q)


def is_square_quad_exact(rem_poly, q_monic):
    """
    Exact closed-form square test in Q[w]/(w^2 - c1*w + c0) without SymPy algebraic_field.
    Returns True iff rem_poly(w) is a square in K.
    """
    c1 = Fraction(-q_monic.nth(1).p, q_monic.nth(1).q)
    c0 = Fraction(q_monic.nth(0).p, q_monic.nth(0).q)
    D = c1 * c1 / 4 - c0  # theta^2 = D, w = theta + c1/2
    r1 = Fraction(rem_poly.nth(1).p, rem_poly.nth(1).q) if rem_poly.degree() >= 1 else Fraction(0)
    r0 = Fraction(rem_poly.nth(0).p, rem_poly.nth(0).q)
    # r1*w + r0 = (r0 + r1*c1/2) + r1*theta = A + B*theta
    A = r0 + r1 * c1 / 2
    B = r1
    if B == 0:
        return (_is_rat_square(A) is not None) or (_is_rat_square(A / D) is not None)
    N = A * A - D * B * B
    s = _is_rat_square(N)
    if s is None:
        return False
    return (_is_rat_square((A + s) / 2) is not None) or (_is_rat_square((A - s) / 2) is not None)


def bucket_indices_exact(deck, sub_indices, q_fac, w_sym):
    """
    Exact square-class partitioning in Q[w]/(q_fac) using norm-squarefree grouping
    + exact quadratic closed form (deg=2) or algebraic_field factor_list (deg>=3).
    NEVER uses modular/prime signatures (zero false splits).
    """
    q_mon = sp.Poly(q_fac, w_sym, domain=sp.QQ).monic()
    deg_q = q_mon.degree()
    zeros = []
    norm_groups = {}
    rems = {}

    for j in sub_indices:
        pj = sp.Poly(deck[j], w_sym, domain=sp.QQ)
        rem = sp.rem(pj, q_mon)
        if rem.is_zero:
            zeros.append(j)
            continue
        rems[j] = rem
        if deg_q == 1:
            lam = -q_mon.nth(0)
            val = Fraction(rem.eval(lam).p, rem.eval(lam).q)
            sf = sqfree_rat(val)
        else:
            nv = norm_in_field_qq(rem, q_mon, w_sym)
            sf = sqfree_rat(nv)
        norm_groups.setdefault(sf, []).append(j)

    if deg_q == 1:
        return zeros, list(norm_groups.values())

    buckets = []
    for sf, grp in norm_groups.items():
        if deg_q == 2:
            sub_b = []
            for j in grp:
                placed = False
                for b in sub_b:
                    rep_rem = rems[b[0]]
                    prod_rem = sp.rem(rems[j] * rep_rem, q_mon)
                    if is_square_quad_exact(prod_rem, q_mon):
                        b.append(j)
                        placed = True
                        break
                if not placed:
                    sub_b.append([j])
            buckets.extend(sub_b)
        else:
            sub_b = []
            for j in grp:
                placed = False
                for b in sub_b:
                    if is_square_in_field_exact((rems[j] * rems[b[0]]).as_expr(), q_mon, w_sym):
                        b.append(j)
                        placed = True
                        break
                if not placed:
                    sub_b.append([j])
            buckets.extend(sub_b)
    return zeros, buckets


def galois_rows_for_bucket(deck, bucket_idxs, q_fac, w_sym):
    q_mon = sp.Poly(q_fac, w_sym, domain=sp.QQ).monic()
    e = q_mon.degree()
    alpha = sp.RootOf(q_mon.as_expr(), 0)
    K_dom = sp.QQ.algebraic_field(alpha)
    t_sym = sp.Symbol("_tgal")

    e_sym = [(-1) ** k * sp.Rational(q_mon.nth(e - k)) for k in range(1, e + 1)]
    ps = [sp.Rational(e)]
    for k in range(1, 2 * e):
        val = sum((-1) ** (j - 1) * e_sym[j - 1] * ps[k - j] for j in range(1, min(k, e + 1)))
        if k <= e:
            val += (-1) ** (k - 1) * k * e_sym[k - 1]
        ps.append(val)

    def tr_poly(p_q):
        rem = sp.rem(p_q, q_mon)
        return sum(sp.Rational(rem.nth(k)) * ps[k] for k in range(e))

    u0 = bucket_idxs[0]
    p_u0 = sp.Poly(deck[u0], w_sym, domain=sp.QQ)
    inv_u0, _, g_g = sp.gcdex(p_u0, q_mon)
    inv_u0 = sp.rem(inv_u0, q_mon)

    rows_dict = {}
    for j in bucket_idxs:
        pj = sp.Poly(deck[j], w_sym, domain=sp.QQ)
        ratio = sp.rem(pj * inv_u0, q_mon)
        p_t = sp.Poly(t_sym**2 - ratio.as_expr().subs(w_sym, alpha), t_sym, domain=K_dom)
        fl = p_t.factor_list()[1]
        fac0 = fl[0][0]
        val = -fac0.nth(0) / fac0.LC()
        anp = K_dom.from_sympy(val)
        ru = sp.Poly([sp.Rational(c.numerator, c.denominator) for c in anp.rep], w_sym, domain=sp.QQ)
        ru2 = sp.rem(ru * ru, q_mon)
        assert ru2 == ratio

        row_g = []
        for a_p in range(e):
            wa_ru = sp.rem(sp.Poly(w_sym**a_p, w_sym, domain=sp.QQ) * ru, q_mon)
            ta = tr_poly(wa_ru)
            for b_p in range(a_p, e):
                wb_ru = sp.rem(sp.Poly(w_sym**b_p, w_sym, domain=sp.QQ) * ru, q_mon)
                tb = tr_poly(wb_ru)
                wab_ru2 = sp.rem(sp.Poly(w_sym ** (a_p + b_p), w_sym, domain=sp.QQ) * ru2, q_mon)
                tab = tr_poly(wab_ru2)
                row_g.append(Fraction(ta.p, ta.q) * Fraction(tb.p, tb.q) - Fraction(tab.p, tab.q))
        rows_dict[j] = row_g
    return rows_dict


def exact_lp_bound_any(A_cols_int, rhs_int, obj_int, sense="min", n_max=100):
    """
    Exact rational LP bound on sum(obj_int[j]*n[j]) s.t. sum(A_cols_int[j]*n[j]) == rhs_int, n >= 0.
    Handles any constant row0 (1 for odd n, 2 for even n) and falls back to exact Fraction Simplex.
    """
    import numpy as np
    from scipy.optimize import linprog
    m = len(A_cols_int)
    s = len(rhs_int)
    if m == 0:
        return None
    A = np.array(A_cols_int, dtype=np.float64)
    rhs_arr = np.array(rhs_int, dtype=np.float64)
    c = np.array(obj_int, dtype=np.float64)
    row0_c = A_cols_int[0][0]
    same_row0 = (row0_c > 0) and all(A_cols_int[j][0] == row0_c for j in range(m))

    if sense == "min":
        res = linprog(c, A_eq=A.T, b_eq=rhs_arr, bounds=(0, None), method="highs")
        if res.success:
            res_d = linprog(-rhs_arr, A_ub=A, b_ub=c, bounds=(None, None), method="highs")
            if res_d.success:
                y_flt = res_d.x
                for scale in [10**6, 10**9, 10**12]:
                    y_int = [int(round(v * scale)) for v in y_flt]
                    max_ex = max(sum(y_int[r] * A_cols_int[j][r] for r in range(s)) - scale * obj_int[j] for j in range(m))
                    if max_ex > 0 and same_row0:
                        y_int[0] -= (max_ex + row0_c - 1) // row0_c
                        max_ex = max(sum(y_int[r] * A_cols_int[j][r] for r in range(s)) - scale * obj_int[j] for j in range(m))
                    if max_ex <= 0:
                        return Fraction(sum(y_int[r] * rhs_int[r] for r in range(s)), scale)
    else:
        res = linprog(-c, A_eq=A.T, b_eq=rhs_arr, bounds=(0, None), method="highs")
        if res.success:
            res_d = linprog(rhs_arr, A_ub=-A, b_ub=-c, bounds=(None, None), method="highs")
            if res_d.success:
                y_flt = res_d.x
                for scale in [10**6, 10**9, 10**12]:
                    y_int = [int(round(v * scale)) for v in y_flt]
                    min_sl = min(sum(y_int[r] * A_cols_int[j][r] for r in range(s)) - scale * obj_int[j] for j in range(m))
                    if min_sl < 0 and same_row0:
                        y_int[0] += (-min_sl + row0_c - 1) // row0_c
                        min_sl = min(sum(y_int[r] * A_cols_int[j][r] for r in range(s)) - scale * obj_int[j] for j in range(m))
                    if min_sl >= 0:
                        return Fraction(sum(y_int[r] * rhs_int[r] for r in range(s)), scale)

    # Exact Fraction Bland-rule Phase-I + Phase-II Simplex fallback
    row_sgn = [1 if rhs_int[r] >= 0 else -1 for r in range(s)]
    T = [[Fraction(0)] * (m + s + 1) for _ in range(s + 1)]
    for r in range(s):
        sg = row_sgn[r]
        for j in range(m):
            T[r][j] = Fraction(sg * A_cols_int[j][r])
        T[r][m + r] = Fraction(1)
        T[r][-1] = Fraction(sg * rhs_int[r])
    for r in range(s):
        T[s][m + r] = Fraction(1)
        for col in range(m + s + 1):
            T[s][col] -= T[r][col]
    basis = [m + r for r in range(s)]

    def pivot_loop(ncols):
        while True:
            enter = -1
            for col in range(ncols):
                if T[s][col] < 0:
                    enter = col
                    break
            if enter == -1:
                break
            leave = -1
            best_r = None
            for r in range(s):
                a = T[r][enter]
                if a > 0:
                    ratio = T[r][-1] / a
                    if leave == -1 or ratio < best_r or (ratio == best_r and basis[r] < basis[leave]):
                        leave = r
                        best_r = ratio
            if leave == -1:
                return False
            piv = T[leave][enter]
            for col in range(len(T[0])):
                T[leave][col] /= piv
            for r in range(s + 1):
                if r != leave and T[r][enter] != 0:
                    fac = T[r][enter]
                    for col in range(len(T[0])):
                        T[r][col] -= fac * T[leave][col]
            basis[leave] = enter
        return True

    pivot_loop(m + s)
    if -T[s][-1] > 0:
        return None
    # Drop artificial columns: keep columns 0..m-1 and RHS
    # Actually pivot out any remaining artificials if zero, or easier: keep Phase-II on non-artificials
    for r in range(s):
        if basis[r] >= m:
            for col in range(m):
                if T[r][col] != 0:
                    piv = T[r][col]
                    for c2 in range(len(T[0])): T[r][c2] /= piv
                    for r2 in range(s + 1):
                        if r2 != r and T[r2][col] != 0:
                            fac = T[r2][col]
                            for c2 in range(len(T[0])): T[r2][c2] -= fac * T[r][c2]
                    basis[r] = col
                    break
    # Set Phase-II objective: min c^T x (or -c^T x)
    sgn_obj = 1 if sense == "min" else -1
    T2 = [T[r][:m] + [T[r][-1]] for r in range(s)] + [[Fraction(sgn_obj * obj_int[j]) for j in range(m)] + [Fraction(0)]]
    for r in range(s):
        if basis[r] < m and T2[s][basis[r]] != 0:
            fac = T2[s][basis[r]]
            for col in range(m + 1):
                T2[s][col] -= fac * T2[r][col]
    while True:
        enter = -1
        for col in range(m):
            if T2[s][col] < 0:
                enter = col
                break
        if enter == -1:
            break
        leave = -1
        best_r = None
        for r in range(s):
            a = T2[r][enter]
            if a > 0:
                ratio = T2[r][-1] / a
                if leave == -1 or ratio < best_r or (ratio == best_r and basis[r] < basis[leave]):
                    leave = r
                    best_r = ratio
        if leave == -1:
            return Fraction(0) if sense == "min" else Fraction(n_max)
        piv = T2[leave][enter]
        for col in range(m + 1):
            T2[leave][col] /= piv
        for r in range(s + 1):
            if r != leave and T2[r][enter] != 0:
                fac = T2[r][enter]
                for col in range(m + 1):
                    T2[r][col] -= fac * T2[leave][col]
        basis[leave] = enter
    opt = -T2[s][-1]
    return opt if sense == "min" else -opt


def enum_cone_sols(deck, act_cols, extra_rows, rhs, n):
    """Enumerate all exact non-negative integer solutions inside a surviving cone."""
    m = len(act_cols)
    sub_deck = [deck[j] for j in act_cols]
    s = len(rhs)

    rows_int = []
    rhs_int = []
    for r_idx in range(s):
        rows_int.append([int(sub_deck[j][r_idx]) for j in range(m)])
        rhs_int.append(int(rhs[r_idx]))
    for row_f, rhs_f in extra_rows:
        lcm_d = rhs_f.denominator
        for j in act_cols:
            lcm_d = math.lcm(lcm_d, row_f[j].denominator)
        rows_int.append([int(row_f[j] * lcm_d) for j in act_cols])
        rhs_int.append(int(rhs_f * lcm_d))

    sub_aug = [[rows_int[r][j] for r in range(len(rows_int))] for j in range(m)]
    M = sp.Matrix([[sp.Rational(rows_int[r][j]) for j in range(m)] + [sp.Rational(rhs_int[r])] for r in range(len(rows_int))])
    R, pivots = M.rref()
    for r in range(R.rows):
        if all(R[r, c] == 0 for c in range(m)) and R[r, m] != 0:
            return []

    piv_set = set(pivots)
    free_cols = [c for c in range(m) if c not in piv_set]
    eqs = []
    for r, pc in enumerate(pivots):
        c0 = Fraction(R[r, m].p, R[r, m].q)
        coeffs = {fc: Fraction(R[r, fc].p, R[r, fc].q) for fc in free_cols if R[r, fc] != 0}
        eqs.append((pc, c0, coeffs))

    bounds = []
    for fc in free_cols:
        obj = [1 if j == fc else 0 for j in range(m)]
        lb = exact_lp_bound_any(sub_aug, rhs_int, obj, sense="min", n_max=n)
        ub = exact_lp_bound_any(sub_aug, rhs_int, obj, sense="max", n_max=n)
        if lb is None or ub is None:
            return []
        lo = math.ceil(lb)
        hi = math.floor(ub)
        if lo > hi:
            return []
        bounds.append((fc, max(0, lo), min(n, hi)))
    bounds.sort(key=lambda t: t[2] - t[1])

    box = 1
    for _, lo, hi in bounds:
        box *= (hi - lo + 1)
    if box > 1_000_000:
        return None

    sols = []
    assign = {}

    def dfs(i, rem_sum):
        if rem_sum < 0:
            return
        if i == len(bounds):
            vec_sub = [0] * m
            for fv, v in assign.items():
                vec_sub[fv] = v
            for pc, c0, coeffs in eqs:
                val = c0 - sum(cf * assign[fv] for fv, cf in coeffs.items())
                if val < 0 or val.denominator != 1:
                    return
                vec_sub[pc] = int(val)
            if sum(vec_sub) == n:
                full_vec = [0] * len(deck)
                for loc_j, glob_j in enumerate(act_cols):
                    full_vec[glob_j] = vec_sub[loc_j]
                sols.append(full_vec)
            return
        fv, lo, hi = bounds[i]
        hi_eff = min(hi, rem_sum)
        for v in range(lo, hi_eff + 1):
            assign[fv] = v
            dfs(i + 1, rem_sum - v)

    dfs(0, n)
    return sols


def prop61_sol_ok(vec, deck, Pw, n, d, c_shift, w, x):
    facs = sp.factor_list(Pw.as_expr())[1]
    roots_info = [(sp.Poly(fac, w), mult) for fac, mult in facs]
    for fac, mf in roots_info:
        k = sum(vec[j] for j, row in enumerate(deck) if sp.rem(sp.Poly(row, w), fac).is_zero)
        if k < 1:
            continue
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
        if tr2_lb > tr2_ub:
            return False
    return True


def sv_kx_galois_check(chi_S, Gcd_x, Gcd2_x, Sim_x, Mult_rad_x, g_list, counts_n, n, x_sym, Q_cache):
    """Test exact K^x + Theorem 7.2 Galois orthogonality on S_v for every active vertex v."""
    x_max_ub = strict_upper_bound_roots(chi_S, x_sym)
    deg_q = (n - 2) - Gcd2_x.degree()
    act_ids = [j for j, cnt in enumerate(counts_n) if cnt > 0]
    for v in act_ids:
        chi_Sv = Gcd_x * g_list[v]
        Gv = sp.gcd(chi_Sv, chi_Sv.diff())
        if Gv.LC() < 0:
            Gv = -Gv
        sim_v_facs = sorted(
            [sp.Poly(f, x_sym, domain=sp.ZZ) for f, m in sp.factor_list(chi_Sv.as_expr())[1] if m == 1],
            key=lambda p: p.degree(),
        )
        if not sim_v_facs:
            continue
        col_q_polys = []
        col_gv_polys = []
        block_eqs = []
        for b in act_ids:
            nb_rem = counts_n[b] - (1 if b == v else 0)
            if nb_rem <= 0:
                continue
            kp = (v, b) if v <= b else (b, v)
            if kp not in Q_cache:
                res = solve_2v_jacobi_pair(g_list[kp[0]], g_list[kp[1]], Sim_x, Mult_rad_x, Gcd2_x, n, x_sym, x_max_ub=x_max_ub)
                uniq = {}
                for s2_val, q_uv, _ in res:
                    key = tuple(int(val) for val in q_uv.all_coeffs())
                    if key not in uniq:
                        uniq[key] = {"q_poly": q_uv, "s2_vals": [s2_val]}
                Q_cache[kp] = list(uniq.values())
                if kp[0] != kp[1]:
                    Q_cache[(kp[1], kp[0])] = Q_cache[kp]
            sc = len(col_q_polys)
            for item in Q_cache[(v, b)]:
                q_uv = item["q_poly"]
                col_q_polys.append(q_uv)
                gv_u, _ = sp.div(Gcd2_x * q_uv, Gv)
                col_gv_polys.append([int(c) for c in gv_u.all_coeffs()])
            block_eqs.append((sc, len(col_q_polys), nb_rem))

        rhs_p, _ = sp.div(chi_Sv.diff(), Gcd2_x)
        rhs_cs = _poly_coeffs_fixed_len(rhs_p, deg_q + 1)
        base_rows = [[_poly_coeffs_fixed_len(q_uv, deg_q + 1)[r_i] for q_uv in col_q_polys] for r_i in range(deg_q + 1)]
        base_rhs = list(rhs_cs)
        for sc, ec, nb_rem in block_eqs:
            base_rows.append([1 if sc <= c < ec else 0 for c in range(len(col_q_polys))])
            base_rhs.append(nb_rem)

        max_l = max(len(r) for r in col_gv_polys)
        col_gv_pad = [[0] * (max_l - len(r)) + r for r in col_gv_polys]
        cones_v = [(list(range(len(col_q_polys))), [])]
        for qf in sim_v_facs:
            nxt_v = []
            for sub_v, ex_v in cones_v:
                zv, bvs = bucket_indices_exact(col_gv_pad, sub_v, qf, x_sym)
                cand_groups = [sorted(zv + b) for b in bvs] if bvs else ([sorted(zv)] if zv else [])
                for idx_g, act_v in enumerate(cand_groups):
                    nex_v = list(ex_v)
                    if qf.degree() >= 2 and bvs:
                        gal = galois_rows_for_bucket(col_gv_pad, bvs[idx_g], qf, x_sym)
                        for g_i in range(qf.degree() * (qf.degree() + 1) // 2):
                            nex_v.append(([gal[j][g_i] if j in gal else Fraction(0) for j in range(len(col_q_polys))], Fraction(0)))
                    cols_T = [[base_rows[r][c] for r in range(len(base_rows))] for c in act_v]
                    rhs_all = list(base_rhs)
                    for row_f, rhs_f in nex_v:
                        lcm_d = rhs_f.denominator
                        for j in act_v:
                            lcm_d = math.lcm(lcm_d, row_f[j].denominator)
                        for loc_j, glob_j in enumerate(act_v):
                            cols_T[loc_j].append(int(row_f[glob_j] * lcm_d))
                        rhs_all.append(int(rhs_f * lcm_d))
                    inf, _ = find_exact_farkas_rational(cols_T, rhs_all)
                    if not inf:
                        nxt_v.append((act_v, nex_v))
            cones_v = nxt_v
        if not cones_v:
            return True, {"method": "sv_kx_galois_farkas", "v_type": v, "counts_n": list(counts_n)}
    return False, None


def solve_candidate(cand, n, d_dim, c_sh, run_stage3=True, run_sv_galois=True):
    t0 = time.time()
    w0 = (-5 - c_sh) // 2
    w, x = sp.symbols("w x")
    idx = cand["index"]
    s = cand["s"]
    deck = [[int(v) for v in row] for row in cand["deck"]]

    Pw = sp.Poly(sum(cand["b"][j] * w ** (d_dim - j) for j in range(d_dim + 1)), w, domain=sp.ZZ)
    Full_w = sp.Poly((w - w0) ** (n - d_dim), w, domain=sp.ZZ) * Pw
    Dw = sp.gcd(Full_w, Full_w.diff())
    if Dw.LC() < 0:
        Dw = -Dw
    quo, _ = sp.div(Full_w.diff(), Dw)
    rhs = [int(v) // 2 for v in quo.all_coeffs()]
    while len(rhs) < s:
        rhs = [0] + rhs

    chi_S = sp.Poly(sp.expand(2 ** (n - 1) * Full_w.as_expr().subs(w, (x - c_sh) / 2)), x, domain=sp.ZZ)
    Gcd_x = sp.gcd(chi_S, chi_S.diff())
    if Gcd_x.LC() < 0:
        Gcd_x = -Gcd_x
    Gcd2_x = sp.gcd(Gcd_x, Gcd_x.diff())
    if Gcd2_x.LC() < 0:
        Gcd2_x = -Gcd2_x

    facs_x = sp.factor_list(chi_S.as_expr())[1]
    Sim_x = sp.Poly(1, x, domain=sp.ZZ)
    Mult_rad_x = sp.Poly(1, x, domain=sp.ZZ)
    for fac, mult in facs_x:
        fp = sp.Poly(fac, x, domain=sp.ZZ)
        if mult == 1:
            Sim_x = Sim_x * fp
        else:
            Mult_rad_x = Mult_rad_x * fp
    diff = (s - 2) - Sim_x.degree()

    simple_facs = sorted(
        [sp.Poly(f, w, domain=sp.ZZ) for f, m in sp.factor_list(Pw.as_expr())[1] if m == 1],
        key=lambda p: p.degree(),
    )

    cones = [(list(range(len(deck))), [])]
    for q in simple_facs:
        nxt_cones = []
        for sub, extra_rows in cones:
            zeros, buckets = bucket_indices_exact(deck, sub, q, w)
            for b in buckets:
                act = sorted(zeros + b)
                new_extra = list(extra_rows)
                if q.degree() >= 2:
                    gal = galois_rows_for_bucket(deck, b, q, w)
                    n_gal = q.degree() * (q.degree() + 1) // 2
                    for g_i in range(n_gal):
                        row_full = [gal[j][g_i] if j in gal else Fraction(0) for j in range(len(deck))]
                        new_extra.append((row_full, Fraction(0)))
                cols_T = [list(deck[j]) for j in act]
                rhs_all = list(rhs)
                for row_f, rhs_f in new_extra:
                    lcm_d = rhs_f.denominator
                    for j in act:
                        lcm_d = math.lcm(lcm_d, row_f[j].denominator)
                    for loc_j, glob_j in enumerate(act):
                        cols_T[loc_j].append(int(row_f[glob_j] * lcm_d))
                    rhs_all.append(int(rhs_f * lcm_d))
                inf, _ = find_exact_farkas_rational(cols_T, rhs_all)
                if not inf:
                    nxt_cones.append((act, new_extra))
        cones = nxt_cones

    g_list = [
        sp.Poly(sp.expand(2 ** (s - 1) * sum(row[k] * w ** (s - 1 - k) for k in range(s)).subs(w, (x - c_sh) / 2)), x, domain=sp.ZZ)
        for row in deck
    ]
    x_max_ub = strict_upper_bound_roots(chi_S, x)
    deg_q = (n - 2) - Gcd2_x.degree()
    Q_cache = {}

    def get_pair_items(a, b):
        kp = (a, b) if a <= b else (b, a)
        if kp not in Q_cache:
            res = solve_2v_jacobi_pair(g_list[kp[0]], g_list[kp[1]], Sim_x, Mult_rad_x, Gcd2_x, n, x, x_max_ub=x_max_ub)
            uniq = {}
            for s2_val, q_uv, _ in res:
                key = tuple(int(val) for val in q_uv.all_coeffs())
                if key not in uniq:
                    uniq[key] = {"q_poly": q_uv, "s2_vals": [s2_val]}
            Q_cache[kp] = list(uniq.values())
            if kp[0] != kp[1]:
                Q_cache[(kp[1], kp[0])] = Q_cache[kp]
        return Q_cache[(a, b)]

    all_sols = []
    skipped_huge_box = False
    coupled_certs = []
    for act, extra_rows in cones:
        sols = enum_cone_sols(deck, act, extra_rows, rhs, n)
        if sols is None and run_stage3 and len(act) <= 35:
            # Coupled Stage-2+3 vertex pruning
            cur_act = list(act)
            changed = True
            while changed and cur_act:
                changed = False
                surv_act = []
                for v in cur_act:
                    m_c = len(cur_act)
                    v_loc = cur_act.index(v)
                    cols_m = []
                    for loc_b, b in enumerate(cur_act):
                        col = list(deck[b]) + [rf[b] for rf, _ in extra_rows] + [0] * (deg_q + 1) + [(-1 if k == loc_b else 0) for k in range(m_c)]
                        cols_m.append(col)
                    for loc_b, b in enumerate(cur_act):
                        for item in get_pair_items(v, b):
                            q_cs = _poly_coeffs_fixed_len(item["q_poly"], deg_q + 1)
                            cols_m.append([0] * (s + len(extra_rows)) + q_cs + [(1 if k == loc_b else 0) for k in range(m_c)])
                    chi_Sv = Gcd_x * g_list[v]
                    rhs_p, _ = sp.div(chi_Sv.diff(), Gcd2_x)
                    rhs_q = _poly_coeffs_fixed_len(rhs_p, deg_q + 1)
                    rhs_tot = [Fraction(vr) for vr in rhs] + [rf for _, rf in extra_rows] + [Fraction(vq) for vq in rhs_q] + [Fraction(-1 if k == v_loc else 0) for k in range(m_c)]
                    rhs_sh = [rhs_tot[r] - Fraction(cols_m[v_loc][r]) for r in range(len(rhs_tot))]
                    cols_int = [[] for _ in range(len(cols_m))]
                    rhs_int = []
                    for r in range(len(rhs_tot)):
                        lcm_d = rhs_sh[r].denominator
                        for cj in range(len(cols_m)):
                            lcm_d = math.lcm(lcm_d, Fraction(cols_m[cj][r]).denominator)
                        for cj in range(len(cols_m)):
                            cols_int[cj].append(int(Fraction(cols_m[cj][r]) * lcm_d))
                        rhs_int.append(int(rhs_sh[r] * lcm_d))
                    inf, y_c = find_exact_farkas_rational(cols_int, rhs_int)
                    if inf:
                        changed = True
                        coupled_certs.append({"v_pruned": v, "cur_act": list(cur_act), "c_farkas": y_c})
                    else:
                        surv_act.append(v)
                cur_act = surv_act
            print(f"  cone pruned {len(act)} -> {len(cur_act)} ({time.time()-t0:.2f}s)", flush=True)
            sols = [] if not cur_act else enum_cone_sols(deck, cur_act, extra_rows, rhs, n)
        if sols is None:
            skipped_huge_box = True
            continue
        for v_sol in sols:
            if v_sol not in all_sols:
                all_sols.append(v_sol)

    after_p61 = [v_sol for v_sol in all_sols if prop61_sol_ok(v_sol, deck, Pw, n, d_dim, c_sh, w, x)]
    print(f"idx={idx:4d} (s={s}, diff={diff}, deck={len(deck):4d}, cones={len(cones)}): stage2_sols={len(all_sols)} (huge_box={skipped_huge_box}), after_p61={len(after_p61)} ({time.time()-t0:.2f}s)", flush=True)

    if not run_stage3 or skipped_huge_box:
        return {"index": idx, "status": "STAGE2_ONLY" if not run_stage3 else "SKIPPED_HUGE_BOX", "stage2_sols": len(after_p61)}

    if not after_p61:
        return {
            "index": idx,
            "status": "KILLED_STAGE2_COUPLED_OR_P61",
            "s": s,
            "diff": diff,
            "Sim_x": sp.sstr(Sim_x.as_expr()),
            "stage2_sols": len(all_sols),
            "after_p61": 0,
            "coupled_certs_count": len(coupled_certs),
            "coupled_certs": coupled_certs,
            "stage3_survivors_count": 0,
            "elapsed_sec": round(time.time() - t0, 3),
        }

    stage3_certs = []
    stage3_survs = []
    sv_galois_certs = []
    for v_sol in after_p61:
        killed, cert = check_stage3_for_counts(chi_S, Gcd_x, Gcd2_x, Sim_x, Mult_rad_x, g_list, v_sol, n, x, Q_cache=Q_cache)
        if killed:
            stage3_certs.append(cert)
        else:
            if run_sv_galois:
                k_sv, c_sv = sv_kx_galois_check(chi_S, Gcd_x, Gcd2_x, Sim_x, Mult_rad_x, g_list, v_sol, n, x, Q_cache=Q_cache)
                if k_sv:
                    sv_galois_certs.append(c_sv)
                    continue
            stage3_survs.append(cert)

    status = "KILLED_STAGE3" if not stage3_survs else "SURVIVED_STAGE3"
    dt = time.time() - t0
    print(f"  => idx={idx:4d} {status}: s3_killed={len(stage3_certs)}, sv_gal_killed={len(sv_galois_certs)}, surv={len(stage3_survs)} ({dt:.2f}s)", flush=True)
    return {
        "index": idx,
        "status": status,
        "s": s,
        "diff": diff,
        "Sim_x": sp.sstr(Sim_x.as_expr()),
        "stage2_sols": len(all_sols),
        "after_p61": len(after_p61),
        "stage3_killed": len(stage3_certs),
        "sv_galois_killed": len(sv_galois_certs),
        "stage3_survivors_count": len(stage3_survs),
        "stage3_survivors": stage3_survs,
        "stage3_certificates": stage3_certs,
        "sv_galois_certificates": sv_galois_certs,
        "coupled_certs_count": len(coupled_certs),
        "coupled_certs": coupled_certs,
        "elapsed_sec": round(dt, 3),
    }


if __name__ == "__main__":
    from pathlib import Path
    _COMP_DIR = Path(__file__).resolve().parent.parent
    if str(_COMP_DIR) not in sys.path:
        sys.path.insert(0, str(_COMP_DIR))
    from _io import POLY_RESULTS_DIR, load_json_auto

    POLY_RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    d59 = load_json_auto("deck_18_59.json")
    n, d_dim, c_sh = d59["n"], d59["d"], d59["c"]
    if len(sys.argv) > 1:
        targets = [int(a) for a in sys.argv[1:]]
        out_path = str(POLY_RESULTS_DIR / "phase3_18_59_batch2.json")
    else:
        targets = [864, 441, 692, 651, 978, 997, 364, 603, 488, 103, 341, 705, 319, 228, 800, 151, 1113]
        out_path = str(POLY_RESULTS_DIR / "phase3_18_59_stage3.json")

    results = {}
    for idx in targets:
        res = solve_candidate(d59["candidates"][idx], n, d_dim, c_sh, run_stage3=True, run_sv_galois=True)
        results[str(idx)] = res

    with open(out_path, "w") as f:
        json.dump({"d": d_dim, "n": n, "targets": targets, "results": results}, f, indent=2)
    sha = hashlib.sha256(open(out_path, "rb").read()).hexdigest()
    print(f"Saved {out_path} (sha256={sha})", flush=True)
