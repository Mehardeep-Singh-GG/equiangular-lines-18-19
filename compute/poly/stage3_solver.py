"""
Exact, float-free Stage-3 (2-vertex Jacobi + 1-vertex deletion derivative system)
solver and verifier for Seidel matrices with minimum eigenvalue >= -5.

Every elimination decision is certified solely in exact ZZ / QQ arithmetic:
  - Cauchy interlacing via exact Sturm PRS Cauchy index (no floating-point roots).
  - Exact rational Farkas certificates (Bland's-rule Phase-I Simplex) and exact RREF box search.
  - Exact 2-adic divisibility 2^{n-2} | chi_{S_{uv}}(2t-1) (even n) or 2^{n-3} | chi_{S_{uv}}(2t-1) (odd n).
"""

import json
import math
import time
from fractions import Fraction
import sympy as sp

from phase2_even import (
    find_exact_farkas_rational,
    certify_no_nonneg_int_solution_exact,
    passes_t42_sub,
)


def exact_real_rooted_ge_neg5(poly_x, x_sym):
    """Exact Sturm check: all roots (counted with multiplicity) are real and >= -5."""
    deg = poly_x.degree()
    if deg == 0:
        return True
    p = sp.Poly(poly_x, x_sym, domain=sp.ZZ)
    if p.LC() < 0:
        p = -p
    sqf_list = p.sqf_list()[1]
    total_real_ge_neg5 = 0
    for fac, mult in sqf_list:
        fp = sp.Poly(fac, x_sym, domain=sp.ZZ)
        d_fac = fp.degree()
        # Shift y = x + 5 -> check all roots y >= 0
        fy = sp.Poly(sp.expand(fp.as_expr().subs(x_sym, x_sym - 5)), x_sym, domain=sp.ZZ)
        if fy.eval(0) == 0:
            # 0 is a simple root of sqf factor fy; divide out x_sym and check > 0
            fy, _ = sp.div(fy, sp.Poly(x_sym, x_sym, domain=sp.ZZ))
            roots_ge0 = 1 + sp.count_roots(fy, 0, None)
        else:
            roots_ge0 = sp.count_roots(fy, 0, None)
        if roots_ge0 != d_fac:
            return False
        total_real_ge_neg5 += mult * roots_ge0
    return total_real_ge_neg5 == deg


def sturm_interlaces(low_poly, high_poly, x_sym):
    """
    Exact float-free Cauchy interlacing via Sturm PRS Cauchy index.
    After cancelling g = gcd(low_poly, high_poly), lp interlaces hp iff
    deg(hp) == deg(lp) + 1 and the Sturm PRS (hp, lp, ...) has deg(hp)+1 terms
    with strictly positive leading coefficients (Cauchy index I_{-inf}^{+inf}(lp/hp) = deg(hp)).
    """
    g = sp.gcd(low_poly, high_poly)
    lp, _ = sp.div(low_poly, g)
    hp, _ = sp.div(high_poly, g)
    if hp.degree() != lp.degree() + 1:
        return False
    if lp.LC() < 0:
        lp = -lp
    if hp.LC() < 0:
        hp = -hp
    d = hp.degree()
    if d == 1:
        return True
    p0 = sp.Poly(hp, x_sym, domain=sp.QQ)
    p1 = sp.Poly(lp, x_sym, domain=sp.QQ)
    for _ in range(d - 1):
        r = -sp.rem(p0, p1)
        if r.is_zero or r.degree() != p1.degree() - 1 or r.LC() <= 0:
            return False
        p0, p1 = p1, r
    return True


def strict_upper_bound_roots(poly_x, x_sym):
    """Return smallest integer M >= 18 such that poly_x(y + M) has all positive coefficients."""
    M = 18
    while True:
        shifted = sp.Poly(sp.expand(poly_x.as_expr().subs(x_sym, x_sym + M)), x_sym, domain=sp.ZZ)
        if shifted.LC() < 0:
            shifted = -shifted
        if all(int(c) > 0 for c in shifted.all_coeffs()):
            return M
        M += 1


def _poly_shift_neg5_asc(cs_desc):
    """Given polynomial coeffs descending in x, return coeffs ascending in y = x + 5 (i.e. x = y - 5)."""
    # Horner in ascending power basis: P(y - 5)
    asc = []
    for c in cs_desc:
        # asc = asc * (y - 5) + c
        nxt = [-5 * v for v in asc] + [0]
        for i, v in enumerate(asc):
            nxt[i + 1] += v
        nxt[0] += c
        asc = nxt
    while len(asc) > 1 and asc[-1] == 0:
        asc.pop()
    return asc


def _poly_prim_int(asc):
    while len(asc) > 1 and asc[-1] == 0:
        asc.pop()
    if len(asc) == 1 and asc[0] == 0:
        return [0]
    g = 0
    for v in asc:
        g = math.gcd(g, abs(v))
    if g > 1:
        asc = [v // g for v in asc]
    return asc


def _poly_prem_neg_int(a_asc, b_asc):
    """Exact negated pseudo-remainder -prem(a, b) scaled by positive square multiplier to preserve signs."""
    a = list(a_asc)
    db = len(b_asc) - 1
    lc_b = b_asc[-1]
    while len(a) - 1 >= db and not (len(a) == 1 and a[0] == 0):
        da = len(a) - 1
        shift = da - db
        lc_a = a[-1]
        g = math.gcd(abs(lc_a), abs(lc_b))
        # Multiply a by (lc_b / g)^2 if da-db step could flip sign? No, multiply by |lc_b // g|? Wait:
        # Standard pseudo-rem multiplies by lc_b^{...}; to guarantee POSITIVE multiplier:
        # multiply a by lc_b * sgn(lc_b) = abs(lc_b) // g? No:
        # We want c1 * a - c2 * x^shift * b where c1 > 0!
        # Let mult_a = abs(lc_b) // g (> 0), mult_b = (lc_a // g) * (1 if lc_b > 0 else -1).
        # Then top coeff = mult_a * lc_a - mult_b * lc_b = (|lc_b|*lc_a - lc_a*sgn(lc_b)*lc_b)/g = 0!
        mult_a = abs(lc_b) // g
        mult_b = (lc_a // g) * (1 if lc_b > 0 else -1)
        a = [v * mult_a for v in a]
        for i in range(db + 1):
            a[i + shift] -= mult_b * b_asc[i]
        while len(a) > 1 and a[-1] == 0:
            a.pop()
    # Negate and make primitive
    neg = [-v for v in a]
    return _poly_prim_int(neg)


def _poly_gcd_int(a_asc, b_asc):
    a = _poly_prim_int(a_asc)
    b = _poly_prim_int(b_asc)
    while not (len(b) == 1 and b[0] == 0):
        r = _poly_prem_neg_int(a, b)
        a, b = b, r
    if a[-1] < 0:
        a = [-v for v in a]
    return _poly_prim_int(a)


def _poly_div_exact_int(a_asc, b_asc):
    a = list(a_asc)
    da = len(a) - 1
    db = len(b_asc) - 1
    lc_b = b_asc[-1]
    q = [0] * (da - db + 1)
    for shift in range(da - db, -1, -1):
        top = a[shift + db]
        assert top % lc_b == 0
        cf = top // lc_b
        q[shift] = cf
        if cf:
            for i in range(db + 1):
                a[shift + i] -= cf * b_asc[i]
    return q


def _sign_changes(seq):
    nz = [1 if v > 0 else -1 for v in seq if v != 0]
    return sum(1 for i in range(len(nz) - 1) if nz[i] != nz[i + 1])


def fast_real_rooted_ge_neg5_int(cs_desc):
    """Exact pure-integer Sturm check that all roots of cs_desc are real and >= -5."""
    y_asc = _poly_shift_neg5_asc(cs_desc)
    deg_orig = len(y_asc) - 1
    if deg_orig <= 0:
        return True
    if y_asc[-1] < 0:
        y_asc = [-v for v in y_asc]
    # Strip any root at y = 0 (x = -5)
    k0 = 0
    while k0 < len(y_asc) and y_asc[k0] == 0:
        k0 += 1
    if k0 > 0:
        y_asc = y_asc[k0:]
    d_rem = len(y_asc) - 1
    if d_rem == 0:
        return True
    # Check both sqf part and repeated gcd recursively via a stack
    stack = [y_asc]
    while stack:
        cur = _poly_prim_int(stack.pop())
        if cur[-1] < 0:
            cur = [-v for v in cur]
        if len(cur) - 1 == 0:
            continue
        if cur[0] == 0:
            return False  # y=0 was already stripped from y_asc!
        dcur = [i * cur[i] for i in range(1, len(cur))]
        g = _poly_gcd_int(cur, dcur)
        if len(g) > 1:
            sqf = _poly_div_exact_int(cur, g)
            stack.append(g)
        else:
            sqf = cur
        # Sturm sequence for squarefree sqf (sqf[0] != 0, sqf[-1] > 0)
        d_sqf = len(sqf) - 1
        if d_sqf == 1:
            # c0 + c1*y = 0 -> y = -c0/c1 > 0 iff c0 < 0
            if sqf[0] >= 0:
                return False
            continue
        p0 = sqf
        p1 = _poly_prim_int([i * sqf[i] for i in range(1, len(sqf))])
        seq_0 = [p0[0], p1[0]]
        seq_inf = [p0[-1], p1[-1]]
        while len(p1) > 1:
            r = _poly_prem_neg_int(p0, p1)
            if len(r) == 1 and r[0] == 0:
                break
            seq_0.append(r[0])
            seq_inf.append(r[-1])
            p0, p1 = p1, r
        if _sign_changes(seq_0) - _sign_changes(seq_inf) != d_sqf:
            return False
    return True


def _poly_crt_qq(r1, m1, r2, m2, x_sym):
    """Exact CRT in QQ[x]: find r mod (m1*m2) with r == r1 mod m1 and r == r2 mod m2 (gcd(m1,m2)=1)."""
    m1_q = sp.Poly(m1, x_sym, domain=sp.QQ)
    m2_q = sp.Poly(m2, x_sym, domain=sp.QQ)
    u, _, g = sp.gcdex(m1_q, m2_q)
    if g.degree() != 0:
        return None
    u_q = u if g.LC() == 1 else sp.Poly(u.as_expr() / g.LC(), x_sym, domain=sp.QQ)
    r1_q = sp.Poly(r1, x_sym, domain=sp.QQ)
    r2_q = sp.Poly(r2, x_sym, domain=sp.QQ)
    prod_m = m1_q * m2_q
    k = sp.rem((r2_q - r1_q) * u_q, m2_q)
    return sp.rem(r1_q + m1_q * k, prod_m)


def _is_rat_square(q):
    if q < 0:
        return None
    if q == 0:
        return Fraction(0)
    sp_n = math.isqrt(q.numerator)
    sp_d = math.isqrt(q.denominator)
    if sp_n * sp_n == q.numerator and sp_d * sp_d == q.denominator:
        return Fraction(sp_n, sp_d)
    return None


def solve_mod_sim_roots(prod_g, Sim_x, x_sym):
    """
    Return all integer polynomials R_uv(x) of degree < deg(Sim_x) such that
    R_uv(x)^2 == prod_g(x) (mod Sim_x(x)), for arbitrary squarefree Sim_x(x).
    """
    if Sim_x.degree() == 0:
        return [sp.Poly(0, x_sym, domain=sp.ZZ)]

    facs = sp.factor_list(Sim_x.as_expr())[1]
    t_sym = sp.Symbol("_tsim")
    per_fac_roots = []

    for fac_expr, mult in facs:
        assert mult == 1, f"Sim_x must be squarefree, got mult={mult}"
        fp = sp.Poly(fac_expr, x_sym, domain=sp.QQ)
        rem = sp.rem(sp.Poly(prod_g, x_sym, domain=sp.QQ), fp)
        if rem.is_zero:
            per_fac_roots.append((fp, [sp.Poly(0, x_sym, domain=sp.QQ)]))
            continue
        if fp.degree() == 1:
            lam = -fp.nth(0) / fp.LC()
            val = Fraction(rem.eval(lam).p, rem.eval(lam).q)
            sr = _is_rat_square(val)
            if sr is None:
                return []
            if sr == 0:
                per_fac_roots.append((fp, [sp.Poly(0, x_sym, domain=sp.QQ)]))
            else:
                r_q = sp.Rational(sr.numerator, sr.denominator)
                per_fac_roots.append((fp, [sp.Poly(r_q, x_sym, domain=sp.QQ), sp.Poly(-r_q, x_sym, domain=sp.QQ)]))
        else:
            alpha = sp.RootOf(fp.as_expr(), 0)
            K_dom = sp.QQ.algebraic_field(alpha)
            p_t = sp.Poly(t_sym**2 - rem.as_expr().subs(x_sym, alpha), t_sym, domain=K_dom)
            fl = p_t.factor_list()[1]
            if not (len(fl) == 2 or fl[0][1] == 2):
                return []
            fac0 = fl[0][0]
            val = -fac0.nth(0) / fac0.LC()
            anp = K_dom.from_sympy(val)
            r_poly = sp.Poly([sp.Rational(c.numerator, c.denominator) for c in anp.rep], x_sym, domain=sp.QQ)
            if r_poly.is_zero:
                per_fac_roots.append((fp, [r_poly]))
            else:
                per_fac_roots.append((fp, [r_poly, -r_poly]))

    # CRT across all irreducible factors
    cur_m, cur_rs = per_fac_roots[0]
    for fp, rs in per_fac_roots[1:]:
        nxt_rs = []
        for r_acc in cur_rs:
            for r_new in rs:
                comb = _poly_crt_qq(r_acc, cur_m, r_new, fp, x_sym)
                if comb is not None:
                    nxt_rs.append(comb)
        cur_m = cur_m * fp
        cur_rs = nxt_rs

    # Filter to exact integer polynomials in ZZ[x]
    out = []
    for r_qq in cur_rs:
        if all(c.q == 1 for c in r_qq.all_coeffs()):
            out.append(sp.Poly(r_qq.as_expr(), x_sym, domain=sp.ZZ))
    return out


def _poly_to_2t_minus_1_mod(poly_desc, mod_req):
    if mod_req <= 1:
        return True
    res_t = [0]
    for c in poly_desc:
        nxt = [0] * (len(res_t) + 1)
        for idx_k, v in enumerate(res_t):
            nxt[idx_k] = (nxt[idx_k] - v) % mod_req
            nxt[idx_k + 1] = (nxt[idx_k + 1] + 2 * v) % mod_req
        nxt[0] = (nxt[0] + c) % mod_req
        res_t = nxt
    return all(v == 0 for v in res_t)


def solve_2v_jacobi_pair(ga_x, gb_x, Sim_x, Mult_rad_x, Gcd2_x, n, x_sym, x_max_ub=18):
    """
    Enumerate ALL exact candidate (s2_uv, q_uv, h_uv) for a pair of vertex types (a, b)
    such that g_a * g_b - Sim_x * q_uv = h_uv^2, chi_{S_{uv}} = Gcd2_x * q_uv has all real roots >= -5,
    interlaces both Mult_rad_x * g_a and Mult_rad_x * g_b, and satisfies the 2-adic divisibility
    2^{n-2} | chi(2t-1) (even n) or 2^{n-3} | chi(2t-1) (odd n).

    Supports arbitrary squarefree Sim_x, exact Cauchy-forced divisor D_h | h_uv and F_forced | q_uv,
    and deg_Q = deg(h_uv) - deg(lcm(Sim_x, D_h)) in {0, 1, 2, 3}.
    """
    deg_h = ga_x.degree() - 1
    e_sim = Sim_x.degree()

    Gcd_x = Gcd2_x * Mult_rad_x
    deg_gcd = Gcd_x.degree()
    gamma1 = int(Gcd_x.nth(deg_gcd - 1)) if deg_gcd >= 1 else 0

    prod_g = ga_x * gb_x
    R_choices = solve_mod_sim_roots(prod_g, Sim_x, x_sym)
    if not R_choices:
        return []

    ga_star = Mult_rad_x * ga_x
    gb_star = Mult_rad_x * gb_x

    # Exact Cauchy-forced divisor F_forced | q_uv and D_h | h_uv
    ga_rep = sp.gcd(ga_star, ga_star.diff())
    if ga_rep.LC() < 0: ga_rep = -ga_rep
    gb_rep = sp.gcd(gb_star, gb_star.diff())
    if gb_rep.LC() < 0: gb_rep = -gb_rep
    F_forced = sp.lcm(ga_rep, gb_rep)
    if F_forced.LC() < 0: F_forced = -F_forced

    common_h = sp.gcd(prod_g, Sim_x * F_forced)
    D_h = sp.Poly(1, x_sym, domain=sp.ZZ)
    if common_h.degree() > 0:
        for fac_expr, mult in sp.factor_list(common_h.as_expr())[1]:
            D_h = D_h * (sp.Poly(fac_expr, x_sym, domain=sp.ZZ) ** ((mult + 1) // 2))

    # Combine h == R mod Sim_x and h == 0 mod D_h -> modulus M_crt = lcm(Sim_x, D_h)
    S0 = sp.gcd(Sim_x, D_h)
    if S0.LC() < 0: S0 = -S0
    Sim_red, _ = sp.div(Sim_x, S0)
    M_crt = Sim_red * D_h
    if M_crt.LC() < 0: M_crt = -M_crt
    e_m = M_crt.degree()
    deg_Q = deg_h - e_m
    assert deg_Q <= 3, f"Unsupported deg_Q={deg_Q} (deg_h={deg_h}, e_sim={e_sim}, e_m={e_m})"

    crt_pairs = []
    for R_poly in R_choices:
        if S0.degree() > 0 and not sp.rem(R_poly, S0).is_zero:
            continue
        if D_h.degree() == 0:
            crt_pairs.append(R_poly)
        elif Sim_red.degree() == 0:
            crt_pairs.append(sp.Poly(0, x_sym, domain=sp.ZZ))
        else:
            R_crt = _poly_crt_qq(R_poly, Sim_red, sp.Poly(0, x_sym, domain=sp.QQ), D_h, x_sym)
            if R_crt is not None and all(c.q == 1 for c in R_crt.all_coeffs()):
                crt_pairs.append(sp.Poly(R_crt.as_expr(), x_sym, domain=sp.ZZ))
    if not crt_pairs:
        return []

    m1 = int(M_crt.nth(e_m - 1)) if e_m >= 1 else 0
    prod_cs = [int(v) for v in prod_g.all_coeffs()]
    sim_cs = [int(v) for v in Sim_x.all_coeffs()]
    mcrt_cs = [int(v) for v in M_crt.all_coeffs()]

    # 2-adic congruence on chi_{S_{uv}}(2t - 1): 2^{n-2} (even n) or 2^{n-3} (odd n)
    t_sym = sp.Symbol("_t2v")
    Gcd2_t = sp.Poly(sp.expand(Gcd2_x.as_expr().subs(x_sym, 2 * t_sym - 1)), t_sym, domain=sp.ZZ)
    gcd2_cs = [int(v) for v in Gcd2_t.all_coeffs()]
    v2_gcd2 = min((abs(v) & -abs(v)).bit_length() - 1 for v in gcd2_cs if v != 0) if any(gcd2_cs) else 0
    exp_req = (n - 2) if (n % 2 == 0) else (n - 3)
    need_v2_q = max(0, exp_req - v2_gcd2)
    mod_req = 1 << need_v2_q

    eval_pts = [-5, x_max_ub]
    if deg_Q == 3:
        eval_pts = [-5, -6, -8, x_max_ub, x_max_ub + 1, x_max_ub + 3]
    ub_at = {}
    mcrt_at = {}
    for x0 in eval_pts:
        g_val = int(prod_g.eval(x0))
        assert g_val >= 0
        ub_at[x0] = math.isqrt(g_val)
        mcrt_at[x0] = int(M_crt.eval(x0))
        assert mcrt_at[x0] != 0

    s2_vals = list(range(-(n - 2), n - 1, 2))
    s2_set = set(s2_vals)
    results = []

    def try_h(h_cs, s2_val):
        deg_p = len(prod_cs) - 1
        deg_h2 = 2 * (len(h_cs) - 1)
        if deg_h2 > deg_p:
            return
        num_cs = list(prod_cs)
        off_h = deg_p - deg_h2
        for i, ai in enumerate(h_cs):
            if ai:
                for j, bj in enumerate(h_cs):
                    num_cs[off_h + i + j] -= ai * bj

        if e_sim == 0:
            q_cs = num_cs
        elif e_sim == 1:
            lam1 = -sim_cs[1]
            q_cs = []
            rem_v = 0
            for c_val in num_cs:
                rem_v = rem_v * lam1 + c_val
                q_cs.append(rem_v)
            if q_cs.pop() != 0:
                return
        else:
            work = list(num_cs)
            q_len = len(work) - e_sim
            if q_len <= 0:
                return
            q_cs = [0] * q_len
            for i in range(q_len):
                coef = work[i]
                q_cs[i] = coef
                if coef != 0:
                    for j in range(1, e_sim + 1):
                        work[i + j] -= coef * sim_cs[j]
            if any(work[q_len:]):
                return

        if not _poly_to_2t_minus_1_mod(q_cs, mod_req):
            return
        if not fast_real_rooted_ge_neg5_int(q_cs):
            return
        q_uv = sp.Poly(q_cs, x_sym, domain=sp.ZZ)
        if F_forced.degree() > 0 and not sp.rem(q_uv, F_forced).is_zero:
            return
        if not exact_real_rooted_ge_neg5(q_uv, x_sym):
            return
        if not sturm_interlaces(q_uv, ga_star, x_sym):
            return
        if not sturm_interlaces(q_uv, gb_star, x_sym):
            return
        h_uv = sp.Poly(h_cs, x_sym, domain=sp.ZZ)
        results.append((s2_val, q_uv, h_uv))

    def try_Q(Q_cs, R_cs, s2_val):
        deg_h_act = max(len(Q_cs) + len(mcrt_cs) - 2, len(R_cs) - 1)
        h_cs = [0] * (deg_h_act + 1)
        off_q = deg_h_act - (len(Q_cs) + len(mcrt_cs) - 2)
        for i, ai in enumerate(Q_cs):
            if ai:
                for j, bj in enumerate(mcrt_cs):
                    h_cs[off_q + i + j] += ai * bj
        off_r = deg_h_act - (len(R_cs) - 1)
        for i, ri in enumerate(R_cs):
            h_cs[off_r + i] += ri
        try_h(h_cs, s2_val)

    for R_poly in crt_pairs:
        R_cs = [int(v) for v in R_poly.all_coeffs()]
        if deg_Q < 0:
            if R_poly.degree() == deg_h and R_poly.LC() == 1:
                r_top = int(R_poly.nth(deg_h - 1)) if deg_h >= 1 else 0
                s2_val = r_top + gamma1
                if s2_val in s2_set:
                    try_h(R_cs, s2_val)
            continue
        r_top = int(R_poly.nth(deg_h - 1)) if deg_h >= 1 else 0
        if deg_Q == 0:
            s2_val = m1 + r_top + gamma1
            if s2_val in s2_set:
                try_Q([1], R_cs, s2_val)
        elif deg_Q == 1:
            for s2 in s2_vals:
                q0 = s2 - gamma1 - m1
                try_Q([1, q0], R_cs, s2)
        elif deg_Q == 2:
            for s2 in s2_vals:
                q1 = s2 - gamma1 - m1
                lo_q0, hi_q0 = -10**18, 10**18
                for x0 in [-5, x_max_ub]:
                    sx = mcrt_at[x0]
                    ub = ub_at[x0]
                    rx = int(R_poly.eval(x0))
                    if sx > 0:
                        lo_x = math.ceil(Fraction(-ub - rx, sx)) - (x0 * x0 + q1 * x0)
                        hi_x = math.floor(Fraction(ub - rx, sx)) - (x0 * x0 + q1 * x0)
                    else:
                        lo_x = math.ceil(Fraction(ub - rx, sx)) - (x0 * x0 + q1 * x0)
                        hi_x = math.floor(Fraction(-ub - rx, sx)) - (x0 * x0 + q1 * x0)
                    lo_q0 = max(lo_q0, lo_x)
                    hi_q0 = min(hi_q0, hi_x)
                for q0 in range(lo_q0, hi_q0 + 1):
                    try_Q([1, q1, q0], R_cs, s2)
        elif deg_Q == 3:
            for s2 in s2_vals:
                q2 = s2 - gamma1 - m1
                ineqs = []
                for x0 in eval_pts:
                    sx = mcrt_at[x0]
                    ub = ub_at[x0]
                    rx = int(R_poly.eval(x0))
                    base = x0**3 + q2 * x0**2
                    if sx > 0:
                        lo_k = math.ceil(Fraction(-ub - rx, sx)) - base
                        hi_k = math.floor(Fraction(ub - rx, sx)) - base
                    else:
                        lo_k = math.ceil(Fraction(ub - rx, sx)) - base
                        hi_k = math.floor(Fraction(-ub - rx, sx)) - base
                    ineqs.append((x0, lo_k, hi_k))
                lo_q1, hi_q1 = -10**18, 10**18
                for x_a, la, ua in ineqs:
                    for x_b, lb, ub in ineqs:
                        if x_b > x_a:
                            lo_q1 = max(lo_q1, math.ceil(Fraction(lb - ua, x_b - x_a)))
                            hi_q1 = min(hi_q1, math.floor(Fraction(ub - la, x_b - x_a)))
                for q1 in range(lo_q1, hi_q1 + 1):
                    lo_q0, hi_q0 = -10**18, 10**18
                    for x0, lo_k, hi_k in ineqs:
                        lo_q0 = max(lo_q0, lo_k - x0 * q1)
                        hi_q0 = min(hi_q0, hi_k - x0 * q1)
                    for q0 in range(lo_q0, hi_q0 + 1):
                        try_Q([1, q2, q1, q0], R_cs, s2)
    return results


def _poly_coeffs_fixed_len(poly, length):
    cs = [int(v) for v in poly.all_coeffs()]
    if len(cs) < length:
        cs = [0] * (length - len(cs)) + cs
    return cs


def check_stage3_for_counts(chi_S, Gcd_x, Gcd2_x, Sim_x, Mult_rad_x, g_list, counts_n, n, x_sym, Q_cache=None):
    """
    Given a Stage-2 solution vector counts_n = [n_0, ..., n_{K-1}] (sum = n),
    compute all 2v-Jacobi quotients and test the Stage-3 1-vertex deletion derivative
    system for EVERY active vertex type v (n_v > 0).

    Returns (killed: bool, cert_or_survivor_info: dict).
    """
    if Q_cache is None:
        Q_cache = {}
    K = len(g_list)
    active = [a for a in range(K) if counts_n[a] > 0]
    x_max_ub = strict_upper_bound_roots(chi_S, x_sym)

    def get_pair(a, b):
        key_p = (a, b) if a <= b else (b, a)
        if key_p not in Q_cache:
            res = solve_2v_jacobi_pair(g_list[key_p[0]], g_list[key_p[1]], Sim_x, Mult_rad_x, Gcd2_x, n, x_sym, x_max_ub=x_max_ub)
            uniq = {}
            for s2_val, q_uv, h_uv in res:
                key = tuple(int(val) for val in q_uv.all_coeffs())
                if key not in uniq:
                    uniq[key] = {"q_poly": q_uv, "s2_vals": [s2_val]}
                else:
                    uniq[key]["s2_vals"].append(s2_val)
            Q_cache[(key_p[0], key_p[1])] = list(uniq.values())
            if key_p[0] != key_p[1]:
                Q_cache[(key_p[1], key_p[0])] = Q_cache[(key_p[0], key_p[1])]
        return Q_cache[(a, b)]

    # Test each active vertex type v (lazy Q_cache so Farkas kills short-circuit early!)
    deg_q = (n - 2) - Gcd2_x.degree()
    per_v_status = []
    for v in active:
        chi_Sv = Gcd_x * g_list[v]
        rhs_poly, rem = sp.div(chi_Sv.diff(), Gcd2_x)
        assert rem.is_zero, "Gcd2_x must divide chi_{S_v}'"
        rhs_cs = _poly_coeffs_fixed_len(rhs_poly, deg_q + 1)

        # Build columns grouped by neighbor vertex type b
        col_vecs = []
        block_eqs = []
        for b in active:
            nb_rem = counts_n[b] - (1 if b == v else 0)
            if nb_rem <= 0:
                continue
            q_items = get_pair(v, b)
            if not q_items:
                return True, {
                    "method": "stage3_empty_pair_type",
                    "v_type": v,
                    "b_type": b,
                    "nb_rem": nb_rem,
                    "counts_n": list(counts_n),
                }
            start_col = len(col_vecs)
            for item in q_items:
                q_cs = _poly_coeffs_fixed_len(item["q_poly"], deg_q + 1)
                col_vecs.append(q_cs)
            end_col = len(col_vecs)
            block_eqs.append((start_col, end_col, nb_rem))

        num_cols = len(col_vecs)
        # Rows: poly coeffs (exclude top 2 redundant? keeping all is harmless and explicit!) + block sums
        A_rows = []
        b_vec = []
        for r_idx in range(deg_q + 1):
            row = [col_vecs[c][r_idx] for c in range(num_cols)]
            if any(row) or rhs_cs[r_idx] != 0:
                A_rows.append(row)
                b_vec.append(rhs_cs[r_idx])
        for sc, ec, nb_rem in block_eqs:
            row = [1 if sc <= c < ec else 0 for c in range(num_cols)]
            A_rows.append(row)
            b_vec.append(nb_rem)

        cols_T = [[A_rows[r][c] for r in range(len(A_rows))] for c in range(num_cols)]
        infeasible, y_cert = find_exact_farkas_rational(cols_T, b_vec)
        if infeasible:
            return True, {
                "method": "stage3_exact_farkas",
                "v_type": v,
                "counts_n": list(counts_n),
                "num_cols": num_cols,
                "c_farkas": [int(val) for val in y_cert],
            }

        # Exact integer non-negative RREF / box exhaustion (only when small free dim)
        ok_int_elim, int_cert = certify_no_nonneg_int_solution_exact(cols_T, b_vec, n_max=n - 1)
        if ok_int_elim:
            return True, {
                "method": "stage3_exact_rref_no_int",
                "v_type": v,
                "counts_n": list(counts_n),
                "detail": int_cert,
            }
        per_v_status.append({"v_type": v, "num_cols": num_cols})

    return False, {"counts_n": list(counts_n), "per_v": per_v_status}
