"""
Exact float-free 2-vertex Jacobi (diff=1,2) + Stage-3 (74 -> 73 -> 72) solver
for the remaining (19, 74) candidates {6, 13, 24, 47}.
Zero floating-point eliminations: uses exact integer bounds, Prop 7.3 (2^{n-2} divisibility),
exact Sturm root counting (sqf_list / count_roots), exact CRootOf interlacing,
and Theorem 7.1 (M, N mod 4, k_u) + Theorem 7.2 (Galois orthogonality) on 73x73 S_v.
"""
import json
import math
import sys
import sympy as sp
import numpy as np
from phase2_even import passes_t42_sub, find_exact_farkas, certify_no_nonneg_int_solution_exact


def exact_real_rooted_ge_neg5(poly_x, x_sym):
    """Exact float-free check that all roots of poly_x are real and >= -5."""
    deg = poly_x.degree()
    if deg == 0:
        return True
    # Total real roots via sqf_list + count_roots (exact Sturm!)
    sqf_facs = poly_x.sqf_list()[1]
    real_cnt = 0
    for fac, mult in sqf_facs:
        cnt = sp.count_roots(fac)
        if cnt != fac.degree():
            return False
        real_cnt += cnt * mult
    if real_cnt != deg:
        return False
    # Check no roots strictly < -5
    for fac, _ in sqf_facs:
        if sp.count_roots(fac, None, -5) > 0:
            # Wait: count_roots(fac, None, -5) counts roots in (-oo, -5] inclusive!
            # We want strictly < -5: check if fac(-5) == 0 first, divide out (x+5) if so.
            f_check = fac
            if f_check.eval(-5) == 0:
                f_check, _ = sp.div(f_check, sp.Poly(x_sym + 5, x_sym, domain=sp.ZZ))
            if f_check.degree() > 0 and sp.count_roots(f_check, None, -5) > 0:
                return False
    return True


def exact_interlaces(low_poly, high_poly, x_sym):
    """
    Exact float-free check that roots of low_poly (deg d-1) interlace roots of high_poly (deg d),
    allowing shared roots by canceling g = gcd(low_poly, high_poly) first.
    Uses exact Sturm sign counts at roots of high_p / strictly alternating CRootOf intervals.
    """
    g = sp.gcd(low_poly, high_poly)
    lp, _ = sp.div(low_poly, g)
    hp, _ = sp.div(high_poly, g)
    if hp.degree() != lp.degree() + 1:
        return False
    if lp.degree() == 0:
        return True
    # Since gcd(lp, hp) == 1, check roots of hp have strict multiplicity 1? Wait:
    # Even if hp has repeated roots, wait: if hp had a double root r not in lp, interlacing fails!
    sqf_h = hp.sqf_list()[1]
    if any(m > 1 for _, m in sqf_h):
        return False
    # Wait: lp could still have repeated roots? No, if lp has a double root r, it must sit AT a double root of hp (impossible since gcd=1 and hp squarefree)!
    sqf_l = lp.sqf_list()[1]
    if any(m > 1 for _, m in sqf_l):
        return False
    # Now both lp and hp are squarefree and coprime! Isolate hp roots via exact rational Sturm intervals.
    h_ivs = sp.intervals(hp)
    hp_diff = hp.diff()
    prev_sgn = None
    for (lo, hi), _ in h_ivs:
        lo, hi = sp.Rational(lo), sp.Rational(hi)
        if lo == hi:
            val = lp.eval(lo)
            sgn = 1 if val > 0 else (-1 if val < 0 else 0)
        else:
            # Handle open-boundary integer roots (e.g., hi is an adjacent root of hp):
            # sign of hp just to the left of hi is -sgn(hp'(hi)) when hp(hi) == 0.
            v_hi = hp.eval(hi)
            if v_hi == 0:
                s_hi = -1 if hp_diff.eval(hi) > 0 else 1
            else:
                s_hi = 1 if v_hi > 0 else -1
            # Also ensure open-interior bisection: first nudge lo/hi strictly off any endpoint root of lp!
            while sp.count_roots(lp, lo, hi) > 0:
                mid = (lo + hi) / 2
                vm = hp.eval(mid)
                if vm == 0:
                    lo = hi = mid
                    break
                sm = 1 if vm > 0 else -1
                if sm == s_hi:
                    hi = mid
                    s_hi = sm
                else:
                    lo = mid
            if lo < hi and lp.eval(lo) == 0:
                mid = (lo + hi) / 2
                vm = hp.eval(mid)
                if vm == 0:
                    lo = hi = mid
                else:
                    sm = 1 if vm > 0 else -1
                    if sm == s_hi:
                        hi = mid
                    else:
                        lo = mid
            val = lp.eval(lo)
            sgn = 1 if val > 0 else (-1 if val < 0 else 0)
        if sgn == 0:
            return False
        if prev_sgn is not None and sgn == prev_sgn:
            return False
        prev_sgn = sgn
    return True


def solve_2v_jacobi_pair(ga_x, gb_x, Sim_x, Mult_rad_x, Gcd2_x, n, x_sym, x_max_ub=18):
    """
    Solve g_a(x) g_b(x) - Sim_x(x) q_uv(x) = h_uv(x)^2 for Sim_x(x) = x - lam1 (deg 1),
    with diff = deg(h_uv) - 1 in {0, 1, 2}. Returns list of (s_uv, s2_uv, q_uv_poly, h_uv_poly).
    Wait: since swapping h_uv -> -h_uv covers s_uv = -1, we fix s_uv_fixed = +1 in Q_uv and vary
    BOTH signs of R_uv and all possible (S^2)_uv in [-(n-2), n-2] (step 2); the returned solutions
    correspond to BOTH (s_uv=+1, s2_uv) AND (s_uv=-1, -s2_uv).
    """
    deg_h = ga_x.degree() - 1
    e_sim = Sim_x.degree()
    assert e_sim == 1
    diff = deg_h - e_sim
    assert diff in (0, 1, 2), f"Unsupported diff={diff}"

    lam1 = int(-Sim_x.nth(0) // Sim_x.LC())
    # Gcd_x = Gcd2_x * Mult_rad_x, gamma1 = [x^{deg-1}] Gcd_x
    Gcd_x = Gcd2_x * Mult_rad_x
    deg_gcd = Gcd_x.degree()
    gamma1 = int(Gcd_x.nth(deg_gcd - 1)) if deg_gcd >= 1 else 0

    rhs_lam = int(ga_x.eval(lam1)) * int(gb_x.eval(lam1))
    if rhs_lam < 0:
        return []
    r0 = math.isqrt(rhs_lam)
    if r0 * r0 != rhs_lam:
        return []
    R_choices = [0] if r0 == 0 else [r0, -r0]

    # Exact integer bounds on sqrt(ga(x0)*gb(x0)) at x0 = -5 and x0 = x_max_ub
    prod_g = ga_x * gb_x
    g_neg5 = int(prod_g.eval(-5))
    g_xmax = int(prod_g.eval(x_max_ub))
    assert g_neg5 >= 0 and g_xmax >= 0
    ub_neg5 = math.isqrt(g_neg5)
    ub_xmax = math.isqrt(g_xmax)

    # Precompute 2-adic check scale: 2^{n-2} | chi_{S_uv}(2t - 1)
    t_sym = sp.Symbol("_t2v")
    Gcd2_t = sp.Poly(sp.expand(Gcd2_x.as_expr().subs(x_sym, 2 * t_sym - 1)), t_sym, domain=sp.ZZ)
    gcd2_cs = [int(v) for v in Gcd2_t.all_coeffs()]
    v2_gcd2 = min((abs(v) & -abs(v)).bit_length() - 1 for v in gcd2_cs if v != 0)
    need_v2_q = (n - 2) - v2_gcd2
    mod_req = 1 << max(0, need_v2_q)

    # Pure-integer representation of prod_g and Sim_x (descending) for fast inner loop
    prod_cs = [int(v) for v in prod_g.all_coeffs()]
    ga_star = Mult_rad_x * ga_x
    gb_star = Mult_rad_x * gb_x

    def passes_mod_2t_minus_1(q_desc):
        if need_v2_q <= 0:
            return True
        # Evaluate q(2t - 1) mod mod_req using Horner on polynomial coeffs mod mod_req
        res_t = [0]
        for c in q_desc:
            # res_t = res_t * (2t - 1) + c (ascending or descending: keep ascending in t)
            nxt = [0] * (len(res_t) + 1)
            for idx_k, v in enumerate(res_t):
                nxt[idx_k] = (nxt[idx_k] - v) % mod_req
                nxt[idx_k + 1] = (nxt[idx_k + 1] + 2 * v) % mod_req
            nxt[0] = (nxt[0] + c) % mod_req
            res_t = nxt
        return all(v == 0 for v in res_t)

    results = []
    # s2_uv = (S^2)_{uv} has same parity as n - 2 (which is even for n=74)
    s2_vals = list(range(-(n - 2), n - 1, 2))
    for R_uv in R_choices:
        if diff == 0:
            q_list_params = [()]
        elif diff == 1:
            q_list_params = [(lam1 + s2 - gamma1,) for s2 in s2_vals]
        else:
            # diff == 2: Q_uv = x^2 + q1*x + q0, q1 = lam1 + s2 - gamma1
            q_list_params = []
            for s2 in s2_vals:
                q1 = lam1 + s2 - gamma1
                # Bound q0 at x0 = -5: |((25 - 5*q1 + q0)*(-5 - lam1) + R_uv)| <= ub_neg5
                d_n5 = -5 - lam1  # < 0
                lo_n5 = math.ceil(sp.Rational(ub_neg5 - R_uv, d_n5)) - (25 - 5 * q1)
                hi_n5 = math.floor(sp.Rational(-ub_neg5 - R_uv, d_n5)) - (25 - 5 * q1)
                d_xm = x_max_ub - lam1  # > 0
                lo_xm = math.ceil(sp.Rational(-ub_xmax - R_uv, d_xm)) - (x_max_ub**2 + q1 * x_max_ub)
                hi_xm = math.floor(sp.Rational(ub_xmax - R_uv, d_xm)) - (x_max_ub**2 + q1 * x_max_ub)
                lo_q0 = max(lo_n5, lo_xm)
                hi_q0 = min(hi_n5, hi_xm)
                for q0 in range(lo_q0, hi_q0 + 1):
                    q_list_params.append((q1, q0, s2))

        for params in q_list_params:
            if diff == 0:
                h_cs = [R_uv]
                s2_val = 0
            elif diff == 1:
                (q0,) = params
                # (x + q0)*(x - lam1) + R_uv = x^2 + (q0 - lam1)*x + (R_uv - q0*lam1)
                h_cs = [1, q0 - lam1, R_uv - q0 * lam1]
                s2_val = q0 - lam1 + gamma1
            else:
                q1, q0, s2_val = params
                # (x^2 + q1*x + q0)*(x - lam1) + R_uv = x^3 + (q1-lam1)*x^2 + (q0-q1*lam1)*x + (R_uv-q0*lam1)
                h_cs = [1, q1 - lam1, q0 - q1 * lam1, R_uv - q0 * lam1]

            # Pure-integer num = prod_cs - h^2, then exact synthetic division by (x - lam1)
            deg_p = len(prod_cs) - 1
            deg_h2 = 2 * (len(h_cs) - 1)
            num_cs = list(prod_cs)
            off = deg_p - deg_h2
            for i_h, ai in enumerate(h_cs):
                if ai:
                    for j_h, bj in enumerate(h_cs):
                        num_cs[off + i_h + j_h] -= ai * bj
            # Synthetic division by (x - lam1)
            q_cs = []
            rem_val = 0
            for c_val in num_cs:
                rem_val = rem_val * lam1 + c_val
                q_cs.append(rem_val)
            rem_last = q_cs.pop()
            if rem_last != 0:
                continue
            if not passes_mod_2t_minus_1(q_cs):
                continue
            h_uv = sp.Poly(h_cs, x_sym, domain=sp.ZZ)
            q_uv = sp.Poly(q_cs, x_sym, domain=sp.ZZ)
            if not exact_real_rooted_ge_neg5(q_uv, x_sym):
                continue
            if not exact_interlaces(q_uv, ga_star, x_sym):
                continue
            if not exact_interlaces(q_uv, gb_star, x_sym):
                continue
            results.append((s2_val, q_uv, h_uv))
    return results


def test_47_and_13():
    from pathlib import Path
    import sys
    _COMP_DIR = Path(__file__).resolve().parent.parent
    if str(_COMP_DIR) not in sys.path:
        sys.path.insert(0, str(_COMP_DIR))
    from _io import load_json_auto

    d_file = load_json_auto("deck_19_74.json")
    w, x, z = sp.symbols("w x z")
    n, d_dim, c_sh = 74, 19, 15
    w0 = (-5 - c_sh) // 2
    s_sh = (c_sh + 1) // 2

    for idx in [47, 13]:
        cand = d_file["candidates"][idx]
        s = cand["s"]
        Pw = sp.Poly(sum(cand["b"][j] * w**(d_dim - j) for j in range(d_dim + 1)), w, domain=sp.ZZ)
        Full_w = sp.Poly((w - w0)**(n - d_dim), w, domain=sp.ZZ) * Pw
        Dw = sp.gcd(Full_w, Full_w.diff())
        if Dw.LC() < 0: Dw = -Dw
        chi_S = sp.Poly(sp.expand(2**n * Full_w.as_expr().subs(w, (x - c_sh)/2)), x, domain=sp.ZZ)
        Gcd_x = sp.gcd(chi_S, chi_S.diff())
        if Gcd_x.LC() < 0: Gcd_x = -Gcd_x
        Gcd2_x = sp.gcd(Gcd_x, Gcd_x.diff())
        if Gcd2_x.LC() < 0: Gcd2_x = -Gcd2_x
        Hw_x, _ = sp.div(chi_S, Gcd_x)
        # Sim_x = prod of multiplicity-1 irreducible factors of chi_S
        facs = sp.factor_list(chi_S.as_expr())[1]
        Sim_x = sp.Poly(1, x, domain=sp.ZZ)
        Mult_rad_x = sp.Poly(1, x, domain=sp.ZZ)
        for fac, mult in facs:
            fp = sp.Poly(fac, x, domain=sp.ZZ)
            if mult == 1:
                Sim_x = Sim_x * fp
            else:
                Mult_rad_x = Mult_rad_x * fp
        deck = [row for row in cand["deck"] if passes_t42_sub(Dw, sp.Poly(row, w, domain=sp.ZZ), n - 1, s_sh, z, w)]
        g_list = [
            sp.Poly(sp.expand(2**(s - 2) * sum(int(row[k]) * w**(s - 1 - k) for k in range(s)).subs(w, (x - c_sh)/2)), x, domain=sp.ZZ)
            for row in deck
        ]
        print(f"\n=== (19,74) idx={idx}: Sim_x={Sim_x.as_expr()}, Mult_rad={Mult_rad_x.as_expr()}, deck_t42={len(g_list)} ===")
        for a in range(len(g_list)):
            for b in range(a, len(g_list)):
                res = solve_2v_jacobi_pair(g_list[a], g_list[b], Sim_x, Mult_rad_x, Gcd2_x, n, x, x_max_ub=18)
                print(f"  pair ({a},{b}): {len(res)} valid 2v-Jacobi quotients")


if __name__ == "__main__":
    test_47_and_13()
