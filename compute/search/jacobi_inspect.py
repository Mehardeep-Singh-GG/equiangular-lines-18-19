"""Detailed exact 2-vertex Jacobi & algebraic inspection of:
  1. (18, 59) idx=861 (verify k_u + 2v(4,9) -> X Y + Y Z = 8 Y -> Frobenius contradiction)
  2. (19, 74) idx=47  (enumerate ALL exact 2v-Jacobi solutions for all 6 block pairs)
"""

from __future__ import annotations
import json
import math
import itertools
from pathlib import Path
import sympy as sp

from attack_861_and_47 import load_candidate, reconstruct_polys_x


def exact_real_rooted_and_ge_neg5(poly_x: sp.Poly, x: sp.Symbol) -> bool:
    """Exact Sturm count checking all roots of poly_x are real and >= -5."""
    sf = sp.sqf_list(poly_x.as_expr())[1]
    for fac, _ in sf:
        p = sp.Poly(fac, x, domain=sp.ZZ)
        deg = p.degree()
        if deg == 0:
            continue
        if p.eval(-5) == 0:
            # Factor out (x+5) and check remaining roots >= -5
            p, _ = sp.div(p, sp.Poly(x + 5, x, domain=sp.ZZ))
            deg = p.degree()
            if deg == 0:
                continue
        if sp.count_roots(p, -5, None) != deg:
            return False
    return True


def exact_interlaces(num_poly: sp.Poly, sub_poly: sp.Poly, x: sp.Symbol) -> bool:
    """Exact float-free Cauchy interlacing check: sub_poly interlaces num_poly."""
    g = sp.gcd(num_poly, sub_poly)
    A = sp.Poly(sp.div(num_poly, g)[0], x, domain=sp.ZZ)
    B = sp.Poly(sp.div(sub_poly, g)[0], x, domain=sp.ZZ)
    dA, dB = A.degree(), B.degree()
    if dA != dB + 1:
        return False
    # Check signs of B at roots of A alternate (using exact CRootOf)
    # Wait: equivalently, if A is square-free (always true after gcd? Wait: A could have repeated roots if mult(num) > mult(sub)+1, impossible by interlacing!).
    if not A.is_sqf or not B.is_sqf:
        return False
    roots_A = [sp.CRootOf(A.as_expr(), i) for i in range(dA)]
    roots_B = [sp.CRootOf(B.as_expr(), i) for i in range(dB)]
    for i in range(dB):
        if not (roots_A[i] < roots_B[i] < roots_A[i + 1]):
            return False
    return True


def passes_2adic(poly_x: sp.Poly, m: int, x: sp.Symbol) -> bool:
    """Proposition 7.3 + Theorem 4.2 on order-m Seidel matrix."""
    t = sp.Symbol("t")
    pt = sp.Poly(sp.expand(poly_x.as_expr().subs(x, 2 * t - 1)), t, domain=sp.ZZ)
    cs = [int(c) for c in pt.all_coeffs()]
    if m % 2 == 0:
        mod = 1 << m
        return all(c % mod == 0 for c in cs)
    else:
        mod_base = 1 << (m - 1)
        if any(c % mod_base != 0 for c in cs):
            return False
        cs4 = [(c // mod_base) % 4 for c in cs]
        while len(cs4) < m + 1:
            cs4 = [0] + cs4
        half = (m - 1) // 2
        q_mod2 = [cs4[2 * k + 1] % 2 for k in range(half + 1)]
        q2 = [0] * m
        for i in range(half + 1):
            for j in range(half + 1):
                q2[i + j] = (q2[i + j] + q_mod2[i] * q_mod2[j]) % 4
        neg_m4 = (-m) % 4
        rhs = [0] * (m + 1)
        for i in range(m):
            rhs[i] = (rhs[i] + 2 * q2[i]) % 4
            rhs[i + 1] = (rhs[i + 1] + neg_m4 * q2[i]) % 4
        return cs4 == rhs


def solve_2v_jacobi_pair(
    chi_S: sp.Poly,
    Gcd_x: sp.Poly,
    H_x: sp.Poly,
    g_a: sp.Poly,
    g_b: sp.Poly,
    n: int,
    x: sp.Symbol,
    require_same_sign_at_root: sp.Poly = None,
) -> List[dict]:
    """Exact diff <= 2 solver for g_a * g_b - H_x * ... -> chi_{S_uv}."""
    facs = sp.factor_list(chi_S.as_expr())[1]
    Sim_expr = sp.Integer(1)
    for fac, mult in facs:
        if mult == 1:
            Sim_expr *= fac
    Sim_x = sp.Poly(Sim_expr, x, domain=sp.ZZ)
    Gcd_2 = sp.gcd(Gcd_x, Gcd_x.diff())
    # Notice: (Gcd_x^2 / Gcd_2) * q_{uv} = chi_S * chi_{S_uv} / Gcd_x^2?
    # Wait: chi_S * chi_{S_uv} = chi_{S_u} * chi_{S_v} - adj_{uv}^2
    # Divide by Gcd_x^2:
    #   (H_x / Gcd_x) * chi_{S_uv} = g_a * g_b - h_{uv}^2
    # Write chi_{S_uv} = Gcd_2 * q_{uv}. Since Gcd_x / Gcd_2 = rad(Gcd_x),
    #   (H_x / rad(Gcd_x)) * q_{uv} = g_a * g_b - h_{uv}^2!
    rad_Gcd, _ = sp.div(Gcd_x, Gcd_2)
    M_poly, rem_rad = sp.div(H_x, rad_Gcd)
    assert rem_rad.is_zero, f"rad(Gcd_x) did not divide H_x!"
    # Actually M_poly == Sim_x!
    assert M_poly == Sim_x, f"M_poly={M_poly.as_expr()} != Sim_x={Sim_x.as_expr()}"

    s = H_x.degree()
    e_sim = Sim_x.degree()
    diff = (s - 2) - e_sim
    assert 0 <= diff <= 2, f"Unsupported diff={diff}"

    # CRT square roots of g_a * g_b mod Sim_x
    prod_ab = sp.Poly(g_a * g_b, x, domain=sp.ZZ)
    sim_facs = [sp.Poly(fac, x, domain=sp.ZZ) for fac, _ in sp.factor_list(Sim_x.as_expr())[1]]

    def mod_sq_roots(poly_f: sp.Poly) -> List[sp.Poly]:
        # Solve R^2 === prod_ab (mod poly_f) for irreducible factor poly_f of deg <= 2
        rem = sp.rem(sp.Poly(poly_f.as_expr(), x, domain=sp.QQ), poly_f)  # wait: prod_ab mod poly_f!
        rem = sp.rem(sp.Poly(prod_ab.as_expr(), x, domain=sp.QQ), poly_f)
        if rem.is_zero:
            return [sp.Poly(0, x, domain=sp.QQ)]
        if poly_f.degree() == 1:
            r = sp.Rational(-poly_f.coeff_monomial(1), poly_f.LC())
            val = sp.Rational(rem.eval(r))
            if val < 0:
                return []
            sp_n, sq_n = math.isqrt(val.p), math.isqrt(val.q)
            if sp_n * sp_n != val.p or sq_n * sq_n != val.q:
                return []
            rt = sp.Rational(sp_n, sq_n)
            return [sp.Poly(rt, x, domain=sp.QQ), sp.Poly(-rt, x, domain=sp.QQ)]
        else:
            # rem = c0 + c1*x; solve (a + b*x)^2 === c0 + c1*x mod (x^2 + p*x + q) in exact QQ
            p_c = sp.Rational(poly_f.coeff_monomial(x), poly_f.LC())
            q_c = sp.Rational(poly_f.coeff_monomial(1), poly_f.LC())
            c0 = sp.Rational(rem.eval(0))
            c1 = sp.Rational(rem.coeff_monomial(x)) if rem.degree() >= 1 else sp.Rational(0)
            a_v, b_v = sp.symbols("a_v b_v")
            sols_ab = sp.solve([a_v**2 - q_c * b_v**2 - c0, 2 * a_v * b_v - p_c * b_v**2 - c1], [a_v, b_v], dict=True)
            out = []
            for sd in sols_ab:
                av, bv = sd[a_v], sd[b_v]
                if av.is_Rational and bv.is_Rational:
                    out.append(sp.Poly(av + bv * x, x, domain=sp.QQ))
            return out

    # CRT combine across sim_facs
    crt_roots = [sp.Poly(0, x, domain=sp.QQ)]
    mod_acc = sp.Poly(1, x, domain=sp.QQ)
    for pf in sim_facs:
        pf_q = sp.Poly(pf.as_expr(), x, domain=sp.QQ)
        local_roots = mod_sq_roots(pf)
        if not local_roots:
            return []
        new_crt = []
        _, _, _ = sp.gcdex(mod_acc, pf_q)
        inv_m = sp.invert(mod_acc, pf_q)
        for r_acc in crt_roots:
            for r_loc in local_roots:
                diff_r = sp.rem(r_loc - r_acc, pf_q)
                comb = sp.rem(r_acc + mod_acc * sp.rem(diff_r * inv_m, pf_q), mod_acc * pf_q)
                new_crt.append(comb)
        crt_roots = new_crt
        mod_acc = mod_acc * pf_q

    # Exact c1_gcd = [x^{deg_g-1}] Gcd_x (raw coeff, NOT negated!)
    deg_g = Gcd_x.degree()
    gamma_1 = int(Gcd_x.coeff_monomial(x ** (deg_g - 1))) if deg_g >= 1 else 0
    S1_sim = -int(Sim_x.coeff_monomial(x ** (e_sim - 1))) if e_sim >= 1 else 0

    # Determine x_hi bound for diff == 2 (largest root of Sim_x + 1, or 30)
    x_hi = 30
    chi_u_x = Gcd_x * g_a
    chi_v_x = Gcd_x * g_b

    solutions = []
    for s_uv in (-1, 1):
        # Determine valid S2_uv range: |S2_uv| <= n - 2 and S2_uv === n - 2 (mod 2)
        # Wait: even sharper, if diff == 0, Q_uv = s_uv uniquely fixes (S^2)_uv!
        # Let's check for each R_uv in crt_roots:
        for R_uv in crt_roots:
            if diff == 0:
                Q_list = [(None, sp.Poly(s_uv, x, domain=sp.QQ))]
            elif diff == 1:
                Q_list = []
                for S2_uv in range(-(n - 2), n - 1, 2):
                    q0 = S2_uv - gamma_1 * s_uv + s_uv * S1_sim
                    Q_list.append((S2_uv, sp.Poly(s_uv * x + q0, x, domain=sp.QQ)))
            else:  # diff == 2
                Q_list = []
                for S2_uv in range(-(n - 2), n - 1, 2):
                    q1 = S2_uv - gamma_1 * s_uv + s_uv * S1_sim
                    # Bound q0 from h_uv(x0)^2 <= g_a(x0)*g_b(x0) at x0 = -5 and x0 = x_hi
                    # Wait: Sim_x(-5) * q_uv(-5) >= 0 and Sim_x(x_hi) * q_uv(x_hi) >= 0!
                    # Let's verify sign of Sim_x(x0) * q_uv(x0):
                    # Both Sim_x and q_uv are monic with all roots >= -5.
                    # If x0 = x_hi > max root of Sim_x and q_uv (note max eig <= n-1):
                    # actually let x0 = n (strictly > max eig <= n-1 and > -5), then Sim_x(n) > 0 and q_uv(n) > 0!
                    # And at x0 = -5: if Sim_x(-5) == 0, skip -5; else Sim_x(-5) has sign (-1)^{e_sim},
                    # wait: q_uv(-5) >= 0 or == 0? q_uv has deg = n - 2 - Gcd_2.deg()!
                    # Actually if q_uv(-5) == 0 then h_uv(-5)^2 = g_a(-5)g_b(-5), else sign of q_uv(-5) is (-1)^{deg q_uv}!
                    # Since Sim_x(-5) * q_uv(-5) >= 0? Wait: check (-1)^{e_sim + deg_q}:
                    # e_sim + deg_q = (n - 2) - deg(Gcd_2) - ... wait: deg(g_a) + deg(g_b) = 2s - 2,
                    # e_sim + deg_q = 2s - 2? No, Gcd_x * h_uv has deg n-2, and chi_S * chi_{uv} has deg 2n-2,
                    # Wait: deg(Sim_x) + deg(q_uv) = (s - deg(Mult_rad)) + ... = deg(g_a) + deg(g_b) = 2s - 2 (even!)
                    # Wait: is e_sim + deg(q_uv) ALWAYS even?!
                    # Check: deg(g_a) + deg(g_b) = 2s - 2 (EVEN!), and h_{uv}^2 has deg 2s - 4 < 2s - 2,
                    # so deg(Sim_x * q_{uv}) = 2s - 2 (EVEN!!).
                    # Thus at x = -5 (since all roots of Sim_x and q_{uv} are >= -5), Sim_x(-5) * q_{uv}(-5) >= 0 ALWAYS!
                    # That means h_{uv}(-5)^2 <= g_a(-5)*g_b(-5) ALWAYS holds!
                    x_test = -5
                    rhs_bound = float(g_a.eval(x_test) * g_b.eval(x_test))
                    if rhs_bound < -1e-9:
                        continue
                    # At x_test = -5: h(-5) = (s_uv*25 - 5*q1 + q0) * Sim(-5) + R(-5)
                    Sim_m5 = sp.Rational(Sim_x.eval(-5))
                    assert Sim_m5 != 0
                    R_m5 = sp.Rational(R_uv.eval(-5))
                    lin_m5 = sp.Rational(s_uv * 25 - 5 * q1)
                    # |(lin_m5 + q0)*Sim_m5 + R_m5| <= sqrt(g_a(-5)*g_b(-5))
                    val_prod_m5 = int(g_a.eval(-5) * g_b.eval(-5))
                    rad_m5 = math.isqrt(val_prod_m5) + 1
                    lo1 = math.ceil((-rad_m5 - R_m5) / abs(Sim_m5) - lin_m5 if Sim_m5 > 0 else (-rad_m5 + R_m5) / abs(Sim_m5) - lin_m5)
                    # Simpler exact: compute center and radius safely with +2 margin!
                    center_m5 = -R_m5 / Sim_m5 - lin_m5
                    half_w_m5 = sp.Rational(rad_m5) / abs(Sim_m5) + 2
                    lo = math.floor(center_m5 - half_w_m5)
                    hi = math.ceil(center_m5 + half_w_m5)
                    # Also intersect with x_test = n (strictly > all eigenvalues!)
                    val_prod_n = int(g_a.eval(n) * g_b.eval(n))
                    if val_prod_n >= 0:
                        rad_n = math.isqrt(val_prod_n) + 1
                        Sim_n = sp.Rational(Sim_x.eval(n))
                        R_n = sp.Rational(R_uv.eval(n))
                        lin_n = sp.Rational(s_uv * n * n + n * q1)
                        center_n = -R_n / Sim_n - lin_n
                        half_w_n = sp.Rational(rad_n) / abs(Sim_n) + 2
                        lo = max(lo, math.floor(center_n - half_w_n))
                        hi = min(hi, math.ceil(center_n + half_w_n))
                    for q0 in range(lo, hi + 1):
                        Q_list.append((S2_uv, sp.Poly(s_uv * x * x + q1 * x + q0, x, domain=sp.QQ)))

            for S2_uv, Q_poly in Q_list:
                h_uv = Q_poly * sp.Poly(Sim_x.as_expr(), x, domain=sp.QQ) + R_uv
                # Check integer coefficients
                if not all(c.is_Integer for c in h_uv.all_coeffs()):
                    continue
                h_uv_z = sp.Poly(h_uv.as_expr(), x, domain=sp.ZZ)
                if require_same_sign_at_root is not None:
                    # Check h_uv and g_a have same sign at roots of require_same_sign_at_root
                    r0 = sp.Rational(-require_same_sign_at_root.coeff_monomial(1), require_same_sign_at_root.LC())
                    if h_uv_z.eval(r0) * g_a.eval(r0) <= 0:
                        continue
                num = sp.Poly(g_a * g_b - h_uv_z * h_uv_z, x, domain=sp.ZZ)
                q_uv, rem_q = sp.div(num, Sim_x)
                if not rem_q.is_zero:
                    continue
                chi_uv = Gcd_2 * q_uv
                if chi_uv.LC() != 1:
                    continue
                # Recover S2_uv if diff==0
                if S2_uv is None:
                    # [x^{s-3}] h_uv = S2_uv - gamma_1 * s_uv
                    c_s3 = int(h_uv_z.coeff_monomial(x ** (s - 3))) if s >= 3 else 0
                    S2_uv_val = c_s3 + gamma_1 * s_uv
                else:
                    S2_uv_val = S2_uv
                # Check 2-adic on order n-2
                if not passes_2adic(chi_uv, n - 2, x):
                    continue
                if not exact_real_rooted_and_ge_neg5(chi_uv, x):
                    continue
                if not (exact_interlaces(chi_u_x, chi_uv, x) and exact_interlaces(chi_v_x, chi_uv, x)):
                    continue
                solutions.append({
                    "s_uv": s_uv,
                    "S2_uv": S2_uv_val,
                    "h_uv": str(h_uv_z.as_expr()),
                    "chi_uv": str(sp.factor(chi_uv.as_expr())),
                    "q_uv": str(sp.factor(q_uv.as_expr())),
                })
    return solutions


def main():
    x = sp.Symbol("x")

    # 1. Verify (18, 59) idx=861 2v-Jacobi between deck[4] (30) and deck[9] (28)
    print("=== (18, 59) idx=861: Exact 2-vertex Jacobi on all block pairs ===")
    d, n, c_shift, cand861 = load_candidate("deck_18_59.json", 861)
    chi_S, f_x, Gcd_x, H_x, quo_x, deck_x = reconstruct_polys_x(d, n, c_shift, cand861)
    for (a, b) in [(4, 5), (5, 9), (4, 9)]:
        sols = solve_2v_jacobi_pair(chi_S, Gcd_x, H_x, deck_x[a][0], deck_x[b][0], n, x)
        print(f"  pair ({a}, {b}) -> {len(sols)} exact 2v-Jacobi solutions:")
        for sol in sols:
            print(f"    s_uv={sol['s_uv']:+d}, S2_uv={sol['S2_uv']:+3d}, chi_uv={sol['chi_uv']}")

    # 2. Verify (19, 74) idx=47 2v-Jacobi on all 6 block pairs!
    print("\n=== (19, 74) idx=47: Exact 2-vertex Jacobi on all 6 block pairs ===")
    d74, n74, c74, cand47 = load_candidate("deck_19_74.json", 47)
    chi74, f74, Gcd74, H74, quo74, deck74 = reconstruct_polys_x(d74, n74, c74, cand47)
    sim11 = sp.Poly(x - 11, x, domain=sp.ZZ)
    for (a, b) in [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)]:
        req = sim11 if (a == 1 and b == 1) else None
        sols = solve_2v_jacobi_pair(chi74, Gcd74, H74, deck74[a][0], deck74[b][0], n74, x, require_same_sign_at_root=req)
        print(f"  pair ({a}, {b}) -> {len(sols)} exact 2v-Jacobi solutions:")
        for sol in sols:
            print(f"    s_uv={sol['s_uv']:+d}, S2_uv={sol['S2_uv']:+3d}, chi_uv={sol['chi_uv']}")


if __name__ == "__main__":
    main()
