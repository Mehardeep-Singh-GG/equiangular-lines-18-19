"""Ultra-fast exact integer 2-vertex Jacobi solver (pure-Python integer arithmetic
for inner loops; SymPy Sturm + CRootOf interlacing only on exact survivors).
"""

from __future__ import annotations
import math
import time
import sympy as sp
from attack_861_and_47 import load_candidate, reconstruct_polys_x
from jacobi_inspect import exact_real_rooted_and_ge_neg5, exact_interlaces


def poly_mul_int(a: list[int], b: list[int]) -> list[int]:
    res = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        for j, bj in enumerate(b):
            res[i + j] += ai * bj
    return res


def poly_sub_int(a: list[int], b: list[int]) -> list[int]:
    n = max(len(a), len(b))
    aa = [0] * (n - len(a)) + a
    bb = [0] * (n - len(b)) + b
    return [x - y for x, y in zip(aa, bb)]


def poly_divmod_monic_int(num: list[int], den: list[int]) -> tuple[list[int], list[int]]:
    assert den[0] == 1
    r = list(num)
    dn = len(num) - len(den)
    if dn < 0:
        return [0], r
    q = [0] * (dn + 1)
    for i in range(dn + 1):
        c = r[i]
        q[i] = c
        if c != 0:
            for j in range(len(den)):
                r[i + j] -= c * den[j]
    rem = r[dn + 1:]
    return q, rem


def poly_eval_int(coeffs: list[int], x_val: int) -> int:
    acc = 0
    for c in coeffs:
        acc = acc * x_val + c
    return acc


def poly_shift_2t_minus_1(coeffs_desc: list[int]) -> list[int]:
    cur = [coeffs_desc[0]] if coeffs_desc else [0]
    for c in coeffs_desc[1:]:
        nxt = [2 * v for v in cur] + [0]
        for i, v in enumerate(cur):
            nxt[i + 1] -= v
        nxt[-1] += c
        cur = nxt
    return cur


def solve_2v_superfast(chi_S, Gcd_x, H_x, g_a, g_b, n, x, require_same_sign_at_root=None):
    facs = sp.factor_list(chi_S.as_expr())[1]
    Sim_expr = sp.Integer(1)
    for fac, mult in facs:
        if mult == 1:
            Sim_expr *= fac
    Sim_x = sp.Poly(Sim_expr, x, domain=sp.ZZ)
    Gcd_2 = sp.gcd(Gcd_x, Gcd_x.diff())
    rad_Gcd, _ = sp.div(Gcd_x, Gcd_2)
    M_poly, _ = sp.div(H_x, rad_Gcd)
    assert M_poly == Sim_x

    s = H_x.degree()
    e_sim = Sim_x.degree()
    diff = (s - 2) - e_sim
    assert 0 <= diff <= 2

    prod_ab = sp.Poly(g_a * g_b, x, domain=sp.ZZ)
    sim_facs = [sp.Poly(fac, x, domain=sp.ZZ) for fac, _ in sp.factor_list(Sim_x.as_expr())[1]]

    def mod_sq_roots(poly_f):
        rem = sp.rem(sp.Poly(prod_ab.as_expr(), x, domain=sp.QQ), poly_f)
        if rem.is_zero:
            return [sp.Poly(0, x, domain=sp.QQ)]
        if poly_f.degree() == 1:
            r = sp.Rational(-poly_f.coeff_monomial(1), poly_f.LC())
            val = sp.Rational(rem.eval(r))
            if val < 0:
                return []
            sn, sq = math.isqrt(val.p), math.isqrt(val.q)
            if sn * sn != val.p or sq * sq != val.q:
                return []
            rt = sp.Rational(sn, sq)
            return [sp.Poly(rt, x, domain=sp.QQ), sp.Poly(-rt, x, domain=sp.QQ)]
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

    crt_roots = [sp.Poly(0, x, domain=sp.QQ)]
    mod_acc = sp.Poly(1, x, domain=sp.QQ)
    for pf in sim_facs:
        pf_q = sp.Poly(pf.as_expr(), x, domain=sp.QQ)
        lr = mod_sq_roots(pf)
        if not lr:
            return []
        inv_m = sp.invert(mod_acc, pf_q)
        crt_roots = [
            sp.rem(ra + mod_acc * sp.rem((rl - ra) * inv_m, pf_q), mod_acc * pf_q)
            for ra in crt_roots for rl in lr
        ]
        mod_acc = mod_acc * pf_q

    int_crt = [R for R in crt_roots if all(c.is_Integer for c in R.all_coeffs())]

    deg_g = Gcd_x.degree()
    # [x^{deg_g-1}] Gcd_x(x): (s_uv*x^4 + beta*x^3)*(x^{deg_g} + c1*x^{deg_g-1}) has [x^{deg_g+3}] = beta + c1*s_uv = S2_uv
    c1_gcd = int(Gcd_x.coeff_monomial(x ** (deg_g - 1))) if deg_g >= 1 else 0
    gamma_1 = c1_gcd  # so beta = S2_uv - gamma_1 * s_uv
    S1_sim = -int(Sim_x.coeff_monomial(x ** (e_sim - 1))) if e_sim >= 1 else 0
    chi_u_x = Gcd_x * g_a
    chi_v_x = Gcd_x * g_b

    Sim_c = [int(v) for v in Sim_x.all_coeffs()]
    prod_c = [int(v) for v in prod_ab.all_coeffs()]
    t = sp.Symbol("t")
    Gcd2_t_c = [int(v) for v in sp.Poly(sp.expand(Gcd_2.as_expr().subs(x, 2 * t - 1)), t, domain=sp.ZZ).all_coeffs()]

    m_sub = n - 2
    v2_g2 = 0
    tmp_g2 = list(Gcd2_t_c)
    while all(c % 2 == 0 for c in tmp_g2):
        v2_g2 += 1
        tmp_g2 = [c // 2 for c in tmp_g2]
    req_v2_total = m_sub if (m_sub % 2 == 0) else (m_sub - 1)
    req_v2_q = max(0, req_v2_total - v2_g2)
    mod_q_pow2 = 1 << req_v2_q

    forced_q_roots = []
    for fac, m_s in facs:
        fp = sp.Poly(fac, x, domain=sp.ZZ)
        if fp.degree() == 1 and m_s >= 2:
            r_int = -int(fp.coeff_monomial(1)) // int(fp.LC())
            def mult_at(p_poly, r_val):
                cnt = 0
                cur = p_poly
                lin = sp.Poly(x - r_val, x, domain=sp.ZZ)
                while True:
                    q_d, rm_d = sp.div(cur, lin)
                    if not rm_d.is_zero:
                        break
                    cnt += 1
                    cur = q_d
                return cnt
            mu = mult_at(chi_u_x, r_int)
            mv = mult_at(chi_v_x, r_int)
            mg2 = mult_at(Gcd_2, r_int)
            if max(mu - 1, mv - 1) > mg2:
                forced_q_roots.append(r_int)

    Sim_m5 = sp.Rational(Sim_x.eval(-5))
    Sim_n = sp.Rational(Sim_x.eval(n))
    prod_m5 = int(prod_ab.eval(-5))
    prod_n = int(prod_ab.eval(n))
    rad_m5 = math.isqrt(prod_m5) + 2
    rad_n = math.isqrt(prod_n) + 2

    test_pts = []
    for tv in range(-2, 5):
        xt = 2 * tv - 1
        st = poly_eval_int(Sim_c, xt)
        if st != 0:
            v2_st = (abs(st) & -abs(st)).bit_length() - 1
            test_pts.append((xt, poly_eval_int(prod_c, xt), st, mod_q_pow2 * (1 << v2_st)))

    solutions = []
    for s_uv in (-1, 1):
        for R_uv in int_crt:
            R_c = [int(v) for v in sp.Poly(R_uv.as_expr(), x, domain=sp.ZZ).all_coeffs()]
            cand_Q = []
            if diff == 0:
                h_c = poly_sub_int(poly_mul_int([s_uv], Sim_c), [-v for v in R_c])
                c_s3 = h_c[1] if len(h_c) >= 2 else 0
                cand_Q.append((c_s3 + gamma_1 * s_uv, [s_uv]))
            elif diff == 1:
                for S2_uv in range(-(n - 2), n - 1, 2):
                    q0 = S2_uv - gamma_1 * s_uv + s_uv * S1_sim
                    cand_Q.append((S2_uv, [s_uv, q0]))
            else:
                R_m5 = poly_eval_int(R_c, -5)
                R_n = poly_eval_int(R_c, n)
                R_pts = [poly_eval_int(R_c, xt) for xt, _, _, _ in test_pts]
                R_forced = [poly_eval_int(R_c, rf) for rf in forced_q_roots]
                Sim_forced = [poly_eval_int(Sim_c, rf) for rf in forced_q_roots]
                prod_forced = [poly_eval_int(prod_c, rf) for rf in forced_q_roots]

                for S2_uv in range(-(n - 2), n - 1, 2):
                    q1 = S2_uv - gamma_1 * s_uv + s_uv * S1_sim
                    c_m5 = -sp.Rational(R_m5, Sim_m5) - (s_uv * 25 - 5 * q1)
                    hw_m5 = sp.Rational(rad_m5, abs(Sim_m5)) + 2
                    lo = math.floor(c_m5 - hw_m5)
                    hi = math.ceil(c_m5 + hw_m5)
                    c_n = -sp.Rational(R_n, Sim_n) - (s_uv * n * n + n * q1)
                    hw_n = sp.Rational(rad_n, abs(Sim_n)) + 2
                    lo = max(lo, math.floor(c_n - hw_n))
                    hi = min(hi, math.ceil(c_n + hw_n))
                    if lo > hi:
                        continue

                    if forced_q_roots:
                        rf = forced_q_roots[0]
                        sf_val = Sim_forced[0]
                        pf_val = prod_forced[0]
                        rt = math.isqrt(pf_val)
                        if rt * rt != pf_val:
                            continue
                        q0_cands = []
                        for target_h in (rt, -rt):
                            num_q0 = target_h - R_forced[0]
                            if num_q0 % sf_val == 0:
                                q0 = num_q0 // sf_val - (s_uv * rf * rf + q1 * rf)
                                if lo <= q0 <= hi:
                                    q0_cands.append(q0)
                    else:
                        q0_cands = range(lo, hi + 1)

                    for q0 in q0_cands:
                        ok_mod = True
                        for idx_pt, (xt, pab_xt, st, m2) in enumerate(test_pts):
                            h_xt = (s_uv * xt * xt + q1 * xt + q0) * st + R_pts[idx_pt]
                            if (pab_xt - h_xt * h_xt) % m2 != 0:
                                ok_mod = False
                                break
                        if ok_mod:
                            cand_Q.append((S2_uv, [s_uv, q1, q0]))

            for S2_uv, Q_c in cand_Q:
                h_c = poly_sub_int(poly_mul_int(Q_c, Sim_c), [-v for v in R_c])
                if require_same_sign_at_root is not None:
                    r0 = -int(require_same_sign_at_root.coeff_monomial(1)) // int(require_same_sign_at_root.LC())
                    ga_c = [int(v) for v in g_a.all_coeffs()]
                    if poly_eval_int(h_c, r0) * poly_eval_int(ga_c, r0) <= 0:
                        continue
                num_c = poly_sub_int(prod_c, poly_mul_int(h_c, h_c))
                q_c, rem_c = poly_divmod_monic_int(num_c, Sim_c)
                if any(v != 0 for v in rem_c):
                    continue
                while len(q_c) > 1 and q_c[0] == 0:
                    q_c = q_c[1:]
                if q_c[0] != 1:
                    continue
                qt_c = poly_shift_2t_minus_1(q_c)
                if any(c % mod_q_pow2 != 0 for c in qt_c):
                    continue
                if m_sub % 2 == 1:
                    chi_t = poly_mul_int(tmp_g2, [c // mod_q_pow2 for c in qt_c])
                    cs4 = [c % 4 for c in chi_t]
                    while len(cs4) < m_sub + 1:
                        cs4 = [0] + cs4
                    half = (m_sub - 1) // 2
                    q_mod2 = [cs4[2 * k + 1] % 2 for k in range(half + 1)]
                    q2 = [0] * m_sub
                    for i in range(half + 1):
                        for j in range(half + 1):
                            q2[i + j] = (q2[i + j] + q_mod2[i] * q_mod2[j]) % 4
                    neg_m4 = (-m_sub) % 4
                    rhs4 = [0] * (m_sub + 1)
                    for i in range(m_sub):
                        rhs4[i] = (rhs4[i] + 2 * q2[i]) % 4
                        rhs4[i + 1] = (rhs4[i + 1] + neg_m4 * q2[i]) % 4
                    if cs4 != rhs4:
                        continue

                q_uv_poly = sp.Poly(sum(c * x ** (len(q_c) - 1 - i) for i, c in enumerate(q_c)), x, domain=sp.ZZ)
                if not exact_real_rooted_and_ge_neg5(q_uv_poly, x):
                    continue
                chi_uv = Gcd_2 * q_uv_poly
                if not (exact_interlaces(chi_u_x, chi_uv, x) and exact_interlaces(chi_v_x, chi_uv, x)):
                    continue
                h_uv_poly = sp.Poly(sum(c * x ** (len(h_c) - 1 - i) for i, c in enumerate(h_c)), x, domain=sp.ZZ)
                solutions.append({
                    "s_uv": s_uv,
                    "S2_uv": S2_uv,
                    "h_uv": str(h_uv_poly.as_expr()),
                    "q_uv": str(sp.factor(q_uv_poly.as_expr())),
                    "chi_uv": str(sp.factor(chi_uv.as_expr())),
                })
    return solutions


def main():
    x = sp.Symbol("x")
    print("=== (18, 59) idx=861 ===")
    d, n, c_shift, cand861 = load_candidate("deck_18_59.json", 861)
    chi_S, f_x, Gcd_x, H_x, quo_x, deck_x = reconstruct_polys_x(d, n, c_shift, cand861)
    for (a, b) in [(4, 5), (5, 9), (4, 9)]:
        sols = solve_2v_superfast(chi_S, Gcd_x, H_x, deck_x[a][0], deck_x[b][0], n, x)
        print(f"  pair ({a}, {b}) -> {len(sols)} sols:")
        for s in sols:
            print(f"    s_uv={s['s_uv']:+d}, S2_uv={s['S2_uv']:+3d}, q_uv={s['q_uv']}")

    print("\n=== (19, 74) idx=47 ===")
    d74, n74, c74, cand47 = load_candidate("deck_19_74.json", 47)
    chi74, f74, Gcd74, H74, quo74, deck74 = reconstruct_polys_x(d74, n74, c74, cand47)
    sim11 = sp.Poly(x - 11, x, domain=sp.ZZ)
    for (a, b) in [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)]:
        req = sim11 if (a == 1 and b == 1) else None
        sols = solve_2v_superfast(chi74, Gcd74, H74, deck74[a][0], deck74[b][0], n74, x, require_same_sign_at_root=req)
        print(f"  pair ({a}, {b}) -> {len(sols)} sols:")
        for s in sols:
            print(f"    s_uv={s['s_uv']:+d}, S2_uv={s['S2_uv']:+3d}, q_uv={s['q_uv']}")


if __name__ == "__main__":
    main()
