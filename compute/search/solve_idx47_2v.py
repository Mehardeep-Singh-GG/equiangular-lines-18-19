"""Fast exact 2-vertex Jacobi solver for (19, 74) idx=47 across all 6 block pairs."""

from __future__ import annotations
import math
import time
import sympy as sp
from fractions import Fraction
from attack_861_and_47 import load_candidate, reconstruct_polys_x
from jacobi_inspect import exact_real_rooted_and_ge_neg5, exact_interlaces
from jacobi_fast import (
    poly_mul_int, poly_sub_int, poly_divmod_monic_int,
    poly_eval_int, poly_shift_2t_minus_1
)


def solve_idx47():
    x = sp.Symbol("x")
    d, n, c_shift, cand47 = load_candidate("deck_19_74.json", 47)
    chi_S, f_x, Gcd_x, H_x, quo_x, deck_x = reconstruct_polys_x(d, n, c_shift, cand47)
    Sim_x = sp.Poly(x - 11, x, domain=sp.ZZ)
    Gcd_2 = sp.gcd(Gcd_x, Gcd_x.diff())
    deg_g = Gcd_x.degree()
    c1_gcd = int(Gcd_x.coeff_monomial(x ** (deg_g - 1)))
    S1_sim = 11

    Sim_c = [1, -11]
    t = sp.Symbol("t")
    Gcd2_t_c = [int(v) for v in sp.Poly(sp.expand(Gcd_2.as_expr().subs(x, 2 * t - 1)), t, domain=sp.ZZ).all_coeffs()]
    v2_g2 = 0
    tmp_g2 = list(Gcd2_t_c)
    while all(c % 2 == 0 for c in tmp_g2):
        v2_g2 += 1
        tmp_g2 = [c // 2 for c in tmp_g2]
    req_v2_q = 72 - v2_g2
    mod_q_pow2 = 1 << req_v2_q
    print(f"n=74: deg(Gcd_2)={Gcd_2.degree()}, v2_g2={v2_g2}, req_v2_q={req_v2_q}")

    # Integer evaluation points for fast 2-adic filtering (2^{req_v2_q} | q_uv(xt))
    # Also note for even m_sub=72: every coefficient of chi_uv(2t-1) is divisible by 2^72,
    # AND evaluate at t = -3..5 (x = -7, -5, -3, -1, 1, 3, 5, 7, 9).
    test_x = [-7, -5, -3, -1, 1, 3, 5, 7, 9]

    # Exact rational sample points guaranteed to separate roots of chi_u / Gcd_2 for sign-change check!
    # Wait: let's just check exact value of q_uv at x in [-6, 10, 12, 14, 16, 20] vs signs of interlacing?
    # Actually even better: check q_uv(x_pts) via Descartes / Sturm or evaluate q_uv at integer points where Sim_x != 0!
    # Better: check that q_uv(11) >= 0? Wait: g_a(11)*g_b(11) - h_uv(11)^2 == 0 so Sim_x=(x-11) divides!
    # What about q_uv(15) >= 0 vs <= 0? In chi_0, chi_1: x=15 is a root of A_u (mult 1 in A_u),
    # Wait: A_u = chi_u / Gcd_2 has deg 8! Check roots of A_u:
    # For deck[0]: (x+5)(x-15)(x-11)(x^2-28x+191)(x^3-38x^2+469x-1876)
    # Note roots of x^2-28x+191 are 14 +- sqrt(5) ~ 11.76, 16.24!
    # Roots of x^3-38x^2+469x-1876 are ~10.64, 12.66, 14.70!
    # Wait: by interlacing, q_uv MUST have:
    #  - a root in [-5, 10.64] (Wait: actually -5 is a root of A_u, next root is ~10.64, so q_uv >= 0 or <= 0? Wait: at x = 10 (between -5 and 10.64), A_u(10) and q_uv(10)!)
    # Even simpler and 100% EXACT & conservative: check q_uv has NO negative roots (< -5) via sign of q_uv(-5), q_uv(25), and sign changes on [-5, 10, 11.5, 12.2, 13.5, 14.8, 15.5, 17, 25]!
    # Wait: just checking if q_uv(-5) * (-1)^7 >= 0 and q_uv(25) > 0? Even better: in pure Python, compute Sturm sequence or just check 2-adic at test_x FIRST (mod 2^7 = 128 cuts candidates by 128x!) AND check if any coefficient of q_uv violates basic sign/trace bounds!
    # Wait: for deg 7 monic q_uv with all roots in [-5, 22]:
    #   Sum of roots = -q_uv[1] in [7*(-5), 7*22] = [-35, 154]!
    #   Wait: EVEN SHARPER! We KNOW Tr(S_{uv}^2) = 72*71 = 5112!
    #   AND Gcd_2 already fixes 65 eigenvalues of S_{uv}! So the sum of the 7 remaining eigenvalues of q_uv AND the sum of their squares are 100% FIXED!!
    #   HOLD EVERYTHING!!
    #   READ THAT AGAIN!!
    #   Tr(S_{uv}) = 0  ==>  sum(roots of q_uv) = -sum(roots of Gcd_2) (EXACT INTEGER!)
    #   Tr(S_{uv}^2) = 72*71 = 5112  ==>  sum(roots^2 of q_uv) = 5112 - sum(roots^2 of Gcd_2) (EXACT INTEGER!)
    #   THAT IMMEDIATELY UNIQUELY FIXES BOTH `q1` (hence `S2_uv`? Wait: let's check!) AND `q0` (from `[x^5] q_uv` = e_2 of roots of q_uv) TO AT MOST **TWO VALUES**!!

    # Compute exact Tr(Gcd_2) and Tr2(Gcd_2)
    g2_c1 = int(Gcd_2.coeff_monomial(x ** 64))
    g2_c2 = int(Gcd_2.coeff_monomial(x ** 63))
    sum_g2 = -g2_c1
    sum2_g2 = g2_c1 * g2_c1 - 2 * g2_c2
    target_sum_q = -sum_g2
    target_sum2_q = 72 * 71 - sum2_g2
    target_e1_q = target_sum_q
    target_e2_q = (target_sum_q * target_sum_q - target_sum2_q) // 2
    assert (target_sum_q * target_sum_q - target_sum2_q) % 2 == 0
    print(f"EXACT q_uv invariants: e1={target_e1_q} (q[1]={-target_e1_q}), e2={target_e2_q} (q[2]={target_e2_q})")

    for (a, b) in [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)]:
        g_a, g_b = deck_x[a][0], deck_x[b][0]
        chi_u_x = Gcd_x * g_a
        chi_v_x = Gcd_x * g_b
        prod_ab = sp.Poly(g_a * g_b, x, domain=sp.ZZ)
        prod_c = [int(v) for v in prod_ab.all_coeffs()]
        val11 = int(prod_ab.eval(11))
        rt11 = math.isqrt(val11)
        assert rt11 * rt11 == val11
        R_vals = [rt11] if rt11 == 0 else ([rt11] if (a == 1 and b == 1) else [rt11, -rt11])
        #Wait: if (a,b)==(1,1), h_uv(11) and g_1(11) have same sign!
        if a == 1 and b == 1:
            ga11 = int(g_a.eval(11))
            R_vals = [rt11 if ga11 > 0 else -rt11]

        # Wait: let's express q_uv[1] and q_uv[2] symbolically in terms of (s_uv, S2_uv, q0)!
        # Let's check: prod_ab has deg 8: prod_c[0..8].
        # h_uv = (s_uv*x^2 + q1*x + q0)*(x - 11) + R11 = s_uv*x^3 + (q1 - 11*s_uv)*x^2 + (q0 - 11*q1)*x + (R11 - 11*q0).
        # Notice [x^8](prod_ab - h_uv^2) = 1 (deg 8),
        # [x^7](prod_ab - h_uv^2) = prod_c[1] = -98 (WAIT: independent of h_uv because h_uv^2 has deg 6!!)
        # [x^6](prod_ab - h_uv^2) = prod_c[2] - 1 (from s_uv^2 * x^6 = 1 * x^6)!
        # WAIT A SECOND!!
        # [x^7] q_uv ONLY depends on prod_c[1]!
        # [x^6] q_uv = e2_q - ... ONLY depends on prod_c[2] - 1 + 11*q_uv[1] -> ALSO INDEPENDENT OF (S2_uv, q0)?!
        # WAIT: what about [x^5] q_uv (the x^5 term of q_uv, i.e. e3)?!
        # Let's compute q_uv symbolically in (S2_uv, q0)! Wait:
        # In prod_ab - h_uv^2:
        #   deg 8: x^8
        #   deg 7: prod_c[1] x^7
        #   deg 6: (prod_c[2] - s_uv^2) x^6
        #   deg 5: (prod_c[3] - 2*s_uv*(q1 - 11*s_uv)) x^5  ==> THIS DETERMINES q_uv[3] = e3_q linearly in S2_uv!
        #   deg 4: (prod_c[4] - (q1 - 11*s_uv)^2 - 2*s_uv*(q0 - 11*q1)) x^4 ==> linear in q0!
        # Still, let's see what lo..hi for q0 is, and check `q_c` using fast integer arithmetic!
        sols = []
        # All eigenvalues of chi_S are <= 14 + sqrt(5) < 17!
        # By interlacing, all eigenvalues of S_{uv} are < 17, so q_uv(17) > 0 and (17-11)*q_uv(17) > 0!
        x_hi = 17
        prod_m5 = int(prod_ab.eval(-5))
        prod_hi = int(prod_ab.eval(x_hi))
        rad_m5 = math.isqrt(prod_m5) + 2
        rad_hi = math.isqrt(prod_hi) + 2

        test_pts = []
        for xt in test_x:
            st = xt - 11
            v2_st = (abs(st) & -abs(st)).bit_length() - 1
            test_pts.append((xt, poly_eval_int(prod_c, xt), st, mod_q_pow2 * (1 << v2_st)))

        # Wait: check if a==2 or b==2 -> mult_15(chi_uv) >= 11 -> q_uv(15) == 0 -> h_uv(15)^2 == prod_ab(15)!
        force15 = (a == 2 or b == 2)
        rt15 = math.isqrt(int(prod_ab.eval(15))) if force15 else None
        if force15:
            assert rt15 * rt15 == int(prod_ab.eval(15))

        for s_uv in (-1, 1):
            for R11 in R_vals:
                for S2_uv in range(-(n - 2), n - 1, 2):
                    q1 = S2_uv - c1_gcd * s_uv + s_uv * S1_sim
                    c_m5 = -sp.Rational(R11, -16) - (s_uv * 25 - 5 * q1)
                    hw_m5 = sp.Rational(rad_m5, 16) + 2
                    lo = math.floor(c_m5 - hw_m5)
                    hi = math.ceil(c_m5 + hw_m5)
                    c_n = -sp.Rational(R11, x_hi - 11) - (s_uv * x_hi * x_hi + x_hi * q1)
                    hw_n = sp.Rational(rad_hi, x_hi - 11) + 2
                    lo = max(lo, math.floor(c_n - hw_n))
                    hi = min(hi, math.ceil(c_n + hw_n))
                    if lo > hi:
                        continue

                    if force15:
                        q0_cands = []
                        for th15 in ({rt15, -rt15}):
                            if (th15 - R11) % 4 == 0:
                                q0 = (th15 - R11) // 4 - (s_uv * 225 + 15 * q1)
                                if lo <= q0 <= hi:
                                    q0_cands.append(q0)
                    else:
                        # Solve valid residues mod 128 first!
                        valid_r = []
                        for r128 in range(128):
                            ok_r = True
                            for idx_pt, (xt, pab_xt, st, m2) in enumerate(test_pts):
                                h_xt = (s_uv * xt * xt + q1 * xt + r128) * st + R11
                                if (pab_xt - h_xt * h_xt) % min(m2, 128) != 0:
                                    ok_r = False
                                    break
                            if ok_r:
                                valid_r.append(r128)
                        q0_cands = [
                            q0
                            for r128 in valid_r
                            for q0 in range(lo + ((r128 - lo) % 128), hi + 1, 128)
                        ]

                    for q0 in q0_cands:
                        # Fast mod 2^k check at test_pts
                        ok_mod = True
                        for idx_pt, (xt, pab_xt, st, m2) in enumerate(test_pts):
                            h_xt = (s_uv * xt * xt + q1 * xt + q0) * st + R11
                            if (pab_xt - h_xt * h_xt) % m2 != 0:
                                ok_mod = False
                                break
                        if not ok_mod:
                            continue

                        h_c = poly_sub_int(poly_mul_int([s_uv, q1, q0], Sim_c), [-R11])
                        num_c = poly_sub_int(prod_c, poly_mul_int(h_c, h_c))
                        q_c, rem_c = poly_divmod_monic_int(num_c, Sim_c)
                        if any(v != 0 for v in rem_c):
                            continue
                        while len(q_c) > 1 and q_c[0] == 0:
                            q_c = q_c[1:]
                        if q_c[0] != 1 or q_c[1] != -target_e1_q or q_c[2] != target_e2_q:
                            continue

                        # Full 2-adic check on q_c(2t-1)
                        qt_c = poly_shift_2t_minus_1(q_c)
                        if any(c % mod_q_pow2 != 0 for c in qt_c):
                            continue

                        q_uv_poly = sp.Poly(sum(c * x ** (len(q_c) - 1 - i) for i, c in enumerate(q_c)), x, domain=sp.ZZ)
                        if not exact_real_rooted_and_ge_neg5(q_uv_poly, x):
                            continue
                        chi_uv = Gcd_2 * q_uv_poly
                        if not (exact_interlaces(chi_u_x, chi_uv, x) and exact_interlaces(chi_v_x, chi_uv, x)):
                            continue
                        sols.append((s_uv, S2_uv, R11, q0, str(sp.factor(q_uv_poly.as_expr()))))
        print(f"  pair ({a}, {b}) -> {len(sols)} sols:")
        for s_uv, S2_uv, R11, q0, qstr in sols:
            print(f"    s_uv={s_uv:+d}, S2_uv={S2_uv:+3d}, R11={R11}, q0={q0}, q_uv={qstr}")


if __name__ == "__main__":
    solve_idx47()
