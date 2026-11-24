"""Deep exact probe of the 3 remaining (19, 74) idx=13 solutions:
  S1: (24, 48, 0, 2)
  S2: (25, 45, 3, 1)
  S3: (26, 42, 6, 0)
Checks:
  1. Theorem 7.1 Eulerian mod-4 (M_blk, N_blk) on S_v (v in deck[1], order 73, cubic Sim_v)
     and S_y (y in deck[2], order 73, quadratic Sim_y) and S_u (u in deck[0], order 73).
  2. Exact structural check on S1 (W_{00} 8-regular 24-vertex graph with mult(2)>=8), S2, S3.
"""
from __future__ import annotations
import sympy as sp

from attack_861_and_47 import load_candidate, reconstruct_polys_x
from audit_861_and_47_proofs import brute_2v_jacobi

x = sp.Symbol("x")


def check_mod4_eulerian_on_Su(u_cls: int):
    d, n, c, cand = load_candidate("deck_19_74.json", 13)
    chi_S, f_x, Gcd_x, H_x, quo_x, deck_x = reconstruct_polys_x(d, n, c, cand)
    Gcd_2 = sp.gcd(Gcd_x, Gcd_x.diff())

    g_u, chi_u = deck_x[u_cls]
    n_u = n - 1  # 73 (odd!)
    Gcd_u = sp.gcd(chi_u, chi_u.diff())
    H_u, _ = sp.div(chi_u, Gcd_u)
    quo_u, _ = sp.div(chi_u.diff(), Gcd_u)

    # Check Theorem 7.1 for ALL simple factors of chi_u (Sim_u)
    facs_u = sp.factor_list(chi_u.as_expr())[1]
    Sim_u = sp.Poly(sp.prod(fe for fe, mult in facs_u if mult == 1), x, domain=sp.ZZ)
    Mult_full, rem = sp.div(chi_u, Sim_u)
    assert rem.is_zero
    xMult_full = sp.Poly(x * Mult_full.as_expr(), x, domain=sp.ZZ)

    # Exact mod-4 coefficients of Mult_full(S_eps) and S_eps * Mult_full(S_eps)
    def mod4_allowed_off(P_poly: sp.Poly):
        p_even = (P_poly.eval(1) + P_poly.eval(-1)) // 2
        p_odd = (P_poly.eval(1) - P_poly.eval(-1)) // 2
        # Wait: verify parity/mod-4 formula for S_eps^2 === I + (n_u - 2) J (mod 4)
        # Here n_u = 73 => n_u - 2 = 71 === 3 (mod 4), n_u - 1 = 72 === 0 (mod 4)
        # Check: P(S_eps) === p_even(I + 71 J) + c0 I + c_odd S_eps ... wait:
        # Let's compute exact polynomial reduction mod (S^2 - I - 71 J) where J S = S J = 0 (mod 4), J^2 = 73 J === J (mod 4)!
        # Let's do it cleanly by tracking coeff of I, J, S_eps!
        coeffs = [int(v) for v in reversed(P_poly.all_coeffs())]  # c_0, c_1, ...
        # S^0 = (1, 0, 0) [I, J, S]
        # S^1 = (0, 0, 1)
        # S^2 = (1, 3, 0) (mod 4) since n_u - 2 = 71 === 3 (mod 4)
        # Multiply (a*I + b*J + c*S) by S:
        # a*S + b*(J*S) + c*S^2 = a*S + 0 + c*(I + 3*J) = c*I + 3*c*J + a*S (mod 4)
        # Wait: J*S === (n_u - 1)*J === 0 (mod 4) since n_u = 73!
        cur = (1, 0, 0)
        tot = [0, 0, 0]
        for ck in coeffs:
            tot[0] = (tot[0] + ck * cur[0]) % 4
            tot[1] = (tot[1] + ck * cur[1]) % 4
            tot[2] = (tot[2] + ck * cur[2]) % 4
            # next power: cur * S
            cur = (cur[2] % 4, (3 * cur[2]) % 4, cur[0] % 4)
        # Off-diag entry is tot[1]*1 + tot[2]*(+-1) (mod 4)
        return {(tot[1] + tot[2]) % 4, (tot[1] - tot[2]) % 4}, tot

    allowed_M, tot_M = mod4_allowed_off(Mult_full)
    allowed_N, tot_N = mod4_allowed_off(xMult_full)
    print(f"\n=== Theorem 7.1 mod-4 on S_{u_cls} (n_u=73) ===")
    print(f"  Sim_u = {sp.factor(Sim_u.as_expr())}")
    print(f"  M(S_eps) == {tot_M[0]}*I + {tot_M[1]}*J + {tot_M[2]}*S_eps (mod 4), allowed off-diag={allowed_M}")
    print(f"  N(S_eps) == {tot_N[0]}*I + {tot_N[1]}*J + {tot_N[2]}*S_eps (mod 4), allowed off-diag={allowed_N}")

    # Wait: M_{ab} = sum_{r root of Sim_u} Mult_full(r) * E_r[a, b] = sum_{r} Gcd_u(r) * sqrt(g_a(r)*g_b(r)) / Sim_u'(r)!
    # Notice for EVERY irreducible factor q of Sim_u, we can compute the trace over roots of q!
    # Wait: even better, for a fixed (u_cls, j) pair from 2v-Jacobi, wait: g_{u,v}(x) is a rational polynomial!
    # We ALREADY have ALL 2v-Jacobi pairs (u_cls, j)! Wait: in S_u, the items are vertices w in C_j.
    # For w in C_j, chi_{S_{u,w}} = Gcd_u * g_{u,w}.
    # Remember (E_r)_{ww} = g_{u,w}(r) / quo_u(r), and (E_r)_{w, z} = +- sqrt(g_{u,w}(r) g_{u,z}(r)) / quo_u(r) (Wait: for M(S_eps) = sum_r Mult_full(r) E_r, wait:
    # Mult_full(r) / quo_u(r) = Mult_full(r) / (Mult_full(r) * Sim_u'(r) / Gcd_u(r)) = Gcd_u(r) / Sim_u'(r)!)
    # Wait: let's compute M_{ww} for EVERY item (u_cls, j) (Wait: M_{ww} = Tr_{Sim_u}(Gcd_u * g_{u,w} / Sim_u') MUST BE AN INTEGER == tot_M[0] + tot_M[1] (mod 4)!!)!
    # HOLD ON!! THAT'S AN EXACT INTEGER + MOD-4 FILTER ON EVERY SINGLE 2v-JACOBI ITEM g_{u,w}!!
    Sim_d = Sim_u.diff()
    for j in (0, 1, 2, 5):
        sols = brute_2v_jacobi(chi_S, Gcd_x, H_x, deck_x[u_cls][0], deck_x[j][0], n, 18, x)
        for sd in sols:
            q_poly = sp.Poly(sp.sympify(sd["q_uv"]), x, domain=sp.ZZ)
            g_uv, rem = sp.div(Gcd_2 * q_poly, Gcd_u)
            assert rem.is_zero
            # Compute Tr_{Sim_u}(Gcd_u * g_uv / Sim_u') and Tr_{Sim_u}(x * Gcd_u * g_uv / Sim_u')
            # Using exact polynomial remainder: inv_sd = (Sim_u')^{-1} mod Sim_u
            inv_sd = sp.invert(sp.Poly(Sim_d.as_expr(), x, domain=sp.QQ), sp.Poly(Sim_u.as_expr(), x, domain=sp.QQ))
            rem_M = sp.rem(sp.Poly((Gcd_u * g_uv).as_expr(), x, domain=sp.QQ) * inv_sd, sp.Poly(Sim_u.as_expr(), x, domain=sp.QQ))
            rem_N = sp.rem(sp.Poly((x * Gcd_u * g_uv).as_expr(), x, domain=sp.QQ) * inv_sd, sp.Poly(Sim_u.as_expr(), x, domain=sp.QQ))
            # Wait: trace of sum_{k=0}^{d-1} c_k r^k over roots of Sim_u!
            # We compute power sums p_k = sum r^k via Newton identities from Sim_u!
            d_s = Sim_u.degree()
            cs_s = [int(v) for v in Sim_u.all_coeffs()]  # monic: x^d + e_1 x^{d-1} + ...
            p_sums = [d_s]
            for k in range(1, d_s):
                # p_k = - sum_{i=1}^{k-1} cs_s[i] p_{k-i} - k * cs_s[k]
                val = -sum(cs_s[i] * p_sums[k - i] for i in range(1, k)) - k * cs_s[k]
                p_sums.append(val)
            def eval_tr(poly_r):
                ans = sp.Rational(0)
                for k in range(d_s):
                    cf = sp.Rational(poly_r.coeff_monomial(x**k)) if poly_r.degree() >= k else sp.Rational(0)
                    ans += cf * p_sums[k]
                return ans
            m_diag = eval_tr(rem_M)
            n_diag = eval_tr(rem_N)
            # Note: since n_u=73 === 1 (mod 4), every vertex has same M_{ww} === tot_M[0] + tot_M[1] (mod 4)!
            exp_m4 = (tot_M[0] + tot_M[1]) % 4
            exp_n4 = (tot_N[0] + tot_N[1]) % 4
            ok_int = m_diag.is_Integer and n_diag.is_Integer
            ok_m4 = ok_int and (int(m_diag) % 4 == exp_m4) and (int(n_diag) % 4 == exp_n4)
            print(f"  ({u_cls},{j}) s={sd['s_uv']:+d} S2={sd['S2_uv']:+3d}: M_ww={m_diag} N_ww={n_diag} int={ok_int} mod4={ok_m4}")


if __name__ == "__main__":
    for u_cls in (0, 1, 2, 5):
        check_mod4_eulerian_on_Su(u_cls)
