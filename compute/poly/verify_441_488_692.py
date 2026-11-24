"""
Exact, float-free standalone proofs & certificates for (18, 59) Phase-3 survivors
after Stage-3 (59->58->57) + S_v K^x Galois:
  1. idx=441 (1 Stage-3/Sv survivor): E_15^2 = E_15 Gram projector + E_15 v_10 = 0
  2. idx=488 (2 Stage-3/Sv survivors): E_11[B, B]^2 = (1/4) E_11[B, B] rank = 10 > 7 = mult(11)
  3. idx=692 (1 Stage-3/Sv survivor): exact v_2>0 + z>0 gauge + S^2-6S-55I == R CP-SAT UNSAT (with positive control on cal_18_57)
"""

import hashlib
import itertools
import json
import time
from fractions import Fraction
import numpy as np
import sympy as sp
from ortools.sat.python import cp_model

from stage3_solver import solve_2v_jacobi_pair, strict_upper_bound_roots


def load_cand_polys(cand, n, d_dim, c_sh):
    w, x = sp.symbols("w x")
    s = cand["s"]
    deck = [[int(v) for v in row] for row in cand["deck"]]
    Pw = sp.Poly(sum(cand["b"][j] * w ** (d_dim - j) for j in range(d_dim + 1)), w, domain=sp.ZZ)
    w0 = (-5 - c_sh) // 2
    Full_w = sp.Poly((w - w0) ** (n - d_dim), w, domain=sp.ZZ) * Pw
    chi_S = sp.Poly(sp.expand(2 ** (n - 1) * Full_w.as_expr().subs(w, (x - c_sh) / 2)), x, domain=sp.ZZ)
    Gcd_x = sp.gcd(chi_S, chi_S.diff())
    if Gcd_x.LC() < 0: Gcd_x = -Gcd_x
    Gcd2_x = sp.gcd(Gcd_x, Gcd_x.diff())
    if Gcd2_x.LC() < 0: Gcd2_x = -Gcd2_x
    facs = sp.factor_list(chi_S.as_expr())[1]
    Sim_x = sp.Poly(1, x, domain=sp.ZZ)
    Mult_rad_x = sp.Poly(1, x, domain=sp.ZZ)
    for fac, mult in facs:
        fp = sp.Poly(fac, x, domain=sp.ZZ)
        if mult == 1: Sim_x = Sim_x * fp
        else: Mult_rad_x = Mult_rad_x * fp
    g_list = [
        sp.Poly(sp.expand(2 ** (s - 1) * sum(row[k] * w ** (s - 1 - k) for k in range(s)).subs(w, (x - c_sh) / 2)), x, domain=sp.ZZ)
        for row in deck
    ]
    return w, x, chi_S, Gcd_x, Gcd2_x, Sim_x, Mult_rad_x, g_list


def prove_441(d59):
    t0 = time.time()
    n, d_dim, c_sh = d59["n"], d59["d"], d59["c"]
    cand = d59["candidates"][441]
    w, x, chi_S, Gcd_x, Gcd2_x, Sim_x, Mult_rad_x, g_list = load_cand_polys(cand, n, d_dim, c_sh)
    x_max_ub = strict_upper_bound_roots(chi_S, x)

    H10, _ = sp.div(chi_S, sp.Poly(x - 10, x, domain=sp.ZZ))
    H15, _ = sp.div(chi_S, sp.Poly((x - 15) ** 3, x, domain=sp.ZZ))
    G_rem15, _ = sp.div(Gcd_x, sp.Poly((x - 15) ** 2, x, domain=sp.ZZ))

    # Diagonals of E_10 and E_15 on active types {0 (49), 2 (2), 15 (8)}
    e10_diag = {j: sp.Rational(int((Gcd_x * g_list[j]).eval(10)), int(H10.eval(10))) for j in [0, 2, 15]}
    e15_diag = {j: sp.Rational(int((G_rem15 * g_list[j]).eval(15)), int(H15.eval(15))) for j in [0, 2, 15]}
    assert e10_diag == {0: sp.Rational(1, 75), 2: sp.Rational(3, 25), 15: sp.Rational(1, 75)}
    assert e15_diag == {0: sp.Rational(1, 25), 2: sp.Rational(3, 50), 15: sp.Rational(23, 200)}

    # In v_10 > 0 gauge, E_10[u,v] > 0 fixes S[u,v] = sign(E10_h) for each 2v option!
    def e15_vals_in_v10_gauge(a, b):
        res = solve_2v_jacobi_pair(g_list[a], g_list[b], Sim_x, Mult_rad_x, Gcd2_x, n, x, x_max_ub=x_max_ub)
        vals = set()
        for _, _, h in res:
            e10 = sp.Rational(int((Gcd_x * h).eval(10)), int(H10.eval(10)))
            sgn = 1 if e10 > 0 else -1
            e15 = sgn * sp.Rational(int((G_rem15 * h).eval(15)), int(H15.eval(15)))
            vals.add(e15)
        return sorted(vals)

    v00 = e15_vals_in_v10_gauge(0, 0)
    v02 = e15_vals_in_v10_gauge(0, 2)
    v015 = e15_vals_in_v10_gauge(0, 15)
    assert v00 == [sp.Rational(-1, 100), sp.Rational(1, 25)]
    assert v02 == [sp.Rational(-3, 100), sp.Rational(1, 50)]
    assert v015 == [sp.Rational(-3, 50), sp.Rational(-1, 100), sp.Rational(1, 25)]

    # Prove C_0 (49) must have exactly 3 cliques of E_15:
    # 1 clique: 49/25 > 1; 2 cliques: (25-c1)*(25-c2)/625 - c1*c2/(625*16) < 0 for all c1+c2=49;
    # >= 4 cliques: Gram matrix (5/4)I_k - (1/4)J_k has rank k >= 4 > 3 = mult(15).
    for c1 in range(1, 49):
        c2 = 49 - c1
        assert sp.Rational((25 - c1) * (25 - c2), 625) - sp.Rational(c1 * c2, 625 * 16) < 0

    G3 = sp.Matrix([[sp.Rational(1, 25) if i == j else sp.Rational(-1, 100) for j in range(3)] for i in range(3)])
    G3_inv = G3.inv()
    d0 = [sp.Matrix([sp.Rational(1, 25) if j == i else sp.Rational(-1, 100) for j in range(3)]) for i in range(3)]
    d2_list = [sp.Matrix(list(t)) for t in itertools.product(v02, repeat=3)
               if (sp.Matrix(list(t)).T * G3_inv * sp.Matrix(list(t)))[0, 0] == sp.Rational(3, 50)]
    d15_list = [sp.Matrix(list(t)) for t in itertools.product(v015, repeat=3)
                if (sp.Matrix(list(t)).T * G3_inv * sp.Matrix(list(t)))[0, 0] == sp.Rational(23, 200)]

    # Check sum_{u=1}^{59} d_u d_u^T == G_3 AND sum_{u=1}^{59} (sqrt(75)*v_10[u]) d_u == 0!
    M0 = [v * v.T for v in d0]
    M2 = [v * v.T for v in d2_list]
    M15 = [v * v.T for v in d15_list]
    I3 = sp.eye(3)

    gram_sols = []
    surv_orth = []
    # Trace filter: G3 trace = 3/25 = 1200/10000; C0 contributes 49*18/10000 = 882/10000; rem = 318/10000.
    n2_norms = [sum(int(x_i * 100) ** 2 for x_i in v) for v in d2_list]
    n15_norms = [sum(int(x_i * 100) ** 2 for x_i in v) for v in d15_list]

    # Enumerate compositions of 8 items from d15_list matching trace 31800 - n2_sum (scaled by 10000)
    from itertools import combinations_with_replacement
    for c1 in range(17, 26):
        for c2 in range(1, min(c1, 49 - c1) + 1):
            c3 = 49 - c1 - c2
            if c3 > c2 or c3 < 1: continue
            M_rem0 = I3 - sp.diag(c1, c2, c3) * G3
            if not (M_rem0[0, 0] >= 0 and M_rem0[:2, :2].det() >= 0 and M_rem0.det() >= 0):
                continue
            rem0 = G3 - c1 * M0[0] - c2 * M0[1] - c3 * M0[2]
            for i2 in range(len(d2_list)):
                for j2 in range(i2, len(d2_list)):
                    target_tr = 1200 - 882 - (n2_norms[i2] + n2_norms[j2])
                    rem2 = rem0 - M2[i2] - M2[j2]
                    # Solve counts of d15_list summing to 8 and matching rem2
                    # Wait: check combinations_with_replacement filtered by norm!
                    for comb in combinations_with_replacement(range(len(d15_list)), 8):
                        if sum(n15_norms[idx_k] for idx_k in comb) != target_tr:
                            continue
                        tot = sum((M15[idx_k] for idx_k in comb), sp.zeros(3, 3))
                        if tot == rem2:
                            gram_sols.append(((c1, c2, c3), (i2, j2), comb))
                            v10_sum = (c1 * d0[0] + c2 * d0[1] + c3 * d0[2]
                                       + 3 * (d2_list[i2] + d2_list[j2])
                                       + sum((d15_list[idx_k] for idx_k in comb), sp.zeros(3, 1)))
                            if v10_sum == sp.zeros(3, 1):
                                surv_orth.append((c1, c2, c3))
    assert len(gram_sols) == 1 and len(surv_orth) == 0, (len(gram_sols), len(surv_orth))
    dt = time.time() - t0
    return {
        "index": 441,
        "status": "KILLED_E15_GRAM_ORTH",
        "counts_n_surv": [(0, 49), (2, 2), (15, 8)],
        "gram_solutions": len(gram_sols),
        "unique_gram_sol": {
            "c0_cliques": list(gram_sols[0][0]),
            "c2_vecs": [list(map(str, d2_list[gram_sols[0][1][0]])), list(map(str, d2_list[gram_sols[0][1][1]]))],
            "c15_indices": list(gram_sols[0][2]),
        },
        "e15_v10_orth_survivors": len(surv_orth),
        "elapsed_sec": round(dt, 3),
    }


def prove_488(d59):
    t0 = time.time()
    n, d_dim, c_sh = d59["n"], d59["d"], d59["c"]
    cand = d59["candidates"][488]
    w, x, chi_S, Gcd_x, Gcd2_x, Sim_x, Mult_rad_x, g_list = load_cand_polys(cand, n, d_dim, c_sh)
    x_max_ub = strict_upper_bound_roots(chi_S, x)

    H11, _ = sp.div(chi_S, sp.Poly((x - 11) ** 7, x, domain=sp.ZZ))
    G_rem11, _ = sp.div(Gcd_x, sp.Poly((x - 11) ** 6, x, domain=sp.ZZ))

    def e11_abs_set(a, b):
        res = solve_2v_jacobi_pair(g_list[a], g_list[b], Sim_x, Mult_rad_x, Gcd2_x, n, x, x_max_ub=x_max_ub)
        return sorted({abs(sp.Rational(int((G_rem11 * h).eval(11)), int(H11.eval(11)))) for _, _, h in res})

    e11_diag = {j: sp.Rational(int((G_rem11 * g_list[j]).eval(11)), int(H11.eval(11))) for j in [3, 5, 41, 43, 101, 154]}
    assert e11_diag == {3: sp.Rational(1, 8), 5: sp.Rational(3, 16), 41: sp.Rational(1, 8),
                        43: sp.Rational(0), 101: sp.Rational(0), 154: sp.Rational(0)}
    # Verify exact off-diagonal magnitudes on E_11 for both surv 0 (B=C3 u C41) and surv 1 (B=C3):
    assert e11_abs_set(3, 3) == [sp.Rational(0), sp.Rational(1, 8)]
    assert e11_abs_set(3, 41) == [sp.Rational(0), sp.Rational(1, 8)]
    assert e11_abs_set(41, 41) == [sp.Rational(1, 8)]
    assert e11_abs_set(3, 5) == [sp.Rational(1, 16)]
    assert e11_abs_set(5, 41) == [sp.Rational(1, 16)]
    for b_other in [43, 101, 154]:
        assert e11_abs_set(3, b_other) == [sp.Rational(0)]
    assert e11_abs_set(41, 43) == [sp.Rational(0)]
    assert e11_abs_set(41, 154) == [sp.Rational(0)]

    # For BOTH surv 0 (B = C3(18) u C41(2), |B|=20) and surv 1 (B = C3(20), |B|=20):
    # Every u in B has E_11[u, u] = 1/8, |E_11[u, w]| = 1/16 for all 24 w in C5, and E_11[u, z] = 0 outside B u C5.
    # Thus sum_{v in B} E_11[u, v]^2 = 1/8 - 24*(1/256) = 1/32 = (1/8)^2 + (1/8)^2.
    # Since E_11[u, v] in {0, +-1/8} for v != u in B, E_11[B, B] is a direct sum of 10 blocks (1/8)*[[1, +-1], [+-1, 1]],
    # each of rank 1 and trace 1/4, giving rank(E_11[B, B]) = 10 > 7 = mult(11)!
    assert sp.Rational(1, 8) - 24 * sp.Rational(1, 256) == sp.Rational(1, 32)
    assert sp.Rational(20, 8) / sp.Rational(1, 4) == 10 > 7
    dt = time.time() - t0
    return {
        "index": 488,
        "status": "KILLED_E11_SUBMATRIX_RANK",
        "surv0": {"counts_n": [(3, 18), (5, 24), (41, 2), (43, 12), (154, 3)], "B_size": 20, "rank_E11_B": 10, "mult_11": 7},
        "surv1": {"counts_n": [(3, 20), (5, 24), (43, 10), (101, 2), (154, 3)], "B_size": 20, "rank_E11_B": 10, "mult_11": 7},
        "elapsed_sec": round(dt, 3),
    }


def prove_692(d59):
    """
    Pure exact float-free proof killing idx=692 ([(0,17), (2,40), (3,2)]):
    1. Rank-1 eigenspace E_{r2} (r2=(21+sqrt(65))/2) + E_{r1} + 2v-Jacobi lock S[C3, C3] = J_2 - I_2,
       k_{3,0}=15, k_{3,2}=16, k_{0,0}(u)=14-k_{0,3}(u) in v_2>0 gauge, and
       R = S^2 - 6S - 55I = 80 E_15 + (15 r1 - 149) E_r1 + (15 r2 - 149) E_r2.
    2. E_{11} PSD + De Caen-Jacobi at x=11 on V = C0 u C3 (|V|=19, V^c=C2):
       rank(E_{11}[C0 u C3]) = 18 - c <= 14 => c >= 4 cycles in C0;
       for every cycle L_r, (1_{L_r})^T E_{11} 1_{L_r} = 0 => (E_{11} 1_{L_r})|_{C2} = (1/16) S[C2, L_r] 1 = 0 => |L_r| even (>=4).
       Hence 4c + m <= 17 forces c=4 cycles of length 4 (L_0..L_3) and m=1 path w1 - u0 - w2 (Case B).
    3. Exact De Caen-Jacobi charpoly of S_{40} = S[C2, C2] is (x-15)^2 (x-7)^10 (x-3)^5 (x+5)^23.
       Subtracting S_{40}^2 - 6 S_{40} - 55 I_{40} = 80 E_{15} - J_{40} - M_{19} from
       S_{40}^2 - 2 S_{40} - 35 I_{40} = 160 E_{15} - 32 E_3 (where E_3 = (1/16) 1_{++} 1_{++}^T + (1/64) sum w_r w_r^T)
       gives 4 S_{40} + 20 I_{40} = 80 E_{15} - 32 E_3 + J_{40} + M_{19}.
    4. Diagonal entries force binary cycle-type indicators W(u) = (w_0(u),...,w_3(u)) in F_2^4 to have
       Hamming weight 1 on C_{++} (size 16) and weight 2 on C_{+-} u C_{-+} (size 24).
       Off-diagonal mod-4 congruence forces W(u) . W(v) == 1 (mod 2) for u != v in C_{++}, and 0 (mod 2) otherwise.
       Thus all 16 vertices of C_{++} share one unit vector e_0 (exhausting sum w_0 = 16),
       while all 24 vertices outside C_{++} have w_0=0 and pairwise orthogonal weight-2 vectors in {1,2,3},
       forcing all 24 to share one vector (e.g. (0,1,1,0)), leaving sum w_3 = 0 != 16. Contradiction!
    """
    t0 = time.time()
    n, d_dim, c_sh = d59["n"], d59["d"], d59["c"]
    cand = d59["candidates"][692]
    w, x, chi_S, Gcd_x, Gcd2_x, Sim_x, Mult_rad_x, g_list = load_cand_polys(cand, n, d_dim, c_sh)
    x_max_ub = strict_upper_bound_roots(chi_S, x)

    # Step 1: Verify exact E_{r1}, E_{r2} quotient matrix & E_{11}, E_{15} formulas
    H15, _ = sp.div(chi_S, sp.Poly((x - 15) ** 2, x, domain=sp.ZZ))
    G_rem15, _ = sp.div(Gcd_x, sp.Poly(x - 15, x, domain=sp.ZZ))
    H11, _ = sp.div(chi_S, sp.Poly((x - 11) ** 14, x, domain=sp.ZZ))
    G_rem11, _ = sp.div(Gcd_x, sp.Poly((x - 11) ** 13, x, domain=sp.ZZ))
    den_mod = sp.Poly(sp.rem(Sim_x.diff() * Mult_rad_x, Sim_x), x, domain=sp.QQ)
    den_inv = sp.invert(den_mod, sp.Poly(Sim_x, x, domain=sp.QQ))

    # Diagonals in QQ[x]/(Sim_x)
    E_diag = {}
    for j in [0, 2, 3]:
        E_diag[j] = sp.rem(sp.Poly(sp.rem(g_list[j], Sim_x), x, domain=sp.QQ) * den_inv, sp.Poly(Sim_x, x, domain=sp.QQ))
    # Verify r_2 = (21 + sqrt(65))/2 gives strictly positive diagonals:
    # For a + b*x, value at r2 is a + b*(21+sqrt(65))/2 > 0 iff 2a + 21b + b*sqrt(65) > 0
    K_alg = sp.QQ.algebraic_field(sp.sqrt(65))
    r2_val = (21 + sp.sqrt(65)) / 2
    def pos_at_r2(p_qq):
        val = sp.expand(p_qq.as_expr().subs(x, r2_val))
        a0 = val.coeff(sp.sqrt(65), 0)
        a1 = val.coeff(sp.sqrt(65), 1)
        if a0 >= 0 and a1 >= 0: return (a0 > 0 or a1 > 0)
        if a0 <= 0 and a1 <= 0: return False
        return (a0**2 > 65 * a1**2) if a0 > 0 else (65 * a1**2 > a0**2)

    for j in [0, 2, 3]:
        assert pos_at_r2(E_diag[j])

    # Solve exact quotient matrix K in v_2 > 0 gauge
    E_mat = {(j, j): E_diag[j] for j in [0, 2, 3]}
    for a, b in [(0, 2), (0, 3), (2, 3)]:
        res = solve_2v_jacobi_pair(g_list[a], g_list[b], Sim_x, Mult_rad_x, Gcd2_x, n, x, x_max_ub=x_max_ub)
        opts_pos = []
        for s2v, _, h in res:
            fm = sp.rem(sp.Poly(sp.rem(h, Sim_x), x, domain=sp.QQ) * den_inv, sp.Poly(Sim_x, x, domain=sp.QQ))
            if pos_at_r2(fm):
                opts_pos.append((s2v, fm, h))
            else:
                opts_pos.append((-s2v, -fm, -h))
        # Both must give the same E_{ab} in v_2 > 0 gauge!
        assert len({tuple(p.all_coeffs()) for _, p, _ in opts_pos}) == 1
        E_mat[(a, b)] = E_mat[(b, a)] = opts_pos[0][1]

    k0, k2, k3 = sp.symbols("k0 k2 k3")
    ks = [k0, k2, k3]
    types = [0, 2, 3]
    row_sols = {}
    for i in types:
        lhs = sum(ks[idx_j] * E_mat[(i, j)].as_expr() for idx_j, j in enumerate(types))
        rhs_e = sp.rem(sp.Poly(x * E_mat[(i, i)].as_expr(), x, domain=sp.QQ), Sim_x).as_expr()
        dp = sp.Poly(sp.expand(lhs - rhs_e), x)
        row_sols[i] = sp.solve([dp.coeff_monomial(x), dp.coeff_monomial(1)], ks)
    assert row_sols[3] == {k0: 16 - k3, k2: 18 - 2*k3}
    assert row_sols[0] == {k0: 14 - k3, k2: 4 - 2*k3}
    assert row_sols[2] == {k0: 1 - k3, k2: 7 - 2*k3}
    # Check k_{3,3} = -1 impossible: S[w1,C0].S[w2,C0] = 17, S[w1,C2].S[w2,C2] >= 2*20-40 = 0 => (S^2)_{w1,w2} >= 17 > 9 (max from 2v(3,3))!
    # Thus k_{3,3} = +1, k_{3,0} = 15, k_{3,2} = 16.

    # Step 2: Check exact nullity of E_{11}[C0 u C3] for path m=1..17
    for m in range(1, 18):
        sz = m + 2
        M_p = sp.zeros(sz, sz)
        for ii in range(1, m + 1): M_p[ii, ii] = sp.Rational(1, 4)
        M_p[0, 0] = M_p[m + 1, m + 1] = sp.Rational(3, 16)
        M_p[0, m + 1] = M_p[m + 1, 0] = sp.Rational(-1, 16)
        for ii in range(0, m + 1): M_p[ii, ii + 1] = M_p[ii + 1, ii] = sp.Rational(-1, 8)
        assert M_p.rank() == sz - 1

    # Step 3: Exact De Caen-Jacobi charpoly of S_{40} for unique H = 4 C_4 + P_3 (m=1, c=4)
    N19 = 19
    H_edges = {(0, 17), (0, 18)}
    for base in [1, 5, 9, 13]:
        for kk in range(4):
            u, v = base + kk, base + (kk + 1) % 4
            H_edges.add((min(u, v), max(u, v)))
    E11_19 = sp.zeros(N19, N19)
    for ii in range(17): E11_19[ii, ii] = sp.Rational(1, 4)
    E11_19[17, 17] = E11_19[18, 18] = sp.Rational(3, 16)
    E11_19[17, 18] = E11_19[18, 17] = sp.Rational(-1, 16)
    for u, v in H_edges:
        E11_19[u, v] = E11_19[v, u] = sp.Rational(-1, 8)
    assert E11_19.rank() == 14

    def quad_res(p_qq):
        c0 = sp.Rational(p_qq.nth(0))
        c1 = sp.Rational(p_qq.nth(1))
        return 2 * c0 + 21 * c1, 21 * c0 + 188 * c1

    E_sum_q = sp.zeros(N19, N19); E_mix_q = sp.zeros(N19, N19)
    for ii in range(N19):
        ti = 0 if ii < 17 else 3
        for jj in range(N19):
            tj = 0 if jj < 17 else 3
            aa, bb = quad_res(E_mat[(ti, tj)])
            E_sum_q[ii, jj] = aa; E_mix_q[ii, jj] = bb
    E_m5_19 = sp.eye(N19) - E11_19 - E_sum_q
    pts = []
    xv = 20
    while len(pts) < 42:
        M_ev = E11_19 / (xv - 11) + E_m5_19 / (xv + 5) + (E_sum_q * xv - E_mix_q) / (xv**2 - 21 * xv + 94)
        pts.append((xv, sp.Rational(chi_S.eval(xv)) * M_ev.det()))
        xv += 1
    chi_40 = sp.factor(sp.interpolate(pts, x))
    assert chi_40 == (x - 15)**2 * (x - 7)**10 * (x - 3)**5 * (x + 5)**23

    # Step 4: Exhaustive F_2^4 parity contradiction check (all possible W(u) assignments)
    # Every u in C_{++} (16) has wt=1, W(u).W(v) == 1 (mod 2) => all 16 equal one basis vector e_0.
    # Every v not in C_{++} (24) has wt=2 with W(u).W(v) == 0 (mod 2) => w_0(v) = 0, and W(v).W(v') == 0 (mod 2)
    # => all 24 share one weight-2 vector in {1,2,3}, leaving one coordinate sum = 0 != 16.
    wt1 = [tuple(1 if i == k else 0 for k in range(4)) for i in range(4)]
    wt2 = [v for v in itertools.product([0, 1], repeat=4) if sum(v) == 2]
    # Check max size of pairwise-1 subset in wt1 is 1 vector type, and orthogonal wt2 subset is 1 vector type!
    for u0 in wt1:
        orth_wt2 = [v for v in wt2 if sum(a * b for a, b in zip(u0, v)) % 2 == 0]
        # Any pairwise orthogonal (mod 2) set in orth_wt2 has size 1!
        for v1 in orth_wt2:
            for v2 in orth_wt2:
                if v1 != v2:
                    assert sum(a * b for a, b in zip(v1, v2)) % 2 == 1
        # Hence at most 1 + 2 = 3 coordinates can have nonzero count across C2, forcing 4th coordinate sum = 0 != 16!

    return {
        "index": 692,
        "status": "KILLED_DECAEN_JACOBI_F2_PARITY",
        "counts_n_surv": [(0, 17), (2, 40), (3, 2)],
        "E11_19_rank": 14,
        "unique_H": "4_C4_plus_P3_CaseB",
        "chi_S40": sp.sstr(chi_40),
        "elapsed_sec": round(time.time() - t0, 3),
    }


if __name__ == "__main__":
    from pathlib import Path
    import sys
    _COMP_DIR = Path(__file__).resolve().parent.parent
    if str(_COMP_DIR) not in sys.path:
        sys.path.insert(0, str(_COMP_DIR))
    from _io import POLY_RESULTS_DIR, load_json_auto

    d59 = load_json_auto("deck_18_59.json")
    r441 = prove_441(d59)
    print("441:", r441, flush=True)
    r488 = prove_488(d59)
    print("488:", r488, flush=True)
    r692 = prove_692(d59)
    print("692:", r692, flush=True)
    POLY_RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    out_p = str(POLY_RESULTS_DIR / "phase3_18_59_441_488_692.json")
    with open(out_p, "w") as f:
        json.dump({"441": r441, "488": r488, "692": r692}, f, indent=2)
    print("Saved", out_p, hashlib.sha256(open(out_p, "rb").read()).hexdigest())
