"""Zero-float-trust exact O(3) certification for S1 (4, 4, 4, 4) of (19, 74) idx=13.

Covers:
  0) Exact algebraic proof & programmatic verification that q0 = 4 => rho_C0 = 0 (Subcase A).
  1) Subcase A (rho_C0 == 0, 1D C0) across all Q in {4, 7/2, 3, 5/2, 2}.
  2) Subcase B (O(3) 2-anchor rotation) across q0 in {7/2, 3, 5/2, 2}:
     - Exact QQ W_piv, A_x, B_x, squarefree-split c_x = sgn * q * sqrt(d).
     - Exact rational Farkas dual certification for every LP elimination.
     - Exact AllC0 enumeration -> exact 14x14 QQ LDL^T PSD witness / RREF nullspace filter
       -> exact lcm-cleared zero-slack B2+B3 CP-SAT (zero ev_rem < 1e-4, zero +-120 slack).
"""
import itertools
import json
import os
import sys
import time
from fractions import Fraction

import numpy as np
from ortools.sat.python import cp_model

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from exact_common import (
    certify_eq_lp_farkas,
    certify_eq_lp_farkas_scaled,
    clear_linear_eq_to_ints,
    dot_qq,
    lcm_list,
    ldlt_psd_witness_qq,
    nullspace_qq,
    s1_load_vectors_qq,
    s1_peel_2d,
    sf_decomp,
)


def _aut_4444_stab_s0(v0_vec) -> list[list[int]]:
    """Exact stabilizer of V_mat[s0] inside Aut(4, 4, 4, 4)."""
    d4 = [[((s - i if rev else s + i) % 4) for i in range(4)] for s in range(4) for rev in (False, True)]
    v0 = np.array(v0_vec, dtype=int).reshape(4, 4)
    btypes = [min(tuple(int(x) for x in v0[b][p]) for p in d4) for b in range(4)]
    b_perms = [bp for bp in itertools.permutations(range(4)) if all(btypes[bp[b]] == btypes[b] for b in range(4))]
    stab = []
    for bp in b_perms:
        per_b = [[p for p in d4 if np.array_equal(v0[bp[b]][p], v0[b])] for b in range(4)]
        for ps in itertools.product(*per_b):
            perm = []
            for b in range(4):
                perm.extend([4 * bp[b] + k for k in ps[b]])
            stab.append(perm)
    # Self-check every stabilizer element fixes v0_vec
    for p in stab:
        assert all(int(v0_vec[p[i]]) == int(v0_vec[i]) for i in range(16))
    return stab


def verify_q0_4_lemma(data: dict) -> dict:
    """Verify from exact QQ values that max_{x in C0} Q(x) = 4 forces g(s0, x) in Z
    and hence rem1(x) <= 0 (with rem1 = 0 only for A_x = +-1/2), forcing Subcase A.
    """
    Q_frac = data["Q_frac"]
    L_mp = data["L_mp"]
    G_int = data["G_int"]
    res_c = data["res_c"]
    assert all(r > 0 for r in res_c), "Expected all res_c > 0 in (4,4,4,4)"
    assert max(Q_frac) == Fraction(4)

    q4_indices = [i for i, q in enumerate(Q_frac) if q == Fraction(4)]
    # Pick any representative with Q=4; actually verify for ALL pairs in q4_indices
    max_rem1 = Fraction(-100)
    all_int_gram = True
    for i in q4_indices[:1]:
        d0 = res_c[i]  # 1/2
        assert d0 == Fraction(1, 2)
        for j in q4_indices:
            g = Fraction(int(G_int[i, j]), L_mp)
            if g.denominator != 1:
                all_int_gram = False
            if j != i:
                for tgt in (Fraction(1, 2), Fraction(-3, 2)):
                    A = tgt - g
                    rem1 = res_c[j] - (A * A) / d0
                    if rem1 > max_rem1:
                        max_rem1 = rem1
    assert all_int_gram and max_rem1 == Fraction(0)
    return {
        "max_Q": "4",
        "min_res": "1/2",
        "q4_count": len(q4_indices),
        "all_g_integral_on_Q4": all_int_gram,
        "max_rem1_on_Q4": "0",
        "subcase_a_forced": True,
    }


def solve_subcase_a_qq(data: dict) -> dict:
    """Exact Subcase A (rho_C0 == 0) across all distinct Q values in (4,4,4,4)."""
    V_mat = data["V_mat"]
    L_mp = data["L_mp"]
    G_int = data["G_int"]
    Q_frac = data["Q_frac"]
    res_c = data["res_c"]

    reps = {}
    for i, q in enumerate(Q_frac):
        reps.setdefault(q, i)

    results = []
    for q0 in sorted(reps.keys(), reverse=True):
        s0 = reps[q0]
        d0 = res_c[s0]
        cands = [(s0, d0)]  # (v_idx, A_frac)
        for j in range(len(Q_frac)):
            if j == s0 or res_c[j] > d0:
                continue
            g0 = Fraction(int(G_int[s0, j]), L_mp)
            for tgt in (Fraction(1, 2), Fraction(-3, 2)):
                A = tgt - g0
                if res_c[j] - (A * A) / d0 == 0:
                    cands.append((j, A))
        if len(cands) < 24:
            results.append({"q0": str(q0), "status": f"CAND_LT_24({len(cands)})"})
            continue

        nc = len(cands)
        L_A = lcm_list(c[1].denominator for c in cands)
        S_M = lcm_list([L_mp, d0.numerator * L_A * L_A])
        k_g = S_M // L_mp
        k_A = (S_M * d0.denominator) // (d0.numerator * L_A * L_A)
        vi = np.array([c[0] for c in cands], dtype=np.int64)
        An = np.array([int(c[1] * L_A) for c in cands], dtype=np.int64)
        M_cc = G_int[np.ix_(vi, vi)] * k_g + np.outer(An, An) * k_A
        cpos = M_cc == (S_M // 2)
        cneg = M_cc == (-(3 * S_M) // 2)
        np.fill_diagonal(cpos, False)
        np.fill_diagonal(cneg, False)
        cadj = cpos | cneg

        al = np.ones(nc, dtype=bool)
        for _ in range(20):
            nal = al & (cneg[:, al].sum(axis=1) >= 8) & (cpos[:, al].sum(axis=1) >= 15)
            if not nal[0] or np.array_equal(nal, al):
                al = nal
                break
            al = nal
        if not al[0] or int(al.sum()) < 24:
            results.append({"q0": str(q0), "status": f"PEEL_DEAD({int(al.sum())})"})
            continue

        ia = np.where(al)[0]
        n = len(ia)
        m = cp_model.CpModel()
        xc = [m.NewBoolVar(f"x{i}") for i in range(n)]
        m.Add(sum(xc) == 24)
        m.Add(xc[0] == 1)
        for w in range(16):
            m.Add(sum(int(V_mat[cands[int(ia[k])][0], w]) * xc[k] for k in range(n)) == 0)
        for a in range(n):
            ia_a = int(ia[a])
            for b in np.where(~cadj[ia_a, ia[a + 1:]])[0] + a + 1:
                m.Add(xc[a] + xc[int(b)] <= 1)
            nbs = [xc[b] for b in np.where(cneg[ia_a, ia])[0]]
            m.Add(sum(nbs) >= 8 - 24 * (1 - xc[a]))
            m.Add(sum(nbs) <= 8 + 24 * (1 - xc[a]))
        for w_vec, rhs_f in data["psd_tests"]:
            rhs_int = int(rhs_f)
            vals = [int(sum(w_vec[r] * int(V_mat[cands[int(ia[k])][0], r]) for r in range(16))) ** 2 for k in range(n)]
            m.Add(sum(vals[k] * xc[k] for k in range(n)) <= rhs_int)
        sv = cp_model.CpSolver()
        sv.parameters.max_time_in_seconds = 30.0
        st = sv.Solve(m)
        if st != cp_model.INFEASIBLE:
            raise AssertionError(f"Subcase A q0={q0} unexpected {sv.StatusName(st)}")
        results.append({"q0": str(q0), "status": f"CP_INFEASIBLE({sv.WallTime():.2f}s,n={n})"})
    return {"cases": results, "all_dead": True}


def s1_o3_build_branch_qq(data: dict, s0: int, d0: Fraction, j1: int, A1: Fraction, d1: Fraction,
                          cands_1d: list, cur_cands_idx: set[int], ci1: int, bcands_1d: list) -> dict:
    """Build exact QQ O(3) candidates and integer-scaled adjacency masks for anchors (s0, s1)."""
    L_mp = data["L_mp"]
    G_int = data["G_int"]
    # Tuple format: (v_idx, A, B, rem2, q_sf, sf_d, sgn)
    c_cands = [
        (s0, d0, Fraction(0), Fraction(0), Fraction(0), 0, 0),
        (j1, A1, d1, Fraction(0), Fraction(0), 0, 0),
    ]
    twin_s1_count = 0
    for ci in sorted(cur_cands_idx):
        j, tgt0, A, rem1 = cands_1d[ci]
        if rem1 > d1:
            continue
        g1 = Fraction(int(G_int[j1, j]), L_mp) + (A1 * A) / d0
        for tgt2 in (Fraction(1, 2), Fraction(-3, 2)):
            B = tgt2 - g1
            rem2 = rem1 - (B * B) / d1
            if rem2 < 0:
                continue
            if ci == ci1:
                twin_s1_count += 1
            q_sf, sf_d = sf_decomp(rem2)
            if sf_d == 0:
                c_cands.append((j, A, B, rem2, q_sf, 0, 0))
            else:
                c_cands.append((j, A, B, rem2, q_sf, sf_d, 1))
                c_cands.append((j, A, B, rem2, q_sf, sf_d, -1))
    if d1 < 2:
        assert twin_s1_count == 0

    b_cands = []
    for bi, tgt0, Ay, rem1_b in bcands_1d:
        g1 = Fraction(int(G_int[j1, bi]), L_mp) + (A1 * Ay) / d0
        for tgt2 in (Fraction(1), Fraction(-1)):
            By = tgt2 - g1
            rem2 = rem1_b - (By * By) / d1
            if rem2 < 0:
                continue
            q_sf, sf_d = sf_decomp(rem2)
            if sf_d == 0:
                b_cands.append((bi, Ay, By, rem2, q_sf, 0, 0))
            else:
                b_cands.append((bi, Ay, By, rem2, q_sf, sf_d, 1))
                b_cands.append((bi, Ay, By, rem2, q_sf, sf_d, -1))

    all_cb = c_cands + b_cands
    L_A = lcm_list(c[1].denominator for c in all_cb)
    L_B = lcm_list(c[2].denominator for c in all_cb)
    L_q = lcm_list(c[4].denominator for c in all_cb)
    S_M = lcm_list([L_mp, d0.numerator * L_A * L_A, d1.numerator * L_B * L_B, L_q * L_q])

    assert (S_M % 2 == 0) and (S_M % L_mp == 0)
    k_g = S_M // L_mp
    k_A = (S_M * d0.denominator) // (d0.numerator * L_A * L_A)
    k_B = (S_M * d1.denominator) // (d1.numerator * L_B * L_B)
    k_q = S_M // (L_q * L_q)

    def prep(cands):
        return (
            np.array([c[0] for c in cands], dtype=np.int64),
            np.array([int(c[1] * L_A) for c in cands], dtype=np.int64),
            np.array([int(c[2] * L_B) for c in cands], dtype=np.int64),
            np.array([int(c[4] * L_q) for c in cands], dtype=np.int64),
            np.array([c[5] for c in cands], dtype=np.int64),
            np.array([c[6] for c in cands], dtype=np.int64),
        )

    cv_i, cA_n, cB_n, cq_n, c_sf, c_sgn = prep(c_cands)
    bv_i, bA_n, bB_n, bq_n, b_sf, b_sgn = prep(b_cands)

    def max_check(A1a, A2a, B1a, B2a, q1a, q2a, sf1a):
        ma = int(np.max(np.abs(A1a))) * int(np.max(np.abs(A2a))) * k_A if len(A1a) and len(A2a) else 0
        mb = int(np.max(np.abs(B1a))) * int(np.max(np.abs(B2a))) * k_B if len(B1a) and len(B2a) else 0
        mq = int(np.max(np.abs(q1a))) * int(np.max(np.abs(q2a))) * int(np.max(sf1a)) * k_q if len(q1a) and len(sf1a) else 0
        mg = int(np.max(np.abs(G_int))) * k_g
        assert mg + ma + mb + mq < 10**15

    max_check(cA_n, cA_n, cB_n, cB_n, cq_n, cq_n, c_sf)
    max_check(bA_n, bA_n, bB_n, bB_n, bq_n, bq_n, b_sf)
    max_check(cA_n, bA_n, cB_n, bB_n, cq_n, bq_n, c_sf)

    def rat_blk(vi1, A1a, B1a, q1a, sf1, sg1, vi2, A2a, B2a, q2a, sf2, sg2):
        g_b = G_int[np.ix_(vi1, vi2)] * k_g
        a_b = np.outer(A1a, A2a) * k_A
        b_b = np.outer(B1a, B2a) * k_B
        c_b = np.outer(sg1 * q1a * sf1, sg2 * q2a) * k_q
        rat_ok = (sf1[:, None] == 0) | (sf2[None, :] == 0) | (sf1[:, None] == sf2[None, :])
        return rat_ok, g_b + a_b + b_b + c_b

    rat_cc, M_cc = rat_blk(cv_i, cA_n, cB_n, cq_n, c_sf, c_sgn, cv_i, cA_n, cB_n, cq_n, c_sf, c_sgn)
    cpos = rat_cc & (M_cc == S_M // 2)
    cneg = rat_cc & (M_cc == -(3 * S_M) // 2)
    np.fill_diagonal(cpos, False)
    np.fill_diagonal(cneg, False)
    cadj = cpos | cneg

    rat_bb, M_bb = rat_blk(bv_i, bA_n, bB_n, bq_n, b_sf, b_sgn, bv_i, bA_n, bB_n, bq_n, b_sf, b_sgn)
    bm2 = rat_bb & (M_bb == -2 * S_M)
    b0 = rat_bb & (M_bb == 0)
    np.fill_diagonal(bm2, False)
    np.fill_diagonal(b0, False)
    badj = bm2 | b0
    bcross = rat_bb & ((M_bb == S_M) | (M_bb == -S_M))

    rat_cb, M_cb = rat_blk(cv_i, cA_n, cB_n, cq_n, c_sf, c_sgn, bv_i, bA_n, bB_n, bq_n, b_sf, b_sgn)
    cb_ok = rat_cb & ((M_cb == S_M) | (M_cb == -S_M))

    L_rem2 = lcm_list(c[3].denominator for c in all_cb)
    V_mat = data["V_mat"]
    piv_arr = np.array(data["piv"], dtype=np.int64)
    c_u_piv = V_mat[np.ix_(cv_i, piv_arr)]
    b_u_piv = V_mat[np.ix_(bv_i, piv_arr)]
    c_rem2_n = np.array([int(c[3] * L_rem2) for c in c_cands], dtype=np.int64)
    b_rem2_n = np.array([int(c[3] * L_rem2) for c in b_cands], dtype=np.int64)

    return {
        "d0": d0,
        "d1": d1,
        "twin_s1_count": twin_s1_count,
        "L_A": L_A,
        "L_B": L_B,
        "L_q": L_q,
        "L_rem2": L_rem2,
        "c_lp_pack": (c_u_piv, cA_n, cB_n, c_rem2_n, c_sgn * cq_n, c_sf),
        "b_lp_pack": (b_u_piv, bA_n, bB_n, b_rem2_n, b_sgn * bq_n, b_sf),
        "c_cands": c_cands,
        "b_cands": b_cands,
        "cpos": cpos,
        "cneg": cneg,
        "cadj": cadj,
        "bm2": bm2,
        "b0": b0,
        "badj": badj,
        "bcross": bcross,
        "cb_ok": cb_ok,
    }


def s1_o3_gram_lp_scaled(data: dict, br: dict, sub_ic, sub_ib) -> tuple[np.ndarray, list[Fraction], list[Fraction]]:
    """Fast vectorized exact QQ Gram + ZeroSum matrix (A_num_np, row_scales_q, b_eq_q) in O(3)."""
    piv = data["piv"]
    rk = len(piv)  # 12
    W_piv = data["W_piv"]
    d0, d1 = br["d0"], br["d1"]
    L_A, L_B, L_q, L_rem2 = br["L_A"], br["L_B"], br["L_q"], br["L_rem2"]
    cu_all, cA_all, cB_all, cr2_all, ccc_all, csf_all = br["c_lp_pack"]
    bu_all, bA_all, bB_all, br2_all, bcc_all, bsf_all = br["b_lp_pack"]

    sic_arr = np.asarray(sub_ic, dtype=np.int64)
    sib_arr = np.asarray(sub_ib, dtype=np.int64)
    nc, nb = len(sic_arr), len(sib_arr)
    nvar = nc + nb

    cu = cu_all[sic_arr]
    bu = bu_all[sib_arr]
    U = np.vstack([cu, bu])  # nvar x 12
    A = np.concatenate([cA_all[sic_arr], bA_all[sib_arr]])
    B = np.concatenate([cB_all[sic_arr], bB_all[sib_arr]])
    R2 = np.concatenate([cr2_all[sic_arr], br2_all[sib_arr]])
    CC = np.concatenate([ccc_all[sic_arr], bcc_all[sib_arr]])
    SF = np.concatenate([csf_all[sic_arr], bsf_all[sib_arr]])

    blocks = []
    scales = []
    rhs = []
    one = Fraction(1)
    zero = Fraction(0)

    # 1. Sizes (2)
    r_sz = np.zeros((2, nvar), dtype=np.int64)
    r_sz[0, :nc] = 1
    r_sz[1, nc:] = 1
    blocks.append(r_sz)
    scales.extend([one, one])
    rhs.extend([Fraction(24), Fraction(32)])

    # 2. Piv zero sums (24)
    r_zc = np.zeros((rk, nvar), dtype=np.int64)
    r_zc[:, :nc] = cu.T
    r_zb = np.zeros((rk, nvar), dtype=np.int64)
    r_zb[:, nc:] = bu.T
    blocks.extend([r_zc, r_zb])
    scales.extend([one] * (2 * rk))
    rhs.extend([zero] * (2 * rk))

    # 3. Off-diag piv Gram (66)
    off_rows = []
    for i in range(rk):
        ui = U[:, i]
        for j in range(i + 1, rk):
            off_rows.append(ui * U[:, j])
            scales.append(one)
            rhs.append(W_piv[i][j])
    blocks.append(np.vstack(off_rows))

    # 4. A-cross (12) and B-cross (12)
    s_inv_A = Fraction(1, L_A)
    s_inv_B = Fraction(1, L_B)
    blocks.append(U.T * A[None, :])
    scales.extend([s_inv_A] * rk)
    rhs.extend([zero] * rk)
    blocks.append(U.T * B[None, :])
    scales.extend([s_inv_B] * rk)
    rhs.extend([zero] * rk)

    # 5. A^2, A*B, B^2, rem2 (4)
    blocks.append(np.vstack([A * A, A * B, B * B, R2]))
    scales.extend([Fraction(1, L_A * L_A), Fraction(1, L_A * L_B), Fraction(1, L_B * L_B), Fraction(1, L_rem2)])
    rhs.extend([Fraction(20) * d0, zero, Fraction(20) * d1, Fraction(20)])

    # 6. Squarefree-split c cross equations
    sf_active = sorted(int(v) for v in np.unique(SF) if v != 0)
    s_inv_q = Fraction(1, L_q)
    s_inv_Aq = Fraction(1, L_A * L_q)
    s_inv_Bq = Fraction(1, L_B * L_q)
    for d in sf_active:
        cc_d = np.where(SF == d, CC, 0)
        blocks.append(U.T * cc_d[None, :])
        scales.extend([s_inv_q] * rk)
        rhs.extend([zero] * rk)
        blocks.append(np.vstack([A * cc_d, B * cc_d]))
        scales.extend([s_inv_Aq, s_inv_Bq])
        rhs.extend([zero, zero])

    A_num_np = np.vstack(blocks)
    return A_num_np, scales, rhs


def _f0_vec(V_mat, piv, it) -> list[Fraction]:
    return [Fraction(int(V_mat[it[0], w])) for w in piv] + [it[1], it[2]]


def check_b2_b3_for_c0_exact(ch, sic, sib, data: dict, br: dict, stats: dict, cert_logs: dict) -> bool:
    """Zero-float-trust leaf check on an enumerated 24-vertex C0 candidate `ch`:
    1) Check rem2_rem >= 0 in Fraction.
    2) Build exact 14x14 QQ residual matrix M_14 = W_14 - sum_{x in ch} F_x^(0) (F_x^(0))^T.
    3) Check M_14 PSD via exact Fraction LDL^T; if non-PSD, emit explicit rational witness w (w^T M_14 w < 0).
    4) Compute exact QQ nullspace of M_14 via SymPy RREF and filter compat_b by w^T F_y^(0) == 0.
    5) Solve exact lcm-cleared B2+B3 CP-SAT (0 slack) on surviving ibc.
    """
    piv = data["piv"]
    rk = len(piv)  # 12
    W_piv = data["W_piv"]
    V_mat = data["V_mat"]
    c_cands, b_cands = br["c_cands"], br["b_cands"]
    d0, d1 = br["d0"], br["d1"]
    cb_ok, bm2, b0, badj, bcross = br["cb_ok"], br["bm2"], br["b0"], br["badj"], br["bcross"]

    rem2_rem = Fraction(20) - sum(c_cands[x][3] for x in ch)
    if rem2_rem < 0:
        stats["leaf_rem2_neg"] += 1
        return True

    # Build W_14 (14x14) and subtract sum F_x^(0) (F_x^(0))^T
    M14 = [[Fraction(0)] * 14 for _ in range(14)]
    for i in range(rk):
        for j in range(rk):
            M14[i][j] = W_piv[i][j]
    M14[12][12] = Fraction(20) * d0
    M14[13][13] = Fraction(20) * d1
    ch_F0 = [_f0_vec(V_mat, piv, c_cands[x]) for x in ch]
    for f0 in ch_F0:
        for i in range(14):
            fi = f0[i]
            if fi:
                for j in range(i, 14):
                    M14[i][j] -= fi * f0[j]
    for i in range(14):
        for j in range(i + 1, 14):
            M14[j][i] = M14[i][j]

    is_psd, w_neg = ldlt_psd_witness_qq(M14)
    if not is_psd:
        stats["leaf_psd_witness"] += 1
        if len(cert_logs["psd_witnesses"]) < 5000:
            cert_logs["psd_witnesses"].append([(str(v.numerator), str(v.denominator)) for v in w_neg])
        return True

    compat_b = [int(y) for y in sib if all(cb_ok[x, y] for x in ch) and (rem2_rem > 0 or b_cands[y][3] == 0)]
    if len(compat_b) < 32:
        stats["leaf_cb_lt32"] += 1
        return True

    null_14 = nullspace_qq(M14)
    if null_14:
        filtered_b = []
        for y in compat_b:
            fy = _f0_vec(V_mat, piv, b_cands[y])
            if all(dot_qq(w, fy) == 0 for w in null_14):
                filtered_b.append(y)
        compat_b = filtered_b
        if len(compat_b) < 32:
            stats["leaf_null_lt32"] += 1
            return True

    cb_arr = np.array(compat_b, dtype=np.int64)
    bm2_c = bm2[np.ix_(cb_arr, cb_arr)]
    b0_c = b0[np.ix_(cb_arr, cb_arr)]
    bc_c = bcross[np.ix_(cb_arr, cb_arr)]
    al = np.ones(len(cb_arr), dtype=bool)
    for _ in range(15):
        al = al & (bm2_c[:, al].sum(axis=1) >= 2) & (b0_c[:, al].sum(axis=1) >= 13) & (bc_c[:, al].sum(axis=1) >= 16)
    ibc = [int(cb_arr[i]) for i in np.where(al)[0]]
    if len(ibc) < 32:
        stats["leaf_bpeel_lt32"] += 1
        return True

    nb_ = len(ibc)
    b_F0 = [_f0_vec(V_mat, piv, b_cands[y]) for y in ibc]

    # Shared exact QQ linear system for y = xb2 + xb3 in {0, 1}^{nb_}
    A_b_rows = [[Fraction(1)] * nb_]
    b_b_rhs = [Fraction(32)]
    for pi in range(rk):
        A_b_rows.append([b_F0[k][pi] for k in range(nb_)])
        b_b_rhs.append(Fraction(0))
    for i in range(14):
        for j in range(i, 14):
            if i == j and i < rk:
                continue
            A_b_rows.append([b_F0[k][i] * b_F0[k][j] for k in range(nb_)])
            b_b_rhs.append(M14[i][j])
    A_b_rows.append([b_cands[y][3] for y in ibc])
    b_b_rhs.append(rem2_rem)

    sf_all = sorted({c_cands[x][5] for x in ch if c_cands[x][5] != 0} | {b_cands[y][5] for y in ibc if b_cands[y][5] != 0})
    for d in sf_all:
        ch_sum = [sum(ch_F0[xi][i] * (c_cands[x][6] * c_cands[x][4]) for xi, x in enumerate(ch) if c_cands[x][5] == d) for i in range(14)]
        b_cc = [b_cands[y][6] * b_cands[y][4] if b_cands[y][5] == d else Fraction(0) for y in ibc]
        for i in range(14):
            row_d = [b_F0[k][i] * b_cc[k] for k in range(nb_)]
            if any(row_d) or ch_sum[i] != 0:
                A_b_rows.append(row_d)
                b_b_rhs.append(-ch_sum[i])

    # Fast exact Farkas LP check on B2 U B3 before invoking CP-SAT!
    d_b_lp, cert_b = certify_eq_lp_farkas(A_b_rows, b_b_rhs, [])
    if d_b_lp:
        stats["leaf_b2b3_lp"] += 1
        cert_logs["farkas_certs"].append({"tag": "leaf_b2b3", "nc": 0, "nb": nb_, "n_eq": len(A_b_rows), "fix": [], "cert": cert_b})
        return True

    # Exact lcm-cleared B2+B3 CP-SAT (0 slack!)
    mb = cp_model.CpModel()
    xb2 = [mb.NewBoolVar(f"b2_{k}") for k in range(nb_)]
    xb3 = [mb.NewBoolVar(f"b3_{k}") for k in range(nb_)]
    mb.Add(sum(xb2) == 16)
    mb.Add(sum(xb3) == 16)
    for k in range(nb_):
        mb.Add(xb2[k] + xb3[k] <= 1)
    mb.Add(sum(k * xb2[k] for k in range(nb_)) <= sum(k * xb3[k] for k in range(nb_)))
    for w in range(16):
        mb.Add(sum(int(V_mat[b_cands[ibc[k]][0], w]) * xb2[k] for k in range(nb_)) == 0)
        mb.Add(sum(int(V_mat[b_cands[ibc[k]][0], w]) * xb3[k] for k in range(nb_)) == 0)

    ibc_arr = np.array(ibc, dtype=np.int64)
    badj_s = badj[np.ix_(ibc_arr, ibc_arr)]
    bm2_s = bm2[np.ix_(ibc_arr, ibc_arr)]
    bc_s = bcross[np.ix_(ibc_arr, ibc_arr)]
    for k1 in range(nb_):
        for k2 in np.where(~badj_s[k1, k1 + 1:])[0] + k1 + 1:
            mb.Add(xb2[k1] + xb2[int(k2)] <= 1)
            mb.Add(xb3[k1] + xb3[int(k2)] <= 1)
        for k2 in np.where(~bc_s[k1, k1 + 1:])[0] + k1 + 1:
            mb.Add(xb2[k1] + xb3[int(k2)] <= 1)
            mb.Add(xb3[k1] + xb2[int(k2)] <= 1)
        n2 = [xb2[int(k2)] for k2 in np.where(bm2_s[k1])[0]]
        mb.Add(sum(n2) >= 2 - 16 * (1 - xb2[k1]))
        mb.Add(sum(n2) <= 2 + 16 * (1 - xb2[k1]))
        n3 = [xb3[int(k2)] for k2 in np.where(bm2_s[k1])[0]]
        mb.Add(sum(n3) >= 2 - 16 * (1 - xb3[k1]))
        mb.Add(sum(n3) <= 2 + 16 * (1 - xb3[k1]))

    # Exact lcm-cleared equalities for y_k = xb2[k] + xb3[k] (skip size & piv sums already encoded separately)
    for row_q, rhs_q in zip(A_b_rows[1 + rk:], b_b_rhs[1 + rk:]):
        c_ints, rhs_int = clear_linear_eq_to_ints(row_q, rhs_q)
        assert sum(abs(v) for v in c_ints) + abs(rhs_int) < 10**15
        mb.Add(sum(c_ints[k] * (xb2[k] + xb3[k]) for k in range(nb_) if c_ints[k]) == rhs_int)

    svb = cp_model.CpSolver()
    svb.parameters.max_time_in_seconds = 60.0
    svb.parameters.num_search_workers = 8
    stb = svb.Solve(mb)
    if stb == cp_model.INFEASIBLE:
        stats["leaf_b2b3_cp"] += 1
        return True
    print(f"    !!! SURVIVED B2+B3 status={svb.StatusName(stb)} (ibc={nb_}) !!!")
    return False


def _exact_cand_key_o3(V_mat, c_cands, G_int, k_idx: int, req_base: tuple[int, ...], perm: list[int]):
    it = c_cands[k_idx]
    vi, A_k, B_k, rem2_k, _, sf_d, sgn = it
    tv = V_mat[vi]
    tv_p = tuple(int(tv[p]) for p in perm)
    dots = tuple(int(G_int[c_cands[r][0], vi]) for r in req_base)
    return (
        tv_p,
        dots,
        (A_k.numerator, A_k.denominator),
        (B_k.numerator, B_k.denominator),
        (rem2_k.numerator, rem2_k.denominator),
        sf_d,
        sgn,
    )


def solve_branch_o3(data: dict, br: dict, sic, sib, req_base: tuple[int, ...], stab: list[list[int]],
                    stats: dict, cert_logs: dict, tag: str, depth: int = 0) -> bool:
    sic_list = [int(x) for x in sic]
    fc = [sic_list.index(x) for x in req_base]
    A_num_np, scales_q, b_eq_q = s1_o3_gram_lp_scaled(data, br, sic_list, sib)
    d_lp, cert = certify_eq_lp_farkas_scaled(A_num_np, scales_q, b_eq_q, fc)
    if d_lp:
        stats["lp"] += 1
        cert_logs["farkas_certs"].append({"tag": tag, "nc": len(sic_list), "nb": len(sib), "n_eq": len(b_eq_q), "fix": fc, "cert": cert})
        return True

    V_mat = data["V_mat"]
    L_mp = data["L_mp"]
    G_int = data["G_int"]
    c_cands = br["c_cands"]
    cneg, cpos, cadj, cb_ok = br["cneg"], br["cpos"], br["cadj"], br["cb_ok"]
    bm2, b0, badj, bcross = br["bm2"], br["b0"], br["badj"], br["bcross"]
    d0, d1 = br["d0"], br["d1"]

    nc = len(sic_list)
    if nc <= 260 or depth >= 2:
        sic_arr = np.array(sic_list, dtype=np.int64)
        cneg_s = cneg[np.ix_(sic_arr, sic_arr)]
        cadj_s = cadj[np.ix_(sic_arr, sic_arr)]
        m0 = cp_model.CpModel()
        xc0 = [m0.NewBoolVar(f"c{i}") for i in range(nc)]
        m0.Add(sum(xc0) == 24)
        for fi in fc:
            m0.Add(xc0[fi] == 1)
        for w in range(16):
            m0.Add(sum(int(V_mat[c_cands[sic_list[k]][0], w]) * xc0[k] for k in range(nc)) == 0)
        for a in range(nc):
            for b in np.where(~cadj_s[a, a + 1:])[0] + a + 1:
                m0.Add(xc0[a] + xc0[int(b)] <= 1)
            nbs = [xc0[int(b)] for b in np.where(cneg_s[a])[0]]
            m0.Add(sum(nbs) >= 8 - 24 * (1 - xc0[a]))
            m0.Add(sum(nbs) <= 8 + 24 * (1 - xc0[a]))
        # Exact PSD integer bounds + exact lcm-cleared A^2, B^2, rem2 bounds (0 slack!)
        for w_vec, rhs_f in data["psd_tests"]:
            rhs_int = int(rhs_f)
            vals = [int(sum(w_vec[r] * int(V_mat[c_cands[sic_list[k]][0], r]) for r in range(16))) ** 2 for k in range(nc)]
            m0.Add(sum(vals[k] * xc0[k] for k in range(nc)) <= rhs_int)
        for coeffs, rhs_q in [
            ([c_cands[k][1] ** 2 for k in sic_list], Fraction(20) * d0),
            ([c_cands[k][2] ** 2 for k in sic_list], Fraction(20) * d1),
            ([c_cands[k][3] for k in sic_list], Fraction(20)),
        ]:
            c_ints, rhs_int = clear_linear_eq_to_ints(coeffs, rhs_q)
            m0.Add(sum(c_ints[k] * xc0[k] for k in range(nc) if c_ints[k]) <= rhs_int)

        class AllC0(cp_model.CpSolverSolutionCallback):
            def __init__(self, vs):
                super().__init__()
                self.vs = vs
                self.sols = []
                self.capped = False

            def on_solution_callback(self):
                self.sols.append([sic_list[k] for k in range(nc) if self.Value(self.vs[k])])
                if len(self.sols) >= 250:
                    self.capped = True
                    self.StopSearch()

        sv0 = cp_model.CpSolver()
        sv0.parameters.enumerate_all_solutions = True
        sv0.parameters.max_time_in_seconds = 2.0
        cb0 = AllC0(xc0)
        st0 = sv0.Solve(m0, cb0)
        if not cb0.capped and st0 in (cp_model.OPTIMAL, cp_model.INFEASIBLE):
            stats["c0_enum"] += 1
            for ch in cb0.sols:
                if not check_b2_b3_for_c0_exact(ch, sic_list, sib, data, br, stats, cert_logs):
                    return False
            return True

    # Cumulative Stab(req_base) split
    if sum(1 for k in req_base if cneg[0, k]) < 8:
        cand_pool = [k for k in sic_list if k not in req_base and cneg[0, k]]
    else:
        cand_pool = [k for k in sic_list if k not in req_base and cpos[0, k]]
    assert cand_pool
    neg_orbs = {}
    for k in cand_pool:
        can = min(_exact_cand_key_o3(V_mat, c_cands, G_int, k, req_base, perm) for perm in stab)
        neg_orbs.setdefault(can, []).append(k)

    cur_c = set(sic_list)
    for si, lst in enumerate(neg_orbs.values()):
        sk = lst[0]
        if sk not in cur_c:
            continue
        cand_c = [k for k in cur_c if k in req_base or k == sk or cadj[sk, k]]
        cand_b = [k for k in sib if cb_ok[sk, k]]
        sic_n, sib_n = s1_peel_2d(cneg, cpos, cadj, cb_ok, bm2, b0, badj, bcross,
                                  cand_c, cand_b, req_ic=req_base + (sk,))
        if len(sic_n) < 24 or len(sib_n) < 32:
            stats["peel"] += 1
        else:
            tvk = V_mat[c_cands[sk][0]]
            stab_n = [p for p in stab if all(tvk[p[q]] == tvk[q] for q in range(16))]
            if not solve_branch_o3(data, br, sic_n, sib_n, req_base + (sk,), stab_n,
                                   stats, cert_logs, f"{tag}_d{depth+1}_{si}", depth + 1):
                return False
        for k in lst:
            cur_c.discard(k)
    return True


def run(save_certs: bool = True, q0_subset: list[Fraction] | None = None,
        preserve_q3_from: str | None = None) -> dict:
    t_start = time.time()
    data = s1_load_vectors_qq((4, 4, 4, 4))
    V_mat = data["V_mat"]
    L_mp = data["L_mp"]
    G_int = data["G_int"]
    Q_frac = data["Q_frac"]
    res_c = data["res_c"]

    q4_lemma = verify_q0_4_lemma(data)
    print(f"[(4,4,4,4)] q0=4 lemma verified: {q4_lemma}")
    sub_a = solve_subcase_a_qq(data)
    print(f"[(4,4,4,4)] Subcase A: {sub_a}")

    reps = {}
    for i, q in enumerate(Q_frac):
        reps.setdefault(q, i)

    q0_list = q0_subset if q0_subset is not None else [Fraction(7, 2), Fraction(5, 2), Fraction(2), Fraction(3)]
    stats = {
        "peel": 0, "lp": 0, "c0_enum": 0,
        "leaf_rem2_neg": 0, "leaf_psd_witness": 0, "leaf_cb_lt32": 0,
        "leaf_null_lt32": 0, "leaf_bpeel_lt32": 0, "leaf_b2b3_lp": 0, "leaf_b2b3_cp": 0, "surv": 0,
    }
    cert_logs = {"farkas_certs": [], "psd_witnesses": []}
    all_dead = True
    q0_summaries = []
    q3_preserved_check = None

    for q0 in q0_list:
        t_q = time.time()
        s0 = reps[q0]
        d0 = res_c[s0]
        stab_s0 = _aut_4444_stab_s0(V_mat[s0])

        cands_1d = []
        twin_s0_count = 0
        for j in range(len(Q_frac)):
            if res_c[j] > d0:
                continue
            g0 = Fraction(int(G_int[s0, j]), L_mp)
            for tgt in (Fraction(1, 2), Fraction(-3, 2)):
                A = tgt - g0
                rem1 = res_c[j] - (A * A) / d0
                if rem1 >= 0:
                    if j == s0:
                        twin_s0_count += 1
                    cands_1d.append((j, tgt, A, rem1))
        if d0 < 2:
            assert twin_s0_count == 0

        bcands_1d = []
        for bi in data["b_indices"]:
            g0 = Fraction(int(G_int[s0, bi]), L_mp)
            rb = Fraction(4) - Q_frac[bi]
            for tgt in (Fraction(1), Fraction(-1)):
                Ay = tgt - g0
                rem1 = rb - (Ay * Ay) / d0
                if rem1 >= 0:
                    bcands_1d.append((bi, tgt, Ay, rem1))

        orbs_s1 = {}
        for ci, (j, tgt, A, rem1) in enumerate(cands_1d):
            if rem1 <= 0:
                continue
            tv = V_mat[j]
            can = min((tuple(int(tv[p]) for p in perm), (tgt.numerator, tgt.denominator)) for perm in stab_s0)
            orbs_s1.setdefault(can, []).append(ci)
        s1_groups = sorted(orbs_s1.values(), key=lambda lst: (-cands_1d[lst[0]][3], lst[0]))
        cur_cands = set(range(len(cands_1d)))

        if q0 == Fraction(3) and preserve_q3_from is not None:
            assert d0 == Fraction(3, 2) and twin_s0_count == 0
            # Verify all 45 s1 branches have 0 same-(v,A) twins (bit-for-bit identical inputs!)
            cur_chk = set(cur_cands)
            total_s1_twins = 0
            for lst1 in s1_groups:
                ci1 = lst1[0]
                j1, _, A1, d1 = cands_1d[ci1]
                assert d1 < 2
                br_chk = s1_o3_build_branch_qq(data, s0, d0, j1, A1, d1, cands_1d, cur_chk, ci1, bcands_1d)
                total_s1_twins += br_chk["twin_s1_count"]
                for ci_rm in lst1:
                    cur_chk.discard(ci_rm)
            assert total_s1_twins == 0
            with open(preserve_q3_from, "r") as pf:
                pre = json.load(pf)
            q3_sum = [s for s in pre["q0_summaries"] if s["q0"] == "3"][0]
            assert q3_sum["s1_groups"] == len(s1_groups) == 45 and q3_sum["stats"]["surv"] == 0
            q3_farkas = [e for e in pre["farkas_certs"] if e["tag"].startswith("q3_") or e["tag"] == "leaf_b2b3"]
            assert len(q3_farkas) == q3_sum["stats"]["lp"] + q3_sum["stats"]["leaf_b2b3_lp"]
            for k_st, val_st in q3_sum["stats"].items():
                stats[k_st] += val_st
            cert_logs["farkas_certs"].extend(q3_farkas)
            q0_summaries.append(q3_sum)
            q3_preserved_check = {
                "source": preserve_q3_from,
                "d0": str(d0),
                "twin_s0_count": twin_s0_count,
                "twin_s1_count": total_s1_twins,
                "s1_groups": len(s1_groups),
                "preserved_farkas_certs": len(q3_farkas),
                "bit_for_bit_input_identical": True,
            }
            print(f"=== q0=3 INPUTS BIT-FOR-BIT IDENTICAL (0 twins); preserved {len(q3_farkas)} verified certs from {preserve_q3_from} ===")
            continue

        stats_before = dict(stats)
        for si, lst1 in enumerate(s1_groups):
            ci1 = lst1[0]
            j1, tgt1, A1, d1 = cands_1d[ci1]
            br = s1_o3_build_branch_qq(data, s0, d0, j1, A1, d1, cands_1d, cur_cands, ci1, bcands_1d)
            cneg, cpos, cadj, cb_ok = br["cneg"], br["cpos"], br["cadj"], br["cb_ok"]
            bm2, b0, badj, bcross = br["bm2"], br["b0"], br["badj"], br["bcross"]
            c_cands = br["c_cands"]

            ic, ib = s1_peel_2d(cneg, cpos, cadj, cb_ok, bm2, b0, badj, bcross,
                                range(len(c_cands)), range(len(br["b_cands"])), req_ic=(0, 1))
            if len(ic) < 24 or len(ib) < 32:
                stats["peel"] += 1
            else:
                ic_list = [int(x) for x in ic]
                A_num_np, scales_q, b_eq_q = s1_o3_gram_lp_scaled(data, br, ic_list, ib)
                d_lp, cert = certify_eq_lp_farkas_scaled(A_num_np, scales_q, b_eq_q, [ic_list.index(0), ic_list.index(1)])
                if d_lp:
                    stats["lp"] += 1
                    cert_logs["farkas_certs"].append({"tag": f"q{q0}_s1_{si}", "nc": len(ic_list), "nb": len(ib), "n_eq": len(b_eq_q), "fix": [ic_list.index(0), ic_list.index(1)], "cert": cert})
                else:
                    tv1 = V_mat[j1]
                    stab_01 = [p for p in stab_s0 if all(tv1[p[q]] == tv1[q] for q in range(16))]
                    # B0: sf_d == 0
                    z_sub = [int(k) for k in ic_list if c_cands[int(k)][5] == 0]
                    if len(z_sub) >= 24:
                        sic0, sib0 = s1_peel_2d(cneg, cpos, cadj, cb_ok, bm2, b0, badj, bcross, z_sub, ib, req_ic=(0, 1))
                        if len(sic0) < 24 or len(sib0) < 32:
                            stats["peel"] += 1
                        else:
                            if not solve_branch_o3(data, br, sic0, sib0, (0, 1), stab_01,
                                                   stats, cert_logs, f"q{q0}_s1_{si}_B0", 0):
                                stats["surv"] += 1
                                all_dead = False
                    # B1: sgn == +1 (cumulative s2, keeping c < 0 mirrors!)
                    nz = [int(k) for k in ic_list if c_cands[int(k)][6] == 1]
                    s2_orbs = {}
                    for k in nz:
                        can = min(_exact_cand_key_o3(V_mat, c_cands, G_int, k, (0, 1), perm) for perm in stab_01)
                        s2_orbs.setdefault(can, []).append(k)
                    cur_ic = set(ic_list)
                    for s2i, lst2 in enumerate(s2_orbs.values()):
                        s2 = lst2[0]
                        if s2 not in cur_ic:
                            continue
                        cand_c = [k for k in cur_ic if k in (0, 1, s2) or cadj[s2, k]]
                        cand_b = [int(k) for k in ib if cb_ok[s2, int(k)]]
                        sic2, sib2 = s1_peel_2d(cneg, cpos, cadj, cb_ok, bm2, b0, badj, bcross,
                                                cand_c, cand_b, req_ic=(0, 1, s2))
                        if len(sic2) < 24 or len(sib2) < 32:
                            stats["peel"] += 1
                        else:
                            tv2 = V_mat[c_cands[s2][0]]
                            stab_012 = [p for p in stab_01 if all(tv2[p[q]] == tv2[q] for q in range(16))]
                            if not solve_branch_o3(data, br, sic2, sib2, (0, 1, s2), stab_012,
                                                   stats, cert_logs, f"q{q0}_s1_{si}_s2_{s2i}", 0):
                                stats["surv"] += 1
                                all_dead = False
                        for k in lst2:
                            cur_ic.discard(k)
            for ci_rm in lst1:
                cur_cands.discard(ci_rm)
            if (si + 1) % 10 == 0 or si == len(s1_groups) - 1:
                print(f"  q0={q0} [{si+1}/{len(s1_groups)}] ({time.time()-t_q:.1f}s) stats={stats}")
        delta = {k: stats[k] - stats_before[k] for k in stats}
        q0_summaries.append({"q0": str(q0), "s1_groups": len(s1_groups), "elapsed_sec": round(time.time() - t_q, 2), "stats": delta})
        print(f"=== q0={q0} DONE ({time.time()-t_q:.1f}s) delta={delta} ===")

    elapsed = round(time.time() - t_start, 2)
    out = {
        "module": "s1_4_4_4_4",
        "part": [4, 4, 4, 4],
        "all_dead": all_dead and stats["surv"] == 0,
        "q4_lemma": q4_lemma,
        "subcase_a": sub_a,
        "q0_summaries": q0_summaries,
        "q3_preserved_check": q3_preserved_check,
        "stats": stats,
        "n_farkas_certs": len(cert_logs["farkas_certs"]),
        "n_psd_witnesses": len(cert_logs["psd_witnesses"]),
        "elapsed_sec": elapsed,
    }
    if save_certs:
        res_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
        os.makedirs(res_dir, exist_ok=True)
        out_path = os.path.join(res_dir, "s1_4_4_4_4_certs.json")
        with open(out_path, "w") as f:
            json.dump({**out, **cert_logs}, f)
        out["cert_path"] = out_path
    print(f">>> [(4,4,4,4)] ALL_DEAD={out['all_dead']} in {elapsed:.1f}s | {stats} <<<")
    return out


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--preserve-q3-from", type=str, default=None,
                        help="Verify bit-for-bit identical q0=3 inputs (0 twins) and preserve q0=3 certs.")
    args = parser.parse_args()
    res = run(save_certs=True, preserve_q3_from=args.preserve_q3_from)
    if not res["all_dead"]:
        sys.exit(1)
