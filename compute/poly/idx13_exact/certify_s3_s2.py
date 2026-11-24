"""Zero-float-trust exact certification of S3 = (26, 42, 6, 0) and S2 = (25, 45, 3, 1)
for (19, 74) idx=13.

Remediates ALL RT-19 blockers:
  1. Exact QQ LDL^T PSD + <= 20I checks (`ldlt_psd_witness_qq`), exact rank (`rref_rank_qq`),
     and exact rational Moore-Penrose pseudoinverses (`pinv_qq`) & nullspaces (`nullspace_qq`).
  2. Exact QQ Schur complements and exact integer (ZZ / object) pairwise compatibility
     checks via `exact_compat_from_gram_zz`: g(u,v) + s_u*s_v*sqrt(r_u*r_v) == p/q
     iff sign_prod * (p*D - q*G_num) > 0 and ((p*D - q*G_num)*D_r)^2 == r_u_num*r_v_num*(q*D)^2.
  3. Exact O(2) rotated residual frames (`rk == 13`) in QQ without any floating-point sqrt(r0):
     pad w_j by beta_j = T_j - g(s0, j) in QQ and M^+ by 1/r0 in QQ so rotated dot products
     g^rot(j,k) = g(j,k) + beta_j*beta_k/r0 remain 100% exact rationals in QQ.
  4. Zero SCALE=10000 / +-50 slacks in CP-SAT:
     - Trace bounds cleared by exact integer LCM.
     - PSD eigenmode-like budgets computed in exact integers via `untrusted_psd_test_vectors`
       (`sum (w^T v)^2 <= w^T (20M - M^2) w` cleared exactly in ZZ).
     - Exact S3 Orbit 9 pair 1 A_1/A_2 residual lower bound >= 7/3 proven via CP-SAT UNSAT
       on `< 7/3` (replacing float `a1_lower = 2.3333`).
     - Exact rational canonical orbit keys (zero `round(... * 1e4)`) and fixed `compat.index(s0_idx)`.
"""
from __future__ import annotations

import itertools
import json
import math
import time
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import numpy as np
from ortools.sat.python import cp_model

from exact_common import (
    build_adj_paths_cycles,
    clear_linear_eq_to_ints,
    dot_qq,
    lcm_list,
    ldlt_psd_witness_qq,
    nullspace_qq,
    pinv_qq,
    to_frac,
    untrusted_psd_test_vectors,
)


def even_parts(m: int, min_p: int = 4):
    if m == 0:
        yield ()
        return
    for p in range(min_p, m + 1, 2):
        for r in even_parts(m - p, p):
            yield (p,) + r


def check_psd_0_20_rank_qq(M_rows: Sequence[Sequence[Fraction]]) -> Tuple[bool, int]:
    """Verify 0 <= M <= 20*I in exact Fraction via pivoted LDL^T, returning (ok, rank)."""
    ok_psd, _ = ldlt_psd_witness_qq(M_rows)
    if not ok_psd:
        return False, -1
    n = len(M_rows)
    twenty = Fraction(20)
    zero = Fraction(0)
    diff20 = [
        [(twenty if i == j else zero) - to_frac(M_rows[i][j]) for j in range(n)]
        for i in range(n)
    ]
    ok_20, _ = ldlt_psd_witness_qq(diff20)
    if not ok_20:
        return False, -1
    # Exact Fraction Gaussian elimination for rank
    A = [[to_frac(M_rows[i][j]) for j in range(n)] for i in range(n)]
    rk = 0
    for c in range(n):
        piv = -1
        for r in range(rk, n):
            if A[r][c] != 0:
                piv = r
                break
        if piv < 0:
            continue
        A[rk], A[piv] = A[piv], A[rk]
        inv = Fraction(1) / A[rk][c]
        for r in range(rk + 1, n):
            f = A[r][c] * inv
            if f != 0:
                for j in range(c, n):
                    A[r][j] -= f * A[rk][j]
        rk += 1
    return True, rk


def make_20M_minus_M2_qq(M_rows: Sequence[Sequence[Fraction]]) -> List[List[Fraction]]:
    n = len(M_rows)
    twenty = Fraction(20)
    M = [[to_frac(M_rows[i][j]) for j in range(n)] for i in range(n)]
    W = [[Fraction(0)] * n for _ in range(n)]
    for i in range(n):
        for j in range(i, n):
            m2 = sum(M[i][k] * M[k][j] for k in range(n))
            val = twenty * M[i][j] - m2
            W[i][j] = W[j][i] = val
    return W


def _mat_qq_to_scaled_arr(mat_qq: Sequence[Sequence[Fraction]]) -> Tuple[np.ndarray, int]:
    D = 1
    for row in mat_qq:
        for v in row:
            vf = to_frac(v)
            if vf != 0:
                D = math.lcm(D, vf.denominator)
    arr = np.array([[int(to_frac(v) * D) for v in row] for row in mat_qq], dtype=object)
    return arr, D


def exact_compat_from_gram_zz(
    W_left_qq: Sequence[Sequence[Fraction]],
    M_gram_qq: Sequence[Sequence[Fraction]],
    W_right_qq: Sequence[Sequence[Fraction]],
    r_left: Sequence[Fraction],
    s_left: Sequence[int],
    r_right: Sequence[Fraction],
    s_right: Sequence[int],
    targets: Sequence[Tuple[int, int]],
) -> np.ndarray:
    """100% exact integer compatibility matrix for:
    g(w_i, w_j) + s_i * s_j * sqrt(r_i * r_j) == p / q,
    where g(u, v) = u^T M_gram v in QQ, r_i, r_j in QQ>=0, s_i, s_j in {+1, -1}.
    Uses int64 only when provably overflow-free (< 2^61), else exact Python object ints.
    """
    nL, nR = len(W_left_qq), len(W_right_qq)
    if nL == 0 or nR == 0:
        return np.zeros((nL, nR), dtype=bool)
    WL_arr, DwL = _mat_qq_to_scaled_arr(W_left_qq)
    Mg_arr, Dm = _mat_qq_to_scaled_arr(M_gram_qq)
    WR_arr, DwR = _mat_qq_to_scaled_arr(W_right_qq)
    D_g = DwL * Dm * DwR

    Dr = 1
    for r in r_left:
        if r != 0:
            Dr = math.lcm(Dr, r.denominator)
    for r in r_right:
        if r != 0:
            Dr = math.lcm(Dr, r.denominator)
    rl_list = [int(r * Dr) for r in r_left]
    rr_list = [int(r * Dr) for r in r_right]

    dim = len(M_gram_qq)
    max_wl = int(np.max(np.abs(WL_arr))) if WL_arr.size else 1
    max_mg = int(np.max(np.abs(Mg_arr))) if Mg_arr.size else 1
    max_wr = int(np.max(np.abs(WR_arr))) if WR_arr.size else 1
    max_g = dim * dim * max_wl * max_mg * max_wr
    max_p = max(abs(p) for p, _ in targets)
    max_q = max(q for _, q in targets)
    max_r = max(rl_list + rr_list + [1])
    max_delta = max_p * D_g + max_q * max_g

    use_i64 = (
        max(max_wl, max_mg, max_wr, D_g, Dr) < 2**28
        and max_g < 2**55
        and (max_delta * Dr) ** 2 < 2**61
        and (max_r * max_r * (max_q * D_g) ** 2) < 2**61
    )
    if use_i64:
        G_num = WL_arr.astype(np.int64) @ Mg_arr.astype(np.int64) @ WR_arr.astype(np.int64).T
        rl = np.array(rl_list, dtype=np.int64)[:, None]
        rr = np.array(rr_list, dtype=np.int64)[None, :]
        sp_mat = np.array(s_left, dtype=np.int64)[:, None] * np.array(s_right, dtype=np.int64)[None, :]
    else:
        G_num = WL_arr @ Mg_arr @ WR_arr.T
        rl = np.array(rl_list, dtype=object)[:, None]
        rr = np.array(rr_list, dtype=object)[None, :]
        sp_mat = np.array(s_left, dtype=object)[:, None] * np.array(s_right, dtype=object)[None, :]

    rprod = rl * rr
    nz = rprod != 0
    ok = np.zeros((nL, nR), dtype=bool)
    Dr2 = Dr * Dr
    for p, q in targets:
        delta = p * D_g - q * G_num
        match_z = (~nz) & (delta == 0)
        qD2 = (q * D_g) ** 2
        match_nz = nz & ((sp_mat * delta) > 0) & ((delta * delta) * Dr2 == rprod * qD2)
        ok |= match_z | match_nz
    return ok


def filter_colspace_and_qf_qq(
    W_rows_qq: Sequence[Sequence[Fraction]],
    Mp_qq: Sequence[Sequence[Fraction]],
    nullbasis_qq: Sequence[Sequence[Fraction]],
    limit_qq: Fraction,
    exact_eq: bool,
) -> Tuple[List[int], List[Fraction]]:
    """Return indices i of W_rows_qq satisfying (N * w_i == 0) and w_i^T Mp w_i <= limit_qq (or == limit_qq)."""
    if len(W_rows_qq) == 0:
        return [], []
    if nullbasis_qq:
        W_arr, _ = _mat_qq_to_scaled_arr(W_rows_qq)
        N_arr, _ = _mat_qq_to_scaled_arr(nullbasis_qq)
        dim = len(W_rows_qq[0])
        max_w = int(np.max(np.abs(W_arr))) if W_arr.size else 1
        max_n = int(np.max(np.abs(N_arr))) if N_arr.size else 1
        if dim * max_w * max_n < 2**61:
            prod = W_arr.astype(np.int64) @ N_arr.astype(np.int64).T
        else:
            prod = W_arr @ N_arr.T
        keep_mask = np.all(prod == 0, axis=1)
        keep_idxs = [i for i, k in enumerate(keep_mask) if k]
    else:
        keep_idxs = list(range(len(W_rows_qq)))
    if not keep_idxs:
        return [], []

    W_keep = [W_rows_qq[i] for i in keep_idxs]
    Wk_arr, Dw = _mat_qq_to_scaled_arr(W_keep)
    Mp_arr, Dm = _mat_qq_to_scaled_arr(Mp_qq)
    D_tot = Dw * Dw * Dm
    lim_num = int(limit_qq * D_tot) if (limit_qq * D_tot).denominator == 1 else None
    dim = len(Mp_qq)
    max_wk = int(np.max(np.abs(Wk_arr))) if Wk_arr.size else 1
    max_mp = int(np.max(np.abs(Mp_arr))) if Mp_arr.size else 1
    if dim * dim * max_wk * max_wk * max_mp < 2**61:
        Wk_i64 = Wk_arr.astype(np.int64)
        WMp = Wk_i64 @ Mp_arr.astype(np.int64)
        q_nums = np.sum(WMp * Wk_i64, axis=1)
    else:
        WMp = Wk_arr @ Mp_arr
        q_nums = np.sum(WMp * Wk_arr, axis=1)

    sel_idxs: List[int] = []
    sel_qs: List[Fraction] = []
    for pos, orig_i in enumerate(keep_idxs):
        qn = int(q_nums[pos])
        qf = Fraction(qn, D_tot)
        if exact_eq:
            if qf == limit_qq:
                sel_idxs.append(orig_i)
                sel_qs.append(qf)
        else:
            if lim_num is not None:
                if qn <= lim_num:
                    sel_idxs.append(orig_i)
                    sel_qs.append(qf)
            elif qf <= limit_qq:
                sel_idxs.append(orig_i)
                sel_qs.append(qf)
    return sel_idxs, sel_qs


def gram_pairs_qq(V_list: Sequence[Sequence[Fraction]], Mp_qq: Sequence[Sequence[Fraction]]) -> List[List[Fraction]]:
    n = len(V_list)
    if n == 0:
        return []
    V_arr, Dv = _mat_qq_to_scaled_arr(V_list)
    Mp_arr, Dm = _mat_qq_to_scaled_arr(Mp_qq)
    D = Dv * Dv * Dm
    dim = len(Mp_qq)
    max_v = int(np.max(np.abs(V_arr))) if V_arr.size else 1
    max_m = int(np.max(np.abs(Mp_arr))) if Mp_arr.size else 1
    if dim * dim * max_v * max_v * max_m < 2**61:
        Vi = V_arr.astype(np.int64)
        G_num = Vi @ Mp_arr.astype(np.int64) @ Vi.T
    else:
        G_num = V_arr @ Mp_arr @ V_arr.T
    return [[Fraction(int(G_num[i, j]), D) for j in range(n)] for i in range(n)]


def add_exact_trace_ub(model: cp_model.CpModel, vars_list, res_qq: Sequence[Fraction], rhs_qq: Fraction, extra_lhs_qq: Fraction = Fraction(0)):
    """Add sum res_qq[k] * x_k + extra_lhs_qq <= rhs_qq cleared by exact integer LCM."""
    rem_rhs = to_frac(rhs_qq) - to_frac(extra_lhs_qq)
    if rem_rhs < 0:
        model.Add(0 == 1)
        return
    denoms = [rem_rhs.denominator] + [to_frac(r).denominator for r in res_qq if r != 0]
    L = lcm_list(denoms)
    rhs_int = int(rem_rhs * L)
    terms = []
    for var, r in zip(vars_list, res_qq):
        if r != 0:
            terms.append(int(to_frac(r) * L) * var)
    if terms:
        model.Add(sum(terms) <= rhs_int)


def add_exact_psd_test_ubs(
    model: cp_model.CpModel,
    vars_list,
    W_rows_qq: Sequence[Sequence[Fraction]],
    psd_tests: Sequence[Tuple[List[int], Fraction]],
    extra_vecs_qq: Sequence[Sequence[Fraction]] = (),
):
    """For each untrusted integer test vector q with exact RHS = q^T W q, add exact integer
    constraint: sum (w_k^T q)^2 * x_k <= q^T W q - sum_{e in extra} (e^T q)^2.
    Note: sound in ZZ whenever W - sum v v^T >= 0!
    """
    for q_vec, rhs_qq in psd_tests:
        extra_sum = Fraction(0)
        for ev in extra_vecs_qq:
            d = sum(to_frac(ev[c]) * q_vec[c] for c in range(len(q_vec)))
            extra_sum += d * d
        rem_rhs = to_frac(rhs_qq) - extra_sum
        if rem_rhs < 0:
            model.Add(0 == 1)
            return
        coeffs = []
        for w in W_rows_qq:
            d = sum(to_frac(w[c]) * q_vec[c] for c in range(len(q_vec)))
            coeffs.append(d * d)
        denoms = [rem_rhs.denominator] + [c.denominator for c in coeffs if c != 0]
        L = lcm_list(denoms)
        rhs_int = int(rem_rhs * L)
        c_ints = [int(c * L) for c in coeffs]
        g = math.gcd(abs(rhs_int), *(abs(c) for c in c_ints if c != 0))
        if g > 1:
            rhs_int //= g
            c_ints = [c // g for c in c_ints]
        # Verify safe int64 range (< 2^60) for CP-SAT sum
        max_sum = sum(abs(c) for c in c_ints) + abs(rhs_int)
        if max_sum < 2**58:
            terms = [c * var for c, var in zip(c_ints, vars_list) if c != 0]
            if terms:
                model.Add(sum(terms) <= rhs_int)


def add_exact_coupled_psd_test_ubs(
    model: cp_model.CpModel,
    vars_a,
    W_a_qq: Sequence[Sequence[Fraction]],
    vars_b,
    W_b_qq: Sequence[Sequence[Fraction]],
    psd_tests: Sequence[Tuple[List[int], Fraction]],
    mult_b: int = 1,
):
    """Exact integer constraint: sum (w_a^T q)^2 x_a + mult_b * sum (w_b^T q)^2 x_b <= q^T W q."""
    for q_vec, rhs_qq in psd_tests:
        ca = [sum(to_frac(w[c]) * q_vec[c] for c in range(len(q_vec))) ** 2 for w in W_a_qq]
        cb = [mult_b * (sum(to_frac(w[c]) * q_vec[c] for c in range(len(q_vec))) ** 2) for w in W_b_qq]
        denoms = [to_frac(rhs_qq).denominator] + [c.denominator for c in ca + cb if c != 0]
        L = lcm_list(denoms)
        rhs_int = int(to_frac(rhs_qq) * L)
        ca_i = [int(c * L) for c in ca]
        cb_i = [int(c * L) for c in cb]
        g = math.gcd(abs(rhs_int), *(abs(c) for c in ca_i + cb_i if c != 0))
        if g > 1:
            rhs_int //= g
            ca_i = [c // g for c in ca_i]
            cb_i = [c // g for c in cb_i]
        if sum(abs(c) for c in ca_i) + sum(abs(c) for c in cb_i) + abs(rhs_int) < 2**58:
            terms = [c * v for c, v in zip(ca_i, vars_a) if c != 0] + [c * v for c, v in zip(cb_i, vars_b) if c != 0]
            if terms:
                model.Add(sum(terms) <= rhs_int)


# ==============================================================================
# PART I: EXACT TOP-LEVEL REDUCTIONS FOR S3=(26,42,6,0) AND S2=(25,45,3,1)
# ==============================================================================

def enumerate_s3_10_orbits():
    """Verify exact Stage-3 E11/E17/E15 constraints on S3=(26,42,6,0) C2 (size 6).
    Checks all (u0, u1, u2) in {(1,1),(1,-1),(-1,-1)}^3 with e1 perp (e2, e3) and v17 perp (e2, e3),
    plus 20*E15[C2] PSD in exact QQ, producing the exact 10 canonical Z_6 orbits.
    """
    blk = [0, 0, 1, 1, 2, 2]
    pairs = [(i, j) for i in range(6) for j in range(i + 1, 6)]
    perms = [[2 * p[0], 2 * p[0] + 1, 2 * p[1], 2 * p[1] + 1, 2 * p[2], 2 * p[2] + 1] for p in itertools.permutations(range(3))]
    seen = set()
    reps = []
    tot_valid = 0
    for u0, u1, u2 in itertools.product([(1, 1), (1, -1), (-1, -1)], repeat=3):
        # v_17 perp (e2, e3) forces block sums equal: u0[0]+u0[1] == u1[0]+u1[1] == u2[0]+u2[1]
        if not (sum(u0) == sum(u1) == sum(u2)):
            continue
        u = list(u0 + u1 + u2)
        doms = [([1] if (blk[i] == blk[j] and u[i] * u[j] == 1) else [1, -1]) for i, j in pairs]
        for vals in itertools.product(*doms):
            Z = [[0] * 6 for _ in range(6)]
            for (i, j), v in zip(pairs, vals):
                Z[i][j] = Z[j][i] = v
            E15 = [[Fraction(0)] * 6 for _ in range(6)]
            for i in range(6):
                E15[i][i] = Fraction(5, 2)
                for j in range(i + 1, 6):
                    s = Z[i][j]
                    if blk[i] == blk[j]:
                        val = Fraction(-3, 2) if u[i] * u[j] == 1 else (Fraction(-1, 2) if s == 1 else Fraction(-5, 2))
                    elif u[i] * u[j] == 1:
                        val = Fraction(-1, 2) if s == 1 else Fraction(-5, 2)
                    else:
                        val = Fraction(1, 2) if s == 1 else Fraction(-3, 2)
                    E15[i][j] = E15[j][i] = val
            ok_psd, _ = ldlt_psd_witness_qq(E15)
            if not ok_psd:
                continue
            ok = True
            c0_list = []
            d_list = []
            for i in range(6):
                c0 = 11 * u[i] - sum(u[j] * Z[i][j] for j in range(6) if j != i)
                if abs(c0) > 26 or c0 % 2 != 0:
                    ok = False
                    break
                c2_sum = sum(Z[i][j] for j in range(6) if j != i)
                zb = [sum(Z[i][j] for j in range(6) if j != i and blk[j] == k) for k in range(3)]
                rhs1 = 11 * ((1 if blk[i] == 1 else 0) - (1 if blk[i] == 0 else 0)) + zb[0] - zb[1]
                rhs2 = 11 * ((1 if blk[i] == 2 else 0) - (1 if blk[i] == 0 else 0)) + zb[0] - zb[2]
                num = (34 - 2 * c2_sum) + rhs1 + rhs2
                if num % 3 != 0:
                    ok = False
                    break
                d0 = num // 3
                d1 = d0 - rhs1
                d2 = d0 - rhs2
                if any(abs(d) > 14 or d % 2 != 0 for d in (d0, d1, d2)):
                    ok = False
                    break
                c0_list.append(c0)
                d_list.append((d0, d1, d2))
            if not ok:
                continue
            assert u == [1, -1, 1, -1, 1, -1], f"Unexpected surviving u={u}"
            tot_valid += 1
            canon = min(tuple(Z[perm[i]][perm[j]] for i in range(6) for j in range(i + 1, 6)) for perm in perms)
            if canon not in seen:
                seen.add(canon)
                reps.append((Z, E15, c0_list, d_list))
    assert tot_valid == 34 and len(reps) == 10
    return reps, [1, -1, 1, -1, 1, -1], blk


# ==============================================================================
# PART II: EXACT S3 C0 / A1 CP-SAT SOLVERS (0D / 1D / ROTATED 2D)
# ==============================================================================

def _solve_s3_c0_cp_exact(
    W_items_qq: Sequence[Sequence[Fraction]],
    M_gram_qq: Sequence[Sequence[Fraction]],
    r_items: Sequence[Fraction],
    s_items: Sequence[int],
    cv_items: Sequence[Tuple[int, ...]],
    csc_items: Sequence[Tuple[int, ...]],
    rneg_items: Sequence[int],
    order: Sequence[int],
    c0_list: Sequence[int],
    req_sum_w: Sequence[int],
    psd_tests: Sequence[Tuple[List[int], Fraction]],
    tr_rhs_qq: Fraction,
    fixed_idxs_orig: Sequence[int] | None = None,
    sym_break_r_check: bool = True,
    stab_s0: Sequence[Sequence[int]] | None = None,
    s0_v_orig: Tuple[int, ...] | None = None,
    W_s0_orig_qq: Sequence[Fraction] | None = None,
    Mp_orig_qq: Sequence[Sequence[Fraction]] | None = None,
    nc_split_thresh: int = 650,
    label: str = "",
    trace_items_qq: Sequence[Fraction] | None = None,
) -> Tuple[bool, str]:
    """Solve 26-vertex C0 subproblem with exact integer compatibility & exact CP-SAT."""
    n_all = len(W_items_qq)
    if n_all < 26:
        return True, f"INIT(|c|={n_all})"
    cpos = exact_compat_from_gram_zz(W_items_qq, M_gram_qq, W_items_qq, r_items, s_items, r_items, s_items, [(1, 2)])
    cneg = exact_compat_from_gram_zz(W_items_qq, M_gram_qq, W_items_qq, r_items, s_items, r_items, s_items, [(-3, 2)])
    np.fill_diagonal(cpos, False)
    np.fill_diagonal(cneg, False)
    cadj = cpos | cneg
    rn_arr = np.array(rneg_items, dtype=int)

    al = np.ones(n_all, dtype=bool)
    fixed_set = set(fixed_idxs_orig or ())
    for _ in range(20):
        nal = al & (cneg[:, al].sum(axis=1) >= rn_arr) & (cpos[:, al].sum(axis=1) >= 25 - rn_arr)
        for fi in fixed_set:
            if not nal[fi]:
                return True, "PEEL_FIXED"
        if np.array_equal(nal, al):
            break
        al = nal
    ia = [i for i in range(n_all) if al[i]]
    nc = len(ia)
    if nc < 26:
        return True, f"PEEL(nc={nc})"

    def run_cp(sub_ia: Sequence[int], fix_in_orig: Sequence[int], timeout: float = 60.0) -> Tuple[int, float]:
        fix_list = list(fix_in_orig)
        fix_s = set(fix_list)
        for a_i in range(len(fix_list)):
            for b_i in range(a_i + 1, len(fix_list)):
                if not cadj[fix_list[a_i], fix_list[b_i]]:
                    return cp_model.INFEASIBLE, 0.0
        sub_filtered = [k for k in sub_ia if k in fix_s or all(cadj[fi, k] for fi in fix_list)]
        if len(sub_filtered) < 26:
            return cp_model.INFEASIBLE, 0.0
        sub_arr = np.array(sub_filtered, dtype=int)
        cpos_s = cpos[np.ix_(sub_arr, sub_arr)]
        cneg_s = cneg[np.ix_(sub_arr, sub_arr)]
        rn_s = rn_arr[sub_arr]
        al_s = np.ones(len(sub_filtered), dtype=bool)
        fix_pos = [sub_filtered.index(fi) for fi in fix_list]
        for _ in range(15):
            nal_s = al_s & (cneg_s[:, al_s].sum(axis=1) >= rn_s) & (cpos_s[:, al_s].sum(axis=1) >= 25 - rn_s)
            if any(not nal_s[fp] for fp in fix_pos):
                return cp_model.INFEASIBLE, 0.0
            if np.array_equal(nal_s, al_s):
                break
            al_s = nal_s
        sub_ia = [sub_filtered[i] for i in range(len(sub_filtered)) if al_s[i]]
        n = len(sub_ia)
        if n < 26:
            return cp_model.INFEASIBLE, 0.0
        idx_map = {orig: pos for pos, orig in enumerate(sub_ia)}
        m = cp_model.CpModel()
        xc = [m.NewBoolVar(f"x{k}") for k in range(n)]
        m.Add(sum(xc) == 26)
        for fi in fix_in_orig:
            m.Add(xc[idx_map[fi]] == 1)
        for mi, oi in enumerate(order):
            m.Add(sum(csc_items[sub_ia[k]][mi] * xc[k] for k in range(n)) == c0_list[oi])
        for w in range(14):
            m.Add(sum(cv_items[sub_ia[k]][w] * xc[k] for k in range(n)) == req_sum_w[w])
        sub_arr = np.array(sub_ia, dtype=int)
        adj_s = cadj[np.ix_(sub_arr, sub_arr)]
        neg_s = cneg[np.ix_(sub_arr, sub_arr)]
        for a in range(n):
            for b in range(a + 1, n):
                if not adj_s[a, b]:
                    m.Add(xc[a] + xc[b] <= 1)
            nbs = [xc[b] for b in range(n) if b != a and neg_s[a, b]]
            req_n = rneg_items[sub_ia[a]]
            m.Add(sum(nbs) >= req_n - 26 * (1 - xc[a]))
            m.Add(sum(nbs) <= req_n + 26 * (1 - xc[a]))
        tr_src = trace_items_qq if trace_items_qq is not None else r_items
        add_exact_trace_ub(m, xc, [tr_src[k] for k in sub_ia], tr_rhs_qq)
        # Note PSD tests act on original M20 coords (first len(q) entries of W_items_qq[k])!
        dim_m = len(psd_tests[0][0]) if psd_tests else 0
        W_sub_orig = [list(W_items_qq[k][:dim_m]) for k in sub_ia]
        add_exact_psd_test_ubs(m, xc, W_sub_orig, psd_tests)
        sv = cp_model.CpSolver()
        sv.parameters.max_time_in_seconds = timeout
        sv.parameters.num_search_workers = 8
        st = sv.Solve(m)
        return st, sv.WallTime()

    if nc <= nc_split_thresh or not stab_s0:
        st, wt = run_cp(ia, fixed_idxs_orig or ())
        assert st == cp_model.INFEASIBLE, f"S3 CP-SAT NOT INFEASIBLE on {label} (nc={nc}): {st}"
        return True, f"INFEASIBLE({wt:.2f}s,nc={nc})"

    # Split large instances cleanly on residual == 0 vs Stab_s0 orbits of residual > 0!
    z_sub = [k for k in ia if r_items[k] == 0]
    if len(z_sub) >= 26:
        f_z = [fi for fi in (fixed_idxs_orig or ()) if r_items[fi] == 0]
        if len(f_z) == len(fixed_idxs_orig or ()):
            st0, wt0 = run_cp(z_sub, f_z)
            assert st0 == cp_model.INFEASIBLE, f"S3 B0 NOT INFEASIBLE on {label}: {st0}"

    fixed_main = list(fixed_idxs_orig or ())
    s0_idx = fixed_main[0] if fixed_main else None
    MpW_s0 = [sum(Mp_orig_qq[r][c] * W_s0_orig_qq[c] for c in range(len(W_s0_orig_qq))) for r in range(len(W_s0_orig_qq))] if (W_s0_orig_qq is not None and Mp_orig_qq is not None) else None
    dim_orig = len(W_s0_orig_qq) if W_s0_orig_qq is not None else (len(W_items_qq[0]) if W_items_qq else 0)
    orbs: Dict[tuple, List[int]] = {}
    for k in ia:
        if r_items[k] == 0 or k in fixed_set:
            continue
        if sym_break_r_check and s_items[k] < 0:
            continue
        tv = cv_items[k]
        bsgn = 0 if sym_break_r_check else s_items[k]
        g0_exact = sum(W_items_qq[k][c] * MpW_s0[c] for c in range(len(MpW_s0))) if MpW_s0 is not None else Fraction(0)
        rot_tail = tuple(W_items_qq[k][dim_orig:])
        can = min((tuple(tv[p] for p in perm), tuple(csc_items[k]), g0_exact, r_items[k], rot_tail, bsgn) for perm in stab_s0)
        orbs.setdefault(can, []).append(k)
    for oi, lst in enumerate(orbs.values()):
        s1 = lst[0]
        compat = [k for k in ia if (k in fixed_set) or k == s1 or cadj[s1, k]]
        if len(compat) < 26:
            continue
        st1, wt1 = run_cp(compat, fixed_main + [s1])
        assert st1 == cp_model.INFEASIBLE, f"S3 B1 orb {oi} NOT INFEASIBLE on {label}: {st1}"
    return True, f"ALL_B0_B1_DEAD({len(orbs)} orbs,nc={nc})"


def run_rotated_orbits_s3(
    W_c0_qq: Sequence[Sequence[Fraction]],
    Mp_qq: Sequence[Sequence[Fraction]],
    res_qq: Sequence[Fraction],
    cv_all: Sequence[Tuple[int, ...]],
    csc_all: Sequence[Tuple[int, ...]],
    rneg_all: Sequence[int],
    order: Sequence[int],
    c0_list: Sequence[int],
    req_sum_w: Sequence[int],
    psd_tests: Sequence[Tuple[List[int], Fraction]],
    stab: Sequence[Sequence[int]],
    tr_rhs_qq: Fraction = Fraction(40),
    rk_dim: int = 13,
    target_orb_idxs: Sequence[int] | None = None,
    label: str = "",
) -> Tuple[bool, str]:
    """100% exact QQ O(2) (or O(1) when rk==14) residual Case 0 + Case 1 orbit loop."""
    n_c0 = len(W_c0_qq)
    if n_c0 < 26:
        return True, f"INIT(|C0|={n_c0})"
    # Exact 14D (or rk) pre-peel using Cauchy-Schwarz compatibility |g_ij - T|^2 <= r_i * r_j!
    # Wait: even better, compute G_base ONCE and pre-peel in exact integer arithmetic!
    W_arr, Dw = _mat_qq_to_scaled_arr(W_c0_qq)
    Mp_arr, Dm = _mat_qq_to_scaled_arr(Mp_qq)
    D_g = Dw * Dw * Dm
    Dr = lcm_list([r.denominator for r in res_qq if r != 0] or [1])
    r_nums = [int(r * Dr) for r in res_qq]
    if len(W_c0_qq[0]) ** 2 * int(np.max(np.abs(W_arr))) ** 2 * int(np.max(np.abs(Mp_arr))) < 2**61:
        Wi = W_arr.astype(np.int64)
        G_num = Wi @ Mp_arr.astype(np.int64) @ Wi.T
        rn = np.array(r_nums, dtype=np.int64)
    else:
        G_num = W_arr @ Mp_arr @ W_arr.T
        rn = np.array(r_nums, dtype=object)
    rprod = rn[:, None] * rn[None, :]
    Dr2 = Dr * Dr
    d_p = 1 * D_g - 2 * G_num
    d_m = (-3) * D_g - 2 * G_num
    can_pos = (d_p * d_p) * Dr2 <= rprod * (4 * D_g * D_g)
    can_neg = (d_m * d_m) * Dr2 <= rprod * (4 * D_g * D_g)
    # Capture self-twin feasibility before clearing the diagonal: m copies of profile i
    # satisfy m * (4 - r_i) <= 4 (from 1^T R_m 1 <= m*r_i + m*(m-1)*(r_i - 4) >= 0).
    self_pos = np.diag(can_pos).copy()
    self_neg = np.diag(can_neg).copy()
    extra_cap = np.array(
        [(int(Fraction(4) / (Fraction(4) - r)) - 1) if r < 4 else 25 for r in res_qq],
        dtype=int,
    )
    extra_pos = self_pos.astype(int) * extra_cap
    extra_neg = self_neg.astype(int) * extra_cap
    np.fill_diagonal(can_pos, False)
    np.fill_diagonal(can_neg, False)
    adj_c = can_pos | can_neg
    rn_arr = np.array(rneg_all, dtype=int)
    al = np.ones(n_c0, dtype=bool)
    for _ in range(15):
        nal = (
            al
            & (can_neg[:, al].sum(axis=1) + extra_neg >= rn_arr)
            & (can_pos[:, al].sum(axis=1) + extra_pos >= 25 - rn_arr)
        )
        if np.array_equal(nal, al):
            break
        al = nal
    ia = [i for i in range(n_c0) if al[i]]
    if len(ia) < 26:
        return True, f"PRE_PEEL({len(ia)})"

    # Case 0: all 26 vertices have res == 0
    z_ia = [i for i in ia if res_qq[i] == 0]
    if len(z_ia) >= 26:
        dead0, msg0 = _solve_s3_c0_cp_exact(
            [W_c0_qq[i] for i in z_ia], Mp_qq, [Fraction(0)] * len(z_ia), [1] * len(z_ia),
            [cv_all[i] for i in z_ia], [csc_all[i] for i in z_ia], [rneg_all[i] for i in z_ia],
            order, c0_list, req_sum_w, psd_tests, tr_rhs_qq, None, True, stab, label=f"{label}_Case0"
        )
        assert dead0, msg0

    # Group nonzero residual states into Stab(v0, v1) orbits
    orbs: Dict[tuple, List[int]] = {}
    for i in ia:
        if res_qq[i] == 0:
            continue
        tv = cv_all[i]
        can = min((tuple(tv[p] for p in perm), csc_all[i]) for perm in stab)
        orbs.setdefault(can, []).append(i)
    orb_reps = sorted([lst[0] for lst in orbs.values()], key=lambda idx: -res_qq[idx])
    sel_orbs = list(range(len(orb_reps))) if target_orb_idxs is None else list(target_orb_idxs)

    m_dim = len(W_c0_qq[0])
    for oi in sel_orbs:
        s0 = orb_reps[oi]
        r0 = res_qq[s0]
        tv0 = cv_all[s0]
        stab_s0 = [perm for perm in stab if tuple(tv0[p] for p in perm) == tv0]
        if rk_dim == 14:
            # 1D exact signed items without rotation! Allow (W[s0], -1) twin when self-compatible.
            W_sub = [W_c0_qq[s0]]
            r_sub = [r0]
            res_orig_sub = [r0]
            s_sub = [1]
            cv_sub = [cv_all[s0]]
            csc_sub = [csc_all[s0]]
            rn_sub = [rneg_all[s0]]
            for j in ia:
                if res_qq[j] > r0:
                    continue
                if j == s0:
                    if not (self_pos[s0] or self_neg[s0]):
                        continue
                elif not adj_c[s0, j]:
                    continue
                g0 = Fraction(int(G_num[s0, j]), D_g)
                rj = res_qq[j]
                for sj in ((1, -1) if rj > 0 else (1,)):
                    if j == s0 and sj == 1:
                        continue
                    matched = False
                    for p, q in ((1, 2), (-3, 2)):
                        delta = Fraction(p, q) - g0
                        if rj == 0:
                            if delta == 0:
                                matched = True
                                break
                        elif sj * delta > 0 and delta * delta == r0 * rj:
                            matched = True
                            break
                    if matched:
                        W_sub.append(W_c0_qq[j])
                        r_sub.append(rj)
                        res_orig_sub.append(rj)
                        s_sub.append(sj)
                        cv_sub.append(cv_all[j])
                        csc_sub.append(csc_all[j])
                        rn_sub.append(rneg_all[j])
            M_rot_qq = Mp_qq
            sym_brk = False
        else:
            # Exact QQ O(2) rotation: pad w_j by beta_j = T - g(s0, j), M_gram = block_diag(Mp, [1/r0])
            # Also generate distinct rotated twin states for j == s0 when self_pos[s0] or self_neg[s0].
            M_rot_qq = [list(row) + [Fraction(0)] for row in Mp_qq] + [[Fraction(0)] * m_dim + [Fraction(1) / r0]]
            W_sub = [list(W_c0_qq[s0]) + [r0]]
            r_sub = [Fraction(0)]
            res_orig_sub = [r0]
            s_sub = [1]
            cv_sub = [cv_all[s0]]
            csc_sub = [csc_all[s0]]
            rn_sub = [rneg_all[s0]]
            for j in ia:
                if res_qq[j] > r0:
                    continue
                if j == s0:
                    if not (self_pos[s0] or self_neg[s0]):
                        continue
                    tgts = ([Fraction(1, 2)] if self_pos[s0] else []) + ([Fraction(-3, 2)] if self_neg[s0] else [])
                else:
                    if not adj_c[s0, j]:
                        continue
                    tgts = ([Fraction(1, 2)] if can_pos[s0, j] else []) + ([Fraction(-3, 2)] if can_neg[s0, j] else [])
                g0 = Fraction(int(G_num[s0, j]), D_g)
                rj = res_qq[j]
                for tgt in tgts:
                    beta = tgt - g0
                    rem = rj - (beta * beta) / r0
                    if rem < 0:
                        continue
                    for sj in ((1, -1) if rem > 0 else (1,)):
                        W_sub.append(list(W_c0_qq[j]) + [beta])
                        r_sub.append(rem)
                        res_orig_sub.append(rj)
                        s_sub.append(sj)
                        cv_sub.append(cv_all[j])
                        csc_sub.append(csc_all[j])
                        rn_sub.append(rneg_all[j])
            sym_brk = True

        dead, msg = _solve_s3_c0_cp_exact(
            W_sub, M_rot_qq, r_sub, s_sub, cv_sub, csc_sub, rn_sub,
            order, c0_list, req_sum_w, psd_tests, tr_rhs_qq, [0], sym_brk, stab_s0,
            cv_all[s0], W_c0_qq[s0], Mp_qq, label=f"{label}_orb{oi}", trace_items_qq=res_orig_sub
        )
        assert dead, msg
    return True, f"ORBS_DEAD({len(sel_orbs)}/{len(orb_reps)})"


# ==============================================================================
# PART III: ALL S3 BRANCHES (ext_neg=0, ext_neg=2, ext_neg=4)
# ==============================================================================

def _perms_for_cycles(offset: int, cl: Sequence[int]) -> List[List[int]]:
    c_groups = []
    off = offset
    for L in cl:
        c_groups.append((L, [[off + ((s - i if rev else s + i) % L) for i in range(L)] for s in range(L) for rev in (False, True)]))
        off += L
    by_L: Dict[int, List[int]] = {}
    for ci, (L, _) in enumerate(c_groups):
        by_L.setdefault(L, []).append(ci)
    perms = []
    for bperm in itertools.product(*(list(itertools.permutations(idxs)) for idxs in by_L.values())):
        cmap = [0] * len(c_groups)
        for idxs, pi_d in zip(by_L.values(), bperm):
            for src, dst in zip(idxs, pi_d):
                cmap[src] = dst
        for cs in itertools.product(*(c_groups[cmap[ci]][1] for ci in range(len(c_groups)))):
            p = list(range(offset))
            for seg in cs:
                p.extend(seg)
            perms.append(p)
    return perms


def certify_s3_extneg0(reps, u, blk) -> dict:
    """Certify S3 Orbits 3, 4, 7, 9 (ext_neg[k0] == 0)."""
    stats: Dict[str, dict] = {}
    parts14 = list(even_parts(14, 4))
    cyc_bal = {
        L: [tuple((-1 if i in c else 1) for i in range(L)) for c in itertools.combinations(range(L), L // 2)]
        for L in (4, 6, 8, 10, 12, 14)
    }

    for ri in (3, 4, 7, 9):
        Z, E15, c0_list, d_list = reps[ri]
        n_mat = [[(14 - d) // 2 for d in d_list[i]] for i in range(6)]
        ext_neg = [sum(n_mat[i][k] for i in range(6) if blk[i] != k) for k in range(3)]
        k0 = ext_neg.index(0)
        z_idx = [2 * k0, 2 * k0 + 1]
        other_z = [j for j in range(6) if blk[j] != k0]
        order = other_z + z_idx
        E6 = [[E15[r][c] for c in order] for r in order]
        E4 = [row[:4] for row in E6[:4]]
        E4p, rk4, _ = pinv_qq(E4)
        # S2 = E6[4:, 4:] - E6[4:, :4] E4p E6[:4, 4:] in exact Fraction
        S2_mat = [[Fraction(0)] * 2 for _ in range(2)]
        for a in range(2):
            for b in range(2):
                sub = sum(E6[4 + a][r] * E4p[r][c] * E6[c][4 + b] for r in range(4) for c in range(4))
                S2_mat[a][b] = E6[4 + a][4 + b] - sub

        orb_log = {}
        for p14 in parts14:
            A = build_adj_paths_cycles([], p14)
            MA = [[Fraction(4 if i == j else (-2 if A[i][j] else 0)) for j in range(14)] for i in range(14)]
            MAp, rkA, _ = pinv_qq(MA)
            cyc_qs = []
            off = 0
            for L in p14:
                Mc_p = [[MAp[off + i][off + j] for j in range(L)] for i in range(L)]
                V = cyc_bal[L]
                qs = [sum(v[i] * Mc_p[i][j] * v[j] for i in range(L) for j in range(L)) for v in V]
                cyc_qs.append((V, qs))
                off += L

            V_c0: List[Tuple[int, ...]] = []
            Q_c0: List[Fraction] = []
            half9 = Fraction(9, 2)
            min_qs = [min(qs) for _, qs in cyc_qs]

            def rec(ci, cq, cv):
                if ci == len(p14):
                    if cq <= half9:
                        V_c0.append(tuple(cv))
                        Q_c0.append(cq)
                    return
                rm = sum(min_qs[ci + 1:], Fraction(0))
                Vs, qs = cyc_qs[ci]
                for ii in range(len(qs)):
                    if cq + qs[ii] + rm <= half9:
                        rec(ci + 1, cq + qs[ii], cv + list(Vs[ii]))

            rec(0, Fraction(0), [])
            idx_z = [i for i, q in enumerate(Q_c0) if q <= S2_mat[0][0]]
            if not idx_z:
                continue
            Vz_list = [[Fraction(v) for v in V_c0[i]] for i in idx_z]
            Gz = gram_pairs_qq(Vz_list, MAp)
            perms14 = _perms_for_cycles(0, p14)
            seen_p = set()
            valid_pairs = []
            for i in range(len(idx_z)):
                d0 = S2_mat[0][0] - Gz[i][i]
                for j in range(len(idx_z)):
                    d1 = S2_mat[1][1] - Gz[j][j]
                    offd = S2_mat[0][1] - Gz[i][j]
                    det2 = d0 * d1 - offd * offd
                    if det2 < 0:
                        continue
                    rk2 = 0 if (d0 == 0 and d1 == 0 and offd == 0) else (1 if det2 == 0 else 2)
                    if rk4 + rkA + rk2 > 15:
                        continue
                    ti = V_c0[idx_z[i]]
                    tj = V_c0[idx_z[j]]
                    can = min(tuple((ti[p], tj[p]) for p in perm) for perm in perms14)
                    if can not in seen_p:
                        seen_p.add(can)
                        valid_pairs.append((ti, tj, rk4 + rkA + rk2))
            if not valid_pairs:
                continue

            pair_logs = []
            for pi_idx, (v0, v1, rk_exp) in enumerate(valid_pairs):
                M20 = [[Fraction(0)] * 20 for _ in range(20)]
                for r in range(14):
                    for c in range(14):
                        M20[r][c] = MA[r][c]
                    M20[r][18] = M20[18][r] = Fraction(v0[r])
                    M20[r][19] = M20[19][r] = Fraction(v1[r])
                for r in range(6):
                    for c in range(6):
                        M20[14 + r][14 + c] = E6[r][c]
                ok20, rk20 = check_psd_0_20_rank_qq(M20)
                if not ok20 or rk20 > 15:
                    pair_logs.append(f"p{pi_idx}:M20_FAIL")
                    continue
                assert rk20 == rk_exp
                Mp20, _, _ = pinv_qq(M20)
                nb20 = nullspace_qq(M20)
                W_mat20 = make_20M_minus_M2_qq(M20)
                psd_tests = untrusted_psd_test_vectors(M20, W_mat20, scale=250)

                # Build C0 candidates in exact Fraction
                W_cand = []
                cand_cv = []
                cand_sc = []
                half_u = [Fraction(-u[oi], 2) for oi in order]
                for sc2 in itertools.product((1, -1), repeat=6):
                    if ri == 9 and (sc2[0] + sc2[1] != 0 or sc2[2] + sc2[3] != 0 or sc2[4] + sc2[5] != 0):
                        continue
                    tail = [Fraction(sc2[mi]) + half_u[mi] for mi in range(6)]
                    for v in V_c0:
                        W_cand.append([Fraction(x) for x in v] + tail)
                        cand_cv.append(v)
                        cand_sc.append(sc2)
                keep_i, keep_q = filter_colspace_and_qf_qq(W_cand, Mp20, nb20, half9, rk20 == 15)
                if len(keep_i) < 26:
                    pair_logs.append(f"p{pi_idx}:|C0|={len(keep_i)}<26")
                    continue

                W_ok = [W_cand[idx] for idx in keep_i]
                cv_ok = [cand_cv[idx] for idx in keep_i]
                sc_ok = [cand_sc[idx] for idx in keep_i]
                res_ok = [half9 - q for q in keep_q]
                rn_ok = [(14 + sum(u[order[mi]] * sc[mi] for mi in range(6))) // 2 for sc in sc_ok]
                req_sum_w = [-(v0[w] - v1[w]) for w in range(14)]
                stab = [perm for perm in perms14 if tuple(v0[p] for p in perm) == v0 and tuple(v1[p] for p in perm) == v1]

                # Special exact tight lower bound for Orbit 9 pair 1 (rk20 == 14) on A1 & A2:
                # Verify min_res(A1) >= 7/3 and min_res(A2) >= 7/3 via pure CP-SAT UNSAT on < 7/3!
                tr_rhs = Fraction(20) * (15 - rk20)
                if ri == 9 and pi_idx == 1 and rk20 == 14:
                    a_min_total = Fraction(0)
                    for blk_pos in ((14, 15), (16, 17)):
                        W_a = []
                        cv_a = []
                        s_a_pair = []
                        for s_blk in (1, -1):
                            for v in V_c0:
                                row = [Fraction(x) for x in v] + [Fraction(0)] * 6
                                row[blk_pos[0]] = Fraction(s_blk)
                                row[blk_pos[1]] = Fraction(-s_blk)
                                W_a.append(row)
                                cv_a.append(v)
                                s_a_pair.append(s_blk)
                        ai_idx, ai_q = filter_colspace_and_qf_qq(W_a, Mp20, nb20, Fraction(4), False)
                        b_W, b_r, b_s, b_cv, b_sp = [], [], [], [], []
                        for k_pos, q_val in zip(ai_idx, ai_q):
                            rv = Fraction(4) - q_val
                            for sgn in ((1, -1) if rv > 0 else (1,)):
                                b_W.append(W_a[k_pos])
                                b_r.append(rv)
                                b_s.append(sgn)
                                b_cv.append(cv_a[k_pos])
                                b_sp.append(s_a_pair[k_pos])
                        m0 = exact_compat_from_gram_zz(b_W, Mp20, b_W, b_r, b_s, b_r, b_s, [(0, 1)])
                        mm2 = exact_compat_from_gram_zz(b_W, Mp20, b_W, b_r, b_s, b_r, b_s, [(-2, 1)])
                        np.fill_diagonal(m0, False)
                        np.fill_diagonal(mm2, False)
                        badj = m0 | mm2
                        al_b = np.ones(len(b_r), dtype=bool)
                        for _ in range(15):
                            na = al_b & (m0[:, al_b].sum(axis=1) >= 11) & (mm2[:, al_b].sum(axis=1) >= 2)
                            if np.array_equal(na, al_b):
                                break
                            al_b = na
                        ib = [ii for ii in range(len(b_r)) if al_b[ii]]
                        ma1 = cp_model.CpModel()
                        xa = [ma1.NewBoolVar(f"a{i}") for i in range(len(ib))]
                        ma1.Add(sum(xa) == 14)
                        ma1.Add(sum(b_sp[ib[i]] * xa[i] for i in range(len(ib))) == 0)
                        req_a = [-(v0[w] + v1[w]) for w in range(14)]
                        for w in range(14):
                            ma1.Add(sum(b_cv[ib[i]][w] * xa[i] for i in range(len(ib))) == req_a[w])
                        ib_arr = np.array(ib, dtype=int)
                        badj_s = badj[np.ix_(ib_arr, ib_arr)]
                        mm2_s = mm2[np.ix_(ib_arr, ib_arr)]
                        for i in range(len(ib)):
                            for j in range(i + 1, len(ib)):
                                if not badj_s[i, j]:
                                    ma1.Add(xa[i] + xa[j] <= 1)
                            nb_m2 = [xa[j] for j in range(len(ib)) if mm2_s[i, j]]
                            ma1.Add(sum(nb_m2) >= 2 - 14 * (1 - xa[i]))
                            ma1.Add(sum(nb_m2) <= 2 + 14 * (1 - xa[i]))
                        # Triangle-free check (every cycle has even length >= 4)
                        for i in range(len(ib)):
                            for j in range(i + 1, len(ib)):
                                if not mm2_s[i, j]:
                                    continue
                                for m_v in range(j + 1, len(ib)):
                                    if mm2_s[i, m_v] and mm2_s[j, m_v]:
                                        ma1.Add(xa[i] + xa[j] + xa[m_v] <= 2)
                        # Exact LCM prove sum_{A_blk} r_y >= 7/3 by proving < 7/3 is INFEASIBLE!
                        L_a = lcm_list([3] + [b_r[idx].denominator for idx in ib if b_r[idx] != 0])
                        ma1.Add(sum(int(b_r[ib[i]] * L_a) * xa[i] for i in range(len(ib))) <= int(Fraction(7, 3) * L_a) - 1)
                        sva = cp_model.CpSolver()
                        sva.parameters.max_time_in_seconds = 15.0
                        sva.parameters.num_search_workers = 8
                        sta = sva.Solve(ma1)
                        assert sta == cp_model.INFEASIBLE, f"Orbit 9 pair 1 min_A_res < 7/3 feasible? {sta}"
                        a_min_total += Fraction(7, 3)
                    tr_rhs = Fraction(20) - a_min_total  # Exact 46/3!

                if ri == 9 and pi_idx == 1 and rk20 == 14:
                    W_1d, r_1d, s_1d, cv_1d, sc_1d, rn_1d = [], [], [], [], [], []
                    for w_row, rv, cv_v, sc_v, rn_v in zip(W_ok, res_ok, cv_ok, sc_ok, rn_ok):
                        for sgn in ((1, -1) if rv > 0 else (1,)):
                            W_1d.append(w_row); r_1d.append(rv); s_1d.append(sgn)
                            cv_1d.append(cv_v); sc_1d.append(sc_v); rn_1d.append(rn_v)
                    cpos_9 = exact_compat_from_gram_zz(W_1d, Mp20, W_1d, r_1d, s_1d, r_1d, s_1d, [(1, 2)])
                    cneg_9 = exact_compat_from_gram_zz(W_1d, Mp20, W_1d, r_1d, s_1d, r_1d, s_1d, [(-3, 2)])
                    np.fill_diagonal(cpos_9, False)
                    np.fill_diagonal(cneg_9, False)
                    cadj_9 = cpos_9 | cneg_9
                    al9 = np.ones(len(W_1d), dtype=bool)
                    for _ in range(15):
                        na9 = al9 & (cneg_9[:, al9].sum(axis=1) >= 8) & (cpos_9[:, al9].sum(axis=1) >= 17)
                        if np.array_equal(na9, al9):
                            break
                        al9 = na9
                    ia9 = [i for i in range(len(W_1d)) if al9[i]]
                    neg0_orbs: Dict[tuple, List[int]] = {}
                    for idx_i in ia9:
                        if sc_1d[idx_i][4] == -1 and s_1d[idx_i] == 1:
                            can = min((tuple(cv_1d[idx_i][p] for p in perm), sc_1d[idx_i]) for perm in stab)
                            neg0_orbs.setdefault(can, []).append(idx_i)
                    for noi, lst in enumerate(neg0_orbs.values()):
                        s0_i = lst[0]
                        tv0 = cv_1d[s0_i]
                        stab_s0 = [perm for perm in stab if tuple(tv0[p] for p in perm) == tv0]
                        if r_1d[s0_i] == 0:
                            z_sub = [s0_i] + [j for j in ia9 if j != s0_i and cadj_9[s0_i, j] and r_1d[j] == 0]
                            if len(z_sub) >= 26:
                                dA, msgA = _solve_s3_c0_cp_exact(
                                    [W_1d[j] for j in z_sub], Mp20, [r_1d[j] for j in z_sub], [s_1d[j] for j in z_sub],
                                    [cv_1d[j] for j in z_sub], [sc_1d[j] for j in z_sub], [rn_1d[j] for j in z_sub],
                                    order, c0_list, req_sum_w, psd_tests, tr_rhs, [0], True, label=f"r9p1_no{noi}_CaseA"
                                )
                                assert dA, msgA
                            nz_orbs: Dict[tuple, List[int]] = {}
                            for j in ia9:
                                if j != s0_i and cadj_9[s0_i, j] and r_1d[j] > 0 and s_1d[j] == 1:
                                    can = min((tuple(cv_1d[j][p] for p in perm), sc_1d[j]) for perm in stab_s0)
                                    nz_orbs.setdefault(can, []).append(j)
                            for s1_lst in nz_orbs.values():
                                s1_i = s1_lst[0]
                                sub_i = [s0_i, s1_i] + [j for j in ia9 if j not in (s0_i, s1_i) and cadj_9[s0_i, j] and cadj_9[s1_i, j]]
                                if len(sub_i) >= 26:
                                    dB, msgB = _solve_s3_c0_cp_exact(
                                        [W_1d[j] for j in sub_i], Mp20, [r_1d[j] for j in sub_i], [s_1d[j] for j in sub_i],
                                        [cv_1d[j] for j in sub_i], [sc_1d[j] for j in sub_i], [rn_1d[j] for j in sub_i],
                                        order, c0_list, req_sum_w, psd_tests, tr_rhs, [0, 1], True, label=f"r9p1_no{noi}_CaseB"
                                    )
                                    assert dB, msgB
                        else:
                            sub_i = [s0_i] + [j for j in ia9 if j != s0_i and cadj_9[s0_i, j]]
                            if len(sub_i) >= 26:
                                dC, msgC = _solve_s3_c0_cp_exact(
                                    [W_1d[j] for j in sub_i], Mp20, [r_1d[j] for j in sub_i], [s_1d[j] for j in sub_i],
                                    [cv_1d[j] for j in sub_i], [sc_1d[j] for j in sub_i], [rn_1d[j] for j in sub_i],
                                    order, c0_list, req_sum_w, psd_tests, tr_rhs, [0], False, label=f"r9p1_no{noi}_CaseR"
                                )
                                assert dC, msgC
                    pair_logs.append(f"p{pi_idx}(rk={rk20}):KILLED_BY_MIN_A1_A2_AND_CASES")
                elif rk20 == 15 or (rk20 == 14 and len(W_ok) < 400):
                    W_1d, r_1d, s_1d, cv_1d, sc_1d, rn_1d = [], [], [], [], [], []
                    for w_row, rv, cv_v, sc_v, rn_v in zip(W_ok, res_ok, cv_ok, sc_ok, rn_ok):
                        for sgn in ((1, -1) if (rk20 == 14 and rv > 0) else (1,)):
                            W_1d.append(w_row); r_1d.append(rv); s_1d.append(sgn)
                            cv_1d.append(cv_v); sc_1d.append(sc_v); rn_1d.append(rn_v)
                    dead, msg = _solve_s3_c0_cp_exact(
                        W_1d, Mp20, r_1d, s_1d, cv_1d, sc_1d, rn_1d,
                        order, c0_list, req_sum_w, psd_tests, tr_rhs, None, True, stab, label=f"r{ri}p{pi_idx}"
                    )
                    assert dead, msg
                    pair_logs.append(f"p{pi_idx}(rk={rk20}):{msg}")
                else:
                    dead, msg = run_rotated_orbits_s3(
                        W_ok, Mp20, res_ok, cv_ok, sc_ok, rn_ok,
                        order, c0_list, req_sum_w, psd_tests, stab, tr_rhs, rk20, None, f"r{ri}p{pi_idx}"
                    )
                    assert dead, msg
                    pair_logs.append(f"p{pi_idx}(rk={rk20}):{msg}")
                print(f"    [S3 orb{ri} {p14} pair {pi_idx}/{len(valid_pairs)-1}] rk={rk20} |C0|={len(W_ok)} -> {pair_logs[-1]}", flush=True)

            orb_log[str(p14)] = pair_logs
        stats[f"orbit_{ri}"] = {"status": "KILLED", "partitions": orb_log}
        print(f"  [S3 ext_neg=0] Orbit {ri} CERTIFIED KILLED: {list(orb_log.keys())}", flush=True)
    return stats


def _certify_s3_path_graph_family(
    Z, E15, c0_list, d_list, u, blk, paths_list, links, cl, k0: int, act_pos: Sequence[int], label: str
) -> List[str]:
    """Certify all symmetry-reduced (v0, v1) pairs on one (paths_list, cl, links) graph of S3."""
    other_z = [j for j in range(6) if blk[j] != k0]
    z_idx = [2 * k0, 2 * k0 + 1]
    order = other_z + z_idx
    E6 = [[E15[r][c] for c in order] for r in order]
    A = build_adj_paths_cycles(paths_list, cl)
    MA = [[Fraction(4 if i == j else (-2 if A[i][j] else 0)) for j in range(14)] for i in range(14)]

    M18 = [[Fraction(0)] * 18 for _ in range(18)]
    for r in range(14):
        for c in range(14):
            M18[r][c] = MA[r][c]
    for r in range(4):
        for c in range(4):
            M18[14 + r][14 + c] = E6[r][c]
    for vi, zp in links:
        M18[vi][14 + zp] = M18[14 + zp][vi] = Fraction(-2)

    ok18, rk18 = check_psd_0_20_rank_qq(M18)
    if not ok18 or rk18 > 15:
        return []

    Mp18, _, _ = pinv_qq(M18)
    P_len = sum(paths_list)
    P_idx = list(range(P_len)) + [14, 15, 16, 17]
    Mp4 = [[M18[r][c] for c in P_idx] for r in P_idx]
    Mp4p, _, _ = pinv_qq(Mp4)
    nb_p4 = nullspace_qq(Mp4)

    cyc_bal = {
        L: [tuple((-1 if i in c else 1) for i in range(L)) for c in itertools.combinations(range(L), L // 2)]
        for L in (4, 6, 8, 10, 12)
    }
    cyc_cands = []
    off = P_len
    for L in cl:
        Mc = [[MA[off + r][off + c] for c in range(L)] for r in range(L)]
        Mcp, _, _ = pinv_qq(Mc)
        V = cyc_bal[L]
        qs = [sum(v[i] * Mcp[i][j] * v[j] for i in range(L) for j in range(L)) for v in V]
        cyc_cands.append((V, qs))
        off += L

    half5 = Fraction(5, 2)
    half9 = Fraction(9, 2)
    valid_for_z = []
    for zi_pos, z_orig in enumerate(z_idx):
        d_req = d_list[z_orig][k0]
        nneg_p = (P_len - d_req) // 2
        if nneg_p < 0 or nneg_p > P_len:
            return []
        p_vecs = [tuple((-1 if i in c else 1) for i in range(P_len)) for c in itertools.combinations(range(P_len), nneg_p)]
        Wp = [[Fraction(x) for x in pv] + [E6[r][4 + zi_pos] for r in range(4)] for pv in p_vecs]
        keep_i, keep_q = filter_colspace_and_qf_qq(Wp, Mp4p, nb_p4, half5, False)
        z_list = []
        min_qs_c = [min(qs) for _, qs in cyc_cands]
        for pos, k_idx in enumerate(keep_i):
            pv = p_vecs[k_idx]
            qp = keep_q[pos]
            if qp + sum(min_qs_c, Fraction(0)) > half5:
                continue

            def rec_z(ci, cq, cv):
                if ci == len(cl):
                    if cq <= half5:
                        z_list.append((tuple(cv), cq))
                    return
                rm = sum(min_qs_c[ci + 1:], Fraction(0))
                Vs, qs = cyc_cands[ci]
                for ii in range(len(qs)):
                    if qs[ii] <= half5 and cq + qs[ii] + rm <= half5:
                        rec_z(ci + 1, cq + qs[ii], cv + list(Vs[ii]))

            rec_z(0, qp, list(pv))
        valid_for_z.append(z_list)

    if not valid_for_z[0] or not valid_for_z[1]:
        return []

    perms = _perms_for_cycles(P_len, cl)
    W_z0 = [[Fraction(x) for x in v] + [E6[r][4] for r in range(4)] for v, _ in valid_for_z[0]]
    W_z1 = [[Fraction(x) for x in v] + [E6[r][5] for r in range(4)] for v, _ in valid_for_z[1]]
    W_arr0, Dw0 = _mat_qq_to_scaled_arr(W_z0)
    W_arr1, Dw1 = _mat_qq_to_scaled_arr(W_z1)
    Mp18_arr, Dm18 = _mat_qq_to_scaled_arr(Mp18)
    D18 = Dw0 * Dm18 * Dw1
    G01_num = W_arr0 @ Mp18_arr @ W_arr1.T

    seen_p = set()
    sym_pairs = []
    for i, (v0, q0) in enumerate(valid_for_z[0]):
        d0 = half5 - q0
        for j, (v1, q1) in enumerate(valid_for_z[1]):
            d1 = half5 - q1
            offd = E6[4][5] - Fraction(int(G01_num[i, j]), D18)
            det2 = d0 * d1 - offd * offd
            if det2 < 0:
                continue
            rk2 = 0 if (d0 == 0 and d1 == 0 and offd == 0) else (1 if det2 == 0 else 2)
            if rk18 + rk2 > 15:
                continue
            can = min(tuple((v0[p], v1[p]) for p in perm) for perm in perms)
            if can not in seen_p:
                seen_p.add(can)
                sym_pairs.append((v0, v1, rk18 + rk2))
    if not sym_pairs:
        return []

    # Build V_by_s0 for C0
    MAp, _, _ = pinv_qq(MA)
    Mp_path = [[MAp[r][c] for c in range(P_len)] for r in range(P_len)]
    p_all = [tuple(x) for x in itertools.product((1, -1), repeat=P_len)]
    p_sums = [sum(pv) for pv in p_all]
    W_pa = [[Fraction(x) for x in pv] for pv in p_all]
    _, p_qs = filter_colspace_and_qf_qq(W_pa, Mp_path, [], Fraction(999), False)
    min_qs_c = [min(qs) for _, qs in cyc_cands]
    rmin_c = sum(min_qs_c, Fraction(0))
    V_by_s0: Dict[int, List[Tuple[int, ...]]] = {}
    for s0_val in (-4, -2, 0, 2, 4):
        if abs(s0_val) > P_len:
            continue
        out = []
        for pv, pq in zip(p_all, p_qs):
            if sum(pv) != s0_val or pq + rmin_c > half9:
                continue

            def rec_c0(ci, cq, cv):
                if ci == len(cl):
                    if cq <= half9:
                        out.append(tuple(cv))
                    return
                rm = sum(min_qs_c[ci + 1:], Fraction(0))
                Vs, qs = cyc_cands[ci]
                for ii in range(len(qs)):
                    if cq + qs[ii] + rm <= half9:
                        rec_c0(ci + 1, cq + qs[ii], cv + list(Vs[ii]))

            rec_c0(0, pq, list(pv))
        if out:
            V_by_s0[s0_val] = out

    logs = []
    half_u = [Fraction(-u[oi], 2) for oi in order]
    for pi_idx, (v0, v1, rk_exp) in enumerate(sym_pairs):
        M20 = [[Fraction(0)] * 20 for _ in range(20)]
        for r in range(18):
            for c in range(18):
                M20[r][c] = M18[r][c]
        for r in range(14):
            M20[r][18] = M20[18][r] = Fraction(v0[r])
            M20[r][19] = M20[19][r] = Fraction(v1[r])
        for r in range(4):
            for c in range(2):
                M20[14 + r][18 + c] = M20[18 + c][14 + r] = E6[r][4 + c]
        M20[18][18] = E6[4][4]
        M20[19][19] = E6[5][5]
        M20[18][19] = M20[19][18] = E6[4][5]
        ok20, rk20 = check_psd_0_20_rank_qq(M20)
        if not ok20 or rk20 > 15:
            logs.append(f"p{pi_idx}:M20_FAIL")
            continue
        assert rk20 == rk_exp
        Mp20, _, _ = pinv_qq(M20)
        nb20 = nullspace_qq(M20)
        W_mat20 = make_20M_minus_M2_qq(M20)
        psd_tests = untrusted_psd_test_vectors(M20, W_mat20, scale=250)

        W_cand, cand_cv, cand_sc = [], [], []
        for sc2 in itertools.product((1, -1), repeat=6):
            s0_val = -sum(sc2[mi] for mi in range(4))
            Vs = V_by_s0.get(s0_val, [])
            if not Vs:
                continue
            tail = [Fraction(sc2[mi]) + half_u[mi] for mi in range(6)]
            for v in Vs:
                W_cand.append([Fraction(x) for x in v] + tail)
                cand_cv.append(v)
                cand_sc.append(sc2)
        keep_i, keep_q = filter_colspace_and_qf_qq(W_cand, Mp20, nb20, half9, rk20 == 15)
        if len(keep_i) < 26:
            logs.append(f"p{pi_idx}:|C0|={len(keep_i)}<26")
            continue

        W_ok = [W_cand[idx] for idx in keep_i]
        cv_ok = [cand_cv[idx] for idx in keep_i]
        sc_ok = [cand_sc[idx] for idx in keep_i]
        res_ok = [half9 - q for q in keep_q]
        rn_ok = [(14 + sum(u[order[mi]] * sc[mi] for mi in range(6))) // 2 for sc in sc_ok]

        S_zA0 = [[1] * 14 for _ in range(6)]
        for vi, zp in links:
            S_zA0[zp][vi] = -1
        S_zA0[4] = list(v0)
        S_zA0[5] = list(v1)
        req_sum_w = [-sum(u[order[mi]] * S_zA0[mi][w] for mi in range(6)) for w in range(14)]
        stab = [perm for perm in perms if tuple(v0[p] for p in perm) == v0 and tuple(v1[p] for p in perm) == v1]

        if rk20 in (14, 15) and (rk20 == 15 or len(W_ok) < 400):
            W_1d, r_1d, s_1d, cv_1d, sc_1d, rn_1d = [], [], [], [], [], []
            for w_row, rv, cv_v, sc_v, rn_v in zip(W_ok, res_ok, cv_ok, sc_ok, rn_ok):
                for sgn in ((1, -1) if (rk20 == 14 and rv > 0) else (1,)):
                    W_1d.append(w_row)
                    r_1d.append(rv)
                    s_1d.append(sgn)
                    cv_1d.append(cv_v)
                    sc_1d.append(sc_v)
                    rn_1d.append(rn_v)
            dead, msg = _solve_s3_c0_cp_exact(
                W_1d, Mp20, r_1d, s_1d, cv_1d, sc_1d, rn_1d,
                order, c0_list, req_sum_w, psd_tests, Fraction(20) * (15 - rk20),
                None, True, stab, label=f"{label}_p{pi_idx}"
            )
            assert dead, msg
            logs.append(f"p{pi_idx}(rk={rk20}):{msg}")
        else:
            dead, msg = run_rotated_orbits_s3(
                W_ok, Mp20, res_ok, cv_ok, sc_ok, rn_ok,
                order, c0_list, req_sum_w, psd_tests, stab,
                Fraction(20) * (15 - rk20), rk20, None, f"{label}_p{pi_idx}"
            )
            assert dead, msg
            logs.append(f"p{pi_idx}(rk={rk20}):{msg}")
    return logs


def certify_s3_extneg2_and_0(reps, u, blk) -> dict:
    """Certify S3 Orbits 1, 2, 5, 6, 8 (ext_neg == 2) and Orbit 0 (ext_neg == [4,4,4])."""
    stats: Dict[str, dict] = {}
    graphs14 = [(k, cl) for k in range(2, 15, 2) for cl in even_parts(14 - k, 4)]

    for ri in (1, 2, 5, 6, 8):
        Z, E15, c0_list, d_list = reps[ri]
        n_mat = [[(14 - d) // 2 for d in d_list[i]] for i in range(6)]
        ext_neg = [sum(n_mat[i][k] for i in range(6) if blk[i] != k) for k in range(3)]
        k0 = ext_neg.index(2)
        other_z = [j for j in range(6) if blk[j] != k0]
        active_other = [j for j in other_z if n_mat[j][k0] == 1]
        assert len(active_other) == 2
        act_pos = [other_z.index(j) for j in active_other]
        orb_log = {}
        for kp, cl in graphs14:
            links = [(0, act_pos[0]), (kp - 1, act_pos[1])]
            logs = _certify_s3_path_graph_family(
                Z, E15, c0_list, d_list, u, blk, [kp], links, cl, k0, act_pos, f"S3_orb{ri}_P{kp}_{cl}"
            )
            if logs:
                orb_log[f"P{kp}_{cl}"] = logs
        stats[f"orbit_{ri}"] = {"status": "KILLED", "surviving_graphs": orb_log}
        print(f"  [S3 ext_neg=2] Orbit {ri} CERTIFIED KILLED ({len(orb_log)} graphs had pairs)", flush=True)

    # Orbit 0 (ext_neg = [4, 4, 4])
    Z0, E15_0, c0_0, d_0 = reps[0]
    configs0 = []
    for cl in even_parts(12, 4):
        for p1_grp in [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]:
            configs0.append(([1, 1], cl, [(0, p1_grp[0][0]), (0, p1_grp[0][1]), (1, p1_grp[1][0]), (1, p1_grp[1][1])]))
    for a in range(3, 14, 2):
        for cl in even_parts(13 - a, 4):
            for z_p1 in itertools.combinations(range(4), 2):
                rem = [x for x in range(4) if x not in z_p1]
                configs0.append(([1, a], cl, [(0, z_p1[0]), (0, z_p1[1]), (1, rem[0]), (a, rem[1])]))
    for a in range(2, 13):
        for b in range(a, 15 - a):
            if (a + b) % 2 != 0:
                continue
            for cl in even_parts(14 - a - b, 4):
                z_sets = (
                    [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]
                    if a == b
                    else [(c, tuple(x for x in range(4) if x not in c)) for c in itertools.combinations(range(4), 2)]
                )
                for za, zb in z_sets:
                    configs0.append(([a, b], cl, [(0, za[0]), (a - 1, za[1]), (a, zb[0]), (a + b - 1, zb[1])]))

    orb0_log = {}
    for ci, (paths, cl, links) in enumerate(configs0):
        logs = _certify_s3_path_graph_family(
            Z0, E15_0, c0_0, d_0, u, blk, paths, links, cl, 0, [0, 1], f"S3_orb0_c{ci}"
        )
        if logs:
            orb0_log[f"cfg_{ci}_{paths}_{cl}"] = logs
    stats["orbit_0"] = {"status": "KILLED", "total_configs": len(configs0), "pair_configs": orb0_log}
    print(f"  [S3 ext_neg=4] Orbit 0 ({len(configs0)} configs) CERTIFIED KILLED", flush=True)
    return stats


# ==============================================================================
# PART IV: EXACT CERTIFICATION OF S2 = (25, 45, 3, 1)
# ==============================================================================

def verify_s2_c2_reduction_qq() -> dict:
    """Prove s=+1 is impossible and s=-1 forces z=(1,1,1) in exact Fraction."""
    # s = +1: check exact modular/parity deg_A1 options on B_1:
    s1_valid = []
    for t1, t2, t3 in itertools.product((-1, 1), repeat=3):
        rhs3 = 3 + (1 - 2) * (t1 + t2 + t3)
        if rhs3 % 3 != 0:
            continue
        x2 = rhs3 // 3
        if x2 % 2 != 0:
            continue
        r1 = x2 + 11 - t1
        deg = (14 - r1) // 2
        if 0 <= deg <= 4:
            s1_valid.append(((t1, t2, t3), deg))
    # For s=+1: only ((-1,-1,-1), deg=0) and ((1,1,1), deg=2) pass modular/parity bounds.
    # Cycle components (deg=2) violate sum_{C_L} 20*E15[v, y_1] = sum_{C_L} (1 - 4/3) = -L/3 != 0.
    # Thus A_1 must consist of 15 isolated vertices (deg=0, t1=-1 => 20*E15[v, y_1] = -7/3).
    # Verify exact 16x16 LDL^T witness & exact Schur value 5/2 - 15*(7/3)^2/4 = -215/12 < 0!
    assert sorted(s1_valid) == [((-1, -1, -1), 0), ((1, 1, 1), 2)], f"Unexpected s=+1 deg: {s1_valid}"
    c_wy1 = Fraction(-1) - Fraction(4, 3)  # -7/3
    schur_s1 = Fraction(5, 2) - 15 * (c_wy1 * c_wy1) / Fraction(4)
    assert schur_s1 == Fraction(-215, 12) and schur_s1 < 0
    M16_s1 = [[Fraction(4 if i == j else 0) for j in range(15)] + [c_wy1] for i in range(15)] + [[c_wy1] * 15 + [Fraction(5, 2)]]
    ok_s1, wit_s1 = ldlt_psd_witness_qq(M16_s1)
    assert not ok_s1 and wit_s1 is not None

    # Verify (20*E15)[B18, y_1] == 0 identically (so C_5 decouples from M_18 in (20*E15)^2 = 20*(20*E15)):
    assert Fraction(1) - 16 * Fraction(0) - 22 * Fraction(3, 66) == 0  # A_0 <-> y_1
    assert Fraction(1) - 16 * Fraction(-1, 16) - 22 * Fraction(6, 66) == 0  # C_2 <-> y_1

    # s = -1: check all 4 sign triples z = (z01, z02, z12) in 20*E15[C2]
    surv_z = []
    for z in ((1, 1, 1), (1, 1, -1), (1, -1, -1), (-1, -1, -1)):
        z01, z02, z12 = z
        M_c2 = [
            [Fraction(5, 2), Fraction(z01) - Fraction(3, 2), Fraction(z02) - Fraction(3, 2)],
            [Fraction(z01) - Fraction(3, 2), Fraction(5, 2), Fraction(z12) - Fraction(3, 2)],
            [Fraction(z02) - Fraction(3, 2), Fraction(z12) - Fraction(3, 2), Fraction(5, 2)],
        ]
        ok, _ = ldlt_psd_witness_qq(M_c2)
        if ok:
            surv_z.append(z)
    assert surv_z == [(1, 1, 1)]
    return {
        "s_plus1_killed": "only deg in {0,2}; zero cycles via 20E15[v,y1]=-1/3; all-deg-0 yields Schur=-215/12 < 0 (16x16 LDL^T witness)",
        "c5_decouples_qq": True,
        "s_minus1_surviving_z": [list(z) for z in surv_z],
    }


def _sym_reps_s0_s2(s0_list: Sequence[Tuple[int, ...]], k_path: int, cyc_lens: Sequence[int]):
    p_perms = [list(range(k_path))]
    if k_path > 1:
        p_perms.append(list(reversed(range(k_path))))
    c_groups = []
    off = k_path
    for L in cyc_lens:
        c_groups.append((L, [[off + ((s - i if rev else s + i) % L) for i in range(L)] for s in range(L) for rev in (False, True)]))
        off += L
    by_L: Dict[int, List[int]] = {}
    for ci, (L, _) in enumerate(c_groups):
        by_L.setdefault(L, []).append(ci)
    full_perms = []
    for pp in p_perms:
        for bperm in itertools.product(*(list(itertools.permutations(idxs)) for idxs in by_L.values())):
            cmap = [0] * len(c_groups)
            for idxs, pi_d in zip(by_L.values(), bperm):
                for src, dst in zip(idxs, pi_d):
                    cmap[src] = dst
            for cs in itertools.product(*(c_groups[cmap[ci]][1] for ci in range(len(c_groups)))):
                p = list(pp)
                for seg in cs:
                    p.extend(seg)
                full_perms.append(p)
    seen = set()
    reps = []
    for v in s0_list:
        can = min(tuple(v[p] for p in perm) for perm in full_perms)
        if can not in seen:
            seen.add(can)
            reps.append((v, full_perms))
    return reps


def _solve_s2_c0_1d_exact(
    W_items_qq: Sequence[Sequence[Fraction]],
    M_gram_qq: Sequence[Sequence[Fraction]],
    r_items: Sequence[Fraction],
    s_items: Sequence[int],
    cv_items: Sequence[Tuple[int, ...]],
    csz0: Sequence[int],
    csz1: Sequence[int],
    csz2: Sequence[int],
    rneg_items: Sequence[int],
    req_c0_rowsum: Sequence[int],
    psd_tests: Sequence[Tuple[List[int], Fraction]],
    tr_rhs_qq: Fraction,
    fixed_idxs_orig: Sequence[int] | None = None,
    sym_break_r_check: bool = True,
    stab_s0: Sequence[Sequence[int]] | None = None,
    W_s0_orig_qq: Sequence[Fraction] | None = None,
    Mp_orig_qq: Sequence[Sequence[Fraction]] | None = None,
    nc_split_thresh: int = 650,
    label: str = "",
    trace_items_qq: Sequence[Fraction] | None = None,
) -> Tuple[bool, str]:
    n_all = len(W_items_qq)
    if n_all < 25:
        return True, f"INIT(|c|={n_all})"
    cpos = exact_compat_from_gram_zz(W_items_qq, M_gram_qq, W_items_qq, r_items, s_items, r_items, s_items, [(1, 2)])
    cneg = exact_compat_from_gram_zz(W_items_qq, M_gram_qq, W_items_qq, r_items, s_items, r_items, s_items, [(-3, 2)])
    np.fill_diagonal(cpos, False)
    np.fill_diagonal(cneg, False)
    cadj = cpos | cneg
    rn_arr = np.array(rneg_items, dtype=int)

    al = np.ones(n_all, dtype=bool)
    fixed_set = set(fixed_idxs_orig or ())
    for _ in range(20):
        nal = al & (cneg[:, al].sum(axis=1) >= rn_arr) & (cpos[:, al].sum(axis=1) >= 24 - rn_arr)
        for fi in fixed_set:
            if not nal[fi]:
                return True, "PEEL_FIXED"
        if np.array_equal(nal, al):
            break
        al = nal
    ia = [i for i in range(n_all) if al[i]]
    nc = len(ia)
    if nc < 25:
        return True, f"PEEL(nc={nc})"

    def run_cp(sub_ia: Sequence[int], fix_in_orig: Sequence[int], timeout: float = 60.0) -> Tuple[int, float]:
        fix_list = list(fix_in_orig)
        fix_s = set(fix_list)
        for a_i in range(len(fix_list)):
            for b_i in range(a_i + 1, len(fix_list)):
                if not cadj[fix_list[a_i], fix_list[b_i]]:
                    return cp_model.INFEASIBLE, 0.0
        sub_filtered = [k for k in sub_ia if k in fix_s or all(cadj[fi, k] for fi in fix_list)]
        if len(sub_filtered) < 25:
            return cp_model.INFEASIBLE, 0.0
        sub_arr = np.array(sub_filtered, dtype=int)
        cpos_s = cpos[np.ix_(sub_arr, sub_arr)]
        cneg_s = cneg[np.ix_(sub_arr, sub_arr)]
        rn_s = rn_arr[sub_arr]
        al_s = np.ones(len(sub_filtered), dtype=bool)
        fix_pos = [sub_filtered.index(fi) for fi in fix_list]
        for _ in range(15):
            nal_s = al_s & (cneg_s[:, al_s].sum(axis=1) >= rn_s) & (cpos_s[:, al_s].sum(axis=1) >= 24 - rn_s)
            if any(not nal_s[fp] for fp in fix_pos):
                return cp_model.INFEASIBLE, 0.0
            if np.array_equal(nal_s, al_s):
                break
            al_s = nal_s
        sub_ia = [sub_filtered[i] for i in range(len(sub_filtered)) if al_s[i]]
        n = len(sub_ia)
        if n < 25:
            return cp_model.INFEASIBLE, 0.0
        idx_map = {orig: pos for pos, orig in enumerate(sub_ia)}
        m = cp_model.CpModel()
        xc = [m.NewBoolVar(f"x{k}") for k in range(n)]
        m.Add(sum(xc) == 25)
        for fi in fix_in_orig:
            m.Add(xc[idx_map[fi]] == 1)
        m.Add(sum(xc[k] for k in range(n) if csz0[sub_ia[k]] == 1) == 18)
        m.Add(sum(xc[k] for k in range(n) if csz1[sub_ia[k]] == 1) == 18)
        m.Add(sum(xc[k] for k in range(n) if csz2[sub_ia[k]] == 1) == 18)
        for w in range(15):
            m.Add(sum(cv_items[sub_ia[k]][w] * xc[k] for k in range(n)) == req_c0_rowsum[w])
        sub_arr = np.array(sub_ia, dtype=int)
        adj_s = cadj[np.ix_(sub_arr, sub_arr)]
        neg_s = cneg[np.ix_(sub_arr, sub_arr)]
        for a in range(n):
            for b in range(a + 1, n):
                if not adj_s[a, b]:
                    m.Add(xc[a] + xc[b] <= 1)
            nbs = [xc[b] for b in range(n) if b != a and neg_s[a, b]]
            req_n = rneg_items[sub_ia[a]]
            m.Add(sum(nbs) >= req_n - 25 * (1 - xc[a]))
            m.Add(sum(nbs) <= req_n + 25 * (1 - xc[a]))
        tr_src = trace_items_qq if trace_items_qq is not None else r_items
        add_exact_trace_ub(m, xc, [tr_src[k] for k in sub_ia], tr_rhs_qq)
        dim_m = len(psd_tests[0][0]) if psd_tests else 0
        W_sub_orig = [list(W_items_qq[k][:dim_m]) for k in sub_ia]
        add_exact_psd_test_ubs(m, xc, W_sub_orig, psd_tests)
        sv = cp_model.CpSolver()
        sv.parameters.max_time_in_seconds = timeout
        sv.parameters.num_search_workers = 8
        st = sv.Solve(m)
        return st, sv.WallTime()

    if nc <= nc_split_thresh or not stab_s0:
        st, wt = run_cp(ia, fixed_idxs_orig or ())
        assert st == cp_model.INFEASIBLE, f"S2 CP-SAT NOT INFEASIBLE on {label} (nc={nc}): {st}"
        return True, f"INFEASIBLE({wt:.2f}s,nc={nc})"

    z_sub = [k for k in ia if r_items[k] == 0]
    if len(z_sub) >= 25:
        f_z = [fi for fi in (fixed_idxs_orig or ()) if r_items[fi] == 0]
        if len(f_z) == len(fixed_idxs_orig or ()):
            st0, _ = run_cp(z_sub, f_z)
            assert st0 == cp_model.INFEASIBLE, f"S2 B0 NOT INFEASIBLE on {label}: {st0}"

    fixed_main = list(fixed_idxs_orig or ())
    MpW_s0 = [sum(Mp_orig_qq[r][c] * W_s0_orig_qq[c] for c in range(len(W_s0_orig_qq))) for r in range(len(W_s0_orig_qq))] if (W_s0_orig_qq is not None and Mp_orig_qq is not None) else None
    dim_orig = len(W_s0_orig_qq) if W_s0_orig_qq is not None else (len(W_items_qq[0]) if W_items_qq else 0)
    orbs: Dict[tuple, List[int]] = {}
    for k in ia:
        if r_items[k] == 0 or k in fixed_set:
            continue
        if sym_break_r_check and s_items[k] < 0:
            continue
        tv = cv_items[k]
        bsgn = 0 if sym_break_r_check else s_items[k]
        g0_exact = sum(W_items_qq[k][c] * MpW_s0[c] for c in range(len(MpW_s0))) if MpW_s0 is not None else Fraction(0)
        rot_tail = tuple(W_items_qq[k][dim_orig:])
        can = min((tuple(tv[p] for p in perm), csz0[k], csz1[k], csz2[k], g0_exact, r_items[k], rot_tail, bsgn) for perm in stab_s0)
        orbs.setdefault(can, []).append(k)
    for oi, lst in enumerate(orbs.values()):
        s1 = lst[0]
        compat = [k for k in ia if (k in fixed_set) or k == s1 or cadj[s1, k]]
        if len(compat) < 25:
            continue
        st1, _ = run_cp(compat, fixed_main + [s1])
        assert st1 == cp_model.INFEASIBLE, f"S2 B1 orb {oi} NOT INFEASIBLE on {label}: {st1}"
    return True, f"ALL_B0_B1_DEAD({len(orbs)} orbs,nc={nc})"


def certify_s2() -> dict:
    """Certify all 14 S2=(25,45,3,1) (k_path, cyc_lens) configurations in zero-float-trust QQ/ZZ."""
    top_check = verify_s2_c2_reduction_qq()
    configs = [(k, cl) for k in range(1, 16, 2) for cl in even_parts(15 - k, 4)]
    assert len(configs) == 15
    cyc_bal = {
        L: [tuple((-1 if i in c else 1) for i in range(L)) for c in itertools.combinations(range(L), L // 2)]
        for L in (4, 6, 8, 10, 12, 14)
    }

    half5 = Fraction(5, 2)
    half9 = Fraction(9, 2)
    four = Fraction(4)
    cfg_stats: Dict[str, dict] = {}

    for k, cl in configs:
        A0 = build_adj_paths_cycles([k], cl)
        degs_A0 = [sum(row) for row in A0]
        MA = [[Fraction(4 if i == j else (-2 if A0[i][j] else 0)) for j in range(15)] for i in range(15)]
        MAp, _, _ = pinv_qq(MA)
        Mp_pk = [[MAp[r][c] for c in range(k)] for r in range(k)]

        # z0 vectors
        p_vecs_1 = [tuple((-1 if i in c else 1) for i in range(k)) for c in itertools.combinations(range(k), (k - 1) // 2)]
        W_p1 = [[Fraction(x) for x in v] for v in p_vecs_1]
        _, q_p1 = filter_colspace_and_qf_qq(W_p1, Mp_pk, [], half5, False)
        gp = [p_vecs_1[i] for i, q in enumerate(q_p1) if q <= half5]

        gc_s0 = []
        gc_c0 = []
        off = k
        for L in cl:
            Mcp = [[MAp[off + r][off + c] for c in range(L)] for r in range(L)]
            V = cyc_bal[L]
            _, qs = filter_colspace_and_qf_qq([[Fraction(x) for x in v] for v in V], Mcp, [], half9, False)
            gc_s0.append([V[i] for i, q in enumerate(qs) if q <= half5])
            gc_c0.append([(V[i], q) for i, q in enumerate(qs) if q <= half9])
            off += L

        s0_list = []
        for pv in gp:
            for c_tup in itertools.product(*gc_s0):
                s0 = tuple(list(pv) + [x for c_v in c_tup for x in c_v])
                s0_f = [Fraction(x) for x in s0]
                if dot_qq(s0_f, [sum(MAp[r][c] * s0_f[c] for c in range(15)) for r in range(15)]) <= half5:
                    s0_list.append(s0)

        if not s0_list:
            cfg_stats[f"P{k}_{cl}"] = {"status": "KILLED", "method": "0_z0_vectors"}
            continue
        reps = _sym_reps_s0_s2(s0_list, k, cl)

        # Build cands_by_pksum for C0 and A1
        pk_all = [tuple(x) for x in itertools.product((1, -1), repeat=k)]
        _, pk_q = filter_colspace_and_qf_qq([[Fraction(x) for x in v] for v in pk_all], Mp_pk, [], half9, False)
        pk_by_sum: Dict[int, List[Tuple[Tuple[int, ...], Fraction]]] = {sv: [] for sv in (-3, -1, 1, 3)}
        for pv, pq in zip(pk_all, pk_q):
            sv = sum(pv)
            if sv in pk_by_sum and pq <= half9:
                pk_by_sum[sv].append((pv, pq))
        cands_by_pksum: Dict[int, List[Tuple[int, ...]]] = {}
        min_qs_c = [min((q for _, q in cl_list), default=Fraction(0)) for cl_list in gc_c0]
        for sv, plist in pk_by_sum.items():
            ov = []
            for pv, pq0 in plist:
                def cre(ci, cqs, cvl):
                    if ci == len(cl):
                        if pq0 + cqs <= half9:
                            ov.append(tuple(list(pv) + cvl))
                        return
                    rm = sum(min_qs_c[ci + 1:], Fraction(0))
                    for cv_v, cq_v in gc_c0[ci]:
                        if pq0 + cqs + cq_v + rm <= half9:
                            cre(ci + 1, cqs + cq_v, cvl + list(cv_v))
                cre(0, Fraction(0), [])
            cands_by_pksum[sv] = ov

        vz1 = [Fraction(-2 if i == 0 else 0) for i in range(15)] + [Fraction(-1, 2)]
        vz2 = [Fraction(-2 if i == k - 1 else 0) for i in range(15)] + [Fraction(-1, 2)]
        vz1_sgn = [-1 if i == 0 else 1 for i in range(15)]
        vz2_sgn = [-1 if i == k - 1 else 1 for i in range(15)]

        rep_logs = []
        for ri, (s0, full_perms) in enumerate(reps):
            M18 = [[Fraction(0)] * 18 for _ in range(18)]
            for r in range(15):
                for c in range(15):
                    M18[r][c] = MA[r][c]
                M18[r][15] = M18[15][r] = Fraction(s0[r])
            M18[15][15] = half5
            for r in range(16):
                M18[r][16] = M18[16][r] = vz1[r]
                M18[r][17] = M18[17][r] = vz2[r]
            M18[16][16] = M18[17][17] = half5
            M18[16][17] = M18[17][16] = Fraction(-1, 2)

            ok18, r18 = check_psd_0_20_rank_qq(M18)
            if not ok18 or r18 > 15:
                rep_logs.append(f"rep{ri}:M18_FAIL(ok={ok18},r={r18})")
                continue

            Mp18, _, _ = pinv_qq(M18)
            nb18 = nullspace_qq(M18)
            W_mat18 = make_20M_minus_M2_qq(M18)
            psd_tests = untrusted_psd_test_vectors(M18, W_mat18, scale=250)

            # Build C0 & A1 in exact Fraction
            c0_W, c0_cv, c0_sz0, c0_sz1, c0_sz2 = [], [], [], [], []
            for sz0, sz1, sz2 in itertools.product((1, -1), repeat=3):
                Vs = cands_by_pksum.get(-(sz1 + sz2 - 1), [])
                tail = [Fraction(sz0) - Fraction(1, 2), Fraction(sz1) - Fraction(1, 2), Fraction(sz2) - Fraction(1, 2)]
                for v in Vs:
                    c0_W.append([Fraction(x) for x in v] + tail)
                    c0_cv.append(v)
                    c0_sz0.append(sz0)
                    c0_sz1.append(sz1)
                    c0_sz2.append(sz2)
            c0_idx, c0_q = filter_colspace_and_qf_qq(c0_W, Mp18, nb18, half9, r18 == 15)

            a1_W, a1_cv, a1_sz0, a1_sz1, a1_sz2 = [], [], [], [], []
            for sz0, sz1, sz2 in itertools.product((1, -1), repeat=3):
                Vs = cands_by_pksum.get(1 - sz1 - sz2, [])
                tail = [Fraction(sz0 - 1), Fraction(sz1), Fraction(sz2 - 1)]
                for v in Vs:
                    a1_W.append([Fraction(x) for x in v] + tail)
                    a1_cv.append(v)
                    a1_sz0.append(sz0)
                    a1_sz1.append(sz1)
                    a1_sz2.append(sz2)
            a1_idx, a1_q = filter_colspace_and_qf_qq(a1_W, Mp18, nb18, four, r18 == 15)

            if len(c0_idx) < 25 or len(a1_idx) < 15:
                rep_logs.append(f"rep{ri}(r={r18}):COUNT_FAIL(|c0|={len(c0_idx)},|a1|={len(a1_idx)})")
                continue

            req_c0_rowsum = [2 - s0[w] - vz1_sgn[w] - vz2_sgn[w] for w in range(15)]
            req_a1_rowsum = [3 - 2 * degs_A0[w] - s0[w] + vz1_sgn[w] for w in range(15)]
            stab = [perm for perm in full_perms if tuple(s0[p] for p in perm) == s0 and (k == 1 or perm[0] == 0)]

            W_c0_ok = [c0_W[i] for i in c0_idx]
            res_c0_ok = [half9 - q for q in c0_q]
            cv_c0_ok = [c0_cv[i] for i in c0_idx]
            sz0_c0_ok = [c0_sz0[i] for i in c0_idx]
            sz1_c0_ok = [c0_sz1[i] for i in c0_idx]
            sz2_c0_ok = [c0_sz2[i] for i in c0_idx]
            rn_c0_ok = [(15 + sz0_c0_ok[i] + sz1_c0_ok[i] + sz2_c0_ok[i]) // 2 for i in range(len(c0_idx))]

            if r18 in (14, 15):
                # Build exact 1D/0D signed C0 & A1 states + full coupled degree peel & CP-SAT!
                cW, cr, cs, ccv, c0z, c1z, c2z, crn = [], [], [], [], [], [], [], []
                for idx_p in range(len(c0_idx)):
                    rv = res_c0_ok[idx_p]
                    for sgn in ((1, -1) if (r18 == 14 and rv > 0) else (1,)):
                        cW.append(W_c0_ok[idx_p]); cr.append(rv); cs.append(sgn)
                        ccv.append(cv_c0_ok[idx_p]); c0z.append(sz0_c0_ok[idx_p]); c1z.append(sz1_c0_ok[idx_p]); c2z.append(sz2_c0_ok[idx_p]); crn.append(rn_c0_ok[idx_p])
                bW, br, bs, bcv, b0z, b2z, bdm2 = [], [], [], [], [], [], []
                for k_i, q_v in zip(a1_idx, a1_q):
                    rv = four - q_v
                    assert rv <= Fraction(2), f"A1 residual > 2 unexpectedly: {rv}"
                    dm2 = (1 if a1_sz0[k_i] == 1 else 0) + (1 if a1_sz2[k_i] == 1 else 0)
                    for sgn in ((1, -1) if (r18 == 14 and rv > 0) else (1,)):
                        bW.append(a1_W[k_i]); br.append(rv); bs.append(sgn)
                        bcv.append(a1_cv[k_i]); b0z.append(a1_sz0[k_i]); b2z.append(a1_sz2[k_i]); bdm2.append(dm2)

                cpos = exact_compat_from_gram_zz(cW, Mp18, cW, cr, cs, cr, cs, [(1, 2)])
                cneg = exact_compat_from_gram_zz(cW, Mp18, cW, cr, cs, cr, cs, [(-3, 2)])
                np.fill_diagonal(cpos, False); np.fill_diagonal(cneg, False)
                cadj = cpos | cneg
                b0 = exact_compat_from_gram_zz(bW, Mp18, bW, br, bs, br, bs, [(0, 1)])
                bm2 = exact_compat_from_gram_zz(bW, Mp18, bW, br, bs, br, bs, [(-2, 1)])
                np.fill_diagonal(b0, False); np.fill_diagonal(bm2, False)
                badj = b0 | bm2
                cb_ok = exact_compat_from_gram_zz(cW, Mp18, bW, cr, cs, br, bs, [(1, 1), (-1, 1)])

                crn_arr = np.array(crn, dtype=int)
                bdm2_arr = np.array(bdm2, dtype=int)
                al_c = np.ones(len(cr), dtype=bool)
                al_b = np.ones(len(br), dtype=bool)
                for _ in range(25):
                    na = al_c & (cneg[:, al_c].sum(axis=1) >= crn_arr) & (cpos[:, al_c].sum(axis=1) >= 24 - crn_arr) & (cb_ok[:, al_b].sum(axis=1) >= 15)
                    nb = al_b & (bm2[:, al_b].sum(axis=1) >= bdm2_arr) & (b0[:, al_b].sum(axis=1) >= 14 - bdm2_arr) & (cb_ok[al_c, :].sum(axis=0) >= 25)
                    if np.array_equal(na, al_c) and np.array_equal(nb, al_b):
                        break
                    al_c, al_b = na, nb
                ic = [i for i in range(len(cr)) if al_c[i]]
                ib = [i for i in range(len(br)) if al_b[i]]
                if len(ic) < 25 or len(ib) < 15 or sum(1 for i in ic if c0z[i] == 1) < 18 or sum(1 for i in ic if c0z[i] == -1) < 7:
                    rep_logs.append(f"rep{ri}(r={r18}):PEEL_DEAD(|c|={len(ic)},|b|={len(ib)})")
                    continue

                # 1. Fast A1-alone CP-SAT (tiny, zero n0*n1 clauses)
                ma1 = cp_model.CpModel()
                n0, n1 = len(ic), len(ib)
                xa = [ma1.NewBoolVar(f"a{i}") for i in range(n1)]
                ma1.Add(sum(xa) == 15)
                ma1.Add(sum(xa[i] for i in range(n1) if b0z[ib[i]] == -1) == 1)
                ma1.Add(sum(xa[i] for i in range(n1) if b2z[ib[i]] == -1) == 1)
                for w in range(15):
                    ma1.Add(sum(bcv[ib[i]][w] * xa[i] for i in range(n1)) == req_a1_rowsum[w])
                ib_arr = np.array(ib, dtype=int)
                badj_s = badj[np.ix_(ib_arr, ib_arr)]; bm2_s = bm2[np.ix_(ib_arr, ib_arr)]
                for a in range(n1):
                    for b in range(a + 1, n1):
                        if not badj_s[a, b]:
                            ma1.Add(xa[a] + xa[b] <= 1)
                    nbs = [xa[b] for b in range(n1) if b != a and bm2_s[a, b]]
                    ma1.Add(sum(nbs) >= bdm2[ib[a]] - 15 * (1 - xa[a]))
                    ma1.Add(sum(nbs) <= bdm2[ib[a]] + 15 * (1 - xa[a]))
                add_exact_trace_ub(ma1, xa, [br[i] for i in ib], Fraction(20) * (15 - r18))
                add_exact_psd_test_ubs(ma1, xa, [bW[i] for i in ib], psd_tests)
                sva = cp_model.CpSolver(); sva.parameters.max_time_in_seconds = 5.0; sva.parameters.num_search_workers = 4
                sta = sva.Solve(ma1)
                if sta == cp_model.INFEASIBLE:
                    rep_logs.append(f"rep{ri}(r={r18}):A1_INFEASIBLE({sva.WallTime():.2f}s,|b|={n1})")
                    print(f"    [S2 (P_{k},{cl}) rep {ri}] -> {rep_logs[-1]}", flush=True)
                    continue

                # 2. Fast C0-alone CP-SAT when small (zero n0*n1 clauses)
                if r18 == 15 or n0 <= 400:
                    mc = cp_model.CpModel()
                    xc = [mc.NewBoolVar(f"c{i}") for i in range(n0)]
                    mc.Add(sum(xc) == 25)
                    mc.Add(sum(xc[i] for i in range(n0) if c0z[ic[i]] == 1) == 18)
                    mc.Add(sum(xc[i] for i in range(n0) if c1z[ic[i]] == 1) == 18)
                    mc.Add(sum(xc[i] for i in range(n0) if c2z[ic[i]] == 1) == 18)
                    for w in range(15):
                        mc.Add(sum(ccv[ic[i]][w] * xc[i] for i in range(n0)) == req_c0_rowsum[w])
                    ic_arr = np.array(ic, dtype=int)
                    cadj_s = cadj[np.ix_(ic_arr, ic_arr)]; cneg_s = cneg[np.ix_(ic_arr, ic_arr)]
                    for a in range(n0):
                        for b in range(a + 1, n0):
                            if not cadj_s[a, b]:
                                mc.Add(xc[a] + xc[b] <= 1)
                        nbs = [xc[b] for b in range(n0) if b != a and cneg_s[a, b]]
                        mc.Add(sum(nbs) >= crn[ic[a]] - 25 * (1 - xc[a]))
                        mc.Add(sum(nbs) <= crn[ic[a]] + 25 * (1 - xc[a]))
                    add_exact_trace_ub(mc, xc, [cr[i] for i in ic], Fraction(20) * (15 - r18))
                    add_exact_psd_test_ubs(mc, xc, [cW[i] for i in ic], psd_tests)
                    svc = cp_model.CpSolver(); svc.parameters.max_time_in_seconds = 10.0; svc.parameters.num_search_workers = 4
                    stc = svc.Solve(mc)
                    if stc == cp_model.INFEASIBLE:
                        rep_logs.append(f"rep{ri}(r={r18}):C0_INFEASIBLE({svc.WallTime():.2f}s,|c|={n0})")
                        print(f"    [S2 (P_{k},{cl}) rep {ri}] -> {rep_logs[-1]}", flush=True)
                        continue
                # Fallback: split Case 0 + Case 1 symmetry-broken C0 orbits if coupled timed out
            else:
                pass

            # r18 == 13 (or fallback): exact QQ Case 0 + Case 1 (with O(2) rotation for r18==13)
            W_arr, Dw = _mat_qq_to_scaled_arr(W_c0_ok)
            Mp_arr, Dm = _mat_qq_to_scaled_arr(Mp18)
            D_g = Dw * Dw * Dm
            Dr = lcm_list([r.denominator for r in res_c0_ok if r != 0] or [1])
            rn_nums = [int(r * Dr) for r in res_c0_ok]
            G_num = (W_arr.astype(np.int64) @ Mp_arr.astype(np.int64) @ W_arr.astype(np.int64).T) if (18 * 18 * int(np.max(np.abs(W_arr))) ** 2 * int(np.max(np.abs(Mp_arr))) < 2**61) else (W_arr @ Mp_arr @ W_arr.T)
            rn_vec = np.array(rn_nums, dtype=np.int64 if isinstance(G_num.flat[0], np.int64) else object)
            rprod = rn_vec[:, None] * rn_vec[None, :]
            Dr2 = Dr * Dr
            d_p = 1 * D_g - 2 * G_num
            d_m = (-3) * D_g - 2 * G_num
            can_pos = (d_p * d_p) * Dr2 <= rprod * (4 * D_g * D_g)
            can_neg = (d_m * d_m) * Dr2 <= rprod * (4 * D_g * D_g)
            self_pos = np.diag(can_pos).copy()
            self_neg = np.diag(can_neg).copy()
            extra_cap = np.array(
                [(int(Fraction(4) / (Fraction(4) - r)) - 1) if r < 4 else 24 for r in res_c0_ok],
                dtype=int,
            )
            extra_pos = self_pos.astype(int) * extra_cap
            extra_neg = self_neg.astype(int) * extra_cap
            np.fill_diagonal(can_pos, False); np.fill_diagonal(can_neg, False)
            adj_c = can_pos | can_neg
            rn_arr = np.array(rn_c0_ok, dtype=int)
            al = np.ones(len(W_c0_ok), dtype=bool)
            for _ in range(20):
                nal = (
                    al
                    & (can_neg[:, al].sum(axis=1) + extra_neg >= rn_arr)
                    & (can_pos[:, al].sum(axis=1) + extra_pos >= 24 - rn_arr)
                )
                if np.array_equal(nal, al):
                    break
                al = nal
            ia = [i for i in range(len(W_c0_ok)) if al[i]]
            z_ia = [i for i in ia if res_c0_ok[i] == 0]
            if len(z_ia) >= 25:
                d0, m0 = _solve_s2_c0_1d_exact(
                    [W_c0_ok[i] for i in z_ia], Mp18, [Fraction(0)] * len(z_ia), [1] * len(z_ia),
                    [cv_c0_ok[i] for i in z_ia], [sz0_c0_ok[i] for i in z_ia], [sz1_c0_ok[i] for i in z_ia], [sz2_c0_ok[i] for i in z_ia],
                    [rn_c0_ok[i] for i in z_ia], req_c0_rowsum, psd_tests, Fraction(20) * (15 - r18),
                    None, True, stab, label=f"S2_P{k}_{cl}_r{ri}_Case0"
                )
                assert d0, m0

            orbs: Dict[tuple, List[int]] = {}
            for i in ia:
                if res_c0_ok[i] == 0:
                    continue
                tv = cv_c0_ok[i]
                can = min((tuple(tv[p] for p in perm), sz0_c0_ok[i], sz1_c0_ok[i], sz2_c0_ok[i]) for perm in stab)
                orbs.setdefault(can, []).append(i)
            orb_reps = sorted([lst[0] for lst in orbs.values()], key=lambda idx: -res_c0_ok[idx])
            for oi, s0_i in enumerate(orb_reps):
                r0 = res_c0_ok[s0_i]
                tv0 = cv_c0_ok[s0_i]
                stab_s0 = [perm for perm in stab if tuple(tv0[p] for p in perm) == tv0]
                if r18 == 14:
                    M_rot = Mp18
                    W_sub = [W_c0_ok[s0_i]]
                    r_sub, res_orig_s, s_sub = [r0], [r0], [1]
                    cv_sub, z0_s, z1_s, z2_s, rn_s = [cv_c0_ok[s0_i]], [sz0_c0_ok[s0_i]], [sz1_c0_ok[s0_i]], [sz2_c0_ok[s0_i]], [rn_c0_ok[s0_i]]
                    for j in ia:
                        if res_c0_ok[j] > r0:
                            continue
                        if j == s0_i:
                            if not (self_pos[s0_i] or self_neg[s0_i]):
                                continue
                        elif not adj_c[s0_i, j]:
                            continue
                        g0 = Fraction(int(G_num[s0_i, j]), D_g)
                        rj = res_c0_ok[j]
                        for sj in ((1, -1) if rj > 0 else (1,)):
                            if j == s0_i and sj == 1:
                                continue
                            if any((rj == 0 and Fraction(p, q) == g0) or (rj > 0 and sj * (Fraction(p, q) - g0) > 0 and (Fraction(p, q) - g0) ** 2 == r0 * rj) for p, q in ((1, 2), (-3, 2))):
                                W_sub.append(W_c0_ok[j]); r_sub.append(rj); res_orig_s.append(rj); s_sub.append(sj)
                                cv_sub.append(cv_c0_ok[j]); z0_s.append(sz0_c0_ok[j]); z1_s.append(sz1_c0_ok[j]); z2_s.append(sz2_c0_ok[j]); rn_s.append(rn_c0_ok[j])
                else:
                    M_rot = [list(row) + [Fraction(0)] for row in Mp18] + [[Fraction(0)] * 18 + [Fraction(1) / r0]]
                    W_sub = [list(W_c0_ok[s0_i]) + [r0]]
                    r_sub, res_orig_s, s_sub = [Fraction(0)], [r0], [1]
                    cv_sub, z0_s, z1_s, z2_s, rn_s = [cv_c0_ok[s0_i]], [sz0_c0_ok[s0_i]], [sz1_c0_ok[s0_i]], [sz2_c0_ok[s0_i]], [rn_c0_ok[s0_i]]
                    for j in ia:
                        if res_c0_ok[j] > r0:
                            continue
                        if j == s0_i:
                            if not (self_pos[s0_i] or self_neg[s0_i]):
                                continue
                            tgts = ([Fraction(1, 2)] if self_pos[s0_i] else []) + ([Fraction(-3, 2)] if self_neg[s0_i] else [])
                        else:
                            if not adj_c[s0_i, j]:
                                continue
                            tgts = ([Fraction(1, 2)] if can_pos[s0_i, j] else []) + ([Fraction(-3, 2)] if can_neg[s0_i, j] else [])
                        g0 = Fraction(int(G_num[s0_i, j]), D_g)
                        rj = res_c0_ok[j]
                        for tgt in tgts:
                            beta = tgt - g0
                            rem = rj - (beta * beta) / r0
                            if rem < 0:
                                continue
                            for sj in ((1, -1) if rem > 0 else (1,)):
                                W_sub.append(list(W_c0_ok[j]) + [beta]); r_sub.append(rem); res_orig_s.append(rj); s_sub.append(sj)
                                cv_sub.append(cv_c0_ok[j]); z0_s.append(sz0_c0_ok[j]); z1_s.append(sz1_c0_ok[j]); z2_s.append(sz2_c0_ok[j]); rn_s.append(rn_c0_ok[j])
                dead, msg = _solve_s2_c0_1d_exact(
                    W_sub, M_rot, r_sub, s_sub, cv_sub, z0_s, z1_s, z2_s, rn_s,
                    req_c0_rowsum, psd_tests, Fraction(20) * (15 - r18), [0], (r18 == 13), stab_s0,
                    W_c0_ok[s0_i], Mp18, label=f"S2_P{k}_{cl}_r{ri}_o{oi}", trace_items_qq=res_orig_s
                )
                assert dead, msg
            rep_logs.append(f"rep{ri}(r={r18}):ALL_{len(orb_reps)}_ORBS_DEAD")

        cfg_stats[f"P{k}_{cl}"] = {"status": "KILLED", "reps": rep_logs}
        print(f"  [S2] (P_{k},{cl}): {len(reps)} reps CERTIFIED KILLED", flush=True)

    return {"top_reduction": top_check, "configs": cfg_stats}


def run(save_certs: bool = True) -> dict:
    t_start = time.time()
    print("=== Certifying S3 = (26, 42, 6, 0) (zero float trust) ===", flush=True)
    reps, u, blk = enumerate_s3_10_orbits()
    s3_ext0 = certify_s3_extneg0(reps, u, blk)
    s3_ext20 = certify_s3_extneg2_and_0(reps, u, blk)
    print("\n=== Certifying S2 = (25, 45, 3, 1) (zero float trust) ===", flush=True)
    s2_res = certify_s2()
    elapsed = round(time.time() - t_start, 2)
    payload = {
        "module": "certify_s3_s2",
        "all_dead": True,
        "stats": {"S3": {**s3_ext0, **s3_ext20}, "S2": s2_res},
        "elapsed_sec": elapsed,
    }
    if save_certs:
        res_dir = Path(__file__).resolve().parent / "results"
        res_dir.mkdir(parents=True, exist_ok=True)
        out_path = res_dir / "cert_s3_s2.json"
        out_path.write_text(json.dumps(payload, indent=2))
        print(f"\nALL S3 & S2 CASES CERTIFIED KILLED in {elapsed:.2f}s -> {out_path}", flush=True)
    return payload


if __name__ == "__main__":
    run(save_certs=True)
