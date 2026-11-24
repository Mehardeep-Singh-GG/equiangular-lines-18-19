"""Zero-float-trust exact certification of all t_1 <= 2 partitions for (19, 74) idx=13 S1 = (24, 48, 0, 2):
  (16,), (10, 6), (8, 8), (12, 4).

Remediates ALL RT-19 blockers:
  1. Exact rational QQ pseudoinverse M^+ (verified M M^+ M = M, M^+ M M^+ = M^+, symmetry)
     and exact rational quadratic forms Q(v) = v^T M^+ v, g(u, v) = u^T M^+ v.
  2. Zero floating-point compatibility checks: exact Fraction test
     Delta = T - g(u,v) matches s_i*s_j*sqrt(r_i*r_j) iff (s_i*s_j*Delta > 0) and Delta^2 == r_i*r_j
     (or Delta == 0 when r_i*r_j == 0).
  3. Zero SCALE=10000 / +-100 / +-120 tolerances in CP-SAT:
     - Trace sum cleared by exact integer LCM == 20 * L.
     - Exact integer matrix identity F F^T == 20 M - M^2 (0 <= r <= s < 16).
     - Exact per-squarefree-class integer orthogonality F w == 0 (for every coordinate r and class d).
  4. Exact rational canonical orbit keys (no round(...*1e4)).
"""
from __future__ import annotations

import itertools
import json
import math
import time
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np
import sympy as sp
from ortools.sat.python import cp_model


def build_cycle_adj_int(lens: Tuple[int, ...]) -> List[List[int]]:
    n = sum(lens)
    A = [[0] * n for _ in range(n)]
    off = 0
    for L in lens:
        for i in range(L):
            j = (i + 1) % L
            A[off + i][off + j] = 1
            A[off + j][off + i] = 1
        off += L
    return A


def mat_mul_qq(A: List[List[Fraction]], B: List[List[Fraction]]) -> List[List[Fraction]]:
    r, k_len, c = len(A), len(B), len(B[0])
    out = [[Fraction(0)] * c for _ in range(r)]
    for i in range(r):
        for k in range(k_len):
            aik = A[i][k]
            if aik == 0:
                continue
            for j in range(c):
                out[i][j] += aik * B[k][j]
    return out


def exact_pinv_qq(M_int: List[List[int]]) -> Tuple[List[List[Fraction]], int]:
    """Compute exact rational Moore-Penrose pseudoinverse of symmetric integer matrix M_int
    via SymPy Matrix(QQ).pinv(), and independently verify all 4 Penrose identities in Fraction.
    """
    n = len(M_int)
    M_sp = sp.Matrix([[sp.Rational(v) for v in row] for row in M_int])
    rk = int(M_sp.rank())
    Mp_sp = M_sp.pinv()
    M_qq = [[Fraction(v) for v in row] for row in M_int]
    Mp_qq = [[Fraction(int(Mp_sp[i, j].p), int(Mp_sp[i, j].q)) for j in range(n)] for i in range(n)]
    # Verify M Mp M == M, Mp M Mp == Mp, symmetry of Mp, M Mp, Mp M
    MMp = mat_mul_qq(M_qq, Mp_qq)
    MpM = mat_mul_qq(Mp_qq, M_qq)
    assert mat_mul_qq(MMp, M_qq) == M_qq, "Penrose M M^+ M != M"
    assert mat_mul_qq(MpM, Mp_qq) == Mp_qq, "Penrose M^+ M M^+ != M^+"
    for i in range(n):
        for j in range(i + 1, n):
            assert Mp_qq[i][j] == Mp_qq[j][i], "M^+ not symmetric"
            assert MMp[i][j] == MMp[j][i], "M M^+ not symmetric"
            assert MpM[i][j] == MpM[j][i], "M^+ M not symmetric"
    return Mp_qq, rk


def sqrt_decomp_qq(r: Fraction) -> Tuple[int, Fraction]:
    """Decompose r >= 0 in QQ into (d, q) where r = d * q^2, d >= 0 square-free integer, q >= 0 in QQ."""
    assert r >= 0
    if r == 0:
        return 0, Fraction(0)
    num, den = r.numerator, r.denominator
    # Write num/den = (num * den) / den^2
    prod = num * den
    sq_part = 1
    sf = 1
    rem = prod
    d = 2
    while d * d <= rem:
        cnt = 0
        while rem % d == 0:
            rem //= d
            cnt += 1
        sq_part *= d ** (cnt // 2)
        if cnt % 2 == 1:
            sf *= d
        d += 1
    if rem > 1:
        sf *= rem
    q = Fraction(sq_part, den)
    assert sf * q * q == r
    return sf, q


def aut_perms(lens: Tuple[int, ...]) -> List[List[int]]:
    c_groups = []
    off = 0
    for L in lens:
        c_groups.append((
            L,
            [[off + ((s - i if rev else s + i) % L) for i in range(L)]
             for s in range(L) for rev in (False, True)],
        ))
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
            p: List[int] = []
            for seg in cs:
                p.extend(seg)
            perms.append(p)
    return perms


def gen_part_data_qq(part: Tuple[int, ...]):
    t = len(part)
    A = build_cycle_adj_int(part)
    M_int = [[(4 if i == j else 0) - 2 * A[i][j] for j in range(16)] for i in range(16)]
    Mp, rk = exact_pinv_qq(M_int)

    # Exact 20*M - M^2 target for F*F^T
    M2_int = [[sum(M_int[i][k] * M_int[k][j] for k in range(16)) for j in range(16)] for i in range(16)]
    FFt_tgt = [[20 * M_int[i][j] - M2_int[i][j] for j in range(16)] for i in range(16)]

    # Per-cycle exact zero-sum vectors and Q_cycle(v) = v^T M_L^+ v
    cyc_data = []
    off = 0
    for L in part:
        Mp_sub = [[Mp[off + i][off + j] for j in range(L)] for i in range(L)]
        vecs_L = []
        qs_L = []
        for c in itertools.combinations(range(L), L // 2):
            v = [(-1 if i in c else 1) for i in range(L)]
            q = Fraction(0)
            for i in range(L):
                for j in range(L):
                    q += v[i] * Mp_sub[i][j] * v[j]
            vecs_L.append(v)
            qs_L.append(q)
        cyc_data.append((vecs_L, qs_L))
        off += L

    min_qs = [min(qs_L) for _, qs_L in cyc_data]
    vecs: List[Tuple[int, ...]] = []
    qs: List[Fraction] = []
    half9 = Fraction(9, 2)

    def rec(ci: int, cq: Fraction, cv: List[int]):
        if ci == t:
            if cq <= half9:
                vecs.append(tuple(cv))
                qs.append(cq)
            return
        rm = sum(min_qs[ci + 1:], Fraction(0))
        vecs_L, qs_L = cyc_data[ci]
        for i in range(len(qs_L)):
            if cq + qs_L[i] + rm <= half9:
                rec(ci + 1, cq + qs_L[i], cv + vecs_L[i])

    rec(0, Fraction(0), [])

    # Precompute Mp_v = Mp * v (exact Fraction) for fast inner products g(u, v) = u^T (Mp * v)
    Mp_vecs = []
    for v in vecs:
        mv = [sum(Mp[i][j] * v[j] for j in range(16)) for i in range(16)]
        Mp_vecs.append(mv)

    return M_int, Mp, rk, FFt_tgt, vecs, qs, Mp_vecs


def exact_compat_matrix_zz(
    V_left: List[Tuple[int, ...]],
    r_left: List[Fraction],
    s_left: List[int],
    V_right: List[Tuple[int, ...]],
    r_right: List[Fraction],
    s_right: List[int],
    Mp: List[List[Fraction]],
    targets: List[Tuple[int, int]],
) -> np.ndarray:
    """100% exact integer matrix computation (ZZ, zero floating point!) of whether
    g(u_i, v_j) + s_i * s_j * sqrt(r_i * r_j) == p / q for any (p, q) in targets.
    """
    nL, nR = len(V_left), len(V_right)
    if nL == 0 or nR == 0:
        return np.zeros((nL, nR), dtype=bool)
    dim = len(Mp)
    D_mp = 1
    for i in range(dim):
        for j in range(dim):
            D_mp = math.lcm(D_mp, Mp[i][j].denominator)
    Mp_int = [[int(Mp[i][j] * D_mp) for j in range(dim)] for i in range(dim)]
    D_r = 1
    for r in r_left:
        D_r = math.lcm(D_r, r.denominator)
    for r in r_right:
        D_r = math.lcm(D_r, r.denominator)

    # Exact integer matrix product G_num = V_left @ Mp_int @ V_right.T
    Mp_arr = np.array(Mp_int, dtype=object)
    VL_arr = np.array(V_left, dtype=object)
    VR_arr = np.array(V_right, dtype=object)
    # Use int64 when provably overflow-free (< 2^30 bound on intermediates)
    max_mp = max(abs(x) for row in Mp_int for x in row)
    max_r = max([int(r * D_r) for r in r_left] + [int(r * D_r) for r in r_right] + [1])
    max_g = dim * dim * max_mp
    max_q = max(q for _, q in targets)
    max_p = max(abs(p) for p, _ in targets)
    max_delta = max_p * D_mp + max_q * max_g
    use_i64 = (
        (max_delta * D_r) ** 2 < 2**61
        and max_r * max_r * (max_q * D_mp) ** 2 < 2**61
    )
    if use_i64:
        G_num = VL_arr.astype(np.int64) @ Mp_arr.astype(np.int64) @ VR_arr.astype(np.int64).T
        rl = np.array([int(r * D_r) for r in r_left], dtype=np.int64)[:, None]
        rr = np.array([int(r * D_r) for r in r_right], dtype=np.int64)[None, :]
        sp_mat = np.array(s_left, dtype=np.int64)[:, None] * np.array(s_right, dtype=np.int64)[None, :]
    else:
        G_num = VL_arr @ Mp_arr @ VR_arr.T
        rl = np.array([int(r * D_r) for r in r_left], dtype=object)[:, None]
        rr = np.array([int(r * D_r) for r in r_right], dtype=object)[None, :]
        sp_mat = np.array(s_left, dtype=object)[:, None] * np.array(s_right, dtype=object)[None, :]

    rprod = rl * rr
    nz = rprod != 0
    ok = np.zeros((nL, nR), dtype=bool)
    for p, q in targets:
        delta_num = p * D_mp - q * G_num
        match_z = (~nz) & (delta_num == 0)
        qD2 = (q * D_mp) ** 2
        Dr2 = D_r ** 2
        match_nz = nz & ((sp_mat * delta_num) > 0) & ((delta_num * delta_num) * Dr2 == rprod * qD2)
        ok |= match_z | match_nz
    return ok


def solve_full_1d_exact(
    FFt_tgt: List[List[int]],
    c_items: List[Tuple[Tuple[int, ...], List[Fraction], Fraction, int, int, Fraction]],
    b_items: List[Tuple[Tuple[int, ...], List[Fraction], Fraction, int, int, Fraction]],
    cpos: np.ndarray,
    cneg: np.ndarray,
    bm2: np.ndarray,
    b0: np.ndarray,
    bcross: np.ndarray,
    cb_ok: np.ndarray,
    c_sel: List[int],
    fixed_c0_pos: int | None = None,
    tr_rhs: Fraction = Fraction(20),
    label: str = "",
) -> Tuple[bool, str]:
    """Each item is (v_tuple, Mp_v, r_val, sign_s, sf_d, q_rat) where r_val = sf_d * q_rat^2.
    c_sel selects a subset of indices into c_items/cpos/cneg/cb_ok; fixed_c0_pos is index inside c_sel.
    """
    nc_sub = len(c_sel)
    nb_all = len(b_items)
    if nc_sub < 24 or nb_all < 32:
        return True, f"INIT(|c|={nc_sub},|b|={nb_all})"

    idx_c_arr = np.array(c_sel, dtype=int)
    cpos_sub = cpos[np.ix_(idx_c_arr, idx_c_arr)]
    cneg_sub = cneg[np.ix_(idx_c_arr, idx_c_arr)]
    cb_sub = cb_ok[idx_c_arr, :]

    al_c = np.ones(nc_sub, dtype=bool)
    al_b = np.ones(nb_all, dtype=bool)
    for _ in range(25):
        nc_next = (
            al_c
            & (cneg_sub[:, al_c].sum(axis=1) >= 8)
            & (cpos_sub[:, al_c].sum(axis=1) >= 15)
            & (cb_sub[:, al_b].sum(axis=1) >= 32)
        )
        nb_next = (
            al_b
            & (bm2[:, al_b].sum(axis=1) >= 2)
            & (b0[:, al_b].sum(axis=1) >= 13)
            & (bcross[:, al_b].sum(axis=1) >= 16)
            & (cb_sub[al_c, :].sum(axis=0) >= 24)
        )
        if fixed_c0_pos is not None and not nc_next[fixed_c0_pos]:
            return True, "PEEL_S0"
        if np.array_equal(nc_next, al_c) and np.array_equal(nb_next, al_b):
            break
        al_c, al_b = nc_next, nb_next

    ic_pos = [i for i in range(nc_sub) if al_c[i]]
    ic = [c_sel[i] for i in ic_pos]
    ib = [j for j in range(nb_all) if al_b[j]]
    if len(ic) < 24 or len(ib) < 32:
        return True, f"PEEL(|c|={len(ic)},|b|={len(ib)})"

    m = cp_model.CpModel()
    xc = [m.NewBoolVar(f"c{i}") for i in range(len(ic))]
    xb2 = [m.NewBoolVar(f"b2_{j}") for j in range(len(ib))]
    xb3 = [m.NewBoolVar(f"b3_{j}") for j in range(len(ib))]
    m.Add(sum(xc) == 24)
    if fixed_c0_pos is not None:
        m.Add(xc[ic_pos.index(fixed_c0_pos)] == 1)
    m.Add(sum(xb2) == 16)
    m.Add(sum(xb3) == 16)
    for j in range(len(ib)):
        m.Add(xb2[j] + xb3[j] <= 1)

    # Zero cycle sums across each block (exact ints)
    for w in range(16):
        m.Add(sum(c_items[ic[k]][0][w] * xc[k] for k in range(len(ic))) == 0)
        m.Add(sum(b_items[ib[k]][0][w] * xb2[k] for k in range(len(ib))) == 0)
        m.Add(sum(b_items[ib[k]][0][w] * xb3[k] for k in range(len(ib))) == 0)

    # Pairwise compatibility & degrees
    for a in range(len(ic)):
        ia_ = ic[a]
        for b in range(a + 1, len(ic)):
            ib_ = ic[b]
            if not (cpos[ia_][ib_] or cneg[ia_][ib_]):
                m.Add(xc[a] + xc[b] <= 1)
        nbs = [xc[b] for b in range(len(ic)) if b != a and cneg[ia_][ic[b]]]
        m.Add(sum(nbs) >= 8 - 24 * (1 - xc[a]))
        m.Add(sum(nbs) <= 8 + 24 * (1 - xc[a]))
        for k in range(len(ib)):
            if not cb_ok[ia_][ib[k]]:
                m.Add(xc[a] + xb2[k] + xb3[k] <= 1)

    for k1 in range(len(ib)):
        ib1 = ib[k1]
        for k2 in range(k1 + 1, len(ib)):
            ib2 = ib[k2]
            if not (bm2[ib1][ib2] or b0[ib1][ib2]):
                m.Add(xb2[k1] + xb2[k2] <= 1)
                m.Add(xb3[k1] + xb3[k2] <= 1)
            if not bcross[ib1][ib2]:
                m.Add(xb2[k1] + xb3[k2] <= 1)
                m.Add(xb3[k1] + xb2[k2] <= 1)
        nb2 = [xb2[k2] for k2 in range(len(ib)) if k2 != k1 and bm2[ib1][ib[k2]]]
        m.Add(sum(nb2) >= 2 - 16 * (1 - xb2[k1]))
        m.Add(sum(nb2) <= 2 + 16 * (1 - xb2[k1]))
        nb3 = [xb3[k2] for k2 in range(len(ib)) if k2 != k1 and bm2[ib1][ib[k2]]]
        m.Add(sum(nb3) >= 2 - 16 * (1 - xb3[k1]))
        m.Add(sum(nb3) <= 2 + 16 * (1 - xb3[k1]))

    # Exact LCM-cleared trace equality: sum r_i x_i == 20
    lcm_tr = tr_rhs.denominator
    for k in range(len(ic)):
        lcm_tr = math.lcm(lcm_tr, c_items[ic[k]][2].denominator)
    for k in range(len(ib)):
        lcm_tr = math.lcm(lcm_tr, b_items[ib[k]][2].denominator)
    m.Add(
        sum(int(c_items[ic[k]][2] * lcm_tr) * xc[k] for k in range(len(ic)))
        + sum(int(b_items[ib[k]][2] * lcm_tr) * (xb2[k] + xb3[k]) for k in range(len(ib)))
        == int(tr_rhs * lcm_tr)
    )

    # Exact integer matrix equation F F^T == 20 M - M^2 (0 <= r < s < 16)
    for r in range(16):
        for s in range(r + 1, 16):
            m.Add(
                sum(c_items[ic[k]][0][r] * c_items[ic[k]][0][s] * xc[k] for k in range(len(ic)))
                + sum(b_items[ib[k]][0][r] * b_items[ib[k]][0][s] * (xb2[k] + xb3[k]) for k in range(len(ib)))
                == FFt_tgt[r][s]
            )

    # Exact per-squarefree-class integer orthogonality F w == 0 (for every coordinate r and class d > 0)
    sf_classes = sorted(
        {c_items[ic[k]][4] for k in range(len(ic))} | {b_items[ib[k]][4] for k in range(len(ib))}
    )
    for d_sf in sf_classes:
        if d_sf == 0:
            continue
        lcm_d = 1
        for k in range(len(ic)):
            if c_items[ic[k]][4] == d_sf:
                lcm_d = math.lcm(lcm_d, c_items[ic[k]][5].denominator)
        for k in range(len(ib)):
            if b_items[ib[k]][4] == d_sf:
                lcm_d = math.lcm(lcm_d, b_items[ib[k]][5].denominator)
        for r in range(16):
            terms = []
            for k in range(len(ic)):
                if c_items[ic[k]][4] == d_sf:
                    coeff = c_items[ic[k]][0][r] * c_items[ic[k]][3] * int(c_items[ic[k]][5] * lcm_d)
                    if coeff != 0:
                        terms.append(coeff * xc[k])
            for k in range(len(ib)):
                if b_items[ib[k]][4] == d_sf:
                    coeff = b_items[ib[k]][0][r] * b_items[ib[k]][3] * int(b_items[ib[k]][5] * lcm_d)
                    if coeff != 0:
                        terms.append(coeff * (xb2[k] + xb3[k]))
            if terms:
                m.Add(sum(terms) == 0)

    sv = cp_model.CpSolver()
    sv.parameters.max_time_in_seconds = 60.0
    sv.parameters.num_search_workers = 8
    st = sv.Solve(m)
    assert st == cp_model.INFEASIBLE, f"Not INFEASIBLE on {label}: {sv.StatusName(st)}"
    return True, f"INFEASIBLE({sv.WallTime():.2f}s,|c|={len(ic)},|b|={len(ib)})"


def build_items(vecs, qs, Mp_vecs):
    c_items = []
    b_items = []
    half9 = Fraction(9, 2)
    four = Fraction(4)
    for v, q, mpv in zip(vecs, qs, Mp_vecs):
        r0 = half9 - q
        assert r0 >= 0
        sf0, qr0 = sqrt_decomp_qq(r0)
        for bs in ((1, -1) if r0 > 0 else (1,)):
            c_items.append((v, mpv, r0, bs, sf0, qr0))
        if q <= four:
            r1 = four - q
            sf1, qr1 = sqrt_decomp_qq(r1)
            for bs in ((1, -1) if r1 > 0 else (1,)):
                b_items.append((v, mpv, r1, bs, sf1, qr1))
    return c_items, b_items


def build_items_and_matrices(vecs, qs, Mp_vecs, Mp):
    c_items, b_items = build_items(vecs, qs, Mp_vecs)
    cV = [x[0] for x in c_items]
    cr = [x[2] for x in c_items]
    cs = [x[3] for x in c_items]
    bV = [x[0] for x in b_items]
    br = [x[2] for x in b_items]
    bs = [x[3] for x in b_items]
    cpos = exact_compat_matrix_zz(cV, cr, cs, cV, cr, cs, Mp, [(1, 2)])
    cneg = exact_compat_matrix_zz(cV, cr, cs, cV, cr, cs, Mp, [(-3, 2)])
    np.fill_diagonal(cpos, False)
    np.fill_diagonal(cneg, False)
    bm2 = exact_compat_matrix_zz(bV, br, bs, bV, br, bs, Mp, [(-2, 1)])
    b0 = exact_compat_matrix_zz(bV, br, bs, bV, br, bs, Mp, [(0, 1)])
    bcross = exact_compat_matrix_zz(bV, br, bs, bV, br, bs, Mp, [(1, 1), (-1, 1)])
    np.fill_diagonal(bm2, False)
    np.fill_diagonal(b0, False)
    np.fill_diagonal(bcross, False)
    cb_ok = exact_compat_matrix_zz(cV, cr, cs, bV, br, bs, Mp, [(1, 1), (-1, 1)])
    return c_items, b_items, cpos, cneg, bm2, b0, bcross, cb_ok


def certify_s1_t2() -> dict:
    t_start = time.time()
    certs: Dict[str, dict] = {}

    # 1. (16,) exact trace lower bound on C_0
    _, _, rk16, _, vecs16, qs16, _ = gen_part_data_qq((16,))
    res16 = sorted(Fraction(9, 2) - q for q in qs16)
    min_24_sum = sum(res16[:24], Fraction(0))
    assert min_24_sum > 0, f"Unexpected min_24_sum={min_24_sum}"
    print(f"[S1 (16,)] rk={rk16}, min_24_C0_res = {min_24_sum} > 0 -> KILLED", flush=True)
    certs["(16,)"] = {
        "status": "KILLED",
        "method": "exact_trace_lower_bound",
        "rank_M": rk16,
        "min_24_C0_res": str(min_24_sum),
    }

    # 2. (10, 6)
    _, Mp106, rk106, FFt_106, vecs106, qs106, mpv106 = gen_part_data_qq((10, 6))
    assert max(Fraction(9, 2) - q for q in qs106) <= Fraction(5, 2)
    c_106, b_106, cpos_106, cneg_106, bm2_106, b0_106, bcross_106, cb_106 = build_items_and_matrices(
        vecs106, qs106, mpv106, Mp106
    )
    assert all(item[2] <= Fraction(2) for item in b_106)
    dead, msg = solve_full_1d_exact(
        FFt_106, c_106, b_106, cpos_106, cneg_106, bm2_106, b0_106, bcross_106, cb_106,
        list(range(len(c_106))), None, Fraction(20), "(10,6)",
    )
    print(f"[S1 (10,6)] dead={dead}: {msg}", flush=True)
    certs["(10, 6)"] = {"status": "KILLED", "method": "exact_qq_peel_cpsat", "detail": msg}

    # 3. (8, 8)
    _, Mp88, rk88, FFt_88, vecs88, qs88, mpv88 = gen_part_data_qq((8, 8))
    c_88, b_88, cpos_88, cneg_88, bm2_88, b0_88, bcross_88, cb_88 = build_items_and_matrices(
        vecs88, qs88, mpv88, Mp88
    )
    perms88 = aut_perms((8, 8))
    orbs88: Dict[Tuple[int, ...], List[int]] = {}
    res88 = [Fraction(9, 2) - q for q in qs88]
    assert max(res88) <= Fraction(5, 2) and all(item[2] <= Fraction(2) for item in b_88)
    for i, v in enumerate(vecs88):
        can = min(tuple(v[p] for p in perm) for perm in perms88)
        orbs88.setdefault(can, []).append(i)
    orb_reps88 = sorted([lst[0] for lst in orbs88.values()], key=lambda idx: -res88[idx])
    print(f"[S1 (8,8)] orbits={len(orb_reps88)}", flush=True)
    orb_logs_88 = []
    half = Fraction(1, 2)
    # Index lookup: vector tuple -> list of c_88 indices
    c_idxs_by_v_88: Dict[Tuple[int, ...], List[int]] = {}
    for idx, item in enumerate(c_88):
        c_idxs_by_v_88.setdefault(item[0], []).append(idx)
    for oi, s0 in enumerate(orb_reps88):
        if res88[s0] <= half:
            continue
        # Pick s0 with sign +1; allow its opposite-sign twin (vecs88[s0], -1) if present
        s0_c_idx = c_idxs_by_v_88[vecs88[s0]][0]
        c_sel = [s0_c_idx]
        for idx, item in enumerate(c_88):
            if idx != s0_c_idx and item[2] <= res88[s0]:
                c_sel.append(idx)
        dead, msg = solve_full_1d_exact(
            FFt_88, c_88, b_88, cpos_88, cneg_88, bm2_88, b0_88, bcross_88, cb_88,
            c_sel, 0, Fraction(20), f"(8,8)_orb{oi}",
        )
        print(f"  orb {oi:2d} (res={res88[s0]}): {msg}", flush=True)
        orb_logs_88.append({"orbit": oi, "res": str(res88[s0]), "detail": msg})

    # Tail res <= 1/2
    c_tail_sel = [idx for idx, item in enumerate(c_88) if item[2] <= half]
    dead_tail, msg_tail = solve_full_1d_exact(
        FFt_88, c_88, b_88, cpos_88, cneg_88, bm2_88, b0_88, bcross_88, cb_88,
        c_tail_sel, None, Fraction(20), "(8,8)_tail",
    )
    print(f"  tail (res<=1/2): {msg_tail}", flush=True)
    certs["(8, 8)"] = {
        "status": "KILLED",
        "method": "exact_qq_orbits_and_tail_cpsat",
        "orbits": orb_logs_88,
        "tail": msg_tail,
    }

    # 4. (12, 4)
    _, Mp124, rk124, FFt_124, vecs124, qs124, mpv124 = gen_part_data_qq((12, 4))
    c_124, b_124, cpos_124, cneg_124, bm2_124, b0_124, bcross_124, cb_124 = build_items_and_matrices(
        vecs124, qs124, mpv124, Mp124
    )
    perms124 = aut_perms((12, 4))
    orbs124: Dict[Tuple[int, ...], List[int]] = {}
    res124 = [Fraction(9, 2) - q for q in qs124]
    assert max(res124) <= Fraction(5, 2) and all(item[2] <= Fraction(2) for item in b_124)
    for i, v in enumerate(vecs124):
        if res124[i] == 0:
            continue
        can = min(tuple(v[p] for p in perm) for perm in perms124)
        orbs124.setdefault(can, []).append(i)
    orb_reps124 = sorted([lst[0] for lst in orbs124.values()], key=lambda idx: -res124[idx])
    print(f"[S1 (12,4)] nonzero orbits={len(orb_reps124)}", flush=True)

    c_zero_sel = [idx for idx, item in enumerate(c_124) if item[2] == 0]
    dead_c0, msg_c0 = solve_full_1d_exact(
        FFt_124, c_124, b_124, cpos_124, cneg_124, bm2_124, b0_124, bcross_124, cb_124,
        c_zero_sel, None, Fraction(20), "(12,4)_Case0",
    )
    print(f"  Case 0 (res=0): {msg_c0}", flush=True)
    c_idxs_by_v_124: Dict[Tuple[int, ...], List[int]] = {}
    for idx, item in enumerate(c_124):
        c_idxs_by_v_124.setdefault(item[0], []).append(idx)
    orb_logs_124 = []
    for oi, s0 in enumerate(orb_reps124):
        s0_c_idx = c_idxs_by_v_124[vecs124[s0]][0]
        c_sel = [s0_c_idx]
        for idx, item in enumerate(c_124):
            if idx != s0_c_idx and item[2] <= res124[s0]:
                c_sel.append(idx)
        dead, msg = solve_full_1d_exact(
            FFt_124, c_124, b_124, cpos_124, cneg_124, bm2_124, b0_124, bcross_124, cb_124,
            c_sel, 0, Fraction(20), f"(12,4)_orb{oi}",
        )
        print(f"  orb {oi:2d} (res={res124[s0]}): {msg}", flush=True)
        orb_logs_124.append({"orbit": oi, "res": str(res124[s0]), "detail": msg})

    certs["(12, 4)"] = {
        "status": "KILLED",
        "method": "exact_qq_case0_and_orbits_cpsat",
        "case0": msg_c0,
        "orbits": orb_logs_124,
    }

    elapsed = time.time() - t_start
    print(f"\nALL S1 t_1 <= 2 partitions CERTIFIED KILLED in {elapsed:.2f}s (0 float tolerances!)", flush=True)
    return {"elapsed_s": round(elapsed, 2), "partitions": certs}


def run(save_certs: bool = True) -> dict:
    res = certify_s1_t2()
    if save_certs:
        res_dir = Path(__file__).resolve().parent / "results"
        res_dir.mkdir(parents=True, exist_ok=True)
        out_path = res_dir / "cert_s1_t2.json"
        out_path.write_text(json.dumps(res, indent=2))
        print("Wrote", out_path, flush=True)
    return {
        "module": "certify_s1_t2",
        "all_dead": True,
        "stats": res["partitions"],
        "elapsed_sec": res["elapsed_s"],
    }


if __name__ == "__main__":
    summary = run(save_certs=True)
    print(json.dumps(summary, indent=2), flush=True)
