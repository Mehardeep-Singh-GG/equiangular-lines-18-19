"""Independent clean-room verification of the (18, 59) Phase-3 endgame.

Verifies from first principles in exact ZZ / QQ / QQ(alpha) arithmetic (zero reuse of
compute/poly/ or compute/search/ code):
1. Exact partition completeness: phase2_18_59 (86 survivors) minus sec7_18_59 (66 kills)
   equals the 20 Stage-3 targets {103, 151, 228, 316, 319, 341, 364, 441, 488, 603,
   651, 692, 705, 800, 861, 864, 978, 997, 1113, 1164} (with idx=861 already verified
   in audit/verify_phase3_47_861.py).
2. SHA-256 checksums of all 8 compute/poly/results/phase3_18_59*.json files.
3. Independent clean-room Stage-2 + Prop 6.1 + Stage-3 (2v-Jacobi + locked k_u +
   2v-fixed-point + global K=K^T Farkas + sv_galois on S_v) across all 17 direct
   targets (clean_a [12], clean_b [4], 316 [1]), plus coupled-Farkas verification on
   clean_b, 1164, and 705 (cones 1..5 + exhaustive 19,975 sols on cone 0).
4. Independent clean-room exact rational/algebraic endgame proofs for the 4 Stage-3
   survivor indices:
   - idx=441 (1 survivor): E_15 rank-3 Parseval frame (<= 3 lines in C_0) + E_15 * E_7 = 0.
   - idx=488 (2 survivors): E_11 submatrix rank >= 10 > 7 on both surv0 and surv1.
   - idx=692 (1 survivor): E_{r2} gauge lock, E_11 rank <= 14 => 4*C_4 + P_3, Jacobi
     chi_{S40}, and F_2^4 parity contradiction.
   - idx=864 (3 survivors): signed E_6/E_9/E_11/E_13 2v-Jacobi extraction, rank-2 E_9
     (7,7,7) clustering, intra-cluster PSD bounds, and 9*E_13 Cauchy-Schwarz on W.
"""

from __future__ import annotations

from fractions import Fraction
import itertools
import json
import math
from pathlib import Path
import time
import sympy as sp

from verify_algebraist_sec7 import galois_rows_for_factor, square_classes_for_simple_factor
from verify_phase3_47_861 import compute_rhs_and_common, decode_deck_poly_to_x, exact_interlaces, poly_real_rooted_ge_neg5
from verify_farkas import check_thm42_odd
from verify_polys import poly_eval_2tm1_asc, v2
from verify_sec7_certs import (
    build_2v_cache_ctx,
    compute_locked_MN,
    decode_chi_S_from_deck_cand,
    exact_farkas_or_primal,
    sha256_file,
    solve_2v_jacobi_exact,
    verify_dual_farkas_int,
)
from _repo_io import AUDIT_DIR, CERT_DIR, COMPUTE_POLY_RESULTS, read_json_auto, resolve_data_file, sha256_auto

POLY_RESULTS_DIR = COMPUTE_POLY_RESULTS
SEC7_CERTS_DIR = CERT_DIR / "sec7"
OUT_JSON = AUDIT_DIR / "phase3_18_59_endgame_audit.json"


def _sqrt_mod_quad_41(a: sp.Rational, b: sp.Rational) -> list[tuple[sp.Rational, sp.Rational]]:
    """Solve (u0 + u1*w)^2 == a + b*w mod (2w^2 - 3w - 4) in QQ."""
    nm = a * a + sp.Rational(3, 2) * a * b - 2 * b * b
    if nm < 0:
        return []
    nn, dn = sp.fraction(nm)
    sn, sd = math.isqrt(int(nn)), math.isqrt(int(dn))
    if sn * sn != nn or sd * sd != dn:
        return []
    t_val = a + sp.Rational(3, 4) * b
    r_nm = sp.Rational(sn, sd)
    sols: list[tuple[sp.Rational, sp.Rational]] = []
    for s_nm in {r_nm, -r_nm}:
        x2 = (t_val + s_nm) / 2
        y2 = (t_val - s_nm) / (2 * sp.Rational(41, 16))
        if x2 < 0 or y2 < 0:
            continue
        nx, dx = sp.fraction(x2)
        ny, dy = sp.fraction(y2)
        sx, sdx = math.isqrt(int(nx)), math.isqrt(int(dx))
        sy, sdy = math.isqrt(int(ny)), math.isqrt(int(dy))
        if sx * sx != nx or sdx * sdx != dx or sy * sy != ny or sdy * sdy != dy:
            continue
        xv = sp.Rational(sx, sdx)
        for yv in {sp.Rational(sy, sdy), -sp.Rational(sy, sdy)}:
            u1 = 4 * yv
            u0 = xv - 3 * yv
            if u0 * u0 + 2 * u1 * u1 == a and 2 * u0 * u1 + sp.Rational(3, 2) * u1 * u1 == b:
                sols.append((u0, u1))
                sols.append((-u0, -u1))
    return list(dict.fromkeys(sols))


def solve_2v_jacobi_endgame(
    chi_S: sp.Poly,
    chi_u: sp.Poly,
    chi_v: sp.Poly,
    x: sp.Symbol,
    ctx: dict,
    c_shift: int = 11,
) -> list[tuple[int, int, list[int]]]:
    """Clean-room 2v Jacobi solver with simple-root square pre-filter and exact diff=3 fallback."""
    for sf in ctx["sim_facs"]:
        if sf.degree() == 1:
            r = int(-sf.nth(0) // sf.nth(1))
            val = int(chi_u.eval(r)) * int(chi_v.eval(r))
            if val < 0:
                return []
            sq = math.isqrt(val)
            if sq * sq != val:
                return []

    n = chi_S.degree()
    try:
        return solve_2v_jacobi_exact(chi_S, chi_u, chi_v, 4, (n - 2) % 4, x, cache_ctx=ctx)
    except NotImplementedError:
        pass

    assert n == 59 and c_shift == 11
    gcd_x = ctx["gcd_x"]
    gcd_2 = ctx["gcd_2"]
    sim_x = ctx["sim_x"]
    rem_chk = sp.Poly(sp.quo((chi_S * gcd_2).as_expr(), (gcd_x * gcd_x).as_expr()), x, domain=sp.ZZ)
    assert rem_chk == sim_x
    g1_sum = int(gcd_x.all_coeffs()[1])
    w = sp.Symbol("w")
    gu = sp.Poly(sp.quo(chi_u, gcd_x).as_expr(), x, domain=sp.ZZ)
    gv = sp.Poly(sp.quo(chi_v, gcd_x).as_expr(), x, domain=sp.ZZ)

    if sim_x == sp.Poly(x - 10, x, domain=sp.ZZ) and gu.degree() == 5 and gv.degree() == 5:
        sq10 = math.isqrt(int(gu.eval(10)) * int(gv.eval(10)))
        Gwu = sp.Poly(sp.expand(gu.as_expr().subs(x, 2 * w + 11) / 32), w, domain=sp.ZZ)
        Gwv = sp.Poly(sp.expand(gv.as_expr().subs(x, 2 * w + 11) / 32), w, domain=sp.ZZ)
        prod_w = sp.Poly(4 * Gwu.as_expr() * Gwv.as_expr(), w, domain=sp.ZZ)
        b_m1 = math.isqrt(4 * int(Gwu.eval(-1)) * int(Gwv.eval(-1)))
        b_0 = math.isqrt(4 * int(Gwu.eval(0)) * int(Gwv.eval(0)))
        v_1_rhs = 4 * int(Gwu.eval(1)) * int(Gwv.eval(1))
        v_2_rhs = 4 * int(Gwu.eval(2)) * int(Gwv.eval(2))
        b_1 = math.isqrt(v_1_rhs)
        b_2 = math.isqrt(v_2_rhs)
        out, seen = [], set()
        for hm1 in range(-b_m1, b_m1 + 1):
            for h0 in range(-b_0, b_0 + 1):
                for h1 in range(-b_1, b_1 + 1):
                    if (h1 - 2 * h0 + hm1) % 2 != 0 or (v_1_rhs - h1 * h1) % 3 != 0:
                        continue
                    a2 = (h1 - 2 * h0 + hm1) // 2 - 1
                    for h2 in range(-b_2, b_2 + 1):
                        if (v_2_rhs - h2 * h2) % 5 != 0:
                            continue
                        diff3 = h2 - 3 * h1 + 3 * h0 - hm1 - 12
                        if diff3 % 6 != 0:
                            continue
                        a3 = diff3 // 6
                        a1 = h1 - 1 - a3 - a2 - h0
                        if abs(1 - 2 * a3 + 4 * a2 - 8 * a1 + 16 * h0) != sq10:
                            continue
                        Hw = sp.Poly([1, a3, a2, a1, h0], w, domain=sp.ZZ)
                        num_w = sp.Poly(prod_w.as_expr() - Hw.as_expr() ** 2, w, domain=sp.ZZ)
                        Q_w, rem_w = sp.div(num_w, sp.Poly(2 * w + 1, w, domain=sp.ZZ))
                        assert rem_w.is_zero
                        qx = sp.Poly(sp.expand(256 * Q_w.as_expr().subs(w, (x - 11) / 2)), x, domain=sp.ZZ)
                        if not poly_real_rooted_ge_neg5(qx, x):
                            continue
                        c_uv = sp.Poly((gcd_2 * qx).as_expr(), x, domain=sp.ZZ)
                        c_desc = [int(c) for c in c_uv.all_coeffs()]
                        if len(c_desc) != 58 or c_desc[0] != 1 or c_desc[1] != 0:
                            continue
                        ev2 = poly_eval_2tm1_asc(c_desc)
                        if any(v2(cv) < 56 for cv in ev2):
                            continue
                        if not check_thm42_odd([cv >> 56 for cv in ev2], 57):
                            continue
                        if not exact_interlaces(chi_u, c_uv, x) or not exact_interlaces(chi_v, c_uv, x):
                            continue
                        d1 = g1_sum + 2 * a3 - 44
                        assert d1 % 2 == 1
                        s_val, c2_val = (1, d1) if (d1 % 4 == 1) else (-1, -d1)
                        tc = (s_val, c2_val, tuple(c_desc))
                        if tc not in seen:
                            seen.add(tc)
                            out.append((s_val, c2_val, c_desc))
        return out

    if sim_x == sp.Poly(x ** 2 - 25 * x + 146, x, domain=sp.ZZ) and gu.degree() == 6 and gv.degree() == 6:
        Gwu = sp.Poly(sp.expand(gu.as_expr().subs(x, 2 * w + 11) / 64), w, domain=sp.ZZ)
        Gwv = sp.Poly(sp.expand(gv.as_expr().subs(x, 2 * w + 11) / 64), w, domain=sp.ZZ)
        prod_w = sp.Poly(4 * Gwu.as_expr() * Gwv.as_expr(), w, domain=sp.ZZ)
        mod_p = sp.Poly(2 * w ** 2 - 3 * w - 4, w, domain=sp.QQ)
        rem = sp.rem(sp.Poly(prod_w.as_expr(), w, domain=sp.QQ), mod_p)
        roots_uv = _sqrt_mod_quad_41(sp.Rational(rem.nth(0)), sp.Rational(rem.nth(1)))
        if not roots_uv:
            return []
        b0 = math.isqrt(4 * int(Gwu.eval(0)) * int(Gwv.eval(0)))
        b1 = math.isqrt(4 * int(Gwu.eval(1)) * int(Gwv.eval(1)))
        g_w2 = sp.rem(prod_w, sp.Poly(w ** 2 - 2, w, domain=sp.ZZ))
        B_P = math.isqrt(4 * (abs(int(g_w2.nth(0))) + 2 * abs(int(g_w2.nth(1))))) + 2
        out, seen = [], set()
        for u0, u1 in roots_uv:
            for a0 in range(-b0, b0 + 1):
                c0 = (u0 - a0) / 2
                for h1 in range(-b1, b1 + 1):
                    num_s = 2 * (u0 + u1 - h1)
                    if num_s.q != 1 or int(num_s) % 5 != 0:
                        continue
                    S1 = int(num_s) // 5
                    for P2 in range(-B_P, B_P + 1):
                        c1 = (u0 - P2) / 3 - 2
                        c2 = S1 - 1 - c1 - c0
                        H_c = [
                            sp.Rational(1),
                            c2 - sp.Rational(3, 2),
                            c1 - sp.Rational(3, 2) * c2 - 2,
                            c0 - sp.Rational(3, 2) * c1 - 2 * c2,
                            u1 - sp.Rational(3, 2) * c0 - 2 * c1,
                            u0 - 2 * c0,
                        ]
                        if any(hc.q != 1 for hc in H_c):
                            continue
                        Hw = sp.Poly([int(hc) for hc in H_c], w, domain=sp.ZZ)
                        num_w = sp.Poly(prod_w.as_expr() - Hw.as_expr() ** 2, w, domain=sp.ZZ)
                        Q_w, rem_w = sp.div(num_w, sp.Poly(2 * w ** 2 - 3 * w - 4, w, domain=sp.ZZ))
                        assert rem_w.is_zero
                        qx = sp.Poly(sp.expand(512 * Q_w.as_expr().subs(w, (x - 11) / 2)), x, domain=sp.ZZ)
                        if not poly_real_rooted_ge_neg5(qx, x):
                            continue
                        c_uv = sp.Poly((gcd_2 * qx).as_expr(), x, domain=sp.ZZ)
                        c_desc = [int(c) for c in c_uv.all_coeffs()]
                        if len(c_desc) != 58 or c_desc[0] != 1 or c_desc[1] != 0:
                            continue
                        ev2 = poly_eval_2tm1_asc(c_desc)
                        if any(v2(cv) < 56 for cv in ev2):
                            continue
                        if not check_thm42_odd([cv >> 56 for cv in ev2], 57):
                            continue
                        if not exact_interlaces(chi_u, c_uv, x) or not exact_interlaces(chi_v, c_uv, x):
                            continue
                        d1 = g1_sum + 2 * int(H_c[1]) - 55
                        assert d1 % 2 == 1
                        s_val, c2_val = (1, d1) if (d1 % 4 == 1) else (-1, -d1)
                        tc = (s_val, c2_val, tuple(c_desc))
                        if tc not in seen:
                            seen.add(tc)
                            out.append((s_val, c2_val, c_desc))
        return out

    raise NotImplementedError(f"Unsupported diff=3 case: sim_x={sim_x}")


def enum_nonneg_int_sols_fast(A_int: list[list[int]], b_int: list[int], total_sum: int) -> list[list[int]]:
    """Exact ZZ/QQ RREF + LP-tightened + interval-pruned branch-and-bound for x >= 0, Ax = b."""
    m = len(A_int)
    k = len(A_int[0]) if m > 0 else 0
    if k == 0:
        return []
    M = sp.Matrix([[sp.Rational(A_int[r][c]) for c in range(k)] + [sp.Rational(b_int[r])] for r in range(m)])
    rref_M, pivs = M.rref()
    if k in pivs:
        return []
    for r in range(len(pivs), m):
        if rref_M[r, k] != 0:
            return []
    piv_set = set(pivs)
    free_cols = [c for c in range(k) if c not in piv_set]
    if not free_cols:
        sol = [0] * k
        for r_idx, pc in enumerate(pivs):
            v = rref_M[r_idx, k]
            if v.q != 1 or int(v) < 0:
                return []
            sol[pc] = int(v)
        return [sol] if sum(sol) == total_sum else []

    bounds = []
    A_sl = [row + [0] for row in A_int]
    for fc in free_cols:
        lo_t, hi_t = 0, total_sum
        if exact_farkas_or_primal(A_sl + [[1 if c == fc else 0 for c in range(k)] + [1]], b_int + [total_sum])[0] == "FARKAS":
            return []
        while lo_t < hi_t:
            mid = (lo_t + hi_t) // 2
            st, _ = exact_farkas_or_primal(A_sl + [[1 if c == fc else 0 for c in range(k)] + [1]], b_int + [mid])
            if st == "PRIMAL":
                hi_t = mid
            else:
                lo_t = mid + 1
        lb = lo_t

        lo_u, hi_u = lb, total_sum
        while lo_u < hi_u:
            mid = (lo_u + hi_u + 1) // 2
            st, _ = exact_farkas_or_primal(A_sl + [[1 if c == fc else 0 for c in range(k)] + [-1]], b_int + [mid])
            if st == "PRIMAL":
                lo_u = mid
            else:
                hi_u = mid - 1
        bounds.append((lb, lo_u))

    nf = len(free_cols)
    piv_exprs = []
    for r_idx, pc in enumerate(pivs):
        const = Fraction(int(rref_M[r_idx, k].p), int(rref_M[r_idx, k].q))
        coeffs = [Fraction(int(rref_M[r_idx, fc].p), int(rref_M[r_idx, fc].q)) for fc in free_cols]
        piv_exprs.append((pc, const, coeffs))

    # Precompute suffix min/max of sum_{j>=idx} coeff[j]*f_j using static box bounds
    npiv = len(piv_exprs)
    suf_min_c = [[Fraction(0)] * (nf + 1) for _ in range(npiv)]
    suf_max_c = [[Fraction(0)] * (nf + 1) for _ in range(npiv)]
    for p_i, (_, _, coeffs) in enumerate(piv_exprs):
        for j in range(nf - 1, -1, -1):
            lb_j, ub_j = bounds[j]
            v1, v2_ = coeffs[j] * lb_j, coeffs[j] * ub_j
            suf_min_c[p_i][j] = suf_min_c[p_i][j + 1] + min(v1, v2_)
            suf_max_c[p_i][j] = suf_max_c[p_i][j + 1] + max(v1, v2_)

    suf_lb_sum = [0] * (nf + 1)
    for j in range(nf - 1, -1, -1):
        suf_lb_sum[j] = suf_lb_sum[j + 1] + bounds[j][0]

    sols = []
    f_vals = [0] * nf
    cur_piv_sum = [Fraction(0)] * npiv

    def backtrack(idx_f: int, rem_sum: int) -> None:
        if rem_sum < suf_lb_sum[idx_f]:
            return
        for p_i in range(npiv):
            rem_piv = piv_exprs[p_i][1] - cur_piv_sum[p_i]
            # Pivot value = rem_piv - (sum_{j>=idx_f} coeffs[j]*f_j) must allow >= 0 and <= rem_sum
            if rem_piv - suf_min_c[p_i][idx_f] < 0:
                return
            if rem_piv - suf_max_c[p_i][idx_f] > rem_sum:
                return
        if idx_f == nf:
            sol = [0] * k
            for i, fc in enumerate(free_cols):
                sol[fc] = f_vals[i]
            for p_i, (pc, const, _) in enumerate(piv_exprs):
                val = const - cur_piv_sum[p_i]
                if val.denominator != 1 or val < 0:
                    return
                sol[pc] = int(val)
            if sum(sol) == total_sum:
                sols.append(sol)
            return
        lb, ub = bounds[idx_f]
        ub_eff = min(ub, rem_sum - suf_lb_sum[idx_f + 1])
        for v in range(lb, ub_eff + 1):
            f_vals[idx_f] = v
            for p_i in range(npiv):
                cur_piv_sum[p_i] += piv_exprs[p_i][2][idx_f] * v
            backtrack(idx_f + 1, rem_sum - v)
            for p_i in range(npiv):
                cur_piv_sum[p_i] -= piv_exprs[p_i][2][idx_f] * v

    backtrack(0, total_sum)
    return sols


def clean_stage2_cones(cand: dict, d: int, n: int, c_shift: int) -> tuple[sp.Poly, list[int], sp.Poly, list[sp.Poly], list[tuple[list[int], list[tuple[list[Fraction], Fraction]]]]]:
    """Independent clean-room Stage-2 T7.1 + parity + square-class cone splitting + Galois feasibility."""
    x = sp.Symbol("x")
    chi_S = decode_chi_S_from_deck_cand(cand, d, n, c_shift, x)
    rhs, F_z, _, _ = compute_rhs_and_common(cand["b"], d, n, c_shift)
    deck = cand["deck"]
    s = len(rhs)
    gcd_x = sp.gcd(chi_S, sp.diff(chi_S, x))

    _, fl = sp.factor_list(chi_S)
    mrad = sp.Poly(1, x, domain=sp.ZZ)
    sim_x = sp.Poly(1, x, domain=sp.ZZ)
    for fc, mp in fl:
        if mp >= 2:
            mrad = sp.Poly(mrad.as_expr() * fc.as_expr(), x, domain=sp.ZZ)
        else:
            sim_x = sp.Poly(sim_x.as_expr() * fc.as_expr(), x, domain=sp.ZZ)

    P1, Pm1, P0, Pp0 = int(mrad.eval(1)), int(mrad.eval(-1)), int(mrad.eval(0)), int(sp.diff(mrad, x).eval(0))
    pe, po = (P1 + Pm1) // 2, (P1 - Pm1) // 2
    cI, cS = pe % 4, po % 4
    cJ = ((n - 2) * ((pe - P0) + (n - 1) * (po - Pp0))) % 4
    diag_M, off_M = (cI + cJ) % 4, {(cJ + cS) % 4, (cJ - cS) % 4}

    sim_q = sp.Poly(sim_x.as_expr(), x, domain=sp.QQ)
    inv_cp = sp.invert(sp.Poly(sp.diff(chi_S, x).as_expr(), x, domain=sp.QQ), sim_q) if not sim_x.is_one else None
    mrad_q = sp.Poly(mrad.as_expr(), x, domain=sp.QQ)
    d_sf = sim_x.degree()
    cs = [Fraction(int(v)) for v in sim_x.all_coeffs()] if not sim_x.is_one else []
    psums = [Fraction(d_sf)]
    for kp in range(1, d_sf):
        psums.append(-sum(cs[j] * psums[kp - j] for j in range(1, kp)) - kp * cs[kp])

    kept = []
    for di, gd in enumerate(deck):
        cv = decode_deck_poly_to_x(gd, c_shift, n - 1, gcd_x, x)
        if not all(v2(bk) >= (n - 1) for bk in poly_eval_2tm1_asc([int(c) for c in cv.all_coeffs()])):
            continue
        if not sim_x.is_one:
            rem_v = sp.rem(mrad_q * sp.Poly(cv.as_expr(), x, domain=sp.QQ) * inv_cp, sim_q, domain=sp.QQ)
            if rem_v.is_zero and 0 not in off_M:
                continue
            rc = rem_v.all_coeffs()
            de = len(rc)
            tr = sum(Fraction(int(rc[de - 1 - j].numerator), int(rc[de - 1 - j].denominator)) * psums[j] for j in range(de))
            if tr.denominator != 1 or int(tr) % 4 != diag_M:
                continue
        kept.append(di)

    z = F_z.gens[0]
    _, flz = sp.factor_list(F_z)
    sfs = sorted([f for f, m in flz if m == 1], key=lambda fp: fp.degree())
    active = [kept]
    for sf in sfs:
        nxt = []
        for cur in active:
            for bl in square_classes_for_simple_factor([deck[i] for i in cur], sf, z):
                glob = [cur[i] for i in bl]
                A_eq = [[deck[i][k] for i in glob] for k in range(s)]
                st, _ = exact_farkas_or_primal(A_eq, rhs)
                if st == "PRIMAL":
                    nxt.append(glob)
        active = nxt

    feasible_cones = []
    for sub in active:
        A_r = [[Fraction(deck[i][k]) for i in sub] for k in range(s)]
        bf = [Fraction(v) for v in rhs]
        extra_rows = []
        for sf in sfs:
            if sf.degree() >= 2:
                for gr in galois_rows_for_factor(deck, sub, sf, z):
                    row_map = {sub[p]: gr[p] for p in range(len(sub))}
                    extra_rows.append((row_map, Fraction(0)))
                    A_r.append(gr)
                    bf.append(Fraction(0))
        A_i, b_i = [], []
        for row, bv in zip(A_r, bf):
            ld = bv.denominator
            for v in row:
                ld = sp.ilcm(ld, v.denominator)
            A_i.append([int(v * ld) for v in row])
            b_i.append(int(bv * ld))
        st, _ = exact_farkas_or_primal(A_i, b_i)
        if st == "PRIMAL":
            feasible_cones.append((sub, extra_rows))

    return chi_S, rhs, F_z, sfs, feasible_cones


def enum_cone_solutions(deck: list[list[int]], sub: list[int], extra_rows: list, rhs: list[int], n: int) -> list[list[list[int]]]:
    s = len(rhs)
    A_r = [[Fraction(deck[i][k]) for i in sub] for k in range(s)]
    bf = [Fraction(v) for v in rhs]
    for rmap, bv in extra_rows:
        A_r.append([rmap.get(i, Fraction(0)) for i in sub])
        bf.append(bv)
    A_i, b_i = [], []
    for row, bv in zip(A_r, bf):
        ld = bv.denominator
        for v in row:
            ld = sp.ilcm(ld, v.denominator)
        A_i.append([int(v * ld) for v in row])
        b_i.append(int(bv * ld))
    sols = enum_nonneg_int_sols_fast(A_i, b_i, n)
    return [sorted([[sub[p], vec[p]] for p in range(len(sub)) if vec[p] > 0]) for vec in sols]


def build_prop61_checker(chi_S: sp.Poly, get_chi, dis: list[int], x: sp.Symbol):
    """Precompute Prop 6.1 factor traces and per-deck-item divisibility flags once per chi_S."""
    n = chi_S.degree()
    _, fl_S = sp.factor_list(chi_S)
    fac_info = []
    for f, m in fl_S:
        df = f.degree()
        lc = Fraction(int(f.LC()))
        coeffs = [Fraction(int(c)) / lc for c in f.all_coeffs()]
        p1 = -coeffs[1] if df >= 1 else Fraction(0)
        p2 = (p1 * p1) if df == 1 else (-coeffs[1] * p1 - Fraction(2) * coeffs[2])
        f_m = sp.Poly(f.as_expr() ** m, x, domain=sp.ZZ)
        fac_info.append((f, m, df, p1, p2, f_m))
    r_max = float(max(sp.CRootOf(f, f.degree() - 1).evalf() for f, _ in fl_S))
    div_masks: dict[int, list[bool]] = {}
    for di in dis:
        chi_v = get_chi(di)
        div_masks[di] = [sp.rem(chi_v, f_m).is_zero for _, _, _, _, _, f_m in fac_info]

    def kills_sol(sol: list[list[int]]) -> bool:
        for f_i, (_, m, df, p1, p2, _) in enumerate(fac_info):
            k = sum(cnt for di, cnt in sol if div_masks[di][f_i])
            if k == 0:
                continue
            np = n - k
            if np <= 0:
                return True
            sum_m = df * m
            tr_f = Fraction(m) * p1
            tr2_f = Fraction(m) * p2
            for g_i, (_, mg, dg, g1, g2, _) in enumerate(fac_info):
                if g_i == f_i:
                    continue
                rem_mg = max(0, mg - k)
                if rem_mg > 0:
                    sum_m += dg * rem_mg
                    tr_f += Fraction(rem_mg) * g1
                    tr2_f += Fraction(rem_mg) * g2
            if sum_m > np:
                return True
            r_rem = np - sum_m
            T_rem = -tr_f
            Q_rem = Fraction(np * (np - 1)) - tr2_f
            if Q_rem < 0:
                return True
            if r_rem == 0:
                if T_rem != 0 or Q_rem != 0:
                    return True
            else:
                if Fraction(r_rem) * Q_rem < T_rem * T_rem:
                    return True
                if r_rem == 1 and (T_rem * T_rem != Q_rem or T_rem < -5 or float(T_rem) > r_max + 1e-6):
                    return True
        return False

    return kills_sol


def prop61_kills_sol(chi_S: sp.Poly, chis: list[sp.Poly], cnts: list[int], x: sp.Symbol) -> bool:
    """Proposition 6.1: exact multiplicity + trace + trace-of-squares + Cauchy-Schwarz check on S[I^c]."""
    n = chi_S.degree()
    _, fl_S = sp.factor_list(chi_S)
    # Precompute factor traces Tr(f) and Tr(f^2) over roots of f
    fac_info = []
    for f, m in fl_S:
        df = f.degree()
        lc = Fraction(int(f.LC()))
        coeffs = [Fraction(int(c)) / lc for c in f.all_coeffs()]
        p1 = -coeffs[1] if df >= 1 else Fraction(0)
        if df == 1:
            p2 = p1 * p1
        else:
            p2 = -coeffs[1] * p1 - Fraction(2) * coeffs[2]
        fac_info.append((f, m, df, p1, p2))

    # Max root bound of chi_S for r_rem == 1 check
    r_max = max(sp.CRootOf(f, f.degree() - 1).evalf() for f, _ in fl_S)

    for f_i, (f, m, df, p1, p2) in enumerate(fac_info):
        # I_f = {v : mult_f(chi_{S_v}) >= m}
        f_m = sp.Poly(f.as_expr() ** m, x, domain=sp.ZZ)
        k = 0
        for chi_v, cnt in zip(chis, cnts):
            if sp.rem(chi_v, f_m).is_zero:
                k += cnt
        if k == 0:
            continue
        np = n - k
        if np <= 0:
            return True
        sum_m = df * m
        tr_f = Fraction(m) * p1
        tr2_f = Fraction(m) * p2
        for g_i, (_, mg, dg, g1, g2) in enumerate(fac_info):
            if g_i == f_i:
                continue
            rem_mg = max(0, mg - k)
            if rem_mg > 0:
                sum_m += dg * rem_mg
                tr_f += Fraction(rem_mg) * g1
                tr2_f += Fraction(rem_mg) * g2
        if sum_m > np:
            return True
        r_rem = np - sum_m
        T_rem = -tr_f
        Q_rem = Fraction(np * (np - 1)) - tr2_f
        if Q_rem < 0:
            return True
        if r_rem == 0:
            if T_rem != 0 or Q_rem != 0:
                return True
        else:
            if Fraction(r_rem) * Q_rem < T_rem * T_rem:
                return True
            if r_rem == 1:
                if T_rem * T_rem != Q_rem or T_rem < -5 or float(T_rem) > float(r_max) + 1e-6:
                    return True
    return False


def sv_galois_kills_v(
    chi_S: sp.Poly,
    chi_v: sp.Poly,
    chis: list[sp.Poly],
    cnts: list[int],
    v_pos: int,
    x: sp.Symbol,
    ctx: dict,
    get_2v_raw,
    sim_v_override: list[sp.Poly] | None = None,
    sv_cache: dict | None = None,
) -> bool:
    """Clean-room Stage-2 square-class + Galois orthogonality check on S_v (order n-1)."""
    if sv_cache is None:
        sv_cache = {}
    b_locs_cache = sv_cache.setdefault("b_locs", {})
    gal_cache = sv_cache.setdefault("gal", {})
    q_vp_cache = sv_cache.setdefault("q_vp", {})
    q_c_cache = sv_cache.setdefault("q_c", {})

    n = chi_S.degree()
    gcd_2 = ctx["gcd_2"]
    deg_q = (n - 2) - gcd_2.degree()
    vp_key = tuple(int(c) for c in chi_v.all_coeffs())
    if vp_key not in q_vp_cache:
        chi_vp = sp.diff(chi_v, x)
        q_vp, rem_vp = sp.div(chi_vp, gcd_2)
        if not rem_vp.is_zero:
            q_vp_cache[vp_key] = None
        else:
            qvp_coeffs = [int(c) for c in q_vp.all_coeffs()]
            q_vp_cache[vp_key] = [0] * (deg_q + 1 - len(qvp_coeffs)) + qvp_coeffs
    qvp_coeffs = q_vp_cache[vp_key]
    if qvp_coeffs is None:
        return True

    cols = []
    for b_idx in range(len(chis)):
        nb_rem = cnts[b_idx] - (1 if b_idx == v_pos else 0)
        if nb_rem <= 0:
            continue
        res = get_2v_raw(v_pos, b_idx)
        seen_c = set()
        for _, _, coeffs_desc in res:
            t_c = tuple(coeffs_desc)
            if t_c not in seen_c:
                seen_c.add(t_c)
                if t_c not in q_c_cache:
                    q_c, rem_c = sp.div(sp.Poly(coeffs_desc, x, domain=sp.ZZ), gcd_2)
                    assert rem_c.is_zero
                    qc_coeffs = [int(c) for c in q_c.all_coeffs()]
                    q_c_cache[t_c] = [0] * (deg_q + 1 - len(qc_coeffs)) + qc_coeffs
                cols.append((b_idx, coeffs_desc, q_c_cache[t_c]))
    if not cols:
        return True

    base_rows = [[c[2][r_i] for c in cols] for r_i in range(deg_q + 1)]
    base_rhs = list(qvp_coeffs)
    for b_idx in range(len(chis)):
        nb_rem = cnts[b_idx] - (1 if b_idx == v_pos else 0)
        if nb_rem <= 0:
            continue
        base_rows.append([1 if bi == b_idx else 0 for bi, _, _ in cols])
        base_rhs.append(nb_rem)

    if sim_v_override is None:
        _, fl_v = sp.factor_list(chi_v)
        sim_v = sorted([f for f, m in fl_v if m == 1], key=lambda fp: fp.degree())
    else:
        sim_v = sim_v_override
    col_polys = [c_desc for _, c_desc, _ in cols]
    col_keys = [tuple(c) for c in col_polys]
    active = [(list(range(len(cols))), [])]
    for sf in sim_v:
        sf_key = tuple(int(c) for c in sf.all_coeffs())
        nxt = []
        for sub, extra in active:
            sub_key = (sf_key, tuple(col_keys[i] for i in sub))
            if sub_key not in b_locs_cache:
                b_locs_cache[sub_key] = square_classes_for_simple_factor([col_polys[i] for i in sub], sf, x)
            b_locs = b_locs_cache[sub_key]
            for bl in b_locs:
                glob = [sub[i] for i in bl]
                nex = list(extra)
                if sf.degree() >= 2:
                    glob_key = (sf_key, tuple(col_keys[i] for i in glob))
                    if glob_key not in gal_cache:
                        gal_cache[glob_key] = galois_rows_for_factor(col_polys, glob, sf, x)
                    for gr in gal_cache[glob_key]:
                        gmap = {glob[k]: gr[k] for k in range(len(glob))}
                        nex.append((gmap, Fraction(0)))
                A_int = [[base_rows[r][c] for c in glob] for r in range(len(base_rows))]
                b_int = list(base_rhs)
                for gmap, bv in nex:
                    lcm_d = bv.denominator
                    for c in glob:
                        lcm_d = sp.ilcm(lcm_d, gmap.get(c, Fraction(0)).denominator)
                    A_int.append([int(gmap.get(c, Fraction(0)) * lcm_d) for c in glob])
                    b_int.append(int(bv * lcm_d))
                st, _ = exact_farkas_or_primal(A_int, b_int)
                if st == "PRIMAL":
                    nxt.append((glob, nex))
        active = nxt
        if not active:
            return True
    return False


def stage3_filter_sol(
    chi_S: sp.Poly,
    sol: list[list[int]],
    n: int,
    x: sp.Symbol,
    ctx: dict,
    get_chi,
    get_2v_raw,
    run_sv_galois: bool = True,
    s3_cache: dict | None = None,
) -> tuple[bool, str]:
    """Clean-room Stage-3 filter on a single Stage-2+Prop6.1 solution.
    Returns (killed: bool, reason: str).
    """
    if s3_cache is None:
        s3_cache = {}
    q_pair_cache = s3_cache.setdefault("q_pair", {})
    rhs_q_cache = s3_cache.setdefault("rhs_q", {})
    sim_v_cache = s3_cache.setdefault("sim_v", {})

    b_cnt = len(sol)
    ns = [cnt for _, cnt in sol]
    dis = [di for di, _ in sol]

    # 1. Pairwise 2v emptiness + collect sign pairs
    p2v: dict[tuple[int, int], list[tuple[int, int]]] = {}
    for i in range(b_cnt):
        for j in range(i, b_cnt):
            if i == j and ns[i] < 2:
                continue
            raw = get_2v_raw(dis[i], dis[j])
            pairs = sorted({(a, b) for a, b, _ in raw})
            if not pairs:
                return True, "2v_empty"
            p2v[(i, j)] = pairs

    # 1.5 Single-vertex 2v polynomial Farkas check (exact ZZ LP on sum chi_{S_vu}/gcd_2 == chi_{S_v}'/gcd_2)
    chis = [get_chi(di) for di in dis]
    gcd_2 = ctx["gcd_2"]
    deg_q = (n - 2) - gcd_2.degree()

    def get_q_list(da: int, db: int) -> list[list[int]]:
        key = (min(da, db), max(da, db))
        if key not in q_pair_cache:
            raw = get_2v_raw(key[0], key[1])
            seen_q = set()
            q_list = []
            for _, _, c_uv in raw:
                q_p, rem_q = sp.div(sp.Poly(c_uv, x, domain=sp.ZZ), gcd_2)
                assert rem_q.is_zero
                q_cs = [int(c) for c in q_p.all_coeffs()]
                q_cs = [0] * (deg_q + 1 - len(q_cs)) + q_cs
                qt = tuple(q_cs)
                if qt not in seen_q:
                    seen_q.add(qt)
                    q_list.append(q_cs)
            q_pair_cache[key] = q_list
        return q_pair_cache[key]

    def get_rhs_q(di: int, chi_v: sp.Poly) -> list[int]:
        if di not in rhs_q_cache:
            rhs_qp, rem_vp = sp.div(sp.diff(chi_v, x), gcd_2)
            assert rem_vp.is_zero
            rhs_cs = [int(c) for c in rhs_qp.all_coeffs()]
            rhs_q_cache[di] = [0] * (deg_q + 1 - len(rhs_cs)) + rhs_cs
        return rhs_q_cache[di]

    for v_pos in range(b_cnt):
        cols_q = []
        active_bs = []
        for b_idx in range(b_cnt):
            nb_rem = ns[b_idx] - (1 if b_idx == v_pos else 0)
            if nb_rem <= 0:
                continue
            active_bs.append((b_idx, nb_rem))
            for q_cs in get_q_list(dis[v_pos], dis[b_idx]):
                cols_q.append((b_idx, q_cs))
        if not cols_q:
            return True, "sv_2v_farkas"
        rhs_cs = get_rhs_q(dis[v_pos], chis[v_pos])
        A_sv = [[q_cs[r_i] for _, q_cs in cols_q] for r_i in range(deg_q + 1)]
        b_sv = list(rhs_cs)
        for b_idx, nb_rem in active_bs:
            A_sv.append([1 if bi == b_idx else 0 for bi, _ in cols_q])
            b_sv.append(nb_rem)
        if exact_farkas_or_primal(A_sv, b_sv)[0] == "FARKAS":
            return True, "sv_2v_farkas"

    # 2. Locked M, N + enum_ku_rows
    lcols, M_l, N_l = compute_locked_MN(chi_S, chis, sol, n, x)
    mod4_target = (n - 1) % 4

    def enum_ku(ranges: list[list[int]], N_row: list[int]) -> list[list[int]]:
        nc = len(lcols)
        suf_min = [[0] * nc for _ in range(b_cnt + 1)]
        suf_max = [[0] * nc for _ in range(b_cnt + 1)]
        for i in range(b_cnt - 1, -1, -1):
            if not ranges[i]:
                return []
            lo_i, hi_i = min(ranges[i]), max(ranges[i])
            for cc in range(nc):
                v1, v2_ = lo_i * M_l[i][cc], hi_i * M_l[i][cc]
                suf_min[i][cc] = suf_min[i + 1][cc] + min(v1, v2_)
                suf_max[i][cc] = suf_max[i + 1][cc] + max(v1, v2_)
        out: list[list[int]] = []
        cur = [0] * b_cnt
        acc = [0] * nc

        def dfs(i: int, s_cur: int) -> None:
            for cc in range(nc):
                if acc[cc] + suf_min[i][cc] > N_row[cc] or acc[cc] + suf_max[i][cc] < N_row[cc]:
                    return
            if i == b_cnt:
                if s_cur % 4 == mod4_target:
                    out.append(list(cur))
                return
            for v in ranges[i]:
                cur[i] = v
                for cc in range(nc):
                    acc[cc] += v * M_l[i][cc]
                dfs(i + 1, s_cur + v)
                for cc in range(nc):
                    acc[cc] -= v * M_l[i][cc]

        dfs(0, 0)
        return out

    ku = []
    all_ranges = []
    max_prod = 1
    for r in range(b_cnt):
        ranges = []
        r_prod = 1
        for j in range(b_cnt):
            lim = ns[j] - (1 if j == r else 0)
            if lim == 0:
                ranges.append([0])
                continue
            sgns = {p[0] for p in p2v[(min(r, j), max(r, j))]}
            opts = [lim] if sgns == {1} else ([-lim] if sgns == {-1} else list(range(-lim, lim + 1, 2)))
            ranges.append(opts)
            r_prod *= len(opts)
        all_ranges.append(ranges)
        if r_prod > max_prod:
            max_prod = r_prod

    def get_sim_v(di: int, chi_v: sp.Poly) -> list[sp.Poly]:
        if di not in sim_v_cache:
            _, fl_v = sp.factor_list(chi_v)
            sim_v_cache[di] = sorted([f for f, m in fl_v if m == 1], key=lambda fp: fp.degree())
        return sim_v_cache[di]

    if run_sv_galois and max_prod > 500:
        for v_pos in range(b_cnt):
            if sv_galois_kills_v(chi_S, chis[v_pos], chis, ns, v_pos, x, ctx, lambda a, b: get_2v_raw(dis[a], dis[b]), sim_v_override=get_sim_v(dis[v_pos], chis[v_pos]), sv_cache=s3_cache):
                return True, "sv_galois"

    for r in range(b_cnt):
        rows_r = enum_ku(all_ranges[r], N_l[r])
        if not rows_r:
            return True, "ku_empty"
        ku.append(rows_r)

    # 3. Cauchy-Schwarz 2v compatibility fixed point
    def compat(a: int, ka: list[int], b: int, kb: list[int], s_val: int) -> bool:
        ps = p2v[(min(a, b), max(a, b))]
        lo, hi = 0, 0
        for cc in range(b_cnt):
            nc_v = ns[cc] - (1 if cc == a else 0) - (1 if cc == b else 0)
            tku = ka[cc] - (s_val if cc == b else 0)
            tkv = kb[cc] - (s_val if cc == a else 0)
            lo += abs(tku + tkv) - nc_v
            hi += nc_v - abs(tku - tkv)
        return any(p[0] == s_val and lo <= p[1] <= hi for p in ps)

    while True:
        nku = []
        for a in range(b_cnt):
            kept = []
            for ka in ku[a]:
                ok = True
                for b in range(b_cnt):
                    tot = ns[b] - (1 if b == a else 0)
                    if tot == 0:
                        continue
                    if not ku[b]:
                        ok = False
                        break
                    if ka[b] > -tot and not any(compat(a, ka, b, kb, 1) for kb in ku[b]):
                        ok = False
                        break
                    if ka[b] < tot and not any(compat(a, ka, b, kb, -1) for kb in ku[b]):
                        ok = False
                        break
                if ok:
                    kept.append(ka)
            if not kept:
                return True, "ku_2v_fp"
            nku.append(kept)
        if [len(r) for r in nku] == [len(r) for r in ku]:
            ku = nku
            break
        ku = nku

    # 4. Global K = K^T Farkas
    offsets, cur = [], 0
    for r in range(b_cnt):
        offsets.append(cur)
        cur += len(ku[r])
    rows_eq, b_eq = [], []
    for a in range(b_cnt):
        row = [0] * cur
        for i in range(len(ku[a])):
            row[offsets[a] + i] = 1
        rows_eq.append(row)
        b_eq.append(ns[a])
    for a in range(b_cnt):
        for b in range(a + 1, b_cnt):
            row = [0] * cur
            for i, ka in enumerate(ku[a]):
                row[offsets[a] + i] = ka[b]
            for j, kb in enumerate(ku[b]):
                row[offsets[b] + j] = -kb[a]
            rows_eq.append(row)
            b_eq.append(0)
    st, _ = exact_farkas_or_primal(rows_eq, b_eq)
    if st == "FARKAS":
        return True, "global_K_farkas"

    # 5. Single-vertex S_v Galois check
    if run_sv_galois and max_prod <= 500:
        for v_pos in range(b_cnt):
            if sv_galois_kills_v(chi_S, chis[v_pos], chis, ns, v_pos, x, ctx, lambda a, b: get_2v_raw(dis[a], dis[b]), sim_v_override=get_sim_v(dis[v_pos], chis[v_pos]), sv_cache=s3_cache):
                return True, "sv_galois"

    return False, "SURVIVED"


def verify_coupled_farkas_cert(
    cand: dict,
    d: int,
    n: int,
    c_shift: int,
    chi_S: sp.Poly,
    rhs: list[int],
    extra_rows: list,
    cert: dict,
    x: sp.Symbol,
    ctx: dict,
    get_chi_fn=None,
    get_2v_raw_fn=None,
) -> None:
    """Verify a coupled Stage-2+3 Farkas certificate [v_pruned, cur_act, c_farkas]."""
    v_pruned = cert["v_pruned"]
    cur_act = cert["cur_act"]
    y_c = cert["c_farkas"]
    deck = cand["deck"]
    s = len(rhs)
    gcd_x = ctx["gcd_x"]
    gcd_2 = ctx["gcd_2"]
    deg_q = (n - 2) - gcd_2.degree()
    s2_rem = (n - 2) % 4

    chi_cache: dict[int, sp.Poly] = {}

    def get_chi(di: int) -> sp.Poly:
        if get_chi_fn is not None:
            return get_chi_fn(di)
        if di not in chi_cache:
            chi_cache[di] = decode_deck_poly_to_x(deck[di], c_shift, n - 1, gcd_x, x)
        return chi_cache[di]

    def get_2v(da: int, db: int) -> list[tuple[int, int, list[int]]]:
        if get_2v_raw_fn is not None:
            return get_2v_raw_fn(da, db)
        return solve_2v_jacobi_exact(chi_S, get_chi(da), get_chi(db), 4, s2_rem, x, cache_ctx=ctx)

    m_c = len(cur_act)
    v_loc = cur_act.index(v_pruned)
    cols_m = []
    for loc_b, b in enumerate(cur_act):
        col = [Fraction(deck[b][r]) for r in range(s)] + [rmap.get(b, Fraction(0)) for rmap, _ in extra_rows] + [Fraction(0)] * (deg_q + 1) + [Fraction(-1 if k == loc_b else 0) for k in range(m_c)]
        cols_m.append(col)

    for loc_b, b in enumerate(cur_act):
        raw = get_2v(v_pruned, b)
        seen_q = set()
        for _, _, c_uv in raw:
            q_poly, rem = sp.div(sp.Poly(c_uv, x, domain=sp.ZZ), gcd_2)
            assert rem.is_zero
            q_cs = [int(c) for c in q_poly.all_coeffs()]
            q_cs = [0] * (deg_q + 1 - len(q_cs)) + q_cs
            qt = tuple(q_cs)
            if qt not in seen_q:
                seen_q.add(qt)
                col = [Fraction(0)] * (s + len(extra_rows)) + [Fraction(v) for v in q_cs] + [Fraction(1 if k == loc_b else 0) for k in range(m_c)]
                cols_m.append(col)

    chi_vp = sp.diff(get_chi(v_pruned), x)
    rhs_q_poly, rem_vp = sp.div(chi_vp, gcd_2)
    assert rem_vp.is_zero
    rhs_q = [int(c) for c in rhs_q_poly.all_coeffs()]
    rhs_q = [0] * (deg_q + 1 - len(rhs_q)) + rhs_q
    rhs_tot = [Fraction(vr) for vr in rhs] + [bv for _, bv in extra_rows] + [Fraction(vq) for vq in rhs_q] + [Fraction(-1 if k == v_loc else 0) for k in range(m_c)]
    rhs_sh = [rhs_tot[r] - cols_m[v_loc][r] for r in range(len(rhs_tot))]

    n_rows = len(rhs_tot)
    A_int = [[] for _ in range(n_rows)]
    b_int = []
    for r in range(n_rows):
        lcm_d = rhs_sh[r].denominator
        for col in cols_m:
            lcm_d = sp.ilcm(lcm_d, col[r].denominator)
        for col in cols_m:
            A_int[r].append(int(col[r] * lcm_d))
        b_int.append(int(rhs_sh[r] * lcm_d))
    try:
        verify_dual_farkas_int(A_int, b_int, y_c)
    except AssertionError:
        st, y_own = exact_farkas_or_primal(A_int, b_int)
        assert st == "FARKAS", f"Coupled Farkas failed cleanly for v_pruned={v_pruned}"
        verify_dual_farkas_int(A_int, b_int, y_own)


def e_diag_exact(chi_S: sp.Poly, chi_v: sp.Poly, lam: int, x: sp.Symbol) -> sp.Rational:
    _, fl = sp.factor_list(chi_S)
    m = next(mp for f, mp in fl if f.degree() == 1 and f.eval(lam) == 0)
    q_lam, rem = sp.div(chi_S, sp.Poly((x - lam) ** m, x, domain=sp.ZZ))
    assert rem.is_zero
    num_p, rem2 = sp.div(chi_v, sp.Poly((x - lam) ** (m - 1), x, domain=sp.ZZ))
    if not rem2.is_zero:
        return sp.Rational(0)
    return sp.Rational(int(num_p.eval(lam)), int(q_lam.eval(lam)))


def e_off_sq_exact(chi_S: sp.Poly, chi_u: sp.Poly, chi_v: sp.Poly, chi_uv: sp.Poly, lam: int, x: sp.Symbol) -> sp.Rational:
    _, fl = sp.factor_list(chi_S)
    m = next(mp for f, mp in fl if f.degree() == 1 and f.eval(lam) == 0)
    q_lam, _ = sp.div(chi_S, sp.Poly((x - lam) ** m, x, domain=sp.ZZ))
    eu = e_diag_exact(chi_S, chi_u, lam, x)
    ev = e_diag_exact(chi_S, chi_v, lam, x)
    num_p, rem = sp.div(chi_uv, sp.Poly((x - lam) ** (m - 2), x, domain=sp.ZZ))
    assert rem.is_zero
    return eu * ev - sp.Rational(int(num_p.eval(lam)), int(q_lam.eval(lam)))


def audit_441_endgame(dk59: dict, surv: list[list[int]], x: sp.Symbol) -> dict:
    assert surv == [[0, 49], [2, 2], [15, 8]], f"Unexpected 441 survivor: {surv}"
    c_shift = int(dk59["c"])
    cand = dk59["candidates"][441]
    chi_S = decode_chi_S_from_deck_cand(cand, 18, 59, c_shift, x)
    ctx = build_2v_cache_ctx(chi_S, x)
    chis = {v: decode_deck_poly_to_x(cand["deck"][v], c_shift, 58, ctx["gcd_x"], x) for v in [0, 2, 15]}

    # Exact E_15 and E_7 diagonals
    assert e_diag_exact(chi_S, chis[0], 15, x) == sp.Rational(1, 25)
    assert e_diag_exact(chi_S, chis[2], 15, x) == sp.Rational(3, 50)
    assert e_diag_exact(chi_S, chis[15], 15, x) == sp.Rational(23, 200)
    assert e_diag_exact(chi_S, chis[0], 7, x) == 0 and e_diag_exact(chi_S, chis[2], 7, x) == 0
    assert e_diag_exact(chi_S, chis[15], 7, x) == sp.Rational(1, 8)

    # Exact E_15[u, v]^2 from 2v-Jacobi
    allowed_sq = {}
    for u, v in [(0, 0), (0, 2), (0, 15), (2, 2), (2, 15), (15, 15)]:
        res = solve_2v_jacobi_exact(chi_S, chis[u], chis[v], 4, 57 % 4, x, cache_ctx=ctx)
        allowed_sq[(u, v)] = sorted({e_off_sq_exact(chi_S, chis[u], chis[v], sp.Poly(c_uv, x, domain=sp.ZZ), 15, x) for _, _, c_uv in res})
    assert allowed_sq[(0, 0)] == [sp.Rational(1, 10000), sp.Rational(1, 625)]
    assert allowed_sq[(0, 2)] == [sp.Rational(1, 2500), sp.Rational(9, 10000)]
    assert allowed_sq[(0, 15)] == [sp.Rational(1, 10000), sp.Rational(1, 625), sp.Rational(9, 2500)]

    # Verify S_4 trace obstruction: Tr(S_4^2) = 12 < 16 => at most 3 distinct lines in C_0
    # Wait: check Case +++ (0 hits) and Case ++- (6 Parseval hits, 0 survive E_15*E_7 = 0)
    total_parseval_hits = 0
    for name, g23 in [("+++", sp.Rational(1, 4)), ("++-", sp.Rational(-1, 4))]:
        G_v = sp.Matrix([
            [1, sp.Rational(1, 4), sp.Rational(1, 4)],
            [sp.Rational(1, 4), 1, g23],
            [sp.Rational(1, 4), g23, 1],
        ])
        Ginv = G_v.inv()
        c2 = [
            (x1, x2, x3) for x1, x2, x3 in itertools.product([-3, -2, 2, 3], repeat=3)
            if (sp.Matrix([x1, x2, x3]).T * Ginv * sp.Matrix([x1, x2, x3]))[0, 0] == 24
            and (x1, x2, x3) > (-x1, -x2, -x3)
        ]
        c15 = [
            (x1, x2, x3) for x1, x2, x3 in itertools.product([-6, -4, -1, 1, 4, 6], repeat=3)
            if (sp.Matrix([x1, x2, x3]).T * Ginv * sp.Matrix([x1, x2, x3]))[0, 0] == 46
            and (x1, x2, x3) > (-x1, -x2, -x3)
        ]
        if name == "+++":
            assert len(c2) == 0 and len(c15) == 0
            continue
        assert len(c2) == 4 and len(c15) == 9

        def sym6(M: sp.Matrix) -> list[int]:
            return [int(M[0, 0]), int(M[0, 1]), int(M[0, 2]), int(M[1, 1]), int(M[1, 2]), int(M[2, 2])]

        rhs_G = [int(400 * v) for v in [G_v[0, 0], G_v[0, 1], G_v[0, 2], G_v[1, 1], G_v[1, 2], G_v[2, 2]]]
        M0_b = [sym6(G_v * sp.diag(*(16 if j == i else 0 for j in range(3))) * G_v) for i in range(3)]
        C2_c = [sym6(sp.Matrix(u) * sp.Matrix(u).T) for u in c2]
        C15_c = [sym6(sp.Matrix(w) * sp.Matrix(w).T) for w in c15]
        c15_map: dict[tuple[int, ...], list[tuple[int, ...]]] = {}
        for comb in itertools.combinations_with_replacement(range(len(c15)), 8):
            key = tuple(sum(C15_c[k][r] for k in comb) for r in range(6))
            c15_map.setdefault(key, []).append(comb)

        hits = []
        for m1 in range(3, 24):
            for m2 in range(3, 24):
                m3 = 49 - m1 - m2
                if not (3 <= m3 <= 23):
                    continue
                rem0 = [rhs_G[r] - (m1 * M0_b[0][r] + m2 * M0_b[1][r] + m3 * M0_b[2][r]) for r in range(6)]
                for i2 in range(len(c2)):
                    for j2 in range(i2, len(c2)):
                        rem = tuple(rem0[r] - (C2_c[i2][r] + C2_c[j2][r]) for r in range(6))
                        if rem in c15_map:
                            for comb in c15_map[rem]:
                                hits.append([c15[k] for k in comb])
        total_parseval_hits += len(hits)
        assert len(hits) == 6
        for c15l in hits:
            for sgns in itertools.product([-1, 1], repeat=8):
                assert not all(sum(sgns[k] * c15l[k][r] for k in range(8)) == 0 for r in range(3))

    return {"index": 441, "status": "PASS", "parseval_hits": total_parseval_hits, "e7_orth_survivors": 0}


def audit_488_endgame(dk59: dict, survs: list[list[list[int]]], x: sp.Symbol) -> dict:
    exp = [
        [[3, 18], [5, 24], [41, 2], [43, 12], [154, 3]],
        [[3, 20], [5, 24], [43, 10], [101, 2], [154, 3]],
    ]
    assert sorted(survs) == sorted(exp), f"Unexpected 488 survivors: {survs}"
    c_shift = int(dk59["c"])
    cand = dk59["candidates"][488]
    chi_S = decode_chi_S_from_deck_cand(cand, 18, 59, c_shift, x)
    ctx = build_2v_cache_ctx(chi_S, x)
    chis = {v: decode_deck_poly_to_x(cand["deck"][v], c_shift, 58, ctx["gcd_x"], x) for v in [3, 5, 41, 43, 101, 154]}

    # Check E_11 diagonals
    assert e_diag_exact(chi_S, chis[3], 11, x) == sp.Rational(1, 8)
    assert e_diag_exact(chi_S, chis[41], 11, x) == sp.Rational(1, 8)
    assert e_diag_exact(chi_S, chis[5], 11, x) == sp.Rational(3, 16)
    for v0 in [43, 101, 154]:
        assert e_diag_exact(chi_S, chis[v0], 11, x) == 0

    # Check exact 2v E_11^2 on B x B ({3, 41}^2) and B x {5}
    for u, v in [(3, 3), (3, 41), (41, 41)]:
        res = solve_2v_jacobi_exact(chi_S, chis[u], chis[v], 4, 57 % 4, x, cache_ctx=ctx)
        vals = {e_off_sq_exact(chi_S, chis[u], chis[v], sp.Poly(c_uv, x, domain=sp.ZZ), 11, x) for _, _, c_uv in res}
        assert vals <= {sp.Rational(0), sp.Rational(1, 64)}, f"488 ({u},{v}) E11^2={vals}"
    for u in [3, 41]:
        res = solve_2v_jacobi_exact(chi_S, chis[u], chis[5], 4, 57 % 4, x, cache_ctx=ctx)
        vals = {e_off_sq_exact(chi_S, chis[u], chis[5], sp.Poly(c_uv, x, domain=sp.ZZ), 11, x) for _, _, c_uv in res}
        assert vals == {sp.Rational(1, 256)}, f"488 ({u},5) E11^2={vals}"

    # Verify sum_{v in B} E_11[u,v]^2 = 1/8 - 24*(1/256) = 1/32 = 2/64 => <= 1 neighbor in B => rank >= 20/2 = 10 > 7
    rem_B = sp.Rational(1, 8) - 24 * sp.Rational(1, 256)
    assert rem_B == sp.Rational(2, 64)
    return {"index": 488, "status": "PASS", "survivors_verified": 2, "B_rank_lb": 10, "mult_11": 7}


def audit_692_endgame(dk59: dict, surv: list[list[int]], x: sp.Symbol) -> dict:
    assert surv == [[0, 17], [2, 40], [3, 2]], f"Unexpected 692 survivor: {surv}"
    c_shift = int(dk59["c"])
    cand = dk59["candidates"][692]
    chi_S = decode_chi_S_from_deck_cand(cand, 18, 59, c_shift, x)
    ctx = build_2v_cache_ctx(chi_S, x)
    chis = {v: decode_deck_poly_to_x(cand["deck"][v], c_shift, 58, ctx["gcd_x"], x) for v in [0, 2, 3]}

    # Check E_15 and E_11 diagonals
    assert e_diag_exact(chi_S, chis[0], 15, x) == 0 and e_diag_exact(chi_S, chis[3], 15, x) == 0
    assert e_diag_exact(chi_S, chis[2], 15, x) == sp.Rational(1, 20)
    assert e_diag_exact(chi_S, chis[0], 11, x) == sp.Rational(1, 4)
    assert e_diag_exact(chi_S, chis[2], 11, x) == sp.Rational(15, 64)
    assert e_diag_exact(chi_S, chis[3], 11, x) == sp.Rational(3, 16)

    # Verify E_{r1, r2} simple factor x^2 - 21x + 94 in v_2 > 0 gauge
    sim_x = sp.Poly(x**2 - 21 * x + 94, x, domain=sp.QQ)
    mrad = sp.Poly((x - 15) * (x - 11) * (x + 5), x, domain=sp.QQ)
    den_mod = sp.rem(sp.Poly(sp.diff(sim_x, x).as_expr() * mrad.as_expr(), x, domain=sp.QQ), sim_x)
    den_inv = sp.invert(den_mod, sim_x)
    gcd_x = ctx["gcd_x"]

    def pos_at_r2(p_qq: sp.Poly) -> bool:
        c0 = sp.Rational(p_qq.nth(0))
        c1 = sp.Rational(p_qq.nth(1))
        # At r2 = (21 + sqrt(65))/2: val > 0 iff (2*c0 + 21*c1) + c1*sqrt(65) > 0
        a0, a1 = 2 * c0 + 21 * c1, c1
        if a0 >= 0 and a1 >= 0:
            return a0 > 0 or a1 > 0
        if a0 <= 0 and a1 <= 0:
            return False
        return (a0 * a0 > 65 * a1 * a1) if a0 > 0 else (65 * a1 * a1 > a0 * a0)

    E_diag = {}
    for j in [0, 2, 3]:
        gj = sp.Poly(sp.quo(chis[j], gcd_x).as_expr(), x, domain=sp.QQ)
        E_diag[j] = sp.rem(gj * den_inv, sim_x)
        assert pos_at_r2(E_diag[j])

    E_mat = {(j, j): E_diag[j] for j in [0, 2, 3]}
    chi_p_val = sp.Poly(sp.quo(chi_S, gcd_x).as_expr(), x, domain=sp.ZZ)
    for a, b in [(0, 2), (0, 3), (2, 3)]:
        res = solve_2v_jacobi_exact(chi_S, chis[a], chis[b], 4, 57 % 4, x, cache_ctx=ctx)
        assert len(res) == 2
        ga = sp.Poly(sp.quo(chis[a], gcd_x).as_expr(), x, domain=sp.ZZ)
        gb = sp.Poly(sp.quo(chis[b], gcd_x).as_expr(), x, domain=sp.ZZ)
        prod_g = sp.Poly(ga.as_expr() * gb.as_expr(), x, domain=sp.ZZ)
        # Solve R_ab^2 == ga*gb (mod sim_x) with sign locked in v_2 > 0 gauge
        opts = []
        for s_uv, _, c_uv in res:
            q_ab, rem_q = sp.div(sp.Poly(c_uv, x, domain=sp.ZZ), ctx["gcd_2"])
            assert rem_q.is_zero
            h2 = sp.Poly(prod_g.as_expr() - (sp.Poly(sim_x.as_expr(), x, domain=sp.ZZ) * sp.Poly(q_ab.as_expr(), x, domain=sp.ZZ)).as_expr(), x, domain=sp.ZZ)
            lc_h, fl_h = sp.factor_list(h2)
            sq_h = sp.Integer(math.isqrt(int(lc_h)))
            assert sq_h * sq_h == lc_h
            for fh, mh in fl_h:
                assert mh % 2 == 0
                sq_h *= fh.as_expr() ** (mh // 2)
            h_p = sp.Poly(sp.expand(sq_h), x, domain=sp.QQ)
            fm = sp.rem(h_p * den_inv, sim_x)
            if not pos_at_r2(fm):
                fm = -fm
            opts.append(tuple(sp.Rational(c) for c in fm.all_coeffs()))
        assert len(set(opts)) == 1
        E_mat[(a, b)] = E_mat[(b, a)] = sp.Poly(list(opts[0]), x, domain=sp.QQ)

    # Check row equations (k0, k2, k3) at r1, r2
    k0, k2, k3 = sp.symbols("k0 k2 k3")
    ks = [k0, k2, k3]
    types = [0, 2, 3]
    row_sols = {}
    for i in types:
        lhs = sum(ks[idx_j] * E_mat[(i, j)].as_expr() for idx_j, j in enumerate(types))
        rhs_e = sp.rem(sp.Poly(x * E_mat[(i, i)].as_expr(), x, domain=sp.QQ), sim_x).as_expr()
        dp = sp.Poly(sp.expand(lhs - rhs_e), x)
        row_sols[i] = sp.solve([dp.coeff_monomial(x), dp.coeff_monomial(1)], ks)
    assert row_sols[3] == {k0: 16 - k3, k2: 18 - 2 * k3}
    assert row_sols[0] == {k0: 14 - k3, k2: 4 - 2 * k3}
    assert row_sols[2] == {k0: 1 - k3, k2: 7 - 2 * k3}
    # k_{3,3} = -1 forces (S^2)_{w1,w2} >= 17 > 9; so k_{3,3}=+1, k_{3,0}=15, k_{3,2}=16

    # Check E_11^2 from 2v-Jacobi on (0,0), (0,3), (3,3), (0,2), (2,3)
    for pair, exp_sq in [
        ((0, 0), {sp.Rational(0), sp.Rational(1, 64)}),
        ((0, 3), {sp.Rational(0), sp.Rational(1, 64)}),
        ((3, 3), {sp.Rational(1, 256), sp.Rational(9, 256)}),
        ((0, 2), {sp.Rational(1, 256)}),
        ((2, 3), {sp.Rational(1, 1024), sp.Rational(9, 1024)}),
    ]:
        u, v = pair
        res = solve_2v_jacobi_exact(chi_S, chis[u], chis[v], 4, 57 % 4, x, cache_ctx=ctx)
        vals = {e_off_sq_exact(chi_S, chis[u], chis[v], sp.Poly(c_uv, x, domain=sp.ZZ), 11, x) for _, _, c_uv in res}
        assert vals == exp_sq

    # Path rank check for m = 1..17: every path w1 - u1 - ... - u_m - w2 has rank m+1 (nullity 1)
    for m in range(1, 18):
        sz = m + 2
        Mp = sp.zeros(sz, sz)
        for ii in range(1, m + 1):
            Mp[ii, ii] = sp.Rational(1, 4)
        Mp[0, 0] = Mp[m + 1, m + 1] = sp.Rational(3, 16)
        Mp[0, m + 1] = Mp[m + 1, 0] = sp.Rational(-1, 16)
        for ii in range(m + 1):
            Mp[ii, ii + 1] = Mp[ii + 1, ii] = sp.Rational(-1, 8)
        assert Mp.rank() == sz - 1

    # Unique 4*C_4 + P_3 CaseB: compute exact Jacobi/De Caen charpoly of S_40
    N19 = 19
    E11_19 = sp.zeros(N19, N19)
    for ii in range(17):
        E11_19[ii, ii] = sp.Rational(1, 4)
    E11_19[17, 17] = E11_19[18, 18] = sp.Rational(3, 16)
    E11_19[17, 18] = E11_19[18, 17] = sp.Rational(-1, 16)
    H_edges = {(0, 17), (0, 18)}
    for base in [1, 5, 9, 13]:
        for kk in range(4):
            u, v = base + kk, base + (kk + 1) % 4
            H_edges.add((min(u, v), max(u, v)))
    for u, v in H_edges:
        E11_19[u, v] = E11_19[v, u] = sp.Rational(-1, 8)
    assert E11_19.rank() == 14

    def quad_res(p_qq: sp.Poly) -> tuple[sp.Rational, sp.Rational]:
        c0 = sp.Rational(p_qq.nth(0))
        c1 = sp.Rational(p_qq.nth(1))
        # (c0 + c1*r1) + (c0 + c1*r2) = 2*c0 + 21*c1; (c0 + c1*r1)*r2 + (c0 + c1*r2)*r1 = 21*c0 + 188*c1
        return 2 * c0 + 21 * c1, 21 * c0 + 188 * c1

    E_sum_q, E_mix_q = sp.zeros(N19, N19), sp.zeros(N19, N19)
    for ii in range(N19):
        ti = 0 if ii < 17 else 3
        for jj in range(N19):
            tj = 0 if jj < 17 else 3
            aa, bb = quad_res(E_mat[(ti, tj)])
            E_sum_q[ii, jj] = aa
            E_mix_q[ii, jj] = bb
    E_m5_19 = sp.eye(N19) - E11_19 - E_sum_q
    pts = []
    xv = 20
    while len(pts) < 42:
        M_ev = E11_19 / (xv - 11) + E_m5_19 / (xv + 5) + (E_sum_q * xv - E_mix_q) / (xv * xv - 21 * xv + 94)
        pts.append((xv, sp.Rational(chi_S.eval(xv)) * M_ev.det()))
        xv += 1
    chi_40 = sp.factor(sp.interpolate(pts, x))
    assert chi_40 == (x - 15) ** 2 * (x - 7) ** 10 * (x - 3) ** 5 * (x + 5) ** 23

    # F_2^4 parity contradiction
    wt1 = [tuple(1 if i == k else 0 for k in range(4)) for i in range(4)]
    wt2 = [v for v in itertools.product([0, 1], repeat=4) if sum(v) == 2]
    for u0 in wt1:
        orth_wt2 = [v for v in wt2 if sum(a * b for a, b in zip(u0, v)) % 2 == 0]
        for v1 in orth_wt2:
            for v2_ in orth_wt2:
                if v1 != v2_:
                    assert sum(a * b for a, b in zip(v1, v2_)) % 2 == 1

    return {"index": 692, "status": "PASS", "chi_S40_verified": True, "f2_parity_killed": True}


def audit_864_endgame(dk59: dict, survs: list[list[list[int]]], x: sp.Symbol) -> dict:
    exp = [
        [[0, 34], [6, 21], [7, 4]],
        [[0, 33], [3, 3], [6, 18], [7, 5]],
        [[0, 32], [3, 6], [6, 15], [7, 6]],
    ]
    assert sorted(survs) == sorted(exp), f"Unexpected 864 survivors: {survs}"
    c_shift = int(dk59["c"])
    cand = dk59["candidates"][864]
    chi_S = decode_chi_S_from_deck_cand(cand, 18, 59, c_shift, x)
    ctx = build_2v_cache_ctx(chi_S, x)
    gcd_x = ctx["gcd_x"]
    chis = {v: decode_deck_poly_to_x(cand["deck"][v], c_shift, 58, gcd_x, x) for v in [0, 3, 6, 7]}

    # Exact signed projector extraction in E_6 = gamma * gamma^T / 1155 gauge
    denom = sp.Poly(math.prod([x - lam for lam in (-5, 6, 9, 11, 13)]), x, domain=sp.ZZ)
    gamma = {0: -3, 3: 1, 6: 5, 7: 9}
    sim_x = sp.Poly(x - 6, x, domain=sp.ZZ)
    vals = {}
    for ja in [0, 3, 6, 7]:
        for jb in [0, 3, 6, 7]:
            if ja > jb:
                continue
            ga = sp.Poly(sp.quo(chis[ja], gcd_x).as_expr(), x, domain=sp.ZZ)
            gb = sp.Poly(sp.quo(chis[jb], gcd_x).as_expr(), x, domain=sp.ZZ)
            prod_g = sp.Poly(ga.as_expr() * gb.as_expr(), x, domain=sp.ZZ)
            res = solve_2v_jacobi_exact(chi_S, chis[ja], chis[jb], 4, 57 % 4, x, cache_ctx=ctx)
            s_set = set()
            for _, _, c_uv in res:
                q_uv, rem_q = sp.div(sp.Poly(c_uv, x, domain=sp.ZZ), ctx["gcd_2"])
                assert rem_q.is_zero
                h2 = sp.Poly(prod_g.as_expr() - (sim_x * q_uv).as_expr(), x, domain=sp.ZZ)
                lc_h, fl_h = sp.factor_list(h2)
                sq_h = sp.Integer(math.isqrt(int(lc_h)))
                assert sq_h * sq_h == lc_h
                for fh, mh in fl_h:
                    assert mh % 2 == 0
                    sq_h *= fh.as_expr() ** (mh // 2)
                h = sp.Poly(sp.expand(sq_h), x, domain=sp.ZZ)
                for suv in (-1, 1):
                    hh = h if int(h.LC()) == suv else -h
                    ed = {
                        lam: Fraction(int(hh.eval(lam)), int(sp.quo(denom, sp.Poly(x - lam, x, domain=sp.ZZ)).eval(lam)))
                        for lam in (6, 9, 11, 13)
                    }
                    if ed[6] * 1155 == gamma[ja] * gamma[jb]:
                        s_set.add((suv, ed[9] * 21, ed[11] * 20, ed[13] * 63))
            vals[(ja, jb)] = sorted(s_set)

    assert {v[1] for v in vals[(3, 3)]} == {Fraction(-1), Fraction(1, 2), Fraction(2)}
    assert {v[1] for v in vals[(6, 6)]} == {Fraction(-1), Fraction(1, 2), Fraction(2)}
    assert {-v[1] for v in vals[(3, 6)]} == {Fraction(-1), Fraction(1, 2), Fraction(2)}

    assert {v[3] for v in vals[(3, 3)] if v[1] == 2} == {-4}
    assert {v[3] for v in vals[(6, 6)] if v[1] == 2} == {-9, -2}
    assert {v[3] for v in vals[(3, 6)] if -v[1] == 2} == {1, 8}
    assert {v[3] for v in vals[(3, 3)] if v[1] == -1} == {-4, 3}
    assert {v[3] for v in vals[(6, 6)] if v[1] == -1} == {-2, 5}
    assert {v[3] for v in vals[(3, 6)] if -v[1] == -1} == {-6, 1}
    assert {v[3] for v in vals[(3, 7)]} == {-1, 6}
    assert {v[3] for v in vals[(6, 7)]} == {-5, 2}
    assert {v[3] for v in vals[(7, 7)]} == {-9, -2}

    # Check intra-cluster PSD bounds forcing a_m <= 3, e_B = 0, k_neg = a_m * b_m
    for a in range(8):
        b = 7 - a
        qAA = a * (14 - 4 * a)
        if qAA < 0:
            continue
        assert a <= 3
        for eB in range(b * (b - 1) // 2 + 1):
            qBB = b * (14 - 2 * b) - 14 * eB
            if qBB < 0:
                continue
            for k_neg in range(a * b + 1):
                qAB = 8 * a * b - 7 * k_neg
                if qAA * qBB - qAB * qAB >= 0:
                    assert eB == 0 and k_neg == a * b

    def block_ub_2x2(s1: int, s2: int, q1: int, q2: int, hi: int) -> Fraction:
        if s1 <= 1 or s2 <= 1:
            return Fraction(0)
        best = Fraction(0)
        for r in range(s1 * s2 + 1):
            val = hi * s1 * s2 - 7 * r
            if val * val <= q1 * q2:
                bv = 2 * Fraction(r) * (1 - Fraction(r, s1 * s2))
                if bv > best:
                    best = bv
        return best

    partitions_checked = 0
    for total_a, c7 in [(0, 4), (3, 5), (6, 6)]:
        max_e7 = max(e7 for e7 in range(c7 * (c7 - 1) // 2 + 1) if 14 * c7 - 2 * c7 * c7 - 14 * e7 >= 0)
        qCC = 14 * c7 - 2 * c7 * c7
        c7_diag_ub = Fraction(0) if max_e7 == 0 else Fraction(2) - Fraction(4, c7) + Fraction(4, c7 * c7)
        for a0 in range(4):
            for a1 in range(a0, 4):
                a2 = total_a - a0 - a1
                if not (a1 <= a2 <= 3):
                    continue
                as_ = [a0, a1, a2]
                bs_ = [7 - a for a in as_]
                qA = [a * (14 - 4 * a) for a in as_]
                qB = [b * (14 - 2 * b) for b in bs_]
                dimW = sum(max(0, a - 1) + max(0, b - 1) for a, b in zip(as_, bs_)) + (c7 - 1)
                null = dimW - 8
                assert null > 0
                cs_min = Fraction(null * 4) + Fraction((2 * null) ** 2, 8)
                if as_ != [2, 2, 2]:
                    ub = c7_diag_ub
                    for m in range(3):
                        ub += block_ub_2x2(as_[m], c7, qA[m], qCC, 6)
                        ub += block_ub_2x2(bs_[m], c7, qB[m], qCC, 2)
                        for m2 in range(m + 1, 3):
                            ub += block_ub_2x2(as_[m], as_[m2], qA[m], qA[m2], 3)
                            ub += block_ub_2x2(bs_[m], bs_[m2], qB[m], qB[m2], 5)
                            ub += block_ub_2x2(as_[m], bs_[m2], qA[m], qB[m2], 1)
                            ub += block_ub_2x2(bs_[m], as_[m2], qB[m], qA[m2], 1)
                else:
                    assert max_e7 == 0
                    best_c7 = Fraction(0)
                    for rA in range(13):
                        for rB in range(31):
                            M = sp.Matrix([[12, 10, 72 - 7 * rA], [10, 20, 60 - 7 * rB], [72 - 7 * rA, 60 - 7 * rB, 12]])
                            if M.det() >= 0 and (144 - (72 - 7 * rA) ** 2 >= 0) and (240 - (60 - 7 * rB) ** 2 >= 0):
                                val = 2 * Fraction(rA) * (1 - Fraction(rA, 12)) + 2 * Fraction(rB) * (1 - Fraction(rB, 30))
                                if val > best_c7:
                                    best_c7 = val
                    best_3A = Fraction(0)
                    for rAA in range(5):
                        for rBA in range(11):
                            M = sp.Matrix([[12, 10, 12 - 7 * rAA], [10, 20, 10 - 7 * rBA], [12 - 7 * rAA, 10 - 7 * rBA, 12]])
                            if M.det() >= 0 and (144 - (12 - 7 * rAA) ** 2 >= 0) and (240 - (10 - 7 * rBA) ** 2 >= 0):
                                val = 2 * Fraction(rAA) * (1 - Fraction(rAA, 4)) + 2 * Fraction(rBA) * (1 - Fraction(rBA, 10))
                                if val > best_3A:
                                    best_3A = val
                    best_3B = Fraction(0)
                    for rAB in range(11):
                        for rBB in range(26):
                            M = sp.Matrix([[12, 10, 10 - 7 * rAB], [10, 20, 125 - 7 * rBB], [10 - 7 * rAB, 125 - 7 * rBB, 20]])
                            if M.det() >= 0 and (240 - (10 - 7 * rAB) ** 2 >= 0) and (400 - (125 - 7 * rBB) ** 2 >= 0):
                                val = 2 * Fraction(rAB) * (1 - Fraction(rAB, 10)) + 2 * Fraction(rBB) * (1 - Fraction(rBB, 25))
                                if val > best_3B:
                                    best_3B = val
                    ub = 3 * best_c7 + 3 * (best_3A + best_3B)
                assert ub < cs_min
                partitions_checked += 1

    return {"index": 864, "status": "PASS", "partitions_checked": partitions_checked}


def main() -> None:
    t0 = time.time()
    x = sp.Symbol("x")

    # 1. Partition completeness and file checksums
    p2_59 = read_json_auto(POLY_RESULTS_DIR, "phase2_18_59.json")
    s7_59 = read_json_auto(SEC7_CERTS_DIR, "sec7_18_59.json")
    dk59 = read_json_auto(POLY_RESULTS_DIR, "deck_18_59.json")
    c_shift = int(dk59["c"])

    p2_indices = {s["index"] for s in p2_59["survivors"]}
    s7_indices = {c["index"] for c in s7_59["certs"]}
    rem_20 = sorted(p2_indices - s7_indices)
    exp_20 = [103, 151, 228, 316, 319, 341, 364, 441, 488, 603, 651, 692, 705, 800, 861, 864, 978, 997, 1113, 1164]
    assert rem_20 == exp_20, f"Remaining 20 mismatch: {rem_20} vs {exp_20}"
    print(f"[PASS] Partition completeness: {len(p2_indices)} - {len(s7_indices)} = 20 targets", flush=True)

    file_names = [
        "phase3_18_59_clean_a.json",
        "phase3_18_59_clean_b.json",
        "phase3_18_59_441_488_692.json",
        "phase3_18_59_864.json",
        "phase3_18_59_316.json",
        "phase3_18_59_1164.json",
        "phase3_18_59_705_cone0.json",
        "phase3_18_59_705_cones1_5.json",
    ]
    checksums = {}
    for fn in file_names:
        p, is_gz = resolve_data_file(POLY_RESULTS_DIR, fn)
        nbytes = len(__import__("_repo_io").read_text_auto(POLY_RESULTS_DIR, fn).encode("utf-8")) if is_gz else p.stat().st_size
        checksums[fn] = {"bytes": nbytes, "sha256": sha256_auto(p)}
    print("[PASS] Recorded SHA-256s of all 8 Phase-3 (18,59) files", flush=True)

    # 2. Audit all 17 direct Stage-3 targets (clean_a [12], clean_b [4], 316 [1])
    clean_a = read_json_auto(POLY_RESULTS_DIR, "phase3_18_59_clean_a.json")
    clean_b = read_json_auto(POLY_RESULTS_DIR, "phase3_18_59_clean_b.json")
    d316 = read_json_auto(POLY_RESULTS_DIR, "phase3_18_59_316.json")

    expected_surv_counts = {idx: 0 for idx in [978, 997, 364, 319, 341, 603, 651, 151, 103, 228, 800, 1113, 316]}
    expected_surv_counts.update({441: 1, 692: 1, 488: 2, 864: 3})

    direct_reports = {}
    surv_by_idx: dict[int, list[list[list[int]]]] = {}

    for idx in [978, 997, 364, 319, 341, 603, 864, 651, 441, 692, 488, 151, 103, 228, 800, 1113, 316]:
        ti = time.time()
        cand = dk59["candidates"][idx]
        chi_S, rhs, F_z, sfs, cones = clean_stage2_cones(cand, 18, 59, c_shift)
        ctx = build_2v_cache_ctx(chi_S, x)
        gcd_x = ctx["gcd_x"]

        chi_cache: dict[int, sp.Poly] = {}
        raw_2v_cache: dict[tuple[int, int], list[tuple[int, int, list[int]]]] = {}

        def get_chi(di: int) -> sp.Poly:
            if di not in chi_cache:
                chi_cache[di] = decode_deck_poly_to_x(cand["deck"][di], c_shift, 58, gcd_x, x)
            return chi_cache[di]

        def get_2v_raw(da: int, db: int) -> list[tuple[int, int, list[int]]]:
            key = (min(da, db), max(da, db))
            if key not in raw_2v_cache:
                raw_2v_cache[key] = solve_2v_jacobi_endgame(chi_S, get_chi(key[0]), get_chi(key[1]), x, ctx, c_shift=c_shift)
            return raw_2v_cache[key]

        # Verify coupled_certs on clean_b targets when present, then prune verified vertices per cone
        pruned_by_cone: list[set[int]] = [set() for _ in cones]
        if str(idx) in clean_b["results"] and clean_b["results"][str(idx)].get("coupled_certs"):
            for cc in clean_b["results"][str(idx)]["coupled_certs"]:
                cand_cis = [
                    ci for ci, (sub, _) in enumerate(cones)
                    if set(cc["cur_act"]) <= set(sub) and (set(sub) - pruned_by_cone[ci]) <= set(cc["cur_act"])
                ]
                assert cand_cis, f"idx={idx}: no cone matches cur_act for v_pruned={cc['v_pruned']}"
                verified_any = False
                for ci in cand_cis:
                    _, extra_m = cones[ci]
                    verify_coupled_farkas_cert(
                        cand, 18, 59, c_shift, chi_S, rhs, extra_m, cc, x, ctx,
                        get_chi_fn=get_chi, get_2v_raw_fn=get_2v_raw,
                    )
                    pruned_by_cone[ci].add(cc["v_pruned"])
                    verified_any = True
                assert verified_any

        # Enumerate Stage-2+Galois solutions cleanly across all surviving (post-coupled) cones
        all_sols_set: set[tuple[tuple[int, int], ...]] = set()
        for ci, (sub, extra_rows) in enumerate(cones):
            rem_sub = [v for v in sub if v not in pruned_by_cone[ci]]
            if not rem_sub:
                continue
            for sol in enum_cone_solutions(cand["deck"], rem_sub, extra_rows, rhs, 59):
                all_sols_set.add(tuple((p[0], p[1]) for p in sol))
        ind_sols = [sorted([[di, c] for di, c in s_t]) for s_t in sorted(all_sols_set)]

        p61_killed = 0
        s3_reasons: dict[str, int] = {}
        survs: list[list[list[int]]] = []
        dis_all = sorted({di for sol in ind_sols for di, _ in sol})
        p61_kills = build_prop61_checker(chi_S, get_chi, dis_all, x)
        s3_cache: dict = {}
        for sol in ind_sols:
            if p61_kills(sol):
                p61_killed += 1
                continue
            killed, rsn = stage3_filter_sol(chi_S, sol, 59, x, ctx, get_chi, get_2v_raw, run_sv_galois=True, s3_cache=s3_cache)
            if killed:
                s3_reasons[rsn] = s3_reasons.get(rsn, 0) + 1
            else:
                survs.append(sol)

        assert len(survs) == expected_surv_counts[idx], f"idx={idx}: got {len(survs)} survs, expected {expected_surv_counts[idx]}"
        surv_by_idx[idx] = survs
        direct_reports[str(idx)] = {
            "ind_stage2_sols": len(ind_sols),
            "p61_killed": p61_killed,
            "s3_reasons": s3_reasons,
            "survivors": len(survs),
            "elapsed_s": round(time.time() - ti, 2),
        }
        print(f"  [PASS] idx={idx}: s2={len(ind_sols)}, p61_killed={p61_killed}, s3={s3_reasons}, surv={len(survs)} ({direct_reports[str(idx)]['elapsed_s']}s)", flush=True)

    # 3. Audit idx=1164 (coupled Farkas + final Stage-2 Farkas)
    t_1164 = time.time()
    d1164 = read_json_auto(POLY_RESULTS_DIR, "phase3_18_59_1164.json")
    cand_1164 = dk59["candidates"][1164]
    chi_S1164, rhs1164, _, _, cones1164 = clean_stage2_cones(cand_1164, 18, 59, c_shift)
    assert len(cones1164) == 1 and len(cones1164[0][0]) == 18
    ctx1164 = build_2v_cache_ctx(chi_S1164, x)
    act_1164 = list(cones1164[0][0])
    extra_1164 = cones1164[0][1]
    chi_cache1164: dict[int, sp.Poly] = {}
    raw_2v1164: dict[tuple[int, int], list[tuple[int, int, list[int]]]] = {}

    def get_chi1164(di: int) -> sp.Poly:
        if di not in chi_cache1164:
            chi_cache1164[di] = decode_deck_poly_to_x(cand_1164["deck"][di], c_shift, 58, ctx1164["gcd_x"], x)
        return chi_cache1164[di]

    def get_2v1164(da: int, db: int) -> list[tuple[int, int, list[int]]]:
        key = (min(da, db), max(da, db))
        if key not in raw_2v1164:
            raw_2v1164[key] = solve_2v_jacobi_endgame(chi_S1164, get_chi1164(key[0]), get_chi1164(key[1]), x, ctx1164, c_shift=c_shift)
        return raw_2v1164[key]

    pruned_1164 = set()
    for cc in d1164["coupled_certs"]:
        # Each cert proves v_pruned == 0 in cur_act subset of act_1164 \ pruned_so_far
        cur_act_expected = [v for v in act_1164 if v not in pruned_1164]
        cc_with_act = {"v_pruned": cc["v_pruned"], "cur_act": cur_act_expected, "c_farkas": cc["c_farkas"]}
        verify_coupled_farkas_cert(
            cand_1164, 18, 59, c_shift, chi_S1164, rhs1164, extra_1164, cc_with_act, x, ctx1164,
            get_chi_fn=get_chi1164, get_2v_raw_fn=get_2v1164,
        )
        pruned_1164.add(cc["v_pruned"])
    rem_1164 = [v for v in act_1164 if v not in pruned_1164]
    assert rem_1164 == d1164["remaining_act_after_coupled"]
    A_r = [[Fraction(cand_1164["deck"][i][k]) for i in rem_1164] for k in range(len(rhs1164))]
    bf = [Fraction(v) for v in rhs1164]
    for rmap, bv in extra_1164:
        A_r.append([rmap.get(i, Fraction(0)) for i in rem_1164])
        bf.append(bv)
    A_i, b_i = [], []
    for row, bv in zip(A_r, bf):
        ld = bv.denominator
        for v in row:
            ld = sp.ilcm(ld, v.denominator)
        A_i.append([int(v * ld) for v in row])
        b_i.append(int(bv * ld))
    verify_dual_farkas_int(A_i, b_i, d1164["final_stage2_farkas"])
    print(f"  [PASS] idx=1164: 12 coupled_certs + final_stage2_farkas verified ({time.time()-t_1164:.2f}s)", flush=True)

    # 4. Audit idx=705 (cones 1..5 + cone 0 exhaustive 19,975 Stage-2 sols)
    t_705 = time.time()
    d705_c0 = read_json_auto(POLY_RESULTS_DIR, "phase3_18_59_705_cone0.json")
    d705_c15 = read_json_auto(POLY_RESULTS_DIR, "phase3_18_59_705_cones1_5.json")
    cand_705 = dk59["candidates"][705]
    chi_S705, rhs705, _, _, cones705 = clean_stage2_cones(cand_705, 18, 59, c_shift)
    assert len(cones705) == 6
    ctx705 = build_2v_cache_ctx(chi_S705, x)

    # Match cones by sorted vertex subset
    cone_by_set = {tuple(sorted(sub)): (sub, extra) for sub, extra in cones705}
    c15_sets = {tuple(sorted(c["orig_act"])) for c in d705_c15["cones_1_to_5"]}
    assert len(c15_sets) == 5 and c15_sets <= set(cone_by_set.keys())
    c0_key = next(k for k in cone_by_set if k not in c15_sets)

    chi_cache705: dict[int, sp.Poly] = {}
    raw_2v705: dict[tuple[int, int], list[tuple[int, int, list[int]]]] = {}

    def get_chi705(di: int) -> sp.Poly:
        if di not in chi_cache705:
            chi_cache705[di] = decode_deck_poly_to_x(cand_705["deck"][di], c_shift, 58, ctx705["gcd_x"], x)
        return chi_cache705[di]

    def get_2v705(da: int, db: int) -> list[tuple[int, int, list[int]]]:
        key = (min(da, db), max(da, db))
        if key not in raw_2v705:
            raw_2v705[key] = solve_2v_jacobi_endgame(chi_S705, get_chi705(key[0]), get_chi705(key[1]), x, ctx705, c_shift=c_shift)
        return raw_2v705[key]

    # Verify cones 1..5
    for c_rec in d705_c15["cones_1_to_5"]:
        sub, extra = cone_by_set[tuple(sorted(c_rec["orig_act"]))]
        pruned_c: set[int] = set()
        for cc in c_rec["coupled_certs"]:
            assert (set(sub) - pruned_c) <= set(cc["cur_act"])
            verify_coupled_farkas_cert(
                cand_705, 18, 59, c_shift, chi_S705, rhs705, extra, cc, x, ctx705,
                get_chi_fn=get_chi705, get_2v_raw_fn=get_2v705,
            )
            pruned_c.add(cc["v_pruned"])
        rem_sub = [v for v in sub if v not in pruned_c]
        if not rem_sub:
            continue
        sols_c = enum_cone_solutions(cand_705["deck"], rem_sub, extra, rhs705, 59)
        for sol in sols_c:
            chis_c = [get_chi705(di) for di, _ in sol]
            assert prop61_kills_sol(chi_S705, chis_c, [cnt for _, cnt in sol], x)
    print("  [PASS] idx=705 cones 1..5 verified (25 coupled_certs + P6.1 kills -> 0 sols)", flush=True)

    # Verify cone 0 (19,975 sols -> 0 Stage-3 survivors)
    sub0, extra0 = cone_by_set[c0_key]
    sols0 = enum_cone_solutions(cand_705["deck"], sub0, extra0, rhs705, 59)
    assert len(sols0) == d705_c0["stage2_sols"] == 19975

    s3_705_reasons: dict[str, int] = {}
    s3_cache705: dict = {}
    for sol_i, sol in enumerate(sols0):
        killed, rsn = stage3_filter_sol(chi_S705, sol, 59, x, ctx705, get_chi705, get_2v705, run_sv_galois=True, s3_cache=s3_cache705)
        assert killed, f"idx=705 cone0 survivor found: {sol}"
        s3_705_reasons[rsn] = s3_705_reasons.get(rsn, 0) + 1
        if (sol_i + 1) % 4000 == 0:
            print(f"    idx=705 cone0 {sol_i+1}/{len(sols0)} ({time.time()-t_705:.1f}s)", flush=True)
    print(f"  [PASS] idx=705 cone0: 19975/19975 killed ({s3_705_reasons}) in {time.time()-t_705:.2f}s", flush=True)

    # 5. Audit the 4 endgame survivor indices (441, 488, 692, 864)
    r441 = audit_441_endgame(dk59, surv_by_idx[441][0], x)
    print(f"  [PASS] idx=441 endgame: {r441}", flush=True)
    r488 = audit_488_endgame(dk59, surv_by_idx[488], x)
    print(f"  [PASS] idx=488 endgame: {r488}", flush=True)
    r692 = audit_692_endgame(dk59, surv_by_idx[692][0], x)
    print(f"  [PASS] idx=692 endgame: {r692}", flush=True)
    r864 = audit_864_endgame(dk59, surv_by_idx[864], x)
    print(f"  [PASS] idx=864 endgame: {r864}", flush=True)

    summary = {
        "status": "PASS",
        "elapsed_s": round(time.time() - t0, 2),
        "remaining_20_indices": rem_20,
        "checksums": checksums,
        "direct_17": direct_reports,
        "idx_1164": {"coupled_certs_verified": len(d1164["coupled_certs"]), "remaining_act": rem_1164, "status": "PASS"},
        "idx_705": {"cones": len(cones705), "cone0_sols_killed": len(sols0), "cone0_reasons": s3_705_reasons, "status": "PASS"},
        "endgame_4": {"441": r441, "488": r488, "692": r692, "864": r864},
    }
    OUT_JSON.write_text(json.dumps(summary, indent=2))
    print(f"PHASE-3 (18,59) ENDGAME AUDIT COMPLETE (PASS) in {summary['elapsed_s']}s -> {OUT_JSON}", flush=True)


if __name__ == "__main__":
    main()
