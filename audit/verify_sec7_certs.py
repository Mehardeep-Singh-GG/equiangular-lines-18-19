"""Independent exact-arithmetic audit of ALL 77 Eulerian and Galois elimination certificates
in `certificates/sec7/` (1 in (18,60), 5 in (17,49), 5 in (19,74), 66 in (18,59)).

Zero code is reused from `compute/poly/` or `compute/search/`.
Uses pure Python Fraction / int / SymPy ZZ / QQ / QQ(alpha) exact arithmetic,
exact primitive integer Sturm root counting >= -5, exact CRootOf interlacing,
exact 2-adic congruences, odd-n Eulerian mod-4 gauge checks, Galois orthogonality,
exact number-field trace locking for M_locked / N_locked, exact Cauchy-Schwarz fixed-point
propagation, and exact Bland's-rule Two-Phase Simplex Farkas verification.
"""

from __future__ import annotations

from fractions import Fraction
import hashlib
import itertools
import json
import math
from pathlib import Path
import time
import sympy as sp

from verify_algebraist_sec7 import (
    check_galois_elimination,
    galois_rows_for_factor,
)
from verify_farkas import check_thm42_odd, exact_farkas_or_primal, poly_shift_linear
from verify_phase2_19_74 import solve_null_dim_0_or_1, square_classes_for_simple_factor
from verify_phase2_certs import compute_rhs_and_common
from verify_phase3_47_861 import decode_deck_poly_to_x, poly_real_rooted_ge_neg5
from verify_polys import count_real_roots_sqf, poly_eval_2tm1_asc, v2
from _repo_io import AUDIT_DIR, CERT_DIR, COMPUTE_POLY_RESULTS, read_json_auto, sha256_auto

CERTS_DIR = CERT_DIR / "sec7"
POLY_RESULTS_DIR = COMPUTE_POLY_RESULTS
OUT_JSON = AUDIT_DIR / "sec7_77_certs_audit.json"


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def verify_dual_farkas_int(A: list[list[int]], b: list[int], y: list[int]) -> None:
    """Verify exact integer Farkas certificate: y^T A >= 0 and y^T b < 0."""
    m = len(A)
    assert len(b) == m and len(y) == m
    ncols = len(A[0]) if m > 0 else 0
    for j in range(ncols):
        val = sum(y[i] * A[i][j] for i in range(m))
        assert val >= 0, f"Farkas failure at col {j}: y^T A_j = {val} < 0"
    yb = sum(y[i] * b[i] for i in range(m))
    assert yb < 0, f"Farkas failure: y^T b = {yb} >= 0"


def exact_interlaces_cached(rb_big, rs_small, deg_big: int, deg_small: int) -> bool:
    if len(rb_big) != deg_big or len(rs_small) != deg_small:
        return False
    for i, rsv in enumerate(rs_small):
        if not (rb_big[i] <= rsv <= rb_big[i + 1]):
            return False
    return True


def tight_upper_int_bound(poly_x: sp.Poly, x: sp.Symbol, start: int = 10) -> int:
    """Exact smallest integer x_hi >= start strictly larger than all real roots of poly_x."""
    y = sp.Symbol("_y_bnd")
    x_hi = start
    while True:
        if int(poly_x.eval(x_hi)) != 0:
            py = sp.Poly(sp.expand(poly_x.as_expr().subs(x, y + x_hi)), y, domain=sp.ZZ)
            # Check 0 roots >= 0 on square-free part
            _, sqf_facs = sp.sqf_list(py)
            has_ge = False
            for fac, _ in sqf_facs:
                tot, nonneg = count_real_roots_sqf([int(c) for c in fac.all_coeffs()])
                if nonneg > 0:
                    has_ge = True
                    break
            if not has_ge:
                return x_hi
        x_hi += 1


def list_poly_mul(a: list[int], b: list[int]) -> list[int]:
    if not a or not b:
        return [0]
    res = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                res[i + j] += ai * bj
    while len(res) > 1 and res[0] == 0:
        res.pop(0)
    return res


def list_poly_sub(a: list[int], b: list[int]) -> list[int]:
    la, lb = len(a), len(b)
    n = max(la, lb)
    pa = [0] * (n - la) + a
    pb = [0] * (n - lb) + b
    res = [pa[i] - pb[i] for i in range(n)]
    while len(res) > 1 and res[0] == 0:
        res.pop(0)
    return res


def list_poly_eval(a: list[int], x0: int) -> int:
    v = 0
    for c in a:
        v = v * x0 + c
    return v


def solve_2v_jacobi_exact(
    chi_S: sp.Poly,
    chi_u: sp.Poly,
    chi_v: sp.Poly,
    s2_step: int,
    s2_rem_mod: int,
    x: sp.Symbol,
    forced_linear_roots: tuple[int, ...] = (),
    cache_ctx: dict | None = None,
) -> list[tuple[int, int, list[int]]]:
    """Independent clean-room exact 2-vertex Jacobi solver supporting ANY Sim_x factor degree
    and diff in {0, 1, 2} (plus diff == 3 when forced_linear_roots has >= 1 root outside Sim_x).
    """
    if cache_ctx is None:
        cache_ctx = build_2v_cache_ctx(chi_S, x)

    gcd_x = cache_ctx["gcd_x"]
    gcd_2 = cache_ctx["gcd_2"]
    mrad_div = cache_ctx["mrad_div"]
    sim_x = cache_ctx["sim_x"]
    sim_facs = cache_ctx["sim_facs"]
    x_bound_hi = cache_ctx["x_bound_hi"]
    sim_hi = cache_ctx["sim_hi"]
    sim_m5 = cache_ctx["sim_m5"]
    sim_m1 = cache_ctx["sim_m1"]
    sim_p1 = cache_ctx["sim_p1"]
    gcd_2_m1 = cache_ctx["gcd_2_m1"]
    gcd_2_p1 = cache_ctx["gcd_2_p1"]
    gamma_1 = cache_ctx["gamma_1"]
    e_sim = cache_ctx["e_sim"]
    S1_sim = cache_ctx["S1_sim"]
    sim_desc = cache_ctx["sim_desc"]
    gcd_2_desc = cache_ctx["gcd_2_desc"]
    g2_2t_asc = cache_ctx["gcd_2_2t_asc"]

    n = chi_S.degree()
    m_ord = n - 2
    req_shift = m_ord if (m_ord % 2 == 0) else (m_ord - 1)
    req_mod = 1 << req_shift

    ga = sp.Poly(sp.quo(chi_u, gcd_x), x, domain=sp.ZZ)
    gb = sp.Poly(sp.quo(chi_v, gcd_x), x, domain=sp.ZZ)
    s = ga.degree() + 1
    diff = (s - 2) - e_sim
    deg_q_exp = m_ord - gcd_2.degree()

    prod_ab = sp.Poly(ga.as_expr() * gb.as_expr(), x, domain=sp.ZZ)
    crt_residues_per_fac: list[tuple[sp.Poly, list[sp.Poly]]] = []
    t = sp.Symbol("_t2v_all")
    for sf in sim_facs:
        rem_sf = sp.rem(prod_ab, sp.Poly(sf.as_expr(), x, domain=sp.QQ), domain=sp.QQ)
        if rem_sf.is_zero:
            crt_residues_per_fac.append((sf, [sp.Poly(0, x, domain=sp.QQ)]))
        elif sf.degree() == 1:
            r0 = -Fraction(int(sf.all_coeffs()[1]), int(sf.all_coeffs()[0]))
            val = Fraction(0)
            for c in rem_sf.all_coeffs():
                val = val * r0 + Fraction(int(c.p), int(c.q))
            sq = math.isqrt(val.numerator)
            assert val.denominator == 1 and sq * sq == val.numerator
            if sq == 0:
                crt_residues_per_fac.append((sf, [sp.Poly(0, x, domain=sp.QQ)]))
            else:
                crt_residues_per_fac.append((sf, [sp.Poly(sq, x, domain=sp.QQ), sp.Poly(-sq, x, domain=sp.QQ)]))
        else:
            alpha = sp.CRootOf(sf, 0)
            K = sp.QQ.algebraic_field(alpha)
            elem_K = K.zero
            for c in rem_sf.all_coeffs():
                elem_K = elem_K * K.unit + K.dom.convert(c)
            sq_poly = sp.Poly.from_dict({(2,): K.one, (0,): -elem_K}, t, domain=K)
            _, fl = sq_poly.factor_list()
            lins = [f for f, _ in fl if f.degree() == 1]
            if not lins:
                return []
            roots_sf = []
            for lf in lins:
                cs = lf.rep.all_coeffs()
                rk = K.exquo(-cs[1], cs[0])
                rp = sp.Poly([Fraction(int(v.numerator), int(v.denominator)) for v in rk.rep], x, domain=sp.QQ)
                if rp not in roots_sf:
                    roots_sf.append(rp)
            crt_residues_per_fac.append((sf, roots_sf))

    R_cands = []
    mods = [sf for sf, _ in crt_residues_per_fac]
    sim_q = sp.Poly(sim_x.as_expr(), x, domain=sp.QQ)
    for combo in itertools.product(*[rs for _, rs in crt_residues_per_fac]):
        cur_r = sp.Poly(0, x, domain=sp.QQ)
        cur_m = sp.Poly(1, x, domain=sp.QQ)
        for mi, ri in zip(mods, combo):
            mi_q = sp.Poly(mi.as_expr(), x, domain=sp.QQ)
            inv = sp.invert(cur_m, mi_q)
            k_poly = sp.rem((ri - cur_r) * inv, mi_q, domain=sp.QQ)
            cur_r = sp.Poly(cur_r.as_expr() + cur_m.as_expr() * k_poly.as_expr(), x, domain=sp.QQ)
            cur_m = sp.Poly(cur_m.as_expr() * mi_q.as_expr(), x, domain=sp.QQ)
        cur_r = sp.rem(cur_r, sim_q, domain=sp.QQ)
        if all(Fraction(c.p, c.q).denominator == 1 for c in cur_r.all_coeffs()):
            R_cands.append(sp.Poly(cur_r.as_expr(), x, domain=sp.ZZ))

    seen_R = set()
    uniq_R = []
    for rp in R_cands:
        t1 = tuple(int(c) for c in rp.all_coeffs())
        if t1 not in seen_R:
            seen_R.add(t1)
            uniq_R.append(rp)

    if not uniq_R:
        return []

    R_data = []
    prod_ab_expr = prod_ab.as_expr()
    for R_poly in uniq_R:
        M_poly, M_rem = sp.div(sp.Poly(prod_ab_expr - R_poly.as_expr() ** 2, x, domain=sp.ZZ), sim_x)
        if not M_rem.is_zero:
            continue
        R_desc = [int(c) for c in R_poly.all_coeffs()]
        M_desc = [int(c) for c in M_poly.all_coeffs()]
        R_data.append((
            R_poly,
            R_desc,
            M_desc,
            int(R_poly.eval(x_bound_hi)),
            int(R_poly.eval(-5)),
            int(R_poly.eval(-1)),
            int(R_poly.eval(1)),
            int(M_poly.eval(-1)),
            int(M_poly.eval(1)),
        ))

    if not R_data:
        return []

    # Cancel common gcd_2 factor from chi_u, chi_v, chi_uv to isolate roots on degree <= 9 polynomials!
    big_u_red = sp.Poly(mrad_div.as_expr() * ga.as_expr(), x, domain=sp.ZZ)
    big_v_red = sp.Poly(mrad_div.as_expr() * gb.as_expr(), x, domain=sp.ZZ)
    # Any linear factor (x - r)^m with m >= 2 in chi_u/gcd_2 or chi_v/gcd_2 forces q_uv(r) = 0 by Cauchy interlacing
    dbl_ints: set[int] = set()
    for poly_r in (big_u_red, big_v_red):
        for fr_p, mp_r in sp.factor_list(poly_r)[1]:
            if mp_r >= 2 and fr_p.degree() == 1 and int(fr_p.LC()) == 1:
                dbl_ints.add(int(-fr_p.nth(0)))
    dbl_list = sorted(dbl_ints)
    sim_dbl = [list_poly_eval(sim_desc, r) for r in dbl_list]
    R_dbl_map = [
        ([list_poly_eval(rd[1], r) for r in dbl_list], [list_poly_eval(rd[2], r) for r in dbl_list])
        for rd in R_data
    ]
    rb_u_red = big_u_red.real_roots()
    rb_v_red = big_v_red.real_roots()
    deg_u_red = big_u_red.degree()
    deg_v_red = big_v_red.degree()

    ga_hi = int(ga.eval(x_bound_hi))
    gb_hi = int(gb.eval(x_bound_hi))
    assert sim_hi > 0 and ga_hi >= 0 and gb_hi >= 0
    bnd_hi = math.isqrt(ga_hi * gb_hi) + 1

    ga_m5 = int(ga.eval(-5))
    gb_m5 = int(gb.eval(-5))
    deg_q = s - 2
    use_m5 = (sim_m5 != 0 and ((sim_m5 > 0) == (deg_q % 2 == 0)) and ga_m5 * gb_m5 >= 0)
    bnd_m5 = (math.isqrt(ga_m5 * gb_m5) + 1) if use_m5 else None

    s2_lo = -(n - 2)
    while (s2_lo - s2_rem_mod) % s2_step != 0:
        s2_lo += 1

    solutions = []

    def check_candidate(s_uv: int, s2_uv: int, Q_desc: list[int], R_poly: sp.Poly, R_desc: list[int], M_desc: list[int], R_m1: int, R_p1: int, M_m1: int, M_p1: int) -> None:
        Q_m1 = list_poly_eval(Q_desc, -1)
        q_uv_m1 = M_m1 - 2 * Q_m1 * R_m1 - Q_m1 * Q_m1 * sim_m1
        if (gcd_2_m1 * q_uv_m1) % req_mod != 0:
            return
        Q_p1 = list_poly_eval(Q_desc, 1)
        q_uv_p1 = M_p1 - 2 * Q_p1 * R_p1 - Q_p1 * Q_p1 * sim_p1
        if (gcd_2_p1 * q_uv_p1) % req_mod != 0:
            return
        if forced_linear_roots:
            for fr in forced_linear_roots:
                if list_poly_eval(Q_desc, fr) * list_poly_eval(sim_desc, fr) + list_poly_eval(R_desc, fr) != 0:
                    return
        # Pure Python integer polynomial q_uv_desc = M - 2*Q*R - Q^2*sim_x
        t1 = list_poly_mul([2 * c for c in Q_desc], R_desc)
        t2 = list_poly_mul(list_poly_mul(Q_desc, Q_desc), sim_desc)
        q_uv_desc = list_poly_sub(M_desc, list_poly_sub(t1, [-c for c in t2]))
        if len(q_uv_desc) - 1 != deg_q_exp or q_uv_desc[0] != 1:
            return
        # Exact ultra-fast necessary condition: all roots >= -5 => q_uv(y - 5) has strictly alternating signs!
        q_shifted = poly_shift_linear(q_uv_desc, 1, -5)
        for j_idx, c_val in enumerate(q_shifted):
            if j_idx % 2 == 0 and c_val < 0:
                return
            if j_idx % 2 == 1 and c_val > 0:
                return
        # Fast 2-adic polynomial check via precomputed gcd_2(2t-1) BEFORE SymPy Sturm/Poly
        q_2t_asc = poly_eval_2tm1_asc(q_uv_desc)
        b_asc = [0] * (len(g2_2t_asc) + len(q_2t_asc) - 1)
        for i_g, vg in enumerate(g2_2t_asc):
            if vg:
                for j_q, vq in enumerate(q_2t_asc):
                    b_asc[i_g + j_q] += vg * vq
        if m_ord % 2 == 0:
            if any(v2(bk) < m_ord for bk in b_asc):
                return
        else:
            if any(v2(bk) < (m_ord - 1) for bk in b_asc):
                return
            P_asc = [bk >> (m_ord - 1) for bk in b_asc]
            if not check_thm42_odd(P_asc, m_ord):
                return
        # Check exact real-rootedness >= -5 on small q_uv BEFORE touching degree-72 chi_uv
        q_uv = sp.Poly(q_uv_desc, x, domain=sp.ZZ)
        if not poly_real_rooted_ge_neg5(q_uv, x):
            return
        chi_uv_desc = list_poly_mul(gcd_2_desc, q_uv_desc)
        # Exact CRootOf interlacing on reduced degree <= 9 polynomials (100% equivalent to full chi_uv)
        rs_uv_red = q_uv.real_roots()
        if not (exact_interlaces_cached(rb_u_red, rs_uv_red, deg_u_red, deg_q_exp) and exact_interlaces_cached(rb_v_red, rs_uv_red, deg_v_red, deg_q_exp)):
            return
        solutions.append((s_uv, s2_uv, chi_uv_desc))

    if diff == 0:
        for s_uv in (1, -1):
            for R_poly, R_desc, M_desc, R_hi, R_m5, R_m1, R_p1, M_m1, M_p1 in R_data:
                r_top = int(R_poly.nth(e_sim - 1)) if e_sim >= 1 else 0
                s2_uv = r_top - s_uv * S1_sim + gamma_1 * s_uv
                if not (-(n - 2) <= s2_uv <= n - 2) or (s2_uv - s2_rem_mod) % s2_step != 0:
                    continue
                check_candidate(s_uv, s2_uv, [s_uv], R_poly, R_desc, M_desc, R_m1, R_p1, M_m1, M_p1)
    elif diff == 1:
        for s_uv in (1, -1):
            for s2_uv in range(s2_lo, n - 1, s2_step):
                q0 = s2_uv - gamma_1 * s_uv + s_uv * S1_sim
                Q_desc = [s_uv, q0]
                Q_hi = s_uv * x_bound_hi + q0
                Q_m5 = -5 * s_uv + q0
                for R_poly, R_desc, M_desc, R_hi, R_m5, R_m1, R_p1, M_m1, M_p1 in R_data:
                    if abs(Q_hi * sim_hi + R_hi) > bnd_hi:
                        continue
                    if use_m5 and abs(Q_m5 * sim_m5 + R_m5) > bnd_m5:
                        continue
                    check_candidate(s_uv, s2_uv, Q_desc, R_poly, R_desc, M_desc, R_m1, R_p1, M_m1, M_p1)
    elif diff == 2:
        for s_uv in (1, -1):
            for s2_uv in range(s2_lo, n - 1, s2_step):
                q1 = s2_uv - gamma_1 * s_uv + s_uv * S1_sim
                for idx_r, (R_poly, R_desc, M_desc, R_hi, R_m5, R_m1, R_p1, M_m1, M_p1) in enumerate(R_data):
                    base_hi = sim_hi * (s_uv * (x_bound_hi ** 2) + q1 * x_bound_hi) + R_hi
                    lo_q0 = math.ceil((-bnd_hi - base_hi) / sim_hi)
                    hi_q0 = math.floor((bnd_hi - base_hi) / sim_hi)
                    if use_m5:
                        base_m5 = sim_m5 * (s_uv * 25 - 5 * q1) + R_m5
                        lo2 = math.ceil((-bnd_m5 - base_m5) / abs(sim_m5)) if sim_m5 > 0 else math.ceil((-bnd_m5 + base_m5) / abs(sim_m5))
                        hi2 = math.floor((bnd_m5 - base_m5) / abs(sim_m5)) if sim_m5 > 0 else math.floor((bnd_m5 + base_m5) / abs(sim_m5))
                        lo_q0 = max(lo_q0, lo2)
                        hi_q0 = min(hi_q0, hi2)
                    if lo_q0 > hi_q0:
                        continue
                    Rd_vals, Md_vals = R_dbl_map[idx_r]
                    for q0 in range(lo_q0, hi_q0 + 1):
                        if dbl_list:
                            bad_d = False
                            for dk_i, rv in enumerate(dbl_list):
                                Q_r = s_uv * rv * rv + q1 * rv + q0
                                if Md_vals[dk_i] - 2 * Q_r * Rd_vals[dk_i] - Q_r * Q_r * sim_dbl[dk_i] != 0:
                                    bad_d = True
                                    break
                            if bad_d:
                                continue
                        check_candidate(s_uv, s2_uv, [s_uv, q1, q0], R_poly, R_desc, M_desc, R_m1, R_p1, M_m1, M_p1)
    elif diff == 3 and forced_linear_roots:
        rf = None
        for cand_r in forced_linear_roots:
            if int(sim_x.eval(cand_r)) != 0:
                rf = cand_r
                break
        assert rf is not None, f"diff=3 requires forced root outside Sim_x, got {forced_linear_roots}"
        sim_rf = int(sim_x.eval(rf))
        for s_uv in (1, -1):
            for s2_uv in range(s2_lo, n - 1, s2_step):
                q2 = s2_uv - gamma_1 * s_uv + s_uv * S1_sim
                for R_poly, R_desc, M_desc, R_hi, R_m5, R_m1, R_p1, M_m1, M_p1 in R_data:
                    R_rf = int(R_poly.eval(rf))
                    if R_rf % sim_rf != 0:
                        continue
                    q_rf_target = -R_rf // sim_rf
                    q0_const = q_rf_target - s_uv * (rf ** 3) - q2 * (rf ** 2)
                    c_hi = sim_hi * (x_bound_hi - rf)
                    base_hi = sim_hi * (s_uv * (x_bound_hi ** 3) + q2 * (x_bound_hi ** 2) + q0_const) + R_hi
                    lo_q1 = math.ceil((-bnd_hi - base_hi) / abs(c_hi)) if c_hi > 0 else math.ceil((-bnd_hi + base_hi) / abs(c_hi))
                    hi_q1 = math.floor((bnd_hi - base_hi) / abs(c_hi)) if c_hi > 0 else math.floor((bnd_hi + base_hi) / abs(c_hi))
                    if use_m5:
                        c_m5 = sim_m5 * (-5 - rf)
                        base_m5 = sim_m5 * (s_uv * (-125) + q2 * 25 + q0_const) + R_m5
                        lo2 = math.ceil((-bnd_m5 - base_m5) / abs(c_m5)) if c_m5 > 0 else math.ceil((-bnd_m5 + base_m5) / abs(c_m5))
                        hi2 = math.floor((bnd_m5 - base_m5) / abs(c_m5)) if c_m5 > 0 else math.floor((bnd_m5 + base_m5) / abs(c_m5))
                        lo_q1 = max(lo_q1, lo2)
                        hi_q1 = min(hi_q1, hi2)
                    if lo_q1 > hi_q1:
                        continue
                    for q1 in range(lo_q1, hi_q1 + 1):
                        q0 = q0_const - rf * q1
                        check_candidate(s_uv, s2_uv, [s_uv, q2, q1, q0], R_poly, R_desc, M_desc, R_m1, R_p1, M_m1, M_p1)
    else:
        raise NotImplementedError(f"Unsupported diff={diff} without forced root")

    return solutions


def build_2v_cache_ctx(chi_S: sp.Poly, x: sp.Symbol) -> dict:
    gcd_x = sp.gcd(chi_S, sp.diff(chi_S, x))
    gcd_2 = sp.gcd(gcd_x, sp.diff(gcd_x, x))
    mrad_div = sp.Poly(sp.quo(gcd_x, gcd_2), x, domain=sp.ZZ)
    _, fac_list = sp.factor_list(chi_S)
    sim_x = sp.Poly(1, x, domain=sp.ZZ)
    sim_facs = []
    for fac, mult in fac_list:
        if mult == 1:
            sim_x = sp.Poly(sim_x.as_expr() * fac.as_expr(), x, domain=sp.ZZ)
            sim_facs.append(fac)
    rad_S = sp.Poly(sim_x.as_expr() * mrad_div.as_expr(), x, domain=sp.ZZ)
    x_bound_hi = tight_upper_int_bound(rad_S, x, start=10)
    deg_g = gcd_x.degree()
    e_sim = sim_x.degree()
    return {
        "gcd_x": gcd_x,
        "gcd_2": gcd_2,
        "mrad_div": mrad_div,
        "sim_x": sim_x,
        "sim_facs": sim_facs,
        "x_bound_hi": x_bound_hi,
        "sim_hi": int(sim_x.eval(x_bound_hi)),
        "sim_m5": int(sim_x.eval(-5)),
        "sim_m1": int(sim_x.eval(-1)),
        "sim_p1": int(sim_x.eval(1)),
        "gcd_2_m1": int(gcd_2.eval(-1)),
        "gcd_2_p1": int(gcd_2.eval(1)),
        "gamma_1": int(gcd_x.all_coeffs()[1]) if deg_g >= 1 else 0,
        "e_sim": e_sim,
        "S1_sim": -int(sim_x.all_coeffs()[1]) if e_sim >= 1 else 0,
        "sim_desc": [int(c) for c in sim_x.all_coeffs()],
        "gcd_2_desc": [int(c) for c in gcd_2.all_coeffs()],
        "gcd_2_2t_asc": poly_eval_2tm1_asc([int(c) for c in gcd_2.all_coeffs()]),
    }


def decode_chi_S_from_deck_cand(cand: dict, d: int, n: int, c_shift: int, x: sp.Symbol) -> sp.Poly:
    w = sp.Symbol("w")
    bw = sp.Poly(cand["b"], w, domain=sp.ZZ)
    lc = int(bw.LC())
    chi_S = sp.Poly(((x + 5) ** (n - d)) * (2 ** d) * bw.as_expr().subs(w, (x - c_shift) / 2) / lc, x, domain=sp.ZZ)
    assert chi_S.LC() == 1 and chi_S.degree() == n
    return chi_S


def enumerate_galois_int_sols(cand: dict, d: int, n: int, c_shift: int) -> list[list[list[int]]]:
    """Independently enumerate ALL nonnegative integer solutions surviving Stage-2 square-class
    cliques + Theorem 7.1 mod-4 (for odd n) + Theorem 7.2 Galois orthogonality.
    """
    rhs, F_z, Gcd_z, _ = compute_rhs_and_common(cand["b"], d, n, c_shift)
    deck = cand["deck"]
    s = len(rhs)
    shift_t = -(c_shift + 1) // 2
    z = F_z.gens[0]
    _, fac_list = sp.factor_list(F_z)
    simple_factors = sorted([f for f, m in fac_list if m == 1], key=lambda fp: fp.degree())

    # Filter deck by Stage-2 parity (2^{n-2} + Thm 4.2 for even n => odd sub; 2^{n-1} for odd n => even sub)
    x = sp.Symbol("x")
    chi_S = decode_chi_S_from_deck_cand(cand, d, n, c_shift, x)
    gcd_x = sp.gcd(chi_S, sp.diff(chi_S, x))
    kept_indices = []
    if n % 2 == 0:
        for idx_d, g_desc in enumerate(deck):
            chi_v = decode_deck_poly_to_x(g_desc, c_shift, n - 1, gcd_x, x)
            ba = poly_eval_2tm1_asc([int(c) for c in chi_v.all_coeffs()])
            if all(v2(bk) >= (n - 2) for bk in ba) and check_thm42_odd([bk >> (n - 2) for bk in ba], n - 1):
                kept_indices.append(idx_d)
    else:
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
        diag_M_allowed = (cI + cJ) % 4
        off_M_allowed = {(cJ + cS) % 4, (cJ - cS) % 4}

        sim_q = sp.Poly(sim_x.as_expr(), x, domain=sp.QQ)
        chi_p = sp.diff(chi_S, x)
        inv_cp = sp.invert(sp.Poly(chi_p.as_expr(), x, domain=sp.QQ), sim_q) if not sim_x.is_one else None
        mrad_q = sp.Poly(mrad.as_expr(), x, domain=sp.QQ)
        d_sf = sim_x.degree()
        cs = [Fraction(int(v)) for v in sim_x.all_coeffs()] if not sim_x.is_one else []
        psums = [Fraction(d_sf)]
        for kpow in range(1, d_sf):
            psums.append(-sum(cs[j] * psums[kpow - j] for j in range(1, kpow)) - kpow * cs[kpow])

        for idx_d, g_desc in enumerate(deck):
            chi_v = decode_deck_poly_to_x(g_desc, c_shift, n - 1, gcd_x, x)
            if not all(v2(bk) >= (n - 1) for bk in poly_eval_2tm1_asc([int(c) for c in chi_v.all_coeffs()])):
                continue
            if not sim_x.is_one:
                rem_v = sp.rem(mrad_q * sp.Poly(chi_v.as_expr(), x, domain=sp.QQ) * inv_cp, sim_q, domain=sp.QQ)
                if rem_v.is_zero and 0 not in off_M_allowed:
                    continue
                rc = rem_v.all_coeffs()
                d_e = len(rc)
                tr_val = sum(Fraction(int(rc[d_e - 1 - j].numerator), int(rc[d_e - 1 - j].denominator)) * psums[j] for j in range(d_e))
                if tr_val.denominator != 1 or int(tr_val) % 4 != diag_M_allowed:
                    continue
            kept_indices.append(idx_d)

    # Hierarchical square-class cone splitting over simple factors with intermediate Farkas pruning
    active = [kept_indices]
    for sf in simple_factors:
        nxt = []
        for cur in active:
            sub_deck = [deck[i] for i in cur]
            b_locs = square_classes_for_simple_factor(sub_deck, sf, z)
            for bl in b_locs:
                glob = [cur[i] for i in bl]
                A_eq = [[deck[i][k] for i in glob] for k in range(s)]
                st, _ = exact_farkas_or_primal(A_eq, rhs)
                if st == "PRIMAL":
                    nxt.append(glob)
        active = nxt
        if not active:
            return []

    sfs_ge2 = [sf for sf in simple_factors if sf.degree() >= 2]
    all_sols: set[tuple[tuple[int, int], ...]] = set()
    for sub in active:
        A_rows_frac = [[Fraction(deck[i][k]) for i in sub] for k in range(s)]
        b_frac = [Fraction(v) for v in rhs]
        for sf in sfs_ge2:
            for gr in galois_rows_for_factor(deck, sub, sf, z):
                A_rows_frac.append(gr)
                b_frac.append(Fraction(0))
        A_int, b_int = [], []
        for row, bv in zip(A_rows_frac, b_frac):
            lcm_d = bv.denominator
            for v in row:
                lcm_d = sp.ilcm(lcm_d, v.denominator)
            A_int.append([int(v * lcm_d) for v in row])
            b_int.append(int(bv * lcm_d))
        st, _ = exact_farkas_or_primal(A_int, b_int)
        if st == "FARKAS":
            continue
        int_sols = enumerate_all_nonneg_int_sols(A_int, b_int, n)
        for sol_vec in int_sols:
            pairs = tuple(sorted((sub[p], sol_vec[p]) for p in range(len(sub)) if sol_vec[p] > 0))
            all_sols.add(pairs)
    return [sorted([list(p) for p in sol]) for sol in sorted(all_sols)]


def enumerate_all_nonneg_int_sols(A_int: list[list[int]], b_int: list[int], total_sum: int) -> list[list[int]]:
    """Exact ZZ/QQ RREF + LP-tightened branch-and-bound enumeration of ALL x >= 0 in Z^k with A x = b."""
    m = len(A_int)
    k = len(A_int[0]) if m > 0 else 0
    if k == 0:
        return []
    M = sp.Matrix([[sp.Rational(A_int[r][c]) for c in range(k)] + [sp.Rational(b_int[r])] for r in range(m)])
    rref_M, pivs = M.rref()
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
        return [sol]

    # Exact LP min/max bounds for each free column via Farkas inequality checks (x_fc <= ub, x_fc >= lb)
    bounds = []
    A_sl = [row + [0] for row in A_int]
    for fc in free_cols:
        # Find tight lb (smallest t >= 0 where x_fc <= t is feasible)
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

        # Find tight ub (largest t <= total_sum where x_fc >= t is feasible)
        lo_u, hi_u = lb, total_sum
        while lo_u < hi_u:
            mid = (lo_u + hi_u + 1) // 2
            st, _ = exact_farkas_or_primal(A_sl + [[1 if c == fc else 0 for c in range(k)] + [-1]], b_int + [mid])
            if st == "PRIMAL":
                lo_u = mid
            else:
                hi_u = mid - 1
        ub = lo_u
        bounds.append((lb, ub))

    piv_exprs = []
    for r_idx, pc in enumerate(pivs):
        const = Fraction(int(rref_M[r_idx, k].p), int(rref_M[r_idx, k].q))
        coeffs = [Fraction(int(rref_M[r_idx, fc].p), int(rref_M[r_idx, fc].q)) for fc in free_cols]
        piv_exprs.append((pc, const, coeffs))

    sols = []
    f_vals = [0] * len(free_cols)

    def backtrack(idx_f: int, rem_sum: int) -> None:
        if idx_f == len(free_cols):
            sol = [0] * k
            for i, fc in enumerate(free_cols):
                sol[fc] = f_vals[i]
            for pc, const, coeffs in piv_exprs:
                val = const - sum(coeffs[i] * f_vals[i] for i in range(len(free_cols)))
                if val.denominator != 1 or val < 0:
                    return
                sol[pc] = int(val)
            if sum(sol) == total_sum:
                sols.append(sol)
            return
        lb, ub = bounds[idx_f]
        ub_eff = min(ub, rem_sum)
        for v in range(lb, ub_eff + 1):
            f_vals[idx_f] = v
            backtrack(idx_f + 1, rem_sum - v)

    backtrack(0, total_sum)
    return sols


def compute_locked_MN(
    chi_S: sp.Poly,
    chis: list[sp.Poly],
    sol: list[list[int]],
    n_ord: int,
    x: sp.Symbol,
) -> tuple[list[int], list[list[int]], list[list[int]]]:
    """Independently compute locked_cols, M_locked, N_locked via exact K_k number-field traces
    and Theorem 7.1 mod-4 congruences.
    """
    chi_p = sp.diff(chi_S, x)
    _, fl = sp.factor_list(chi_S)
    sim_facs = [f for f, m in fl if m == 1]
    mrad = sp.Poly(1, x, domain=sp.ZZ)
    for f, m in fl:
        if m >= 2:
            mrad = sp.Poly(mrad.as_expr() * f.as_expr(), x, domain=sp.ZZ)

    def thm71_coeffs(P: sp.Poly) -> tuple[int, int, int]:
        P1, Pm1, P0, Pp0 = int(P.eval(1)), int(P.eval(-1)), int(P.eval(0)), int(sp.diff(P, x).eval(0))
        pe, po = (P1 + Pm1) // 2, (P1 - Pm1) // 2
        return pe % 4, po % 4, ((n_ord - 2) * ((pe - P0) + (n_ord - 1) * (po - Pp0))) % 4

    _, cSM, cJM = thm71_coeffs(mrad)
    _, cSN, cJN = thm71_coeffs(sp.Poly(x * mrad.as_expr(), x, domain=sp.ZZ))
    off_M = {(cJM + cSM) % 4, (cJM - cSM) % 4}
    off_N = {(cJN + cSN) % 4, (cJN - cSN) % 4}

    t = sp.Symbol("_t_lock")
    K_data = []
    for sf in sim_facs:
        alpha = sp.CRootOf(sf, 0)
        K = sp.QQ.algebraic_field(alpha)

        def make_helpers(sf_loc, K_loc):
            sf_q = sp.Poly(sf_loc.as_expr(), x, domain=sp.QQ)

            def toK(p_x):
                r = sp.rem(sp.Poly(p_x.as_expr(), x, domain=sp.QQ), sf_q, domain=sp.QQ)
                res = K_loc.zero
                for co in r.all_coeffs():
                    res = res * K_loc.unit + K_loc.dom.convert(co)
                return res

            d_sf = sf_loc.degree()
            cs = [Fraction(int(v)) for v in sf_loc.all_coeffs()]
            psums = [Fraction(d_sf)]
            for kpow in range(1, 2 * d_sf):
                if kpow <= d_sf:
                    val = -sum(cs[j] * psums[kpow - j] for j in range(1, kpow)) - kpow * cs[kpow]
                else:
                    val = -sum(cs[j] * psums[kpow - j] for j in range(1, d_sf + 1))
                psums.append(val)

            def trK(elem):
                rc = elem.rep
                d_e = len(rc)
                return sum(Fraction(int(rc[d_e - 1 - j].numerator), int(rc[d_e - 1 - j].denominator)) * psums[j] for j in range(d_e))

            return toK, trK

        toK, trK = make_helpers(sf, K)
        m_k = toK(mrad)
        cp_k = toK(chi_p)
        ds_k = [toK(ch) / cp_k for ch in chis]
        K_data.append((K, m_k, ds_k, trK))

    b_cnt = len(sol)
    locked_cols = []
    cols_M, cols_N = [], []
    for b in range(b_cnt):
        ok_b = True
        col_M, col_N = [], []
        for a in range(b_cnt):
            per_k_MN = []
            for K, m_k, ds_k, trK in K_data:
                prod_sq = (m_k * m_k) * ds_k[a] * ds_k[b]
                if prod_sq == K.zero:
                    per_k_MN.append([(Fraction(0), Fraction(0))])
                else:
                    sqp = sp.Poly.from_dict({(2,): K.one, (0,): -prod_sq}, t, domain=K)
                    _, fl2 = sqp.factor_list()
                    lf = [f for f, _ in fl2 if f.degree() == 1][0]
                    cs2 = lf.rep.all_coeffs()
                    rk = K.exquo(-cs2[1], cs2[0])
                    trM = trK(rk)
                    trN = trK(K.unit * rk)
                    per_k_MN.append([(trM, trN), (-trM, -trN)])
            cands_MN = set()
            for tup in itertools.product(*per_k_MN):
                M_tot = sum(v[0] for v in tup)
                N_tot = sum(v[1] for v in tup)
                if M_tot.denominator == 1 and N_tot.denominator == 1:
                    Mi, Ni = int(M_tot), int(N_tot)
                    if a == b and sol[a][1] == 1:
                        diagM = sum(trK(m_k * ds_k[a]) for K, m_k, ds_k, trK in K_data)
                        diagN = sum(trK(K.unit * m_k * ds_k[a]) for K, m_k, ds_k, trK in K_data)
                        if Mi == int(diagM) and Ni == int(diagN):
                            cands_MN.add((Mi, Ni))
                    else:
                        if (Mi % 4 in off_M) and (Ni % 4 in off_N):
                            cands_MN.add((Mi, Ni))
            if len(cands_MN) != 1:
                ok_b = False
                break
            Mi, Ni = next(iter(cands_MN))
            col_M.append(Mi)
            col_N.append(Ni)
        if ok_b:
            locked_cols.append(b)
            cols_M.append(col_M)
            cols_N.append(col_N)

    M_locked = [[cols_M[c_i][r] for c_i in range(len(locked_cols))] for r in range(b_cnt)]
    N_locked = [[cols_N[c_i][r] for c_i in range(len(locked_cols))] for r in range(b_cnt)]
    return locked_cols, M_locked, N_locked


def audit_ku_and_2v_exact(cert: dict, dk: dict, d: int, n: int, x: sp.Symbol) -> dict:
    idx = cert["index"]
    c_shift = int(dk["c"])
    cand = dk["candidates"][idx]
    chi_S = decode_chi_S_from_deck_cand(cand, d, n, c_shift, x)
    ctx = build_2v_cache_ctx(chi_S, x)
    gcd_x = ctx["gcd_x"]

    # Completeness check: independently enumerate ALL Galois-surviving Stage-2 integer sols
    ind_sols = enumerate_galois_int_sols(cand, d, n, c_shift)
    cert_sols = [sorted([list(p) for p in sc["sol"]]) for sc in cert["sol_certs"]]
    ind_set = {tuple(tuple(p) for p in s) for s in ind_sols}
    cert_set = {tuple(tuple(p) for p in s) for s in cert_sols}
    missed_sols = sorted(ind_set - cert_set)
    if missed_sols:
        print(f"  [FLAG] ({d},{n}) idx={idx}: cert omitted {len(missed_sols)} Galois sols! true={len(ind_set)}, cert={len(cert_set)}")

    chi_cache: dict[int, sp.Poly] = {}

    def get_chi(di: int) -> sp.Poly:
        if di not in chi_cache:
            chi_cache[di] = decode_deck_poly_to_x(cand["deck"][di], c_shift, n - 1, gcd_x, x)
        return chi_cache[di]

    pair_2v_cache: dict[tuple[int, int], list[tuple[int, int]]] = {}
    s2_rem_mod = (n - 2) % 4

    def get_2v_pairs(da: int, db: int) -> list[tuple[int, int]]:
        key = (min(da, db), max(da, db))
        if key not in pair_2v_cache:
            sols = solve_2v_jacobi_exact(chi_S, get_chi(key[0]), get_chi(key[1]), s2_step=4, s2_rem_mod=s2_rem_mod, x=x, cache_ctx=ctx)
            # Deduplicate (s_uv, s2_uv)
            pair_2v_cache[key] = sorted({(s_uv, s2_uv) for s_uv, s2_uv, _ in sols})
        return pair_2v_cache[key]

    reasons_count: dict[str, int] = {}
    for sc in cert["sol_certs"]:
        kr = sc["kill_reason"]
        reasons_count[kr] = reasons_count.get(kr, 0) + 1
        sol = sc["sol"]
        if kr == "2v_jacobi_empty":
            da, db = sc["deck_pair"]
            assert [sol[sc["empty_pair"][0]][0], sol[sc["empty_pair"][1]][0]] == [da, db]
            assert get_2v_pairs(da, db) == [], f"Expected empty 2v for idx={idx} pair {(da, db)}"
            continue

        chis = [get_chi(di) for di, _ in sol]
        locked_cols, M_locked, N_locked = compute_locked_MN(chi_S, chis, sol, n, x)
        assert locked_cols == sc["locked_cols"], f"idx={idx}: locked_cols mismatch {locked_cols} vs {sc['locked_cols']}"
        assert M_locked == sc["M_locked"] and N_locked == sc["N_locked"], f"idx={idx}: M/N mismatch"

        ns = [cnt for _, cnt in sol]
        b_cnt = len(ns)
        mod4_target = (n - 1) % 4

        def enum_ku_rows(ranges: list[list[int]], N_row: list[int]) -> list[list[int]]:
            nc = len(M_locked[0]) if b_cnt and M_locked[0] else 0
            suf_min = [[0] * nc for _ in range(b_cnt + 1)]
            suf_max = [[0] * nc for _ in range(b_cnt + 1)]
            for i in range(b_cnt - 1, -1, -1):
                if not ranges[i]:
                    return []
                lo_i, hi_i = min(ranges[i]), max(ranges[i])
                for cc in range(nc):
                    v1, v2_v = lo_i * M_locked[i][cc], hi_i * M_locked[i][cc]
                    suf_min[i][cc] = suf_min[i + 1][cc] + min(v1, v2_v)
                    suf_max[i][cc] = suf_max[i + 1][cc] + max(v1, v2_v)
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
                        acc[cc] += v * M_locked[i][cc]
                    dfs(i + 1, s_cur + v)
                    for cc in range(nc):
                        acc[cc] -= v * M_locked[i][cc]

            dfs(0, 0)
            return out

        if kr == "ku_empty":
            p2v_cert = sc.get("2v_pairs", {})
            ku_init = []
            for r in range(b_cnt):
                ranges = []
                for j in range(b_cnt):
                    lim = ns[j] - (1 if j == r else 0)
                    key_s = f"{min(r,j)},{max(r,j)}"
                    if key_s in p2v_cert:
                        ps = get_2v_pairs(sol[min(r, j)][0], sol[max(r, j)][0])
                        assert sorted([list(p) for p in ps]) == sorted(p2v_cert[key_s])
                        sgns = {p[0] for p in ps}
                        if sgns == {1}:
                            ranges.append([lim])
                        elif sgns == {-1}:
                            ranges.append([-lim])
                        elif not sgns:
                            ranges.append([])
                        else:
                            ranges.append(list(range(-lim, lim + 1, 2)))
                    else:
                        ranges.append(list(range(-lim, lim + 1, 2)))
                ku_init.append(enum_ku_rows(ranges, N_locked[r]))
            if any(len(x_l) == 0 for x_l in ku_init):
                continue
            # Fallback: compute 2v_pairs directly (cert omits 2v_pairs when 2v_empty/sign-lock hits during ku build)
            killed_via_2v = False
            p2v_full: dict[tuple[int, int], list[tuple[int, int]]] = {}
            for r in range(b_cnt):
                for j in range(r, b_cnt):
                    if r == j and ns[r] < 2:
                        continue
                    ps = get_2v_pairs(sol[r][0], sol[j][0])
                    if not ps:
                        killed_via_2v = True
                        break
                    p2v_full[(r, j)] = ps
                if killed_via_2v:
                    break
            if killed_via_2v:
                continue
            ku_locked = []
            for r in range(b_cnt):
                ranges = []
                for j in range(b_cnt):
                    lim = ns[j] - (1 if j == r else 0)
                    if lim == 0:
                        ranges.append([0])
                        continue
                    sgns = {p[0] for p in p2v_full[(min(r, j), max(r, j))]}
                    ranges.append([lim] if sgns == {1} else ([-lim] if sgns == {-1} else list(range(-lim, lim + 1, 2))))
                ku_locked.append(enum_ku_rows(ranges, N_locked[r]))
            assert any(len(x_l) == 0 for x_l in ku_locked), (
                f"idx={idx} sol={sc['sol_index']} ku_empty failed even with 2v: {[len(x_l) for x_l in ku_locked]}"
            )
            continue

        if kr == "global_K_farkas" and not sc.get("2v_pairs"):
            ku_nolock = [
                enum_ku_rows([list(range(-(ns[j] - (1 if j == r else 0)), ns[j] - (1 if j == r else 0) + 1, 2)) for j in range(b_cnt)], N_locked[r])
                for r in range(b_cnt)
            ]
            assert [sorted(x_l) for x_l in ku_nolock] == [sorted(x_l) for x_l in sc["valid_ku_final"]]
            verify_dual_farkas_int(sc["rows_eq"], sc["b_eq"], sc["dual_y_int"])
            st, _ = exact_farkas_or_primal(sc["rows_eq"], sc["b_eq"])
            assert st == "FARKAS", f"idx={idx} global_K_farkas actually feasible!"
            continue

        # For ku_2v_fixed_point and global_K_farkas (with 2v_pairs): compute ALL 2v_pairs independently and run exact FP
        p2v_ind = {}
        for r in range(b_cnt):
            for j in range(r, b_cnt):
                if r == j and ns[r] < 2:
                    continue
                ps = get_2v_pairs(sol[r][0], sol[j][0])
                p2v_ind[(r, j)] = ps
                key_s = f"{r},{j}"
                if key_s in sc.get("2v_pairs", {}):
                    assert sorted([list(p) for p in ps]) == sorted(sc["2v_pairs"][key_s])
                if not ps:
                    raise AssertionError(f"Unexpected empty 2v inside {kr}")

        ku = []
        for r in range(b_cnt):
            ranges = []
            for j in range(b_cnt):
                lim = ns[j] - (1 if j == r else 0)
                if lim == 0:
                    ranges.append([0])
                    continue
                sgns = {p[0] for p in p2v_ind[(min(r, j), max(r, j))]}
                if sgns == {1}:
                    ranges.append([lim])
                elif sgns == {-1}:
                    ranges.append([-lim])
                else:
                    ranges.append(list(range(-lim, lim + 1, 2)))
            ku.append(enum_ku_rows(ranges, N_locked[r]))

        def compat(a: int, ka: list[int], b: int, kb: list[int], s_val: int) -> bool:
            ps = p2v_ind[(min(a, b), max(a, b))]
            lo, hi = 0, 0
            for cc in range(b_cnt):
                nc = ns[cc] - (1 if cc == a else 0) - (1 if cc == b else 0)
                tku = ka[cc] - (s_val if cc == b else 0)
                tkv = kb[cc] - (s_val if cc == a else 0)
                lo += abs(tku + tkv) - nc
                hi += nc - abs(tku - tkv)
            return any(p[0] == s_val and lo <= p[1] <= hi for p in ps)

        while True:
            new_ku = []
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
                new_ku.append(kept)
            if [len(x_l) for x_l in new_ku] == [len(x_l) for x_l in ku]:
                ku = new_ku
                break
            ku = new_ku

        if kr == "ku_2v_fixed_point":
            assert any(len(x_l) == 0 for x_l in ku), f"idx={idx} FP did not kill: {[len(x_l) for x_l in ku]}"
        elif kr == "global_K_farkas":
            assert all(len(x_l) > 0 for x_l in ku)
            assert [sorted(x_l) for x_l in ku] == [sorted(x_l) for x_l in sc["valid_ku_final"]]
            # Independently verify Farkas on global K = K^T system
            verify_dual_farkas_int(sc["rows_eq"], sc["b_eq"], sc["dual_y_int"])
            st, _ = exact_farkas_or_primal(sc["rows_eq"], sc["b_eq"])
            assert st == "FARKAS", f"idx={idx} global_K_farkas actually feasible!"
        else:
            raise ValueError(f"Unknown kill_reason: {kr}")

    # Also independently verify any missed_sols are killed by 2v_empty or ku_empty!
    missed_still_killed = 0
    for ms in missed_sols:
        sol_m = [list(p) for p in ms]
        ns_m = [cnt for _, cnt in sol_m]
        b_m = len(ns_m)
        # Check pairwise 2v emptiness first if diff <= 1 (fast) or check locked ku
        chis_m = [get_chi(di) for di, _ in sol_m]
        lcols_m, M_m, N_m = compute_locked_MN(chi_S, chis_m, sol_m, n, x)
        # Check if any row has 0 valid ku even before 2v sign lock
        row_killed = False
        for r in range(b_m):
            ranges = [list(range(-(ns_m[j] - (1 if j == r else 0)), ns_m[j] - (1 if j == r else 0) + 1, 2)) for j in range(b_m)]
            cnt_r = sum(
                1 for k in itertools.product(*ranges)
                if sum(k) % 4 == (n - 1) % 4
                and all(sum(k[i] * M_m[i][c_i] for i in range(b_m)) == N_m[r][c_i] for c_i in range(len(lcols_m)))
            )
            if cnt_r == 0:
                row_killed = True
                break
        if row_killed:
            missed_still_killed += 1
            continue
        # Otherwise check 2v pairs emptiness
        empty_2v = False
        for r in range(b_m):
            for j in range(r, b_m):
                if r == j and ns_m[r] < 2:
                    continue
                if get_2v_pairs(sol_m[r][0], sol_m[j][0]) == []:
                    empty_2v = True
                    break
            if empty_2v:
                break
        assert empty_2v, f"Missed sol {sol_m} in ({d},{n}) idx={idx} survived BOTH ku_empty and 2v_empty!"
        missed_still_killed += 1

    return {
        "index": idx,
        "sols_verified": len(cert["sol_certs"]),
        "true_galois_sols": len(ind_set),
        "missed_sols_count": len(missed_sols),
        "missed_still_killed": missed_still_killed,
        "reasons": reasons_count,
        "status": "COMPLETENESS_FAIL_SOUNDNESS_PASS" if missed_sols else "PASS",
    }


def audit_stage3_74_to_73_sol(
    chi_S74: sp.Poly,
    chi_types: dict[int, sp.Poly],
    sc: dict,
    x: sp.Symbol,
    ctx74: dict,
    pair_cache74: dict[tuple[int, int, tuple[int, ...]], list[list[int]]],
    forced_roots: tuple[int, ...] = (),
) -> None:
    """Independently verify a 74->73 Stage-3 elimination subcert."""
    sol = sc["sol"]
    v_deck = sc["deleted_v_deck"]
    s3 = sc["stage3"]
    assert s3["killed"] is True

    chi_v73 = chi_types[v_deck]
    assert [int(c) for c in chi_v73.all_coeffs()] == s3["F_v_coeffs"]

    # Check Stage-3 count constraints match sol minus deleted vertex v_deck
    expected_cnts = {str(di): (cnt - (1 if di == v_deck else 0)) for di, cnt in sol if (cnt - (1 if di == v_deck else 0)) > 0}
    assert {str(k): int(v) for k, v in s3["cnt_constraints"].items()} == expected_cnts

    # Independently check Theorem 7.1 M, N mod 4 on S_v (order 73, odd!)
    _, fl73 = sp.factor_list(chi_v73)
    sim_v = sp.Poly(1, x, domain=sp.ZZ)
    mrad_v = sp.Poly(1, x, domain=sp.ZZ)
    for fc, mp in fl73:
        if mp == 1:
            sim_v = sp.Poly(sim_v.as_expr() * fc.as_expr(), x, domain=sp.ZZ)
        else:
            mrad_v = sp.Poly(mrad_v.as_expr() * fc.as_expr(), x, domain=sp.ZZ)
    assert sp.Poly(s3["Sim_v"], x, domain=sp.ZZ) == sim_v

    P1, Pm1, P0, Pp0 = int(mrad_v.eval(1)), int(mrad_v.eval(-1)), int(mrad_v.eval(0)), int(sp.diff(mrad_v, x).eval(0))
    pe, po = (P1 + Pm1) // 2, (P1 - Pm1) // 2
    cI, cS = pe % 4, po % 4
    cJ = (71 * ((pe - P0) + 72 * (po - Pp0))) % 4
    assert sorted({(cJ + cS) % 4, (cJ - cS) % 4}) == sorted(s3["off_M_mod4"])
    assert (cI + cJ) % 4 == s3["diag_M_mod4"]

    # Independently verify ZERO valid 2v(v_deck, u) candidate was omitted from chi72_cands_coeffs!
    for di in expected_cnts:
        u_deck = int(di)
        ckey = (min(v_deck, u_deck), max(v_deck, u_deck), forced_roots)
        if ckey not in pair_cache74:
            sols_2v = solve_2v_jacobi_exact(
                chi_S74, chi_types[v_deck], chi_types[u_deck],
                s2_step=2, s2_rem_mod=0, x=x,
                forced_linear_roots=forced_roots, cache_ctx=ctx74,
            )
            pair_cache74[ckey] = sorted({tuple(p) for _, _, p in sols_2v})
        ind_cands = [list(p) for p in pair_cache74[ckey]]
        cert_group_cands = [
            s3["chi72_cands_coeffs"][i]
            for i, lbl in enumerate(s3["chi72_group_labels"])
            if lbl == u_deck
        ]
        assert set(tuple(p) for p in ind_cands) <= set(tuple(p) for p in cert_group_cands), (
            f"Stage-3 omitted valid 2v cand for (v={v_deck}, u={u_deck})!"
        )

    # Verify every cone Farkas certificate (exact integer y^T A >= 0 and y^T b < 0)
    # and check cone_local_ids cover all kept_local_ids!
    assert len(s3["cones"]) >= 1
    covered_ids: set[int] = set()
    for cone in s3["cones"]:
        assert cone["status"] == "FARKAS"
        verify_dual_farkas_int(cone["A_orth"], cone["b_orth"], cone["dual_y_int"])
        covered_ids.update(cone["cone_local_ids"])
    assert set(s3["kept_local_ids"]) <= covered_ids


def main() -> None:
    t0 = time.time()
    x = sp.Symbol("x")
    manifest = json.loads((CERTS_DIR / "MANIFEST.json").read_text())
    for fname, meta in manifest["files"].items():
        p = CERTS_DIR / fname
        assert p.stat().st_size == meta["bytes"] and sha256_file(p) == meta["sha256"], f"SHA mismatch on {fname}"
    print(f"[PASS] MANIFEST.json verified (4 files, {manifest['total_killed']} certs)")

    summary = {"manifest_sha256": sha256_file(CERTS_DIR / "MANIFEST.json"), "files": {}}

    # 1. Verify (18, 60): 1 cert (idx=11)
    d60 = read_json_auto(CERTS_DIR, "sec7_18_60.json")
    p2_60 = read_json_auto(POLY_RESULTS_DIR, "phase2_18_60.json")
    assert len(d60["certs"]) == 1 and d60["certs"][0]["index"] == 11
    dk60 = read_json_auto(POLY_RESULTS_DIR, "deck_18_60.json")
    dk59 = read_json_auto(POLY_RESULTS_DIR, "deck_18_59.json")
    c11 = d60["certs"][0]
    ind11 = enumerate_galois_int_sols(dk60["candidates"][11], 18, 60, int(dk60["c"]))
    assert ind11 == [[[0, 16], [1, 44]], [[0, 27], [2, 33]]]
    all_raw11 = enumerate_all_nonneg_int_sols(c11["A_b"], c11["b_b"], 60)
    assert all_raw11 == c11["int_sols"] and len(all_raw11) == 12
    # Verify x0 <= 15 Farkas certificate
    A_le = [row + ([1] if i == 0 else []) for i, row in enumerate(c11["A_b"])]
    # Wait: x0 + slack = 15 => append [1, 0, 0, 1] row:
    A_x0 = [row + [0] for row in c11["A_b"]] + [[1, 0, 0, 1]]
    b_x0 = list(c11["b_b"]) + [15]
    verify_dual_farkas_int(A_x0, b_x0, c11["x0_le_15_farkas_y_int"])
    chi_S11 = decode_chi_S_from_deck_cand(dk60["candidates"][11], 18, 60, int(dk60["c"]), x)
    gcd11 = sp.gcd(chi_S11, sp.diff(chi_S11, x))
    chi_v0_11 = decode_deck_poly_to_x(dk60["candidates"][11]["deck"][0], int(dk60["c"]), 59, gcd11, x)
    chi_59_898 = decode_chi_S_from_deck_cand(dk59["candidates"][898], 18, 59, int(dk59["c"]), x)
    assert chi_v0_11 == chi_59_898
    summary["files"]["sec7_18_60.json"] = {"verified": 1, "remaining_phase2": len(p2_60["survivors"]) - 1}
    print("[PASS] sec7_18_60.json: 1/1 verified (idx=11 -> 18_59 idx=898)")

    # 2. Verify (17, 49): 5 certs (idx=66, 27, 58, 72, 70)
    d17 = read_json_auto(CERTS_DIR, "sec7_17_49.json")
    p2_17 = read_json_auto(POLY_RESULTS_DIR, "phase2_17_49.json")
    dk17 = read_json_auto(POLY_RESULTS_DIR, "deck_17_49.json")
    surv17 = {s["index"] for s in p2_17["survivors"]}
    killed17 = {c["index"] for c in d17["certs"]}
    assert killed17 <= surv17 and len(killed17) == 5
    res17 = []
    for cert in d17["certs"]:
        idx, m = cert["index"], cert["method"]
        if m == "galois_farkas":
            assert enumerate_galois_int_sols(dk17["candidates"][idx], 17, 49, int(dk17["c"])) == []
            for lc in cert["leaf_cones"]:
                verify_dual_farkas_int(lc["A_orth"], lc["b_orth"], lc["dual_y_int"])
            res17.append({"index": idx, "method": m, "status": "PASS"})
        elif m == "ku_and_2v_exact":
            res17.append(audit_ku_and_2v_exact(cert, dk17, 17, 49, x))
        elif m == "stage3_49_48_47_linear_farkas":
            cand70 = dk17["candidates"][70]
            c_shift = int(dk17["c"])
            ind70 = enumerate_galois_int_sols(cand70, 17, 49, c_shift)
            assert ind70 == [cert["sol"]]
            chi_S = decode_chi_S_from_deck_cand(cand70, 17, 49, c_shift, x)
            ctx70 = build_2v_cache_ctx(chi_S, x)
            gcd_x = ctx70["gcd_x"]
            chi0 = decode_deck_poly_to_x(cand70["deck"][0], c_shift, 48, gcd_x, x)
            chi3 = decode_deck_poly_to_x(cand70["deck"][3], c_shift, 48, gcd_x, x)
            s2_00 = sorted({tuple(p) for _, _, p in solve_2v_jacobi_exact(chi_S, chi0, chi0, 4, 3, x, cache_ctx=ctx70)})
            s2_03 = sorted({tuple(p) for _, _, p in solve_2v_jacobi_exact(chi_S, chi0, chi3, 4, 3, x, cache_ctx=ctx70)})
            assert set(s2_00) == set(tuple(p) for p in cert["c47_2v00_coeffs"])
            assert set(s2_03) == set(tuple(p) for p in cert["c47_2v03_coeffs"])
            verify_dual_farkas_int(cert["A_lin"], cert["b_lin"], cert["dual_y_int"])
            st, _ = exact_farkas_or_primal(cert["A_lin"], cert["b_lin"])
            assert st == "FARKAS"
            res17.append({"index": idx, "method": m, "status": "PASS"})
        else:
            raise ValueError(f"Unknown method in 17_49: {m}")
    summary["files"]["sec7_17_49.json"] = {"verified": 5, "remaining_phase2": len(surv17 - killed17), "details": res17}
    print(f"[PASS] sec7_17_49.json: 5/5 verified in {time.time()-t0:.2f}s")

    # 3. Verify (19, 74): 5 certs (idx=134, 74, 47, 6, 24)
    t19 = time.time()
    d19 = read_json_auto(CERTS_DIR, "sec7_19_74.json")
    p2_19 = read_json_auto(POLY_RESULTS_DIR, "phase2_19_74.json")
    dk19 = read_json_auto(POLY_RESULTS_DIR, "deck_19_74.json")
    surv19 = {s["index"] for s in p2_19["survivors"]}
    killed19 = {c["index"] for c in d19["certs"]}
    assert killed19 <= surv19 and len(killed19) == 5 and sorted(surv19 - killed19) == [13, 136]
    c19_shift = int(dk19["c"])
    res19 = []
    for cert in d19["certs"]:
        idx, m = cert["index"], cert["method"]
        cand = dk19["candidates"][idx]
        chi_S = decode_chi_S_from_deck_cand(cand, 19, 74, c19_shift, x)
        ctx = build_2v_cache_ctx(chi_S, x)
        gcd_x = ctx["gcd_x"]
        ind_sols = enumerate_galois_int_sols(cand, 19, 74, c19_shift)
        if m == "stage3_74_to_73_galois_farkas":
            cert_sols = [sorted([list(p) for p in cert["sol"]])]
        else:
            cert_sols = [sorted([list(p) for p in sc["sol"]]) for sc in cert["sol_certs"]]
        assert set(tuple(tuple(p) for p in s) for s in ind_sols) <= set(tuple(tuple(p) for p in s) for s in cert_sols)

        chi_types = {di: decode_deck_poly_to_x(cand["deck"][di], c19_shift, 73, gcd_x, x) for s in cert_sols for di, _ in s}
        pair_cache: dict[tuple[int, int, tuple[int, ...]], list[list[int]]] = {}

        if m == "2v_jacobi_diff1":
            for sc in cert["sol_certs"]:
                da, db = sc["empty_2v_deck_pair"]
                ck = (min(da, db), max(da, db), ())
                if ck not in pair_cache:
                    pair_cache[ck] = solve_2v_jacobi_exact(chi_S, chi_types[da], chi_types[db], 2, 0, x, cache_ctx=ctx)
                assert pair_cache[ck] == []
            res19.append({"index": idx, "method": m, "sols": len(cert["sol_certs"]), "status": "PASS"})
        elif m == "stage3_74_to_73_galois_farkas":
            assert len(cert["per_vertex_stage3"]) == len(cert["sol"])
            for pv in cert["per_vertex_stage3"]:
                sub_sc = {"sol": cert["sol"], "deleted_v_deck": pv["deleted_v_deck"], "stage3": pv["stage3"]}
                audit_stage3_74_to_73_sol(chi_S, chi_types, sub_sc, x, ctx, pair_cache)
            res19.append({"index": idx, "method": m, "sols": 1, "status": "PASS"})
        elif m in ("stage3_74_to_73_parity_and_galois", "stage3_74_to_73_plus_2v", "stage3_74_to_73_and_E17"):
            for sc in cert["sol_certs"]:
                kr = sc.get("kill_reason")
                if kr == "2v_jacobi_empty":
                    da, db = sc["empty_2v_deck_pair"]
                    assert solve_2v_jacobi_exact(chi_S, chi_types[da], chi_types[db], 2, 0, x, cache_ctx=ctx) == []
                else:
                    forced_r = ()
                    if idx == 24 and sc["deleted_v_deck"] == 1:
                        # Prove (x-17)(x-13) | h_uv from E_17 e_1 = 0 and E_13 e_1 = 0
                        _, fl_S = sp.factor_list(chi_S)
                        _, fl_1 = sp.factor_list(chi_types[1])
                        mult_S = {str(f.as_expr()): mp for f, mp in fl_S}
                        mult_1 = {str(f.as_expr()): mp for f, mp in fl_1}
                        assert mult_1["x - 17"] == mult_S["x - 17"] and mult_1["x - 13"] > mult_S["x - 13"]
                        forced_r = (17, 13)
                    if kr == "E17_triangle_inequality_and_stage3_v1":
                        cp17 = int(sp.diff(chi_S, x).eval(17))
                        diags17 = {di: Fraction(int(chi_types[di].eval(17)), cp17) for di, _ in sc["sol"]}
                        assert diags17[0] == Fraction(1, 44) and diags17[6] == Fraction(1, 11)
                        assert sc["E17_triangle_lhs"] == 34 and sc["E17_triangle_rhs"] == 32
                    audit_stage3_74_to_73_sol(chi_S, chi_types, sc, x, ctx, pair_cache, forced_roots=forced_r)
            res19.append({"index": idx, "method": m, "sols": len(cert["sol_certs"]), "status": "PASS"})
        else:
            raise ValueError(f"Unknown method in 19_74: {m}")
    summary["files"]["sec7_19_74.json"] = {"verified": 5, "remaining": sorted(surv19 - killed19), "details": res19}
    print(f"[PASS] sec7_19_74.json: 5/5 verified (remaining={sorted(surv19 - killed19)}) in {time.time()-t19:.2f}s")

    # 4. Verify (18, 59): 66 certs (45 galois_farkas, 2 galois_zero_int_sol, 19 ku_and_2v_exact)
    t18 = time.time()
    d18 = read_json_auto(CERTS_DIR, "sec7_18_59.json")
    p2_18 = read_json_auto(POLY_RESULTS_DIR, "phase2_18_59.json")
    surv18 = {s["index"] for s in p2_18["survivors"]}
    killed18 = {c["index"] for c in d18["certs"]}
    assert killed18 <= surv18 and len(killed18) == 66 and len(surv18 - killed18) == 20
    c59_shift = int(dk59["c"])

    galois_cnt, zero_int_cnt, ku2v_cnt = 0, 0, 0
    completeness_failures_18 = []
    for cert in d18["certs"]:
        idx, m = cert["index"], cert["method"]
        if m in ("galois_farkas", "galois_zero_int_sol"):
            # Independent clean-room Galois cone enumeration + exact zero-int-sol verification
            ind_sols = enumerate_galois_int_sols(dk59["candidates"][idx], 18, 59, c59_shift)
            assert ind_sols == [], f"(18,59) idx={idx} unexpectedly feasible! {ind_sols}"
            # Also verify every exported leaf_cone dual_y_int / box_cert
            for lc in cert["leaf_cones"]:
                if lc["status"] == "FARKAS":
                    verify_dual_farkas_int(lc["A_orth"], lc["b_orth"], lc["dual_y_int"])
                elif lc["status"] == "ZERO_INT_SOL":
                    bc = lc["box_cert"]
                    for fb in bc["fcol_bounds"]:
                        col = fb["col"]
                        # Verify lb-1 infeasible & ub+1 infeasible if Farkas cert supplied
                        if fb["lb_strict_below_farkas_y_int"] is not None:
                            A_lo = [r + [0] for r in lc["A_orth"]] + [[1 if j == col else 0 for j in range(len(lc["A_orth"][0]))] + [1]]
                            b_lo = list(lc["b_orth"]) + [fb["lb"] - 1]
                            verify_dual_farkas_int(A_lo, b_lo, fb["lb_strict_below_farkas_y_int"])
                        if fb["ub_strict_above_farkas_y_int"] is not None:
                            A_hi = [r + [0] for r in lc["A_orth"]] + [[1 if j == col else 0 for j in range(len(lc["A_orth"][0]))] + [-1]]
                            b_hi = list(lc["b_orth"]) + [fb["ub"] + 1]
                            verify_dual_farkas_int(A_hi, b_hi, fb["ub_strict_above_farkas_y_int"])
                    assert enumerate_all_nonneg_int_sols(lc["A_orth"], lc["b_orth"], 59) == []
                else:
                    raise ValueError(f"Unknown leaf_cone status: {lc['status']}")
            if m == "galois_farkas":
                galois_cnt += 1
            else:
                zero_int_cnt += 1
        elif m == "ku_and_2v_exact":
            r_ku = audit_ku_and_2v_exact(cert, dk59, 18, 59, x)
            if r_ku["missed_sols_count"] > 0:
                completeness_failures_18.append(r_ku)
            ku2v_cnt += 1
            print(f"  [18,59] ku_and_2v_exact idx={idx} ({r_ku['sols_verified']} sols) {r_ku['status']} ({time.time()-t18:.1f}s)", flush=True)
        else:
            raise ValueError(f"Unknown method in 18_59: {m}")

    summary["files"]["sec7_18_59.json"] = {
        "verified": 66,
        "galois_farkas": galois_cnt,
        "galois_zero_int_sol": zero_int_cnt,
        "ku_and_2v_exact": ku2v_cnt,
        "remaining_phase2": len(surv18 - killed18),
        "completeness_failures": completeness_failures_18,
    }
    print(f"[DONE] sec7_18_59.json: 66/66 audited ({galois_cnt} galois_farkas, {zero_int_cnt} zero_int, {ku2v_cnt} ku_and_2v_exact, completeness_failures={len(completeness_failures_18)}) in {time.time()-t18:.2f}s")

    summary["elapsed_s"] = round(time.time() - t0, 2)
    has_fail = any(r.get("missed_sols_count", 0) > 0 for r in res17) or bool(completeness_failures_18)
    summary["status"] = "FAIL_COMPLETENESS" if has_fail else "PASS"
    OUT_JSON.write_text(json.dumps(summary, indent=2))
    print(f"SEC7 77-CERT AUDIT COMPLETE (status={summary['status']}) in {summary['elapsed_s']}s -> {OUT_JSON}")
    if has_fail:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
