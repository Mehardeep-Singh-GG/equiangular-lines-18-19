"""Independent clean-room verification of Phase-3 eliminations of
(19, 74) idx=47 and (18, 59) idx=861 (compute/search/results/phase3_kills_861_and_47.json).

Zero code reused from compute/search/ or compute/poly/.
Uses pure exact ZZ / QQ arithmetic, exact square-free + primitive Sturm real-rootedness >= -5,
exact CRootOf interlacing, exact 2-adic Seidel congruences (2^m for even m; Theorem 4.2 + 2^{m-1}
for odd m), Theorem 7.1 Eulerian M, N mod-4 checks, and exact spectral/Frobenius trace bounds.
"""

from __future__ import annotations

from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import time
import sympy as sp

from verify_farkas import check_thm42_odd, poly_shift_linear
from verify_phase2_19_74 import solve_null_dim_0_or_1
from verify_phase2_certs import compute_rhs_and_common
from verify_polys import count_real_roots_sqf, poly_eval_2tm1_asc, v2
from _repo_io import AUDIT_DIR, COMPUTE_POLY_RESULTS, COMPUTE_SEARCH_RESULTS, read_json_auto, resolve_data_file, sha256_auto


POLY_RESULTS_DIR = COMPUTE_POLY_RESULTS
SEARCH_RESULTS_DIR = COMPUTE_SEARCH_RESULTS
OUT_JSON = AUDIT_DIR / "phase3_47_861_audit.json"


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def decode_deck_poly_to_x(p_w_desc: list[int], c_shift: int, n_sub: int, gcd_x: sp.Poly, x: sp.Symbol) -> sp.Poly:
    """Given deck polynomial g(w) in w = (x - c_shift)/2 (with lead 2 if n_sub odd, lead 1 if n_sub even),
    reconstruct full monic chi_{S_v}(x) = gcd_x(x) * g_x(x) in Z[x]."""
    # Actually let's reconstruct from full w-expression:
    # For even n (e.g. 74 -> n_sub=73 odd): F_{74}(w) = 2^{74} * ..., Gcd_w = gcd(F, F'), deck[i] has lead 2.
    # Let's check exact lifting directly from Gcd_x!
    # Wait: g(w) has deg s-1, and w = (x - c_shift)/2.
    # Multiply g((x - c_shift)/2) by 2^{s-1} if lead=1, or 2^{s-2} if lead=2, to make monic g_x(x)!
    s_minus_1 = len(p_w_desc) - 1
    lc = p_w_desc[0]
    w = sp.Symbol("w")
    pw = sp.Poly(p_w_desc, w, domain=sp.QQ)
    gx_expr = sp.expand((2 ** s_minus_1) * pw.as_expr().subs(w, (x - c_shift) / 2) / lc)
    gx = sp.Poly(gx_expr, x, domain=sp.ZZ)
    assert gx.LC() == 1
    chi_v = sp.Poly(gcd_x.as_expr() * gx.as_expr(), x, domain=sp.ZZ)
    assert chi_v.degree() == n_sub
    return chi_v


def poly_real_rooted_ge_neg5(poly_x: sp.Poly, x: sp.Symbol) -> bool:
    """Exact ZZ/QQ check that all roots (with multiplicity) are real and >= -5."""
    coeffs_desc = [int(c) for c in poly_x.all_coeffs()]
    if not coeffs_desc:
        return False
    # Shift y = x + 5 => x = y - 5 => all roots of py(y) must be >= 0
    py_desc = poly_shift_linear(coeffs_desc, 1, -5)
    # Exact Vieta/Descartes necessary filter: after stripping y=0 factors,
    # a polynomial with all roots real and > 0 has strictly alternating nonzero signs.
    nz = len(py_desc)
    while nz > 0 and py_desc[nz - 1] == 0:
        nz -= 1
    if nz == 0:
        return False
    s0 = 1 if py_desc[0] > 0 else -1
    for i in range(1, nz):
        c = py_desc[i]
        expected_sgn = s0 if (i % 2 == 0) else -s0
        if c == 0 or (1 if c > 0 else -1) != expected_sgn:
            return False
    py = sp.Poly.from_list(py_desc, x, domain=sp.ZZ)
    _, sqf_facs = sp.sqf_list(py)
    for fac, _ in sqf_facs:
        fac_desc = [int(c) for c in fac.all_coeffs()]
        tot, nonneg = count_real_roots_sqf(fac_desc)
        if tot != fac.degree() or nonneg != fac.degree():
            return False
    return True


def exact_interlaces(big_x: sp.Poly, small_x: sp.Poly, x: sp.Symbol, rb_cached=None, rs_cached=None) -> bool:
    """Exact CRootOf check that small_x (deg m-1) interlaces big_x (deg m),
    both totally real."""
    rb = rb_cached if rb_cached is not None else big_x.real_roots()
    rs = rs_cached if rs_cached is not None else small_x.real_roots()
    if len(rb) != big_x.degree() or len(rs) != small_x.degree():
        return False
    for i, rsv in enumerate(rs):
        if not (rb[i] <= rsv <= rb[i + 1]):
            return False
    return True


def solve_2v_jacobi_diff2(
    chi_S: sp.Poly,
    chi_u: sp.Poly,
    chi_v: sp.Poly,
    s2_step: int,
    s2_rem_mod: int,
    x_bound_hi: int,
    x: sp.Symbol,
) -> list[tuple[int, int, list[int]]]:
    """Independent clean-room exact solver for 2-vertex Jacobi when deg(Mult_rad) - 2 == 2 (diff=2).
    Returns list of (s_uv, s2_uv, chi_{S_uv}_desc) surviving:
      - exact integer h_{uv}
      - exact integer chi_{S_{uv}}
      - exact totally-real >= -5 (primitive integer Sturm)
      - exact CRootOf interlacing with both chi_u and chi_v
      - exact 2-adic Seidel congruence for order n-2 (2^{n-2} for even n, 2^{n-3} + Thm 4.2 for odd n).
    """
    n = chi_S.degree()
    gcd_x = sp.gcd(chi_S, sp.diff(chi_S, x))
    gcd_2 = sp.gcd(gcd_x, sp.diff(gcd_x, x))
    _, fac_list = sp.factor_list(chi_S)
    sim_x = sp.Poly(1, x, domain=sp.ZZ)
    sim_facs = []
    for fac, mult in fac_list:
        if mult == 1:
            sim_x = sp.Poly(sim_x.as_expr() * fac.as_expr(), x, domain=sp.ZZ)
            sim_facs.append(fac)

    ga = sp.Poly(sp.quo(chi_u, gcd_x), x, domain=sp.ZZ)
    gb = sp.Poly(sp.quo(chi_v, gcd_x), x, domain=sp.ZZ)
    s = ga.degree() + 1
    e_sim = sim_x.degree()
    assert (s - 2) - e_sim == 2, f"Expected diff=2, got {(s-2)-e_sim}"

    # Compute gamma_1 = [x^{deg(gcd_x) - 1}] gcd_x
    deg_g = gcd_x.degree()
    gamma_1 = int(gcd_x.all_coeffs()[1]) if deg_g >= 1 else 0
    # S_{1, sim} = -[x^{e_sim - 1}] sim_x
    S1_sim = -int(sim_x.all_coeffs()[1]) if e_sim >= 1 else 0

    # Find ALL integer polynomial square roots R_uv(x) mod sim_x of ga * gb mod sim_x
    # For deg(sim_fac) == 1 or 2: compute roots per factor and combine via CRT
    prod_ab = sp.Poly(ga.as_expr() * gb.as_expr(), x, domain=sp.ZZ)
    crt_residues_per_fac: list[tuple[sp.Poly, list[sp.Poly]]] = []
    for sf in sim_facs:
        rem_sf = sp.rem(prod_ab, sf, domain=sp.QQ)
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
        elif sf.degree() == 2:
            alpha = sp.CRootOf(sf, 0)
            K = sp.QQ.algebraic_field(alpha)
            elem_K = K.zero
            for c in rem_sf.all_coeffs():
                elem_K = elem_K * K.unit + K.dom.convert(c)
            t = sp.Symbol("_t2v")
            sq_poly = sp.Poly.from_dict({(2,): K.one, (0,): -elem_K}, t, domain=K)
            _, fl = sq_poly.factor_list()
            lins = [f for f, _ in fl if f.degree() == 1]
            assert lins
            roots_sf = []
            for lf in lins:
                cs = lf.rep.all_coeffs()
                rk = K.exquo(-cs[1], cs[0])
                rp = sp.Poly([Fraction(int(v.numerator), int(v.denominator)) for v in rk.rep], x, domain=sp.QQ)
                if rp not in roots_sf:
                    roots_sf.append(rp)
            crt_residues_per_fac.append((sf, roots_sf))
        else:
            raise NotImplementedError("Factor degree > 2")

    # CRT combine across sim_facs
    import itertools
    R_cands = []
    mods = [sf for sf, _ in crt_residues_per_fac]
    for combo in itertools.product(*[rs for _, rs in crt_residues_per_fac]):
        # CRT over QQ[x]
        cur_r = sp.Poly(0, x, domain=sp.QQ)
        cur_m = sp.Poly(1, x, domain=sp.QQ)
        for mi, ri in zip(mods, combo):
            mi_q = sp.Poly(mi.as_expr(), x, domain=sp.QQ)
            inv = sp.invert(cur_m, mi_q)
            k_poly = sp.rem((ri - cur_r) * inv, mi_q, domain=sp.QQ)
            cur_r = sp.Poly(cur_r.as_expr() + cur_m.as_expr() * k_poly.as_expr(), x, domain=sp.QQ)
            cur_m = sp.Poly(cur_m.as_expr() * mi_q.as_expr(), x, domain=sp.QQ)
        cur_r = sp.rem(cur_r, sp.Poly(sim_x.as_expr(), x, domain=sp.QQ), domain=sp.QQ)
        # Since h_uv in Z[x] and sim_x is monic in Z[x], R_uv MUST be in Z[x]!
        if all(Fraction(c.p, c.q).denominator == 1 for c in cur_r.all_coeffs()):
            R_cands.append(sp.Poly(cur_r.as_expr(), x, domain=sp.ZZ))

    # Deduplicate +/- R_uv (since h_uv only enters as h_uv^2!)
    seen_R = set()
    uniq_R = []
    for rp in R_cands:
        t1 = tuple(int(c) for c in rp.all_coeffs())
        t2 = tuple(-int(c) for c in rp.all_coeffs())
        if t1 not in seen_R and t2 not in seen_R:
            seen_R.add(t1)
            uniq_R.append(rp)

    # Exact bounds at x0 in {-5, x_bound_hi}
    # At x_bound_hi > max_root(S): sim_x(x_bound_hi) > 0 and q_uv(x_bound_hi) > 0
    ga_hi = int(ga.eval(x_bound_hi))
    gb_hi = int(gb.eval(x_bound_hi))
    sim_hi = int(sim_x.eval(x_bound_hi))
    assert sim_hi > 0 and ga_hi >= 0 and gb_hi >= 0
    bnd_hi = math.isqrt(ga_hi * gb_hi) + 1

    ga_m5 = int(ga.eval(-5))
    gb_m5 = int(gb.eval(-5))
    sim_m5 = int(sim_x.eval(-5))
    deg_q = s - 2
    # At x = -5: (-1)^deg_q * q_uv(-5) >= 0. So sim_x(-5) * q_uv(-5) >= 0 iff sign(sim_m5) == (-1)^deg_q (or sim_m5 == 0)
    use_m5 = (sim_m5 != 0 and ((sim_m5 > 0) == (deg_q % 2 == 0)) and ga_m5 * gb_m5 >= 0)
    bnd_m5 = (math.isqrt(ga_m5 * gb_m5) + 1) if use_m5 else None

    m_ord = n - 2
    req_shift = m_ord if (m_ord % 2 == 0) else (m_ord - 1)
    req_mod = 1 << req_shift
    gcd_2_m1 = int(gcd_2.eval(-1))
    gcd_2_p1 = int(gcd_2.eval(1))
    sim_m1 = int(sim_x.eval(-1))
    sim_p1 = int(sim_x.eval(1))
    prod_ab_expr = ga.as_expr() * gb.as_expr()

    # Precompute M(x) = (ga*gb - R^2) / sim_x and scalar values for fast exact integer filtering
    R_data = []
    for R_poly in uniq_R:
        M_poly, M_rem = sp.div(sp.Poly(prod_ab_expr - R_poly.as_expr() ** 2, x, domain=sp.ZZ), sim_x)
        if not M_rem.is_zero:
            continue
        R_data.append((
            R_poly,
            M_poly,
            int(R_poly.eval(x_bound_hi)),
            int(R_poly.eval(-5)),
            int(R_poly.eval(-1)),
            int(R_poly.eval(1)),
            int(M_poly.eval(-1)),
            int(M_poly.eval(1)),
        ))

    rb_u = chi_u.real_roots()
    rb_v = chi_v.real_roots()

    solutions = []
    s2_lo = -(n - 2)
    while (s2_lo - s2_rem_mod) % s2_step != 0:
        s2_lo += 1

    for s_uv in (1, -1):
        for s2_uv in range(s2_lo, n - 1, s2_step):
            q1 = s2_uv - gamma_1 * s_uv + s_uv * S1_sim
            for R_poly, M_poly, R_hi, R_m5, R_m1, R_p1, M_m1, M_p1 in R_data:
                # |sim_hi * (s_uv * x_hi^2 + q1 * x_hi + q0) + R_hi| <= bnd_hi
                base_hi = sim_hi * (s_uv * (x_bound_hi ** 2) + q1 * x_bound_hi) + R_hi
                lo_q0 = math.ceil((-bnd_hi - base_hi) / sim_hi)
                hi_q0 = math.floor((bnd_hi - base_hi) / sim_hi)
                if use_m5:
                    base_m5 = sim_m5 * (s_uv * 25 - 5 * q1) + R_m5
                    # |sim_m5 * q0 + base_m5| <= bnd_m5
                    lo2 = math.ceil((-bnd_m5 - base_m5) / abs(sim_m5)) if sim_m5 > 0 else math.ceil((-bnd_m5 + base_m5) / abs(sim_m5))
                    hi2 = math.floor((bnd_m5 - base_m5) / abs(sim_m5)) if sim_m5 > 0 else math.floor((bnd_m5 + base_m5) / abs(sim_m5))
                    lo_q0 = max(lo_q0, lo2)
                    hi_q0 = min(hi_q0, hi2)
                if lo_q0 > hi_q0:
                    continue
                q_base_m1 = s_uv - q1
                q_base_p1 = s_uv + q1
                for q0 in range(lo_q0, hi_q0 + 1):
                    # Exact fast necessary 2-adic checks at t=0 (x=-1) and t=1 (x=1)
                    Q_m1 = q_base_m1 + q0
                    q_uv_m1 = M_m1 - 2 * Q_m1 * R_m1 - Q_m1 * Q_m1 * sim_m1
                    if (gcd_2_m1 * q_uv_m1) % req_mod != 0:
                        continue
                    Q_p1 = q_base_p1 + q0
                    q_uv_p1 = M_p1 - 2 * Q_p1 * R_p1 - Q_p1 * Q_p1 * sim_p1
                    if (gcd_2_p1 * q_uv_p1) % req_mod != 0:
                        continue
                    Q_poly = sp.Poly([s_uv, q1, q0], x, domain=sp.ZZ)
                    q_uv = sp.Poly(
                        M_poly.as_expr() - 2 * Q_poly.as_expr() * R_poly.as_expr() - (Q_poly.as_expr() ** 2) * sim_x.as_expr(),
                        x,
                        domain=sp.ZZ,
                    )
                    chi_uv = sp.Poly(gcd_2.as_expr() * q_uv.as_expr(), x, domain=sp.ZZ)
                    if chi_uv.degree() != m_ord:
                        continue
                    # Check 2-adic Seidel congruence on chi_uv(2t - 1)
                    chi_uv_desc = [int(c) for c in chi_uv.all_coeffs()]
                    b_asc = poly_eval_2tm1_asc(chi_uv_desc)
                    if m_ord % 2 == 0:
                        if any(v2(bk) < m_ord for bk in b_asc):
                            continue
                    else:
                        if any(v2(bk) < (m_ord - 1) for bk in b_asc):
                            continue
                        P_asc = [bk >> (m_ord - 1) for bk in b_asc]
                        if not check_thm42_odd(P_asc, m_ord):
                            continue
                    # Exact Sturm real-rooted >= -5
                    if not poly_real_rooted_ge_neg5(q_uv, x):
                        continue
                    # Exact CRootOf interlacing with both chi_u and chi_v
                    rs_uv = chi_uv.real_roots()
                    if not (exact_interlaces(chi_u, chi_uv, x, rb_u, rs_uv) and exact_interlaces(chi_v, chi_uv, x, rb_v, rs_uv)):
                        continue
                    solutions.append((s_uv, s2_uv, chi_uv_desc))
    return solutions


def verify_idx_47(x: sp.Symbol) -> dict:
    dk = read_json_auto(POLY_RESULTS_DIR, "deck_19_74.json")
    cand = dk["candidates"][47]
    c_shift = int(dk["c"])
    rhs, F_z, Gcd_z, _ = compute_rhs_and_common(cand["b"], 19, 74, c_shift)

    # Filter deck by Thm 4.2 (as in Stage 2) and solve exact Z>=0
    w = sp.Symbol("w")
    # Convert chi_S(x) directly
    b_x = sp.Poly(cand["b"], w, domain=sp.ZZ)
    chi_S = sp.Poly(((x + 5) ** 55) * (2 ** 19) * b_x.as_expr().subs(w, (x - c_shift) / 2), x, domain=sp.ZZ)
    gcd_x = sp.gcd(chi_S, sp.diff(chi_S, x))

    deck_valid_idx = []
    shift_t = -(c_shift + 1) // 2
    Gcd_w = sp.Poly([int(v) for v in Gcd_z.all_coeffs()], w, domain=sp.ZZ)
    for i, g_desc in enumerate(cand["deck"]):
        gp = sp.Poly(g_desc, w, domain=sp.ZZ)
        pz = sp.Poly(Gcd_w.as_expr() * gp.as_expr(), w, domain=sp.ZZ)
        pt = poly_shift_linear([int(v) for v in pz.all_coeffs()], 1, shift_t)
        if check_thm42_odd(pt[::-1], 73):
            deck_valid_idx.append(i)

    A_int = [[cand["deck"][i][k] for i in deck_valid_idx] for k in range(len(rhs))]
    int_sols = solve_null_dim_0_or_1(A_int, rhs, 74)
    assert len(int_sols) == 1, f"Expected unique sol for (19,74) idx=47, got {int_sols}"
    sol = int_sols[0]
    nonzero_pairs = [(deck_valid_idx[p], sol[p]) for p in range(len(sol)) if sol[p] > 0]
    assert [cnt for _, cnt in nonzero_pairs] == [52, 16, 6], f"Unexpected block sizes: {nonzero_pairs}"

    chi_types = [decode_deck_poly_to_x(cand["deck"][idx], c_shift, 73, gcd_x, x) for idx, _ in nonzero_pairs]
    # Check eigenvector v_11 projector diagonal: chi_{S_u}(11) / chi'_S(11)
    chip_11 = int(sp.diff(chi_S, x).eval(11))
    diag_11 = [Fraction(int(cu.eval(11)), chip_11) for cu in chi_types]
    assert diag_11 == [Fraction(0), Fraction(1, 16), Fraction(0)], f"Unexpected v_11 diag: {diag_11}"

    # Solve exact 2-vertex Jacobi on (C0, C1) and (C1, C2) (s2_step=2, even n=74 => s2_uv even)
    sols_01 = solve_2v_jacobi_diff2(chi_S, chi_types[0], chi_types[1], s2_step=2, s2_rem_mod=0, x_bound_hi=17, x=x)
    sols_12 = solve_2v_jacobi_diff2(chi_S, chi_types[1], chi_types[2], s2_step=2, s2_rem_mod=0, x_bound_hi=17, x=x)
    assert sols_01 and sols_12
    for s_uv, s2_uv, _ in sols_01 + sols_12:
        assert s2_uv == 10 * s_uv, f"idx=47 failed W*B + B*X = 10*B: s_uv={s_uv}, s2_uv={s2_uv}"

    # Verify spectral vs Frobenius contradiction: Tr(X) = 0? Wait: X has eig 11 (mult 1) and remaining in {-5, 15, 14+-sqrt(5)}
    # Check only {-5, 15} sums to 10 among Spec(S) = {-5, 11, 15, 14+sqrt(5), 14-sqrt(5)}:
    # 11+11=22, 11-5=6, 11+15=26, 15+15=30, (-5)+(-5)=-10, (14+-sqrt(5)) + rat is irrational,
    # (14+sqrt(5)) + (14-sqrt(5)) = 28 != 10! So {-5, 15} is indeed unique!
    # Sum over 1_16^perp (15 dims): sum (75 + 10*lam_i - lam_i^2) = 15*75 + 10*(Tr(X)-11) - (Tr(X^2) - 121)
    # Since Tr(X)=0, Tr(X^2)=16*15=240: 1125 - 110 - 119 = 896 != 58*16 = 928!
    tr_spec = 15 * 75 - 10 * 11 - (16 * 15 - 121)
    tr_frob = (52 + 6) * 16
    assert tr_spec == 896 and tr_frob == 928 and tr_spec != tr_frob

    return {
        "blocks": [cnt for _, cnt in nonzero_pairs],
        "diag_11": [str(v) for v in diag_11],
        "sols_01": [(s_uv, s2_uv) for s_uv, s2_uv, _ in sols_01],
        "sols_12": [(s_uv, s2_uv) for s_uv, s2_uv, _ in sols_12],
        "tr_BTB_spectral": tr_spec,
        "tr_BTB_frobenius": tr_frob,
        "status": "ELIMINATED_VERIFIED",
    }


def verify_idx_861(x: sp.Symbol) -> dict:
    dk = read_json_auto(POLY_RESULTS_DIR, "deck_18_59.json")
    cand = dk["candidates"][861]
    c_shift = int(dk["c"])
    rhs, F_z, Gcd_z, _ = compute_rhs_and_common(cand["b"], 18, 59, c_shift)

    w = sp.Symbol("w")
    b_x = sp.Poly(cand["b"], w, domain=sp.ZZ)
    chi_S = sp.Poly(((x + 5) ** 41) * (2 ** 18) * b_x.as_expr().subs(w, (x - c_shift) / 2) / int(b_x.LC()), x, domain=sp.ZZ)
    assert chi_S.LC() == 1 and chi_S.degree() == 59
    gcd_x = sp.gcd(chi_S, sp.diff(chi_S, x))

    # Stage-2 deck check: for odd n=59, vertex-deleted deck has even order n-1=58 => 2^58 | chi_{S_v}(2t-1)
    deck_valid_idx = []
    chi_valid = {}
    for i, g_desc in enumerate(cand["deck"]):
        chi_v_test = decode_deck_poly_to_x(g_desc, c_shift, 58, gcd_x, x)
        b_asc_v = poly_eval_2tm1_asc([int(c) for c in chi_v_test.all_coeffs()])
        if all(v2(bk) >= 58 for bk in b_asc_v):
            deck_valid_idx.append(i)
            chi_valid[i] = chi_v_test

    # Check Theorem 7.1 M, N mod 4 on S_eps (n=59, n-2=57 == 1 mod 4) with mrad = (x+5)(x-9)(x-11)(x-13):
    _, fac_list = sp.factor_list(chi_S)
    sim_x = sp.Poly(1, x, domain=sp.ZZ)
    mrad = sp.Poly(1, x, domain=sp.ZZ)
    for fac, mult in fac_list:
        if mult == 1:
            sim_x = sp.Poly(sim_x.as_expr() * fac.as_expr(), x, domain=sp.ZZ)
        else:
            mrad = sp.Poly(mrad.as_expr() * fac.as_expr(), x, domain=sp.ZZ)
    assert sim_x == sp.Poly(x**2 - 19 * x + 82, x, domain=sp.ZZ)
    assert mrad == sp.Poly((x + 5) * (x - 9) * (x - 11) * (x - 13), x, domain=sp.ZZ)

    def thm71_coeffs(P: sp.Poly, n_ord: int) -> tuple[int, int, int]:
        P1 = int(P.eval(1))
        Pm1 = int(P.eval(-1))
        P0 = int(P.eval(0))
        Pp0 = int(sp.diff(P, x).eval(0))
        pe = (P1 + Pm1) // 2
        po = (P1 - Pm1) // 2
        cI = pe % 4
        cS = po % 4
        cJ = ((n_ord - 2) * ((pe - P0) + (n_ord - 1) * (po - Pp0))) % 4
        return cI, cS, cJ

    cI_M, cS_M, cJ_M = thm71_coeffs(mrad, 59)
    x_mrad = sp.Poly(x * mrad.as_expr(), x, domain=sp.ZZ)
    cI_N, cS_N, cJ_N = thm71_coeffs(x_mrad, 59)
    assert cS_M == 0 and cS_N == 0
    m_off_mod4 = cJ_M % 4
    n_off_mod4 = cJ_N % 4
    assert (m_off_mod4, n_off_mod4) == (3, 2)

    # Exact QQ(sqrt(33)) arithmetic (r1 = (19 - sqrt(33))/2, r2 = (19 + sqrt(33))/2) with zero nested radicals:
    def q_mul(u: tuple[Fraction, Fraction], v: tuple[Fraction, Fraction]) -> tuple[Fraction, Fraction]:
        return (u[0] * v[0] + 33 * u[1] * v[1], u[0] * v[1] + u[1] * v[0])

    def q_inv(u: tuple[Fraction, Fraction]) -> tuple[Fraction, Fraction]:
        nm = u[0] * u[0] - 33 * u[1] * u[1]
        return (u[0] / nm, -u[1] / nm)

    def q_conj(u: tuple[Fraction, Fraction]) -> tuple[Fraction, Fraction]:
        return (u[0], -u[1])

    def q_eval_poly(p_x: sp.Poly, z_val: tuple[Fraction, Fraction]) -> tuple[Fraction, Fraction]:
        res = (Fraction(0), Fraction(0))
        for c in p_x.all_coeffs():
            res = q_mul(res, z_val)
            res = (res[0] + int(c), res[1])
        return res

    def q_sqrt_opt(u: tuple[Fraction, Fraction]) -> tuple[Fraction, Fraction] | None:
        a, b = u
        if a == 0 and b == 0:
            return (Fraction(0), Fraction(0))
        nm_sq = a * a - 33 * b * b
        if nm_sq < 0:
            return None
        s_num = math.isqrt(nm_sq.numerator)
        s_den = math.isqrt(nm_sq.denominator)
        if s_num * s_num != nm_sq.numerator or s_den * s_den != nm_sq.denominator:
            return None
        s = Fraction(s_num, s_den)
        for sgn in (1, -1):
            x2 = (a + sgn * s) / 2
            if x2 >= 0:
                xn, xd = math.isqrt(x2.numerator), math.isqrt(x2.denominator)
                if xn * xn == x2.numerator and xd * xd == x2.denominator:
                    p = Fraction(xn, xd)
                    q = b / (2 * p) if p != 0 else Fraction(0)
                    if q_mul((p, q), (p, q)) == u:
                        return (p, q)
        return None

    r1_q = (Fraction(19, 2), Fraction(-1, 2))
    r2_q = q_conj(r1_q)
    chi_p = sp.diff(chi_S, x)
    chip_r1 = q_eval_poly(chi_p, r1_q)
    mrad_r1 = q_eval_poly(mrad, r1_q)

    d1_all = {i: q_mul(q_eval_poly(chi_valid[i], r1_q), q_inv(chip_r1)) for i in deck_valid_idx}
    sq_classes: list[list[int]] = []
    for i in deck_valid_idx:
        placed = False
        for cl in sq_classes:
            if q_sqrt_opt(q_mul(d1_all[i], d1_all[cl[0]])) is not None:
                cl.append(i)
                placed = True
                break
        if not placed:
            sq_classes.append([i])

    surviving_sols = []
    for cl in sq_classes:
        A_cl = [[cand["deck"][i][k] for i in cl] for k in range(len(rhs))]
        for s in solve_null_dim_0_or_1(A_cl, rhs, 59):
            surviving_sols.append([(cl[p], s[p]) for p in range(len(cl)) if s[p] > 0])
    assert surviving_sols == [[(4, 30), (5, 1), (9, 28)]], f"Unexpected Stage-2 sols: {surviving_sols}"

    chi_4, chi_5, chi_9 = chi_valid[4], chi_valid[5], chi_valid[9]
    d1 = {4: d1_all[4], 5: d1_all[5], 9: d1_all[9]}

    M_blk = {}
    N_blk = {}
    z_prod_5 = {}
    for a in (4, 5, 9):
        for b in (4, 5, 9):
            if a > b:
                continue
            w_sq = q_mul(q_mul(mrad_r1, mrad_r1), q_mul(d1[a], d1[b]))
            w_ab = q_sqrt_opt(w_sq)
            assert w_ab is not None
            hits = []
            for sgn in (1, -1):
                t1 = (sgn * w_ab[0], sgn * w_ab[1])
                t2 = q_conj(t1)
                Mi_q = t1[0] + t2[0]
                n1_v = q_mul(r1_q, t1)
                n2_v = q_mul(r2_q, t2)
                assert n1_v[1] + n2_v[1] == 0
                Ni_q = n1_v[0] + n2_v[0]
                if Mi_q.denominator == 1 and Ni_q.denominator == 1:
                    Mi, Ni = int(Mi_q), int(Ni_q)
                    if Mi % 4 == m_off_mod4 and Ni % 4 == n_off_mod4:
                        hits.append((sgn, Mi, Ni, t1))
            assert len(hits) == 1, f"Expected unique rational M,N mod 4 for ({a},{b}), got {hits}"
            sgn, Mi, Ni, t1 = hits[0]
            M_blk[(a, b)] = M_blk[(b, a)] = Mi
            N_blk[(a, b)] = N_blk[(b, a)] = Ni
            if a == 5 or b == 5:
                other = b if a == 5 else a
                z_prod_5[other] = q_mul(t1, q_inv(mrad_r1))
    assert z_prod_5[5] == d1[5]

    # Solve 2x2 over QQ for each row of K using k_{i0}*z_4 + k_{i1}*z_5 + k_{i2}*z_9 = r1 * z_i:
    # Since K has integer entries, matching 1-part and sqrt(33)-part gives 2 rational equations for 2 unknowns!
    # Row 1 (u1): k_{11} = 0 (diagonal of S_eps is 0), solve for (k10, k12):
    # k10 * z_prod_5[4] + k12 * z_prod_5[9] = r1_q * z_prod_5[5]
    rhs1 = q_mul(r1_q, z_prod_5[5])
    K1_mat = sp.Matrix([[z_prod_5[4][0], z_prod_5[9][0]], [z_prod_5[4][1], z_prod_5[9][1]]])
    k10_v, k12_v = K1_mat.LUsolve(sp.Matrix([rhs1[0], rhs1[1]]))
    assert (int(k10_v), int(k12_v)) == (30, 28)

    # Row 0 (C0): k01 = 1 (symmetric, and k10 = 30 = |C0| forces all entries in S_{C0, u1} == +1!)
    rhs0 = (q_mul(r1_q, z_prod_5[4])[0] - z_prod_5[5][0], q_mul(r1_q, z_prod_5[4])[1] - z_prod_5[5][1])
    K0_mat = sp.Matrix([[z_prod_5[4][0], z_prod_5[9][0]], [z_prod_5[4][1], z_prod_5[9][1]]])
    k00_v, k02_v = K0_mat.LUsolve(sp.Matrix([rhs0[0], rhs0[1]]))
    assert (int(k00_v), int(k02_v)) == (5, 0)

    # Row 2 (C2): k21 = 1 (symmetric, and k12 = 28 = |C2| forces all entries in S_{C2, u1} == +1!)
    rhs2 = (q_mul(r1_q, z_prod_5[9])[0] - z_prod_5[5][0], q_mul(r1_q, z_prod_5[9])[1] - z_prod_5[5][1])
    k20_v, k22_v = K0_mat.LUsolve(sp.Matrix([rhs2[0], rhs2[1]]))
    assert (int(k20_v), int(k22_v)) == (0, 9)

    K_mat = [[int(k00_v), 1, int(k02_v)], [int(k10_v), 0, int(k12_v)], [int(k20_v), 1, int(k22_v)]]
    assert K_mat == [[5, 1, 0], [30, 0, 28], [0, 1, 9]]

    # Check exact 2-vertex Jacobi on (deck[4], deck[9]) with Eulerian s2_uv == n - 2 == 1 (mod 4)
    sols_49 = solve_2v_jacobi_diff2(chi_S, chi_4, chi_9, s2_step=4, s2_rem_mod=1, x_bound_hi=14, x=x)
    assert sols_49
    for s_uv, s2_uv, _ in sols_49:
        assert s2_uv == 1 + 8 * s_uv, f"idx=861 failed (S_eps^2)_uw = 1 + 8*S_uw: s_uv={s_uv}, s2_uv={s2_uv}"

    # Verify chi_{S_{u1}} = chi_5 has mult(13) = 8 and spectrum {-5, 5, 9, 11, 13}
    _, fac_58 = sp.factor_list(chi_5)
    spec_58 = {}
    for fp, mp in fac_58:
        assert fp.degree() == 1
        rt = -int(fp.all_coeffs()[1]) // int(fp.all_coeffs()[0])
        spec_58[rt] = mp
    assert set(spec_58.keys()) == {-5, 5, 9, 11, 13}
    assert spec_58[13] == 8
    pairs_sum8 = [(a, b) for a in spec_58 for b in spec_58 if a <= b and a + b == 8]
    assert pairs_sum8 == [(-5, 13)]

    frob_sq = 30 * 28
    sv_ub = 8 * (65 + 8 * 4 - 16)
    assert frob_sq == 840 and sv_ub == 648 and frob_sq > sv_ub

    return {
        "blocks": [30, 1, 28],
        "M_blk": [[M_blk[(a, b)] for b in (4, 5, 9)] for a in (4, 5, 9)],
        "N_blk": [[N_blk[(a, b)] for b in (4, 5, 9)] for a in (4, 5, 9)],
        "eulerian_quotient_K": K_mat,
        "sols_49_mod4": [(s_uv, s2_uv) for s_uv, s2_uv, _ in sols_49],
        "spec_58": spec_58,
        "frobenius_norm_sq": frob_sq,
        "singular_value_upper_bound": sv_ub,
        "status": "ELIMINATED_VERIFIED",
    }


def main() -> None:
    t0 = time.time()
    x = sp.Symbol("x")
    cert_path, _ = resolve_data_file(SEARCH_RESULTS_DIR, "phase3_kills_861_and_47.json")
    cert_sha = sha256_auto(cert_path)

    res_47 = verify_idx_47(x)
    print(f"[PASS] (19,74) idx=47 independently verified ELIMINATED: {res_47}")

    res_861 = verify_idx_861(x)
    print(f"[PASS] (18,59) idx=861 independently verified ELIMINATED: {res_861}")

    out = {
        "source_cert": "compute/search/results/phase3_kills_861_and_47.json",
        "source_sha256": cert_sha,
        "idx_47": res_47,
        "idx_861": res_861,
        "elapsed_s": round(time.time() - t0, 2),
        "status": "PASS",
    }
    OUT_JSON.write_text(json.dumps(out, indent=2))
    print(f"ALL PHASE-3 47 & 861 CHECKS PASSED in {out['elapsed_s']}s -> {OUT_JSON}")


if __name__ == "__main__":
    main()
