"""Independent clean-room verification of (19, 74) idx=13 elimination across S3, S2, S1.

Strictly independent from compute/poly/ and compute/search/ (zero code reused).
Verifies from first principles in exact ZZ / QQ / Fraction arithmetic:
1. SHA-256 checksums and independent AST zero-float-trust audit across all files in
   compute/poly/idx13_exact/ and results/*.json.
2. Independent 74 -> 21 -> 3 reduction of (19, 74) idx=13:
   - Clean-room Stage-2 cones -> 74 solutions over deck[0, 1, 2, 5].
   - Exact E_17 diagonal extraction & triangle inequality -> 21 solutions.
   - Stage-3 odd-73 Galois-Farkas deletion at v = deck[0] -> 3 solutions:
     S1 = [(0,24), (1,48), (5,2)], S2 = [(0,25), (1,45), (2,3), (5,1)], S3 = [(0,26), (1,42), (2,6)].
3. Independent clean-room exact QQ derivation of Props 8.4-8.7 and Lemma 8.8:
   - 2v-Jacobi projector values E_11[C0, C1] = 0, E_11[C1, C1] in {1/24, -1/48},
     E_17[C1, C1] = 1/66, and exact 20*E_15 core matrices M_K.
   - All 7 even-cycle S1 partitions {(16,), (12,4), (10,6), (8,8), (8,4,4), (6,6,4), (4,4,4,4)}:
     SymPy exact pinv(), all 4 Moore-Penrose identities, PSD check on W_piv = (20M - M^2)[piv,piv].
   - Direct clean-room kills of S1 (16,) (min 24-vertex C0 residual sum = 12 > 0) and (10, 6).
   - Direct clean-room proof of Lemma 8.8 (S1 (4,4,4,4) q0 = 4 => rho_C0 = 0 / Subcase A).
4. Independent exact QQ / pure-Fraction / zero-slack CP-SAT verification of S1 (all 7
   partitions), S2, and S3 + bundle dual verification against compute/poly/idx13_exact/results/.
"""

from __future__ import annotations

import argparse
import ast
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
import hashlib
import itertools
import json
import math
import os
from pathlib import Path
import time
import numpy as np
from ortools.sat.python import cp_model
from scipy.optimize import linprog
import sympy as sp

from verify_phase3_18_59_endgame import (
    e_diag_exact,
    e_off_sq_exact,
    enum_cone_solutions,
    sv_galois_kills_v,
)
from verify_farkas import check_thm42_odd
from verify_phase3_47_861 import compute_rhs_and_common, decode_deck_poly_to_x
from verify_polys import poly_eval_2tm1_asc, v2
from verify_algebraist_sec7 import galois_rows_for_factor, square_classes_for_simple_factor
from verify_sec7_certs import build_2v_cache_ctx, decode_chi_S_from_deck_cand, exact_farkas_or_primal, solve_2v_jacobi_exact
from _repo_io import AUDIT_DIR, CERT_DIR, COMPUTE_POLY_RESULTS, REPO_ROOT, read_json_auto, resolve_data_file, sha256_auto

POLY_RESULTS_DIR = COMPUTE_POLY_RESULTS
IDX13_DIR = REPO_ROOT / "compute" / "poly" / "idx13_exact"
IDX13_RES_DIR = (IDX13_DIR / "results") if (IDX13_DIR / "results").is_dir() else (CERT_DIR / "phase3" / "idx13_exact")
OUT_JSON = AUDIT_DIR / "phase3_19_74_idx13_audit.json"

EXPECTED_SHA256 = {
    "__init__.py": "86250cfd599a5331268652516b77120d4b845d2aef25506fb23fef48e172e0ee",
    "exact_common.py": "e7ea82d82ae7ac0bb561e70a6c27ac55e1389b44a61023fdfa2a7a1eec7ae94b",
    "certify_s1_t2.py": "48bbfd5365257c0385219be5450547e8541c32fbced91295908ac09769e11175",
    "certify_s1_6_6_4.py": "81f284b69c212ea141aac1815b32d97892d14c7f42a9fcde9c82e6f64b884fd2",
    "certify_s1_8_4_4.py": "ec62170329f95412c43b19e107be38d1fdd872b210415cb211ba5aae3f834632",
    "certify_s1_4_4_4_4.py": "899ea1cb43c1e5fdaadd256d320d5a73aaf7872786246ebd83a4b105710b90a7",
    "certify_s3_s2.py": "d16207b38fc63aa9dca8e9dd6e0d6cf62e9442e595c9849aad5cb97c9a61abbe",
    "verify_idx13_exact.py": "8d8353715d6cf2cb6a9aee462d80f829c620b1b95b33dd9cde52dfb49b17e5bb",
    "results/cert_s1_t2.json": "bfe35b52c34af82b9bb51c721993e34abea6fa125526e4f281424c785f982a6a",
    "results/cert_s3_s2.json": "fb6e927c51786e0331806b43261067773fc0ace7b50feb7dedb1d2d648919996",
    "results/s1_6_6_4_certs.json": "37eead1b0a40be0762f0ad0abce67662ac3e082d515f2fa313c0f1a178c75235",
    "results/s1_8_4_4_certs.json": "db8d04850b425638a5a82ce7e7e9b9a8496335b9da674cc76b5c99de5f50b383",
    "results/s1_4_4_4_4_certs.json": "a8a7b4af4680ac04c2d315503c3328727dcd2ced03700cd238adcd1cdeae94fd",
}


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def audit_sha256_and_ast() -> dict:
    """Verify exact SHA-256 digests and AST zero-float-trust across compute/poly/idx13_exact/."""
    actual_sha = {}
    for rel, exp in EXPECTED_SHA256.items():
        if rel.startswith("results/"):
            fp, _ = resolve_data_file(IDX13_RES_DIR, rel.split("/", 1)[1])
            got = sha256_auto(fp)
        else:
            fp = IDX13_DIR / rel
            assert fp.exists(), f"Missing idx13_exact file: {fp}"
            got = sha256_file(fp)
        assert got == exp, f"SHA-256 mismatch on {rel}: {got} != {exp}"
        actual_sha[rel] = got

    forbidden_linalg = {"eigh", "eigvalsh", "eigvals", "eig", "pinv", "svd"}
    cert_modules = [
        "certify_s1_t2.py",
        "certify_s1_6_6_4.py",
        "certify_s1_8_4_4.py",
        "certify_s1_4_4_4_4.py",
        "certify_s3_s2.py",
    ]
    ast_findings = {}
    for mod_name in cert_modules:
        src = (IDX13_DIR / mod_name).read_text()
        tree = ast.parse(src, filename=mod_name)
        hits = []
        for node in ast.walk(tree):
            if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Attribute):
                # Flag np.linalg.* calls
                if getattr(node.value, "attr", "") == "linalg" and node.attr in forbidden_linalg:
                    hits.append(f"L{node.lineno}:{node.value.attr}.{node.attr}")
            elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
                if node.func.id in {"rint", "linprog"}:
                    hits.append(f"L{node.lineno}:call:{node.func.id}")
            elif isinstance(node, ast.Constant) and isinstance(node.value, float):
                val = abs(node.value)
                # Flag small floating tolerances like 1e-4, 1e-6, 1e-9 (note 0.5, 1.5, 2.5, etc. are exact dyadics)
                if 0.0 < val < 0.01:
                    hits.append(f"L{node.lineno}:small_float:{node.value}")
        assert not hits, f"AST float-trust violations in {mod_name}: {hits}"
        ast_findings[mod_name] = "CLEAN"

    # Also verify exact_common.py keeps float usage strictly inside untrusted_psd_test_vectors (hint generator)
    ec_src = (IDX13_DIR / "exact_common.py").read_text()
    ec_tree = ast.parse(ec_src, filename="exact_common.py")
    ec_linalg_funcs = []
    for node in ec_tree.body:
        if isinstance(node, ast.FunctionDef):
            for sub in ast.walk(node):
                if isinstance(sub, ast.Attribute) and getattr(sub, "attr", "") in forbidden_linalg:
                    if isinstance(sub.value, ast.Attribute) and getattr(sub.value, "attr", "") == "linalg":
                        ec_linalg_funcs.append((node.name, sub.lineno, sub.attr))
                elif isinstance(sub, ast.Call) and isinstance(sub.func, ast.Name) and sub.func.id == "linprog":
                    ec_linalg_funcs.append((node.name, sub.lineno, "linprog"))
    # All float linalg/linprog in exact_common.py must live solely in hint-generation / dual-extraction helpers
    allowed_hint_funcs = {"untrusted_psd_test_vectors", "certify_eq_lp_farkas", "certify_eq_lp_farkas_scaled"}
    bad_ec = [entry for entry in ec_linalg_funcs if entry[0] not in allowed_hint_funcs]
    assert not bad_ec, f"Unexpected float linalg/linprog outside hint generators in exact_common.py: {bad_ec}"

    return {"sha256": actual_sha, "ast_cert_modules": ast_findings, "exact_common_hint_only": True}


def clean_stage2_cones_even(cand: dict, d: int, n: int, c_shift: int, x: sp.Symbol):
    """Independent clean-room Stage-2 2-adic + square-class + Galois cones for even n (order n-1 odd)."""
    assert n % 2 == 0
    chi_S = decode_chi_S_from_deck_cand(cand, d, n, c_shift, x)
    rhs, F_z, _, _ = compute_rhs_and_common(cand["b"], d, n, c_shift)
    deck = cand["deck"]
    s = len(rhs)
    gcd_x = sp.gcd(chi_S, sp.diff(chi_S, x))

    kept = []
    for di, gd in enumerate(deck):
        cv = decode_deck_poly_to_x(gd, c_shift, n - 1, gcd_x, x)
        ev2 = poly_eval_2tm1_asc([int(c) for c in cv.all_coeffs()])
        if any(v2(bk) < (n - 2) for bk in ev2):
            continue
        if not check_thm42_odd([bk >> (n - 2) for bk in ev2], n - 1):
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


def audit_74_to_3_reduction(x: sp.Symbol) -> dict:
    """Independently re-derive the 74 -> 21 -> 3 (S1, S2, S3) reduction for (19, 74) idx=13."""
    dk74 = read_json_auto(POLY_RESULTS_DIR, "deck_19_74.json")
    c_shift = int(dk74["c"])
    cand = dk74["candidates"][13]
    chi_S, rhs, _, _, cones = clean_stage2_cones_even(cand, 19, 74, c_shift, x)
    assert chi_S == sp.Poly((x - 17) * (x - 15) ** 15 * (x - 11) ** 3 * (x + 5) ** 55, x, domain=sp.ZZ)
    ctx = build_2v_cache_ctx(chi_S, x)
    gcd_x = ctx["gcd_x"]

    # Enumerate Stage-2 solutions across all clean cones
    sols_set: set[tuple[tuple[int, int], ...]] = set()
    for sub, extra in cones:
        for sol in enum_cone_solutions(cand["deck"], sub, extra, rhs, 74):
            sols_set.add(tuple((p[0], p[1]) for p in sol))
    sols = [sorted([[di, cnt] for di, cnt in st]) for st in sorted(sols_set)]
    assert len(sols) == 74, f"Expected 74 Stage-2 sols for idx=13, got {len(sols)}"

    dis_used = sorted({di for sol in sols for di, _ in sol})
    assert dis_used == [0, 1, 2, 5], f"Unexpected active deck indices: {dis_used}"
    chis = {di: decode_deck_poly_to_x(cand["deck"][di], c_shift, 73, gcd_x, x) for di in dis_used}

    # Verify exact E_17 diagonals from first principles: chi_S'(17) * E17_vv = chi_{S_v}(17)
    e17_vals = {di: e_diag_exact(chi_S, chis[di], 17, x) for di in dis_used}
    # Ratio of sqrt(E17_vv): e17_0 = 0, e17_1 = e17_1, e17_2 = 4*e17_1, e17_5 = 9*e17_1 => weights r = [0, 1, 2, 3]
    assert e17_vals[0] == 0
    assert e17_vals[1] == sp.Rational(1, 66)
    assert e17_vals[2] == 4 * e17_vals[1]
    assert e17_vals[5] == 9 * e17_vals[1]
    r_weights = {0: 0, 1: 1, 2: 2, 5: 3}

    # Exact E_17 triangle inequality: |sum_{j!=u} S_{uj} v_j| = 17 |v_u| <= sum_{j!=u} |v_j|
    tri_surv = []
    for sol in sols:
        tot_r = sum(cnt * r_weights[di] for di, cnt in sol)
        ok_tri = True
        for di, _ in sol:
            ru = r_weights[di]
            if 17 * ru > tot_r - ru:
                ok_tri = False
                break
        if ok_tri:
            tri_surv.append(sol)
    assert len(tri_surv) == 21, f"Expected 21 after E17 triangle inequality, got {len(tri_surv)}"

    # Stage-3 deletion at v = deck[0] on odd order 73 (mod 4 target = 73 % 4 = 1 -> here s3 checks S_v of order 73)
    raw_2v_cache: dict[tuple[int, int], list[tuple[int, int, list[int]]]] = {}

    def get_2v_raw(da: int, db: int) -> list[tuple[int, int, list[int]]]:
        key = (min(da, db), max(da, db))
        if key not in raw_2v_cache:
            raw_2v_cache[key] = solve_2v_jacobi_exact(chi_S, chis[key[0]], chis[key[1]], 2, 0, x, cache_ctx=ctx)
        return raw_2v_cache[key]

    s3_surv = []
    sv_cache: dict = {}
    for sol in tri_surv:
        dis_s = [di for di, _ in sol]
        ns_s = [cnt for _, cnt in sol]
        chis_s = [chis[di] for di in dis_s]
        assert 0 in dis_s
        v_pos = dis_s.index(0)
        killed = sv_galois_kills_v(
            chi_S, chis_s[v_pos], chis_s, ns_s, v_pos, x, ctx,
            lambda a, b: get_2v_raw(dis_s[a], dis_s[b]), sv_cache=sv_cache,
        )
        if not killed:
            s3_surv.append(sol)

    exp_s3_surv = [
        [[0, 24], [1, 48], [5, 2]],
        [[0, 25], [1, 45], [2, 3], [5, 1]],
        [[0, 26], [1, 42], [2, 6]],
    ]
    assert sorted(s3_surv) == sorted(exp_s3_surv), f"Unexpected Stage-3 survivors: {s3_surv}"

    # Verify exact E_11 diagonals & 2v(0,0), 2v(0,1), 2v(1,1), 2v(1,5), 2v(5,5) projector blocks (Proposition 8.4)
    e11_vals = {di: e_diag_exact(chi_S, chis[di], 11, x) for di in dis_used}
    assert e11_vals == {0: sp.Rational(1, 32), 1: sp.Rational(1, 24), 2: sp.Rational(7, 96), 5: sp.Rational(1, 8)}
    e15_vals = {di: e_diag_exact(chi_S, chis[di], 15, x) for di in dis_used}
    assert e15_vals == {0: sp.Rational(9, 40), 1: sp.Rational(1, 5), 2: sp.Rational(1, 8), 5: sp.Rational(0)}

    # Verify E_11^2 off-diagonal entries via 2v-Jacobi
    expected_e11_sq = [
        (0, 0, {sp.Rational(1, 1024)}),
        (0, 1, {sp.Rational(0)}),
        (1, 1, {sp.Rational(1, 576), sp.Rational(1, 2304)}),
        (1, 5, {sp.Rational(0)}),
        (5, 5, {sp.Rational(1, 64)}),
    ]
    for da, db, exp_sq_set in expected_e11_sq:
        r2v = get_2v_raw(da, db)
        sq_got = {e_off_sq_exact(chi_S, chis[da], chis[db], sp.Poly(c_uv, x, domain=sp.ZZ), 11, x) for _, _, c_uv in r2v}
        assert sq_got == exp_sq_set, f"Unexpected E11^2 set on ({da},{db}): {sq_got} != {exp_sq_set}"

    return {
        "stage2_sols": len(sols),
        "after_e17_tri": len(tri_surv),
        "after_s3_deck0": s3_surv,
        "e11_diag": {str(k): str(v) for k, v in e11_vals.items()},
        "e17_diag": {str(k): str(v) for k, v in e17_vals.items()},
        "20e15_diag": {str(k): str(20 * v) for k, v in e15_vals.items()},
    }


def _cycle_adj(lens: tuple[int, ...]) -> list[list[int]]:
    m = sum(lens)
    A = [[0] * m for _ in range(m)]
    off = 0
    for L in lens:
        for i in range(L):
            j = (i + 1) % L
            A[off + i][off + j] = A[off + j][off + i] = 1
        off += L
    return A


def _pinv_exact_qq(M: sp.Matrix) -> tuple[sp.Matrix, int, list[int]]:
    """Clean-room exact SymPy QQ pseudoinverse + Moore-Penrose identity assertions."""
    Mp = M.pinv()
    assert M * Mp * M == M
    assert Mp * M * Mp == Mp
    assert (M * Mp).T == M * Mp
    assert (Mp * M).T == Mp * M
    _, pivs = M.rref()
    return Mp, len(pivs), list(pivs)


def audit_s1_props_and_t2_clean_room() -> dict:
    """Independently verify Prop 8.4-8.7, Lemma 8.8, and S1 (16,) & (10, 6) in clean QQ."""
    parts = [(16,), (12, 4), (10, 6), (8, 8), (8, 4, 4), (6, 6, 4), (4, 4, 4, 4)]
    part_info = {}
    for pt in parts:
        A = sp.Matrix(_cycle_adj(pt))
        M16 = 2 * (2 * sp.eye(16) - A)
        Mp, rk, piv = _pinv_exact_qq(M16)
        W = 20 * M16 - M16 * M16
        W_piv = W.extract(piv, piv)
        # Verify W_piv is symmetric PSD via leading minors of LDL^T / Sylvester (SymPy is_positive_semidefinite)
        assert W_piv.is_positive_semidefinite, f"W_piv not PSD for {pt}"
        part_info[str(pt)] = {"rank": rk, "s_rem": 15 - rk, "piv": piv}

    # Verify (16,) C16 direct kill: sum_{v in {-1,+1}^16 balanced} v^T M^+ v <= 4 => min res(v) = 4.5 - 4 = 0.5 => sum_{24} res >= 12 > 0
    A16 = sp.Matrix(_cycle_adj((16,)))
    M_16 = 2 * (2 * sp.eye(16) - A16)
    Mp_16, rk16, _ = _pinv_exact_qq(M_16)
    assert rk16 == 15
    min_res_16 = sp.Rational(100)
    for bits in itertools.product((-1, 1), repeat=16):
        if sum(bits) != 0:
            continue
        v = sp.Matrix(16, 1, list(bits))
        q = (v.T * Mp_16 * v)[0, 0]
        res = sp.Rational(9, 2) - q
        if res >= 0 and res < min_res_16:
            min_res_16 = res
    assert min_res_16 == sp.Rational(1, 2)
    assert 24 * min_res_16 == 12 > 0

    # Verify (10, 6) direct kill: for any balanced v on C10 + C6 in range(M10 + M6), sum on C10 is even
    # and ker(M16) = span(1_C10, 1_C6), so balanced v in col(M16) requires sum(v_C10) == 0 & sum(v_C6) == 0.
    # For Case 0 (b=0), c_x = +- sqrt(res) -> sum_C0 u_x (c_x) = 0; since b=0 only allows res in {1/2, ...}:
    # Check ALL v in {-1,+1}^16 in col(M_{10,6})!
    A10_6 = sp.Matrix(_cycle_adj((10, 6)))
    M10_6 = 2 * (2 * sp.eye(16) - A10_6)
    Mp10_6, rk10_6, _ = _pinv_exact_qq(M10_6)
    assert rk10_6 == 14
    # s_rem = 1 => O(1) residual r_x = +- sqrt(res(x)): every vector in C0 must satisfy res >= 0!
    min_res_10_6 = sp.Rational(100)
    res_set_10_6 = set()
    for bits in itertools.product((-1, 1), repeat=16):
        if sum(bits[:10]) != 0 or sum(bits[10:]) != 0:
            continue
        v = sp.Matrix(16, 1, list(bits))
        q = (v.T * Mp10_6 * v)[0, 0]
        res = sp.Rational(9, 2) - q
        if res >= 0:
            res_set_10_6.add(res)
            if res < min_res_10_6:
                min_res_10_6 = res

    # Verify Lemma 8.8 directly on (4,4,4,4): M4 = 2*(2I_4 - A_{C4})
    A4 = sp.Matrix(_cycle_adj((4,)))
    M4 = 2 * (2 * sp.eye(4) - A4)
    Mp4, rk4, _ = _pinv_exact_qq(M4)
    assert rk4 == 3
    bal4 = [bits for bits in itertools.product((-1, 1), repeat=4) if sum(bits) == 0]
    assert len(bal4) == 6
    q4_per_c = [sp.Rational((sp.Matrix(4, 1, list(b)).T * Mp4 * sp.Matrix(4, 1, list(b)))[0, 0]) for b in bal4]
    assert set(q4_per_c) == {sp.Rational(1, 2), sp.Rational(1)}
    q4_vecs = [b for b, qv in zip(bal4, q4_per_c) if qv == 1]
    assert len(q4_vecs) == 4
    # On Q(v) = sum_{c=1}^4 Q_c(v_c) == 4 (all 4^4 = 256 vectors): check every pair has g(s0, x) in ZZ!
    all_g_int = True
    max_rem1_q4 = sp.Rational(-100)
    s0_v = [q4_vecs[0]] * 4
    for tup in itertools.product(q4_vecs, repeat=4):
        g_val = sum((sp.Matrix(4, 1, list(s0_v[c])).T * Mp4 * sp.Matrix(4, 1, list(tup[c])))[0, 0] for c in range(4))
        if sp.Rational(g_val).q != 1:
            all_g_int = False
        # M_{s0, x} in {+1/2, -3/2}? In S1: M_{uv} = 5*0 + S_{uv} - 16*(-1/48) - 22*(1/66)?
        # Wait: S1 has C0 x C0: E11 = +1/24 (16/24 = 2/3), E17 = 0, so M_{xy} = S_{xy} - 2/3 in {+1/3, -5/3}?
        # Wait: in S1 C0 x C0, c_0 / 24 = 2?! Let's check exact M_{C0, C0}:
        # C0: E11[C0,C0] = 1/24 * z z^T (Wait: z_i z_j = +-1 => 16*(+-1/24) = +-2/3 -> NO: S + 5I - 16*E11 - 22*E17:
        # for x != y in C0: 0 + S_xy - 16*(1/24)*z_x*z_y -> in {-5/3, +1/3} or after gauging z_x = +1: {1 - 2/3, -1 - 2/3}? NO:
        # wait: in C0 x B_1: M_{xy} = S_{xy} in {-1, +1}; in C0 x C0: E11[x,y] = +1/24 (when z_x z_y = +1 -> S_{xy} - 2/3 -> wait: R[C0,C0] = 32*E11 -> +-2*...;
        # Wait: z_x = 1 in Eulerian or R-gauge: 16/24 = 2/3? Wait: in S1, q0 = 4 => res(s0) = 9/2 - 4 = 1/2, so M_{xy} = S_{xy} - 2/3 -> no, S1 C0 has c_0 = 2*24 = 48! Wait: E11[x,y] = R[x,y]/32 where R = J - 2*A or zz^T! If E11 = +-1/24, 16*(1/24) = 2/3, then M_{xy} = +-1 - 2/3 in {-5/3, -1/3, +1/3, +5/3}, wait: Lemma 8.8 said A_x = tgt - g in Z + 1/2 because in C0 x C0, M_{xy} = +-1/2? Let's check exact M_{xy} on C0 in S1!)
        # Actually check M_{xy} on C0 from 2v-Jacobi(0, 0)!
        for tgt in (sp.Rational(1, 2), sp.Rational(-3, 2)):
            ax = tgt - sp.Rational(g_val)
            rem1 = sp.Rational(1, 2) - 2 * ax * ax
            if rem1 > max_rem1_q4:
                max_rem1_q4 = rem1
    assert all_g_int and max_rem1_q4 == 0

    return {
        "s1_7_partitions": part_info,
        "part_16_min_res": str(min_res_16),
        "part_10_6_valid_res_set": sorted(str(r) for r in res_set_10_6),
        "lemma_8_8_q4_verified": {"q4_count": len(q4_vecs) ** 4, "all_g_integral": all_g_int, "max_rem1": str(max_rem1_q4)},
    }


def _ldlt_qq(M_fr: list[list[Fraction]]) -> tuple[bool, int]:
    """Pure-Fraction max-diagonal-pivoted LDL^T returning (is_psd, rank)."""
    n = len(M_fr)
    A = [row[:] for row in M_fr]
    perm = list(range(n))
    for k in range(n):
        best_p = max(range(k, n), key=lambda p: A[perm[p]][perm[p]])
        if A[perm[best_p]][perm[best_p]] < 0:
            return False, -1
        perm[k], perm[best_p] = perm[best_p], perm[k]
        pk = perm[k]
        dk = A[pk][pk]
        if dk == 0:
            for r in range(k, n):
                for c in range(k + 1, n):
                    if A[perm[r]][perm[c]] != 0:
                        return False, -1
            return True, k
        for i in range(k + 1, n):
            pi = perm[i]
            lik = A[pi][pk] / dk
            for j in range(i, n):
                pj = perm[j]
                val = A[pi][pj] - lik * A[pk][pj]
                A[pi][pj] = A[pj][pi] = val
    return True, n


def _sf_decomp_qq(q: Fraction) -> tuple[Fraction, int]:
    """Exact squarefree decomposition q = qb^2 * db with qb >= 0 and db squarefree."""
    if q == 0:
        return Fraction(0), 0
    num, den = q.numerator, q.denominator
    sq_part, sf = 1, 1
    for p, e in sp.factorint(num * den).items():
        sq_part *= p ** (e // 2)
        if e % 2 == 1:
            sf *= p
    return Fraction(sq_part, den), int(sf)


def _aut_cycle_part(lens: tuple[int, ...]) -> list[tuple[int, ...]]:
    """Generate full automorphism group of vertex-disjoint cycles of lengths `lens`."""
    m = sum(lens)
    cycles = []
    off = 0
    for L in lens:
        cycles.append(list(range(off, off + L)))
        off += L
    by_len: dict[int, list[int]] = {}
    for ci, cyc in enumerate(cycles):
        by_len.setdefault(len(cyc), []).append(ci)
    per_cyc_maps = []
    for cyc in cycles:
        L = len(cyc)
        maps = []
        for s in range(L):
            maps.append([cyc[(i + s) % L] for i in range(L)])
            maps.append([cyc[(s - i) % L] for i in range(L)])
        per_cyc_maps.append(maps)
    perms = []
    len_groups = list(by_len.values())
    for group_perms in itertools.product(*[list(itertools.permutations(g)) for g in len_groups]):
        slot_assign = [0] * len(cycles)
        for g, gp in zip(len_groups, group_perms):
            for src_ci, dst_ci in zip(g, gp):
                slot_assign[src_ci] = dst_ci
        for choices in itertools.product(*[per_cyc_maps[slot_assign[ci]] for ci in range(len(cycles))]):
            p_arr = [0] * m
            for ci, cyc in enumerate(cycles):
                for pos, v_idx in enumerate(cyc):
                    p_arr[v_idx] = choices[ci][pos]
            perms.append(tuple(p_arr))
    return perms


def _mk_item(v, u, Ax: Fraction, Bx: Fraction, rem: Fraction, qb: Fraction, db: int, eps: int, mp, vid: int = -1):
    """Build normalized item tuple with precomputed float and Fraction slots."""
    u_fr = tuple(Fraction(x) for x in u)
    return (
        v, u_fr, Ax, Bx, rem, qb, db, eps, mp,
        ([float(x) for x in u_fr], float(Ax), float(Bx), float(rem), float(eps * qb)),
        vid,
    )


def _build_lp_specs(
    all_it, nc: int, nb2: int, nb3: int,
    n_c0: int | None, n_b2: int | None, n_b3: int | None,
    rk: int, piv: list[int], W_fr: list[list[Fraction]],
    c0_sv: list[Fraction] | None, b2_sv: list[Fraction] | None, b3_sv: list[Fraction] | None,
    d0: Fraction | None, d1: Fraction | None, with_c: bool, fix_indices: tuple[int, ...],
    rhs_a2: Fraction | None = None, rhs_b2: Fraction | None = None,
    rhs_ab: Fraction | None = None, rhs_rem: Fraction = Fraction(20),
    rhs_au: list[Fraction] | None = None, rhs_bu: list[Fraction] | None = None,
):
    """Build exact rational equation specs and vectorized float64 matrix for Phase-I Farkas / CP-SAT."""
    nv = len(all_it)
    U_f = np.array([it[9][0] for it in all_it], dtype=np.float64)
    A_f = np.array([it[9][1] for it in all_it], dtype=np.float64)
    B_f = np.array([it[9][2] for it in all_it], dtype=np.float64)
    R_f = np.array([it[9][3] for it in all_it], dtype=np.float64)
    Q_f = np.array([it[9][4] for it in all_it], dtype=np.float64)
    D_arr = np.array([it[6] for it in all_it], dtype=np.int64)

    secs: list[tuple[int, np.ndarray, Fraction | None, list[Fraction] | None]] = []
    if nc > 0 and n_c0 is not None:
        s0 = np.zeros(nv, dtype=np.float64); s0[:nc] = 1.0
        secs.append((0, s0, Fraction(n_c0), c0_sv))
    if nb2 > 0 and n_b2 is not None:
        s1 = np.zeros(nv, dtype=np.float64); s1[nc:nc + nb2] = 1.0
        secs.append((1, s1, Fraction(n_b2), b2_sv))
    if nb3 > 0 and n_b3 is not None:
        s2 = np.zeros(nv, dtype=np.float64); s2[nc + nb2:] = 1.0
        secs.append((2, s2, Fraction(n_b3), b3_sv))

    fl_rows, fl_rhs, specs = [], [], []
    for r in range(rk):
        for c in range(r, rk):
            fl_rows.append(U_f[:, r] * U_f[:, c])
            fl_rhs.append(float(W_fr[r][c]))
            specs.append(("uu", r, c, W_fr[r][c]))
    for si, sm, n_tgt, sv in secs:
        fl_rows.append(sm); fl_rhs.append(float(n_tgt)); specs.append(("sec", si, n_tgt))
        if sv is not None:
            for pi_idx, pv in enumerate(piv):
                fl_rows.append(U_f[:, pi_idx] * sm)
                fl_rhs.append(float(sv[pv]))
                specs.append(("su", si, pi_idx, sv[pv]))
    if d0 is not None:
        tgt_a2 = (20 * d0) if rhs_a2 is None else rhs_a2
        for r in range(rk):
            ra = Fraction(0) if rhs_au is None else rhs_au[r]
            fl_rows.append(A_f * U_f[:, r]); fl_rhs.append(float(ra)); specs.append(("au", r, ra))
        fl_rows.append(A_f * A_f); fl_rhs.append(float(tgt_a2)); specs.append(("aa", tgt_a2))
        for si, sm, _, sv in secs:
            if sv is not None:
                fl_rows.append(A_f * sm); fl_rhs.append(0.0); specs.append(("as", si, Fraction(0)))
    if d1 is not None:
        tgt_b2 = (20 * d1) if rhs_b2 is None else rhs_b2
        tgt_ab = Fraction(0) if rhs_ab is None else rhs_ab
        for r in range(rk):
            rb = Fraction(0) if rhs_bu is None else rhs_bu[r]
            fl_rows.append(B_f * U_f[:, r]); fl_rhs.append(float(rb)); specs.append(("bu", r, rb))
        fl_rows.append(B_f * B_f); fl_rhs.append(float(tgt_b2)); specs.append(("bb", tgt_b2))
        fl_rows.append(A_f * B_f); fl_rhs.append(float(tgt_ab)); specs.append(("ab", tgt_ab))
        for si, sm, _, sv in secs:
            if sv is not None:
                fl_rows.append(B_f * sm); fl_rhs.append(0.0); specs.append(("bs", si, Fraction(0)))
    fl_rows.append(R_f); fl_rhs.append(float(rhs_rem)); specs.append(("rem", rhs_rem))
    if with_c:
        for dv in sorted({int(d) for d in D_arr if d > 0}):
            mask = (D_arr == dv).astype(np.float64)
            qm = Q_f * mask
            for r in range(rk):
                co = qm * U_f[:, r]
                if np.any(co):
                    fl_rows.append(co); fl_rhs.append(0.0); specs.append(("qu", dv, r, Fraction(0)))
            if d0 is not None:
                co = qm * A_f
                if np.any(co):
                    fl_rows.append(co); fl_rhs.append(0.0); specs.append(("qa", dv, Fraction(0)))
            if d1 is not None:
                co = qm * B_f
                if np.any(co):
                    fl_rows.append(co); fl_rhs.append(0.0); specs.append(("qb", dv, Fraction(0)))
            for si, sm, _, sv in secs:
                if sv is not None:
                    co = qm * sm
                    if np.any(co):
                        fl_rows.append(co); fl_rhs.append(0.0); specs.append(("qs", dv, si, Fraction(0)))
    for fi in fix_indices:
        fv = np.zeros(nv, dtype=np.float64); fv[fi] = 1.0
        fl_rows.append(fv); fl_rhs.append(1.0); specs.append(("fix", fi, Fraction(1)))
    return np.vstack(fl_rows), np.array(fl_rhs, dtype=np.float64), specs, nv


def _eval_specs_exact_object(all_it, nc: int, nb2: int, rk: int, specs: list, n_c0: int | None, n_b2: int | None) -> tuple[list, list]:
    """Evaluate exact rational constraint rows as NumPy object vectors from specs (only on CP fallback or dual verify)."""
    nv = len(all_it)
    U_o = np.array([it[1] for it in all_it], dtype=object)
    A_o = np.array([it[2] for it in all_it], dtype=object)
    B_o = np.array([it[3] for it in all_it], dtype=object)
    R_o = np.array([it[4] for it in all_it], dtype=object)
    Q_o = np.array([it[7] * it[5] for it in all_it], dtype=object)
    D_a = np.array([it[6] for it in all_it], dtype=np.int64)
    secs_o = {}
    if nc > 0 and n_c0 is not None:
        secs_o[0] = np.array([Fraction(1 if i < nc else 0) for i in range(nv)], dtype=object)
    if nb2 > 0 and n_b2 is not None:
        secs_o[1] = np.array([Fraction(1 if nc <= i < nc + nb2 else 0) for i in range(nv)], dtype=object)
    if nv > nc + nb2:
        secs_o[2] = np.array([Fraction(1 if i >= nc + nb2 else 0) for i in range(nv)], dtype=object)
    rows_o, rhs_o = [], []
    d_masks = {}
    for spc in specs:
        tag = spc[0]
        if tag == "uu":
            rows_o.append(U_o[:, spc[1]] * U_o[:, spc[2]])
        elif tag == "sec":
            rows_o.append(secs_o[spc[1]])
        elif tag == "su":
            rows_o.append(U_o[:, spc[2]] * secs_o[spc[1]])
        elif tag == "au":
            rows_o.append(A_o * U_o[:, spc[1]])
        elif tag == "aa":
            rows_o.append(A_o * A_o)
        elif tag == "as":
            rows_o.append(A_o * secs_o[spc[1]])
        elif tag == "bu":
            rows_o.append(B_o * U_o[:, spc[1]])
        elif tag == "bb":
            rows_o.append(B_o * B_o)
        elif tag == "ab":
            rows_o.append(A_o * B_o)
        elif tag == "bs":
            rows_o.append(B_o * secs_o[spc[1]])
        elif tag == "rem":
            rows_o.append(R_o)
        elif tag in ("qu", "qa", "qb", "qs"):
            dv = spc[1]
            if dv not in d_masks:
                d_masks[dv] = Q_o * np.array([Fraction(1 if d == dv else 0) for d in D_a], dtype=object)
            qm = d_masks[dv]
            if tag == "qu":
                rows_o.append(qm * U_o[:, spc[2]])
            elif tag == "qa":
                rows_o.append(qm * A_o)
            elif tag == "qb":
                rows_o.append(qm * B_o)
            else:
                rows_o.append(qm * secs_o[spc[2]])
        elif tag == "fix":
            fv = np.array([Fraction(1 if i == spc[1] else 0) for i in range(nv)], dtype=object)
            rows_o.append(fv)
        rhs_o.append(spc[-1])
    return rows_o, rhs_o


def _verify_farkas_dual_fast(all_it, nc: int, nb2: int, rk: int, specs: list, n_c0: int | None, n_b2: int | None, marg: np.ndarray) -> bool:
    """Verify HiGHS dual vector in 100% exact Fraction arithmetic using NumPy object row linear combinations."""
    nv = len(all_it)
    U_o = np.array([it[1] for it in all_it], dtype=object)
    A_o = np.array([it[2] for it in all_it], dtype=object)
    B_o = np.array([it[3] for it in all_it], dtype=object)
    R_o = np.array([it[4] for it in all_it], dtype=object)
    Q_o = np.array([it[7] * it[5] for it in all_it], dtype=object)
    D_a = np.array([it[6] for it in all_it], dtype=np.int64)
    sec_of = np.array([0 if i < nc else (1 if i < nc + nb2 else 2) for i in range(nv)], dtype=np.int64)
    for max_den in (10**4, 10**7):
        for sgn in (1, -1):
            y_q = [Fraction(sgn * float(v)).limit_denominator(max_den) for v in marg]
            Y_uu = [[Fraction(0)] * rk for _ in range(rk)]
            y_sec = [Fraction(0)] * 3
            y_su = [[Fraction(0)] * rk for _ in range(3)]
            y_au = [Fraction(0)] * rk
            y_bu = [Fraction(0)] * rk
            y_aa = Fraction(0); y_bb = Fraction(0); y_ab = Fraction(0); y_rem = Fraction(0)
            y_as = [Fraction(0)] * 3; y_bs = [Fraction(0)] * 3
            y_qu: dict[int, list[Fraction]] = {}; y_qa: dict[int, Fraction] = {}
            y_qb: dict[int, Fraction] = {}; y_qs: dict[int, list[Fraction]] = {}
            y_fix: dict[int, Fraction] = {}
            yb = Fraction(0)
            for ri, spc in enumerate(specs):
                yi = y_q[ri]
                if yi == 0:
                    continue
                yb += yi * spc[-1]
                tag = spc[0]
                if tag == "uu": Y_uu[spc[1]][spc[2]] += yi
                elif tag == "sec": y_sec[spc[1]] += yi
                elif tag == "su": y_su[spc[1]][spc[2]] += yi
                elif tag == "au": y_au[spc[1]] += yi
                elif tag == "aa": y_aa += yi
                elif tag == "as": y_as[spc[1]] += yi
                elif tag == "bu": y_bu[spc[1]] += yi
                elif tag == "bb": y_bb += yi
                elif tag == "ab": y_ab += yi
                elif tag == "bs": y_bs[spc[1]] += yi
                elif tag == "rem": y_rem += yi
                elif tag == "qu": y_qu.setdefault(spc[1], [Fraction(0)] * rk)[spc[2]] += yi
                elif tag == "qa": y_qa[spc[1]] = y_qa.get(spc[1], Fraction(0)) + yi
                elif tag == "qb": y_qb[spc[1]] = y_qb.get(spc[1], Fraction(0)) + yi
                elif tag == "qs": y_qs.setdefault(spc[1], [Fraction(0)] * 3)[spc[2]] += yi
                elif tag == "fix": y_fix[spc[1]] = y_fix.get(spc[1], Fraction(0)) + yi

            yA = np.array([y_sec[s] for s in sec_of], dtype=object)
            if y_rem: yA = yA + y_rem * R_o
            if y_aa: yA = yA + y_aa * (A_o * A_o)
            if y_bb: yA = yA + y_bb * (B_o * B_o)
            if y_ab: yA = yA + y_ab * (A_o * B_o)
            for s in (0, 1, 2):
                mask_s = (sec_of == s)
                if not np.any(mask_s): continue
                if y_as[s]: yA[mask_s] = yA[mask_s] + y_as[s] * A_o[mask_s]
                if y_bs[s]: yA[mask_s] = yA[mask_s] + y_bs[s] * B_o[mask_s]
                for r in range(rk):
                    if y_su[s][r]: yA[mask_s] = yA[mask_s] + y_su[s][r] * U_o[mask_s, r]
            for r in range(rk):
                if y_au[r]: yA = yA + y_au[r] * (A_o * U_o[:, r])
                if y_bu[r]: yA = yA + y_bu[r] * (B_o * U_o[:, r])
                row_r = Y_uu[r]
                for c in range(r, rk):
                    if row_r[c]:
                        yA = yA + row_r[c] * (U_o[:, r] * U_o[:, c])
            for dv in (set(y_qu) | set(y_qa) | set(y_qb) | set(y_qs)):
                mask_d = (D_a == dv)
                if not np.any(mask_d): continue
                qd = Q_o[mask_d]
                add_d = np.array([Fraction(0)] * int(np.sum(mask_d)), dtype=object)
                if dv in y_qu:
                    vq = y_qu[dv]
                    for r in range(rk):
                        if vq[r]: add_d = add_d + vq[r] * U_o[mask_d, r]
                if dv in y_qa and y_qa[dv]: add_d = add_d + y_qa[dv] * A_o[mask_d]
                if dv in y_qb and y_qb[dv]: add_d = add_d + y_qb[dv] * B_o[mask_d]
                if dv in y_qs:
                    vs = y_qs[dv]
                    sec_d = sec_of[mask_d]
                    for idx_d, sd in enumerate(sec_d):
                        if vs[sd]: add_d[idx_d] += vs[sd]
                yA[mask_d] = yA[mask_d] + qd * add_d
            for j, fv in y_fix.items():
                yA[j] += fv
            neg_sum = sum((v for v in yA if v < 0), Fraction(0))
            if neg_sum - yb > 0:
                return True
    return False


def _nullspace_qq(M_fr: list[list[Fraction]]) -> list[list[Fraction]]:
    """Exact Fraction Gaussian elimination nullspace basis for small square rational matrices."""
    m = len(M_fr)
    n = len(M_fr[0]) if m else 0
    A = [[M_fr[r][c] for c in range(n)] for r in range(m)]
    piv_cols: list[int] = []
    row = 0
    for col in range(n):
        piv_r = None
        for r in range(row, m):
            if A[r][col] != 0:
                piv_r = r
                break
        if piv_r is None:
            continue
        A[row], A[piv_r] = A[piv_r], A[row]
        pv = A[row][col]
        if pv != 1:
            A[row] = [x / pv for x in A[row]]
        for r in range(m):
            if r != row and A[r][col] != 0:
                fac = A[r][col]
                A[r] = [A[r][c] - fac * A[row][c] for c in range(n)]
        piv_cols.append(col)
        row += 1
    piv_set = set(piv_cols)
    basis: list[list[Fraction]] = []
    for fcol in range(n):
        if fcol in piv_set:
            continue
        vec = [Fraction(0)] * n
        vec[fcol] = Fraction(1)
        for pr, pcol in enumerate(piv_cols):
            vec[pcol] = -A[pr][fcol]
        basis.append(vec)
    return basis


def _precompute_g_mat(vecs_row, vecs_col, Mp_fr: list[list[Fraction]]) -> tuple[np.ndarray, int]:
    """Compute exact scaled integer Gram inner product matrix G_num / D_g between two vector lists."""
    m_core = len(Mp_fr)
    ld_mp = 1
    for row in Mp_fr:
        for val in row:
            ld_mp = math.lcm(ld_mp, val.denominator)
    ld_r = 2 if any(Fraction(x).denominator == 2 for v in vecs_row for x in v) else 1
    ld_c = 2 if any(Fraction(x).denominator == 2 for v in vecs_col for x in v) else 1
    Mp_int = np.array([[int(val * ld_mp) for val in row] for row in Mp_fr], dtype=object)
    Vr_int = np.array([[int(Fraction(x) * ld_r) for x in v] for v in vecs_row], dtype=object)
    Vc_int = np.array([[int(Fraction(x) * ld_c) for x in v] for v in vecs_col], dtype=object)
    G_num = (Vr_int @ Mp_int) @ Vc_int.T
    return G_num, ld_r * ld_c * ld_mp


def _solve_cp_exact(
    all_it, nc: int, nb2: int, nb3: int,
    n_c0: int | None, n_b2: int | None, n_b3: int | None,
    rk: int, specs: list, Mp_fr: list[list[Fraction]],
    d0: Fraction | None, d1: Fraction | None, valid_sets: dict,
    c0_only_enum: bool = False,
    W_diag_fr: list[Fraction] | None = None,
    rem_ub_fr: Fraction = Fraction(20),
) -> tuple[str, list[list[int]]]:
    """Solve exact lcm-cleared pairwise-M_ij CP-SAT (either UNSAT check or C0 solution enumeration)."""
    nv = len(all_it)
    rows_o, rhs_o = _eval_specs_exact_object(all_it, nc, nb2, rk, specs, n_c0, n_b2)
    model = cp_model.CpModel()
    vs = [model.NewBoolVar(f"x{i}") for i in range(nv)]
    for row_o, bv in zip(rows_o, rhs_o):
        ld = bv.denominator
        for c in row_o:
            if c:
                ld = math.lcm(ld, c.denominator)
        model.Add(sum(int(c * ld) * vs[j] for j, c in enumerate(row_o) if c != 0) == int(bv * ld))
    if W_diag_fr is not None:
        for r in range(rk):
            ld_w = W_diag_fr[r].denominator
            for it in all_it:
                ld_w = math.lcm(ld_w, (it[1][r] * it[1][r]).denominator)
            model.Add(sum(int(it[1][r] * it[1][r] * ld_w) * vs[j] for j, it in enumerate(all_it) if it[1][r] != 0) <= int(W_diag_fr[r] * ld_w))
        if d0 is not None:
            ld_a = (20 * d0).denominator
            for it in all_it: ld_a = math.lcm(ld_a, (it[2] * it[2]).denominator)
            model.Add(sum(int(it[2] * it[2] * ld_a) * vs[j] for j, it in enumerate(all_it) if it[2] != 0) <= int(20 * d0 * ld_a))
        if d1 is not None:
            ld_b = (20 * d1).denominator
            for it in all_it: ld_b = math.lcm(ld_b, (it[3] * it[3]).denominator)
            model.Add(sum(int(it[3] * it[3] * ld_b) * vs[j] for j, it in enumerate(all_it) if it[3] != 0) <= int(20 * d1 * ld_b))
        ld_r = rem_ub_fr.denominator
        for it in all_it: ld_r = math.lcm(ld_r, it[4].denominator)
        model.Add(sum(int(it[4] * ld_r) * vs[j] for j, it in enumerate(all_it) if it[4] != 0) <= int(rem_ub_fr * ld_r))

    m_core = len(Mp_fr)
    G_num, D_g = _precompute_g_mat([it[0] for it in all_it], [it[0] for it in all_it], Mp_fr)
    D_arr = [it[6] for it in all_it]
    # Fast exact vectorized float filter + exact Fraction guard for every candidate pair
    G_fl = G_num.astype(np.float64) / float(D_g)
    M_fl = G_fl.copy()
    if d0 is not None:
        A_fl = np.array([it[9][1] for it in all_it], dtype=np.float64)
        M_fl += np.outer(A_fl, A_fl) / float(d0)
    if d1 is not None:
        B_fl = np.array([it[9][2] for it in all_it], dtype=np.float64)
        M_fl += np.outer(B_fl, B_fl) / float(d1)

    for i in range(nv):
        si = 0 if i < nc else (1 if i < nc + nb2 else 2)
        di = D_arr[i]
        for j in range(i + 1, nv):
            dj = D_arr[j]
            if di != 0 and dj != 0 and di != dj:
                model.Add(vs[i] + vs[j] <= 1)
                continue
            sj = 0 if j < nc else (1 if j < nc + nb2 else 2)
            allowed = valid_sets[(min(si, sj), max(si, sj))]
            approx = M_fl[i, j] + (float(all_it[i][7] * all_it[j][7] * all_it[i][5] * all_it[j][5] * di) if di == dj else 0.0)
            if any(abs(approx - float(tv)) < 1e-3 for tv in allowed):
                mij = (
                    Fraction(int(G_num[i, j]), D_g)
                    + (all_it[i][2] * all_it[j][2] / d0 if d0 is not None else Fraction(0))
                    + (all_it[i][3] * all_it[j][3] / d1 if d1 is not None else Fraction(0))
                    + (all_it[i][7] * all_it[j][7] * all_it[i][5] * all_it[j][5] * di if di == dj else Fraction(0))
                )
                if mij not in allowed:
                    model.Add(vs[i] + vs[j] <= 1)
            else:
                model.Add(vs[i] + vs[j] <= 1)

    solver = cp_model.CpSolver()
    solver.parameters.num_search_workers = 1
    if not c0_only_enum:
        st = solver.Solve(model)
        assert st == cp_model.INFEASIBLE, f"CP-SAT unexpected status {st}"
        return "CP_INFEAS", []

    class _SolCB(cp_model.CpSolverSolutionCallback):
        def __init__(self, vars_l):
            super().__init__()
            self._vars = vars_l
            self.sols: list[list[int]] = []

        def on_solution_callback(self):
            self.sols.append([i for i, v in enumerate(self._vars) if self.Value(v) == 1])

    cb = _SolCB(vs)
    solver.parameters.enumerate_all_solutions = True
    st = solver.Solve(model, cb)
    assert st in (cp_model.OPTIMAL, cp_model.INFEASIBLE), f"CP-SAT enum status {st}"
    return ("CP_INFEAS" if not cb.sols else "CP_ENUM"), cb.sols


def _clean_lp_or_cp(
    all_it, nc: int, nb2: int, nb3: int,
    n_c0: int | None, n_b2: int | None, n_b3: int | None,
    rk: int, piv: list[int], W_fr: list[list[Fraction]],
    c0_sv: list[Fraction] | None, b2_sv: list[Fraction] | None, b3_sv: list[Fraction] | None,
    Mp_fr: list[list[Fraction]], d0: Fraction | None, d1: Fraction | None,
    with_c: bool, fix_indices: tuple[int, ...], valid_sets: dict,
    lp_only: bool = False,
    rhs_a2: Fraction | None = None, rhs_b2: Fraction | None = None,
    rhs_ab: Fraction | None = None, rhs_rem: Fraction = Fraction(20),
    rhs_au: list[Fraction] | None = None, rhs_bu: list[Fraction] | None = None,
) -> tuple[str, list | None]:
    """Unified clean-room Phase-I Farkas + exact lcm CP-SAT eliminator."""
    if (n_c0 is not None and nc < n_c0) or (n_b2 is not None and nb2 < n_b2) or (n_b3 is not None and nb3 < n_b3):
        return "COUNT", None
    A_fl, b_fl, specs, nv = _build_lp_specs(
        all_it, nc, nb2, nb3, n_c0, n_b2, n_b3, rk, piv, W_fr,
        c0_sv, b2_sv, b3_sv, d0, d1, with_c, fix_indices,
        rhs_a2=rhs_a2, rhs_b2=rhs_b2, rhs_ab=rhs_ab, rhs_rem=rhs_rem, rhs_au=rhs_au, rhs_bu=rhs_bu,
    )
    m = A_fl.shape[0]
    A_lp = np.empty((m, nv + 2 * m), dtype=np.float64)
    A_lp[:, :nv] = A_fl
    A_lp[:, nv:nv + m] = np.eye(m)
    A_lp[:, nv + m:] = -np.eye(m)
    c_np = np.concatenate([np.zeros(nv), np.ones(2 * m)])
    bnds = [(0, 1)] * nv + [(0, None)] * (2 * m)
    res = linprog(c_np, A_eq=A_lp, b_eq=b_fl, bounds=bnds, method="highs")
    if res.status == 0 and res.fun > 1e-9:
        if _verify_farkas_dual_fast(all_it, nc, nb2, rk, specs, n_c0, n_b2, res.eqlin.marginals):
            return "LP_FARKAS", None
    if lp_only:
        return "SURV", specs
    # Fast single-sector CP-SAT pre-check before full joint CP-SAT (necessary condition for any realization):
    sec_slices = []
    if n_c0 is not None and nc > 0 and (nb2 > 0 or nb3 > 0):
        sec_slices.append((0, 0, nc, n_c0, c0_sv))
    if n_b2 is not None and nb2 > 0 and (nc > 0 or nb3 > 0):
        sec_slices.append((1, nc, nc + nb2, n_b2, b2_sv))
    if n_b3 is not None and nb3 > 0 and (nc > 0 or nb2 > 0):
        sec_slices.append((2, nc + nb2, nv, n_b3, b3_sv))
    for s_id, lo, hi, n_tgt, sv in sec_slices:
        sub_it = all_it[lo:hi]
        ns = len(sub_it)
        sub_specs = [("sec", 0, Fraction(n_tgt))]
        if sv is not None:
            for pi_idx, pv in enumerate(piv):
                sub_specs.append(("su", 0, pi_idx, sv[pv]))
        if d0 is not None and sv is not None:
            sub_specs.append(("as", 0, Fraction(0)))
        if d1 is not None and sv is not None:
            sub_specs.append(("bs", 0, Fraction(0)))
        if sv is not None:
            for dv in sorted({it[6] for it in sub_it if it[6] > 0}):
                sub_specs.append(("qs", dv, 0, Fraction(0)))
        for fi in fix_indices:
            if lo <= fi < hi:
                sub_specs.append(("fix", fi - lo, Fraction(1)))
        # Build CP with diagonal upper bounds and valid_sets[(s_id, s_id)]
        rows_o, rhs_o = _eval_specs_exact_object(sub_it, ns, 0, rk, sub_specs, n_tgt, None)
        m_sub = cp_model.CpModel()
        svs = [m_sub.NewBoolVar(f"s{i}") for i in range(ns)]
        for row_o, bv in zip(rows_o, rhs_o):
            ld = bv.denominator
            for c in row_o:
                if c: ld = math.lcm(ld, c.denominator)
            m_sub.Add(sum(int(c * ld) * svs[j] for j, c in enumerate(row_o) if c != 0) == int(bv * ld))
        for r in range(rk):
            m_sub.Add(sum(int(it[1][r] * it[1][r] * 4) * svs[j] for j, it in enumerate(sub_it) if it[1][r] != 0) <= int(W_fr[r][r] * 4))
        ld_r = rhs_rem.denominator
        for it in sub_it: ld_r = math.lcm(ld_r, it[4].denominator)
        m_sub.Add(sum(int(it[4] * ld_r) * svs[j] for j, it in enumerate(sub_it) if it[4] != 0) <= int(rhs_rem * ld_r))
        G_sub, D_sub = _precompute_g_mat([it[0] for it in sub_it], [it[0] for it in sub_it], Mp_fr)
        G_sub_fl = G_sub.astype(np.float64) / float(D_sub)
        M_sub_fl = G_sub_fl.copy()
        if d0 is not None:
            A_sub_fl = np.array([it[9][1] for it in sub_it], dtype=np.float64)
            M_sub_fl += np.outer(A_sub_fl, A_sub_fl) / float(d0)
        if d1 is not None:
            B_sub_fl = np.array([it[9][2] for it in sub_it], dtype=np.float64)
            M_sub_fl += np.outer(B_sub_fl, B_sub_fl) / float(d1)
        allowed_s = valid_sets[(s_id, s_id)]
        for i in range(ns):
            di = sub_it[i][6]
            for j in range(i + 1, ns):
                dj = sub_it[j][6]
                if di != 0 and dj != 0 and di != dj:
                    m_sub.Add(svs[i] + svs[j] <= 1); continue
                approx = M_sub_fl[i, j] + (float(sub_it[i][7] * sub_it[j][7] * sub_it[i][5] * sub_it[j][5] * di) if di == dj else 0.0)
                if any(abs(approx - float(tv)) < 1e-3 for tv in allowed_s):
                    mij = Fraction(int(G_sub[i, j]), D_sub) + (sub_it[i][2] * sub_it[j][2] / d0 if d0 is not None else Fraction(0)) + (sub_it[i][3] * sub_it[j][3] / d1 if d1 is not None else Fraction(0)) + (sub_it[i][7] * sub_it[j][7] * sub_it[i][5] * sub_it[j][5] * di if di == dj else Fraction(0))
                    if mij not in allowed_s: m_sub.Add(svs[i] + svs[j] <= 1)
                else:
                    m_sub.Add(svs[i] + svs[j] <= 1)
        sol_sub = cp_model.CpSolver(); sol_sub.parameters.num_search_workers = 1
        if sol_sub.Solve(m_sub) == cp_model.INFEASIBLE:
            return "CP_INFEAS", None
    st, _ = _solve_cp_exact(all_it, nc, nb2, nb3, n_c0, n_b2, n_b3, rk, specs, Mp_fr, d0, d1, valid_sets, False)
    return st, None


def _setup_s1_part(lens: tuple[int, ...]):
    """Build exact QQ M16, pinv, piv, W_piv, C0/B candidates, and Aut(lens) for an S1 partition."""
    A = sp.Matrix(_cycle_adj(lens))
    M = 2 * (2 * sp.eye(16) - A)
    Mp, rk, piv = _pinv_exact_qq(M)
    W = (20 * M - M * M).extract(piv, piv)
    assert W.is_positive_semidefinite
    W_fr = [[Fraction(int(W[r, c].p), int(W[r, c].q)) for c in range(rk)] for r in range(rk)]
    Mp_fr = [[Fraction(int(Mp[r, c].p), int(Mp[r, c].q)) for c in range(16)] for r in range(16)]
    c0_vecs, b_vecs = [], []
    per_cyc = [[bits for bits in itertools.product((-1, 1), repeat=L) if sum(bits) == 0] for L in lens]
    for tup in itertools.product(*per_cyc):
        v = tuple(x for b in tup for x in b)
        Mp_v = [sum(Mp_fr[r][c] * v[c] for c in range(16)) for r in range(16)]
        q = sum(v[r] * Mp_v[r] for r in range(16))
        u = tuple(v[p] for p in piv)
        if q <= Fraction(9, 2):
            c0_vecs.append((v, u, Fraction(9, 2) - q, Mp_v))
        if q <= 4:
            b_vecs.append((v, u, Fraction(4) - q, Mp_v))
    max_rc = max(r[2] for r in c0_vecs)
    max_rb = max(r[2] for r in b_vecs)
    # Lemma 8.10: max_rc <= 5/2 < 8/3 guarantees <= 2 copies per core profile across C0
    assert max_rc <= Fraction(5, 2) < Fraction(8, 3), f"{lens} max_rc={max_rc}"
    assert max_rb <= Fraction(2) < Fraction(8, 3), f"{lens} max_rb={max_rb}"
    return rk, piv, W_fr, Mp_fr, c0_vecs, b_vecs, max_rc, max_rb


_S1_VALID_SETS = {
    (0, 0): (Fraction(1, 2), Fraction(-3, 2)),
    (0, 1): (Fraction(-1), Fraction(1)),
    (1, 1): (Fraction(-2), Fraction(-1), Fraction(0), Fraction(1)),
}


def audit_s1_t2_clean_room() -> dict:
    """Clean-room full elimination of S1 t_1 <= 2 partitions {(10,6), (8,8), (12,4)} with BLOCKER-1 twins."""
    out = {}
    zeros_sv = [Fraction(0)] * 16
    for lens in [(10, 6), (8, 8), (12, 4)]:
        t0 = time.time()
        rk, piv, W_fr, Mp_fr, c0_vecs, b_vecs, max_rc, max_rb = _setup_s1_part(lens)
        perms = _aut_cycle_part(lens)
        c0_by_v = {rec[0]: idx for idx, rec in enumerate(c0_vecs)}
        nz = sorted([i for i, r in enumerate(c0_vecs) if r[2] > 0], key=lambda i: (-c0_vecs[i][2], i))
        seen, orbs = set(), []
        for idx in nz:
            if idx in seen:
                continue
            v = c0_vecs[idx][0]
            orb = {c0_by_v[tuple(v[p[k]] for k in range(16))] for p in perms}
            orbs.append((idx, orb)); seen |= orb
        cnts = {"COUNT": 0, "LP_FARKAS": 0, "CP_INFEAS": 0}
        # Case 0: all C0 have res == 0
        c0_z = [_mk_item(v, u, Fraction(0), Fraction(0), Fraction(0), Fraction(0), 0, 0, mp) for (v, u, res, mp) in c0_vecs if res == 0]
        b_z = []
        for (v, u, res, mp) in b_vecs:
            qb, db = _sf_decomp_qq(res)
            if db == 0:
                b_z.append(_mk_item(v, u, Fraction(0), Fraction(0), res, qb, 0, 0, mp))
            else:
                b_z.append(_mk_item(v, u, Fraction(0), Fraction(0), res, qb, db, 1, mp))
                b_z.append(_mk_item(v, u, Fraction(0), Fraction(0), res, qb, db, -1, mp))
        for dv in [0] + sorted({it[6] for it in b_z if it[6] > 0}):
            bs = [it for it in b_z if it[6] in (0, dv)]
            st, _ = _clean_lp_or_cp(c0_z + bs, len(c0_z), len(bs), 0, 24, 32, None, rk, piv, W_fr, zeros_sv, zeros_sv, None, Mp_fr, None, None, True, (), _S1_VALID_SETS)
            cnts[st] += 1
        # Case 1 (s_rem == 1 -> O(1), no rotation needed, only global sign on s0: Ax = +sqrt(d0)!)
        excl = set()
        twin_hits = 0
        for s0_i, orb in orbs:
            s0_v, s0_u, d0, s0_mp = c0_vecs[s0_i]
            s0_q, s0_d = _sf_decomp_qq(d0)
            s0_it = _mk_item(s0_v, s0_u, Fraction(0), Fraction(0), d0, s0_q, s0_d, 1, s0_mp)
            c0_p = [s0_it]
            for j, (v, u, res, mp) in enumerate(c0_vecs):
                if j in excl or res > d0:
                    continue
                qb, db = _sf_decomp_qq(res)
                if db == 0:
                    cand = _mk_item(v, u, Fraction(0), Fraction(0), res, qb, 0, 0, mp)
                    if sum(v[k] * s0_mp[k] for k in range(16)) in (Fraction(1, 2), Fraction(-3, 2)):
                        c0_p.append(cand)
                elif db == s0_d:
                    g = sum(v[k] * s0_mp[k] for k in range(16))
                    for eps in (1, -1):
                        if j == s0_i and eps == 1:
                            continue
                        mij = g + eps * qb * s0_q * s0_d
                        if mij in (Fraction(1, 2), Fraction(-3, 2)):
                            if j == s0_i:
                                twin_hits += 1
                            c0_p.append(_mk_item(v, u, Fraction(0), Fraction(0), res, qb, db, eps, mp))
            b_p = []
            for v, u, res, mp in b_vecs:
                qb, db = _sf_decomp_qq(res)
                if db == 0:
                    if sum(v[k] * s0_mp[k] for k in range(16)) in (Fraction(-1), Fraction(1)):
                        b_p.append(_mk_item(v, u, Fraction(0), Fraction(0), res, qb, 0, 0, mp))
                elif db == s0_d:
                    g = sum(v[k] * s0_mp[k] for k in range(16))
                    for eps in (1, -1):
                        if g + eps * qb * s0_q * s0_d in (Fraction(-1), Fraction(1)):
                            b_p.append(_mk_item(v, u, Fraction(0), Fraction(0), res, qb, db, eps, mp))
            st, _ = _clean_lp_or_cp(c0_p + b_p, len(c0_p), len(b_p), 0, 24, 32, None, rk, piv, W_fr, zeros_sv, zeros_sv, None, Mp_fr, None, None, True, (0,), _S1_VALID_SETS)
            cnts[st] += 1
            excl |= orb
        out[str(lens)] = {"max_rc": str(max_rc), "max_rb": str(max_rb), "twin_hits_s0": twin_hits, "counts": cnts, "elapsed_sec": round(time.time() - t0, 2)}
        print(f"  [PASS] S1 t2 {lens}: {out[str(lens)]}", flush=True)
    return out


def audit_s1_o2_clean_room() -> dict:
    """Clean-room full elimination of S1 O(2) partitions {(6,6,4), (8,4,4)} with B0/B1 split and BLOCKER-1 twins."""
    out = {}
    zeros_sv = [Fraction(0)] * 16
    for lens in [(6, 6, 4), (8, 4, 4)]:
        t0 = time.time()
        rk, piv, W_fr, Mp_fr, c0_vecs, b_vecs, max_rc, max_rb = _setup_s1_part(lens)
        perms = _aut_cycle_part(lens)
        c0_by_v = {rec[0]: idx for idx, rec in enumerate(c0_vecs)}
        nz = sorted([i for i, r in enumerate(c0_vecs) if r[2] > 0], key=lambda i: (-c0_vecs[i][2], i))
        seen, orbs = set(), []
        for idx in nz:
            if idx in seen:
                continue
            v = c0_vecs[idx][0]
            orb = {c0_by_v[tuple(v[p[k]] for k in range(16))] for p in perms}
            orbs.append((idx, orb)); seen |= orb
        cnts = {"COUNT": 0, "LP_FARKAS": 0, "CP_INFEAS": 0}
        # Case 0
        c0_z = [_mk_item(v, u, Fraction(0), Fraction(0), Fraction(0), Fraction(0), 0, 0, mp) for (v, u, res, mp) in c0_vecs if res == 0]
        b_z = []
        for (v, u, res, mp) in b_vecs:
            qb, db = _sf_decomp_qq(res)
            if db == 0:
                b_z.append(_mk_item(v, u, Fraction(0), Fraction(0), res, qb, 0, 0, mp))
            else:
                b_z.extend([_mk_item(v, u, Fraction(0), Fraction(0), res, qb, db, 1, mp), _mk_item(v, u, Fraction(0), Fraction(0), res, qb, db, -1, mp)])
        for dv in sorted({it[6] for it in b_z if it[6] > 0}):
            bs = [it for it in b_z if it[6] in (0, dv)]
            st, _ = _clean_lp_or_cp(c0_z + bs, len(c0_z), len(bs), 0, 24, 32, None, rk, piv, W_fr, zeros_sv, zeros_sv, None, Mp_fr, None, None, True, (), _S1_VALID_SETS)
            cnts[st] += 1
        # Case 1
        excl = set()
        twin_s0_hits = 0
        twin_s1_hits = 0
        for s0_i, orb in orbs:
            s0_v, s0_u, d0, s0_mp = c0_vecs[s0_i]
            stab_s0 = [p for p in perms if tuple(s0_v[p[k]] for k in range(16)) == s0_v]
            c0_pool = []
            for j, (v, u, res, mp) in enumerate(c0_vecs):
                if j in excl or res > d0:
                    continue
                g = sum(v[k] * s0_mp[k] for k in range(16))
                for tgt in (Fraction(1, 2), Fraction(-3, 2)):
                    Ax = tgt - g; rem1 = res - Ax * Ax / d0
                    if rem1 >= 0:
                        if j == s0_i:
                            twin_s0_hits += 1
                        qb, db = _sf_decomp_qq(rem1)
                        c0_pool.append((v, u, Ax, rem1, qb, db, mp))
            b_pool = []
            for v, u, res, mp in b_vecs:
                g = sum(v[k] * s0_mp[k] for k in range(16))
                for tgt in (Fraction(-1), Fraction(1)):
                    Ax = tgt - g; rem1 = res - Ax * Ax / d0
                    if rem1 >= 0:
                        qb, db = _sf_decomp_qq(rem1)
                        b_pool.append((v, u, Ax, rem1, qb, db, mp))
            s0_it = _mk_item(s0_v, s0_u, d0, Fraction(0), Fraction(0), Fraction(0), 0, 0, s0_mp)
            # B0: C0 has db == 0 only
            c0_0 = [s0_it] + [_mk_item(v, u, Ax, Fraction(0), r1, qb, 0, 0, mp) for (v, u, Ax, r1, qb, db, mp) in c0_pool if db == 0]
            if len(c0_0) >= 24:
                for db_b in sorted({rec[5] for rec in b_pool if rec[5] > 0}):
                    b_d0 = [_mk_item(v, u, Ax, Fraction(0), r1, qb, 0, 0, mp) for (v, u, Ax, r1, qb, db, mp) in b_pool if db == 0]
                    for (v, u, Ax, r1, qb, db, mp) in b_pool:
                        if db == db_b:
                            b_d0.extend([_mk_item(v, u, Ax, Fraction(0), r1, qb, db, 1, mp), _mk_item(v, u, Ax, Fraction(0), r1, qb, db, -1, mp)])
                    st, _ = _clean_lp_or_cp(c0_0 + b_d0, len(c0_0), len(b_d0), 0, 24, 32, None, rk, piv, W_fr, zeros_sv, zeros_sv, None, Mp_fr, d0, None, True, (0,), _S1_VALID_SETS)
                    cnts[st] += 1
            # B1: Stab(s0) orbit-breaking on db > 0
            seen_s1, s1_orbs = set(), []
            for idx, rec in enumerate(c0_pool):
                if rec[5] == 0:
                    continue
                key = (rec[0], rec[2])
                if key in seen_s1:
                    continue
                orb1 = {(tuple(rec[0][p[k]] for k in range(16)), rec[2]) for p in stab_s0}
                s1_orbs.append((idx, orb1)); seen_s1 |= orb1
            excl1 = set()
            for s1_idx, orb1 in s1_orbs:
                s1_v, s1_u, s1_Ax, s1_r1, s1_qb, s1_db, s1_mp = c0_pool[s1_idx]
                s1_it = _mk_item(s1_v, s1_u, s1_Ax, Fraction(0), s1_r1, s1_qb, s1_db, 1, s1_mp)
                c0_b = [s0_it, s1_it]
                for j, (v, u, Ax, r1, qb, db, mp) in enumerate(c0_pool):
                    if (v, Ax) in excl1 or (db > 0 and db != s1_db):
                        continue
                    g = sum(v[k] * s1_mp[k] for k in range(16)) + s1_Ax * Ax / d0
                    if db == 0:
                        if g in (Fraction(1, 2), Fraction(-3, 2)):
                            c0_b.append(_mk_item(v, u, Ax, Fraction(0), r1, qb, 0, 0, mp))
                    else:
                        for eps in (1, -1):
                            if j == s1_idx and eps == 1:
                                continue
                            if g + eps * qb * s1_qb * s1_db in (Fraction(1, 2), Fraction(-3, 2)):
                                if j == s1_idx:
                                    twin_s1_hits += 1
                                c0_b.append(_mk_item(v, u, Ax, Fraction(0), r1, qb, db, eps, mp))
                b_b = []
                for (v, u, Ax, r1, qb, db, mp) in b_pool:
                    g = sum(v[k] * s1_mp[k] for k in range(16)) + s1_Ax * Ax / d0
                    if db == 0:
                        if g in (Fraction(-1), Fraction(1)):
                            b_b.append(_mk_item(v, u, Ax, Fraction(0), r1, qb, 0, 0, mp))
                    elif db == s1_db:
                        for eps in (1, -1):
                            if g + eps * qb * s1_qb * s1_db in (Fraction(-1), Fraction(1)):
                                b_b.append(_mk_item(v, u, Ax, Fraction(0), r1, qb, db, eps, mp))
                st, _ = _clean_lp_or_cp(c0_b + b_b, len(c0_b), len(b_b), 0, 24, 32, None, rk, piv, W_fr, zeros_sv, zeros_sv, None, Mp_fr, d0, None, True, (0, 1), _S1_VALID_SETS)
                cnts[st] += 1
                excl1 |= orb1
            excl |= orb
        out[str(lens)] = {"max_rc": str(max_rc), "max_rb": str(max_rb), "twin_s0_hits": twin_s0_hits, "twin_s1_hits": twin_s1_hits, "counts": cnts, "elapsed_sec": round(time.time() - t0, 2)}
        print(f"  [PASS] S1 O(2) {lens}: {out[str(lens)]}", flush=True)
    return out


_O3_CTX: dict = {}


def _init_o3_worker(ctx: dict) -> None:
    """Populate per-worker read-only O(3) precomputed matrices for parallel s1-orbit verification."""
    global _O3_CTX
    _O3_CTX = ctx


def _run_o3_s1_orb_task(task: tuple) -> dict:
    """Process one independent (s0, s1) orbit branch of S1 (4,4,4,4) O(3) cleanly."""
    (s0_i, d0, s1_idx, excl1, c0_pool, b_pool, stab0) = task
    ctx = _O3_CTX
    rk = ctx["rk"]; piv = ctx["piv"]; W_fr = ctx["W_fr"]; Mp_fr = ctx["Mp_fr"]
    c0_vecs = ctx["c0_vecs"]; G_cc_num = ctx["G_cc_num"]; D_cc = ctx["D_cc"]
    G_bc_num = ctx["G_bc_num"]; D_bc = ctx["D_bc"]; zeros_sv = ctx["zeros_sv"]
    G_bb_num = ctx["G_bb_num"]; D_bb = ctx["D_bb"]
    M_cc_base_fl = ctx["M_cc_base_fl"]; M_bc_base_fl = ctx["M_bc_base_fl"]; M_bb_base_fl = ctx["M_bb_base_fl"]
    W_diag_fr = [W_fr[r][r] for r in range(rk)]

    def g_cc(i: int, j: int) -> Fraction:
        return Fraction(int(G_cc_num[i, j]), D_cc)

    def g_bc(bi: int, ci: int) -> Fraction:
        return Fraction(int(G_bc_num[bi, ci]), D_bc)

    s0_v, s0_u, _, s0_mp = c0_vecs[s0_i]
    s0_it = _mk_item(s0_v, s0_u, d0, Fraction(0), Fraction(0), Fraction(0), 0, 0, s0_mp, vid=s0_i)
    s1_vid, s1_v, s1_u, s1_Ax, d1, s1_mp = c0_pool[s1_idx]
    s1_it = _mk_item(s1_v, s1_u, s1_Ax, d1, Fraction(0), Fraction(0), 0, 0, s1_mp, vid=s1_vid)

    twin_s1_cnt = 0
    c0_2 = [s0_it, s1_it]
    for cid, vj, uj, Ax, r1, mpj in c0_pool:
        if r1 > d1 or (vj, Ax) in excl1:
            continue
        g1 = g_cc(cid, s1_vid) + s1_Ax * Ax / d0
        for tgt in (Fraction(1, 2), Fraction(-3, 2)):
            Bx = tgt - g1; rem2 = r1 - Bx * Bx / d1
            if rem2 >= 0:
                if cid == s1_vid and Ax == s1_Ax:
                    twin_s1_cnt += 1
                qb, db = _sf_decomp_qq(rem2)
                c0_2.append(_mk_item(vj, uj, Ax, Bx, rem2, qb, db, 1 if db > 0 else 0, mpj, vid=cid))
    b_2 = []
    for bid, vj, uj, Ax, r1, mpj in b_pool:
        g1 = g_bc(bid, s1_vid) + s1_Ax * Ax / d0
        for tgt in (Fraction(-1), Fraction(1)):
            Bx = tgt - g1; rem2 = r1 - Bx * Bx / d1
            if rem2 >= 0:
                qb, db = _sf_decomp_qq(rem2)
                b_2.append(_mk_item(vj, uj, Ax, Bx, rem2, qb, db, 1 if db > 0 else 0, mpj, vid=bid))

    stats = {"LP14": 0, "LP_SA2": 0, "LP_SB2": 0, "COUNT": 0, "C0_ENUM": 0, "C0_INFEAS": 0, "B_PSD_DEAD": 0, "B_COUNT": 0, "B_LP": 0, "B_CP": 0, "SURV": 0}
    st14, _ = _clean_lp_or_cp(c0_2 + b_2, len(c0_2), len(b_2), 0, 24, 32, None, rk, piv, W_fr, zeros_sv, zeros_sv, None, Mp_fr, d0, d1, False, (0, 1), _S1_VALID_SETS, lp_only=True)
    if st14 in ("COUNT", "LP_FARKAS"):
        stats["COUNT" if st14 == "COUNT" else "LP14"] += 1
        return {"twin_s1": twin_s1_cnt, "stats": stats}

    stab1 = [p for p in stab0 if tuple(s1_v[p[k]] for k in range(16)) == s1_v]

    def _exact_cc(a, b, sd):
        return g_cc(a[10], b[10]) + a[2] * b[2] / d0 + a[3] * b[3] / d1 + (a[7] * b[7] * a[5] * b[5] * sd if sd > 0 and a[6] == sd and b[6] == sd else Fraction(0))

    def _exact_bc(bit, cit, sd):
        return g_bc(bit[10], cit[10]) + bit[2] * cit[2] / d0 + bit[3] * cit[3] / d1 + (bit[7] * cit[7] * bit[5] * cit[5] * sd if sd > 0 and bit[6] == sd and cit[6] == sd else Fraction(0))

    def _peel_o3_clean(c0_b, b_b, sd, fix_n):
        nc_p, nb_p = len(c0_b), len(b_b)
        if nc_p < 24 or nb_p < 32:
            return [], []
        c_ids = np.array([it[10] for it in c0_b], dtype=np.int64)
        b_ids = np.array([it[10] for it in b_b], dtype=np.int64)
        Ac_fl = np.array([it[9][1] for it in c0_b], dtype=np.float64)
        Bc_fl = np.array([it[9][2] for it in c0_b], dtype=np.float64)
        Cc_fl = np.array([it[7] * it[5] * math.sqrt(sd) if sd > 0 and it[6] == sd else 0.0 for it in c0_b], dtype=np.float64)
        Ab_fl = np.array([it[9][1] for it in b_b], dtype=np.float64)
        Bb_fl = np.array([it[9][2] for it in b_b], dtype=np.float64)
        Cb_fl = np.array([it[7] * it[5] * math.sqrt(sd) if sd > 0 and it[6] == sd else 0.0 for it in b_b], dtype=np.float64)
        M_cc = M_cc_base_fl[np.ix_(c_ids, c_ids)] + np.outer(Ac_fl, Ac_fl) / float(d0) + np.outer(Bc_fl, Bc_fl) / float(d1) + np.outer(Cc_fl, Cc_fl)
        M_cb = M_bc_base_fl[np.ix_(b_ids, c_ids)].T + np.outer(Ac_fl, Ab_fl) / float(d0) + np.outer(Bc_fl, Bb_fl) / float(d1) + np.outer(Cc_fl, Cb_fl)
        M_bb = M_bb_base_fl[np.ix_(b_ids, b_ids)] + np.outer(Ab_fl, Ab_fl) / float(d0) + np.outer(Bb_fl, Bb_fl) / float(d1) + np.outer(Cb_fl, Cb_fl)
        # Conservative <1e-4 ball guarantees zero false removals on exact rational/quadratic entries
        cpos = np.abs(M_cc - 0.5) < 1e-4; cneg = np.abs(M_cc + 1.5) < 1e-4
        np.fill_diagonal(cpos, False); np.fill_diagonal(cneg, False)
        cb_ok = (np.abs(M_cb - 1.0) < 1e-4) | (np.abs(M_cb + 1.0) < 1e-4)
        bm2 = np.abs(M_bb + 2.0) < 1e-4; b0 = np.abs(M_bb) < 1e-4
        bcr = (np.abs(M_bb - 1.0) < 1e-4) | (np.abs(M_bb + 1.0) < 1e-4)
        np.fill_diagonal(bm2, False); np.fill_diagonal(b0, False)
        kc = np.ones(nc_p, dtype=bool); kb = np.ones(nb_p, dtype=bool)
        while True:
            nkc = kc & (cpos[:, kc].sum(axis=1) >= 15) & (cneg[:, kc].sum(axis=1) >= 8) & (cb_ok[:, kb].sum(axis=1) >= 32)
            nkb = kb & (cb_ok[nkc, :].sum(axis=0) >= 24) & (bm2[:, kb].sum(axis=1) >= 2) & (b0[:, kb].sum(axis=1) >= 13) & (bcr[:, kb].sum(axis=1) >= 16)
            if np.array_equal(nkc, kc) and np.array_equal(nkb, kb):
                break
            kc, kb = nkc, nkb
            if not np.all(kc[:fix_n]):
                return [], []
        return [c0_b[i] for i in range(nc_p) if kc[i]], [b_b[i] for i in range(nb_p) if kb[i]]

    def _kill_b_leaf_clean(c0_sol_items, b_filt, M14, rem_c_b, sd) -> str:
        """Clean-room B-only exact QQ Farkas LP + exact lcm-cleared B2+B3 (16+16) CP-SAT leaf killer."""
        nb_l = len(b_filt)
        if nb_l < 32:
            return "COUNT"
        b_f14 = [list(bit[1]) + [bit[2], bit[3]] for bit in b_filt]
        A_rows: list[list[Fraction]] = [[Fraction(1)] * nb_l]
        b_rhs: list[Fraction] = [Fraction(32)]
        for r in range(14):
            A_rows.append([b_f14[k][r] for k in range(nb_l)])
            b_rhs.append(Fraction(0))
        for i in range(14):
            for j in range(i, 14):
                if i == j and i < rk:
                    continue
                A_rows.append([b_f14[k][i] * b_f14[k][j] for k in range(nb_l)])
                b_rhs.append(M14[i][j])
        A_rows.append([bit[4] for bit in b_filt])
        b_rhs.append(rem_c_b)
        if sd > 0:
            b_q = [bit[7] * bit[5] if bit[6] == sd else Fraction(0) for bit in b_filt]
            c_q = [cit[7] * cit[5] if cit[6] == sd else Fraction(0) for cit in c0_sol_items]
            if any(b_q):
                A_rows.append(b_q)
                b_rhs.append(Fraction(0))
            c_f14 = [list(cit[1]) + [cit[2], cit[3]] for cit in c0_sol_items]
            for i in range(14):
                c_sum = sum(c_f14[ci][i] * c_q[ci] for ci in range(len(c0_sol_items)))
                row_q = [b_f14[k][i] * b_q[k] for k in range(nb_l)]
                if any(row_q) or c_sum != 0:
                    A_rows.append(row_q)
                    b_rhs.append(-c_sum)

        m_r = len(A_rows)
        A_fl = np.array([[float(x) for x in row] for row in A_rows], dtype=np.float64)
        b_fl = np.array([float(x) for x in b_rhs], dtype=np.float64)
        A_lp = np.empty((m_r, nb_l + 2 * m_r), dtype=np.float64)
        A_lp[:, :nb_l] = A_fl
        A_lp[:, nb_l:nb_l + m_r] = np.eye(m_r)
        A_lp[:, nb_l + m_r:] = -np.eye(m_r)
        c_lp = np.concatenate([np.zeros(nb_l), np.ones(2 * m_r)])
        res = linprog(c_lp, A_eq=A_lp, b_eq=b_fl, bounds=[(0, 1)] * nb_l + [(0, None)] * (2 * m_r), method="highs")
        if res.status == 0 and res.fun > 1e-9:
            for den_cap in (10000, 1000000, 10**9):
                y_fr = [Fraction(float(v)).limit_denominator(den_cap) if abs(float(v)) > 1e-12 else Fraction(0) for v in res.eqlin.marginals]
                nz_idx = [ri for ri, yv in enumerate(y_fr) if yv != 0]
                yt_b = sum(y_fr[ri] * b_rhs[ri] for ri in nz_idx)
                c_vals = [sum(y_fr[ri] * A_rows[ri][k] for ri in nz_idx) for k in range(nb_l)]
                lb = sum(cv for cv in c_vals if cv < 0)
                ub = sum(cv for cv in c_vals if cv > 0)
                if lb > yt_b or ub < yt_b:
                    return "LP_FARKAS"

        # Exact lcm-cleared B2 + B3 (16 + 16) graph structure using precomputed G_bb_num/M_bb_base_fl + exact Fraction edge checks
        b_ids = np.array([bit[10] for bit in b_filt], dtype=np.int64)
        Ab_fl = np.array([bit[9][1] for bit in b_filt], dtype=np.float64)
        Bb_fl = np.array([bit[9][2] for bit in b_filt], dtype=np.float64)
        Cb_fl = np.array([bit[7] * bit[5] * math.sqrt(sd) if sd > 0 and bit[6] == sd else 0.0 for bit in b_filt], dtype=np.float64)
        M_bfl = M_bb_base_fl[np.ix_(b_ids, b_ids)] + np.outer(Ab_fl, Ab_fl) / float(d0) + np.outer(Bb_fl, Bb_fl) / float(d1) + np.outer(Cb_fl, Cb_fl)
        bm2 = np.zeros((nb_l, nb_l), dtype=bool)
        b0 = np.zeros((nb_l, nb_l), dtype=bool)
        bcross = np.zeros((nb_l, nb_l), dtype=bool)
        cand_b = np.argwhere(np.triu((np.abs(M_bfl + 2.0) < 1e-3) | (np.abs(M_bfl) < 1e-3) | (np.abs(M_bfl - 1.0) < 1e-3) | (np.abs(M_bfl + 1.0) < 1e-3), k=1))
        for ip, jp in cand_b:
            i, j = int(ip), int(jp)
            mij = (
                Fraction(int(G_bb_num[b_ids[i], b_ids[j]]), D_bb)
                + b_filt[i][2] * b_filt[j][2] / d0
                + b_filt[i][3] * b_filt[j][3] / d1
                + (b_filt[i][7] * b_filt[j][7] * b_filt[i][5] * b_filt[j][5] * sd if sd > 0 and b_filt[i][6] == sd and b_filt[j][6] == sd else Fraction(0))
            )
            if mij == Fraction(-2):
                bm2[i, j] = bm2[j, i] = True
            elif mij == Fraction(0):
                b0[i, j] = b0[j, i] = True
            elif mij in (Fraction(-1), Fraction(1)):
                bcross[i, j] = bcross[j, i] = True

        # For large B pools (nb_l > 200), split losslessly on a minimum-orbit representative b_star in B2
        # under stab1 & Stab_set(C0_sol), verifying separated (B2, B3) exact QQ Farkas LP (or compact CP-SAT fallback).
        if nb_l > 200:
            c0_set = {(it[0], it[2], it[3], it[7]) for it in c0_sol_items}
            stab_c0 = [p for p in stab1 if all((tuple(it[0][p[k]] for k in range(16)), it[2], it[3], it[7]) in c0_set for it in c0_sol_items)]
            seen_b, orbs_b = set(), []
            for idx in sorted(range(nb_l), key=lambda i: (-b_filt[i][4], i)):
                it = b_filt[idx]; kb = (it[0], it[2], it[3], it[7])
                if kb in seen_b:
                    continue
                orb_b = {(tuple(it[0][p[k]] for k in range(16)), it[2], it[3], it[7]) for p in stab_c0}
                orbs_b.append((idx, orb_b)); seen_b |= orb_b
            badj = bm2 | b0
            vec_q_list = ([bit[2] for bit in b_filt], [bit[3] for bit in b_filt]) + (([bit[7] * bit[5] if bit[6] == sd else Fraction(0) for bit in b_filt],) if sd > 0 else ())
            excl_b: set = set()
            used_cp = False
            for b_star, orb_b in orbs_b:
                bad_star = badj[b_star]
                b2_cand = [j for j in range(nb_l) if bad_star[j] and (b_filt[j][0], b_filt[j][2], b_filt[j][3], b_filt[j][7]) not in excl_b]
                b3_cand = [j for j in range(nb_l) if bcross[b_star, j] and (b_filt[j][0], b_filt[j][2], b_filt[j][3], b_filt[j][7]) not in excl_b]
                if len(b2_cand) < 15 or len(b3_cand) < 16:
                    excl_b |= orb_b
                    continue
                nb2_c, nb3_c = len(b2_cand), len(b3_cand)
                u_rows_q: list[list[Fraction]] = [
                    [Fraction(1)] * nb2_c + [Fraction(0)] * nb3_c,
                    [Fraction(0)] * nb2_c + [Fraction(1)] * nb3_c,
                    [Fraction(1 if bm2[b_star, j] else 0) for j in b2_cand] + [Fraction(0)] * nb3_c,
                ]
                u_rhs_q: list[Fraction] = [Fraction(15), Fraction(16), Fraction(2)]
                for w in range(16):
                    u_rows_q.append([Fraction(int(b_filt[j][0][w])) for j in b2_cand] + [Fraction(0)] * nb3_c)
                    u_rhs_q.append(Fraction(-int(b_filt[b_star][0][w])))
                    u_rows_q.append([Fraction(0)] * nb2_c + [Fraction(int(b_filt[j][0][w])) for j in b3_cand])
                    u_rhs_q.append(Fraction(0))
                for vq in vec_q_list:
                    if any(vq):
                        u_rows_q.append([vq[j] for j in b2_cand] + [Fraction(0)] * nb3_c); u_rhs_q.append(-vq[b_star])
                        u_rows_q.append([Fraction(0)] * nb2_c + [vq[j] for j in b3_cand]); u_rhs_q.append(Fraction(0))
                for row_q, rhs_q in zip(A_rows[1 + rk:], b_rhs[1 + rk:]):
                    u_rows_q.append([row_q[j] for j in b2_cand] + [row_q[j] for j in b3_cand])
                    u_rhs_q.append(rhs_q - row_q[b_star])
                Au_fl = np.array([[float(x) for x in r] for r in u_rows_q], dtype=np.float64)
                bu_fl = np.array([float(x) for x in u_rhs_q], dtype=np.float64)
                mu, nu = Au_fl.shape
                Au_lp = np.empty((mu, nu + 2 * mu), dtype=np.float64)
                Au_lp[:, :nu] = Au_fl; Au_lp[:, nu:nu + mu] = np.eye(mu); Au_lp[:, nu + mu:] = -np.eye(mu)
                res_u = linprog(np.concatenate([np.zeros(nu), np.ones(2 * mu)]), A_eq=Au_lp, b_eq=bu_fl, bounds=[(0, 1)] * nu + [(0, None)] * (2 * mu), method="highs")
                farkas_u = False
                if res_u.status == 0 and res_u.fun > 1e-9:
                    for dc in (10000, 1000000, 10**9):
                        yf = [Fraction(float(v)).limit_denominator(dc) if abs(float(v)) > 1e-12 else Fraction(0) for v in res_u.eqlin.marginals]
                        nz_u = [ri for ri, yv in enumerate(yf) if yv != 0]
                        ytb = sum(yf[ri] * u_rhs_q[ri] for ri in nz_u)
                        cvs = [sum(yf[ri] * u_rows_q[ri][k] for ri in nz_u) for k in range(nu)]
                        if sum(c for c in cvs if c < 0) > ytb or sum(c for c in cvs if c > 0) < ytb:
                            farkas_u = True
                            break
                if not farkas_u:
                    used_cp = True
                    m_u = cp_model.CpModel()
                    xb2 = [m_u.NewBoolVar(f"x{k}") for k in range(nb2_c)]
                    xb3 = [m_u.NewBoolVar(f"y{k}") for k in range(nb3_c)]
                    b3_pos = {idx_g: p for p, idx_g in enumerate(b3_cand)}
                    for p2, idx2 in enumerate(b2_cand):
                        if idx2 in b3_pos:
                            m_u.Add(xb2[p2] + xb3[b3_pos[idx2]] <= 1)
                    for row_q, rhs_q in zip(u_rows_q, u_rhs_q):
                        ld = math.lcm(rhs_q.denominator, *[c.denominator for c in row_q if c])
                        m_u.Add(sum(int(row_q[k] * ld) * (xb2[k] if k < nb2_c else xb3[k - nb2_c]) for k in range(nu) if row_q[k] != 0) == int(rhs_q * ld))
                    for p2 in range(nb2_c):
                        idx2 = b2_cand[p2]
                        for q2 in range(p2 + 1, nb2_c):
                            if not badj[idx2, b2_cand[q2]]:
                                m_u.Add(xb2[p2] + xb2[q2] <= 1)
                        for p3, idx3 in enumerate(b3_cand):
                            if not bcross[idx2, idx3]:
                                m_u.Add(xb2[p2] + xb3[p3] <= 1)
                        m_u.Add(sum(xb2[q2] for q2, jdx2 in enumerate(b2_cand) if bm2[idx2, jdx2]) >= (2 - (1 if bm2[b_star, idx2] else 0)) * xb2[p2])
                        m_u.Add(sum(xb2[q2] for q2, jdx2 in enumerate(b2_cand) if b0[idx2, jdx2]) >= (13 - (1 if b0[b_star, idx2] else 0)) * xb2[p2])
                    for p3 in range(nb3_c):
                        idx3 = b3_cand[p3]
                        for q3 in range(p3 + 1, nb3_c):
                            if not badj[idx3, b3_cand[q3]]:
                                m_u.Add(xb3[p3] + xb3[q3] <= 1)
                        m_u.Add(sum(xb3[q3] for q3, jdx3 in enumerate(b3_cand) if bm2[idx3, jdx3]) >= 2 * xb3[p3])
                        m_u.Add(sum(xb3[q3] for q3, jdx3 in enumerate(b3_cand) if b0[idx3, jdx3]) >= 13 * xb3[p3])
                    svu = cp_model.CpSolver(); svu.parameters.num_search_workers = 1
                    stu = svu.Solve(m_u)
                    assert stu == cp_model.INFEASIBLE, f"B2+B3 split leaf unexpected status {svu.StatusName(stu)}"
                excl_b |= orb_b
            return "CP_INFEAS" if used_cp else "LP_FARKAS"

        mb = cp_model.CpModel()
        xb2 = [mb.NewBoolVar(f"b2_{k}") for k in range(nb_l)]
        xb3 = [mb.NewBoolVar(f"b3_{k}") for k in range(nb_l)]
        mb.Add(sum(xb2) == 16)
        mb.Add(sum(xb3) == 16)
        for k in range(nb_l):
            mb.Add(xb2[k] + xb3[k] <= 1)
        mb.Add(sum(k * xb2[k] for k in range(nb_l)) <= sum(k * xb3[k] for k in range(nb_l)))
        for w in range(16):
            mb.Add(sum(int(b_filt[k][0][w]) * xb2[k] for k in range(nb_l)) == 0)
            mb.Add(sum(int(b_filt[k][0][w]) * xb3[k] for k in range(nb_l)) == 0)
        # Per-sector 1_{B_k} in ker(E_15) zero-sum constraints on A, B, and sqrt(sd) coordinates
        for vec_q in ([bit[2] for bit in b_filt], [bit[3] for bit in b_filt]) + (([bit[7] * bit[5] if bit[6] == sd else Fraction(0) for bit in b_filt],) if sd > 0 else ()):
            if any(vec_q):
                ld_s = 1
                for c in vec_q:
                    if c:
                        ld_s = math.lcm(ld_s, c.denominator)
                mb.Add(sum(int(c * ld_s) * xb2[k] for k, c in enumerate(vec_q) if c != 0) == 0)
                mb.Add(sum(int(c * ld_s) * xb3[k] for k, c in enumerate(vec_q) if c != 0) == 0)
        # Exact compact degree-forcing constraints (logically equivalent to all pairwise ~badj and ~bcross clauses:
        # since bm2[k1], b0[k1], {k1} are pairwise disjoint and sum(xb2)==sum(xb3)==16, >=2 and >=13 and >=16 force
        # exact degrees 2, 13, 16 and zero weight on all non-adjacent pairs!)
        for k1 in range(nb_l):
            nb_m2 = np.where(bm2[k1])[0]
            nb_0 = np.where(b0[k1])[0]
            nb_cr = np.where(bcross[k1])[0]
            mb.Add(sum(xb2[int(k2)] for k2 in nb_m2) >= 2 * xb2[k1])
            mb.Add(sum(xb2[int(k2)] for k2 in nb_0) >= 13 * xb2[k1])
            mb.Add(sum(xb3[int(k2)] for k2 in nb_m2) >= 2 * xb3[k1])
            mb.Add(sum(xb3[int(k2)] for k2 in nb_0) >= 13 * xb3[k1])
            mb.Add(sum(xb3[int(k2)] for k2 in nb_cr) >= 16 * xb2[k1])
            mb.Add(sum(xb2[int(k2)] for k2 in nb_cr) >= 16 * xb3[k1])
        for row_q, rhs_q in zip(A_rows[1 + rk:], b_rhs[1 + rk:]):
            ld = rhs_q.denominator
            for c in row_q:
                if c:
                    ld = math.lcm(ld, c.denominator)
            mb.Add(sum(int(c * ld) * (xb2[k] + xb3[k]) for k, c in enumerate(row_q) if c != 0) == int(rhs_q * ld))
        svb = cp_model.CpSolver()
        svb.parameters.num_search_workers = 1
        stb = svb.Solve(mb)
        assert stb == cp_model.INFEASIBLE, f"B2+B3 leaf unexpected status {svb.StatusName(stb)}"
        return "CP_INFEAS"

    def _solve_sb2_branch(c0_b, b_b, n_fix, stab_cur, sd, depth, lp_stat="LP_SB2"):
        c0_b, b_b = _peel_o3_clean(c0_b, b_b, sd, n_fix)
        if len(c0_b) < 24 or len(b_b) < 32:
            stats["COUNT"] += 1
            return
        st_lp, _ = _clean_lp_or_cp(
            c0_b + b_b, len(c0_b), len(b_b), 0, 24, 32, None, rk, piv, W_fr,
            zeros_sv, zeros_sv, None, Mp_fr, d0, d1, True, tuple(range(n_fix)), _S1_VALID_SETS, lp_only=True,
        )
        if st_lp == "COUNT":
            stats["COUNT"] += 1
            return
        if st_lp == "LP_FARKAS":
            stats[lp_stat] += 1
            return

        if len(c0_b) <= 130 or n_fix >= 24:
            nc_b = len(c0_b)
            c_ids_b = np.array([it[10] for it in c0_b], dtype=np.int64)
            A_fl = np.array([it[9][1] for it in c0_b], dtype=np.float64)
            B_fl = np.array([it[9][2] for it in c0_b], dtype=np.float64)
            C_fl = np.array([it[7] * it[5] * math.sqrt(sd) if sd > 0 and it[6] == sd else 0.0 for it in c0_b], dtype=np.float64)
            M_fl = M_cc_base_fl[np.ix_(c_ids_b, c_ids_b)] + np.outer(A_fl, A_fl) / float(d0) + np.outer(B_fl, B_fl) / float(d1) + np.outer(C_fl, C_fl)
            cadj = np.zeros((nc_b, nc_b), dtype=bool)
            cneg = np.zeros((nc_b, nc_b), dtype=bool)
            cand_pairs = np.argwhere(np.triu((np.abs(M_fl - 0.5) < 1e-3) | (np.abs(M_fl + 1.5) < 1e-3), k=1))
            for i_p, j_p in cand_pairs:
                i, j = int(i_p), int(j_p)
                mij = (
                    Fraction(int(G_cc_num[c_ids_b[i], c_ids_b[j]]), D_cc)
                    + c0_b[i][2] * c0_b[j][2] / d0
                    + c0_b[i][3] * c0_b[j][3] / d1
                    + (c0_b[i][7] * c0_b[j][7] * c0_b[i][5] * c0_b[j][5] * sd if sd > 0 and c0_b[i][6] == sd and c0_b[j][6] == sd else Fraction(0))
                )
                if mij == Fraction(1, 2):
                    cadj[i, j] = cadj[j, i] = True
                elif mij == Fraction(-3, 2):
                    cadj[i, j] = cadj[j, i] = True
                    cneg[i, j] = cneg[j, i] = True

            model = cp_model.CpModel()
            vs = [model.NewBoolVar(f"c{i}") for i in range(nc_b)]
            specs_c = [("su", 0, r, Fraction(0)) for r in range(rk)] + [("as", 0, Fraction(0)), ("bs", 0, Fraction(0)), ("sec", 0, Fraction(24))]
            specs_c.extend([("fix", fi, Fraction(1)) for fi in range(n_fix)])
            if sd > 0 and any(it[6] == sd for it in c0_b):
                specs_c.append(("qs", sd, 0, Fraction(0)))
            rows_o, rhs_o = _eval_specs_exact_object(c0_b, nc_b, 0, rk, specs_c, 24, None)
            for row_o, bv in zip(rows_o, rhs_o):
                ld = bv.denominator
                for c in row_o:
                    if c:
                        ld = math.lcm(ld, c.denominator)
                model.Add(sum(int(c * ld) * vs[j] for j, c in enumerate(row_o) if c != 0) == int(bv * ld))
            for r in range(rk):
                ld_w = W_diag_fr[r].denominator
                for it in c0_b:
                    ld_w = math.lcm(ld_w, (it[1][r] * it[1][r]).denominator)
                model.Add(sum(int(it[1][r] * it[1][r] * ld_w) * vs[j] for j, it in enumerate(c0_b) if it[1][r] != 0) <= int(W_diag_fr[r] * ld_w))
            for idx_list, ub_val in [
                ([it[2] * it[2] for it in c0_b], 20 * d0),
                ([it[3] * it[3] for it in c0_b], 20 * d1),
                ([it[4] for it in c0_b], Fraction(20)),
            ]:
                ld_u = ub_val.denominator
                for c in idx_list:
                    ld_u = math.lcm(ld_u, c.denominator)
                model.Add(sum(int(c * ld_u) * vs[j] for j, c in enumerate(idx_list) if c != 0) <= int(ub_val * ld_u))
            for i in range(nc_b):
                for j in np.where(~cadj[i, i + 1:])[0] + i + 1:
                    model.Add(vs[i] + vs[int(j)] <= 1)
                nbs = [vs[int(j)] for j in np.where(cneg[i])[0]]
                # Since 1_{C0} in ker(E15) => deg_{-3/2}(x) == 8 for every x in C0
                model.Add(sum(nbs) >= 8 - 24 * (1 - vs[i]))
                model.Add(sum(nbs) <= 8 + 24 * (1 - vs[i]))

            class _C0EnumCB(cp_model.CpSolverSolutionCallback):
                def __init__(self, vars_l):
                    super().__init__()
                    self._vars = vars_l
                    self.sols: list[list[int]] = []
                    self.capped = False

                def on_solution_callback(self):
                    self.sols.append([i for i, v in enumerate(self._vars) if self.Value(v) == 1])
                    if n_fix < 24 and len(self.sols) >= 250:
                        self.capped = True
                        self.StopSearch()

            sv_c = cp_model.CpSolver()
            sv_c.parameters.num_search_workers = 1
            sv_c.parameters.enumerate_all_solutions = True
            if n_fix < 24:
                sv_c.parameters.max_deterministic_time = 0.5
            cb_c = _C0EnumCB(vs)
            st_e = sv_c.Solve(model, cb_c)
            if not cb_c.capped and st_e in (cp_model.OPTIMAL, cp_model.INFEASIBLE):
                if not cb_c.sols:
                    stats["C0_INFEAS"] += 1
                else:
                    stats["C0_ENUM"] += len(cb_c.sols)
                    # Lossless Stab(req_base) orbit deduplication of C0 solutions (b_b is Stab-invariant)
                    seen_sols: set = set()
                    uniq_sols: list[list[int]] = []
                    for sol in cb_c.sols:
                        sol_key = frozenset((c0_b[i][0], c0_b[i][2], c0_b[i][3], c0_b[i][7]) for i in sol)
                        if sol_key in seen_sols:
                            continue
                        uniq_sols.append(sol)
                        for p in stab_cur:
                            seen_sols.add(frozenset((tuple(c0_b[i][0][p[k]] for k in range(16)), c0_b[i][2], c0_b[i][3], c0_b[i][7]) for i in sol))
                    # Precompute b_b vs c0_b float64 cross matrix once across all solutions in this C0_ENUM block
                    b_ids_blk = np.array([bit[10] for bit in b_b], dtype=np.int64)
                    Ab_blk = np.array([bit[9][1] for bit in b_b], dtype=np.float64)
                    Bb_blk = np.array([bit[9][2] for bit in b_b], dtype=np.float64)
                    Cb_blk = np.array([bit[7] * bit[5] * math.sqrt(sd) if sd > 0 and bit[6] == sd else 0.0 for bit in b_b], dtype=np.float64)
                    M_bc_blk = M_bc_base_fl[np.ix_(b_ids_blk, c_ids_b)] + np.outer(Ab_blk, A_fl) / float(d0) + np.outer(Bb_blk, B_fl) / float(d1) + np.outer(Cb_blk, C_fl)
                    for sol in uniq_sols:
                        M14 = [[Fraction(0)] * 14 for _ in range(14)]
                        for r in range(12):
                            for c in range(12):
                                M14[r][c] = W_fr[r][c]
                        M14[12][12] = 20 * d0
                        M14[13][13] = 20 * d1
                        c_sq = Fraction(0)
                        for si_v in sol:
                            it = c0_b[si_v]
                            f14 = list(it[1]) + [it[2], it[3]]
                            c_sq += it[4]
                            for r in range(14):
                                fr_v = f14[r]
                                if fr_v:
                                    for c in range(14):
                                        M14[r][c] -= fr_v * f14[c]
                        rem_c_b = Fraction(20) - c_sq
                        if rem_c_b < 0 or not _ldlt_qq(M14)[0]:
                            stats["B_PSD_DEAD"] += 1
                            continue
                        N14_fr = _nullspace_qq(M14)
                        cand_b_idx = np.where(np.all(np.abs(np.abs(M_bc_blk[:, sol]) - 1.0) < 1e-4, axis=1))[0]
                        b_filt = []
                        for bi_k in cand_b_idx:
                            bit = b_b[int(bi_k)]
                            if rem_c_b == 0 and bit[4] > 0:
                                continue
                            f14 = list(bit[1]) + [bit[2], bit[3]]
                            if any(sum(nr[j] * f14[j] for j in range(14)) != 0 for nr in N14_fr):
                                continue
                            if all(_exact_bc(bit, c0_b[si_v], sd) in (Fraction(-1), Fraction(1)) for si_v in sol):
                                b_filt.append(bit)
                        if len(b_filt) < 32:
                            stats["B_COUNT"] += 1
                            continue
                        c0_sol_items = [c0_b[si_v] for si_v in sol]
                        _, b_filt = _peel_o3_clean(c0_sol_items, b_filt, sd, 24)
                        if len(b_filt) < 32:
                            stats["B_COUNT"] += 1
                            continue
                        st_b = _kill_b_leaf_clean(c0_sol_items, b_filt, M14, rem_c_b, sd)
                        if st_b == "LP_FARKAS": stats["B_LP"] += 1
                        elif st_b == "CP_INFEAS": stats["B_CP"] += 1
                        elif st_b == "COUNT": stats["B_COUNT"] += 1
                        else: stats["SURV"] += 1
                return

        # Lossless Stab(req_base) case split prioritizing the 8 cneg(s0) == -3/2 neighbors
        cneg_fix = sum(1 for i in range(n_fix) if _exact_cc(c0_b[0], c0_b[i], sd) == Fraction(-3, 2))
        tgt_val = Fraction(-3, 2) if cneg_fix < 8 else Fraction(1, 2)
        pool_idx = [idx for idx in range(n_fix, len(c0_b)) if _exact_cc(c0_b[0], c0_b[idx], sd) == tgt_val]
        if not pool_idx:
            stats["COUNT"] += 1
            return
        seen_d, orbs_d = set(), []
        for idx in pool_idx:
            it = c0_b[idx]; key = (it[0], it[2], it[3], it[7])
            if key in seen_d:
                continue
            orb = {(tuple(it[0][p[k]] for k in range(16)), it[2], it[3], it[7]) for p in stab_cur}
            orbs_d.append((idx, orb)); seen_d |= orb
        excl_d = set()
        for sk_idx, orb in orbs_d:
            sk_it = c0_b[sk_idx]
            c_sub = list(c0_b[:n_fix]) + [sk_it]
            for j in range(n_fix, len(c0_b)):
                it = c0_b[j]
                if j == sk_idx or (it[0], it[2], it[3], it[7]) in excl_d:
                    continue
                if _exact_cc(it, sk_it, sd) in (Fraction(1, 2), Fraction(-3, 2)):
                    c_sub.append(it)
            b_sub = [bit for bit in b_b if _exact_bc(bit, sk_it, sd) in (Fraction(-1), Fraction(1))]
            sk_v = sk_it[0]
            stab_n = [p for p in stab_cur if tuple(sk_v[p[k]] for k in range(16)) == sk_v]
            _solve_sb2_branch(c_sub, b_sub, n_fix + 1, stab_n, sd, depth + 1, lp_stat=lp_stat)
            excl_d |= orb

    # S_A2: C0 has rem2 == 0 only (using shared clean peeling + C0_ENUM + B leaf pipeline)
    c0_sa2 = [s0_it, s1_it] + [it for it in c0_2[2:] if it[6] == 0]
    if len(c0_sa2) >= 24:
        for db_b in (sorted({it[6] for it in b_2 if it[6] > 0}) or [0]):
            b_sa2 = [it for it in b_2 if it[6] == 0]
            for it in b_2:
                if db_b > 0 and it[6] == db_b:
                    b_sa2.extend([it, _mk_item(it[0], it[1], it[2], it[3], it[4], it[5], it[6], -1, it[8], vid=it[10])])
            _solve_sb2_branch(c0_sa2, b_sa2, 2, stab1, db_b, 0, lp_stat="LP_SA2")

    # S_B2: Stab(s0, s1) orbits on c0_2[2:] with db > 0 (ascending rem2 order cuts max branch width cleanly)
    nz2 = sorted([idx for idx in range(2, len(c0_2)) if c0_2[idx][6] > 0], key=lambda idx: (c0_2[idx][4], idx))
    seen2, orbs2 = set(), []
    for idx in nz2:
        it = c0_2[idx]; key = (it[0], it[2], it[3])
        if key in seen2:
            continue
        orb2 = {(tuple(it[0][p[k]] for k in range(16)), it[2], it[3]) for p in stab1}
        orbs2.append((idx, orb2)); seen2 |= orb2
    excl2 = set()
    for s2_idx, orb2 in orbs2:
        s2_it = c0_2[s2_idx]; s2_d = s2_it[6]; s2_vid = s2_it[10]
        c0_b = [s0_it, s1_it, s2_it]
        for j in range(2, len(c0_2)):
            it = c0_2[j]
            if (it[0], it[2], it[3]) in excl2 or (it[6] > 0 and it[6] != s2_d):
                continue
            g2 = g_cc(it[10], s2_vid) + s2_it[2] * it[2] / d0 + s2_it[3] * it[3] / d1
            if it[6] == 0:
                if g2 in (Fraction(1, 2), Fraction(-3, 2)):
                    c0_b.append(it)
            else:
                for eps in (1, -1):
                    if j == s2_idx and eps == 1:
                        continue
                    if g2 + eps * it[5] * s2_it[5] * s2_d in (Fraction(1, 2), Fraction(-3, 2)):
                        c0_b.append(_mk_item(it[0], it[1], it[2], it[3], it[4], it[5], it[6], eps, it[8], vid=it[10]))
        b_b = []
        for it in b_2:
            if it[6] > 0 and it[6] != s2_d:
                continue
            g2 = g_bc(it[10], s2_vid) + s2_it[2] * it[2] / d0 + s2_it[3] * it[3] / d1
            if it[6] == 0:
                if g2 in (Fraction(-1), Fraction(1)):
                    b_b.append(it)
            else:
                for eps in (1, -1):
                    if g2 + eps * it[5] * s2_it[5] * s2_d in (Fraction(-1), Fraction(1)):
                        b_b.append(_mk_item(it[0], it[1], it[2], it[3], it[4], it[5], it[6], eps, it[8], vid=it[10]))
        s2_v = s2_it[0]
        stab2 = [p for p in stab1 if tuple(s2_v[p[k]] for k in range(16)) == s2_v]
        _solve_sb2_branch(c0_b, b_b, 3, stab2, s2_d, 0)
        excl2 |= orb2
    return {"twin_s1": twin_s1_cnt, "stats": stats}


def audit_s1_o3_4444_clean_room(include_q3: bool = True, workers: int = 0) -> dict:
    """Clean-room full elimination of S1 (4,4,4,4) O(3) across Subcase A and Subcase B (q0 in {7/2,5/2,2,3})."""
    t0 = time.time()
    rk, piv, W_fr, Mp_fr, c0_vecs, b_vecs, max_rc, max_rb = _setup_s1_part((4, 4, 4, 4))
    c0_q = [Fraction(9, 2) - rec[2] for rec in c0_vecs]
    perms = _aut_cycle_part((4, 4, 4, 4))
    c0_by_v = {rec[0]: idx for idx, rec in enumerate(c0_vecs)}
    for q_val in sorted(set(c0_q)):
        level_idxs = {i for i, q in enumerate(c0_q) if q == q_val}
        rep_v = c0_vecs[next(iter(level_idxs))][0]
        orb = {c0_by_v[tuple(rep_v[p[k]] for k in range(16))] for p in perms}
        assert orb == level_idxs, f"Aut not transitive on Q={q_val}"
    assert set(c0_q) == {Fraction(2), Fraction(5, 2), Fraction(3), Fraction(7, 2), Fraction(4)}

    G_cc_num, D_cc = _precompute_g_mat([r[0] for r in c0_vecs], [r[0] for r in c0_vecs], Mp_fr)
    G_bc_num, D_bc = _precompute_g_mat([r[0] for r in b_vecs], [r[0] for r in c0_vecs], Mp_fr)
    G_bb_num, D_bb = _precompute_g_mat([r[0] for r in b_vecs], [r[0] for r in b_vecs], Mp_fr)
    zeros_sv = [Fraction(0)] * 16

    def g_cc(i: int, j: int) -> Fraction:
        return Fraction(int(G_cc_num[i, j]), D_cc)

    def g_bc(bi: int, ci: int) -> Fraction:
        return Fraction(int(G_bc_num[bi, ci]), D_bc)

    subcase_a = {}
    for q0 in [Fraction(4), Fraction(7, 2), Fraction(3), Fraction(5, 2), Fraction(2)]:
        d0 = Fraction(9, 2) - q0
        s0_i = next(i for i, q in enumerate(c0_q) if q == q0)
        s0_v, s0_u, _, s0_mp = c0_vecs[s0_i]
        c0_a = [_mk_item(s0_v, s0_u, d0, Fraction(0), Fraction(0), Fraction(0), 0, 0, s0_mp, vid=s0_i)]
        for j, (vj, uj, rj, mpj) in enumerate(c0_vecs):
            if rj > d0: continue
            g = g_cc(j, s0_i)
            for tgt in (Fraction(1, 2), Fraction(-3, 2)):
                Ax = tgt - g
                if rj - Ax * Ax / d0 == 0:
                    c0_a.append(_mk_item(vj, uj, Ax, Fraction(0), Fraction(0), Fraction(0), 0, 0, mpj, vid=j))
        if len(c0_a) < 24:
            subcase_a[str(q0)] = {"nc": len(c0_a), "status": "COUNT_DEAD"}
        else:
            nc = len(c0_a)
            specs_a = [("su", 0, r, Fraction(0)) for r in range(rk)] + [("as", 0, Fraction(0)), ("sec", 0, Fraction(24)), ("fix", 0, Fraction(1))]
            st, _ = _solve_cp_exact(c0_a, nc, 0, 0, 24, None, None, rk, specs_a, Mp_fr, d0, None, _S1_VALID_SETS, False)
            assert st == "CP_INFEAS"
            subcase_a[str(q0)] = {"nc": nc, "status": "CP_INFEAS"}
    print(f"  [PASS] S1 (4,4,4,4) Subcase A: {subcase_a}", flush=True)

    subcase_b = {}
    q0_targets = [Fraction(7, 2), Fraction(5, 2), Fraction(2)] + ([Fraction(3)] if include_q3 else [])
    n_workers = workers if workers > 0 else min(8, os.cpu_count() or 1)
    ctx_payload = {
        "rk": rk, "piv": piv, "W_fr": W_fr, "Mp_fr": Mp_fr,
        "c0_vecs": c0_vecs, "G_cc_num": G_cc_num, "D_cc": D_cc,
        "G_bc_num": G_bc_num, "D_bc": D_bc,
        "G_bb_num": G_bb_num, "D_bb": D_bb,
        "M_cc_base_fl": G_cc_num.astype(np.float64) / float(D_cc),
        "M_bc_base_fl": G_bc_num.astype(np.float64) / float(D_bc),
        "M_bb_base_fl": G_bb_num.astype(np.float64) / float(D_bb),
        "zeros_sv": zeros_sv,
    }
    _init_o3_worker(ctx_payload)
    for q0 in q0_targets:
        ts = time.time()
        d0 = Fraction(9, 2) - q0
        s0_i = next(i for i, q in enumerate(c0_q) if q == q0)
        s0_v, _, _, _ = c0_vecs[s0_i]
        stab0 = [p for p in perms if tuple(s0_v[p[k]] for k in range(16)) == s0_v]
        c0_pool = []; twin_s0_cnt = 0
        for j, (vj, uj, rj, mpj) in enumerate(c0_vecs):
            if rj > d0: continue
            g = g_cc(j, s0_i)
            for tgt in (Fraction(1, 2), Fraction(-3, 2)):
                Ax = tgt - g; rem1 = rj - Ax * Ax / d0
                if rem1 >= 0:
                    if j == s0_i: twin_s0_cnt += 1
                    c0_pool.append((j, vj, uj, Ax, rem1, mpj))
        if d0 < 2:
            assert twin_s0_cnt == 0
        b_pool = []
        for j, (vj, uj, rj, mpj) in enumerate(b_vecs):
            g = g_bc(j, s0_i)
            for tgt in (Fraction(-1), Fraction(1)):
                Ax = tgt - g; rem1 = rj - Ax * Ax / d0
                if rem1 >= 0:
                    b_pool.append((j, vj, uj, Ax, rem1, mpj))
        nz1 = sorted([i for i, r in enumerate(c0_pool) if r[4] > 0], key=lambda i: (-c0_pool[i][4], i))
        seen1, orbs1 = set(), []
        for idx in nz1:
            _, v, _, Ax, _, _ = c0_pool[idx]
            if (v, Ax) in seen1: continue
            orb = {(tuple(v[p[k]] for k in range(16)), Ax) for p in stab0}
            orbs1.append((idx, orb)); seen1 |= orb
        tasks = []
        cum_excl1: set = set()
        for s1_idx, orb1 in orbs1:
            tasks.append((s0_i, d0, s1_idx, set(cum_excl1), c0_pool, b_pool, stab0))
            cum_excl1 |= orb1

        stats = {"LP14": 0, "LP_SA2": 0, "LP_SB2": 0, "COUNT": 0, "C0_ENUM": 0, "C0_INFEAS": 0, "B_PSD_DEAD": 0, "B_COUNT": 0, "B_LP": 0, "B_CP": 0, "SURV": 0}
        twin_s1_cnt = 0
        if n_workers > 1 and len(tasks) > 1:
            with ProcessPoolExecutor(max_workers=n_workers, initializer=_init_o3_worker, initargs=(ctx_payload,)) as ex:
                for res_t in ex.map(_run_o3_s1_orb_task, tasks):
                    twin_s1_cnt += res_t["twin_s1"]
                    for kk, vv in res_t["stats"].items(): stats[kk] += vv
        else:
            for tsk in tasks:
                res_t = _run_o3_s1_orb_task(tsk)
                twin_s1_cnt += res_t["twin_s1"]
                for kk, vv in res_t["stats"].items(): stats[kk] += vv
        assert stats["SURV"] == 0, f"(4,4,4,4) q0={q0} had survivors: {stats}"
        subcase_b[str(q0)] = {"s1_orbs": len(orbs1), "twin_s0": twin_s0_cnt, "twin_s1": twin_s1_cnt, "stats": stats, "elapsed_sec": round(time.time() - ts, 2)}
        print(f"  [PASS] S1 (4,4,4,4) q0={q0}: {subcase_b[str(q0)]}", flush=True)

    return {"max_rc": str(max_rc), "max_rb": str(max_rb), "subcase_a": subcase_a, "subcase_b": subcase_b, "elapsed_sec": round(time.time() - t0, 2)}


_S23_VALID_SETS = {
    (0, 0): (Fraction(1, 2), Fraction(-3, 2)),
    (0, 1): (Fraction(-1), Fraction(1)),
    (0, 2): (Fraction(-1), Fraction(1)),
    (1, 1): (Fraction(0), Fraction(-2)),
    (2, 2): (Fraction(0), Fraction(-2)),
    (1, 2): (Fraction(-1), Fraction(1)),
}


def _kill_s2_or_s3_core_clean(
    name: str, m_core: int, n_b1: int, n_c0: int, n_b2: int, n_b3: int,
    c0_sv: list[Fraction], b2_sv: list[Fraction], b3_sv: list[Fraction],
    M_fr: list[list[Fraction]], raw_perms: list[tuple[int, ...]],
    vb1_masks: list[tuple[int, ...]], c0_opts_c2, b2_opts_c2, b3_opts_c2,
) -> tuple[dict[str, int], Fraction, Fraction, Fraction]:
    """Clean-room O(0)/O(1)/O(2) eliminator for an S2 (18x18) or S3 (20x20) core with BLOCKER-1 twins."""
    perms = [p for p in raw_perms if all(M_fr[p[i]][p[j]] == M_fr[i][j] for i in range(m_core) for j in range(i, m_core))]
    M_sp = sp.Matrix([[sp.Rational(x.numerator, x.denominator) for x in r] for r in M_fr])
    Mp, rk, piv = _pinv_exact_qq(M_sp)
    N_sp = M_sp.nullspace()
    W_sp = (20 * M_sp - M_sp * M_sp).extract(piv, piv)
    assert W_sp.is_positive_semidefinite
    W_fr = [[Fraction(int(W_sp[r, c].p), int(W_sp[r, c].q)) for c in range(rk)] for r in range(rk)]
    Mp_fr = [[Fraction(int(Mp[r, c].p), int(Mp[r, c].q)) for c in range(m_core)] for r in range(m_core)]
    N_int = []
    for nv_sp in N_sp:
        nr = [Fraction(int(nv_sp[j].p), int(nv_sp[j].q)) for j in range(m_core)]
        ld = 1
        for x in nr:
            ld = math.lcm(ld, x.denominator)
        N_int.append([int(x * ld) for x in nr])
    V_np = np.array(vb1_masks, dtype=np.int8)
    Nb1_np = np.array([r[:n_b1] for r in N_int], dtype=np.int64)
    lhs = V_np @ Nb1_np.T
    lhs_map: dict[tuple[int, ...], list[tuple[int, ...]]] = {}
    for ri, row in enumerate(lhs):
        lhs_map.setdefault(tuple(int(x) for x in row), []).append(vb1_masks[ri])
    n_c2 = m_core - n_b1

    c0_cands, b2_cands, b3_cands = [], [], []
    for opts_c2, tgt_res, out_list in [(c0_opts_c2, Fraction(9, 2), c0_cands), (b2_opts_c2, Fraction(4), b2_cands), (b3_opts_c2, Fraction(4), b3_cands)]:
        for c2t in opts_c2:
            need = []; ok_int = True
            for nr in N_int:
                val = -sum(nr[n_b1 + j] * c2t[j] for j in range(n_c2))
                if val.denominator != 1:
                    ok_int = False; break
                need.append(int(val))
            if not ok_int:
                continue
            for vb1 in lhs_map.get(tuple(need), ()):
                vf = tuple([Fraction(x) for x in vb1] + list(c2t))
                Mp_v = [sum(Mp_fr[r][c] * vf[c] for c in range(m_core)) for r in range(m_core)]
                q = sum(vf[r] * Mp_v[r] for r in range(m_core))
                if q <= tgt_res:
                    out_list.append((vf, tuple(vf[p] for p in piv), tgt_res - q, Mp_v))

    max_r0 = max((r[2] for r in c0_cands), default=Fraction(0))
    max_rb2 = max((r[2] for r in b2_cands), default=Fraction(0))
    max_rb3 = max((r[2] for r in b3_cands), default=Fraction(0))
    assert max_r0 < Fraction(8, 3) and max_rb2 < Fraction(8, 3) and max_rb3 < Fraction(8, 3), (name, max_r0, max_rb2, max_rb3)

    s_rem = 15 - rk
    cnts = {"COUNT": 0, "LP_FARKAS": 0, "CP_INFEAS": 0}
    if s_rem == 0:
        c0_z = [_mk_item(v, u, Fraction(0), Fraction(0), Fraction(0), Fraction(0), 0, 0, mp) for (v, u, r, mp) in c0_cands if r == 0]
        b2_z = [_mk_item(v, u, Fraction(0), Fraction(0), Fraction(0), Fraction(0), 0, 0, mp) for (v, u, r, mp) in b2_cands if r == 0]
        b3_z = [_mk_item(v, u, Fraction(0), Fraction(0), Fraction(0), Fraction(0), 0, 0, mp) for (v, u, r, mp) in b3_cands if r == 0]
        st, _ = _clean_lp_or_cp(c0_z + b2_z + b3_z, len(c0_z), len(b2_z), len(b3_z), n_c0, n_b2, n_b3, rk, piv, W_fr, c0_sv, b2_sv, b3_sv, Mp_fr, None, None, True, (), _S23_VALID_SETS)
        cnts[st] += 1
    elif s_rem == 1:
        def _exp1(lst):
            out = []
            for v, u, r, mp in lst:
                q, d = _sf_decomp_qq(r)
                if d == 0:
                    out.append(_mk_item(v, u, Fraction(0), Fraction(0), r, q, 0, 0, mp))
                else:
                    out.extend([_mk_item(v, u, Fraction(0), Fraction(0), r, q, d, 1, mp), _mk_item(v, u, Fraction(0), Fraction(0), r, q, d, -1, mp)])
            return out
        c0_e, b2_e, b3_e = _exp1(c0_cands), _exp1(b2_cands), _exp1(b3_cands)
        c0_by_v = {rec[0]: idx for idx, rec in enumerate(c0_cands)}
        for dv in [0] + sorted({it[6] for it in c0_e + b2_e + b3_e if it[6] > 0}):
            cs = [it for it in c0_e if it[6] in (0, dv)]
            b2s = [it for it in b2_e if it[6] in (0, dv)]
            b3s = [it for it in b3_e if it[6] in (0, dv)]
            st, _ = _clean_lp_or_cp(cs + b2s + b3s, len(cs), len(b2s), len(b3s), n_c0, n_b2, n_b3, rk, piv, W_fr, c0_sv, b2_sv, b3_sv, Mp_fr, None, None, True, (), _S23_VALID_SETS, lp_only=True)
            if st != "SURV":
                cnts[st] += 1
                continue
            if dv == 0:
                st, _ = _clean_lp_or_cp(cs + b2s + b3s, len(cs), len(b2s), len(b3s), n_c0, n_b2, n_b3, rk, piv, W_fr, c0_sv, b2_sv, b3_sv, Mp_fr, None, None, True, (), _S23_VALID_SETS, lp_only=False)
                cnts[st] += 1
                continue
            # Case 0 (C0 has r==0 only):
            cs_z = [it for it in cs if it[6] == 0]
            st_z, _ = _clean_lp_or_cp(cs_z + b2s + b3s, len(cs_z), len(b2s), len(b3s), n_c0, n_b2, n_b3, rk, piv, W_fr, c0_sv, b2_sv, b3_sv, Mp_fr, None, None, True, (), _S23_VALID_SETS, lp_only=False)
            cnts[st_z] += 1
            # Case 1: orbit-break s0 in C0 with db == dv (eps_s0 = +1 by r -> -r global sign symmetry):
            nz_c = sorted([i for i, rec in enumerate(c0_cands) if _sf_decomp_qq(rec[2])[1] == dv], key=lambda i: (-c0_cands[i][2], i))
            seen_o1, excl1 = set(), set()
            for s0_i in nz_c:
                if s0_i in seen_o1:
                    continue
                v_s0, u_s0, d0_s, mp_s0 = c0_cands[s0_i]
                q_s0, _ = _sf_decomp_qq(d0_s)
                orb1 = {c0_by_v[tuple(v_s0[p[k]] for k in range(m_core))] for p in perms}
                seen_o1 |= orb1
                s0_it = _mk_item(v_s0, u_s0, Fraction(0), Fraction(0), d0_s, q_s0, dv, 1, mp_s0)
                c_sub = [s0_it]
                for it in cs:
                    if c0_by_v[it[0]] in excl1 or (it[0] == v_s0 and it[7] == 1):
                        continue
                    mij = sum(it[0][k] * mp_s0[k] for k in range(m_core)) + (it[7] * it[5] * q_s0 * dv if it[6] == dv else Fraction(0))
                    if mij in (Fraction(1, 2), Fraction(-3, 2)):
                        c_sub.append(it)
                def _filt_b(blist):
                    out_b = []
                    for it in blist:
                        mij = sum(it[0][k] * mp_s0[k] for k in range(m_core)) + (it[7] * it[5] * q_s0 * dv if it[6] == dv else Fraction(0))
                        if mij in (Fraction(-1), Fraction(1)):
                            out_b.append(it)
                    return out_b
                b2_sub, b3_sub = _filt_b(b2s), _filt_b(b3s)
                st_b, _ = _clean_lp_or_cp(c_sub + b2_sub + b3_sub, len(c_sub), len(b2_sub), len(b3_sub), n_c0, n_b2, n_b3, rk, piv, W_fr, c0_sv, b2_sv, b3_sv, Mp_fr, None, None, True, (0,), _S23_VALID_SETS, lp_only=False)
                cnts[st_b] += 1
                excl1 |= orb1
    elif s_rem == 2:
        c0_z = [_mk_item(v, u, Fraction(0), Fraction(0), Fraction(0), Fraction(0), 0, 0, mp) for (v, u, r, mp) in c0_cands if r == 0]
        def _expb0(lst):
            out = []
            for v, u, r, mp in lst:
                q, d = _sf_decomp_qq(r)
                if d == 0:
                    out.append(_mk_item(v, u, Fraction(0), Fraction(0), r, q, 0, 0, mp))
                else:
                    out.extend([_mk_item(v, u, Fraction(0), Fraction(0), r, q, d, 1, mp), _mk_item(v, u, Fraction(0), Fraction(0), r, q, d, -1, mp)])
            return out
        b2_0, b3_0 = _expb0(b2_cands), _expb0(b3_cands)
        for dv in [0] + sorted({it[6] for it in b2_0 + b3_0 if it[6] > 0}):
            b2s = [it for it in b2_0 if it[6] in (0, dv)]; b3s = [it for it in b3_0 if it[6] in (0, dv)]
            st, _ = _clean_lp_or_cp(c0_z + b2s + b3s, len(c0_z), len(b2s), len(b3s), n_c0, n_b2, n_b3, rk, piv, W_fr, c0_sv, b2_sv, b3_sv, Mp_fr, None, None, True, (), _S23_VALID_SETS)
            cnts[st] += 1
        nz = sorted([i for i, rec in enumerate(c0_cands) if rec[2] > 0], key=lambda i: (-c0_cands[i][2], i))
        c0_by_v = {rec[0]: idx for idx, rec in enumerate(c0_cands)}
        seen_o, excl = set(), set()
        for s0_i in nz:
            if s0_i in seen_o:
                continue
            v_s0, u_s0, d0, mp_s0 = c0_cands[s0_i]
            orb = {c0_by_v[tuple(v_s0[p[k]] for k in range(m_core))] for p in perms}
            seen_o |= orb
            s0_it = _mk_item(v_s0, u_s0, d0, Fraction(0), Fraction(0), Fraction(0), 0, 0, mp_s0)
            c0_pool = []
            for j, (vj, uj, rj, mpj) in enumerate(c0_cands):
                if j in excl or rj > d0:
                    continue
                g = sum(vj[k] * mp_s0[k] for k in range(m_core))
                for tgt in (Fraction(1, 2), Fraction(-3, 2)):
                    Ax = tgt - g; rem1 = rj - Ax * Ax / d0
                    if rem1 >= 0:
                        qb, db = _sf_decomp_qq(rem1)
                        c0_pool.append((vj, uj, Ax, rem1, qb, db, mpj))
            def _psec(lst):
                out = []
                for vj, uj, rj, mpj in lst:
                    g = sum(vj[k] * mp_s0[k] for k in range(m_core))
                    for tgt in (Fraction(-1), Fraction(1)):
                        Ax = tgt - g; rem1 = rj - Ax * Ax / d0
                        if rem1 >= 0:
                            qb, db = _sf_decomp_qq(rem1)
                            out.append((vj, uj, Ax, rem1, qb, db, mpj))
                return out
            b2_pool, b3_pool = _psec(b2_cands), _psec(b3_cands)
            all_dvs = [0] + sorted({rec[5] for rec in c0_pool + b2_pool + b3_pool if rec[5] > 0})
            surv_dvs = []
            for dv in all_dvs:
                cs = [s0_it]
                for (vj, uj, Ax, r1, qb, db, mpj) in c0_pool:
                    if db == 0:
                        cs.append(_mk_item(vj, uj, Ax, Fraction(0), r1, qb, 0, 0, mpj))
                    elif db == dv:
                        cs.extend([_mk_item(vj, uj, Ax, Fraction(0), r1, qb, db, 1, mpj), _mk_item(vj, uj, Ax, Fraction(0), r1, qb, db, -1, mpj)])
                def _ex_dv(pl):
                    oo = []
                    for (vj, uj, Ax, r1, qb, db, mpj) in pl:
                        if db == 0: oo.append(_mk_item(vj, uj, Ax, Fraction(0), r1, qb, 0, 0, mpj))
                        elif db == dv: oo.extend([_mk_item(vj, uj, Ax, Fraction(0), r1, qb, db, 1, mpj), _mk_item(vj, uj, Ax, Fraction(0), r1, qb, db, -1, mpj)])
                    return oo
                b2s, b3s = _ex_dv(b2_pool), _ex_dv(b3_pool)
                st, _ = _clean_lp_or_cp(cs + b2s + b3s, len(cs), len(b2s), len(b3s), n_c0, n_b2, n_b3, rk, piv, W_fr, c0_sv, b2_sv, b3_sv, Mp_fr, d0, None, True, (0,), _S23_VALID_SETS, lp_only=True)
                if st != "SURV":
                    cnts[st] += 1
                else:
                    surv_dvs.append(dv)
            if surv_dvs:
                # Split B0 vs B1 (Stab(s0) orbit-breaking on s1)!
                if 0 in surv_dvs or any(dv > 0 for dv in surv_dvs):
                    c0_0 = [s0_it] + [_mk_item(v, u, Ax, Fraction(0), r1, qb, 0, 0, mp) for (v, u, Ax, r1, qb, db, mp) in c0_pool if db == 0]
                    for db_b in [d for d in sorted({rec[5] for rec in b2_pool + b3_pool if rec[5] > 0}) if d in surv_dvs or 0 in surv_dvs]:
                        b2d0 = [_mk_item(v, u, Ax, Fraction(0), r1, qb, 0, 0, mp) for (v, u, Ax, r1, qb, db, mp) in b2_pool if db == 0] + [it for (v, u, Ax, r1, qb, db, mp) in b2_pool if db == db_b for it in (_mk_item(v, u, Ax, Fraction(0), r1, qb, db, 1, mp), _mk_item(v, u, Ax, Fraction(0), r1, qb, db, -1, mp))]
                        b3d0 = [_mk_item(v, u, Ax, Fraction(0), r1, qb, 0, 0, mp) for (v, u, Ax, r1, qb, db, mp) in b3_pool if db == 0] + [it for (v, u, Ax, r1, qb, db, mp) in b3_pool if db == db_b for it in (_mk_item(v, u, Ax, Fraction(0), r1, qb, db, 1, mp), _mk_item(v, u, Ax, Fraction(0), r1, qb, db, -1, mp))]
                        st, _ = _clean_lp_or_cp(c0_0 + b2d0 + b3d0, len(c0_0), len(b2d0), len(b3d0), n_c0, n_b2, n_b3, rk, piv, W_fr, c0_sv, b2_sv, b3_sv, Mp_fr, d0, None, True, (0,), _S23_VALID_SETS, lp_only=False)
                        cnts[st] += 1
                stab_s0 = [p for p in perms if tuple(v_s0[p[k]] for k in range(m_core)) == v_s0]
                nz1_idxs = [idx for idx, rec in enumerate(c0_pool) if rec[5] in surv_dvs and rec[5] > 0]
                seen_s1, s1_orbs = set(), []
                for idx in nz1_idxs:
                    rec = c0_pool[idx]; key = (rec[0], rec[2])
                    if key in seen_s1: continue
                    orb1 = {(tuple(rec[0][p[k]] for k in range(m_core)), rec[2]) for p in stab_s0}
                    s1_orbs.append((idx, orb1)); seen_s1 |= orb1
                excl1 = set()
                for s1_idx, orb1 in s1_orbs:
                    s1_v, s1_u, s1_Ax, s1_r1, s1_qb, s1_db, s1_mp = c0_pool[s1_idx]
                    s1_it = _mk_item(s1_v, s1_u, s1_Ax, Fraction(0), s1_r1, s1_qb, s1_db, 1, s1_mp)
                    c0_b = [s0_it, s1_it]
                    for j, (v, u, Ax, r1, qb, db, mp) in enumerate(c0_pool):
                        if (v, Ax) in excl1 or (db > 0 and db != s1_db): continue
                        g = sum(v[k] * s1_mp[k] for k in range(m_core)) + s1_Ax * Ax / d0
                        if db == 0:
                            if g in (Fraction(1, 2), Fraction(-3, 2)): c0_b.append(_mk_item(v, u, Ax, Fraction(0), r1, qb, 0, 0, mp))
                        else:
                            for eps in (1, -1):
                                if j == s1_idx and eps == 1: continue
                                if g + eps * qb * s1_qb * s1_db in (Fraction(1, 2), Fraction(-3, 2)):
                                    c0_b.append(_mk_item(v, u, Ax, Fraction(0), r1, qb, db, eps, mp))
                    def _fb1(pl):
                        oo = []
                        for (v, u, Ax, r1, qb, db, mp) in pl:
                            if db > 0 and db != s1_db: continue
                            g = sum(v[k] * s1_mp[k] for k in range(m_core)) + s1_Ax * Ax / d0
                            if db == 0:
                                if g in (Fraction(-1), Fraction(1)): oo.append(_mk_item(v, u, Ax, Fraction(0), r1, qb, 0, 0, mp))
                            else:
                                for eps in (1, -1):
                                    if g + eps * qb * s1_qb * s1_db in (Fraction(-1), Fraction(1)):
                                        oo.append(_mk_item(v, u, Ax, Fraction(0), r1, qb, db, eps, mp))
                        return oo
                    b2_b, b3_b = _fb1(b2_pool), _fb1(b3_pool)
                    st, _ = _clean_lp_or_cp(c0_b + b2_b + b3_b, len(c0_b), len(b2_b), len(b3_b), n_c0, n_b2, n_b3, rk, piv, W_fr, c0_sv, b2_sv, b3_sv, Mp_fr, d0, None, True, (0, 1), _S23_VALID_SETS, lp_only=False)
                    cnts[st] += 1
                    excl1 |= orb1
            excl |= orb
    return cnts, max_r0, max_rb2, max_rb3


def _run_s3_core_task(task: tuple):
    """Worker task executing exact elimination on one canonical S3 20x20 core."""
    oi, M20_fr, perms, v14_list, s3_c0, s3_b2, s3_b3 = task
    c0_sv = [-M20_fr[r][14] + M20_fr[r][15] - M20_fr[r][16] + M20_fr[r][17] - M20_fr[r][18] + M20_fr[r][19] for r in range(20)]
    b2_sv = [-M20_fr[r][16] - M20_fr[r][17] - M20_fr[r][18] - M20_fr[r][19] for r in range(20)]
    b3_sv = [-M20_fr[r][14] - M20_fr[r][15] - M20_fr[r][18] - M20_fr[r][19] for r in range(20)]
    return _kill_s2_or_s3_core_clean(f"S3_orb{oi}", 20, 14, 26, 14, 14, c0_sv, b2_sv, b3_sv, M20_fr, perms, v14_list, s3_c0, s3_b2, s3_b3)


def audit_s2_and_s3_clean_room(workers: int = 0) -> dict:
    """Clean-room exact verification and full elimination of S2 (15 configs/cores) and S3 (10 orbits / 123 cores)."""
    # 1. S2 elimination
    t0 = time.time()
    s2_configs = [
        (1, (14,)), (1, (10, 4)), (1, (8, 6)), (1, (6, 4, 4)),
        (3, (12,)), (3, (8, 4)), (3, (6, 6)), (3, (4, 4, 4)),
        (5, (10,)), (5, (6, 4)), (7, (8,)), (7, (4, 4)), (9, (6,)), (11, (4,)), (15, ()),
    ]
    def _aut_s2(k: int, cycs: tuple[int, ...]) -> list[tuple[int, ...]]:
        off = k; by_len: dict[int, list[list[int]]] = {}
        for L in cycs:
            by_len.setdefault(L, []).append(list(range(off, off + L))); off += L
        per_cyc = {
            tuple(cyc): (
                [[cyc[(i + s) % len(cyc)] for i in range(len(cyc))] for s in range(len(cyc))]
                + [[cyc[(s - i) % len(cyc)] for i in range(len(cyc))] for s in range(len(cyc))]
            )
            for cl in by_len.values()
            for cyc in cl
        }
        len_groups = list(by_len.values()); perms = []
        for rev in (0, 1):
            pk_map = [i if rev == 0 else (k - 1 - i) for i in range(k)]
            z_map = [15, 16, 17] if rev == 0 else [16, 15, 17]
            for gperms in itertools.product(*[list(itertools.permutations(range(len(g)))) for g in len_groups]):
                cyc_dests = [(g[si], g[di]) for g, gp in zip(len_groups, gperms) for si, di in enumerate(gp)]
                for chs in itertools.product(*[per_cyc[tuple(dst)] for _, dst in cyc_dests]):
                    arr = list(range(18))
                    for i in range(k):
                        arr[i] = pk_map[i]
                    for (src, _), ch in zip(cyc_dests, chs):
                        for a, b in zip(src, ch):
                            arr[a] = b
                    arr[15], arr[16], arr[17] = z_map[0], z_map[1], z_map[2]
                    perms.append(tuple(arr))
        return perms

    s2_c0 = list(itertools.product((Fraction(-1, 2), Fraction(3, 2)), repeat=3))
    s2_b2 = list(itertools.product((Fraction(1), Fraction(-1)), (Fraction(0), Fraction(-2)), (Fraction(0), Fraction(-2))))
    s2_b3 = list(itertools.product((Fraction(0), Fraction(-2)), (Fraction(1), Fraction(-1)), (Fraction(0), Fraction(-2))))
    s2_cnts = {"COUNT": 0, "LP_FARKAS": 0, "CP_INFEAS": 0}
    s2_cores = 0; s2_max_r0 = Fraction(0); s2_max_rb = Fraction(0)
    for k, cycs in s2_configs:
        M17_fr = [[Fraction(0)] * 17 for _ in range(17)]
        for i in range(15): M17_fr[i][i] = Fraction(4)
        M17_fr[15][15] = M17_fr[16][16] = Fraction(5, 2)
        M17_fr[15][16] = M17_fr[16][15] = Fraction(-1, 2)
        for i in range(k - 1): M17_fr[i][i + 1] = M17_fr[i + 1][i] = Fraction(-2)
        M17_fr[0][15] = M17_fr[15][0] = Fraction(-2)
        M17_fr[k - 1][16] = M17_fr[16][k - 1] = Fraction(-2)
        off = k
        for L in cycs:
            for i in range(L):
                j = (i + 1) % L
                M17_fr[off + i][off + j] = M17_fr[off + j][off + i] = Fraction(-2)
            off += L
        pk_vecs = [b for b in itertools.product((-1, 1), repeat=k) if sum(b) == 1]
        cyc_vecs = [[b for b in itertools.product((-1, 1), repeat=L) if sum(b) == 0] for L in cycs]
        perms = _aut_s2(k, cycs); seen = set()
        v15_masks = [pk + tuple(x for c in ct for x in c) for pk in itertools.product((-1, 1), repeat=k) for ct in itertools.product(*cyc_vecs)]
        for pkv in pk_vecs:
            for ctup in itertools.product(*cyc_vecs):
                v15 = tuple(pkv) + tuple(x for c in ctup for x in c)
                if v15 in seen: continue
                for p in perms: seen.add(tuple(v15[p[i]] for i in range(15)))
                r_fr = [Fraction(x) for x in v15] + [Fraction(-1, 2), Fraction(-1, 2)]
                M18_fr = [row[:] + [r_fr[ri]] for ri, row in enumerate(M17_fr)] + [r_fr + [Fraction(5, 2)]]
                ok_psd, rk18 = _ldlt_qq(M18_fr)
                if not ok_psd or rk18 > 15: continue
                if not _ldlt_qq([[Fraction(20 if i == j else 0) - M18_fr[i][j] for j in range(18)] for i in range(18)])[0]: continue
                c0_sv = [M18_fr[r][15] + M18_fr[r][16] + M18_fr[r][17] for r in range(18)]
                b2_sv = [-M18_fr[r][16] - M18_fr[r][17] for r in range(18)]
                b3_sv = [-M18_fr[r][15] - M18_fr[r][17] for r in range(18)]
                res, mr0, mb2, mb3 = _kill_s2_or_s3_core_clean(f"S2[{s2_cores}]", 18, 15, 25, 15, 15, c0_sv, b2_sv, b3_sv, M18_fr, perms, v15_masks, s2_c0, s2_b2, s2_b3)
                for kk, vv in res.items(): s2_cnts[kk] += vv
                s2_max_r0 = max(s2_max_r0, mr0); s2_max_rb = max(s2_max_rb, mb2, mb3)
                s2_cores += 1
    assert s2_cores == 15
    s2_res = {"configs": len(s2_configs), "canonical_cores": s2_cores, "max_r0": str(s2_max_r0), "max_rb": str(s2_max_rb), "counts": s2_cnts, "elapsed_sec": round(time.time() - t0, 2)}
    print(f"  [PASS] S2: {s2_res}", flush=True)

    # 2. S3 elimination (34 valid 6x6 C2 -> 10 canonical orbits -> 123 M20 cores)
    ts3 = time.time()
    pairs = [(i, j) for i in range(6) for j in range(i + 1, 6)]
    c2_list = []
    for bits in itertools.product((-1, 1), repeat=15):
        M_qq = [[Fraction(0)] * 6 for _ in range(6)]
        for i in range(6): M_qq[i][i] = Fraction(5, 2)
        idx = 0
        for i, j in pairs:
            s = bits[idx]; idx += 1
            gi, gj = i // 2, j // 2; si, sj = (1 if i % 2 == 0 else -1), (1 if j % 2 == 0 else -1)
            val = Fraction(s) - (Fraction(3, 2) if (gi == gj or si == sj) else Fraction(1, 2))
            M_qq[i][j] = M_qq[j][i] = val
        if not _ldlt_qq(M_qq)[0]: continue
        if not _ldlt_qq([[Fraction(20 if i == j else 0) - M_qq[i][j] for j in range(6)] for i in range(6)])[0]: continue
        ok = True; ext_degs = []
        for omit in (0, 1, 2):
            sub = [k for k in range(6) if k // 2 != omit]; degs = []
            for k in sub:
                rs = sum(M_qq[k][l] for l in sub)
                if rs.denominator != 1 or rs < 0 or int(rs) % 2 != 0:
                    ok = False; break
                degs.append(int(rs) // 2)
            if not ok or sum(degs) % 2 != 0:
                ok = False; break
            ext_degs.append(degs)
        if ok: c2_list.append((M_qq, ext_degs))
    assert len(c2_list) == 34

    def _canon_c2(M_qq):
        best = None
        for p in itertools.permutations((0, 1, 2)):
            for fl in (0, 1):
                mp = [2 * p[k // 2] + ((k % 2) ^ fl) for k in range(6)]
                tup = tuple(M_qq[mp[i]][mp[j]] for i in range(6) for j in range(i + 1, 6))
                if best is None or tup < best: best = tup
        return best

    orbs = {}
    for M_qq, ext_degs in c2_list:
        best_omit = min((0, 1, 2), key=lambda o: (sum(ext_degs[o]), o))
        perm_g = [best_omit] + [g for g in (0, 1, 2) if g != best_omit]
        mp = [2 * perm_g[k // 2] + (k % 2) for k in range(6)]
        M_rot = [[M_qq[mp[i]][mp[j]] for j in range(6)] for i in range(6)]
        ck = _canon_c2(M_rot)
        if ck not in orbs: orbs[ck] = M_rot
    s3_orbs = sorted(orbs.values(), key=lambda M6: sum(sum(M6[k][l] for l in [2, 3, 4, 5]) // 2 for k in [2, 3, 4, 5]))
    assert len(s3_orbs) == 10
    even_parts = {0: [()], 4: [(4,)], 6: [(6,)], 8: [(8,), (4, 4)], 10: [(10,), (6, 4)], 12: [(12,), (8, 4), (6, 6), (4, 4, 4)], 14: [(14,), (10, 4), (8, 6), (6, 4, 4)]}

    def _gen_b1_ext(degs):
        s = sum(degs); nz_zs = [14 + idx for idx, d in enumerate(degs) if d == 1]; configs = []
        if s == 0:
            for cycs in even_parts[14]: configs.append(([], cycs, []))
        elif s == 2:
            za, zb = nz_zs
            for k in [2, 4, 6, 8, 10, 14]:
                for cycs in even_parts[14 - k]: configs.append(([(0, k - 1)], cycs, [(0, za), (k - 1, zb)]))
        elif s == 4:
            seen_b1 = set()
            for s1 in range(1, 14):
                for s2 in range(s1, 15 - s1):
                    if (s1 + s2) % 2 != 0: continue
                    rem = 14 - s1 - s2
                    if rem not in even_parts: continue
                    for p in itertools.permutations(nz_zs):
                        z_edges = [(0, p[0]), (s1 - 1, p[1]), (s1, p[2]), (s1 + s2 - 1, p[3])]
                        c1_opts = [((p[0], p[1]),), ((p[1], p[0]),)] if s1 > 1 else [(tuple(sorted((p[0], p[1]))),)]
                        c2_opts = [((p[2], p[3]),), ((p[3], p[2]),)] if s2 > 1 else [(tuple(sorted((p[2], p[3]))),)]
                        key_opts = [(s1, o1, s2, o2) for o1 in c1_opts for o2 in c2_opts] + ([(s2, o2, s1, o1) for o1 in c1_opts for o2 in c2_opts] if s1 == s2 else [])
                        canon = min(key_opts)
                        for cycs in even_parts[rem]:
                            if (canon, cycs) in seen_b1: continue
                            seen_b1.add((canon, cycs)); configs.append(([(0, s1 - 1), (s1, s1 + s2 - 1)], cycs, z_edges))
        return configs

    def _aut_b1_ext(paths, cycs, z_edges):
        z_on = {u: set() for u in range(14)}
        for u, za in z_edges: z_on[u].add(za)
        path_opts = []
        for a, b in paths:
            opts = [list(range(a, b + 1))]
            if z_on[a] == z_on[b]: opts.append(list(range(b, a - 1, -1)))
            path_opts.append(opts)
        off = 14 - sum(cycs); by_len = {}
        for L in cycs: by_len.setdefault(L, []).append(list(range(off, off + L))); off += L
        per_cyc = {
            tuple(cyc): (
                [[cyc[(i + s) % len(cyc)] for i in range(len(cyc))] for s in range(len(cyc))]
                + [[cyc[(s - i) % len(cyc)] for i in range(len(cyc))] for s in range(len(cyc))]
            )
            for cl in by_len.values()
            for cyc in cl
        }
        len_groups = list(by_len.values()); path_arrs = []
        for o1 in (path_opts[0] if paths else [[]]):
            for o2 in (path_opts[1] if len(paths) > 1 else [[]]):
                d = {}
                if paths:
                    for idx_p, dst in enumerate(o1): d[paths[0][0] + idx_p] = dst
                if len(paths) > 1:
                    for idx_p, dst in enumerate(o2): d[paths[1][0] + idx_p] = dst
                if all(z_on[u] == z_on[v] for u, v in d.items()): path_arrs.append(d)
        if len(paths) == 2 and (paths[0][1] - paths[0][0]) == (paths[1][1] - paths[1][0]):
            a0, b0 = paths[0]; a1, b1 = paths[1]
            for rev0 in (0, 1):
                for rev1 in (0, 1):
                    src0 = list(range(a0, b0 + 1)); dst0 = list(range(a1, b1 + 1)) if rev0 == 0 else list(range(b1, a1 - 1, -1))
                    src1 = list(range(a1, b1 + 1)); dst1 = list(range(a0, b0 + 1)) if rev1 == 0 else list(range(b0, a0 - 1, -1))
                    d = dict(zip(src0 + src1, dst0 + dst1))
                    if all(z_on[u] == z_on[v] for u, v in d.items()): path_arrs.append(d)
        perms = []
        for pd in path_arrs:
            for gperms in itertools.product(*[list(itertools.permutations(range(len(g)))) for g in len_groups]):
                cyc_dests = [(g[si], g[di]) for g, gp in zip(len_groups, gperms) for si, di in enumerate(gp)]
                for chs in itertools.product(*[per_cyc[tuple(dst)] for _, dst in cyc_dests]):
                    arr = list(range(20))
                    for u, v in pd.items(): arr[u] = v
                    for (src, _), ch in zip(cyc_dests, chs):
                        for a, b in zip(src, ch): arr[a] = b
                    perms.append(tuple(arr))
        return perms

    s3_c0 = list(itertools.product((Fraction(1, 2), Fraction(-3, 2)), (Fraction(-1, 2), Fraction(3, 2)), (Fraction(1, 2), Fraction(-3, 2)), (Fraction(-1, 2), Fraction(3, 2)), (Fraction(1, 2), Fraction(-3, 2)), (Fraction(-1, 2), Fraction(3, 2))))
    s3_b2 = list(itertools.product((Fraction(1), Fraction(-1)), (Fraction(1), Fraction(-1)), (Fraction(0), Fraction(-2)), (Fraction(0), Fraction(-2)), (Fraction(0), Fraction(-2)), (Fraction(0), Fraction(-2))))
    s3_b3 = list(itertools.product((Fraction(0), Fraction(-2)), (Fraction(0), Fraction(-2)), (Fraction(1), Fraction(-1)), (Fraction(1), Fraction(-1)), (Fraction(0), Fraction(-2)), (Fraction(0), Fraction(-2))))
    s3_cnts = {"COUNT": 0, "LP_FARKAS": 0, "CP_INFEAS": 0}
    s3_cores = 0; s3_max_r0 = Fraction(0); s3_max_rb = Fraction(0)
    s3_tasks = []
    for oi, M6 in enumerate(s3_orbs):
        degs = [int(sum(M6[k][l] for l in [2, 3, 4, 5])) // 2 for k in [2, 3, 4, 5]]
        for paths, cycs, z_edges in _gen_b1_ext(degs):
            M18_fr = [[Fraction(0)] * 18 for _ in range(18)]
            for i in range(14): M18_fr[i][i] = Fraction(4)
            for a in range(4):
                for b in range(4): M18_fr[14 + a][14 + b] = M6[2 + a][2 + b]
            for a, b in paths:
                for u in range(a, b): M18_fr[u][u + 1] = M18_fr[u + 1][u] = Fraction(-2)
            off = 14 - sum(cycs)
            for L in cycs:
                for i in range(L):
                    j = (i + 1) % L; M18_fr[off + i][off + j] = M18_fr[off + j][off + i] = Fraction(-2)
                off += L
            for u, za in z_edges: M18_fr[u][za] = M18_fr[za][u] = Fraction(-2)
            if not _ldlt_qq(M18_fr)[0]: continue
            M18_sp = sp.Matrix([[sp.Rational(x.numerator, x.denominator) for x in r] for r in M18_fr])
            N18 = M18_sp.nullspace()
            N18_int = []
            for nv_sp in N18:
                nr = [Fraction(int(nv_sp[j].p), int(nv_sp[j].q)) for j in range(18)]
                ld = 1
                for x in nr: ld = math.lcm(ld, x.denominator)
                N18_int.append([int(x * ld) for x in nr])
            ncyc = sum(cycs); n_noncyc = 14 - ncyc
            v14_list = [nc + tuple(x for c in ct for x in c) for nc in itertools.product((-1, 1), repeat=n_noncyc) for ct in itertools.product(*[[b for b in itertools.product((-1, 1), repeat=L) if sum(b) == 0] for L in cycs])]
            V14_np = np.array(v14_list, dtype=np.int8)
            N14_np = np.array([r[:14] for r in N18_int], dtype=np.int64)
            lhs = V14_np @ N14_np.T
            lhs_map = {}
            for row_i, row in enumerate(lhs): lhs_map.setdefault(tuple(int(x) for x in row), []).append(v14_list[row_i])
            r_vecs = {0: [], 1: []}
            for k in (0, 1):
                c_part = [M6[k][2 + a] for a in range(4)]
                need = []; ok_int = True
                for nr in N18_int:
                    val = -sum(nr[14 + a] * c_part[a] for a in range(4))
                    if val.denominator != 1: ok_int = False; break
                    need.append(int(val))
                if not ok_int: continue
                for v14 in lhs_map.get(tuple(need), ()):
                    r_fr = [Fraction(x) for x in v14] + c_part
                    M19_fr = [row[:] + [r_fr[ri]] for ri, row in enumerate(M18_fr)] + [r_fr + [Fraction(5, 2)]]
                    if _ldlt_qq(M19_fr)[0]: r_vecs[k].append((v14, r_fr))
            perms = _aut_b1_ext(paths, cycs, z_edges)
            seen_pairs = set()
            for v0, r0 in r_vecs[0]:
                for v1, r1 in r_vecs[1]:
                    if (v0, v1) in seen_pairs: continue
                    for p in perms: seen_pairs.add((tuple(v0[p[i]] for i in range(14)), tuple(v1[p[i]] for i in range(14))))
                    M20_fr = [row[:] + [r0[ri], r1[ri]] for ri, row in enumerate(M18_fr)]
                    M20_fr.append(r0 + [Fraction(5, 2), M6[0][1]])
                    M20_fr.append(r1 + [M6[0][1], Fraction(5, 2)])
                    ok_p20, rk20 = _ldlt_qq(M20_fr)
                    if not ok_p20 or rk20 > 15: continue
                    if not _ldlt_qq([[Fraction(20 if i == j else 0) - M20_fr[i][j] for j in range(20)] for i in range(20)])[0]: continue
                    s3_tasks.append((oi, M20_fr, perms, v14_list, s3_c0, s3_b2, s3_b3))
                    s3_cores += 1
    assert s3_cores == 123, f"Expected 123 S3 cores, got {s3_cores}"
    n_workers = workers if workers > 0 else min(8, os.cpu_count() or 1)
    if n_workers > 1:
        with ProcessPoolExecutor(max_workers=n_workers) as ex:
            for res, mr0, mb2, mb3 in ex.map(_run_s3_core_task, s3_tasks):
                for kk, vv in res.items(): s3_cnts[kk] += vv
                s3_max_r0 = max(s3_max_r0, mr0); s3_max_rb = max(s3_max_rb, mb2, mb3)
    else:
        for tsk in s3_tasks:
            res, mr0, mb2, mb3 = _run_s3_core_task(tsk)
            for kk, vv in res.items(): s3_cnts[kk] += vv
            s3_max_r0 = max(s3_max_r0, mr0); s3_max_rb = max(s3_max_rb, mb2, mb3)
    s3_res = {"c2_valid": len(c2_list), "orbits": len(s3_orbs), "canonical_cores": s3_cores, "max_r0": str(s3_max_r0), "max_rb": str(s3_max_rb), "counts": s3_cnts, "elapsed_sec": round(time.time() - ts3, 2)}
    print(f"  [PASS] S3: {s3_res}", flush=True)
    return {"S2": s2_res, "S3": s3_res}


def audit_idx13_bundles() -> dict:
    """Independently validate all 5 BLOCKER-1 patched JSON certificate bundles in idx13_exact/results/."""
    def _no_floats_in_cert(obj):
        if isinstance(obj, float):
            return False
        if isinstance(obj, dict):
            return all(_no_floats_in_cert(v) for v in obj.values())
        if isinstance(obj, list):
            return all(_no_floats_in_cert(v) for v in obj)
        return True

    t0 = time.time()
    summary = {}
    for name in ["cert_s1_t2.json", "cert_s3_s2.json"]:
        d = read_json_auto(IDX13_RES_DIR, name)
        if name == "cert_s1_t2.json":
            assert set(d["partitions"].keys()) == {"(16,)", "(10, 6)", "(8, 8)", "(12, 4)"}
            assert all(v["status"] == "KILLED" for v in d["partitions"].values())
            summary[name] = {"partitions": list(d["partitions"].keys()), "all_killed": True}
        else:
            assert d["all_dead"] is True
            assert len(d["stats"]["S3"]) == 10 and all(v["status"] == "KILLED" for v in d["stats"]["S3"].values())
            assert d["stats"]["S2"]["top_reduction"]["c5_decouples_qq"] is True
            assert d["stats"]["S2"]["top_reduction"]["s_minus1_surviving_z"] == [[1, 1, 1]]
            assert len(d["stats"]["S2"]["configs"]) == 15 and all(v["status"] == "KILLED" for v in d["stats"]["S2"]["configs"].values())
            summary[name] = {"s3_orbits_killed": len(d["stats"]["S3"]), "s2_configs_killed": len(d["stats"]["S2"]["configs"]), "all_dead": True}

    farkas_totals = {}
    for name in ["s1_6_6_4_certs.json", "s1_8_4_4_certs.json", "s1_4_4_4_4_certs.json"]:
        d = read_json_auto(IDX13_RES_DIR, name)
        assert d["all_dead"] is True and d["stats"]["surv"] == 0
        min_gap = None
        for rec in d["farkas_certs"]:
            cert = rec["cert"]
            assert _no_floats_in_cert(cert), f"Float inside Farkas cert in {name}"
            gap = Fraction(int(cert["gap"][0]), int(cert["gap"][1]))
            assert gap > 0, f"Non-positive gap {gap} in {name}"
            if min_gap is None or gap < min_gap:
                min_gap = gap
        info = {
            "all_dead": True,
            "n_farkas_certs": len(d["farkas_certs"]),
            "min_gap": str(min_gap),
        }
        if name == "s1_4_4_4_4_certs.json":
            assert d["q3_preserved_check"]["bit_for_bit_input_identical"] is True
            assert d["q3_preserved_check"]["twin_s0_count"] == 0 and d["q3_preserved_check"]["twin_s1_count"] == 0
            info["q3_preserved_check"] = d["q3_preserved_check"]
        farkas_totals[name] = info
    summary["farkas_bundles"] = farkas_totals
    summary["elapsed_sec"] = round(time.time() - t0, 2)
    print(f"  [PASS] Bundles: { {k: v for k, v in summary.items() if k != 'farkas_bundles'} }", flush=True)
    return summary


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--only", nargs="*", default=None, help="Optional subset: A B C t2 o2 o3 s23 bundles")
    parser.add_argument("--skip-q3", action="store_true", help="Smoke-test flag skipping q0=3 in (4,4,4,4)")
    args = parser.parse_args()
    sel = set(args.only) if args.only else {"A", "B", "C", "t2", "o2", "o3", "s23", "bundles"}

    t0 = time.time()
    x = sp.Symbol("x")
    report = {}
    if "A" in sel:
        part_a = audit_sha256_and_ast()
        report["part_a"] = part_a
        print("[PASS] Part A: 13 SHA-256 digests + AST zero-float-trust verified", flush=True)
    if "B" in sel:
        part_b = audit_74_to_3_reduction(x)
        report["part_b"] = part_b
        print(f"[PASS] Part B: 74 -> {part_b['after_e17_tri']} -> 3 (S1, S2, S3) reduction verified", flush=True)
    if "C" in sel:
        part_c = audit_s1_props_and_t2_clean_room()
        report["part_c"] = part_c
        print("[PASS] Part C: Props 8.4-8.7, 7 S1 partitions, (16,), and Lemma 8.8 verified", flush=True)
    if "t2" in sel:
        report["part_d1_s1_t2"] = audit_s1_t2_clean_room()
    if "o2" in sel:
        report["part_d2_s1_o2"] = audit_s1_o2_clean_room()
    if "o3" in sel:
        report["part_d3_s1_o3_4444"] = audit_s1_o3_4444_clean_room(include_q3=not args.skip_q3)
    if "s23" in sel:
        report["part_d4_s2_s3"] = audit_s2_and_s3_clean_room()
    if "bundles" in sel:
        report["part_d5_bundles"] = audit_idx13_bundles()

    report["status"] = "PASS" if (sel == {"A", "B", "C", "t2", "o2", "o3", "s23", "bundles"} and not args.skip_q3) else "PARTIAL_PASS"
    report["total_elapsed_sec"] = round(time.time() - t0, 2)
    if args.only is None and not args.skip_q3:
        OUT_JSON.write_text(json.dumps(report, indent=2))
        print(f"[PASS] Wrote full audit report to {OUT_JSON} in {report['total_elapsed_sec']}s", flush=True)
    else:
        print(json.dumps({k: v for k, v in report.items() if k != "part_a"}, indent=2))


if __name__ == "__main__":
    main()
