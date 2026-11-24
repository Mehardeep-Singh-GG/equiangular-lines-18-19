"""
Independent integer-exact verifier for all Phase-3 (19,74) and (18,59) certificates in compute/poly/results/.
Checks:
  1. Zero occurrences of banned legacy polynomial-signature / tight-bound helpers in compute/poly/.
  2. Exact Stage-3 Farkas duals (c_farkas^T col >= 0 and c_farkas^T rhs < 0) on (19,74) {47, 6, 24} and (18,59) candidates.
  3. Exact Coupled Stage-2+3 Farkas duals (c_farkas^T col >= 0 and c_farkas^T rhs < 0) on {103, 800, 1113, 1164, 705 cones 3-4}.
  4. Completeness of all 19 (18,59) candidates.
"""

import hashlib
import json
import math
from pathlib import Path
from fractions import Fraction
import sys
import sympy as sp

_COMP_DIR = Path(__file__).resolve().parent.parent
if str(_COMP_DIR) not in sys.path:
    sys.path.insert(0, str(_COMP_DIR))
from _io import POLY_DIR as _POLY_DIR, POLY_RESULTS_DIR, load_json_auto

from run_stage3_18_59 import (
    bucket_indices_exact,
    galois_rows_for_bucket,
    is_square_in_field_exact,
    is_square_quad_exact,
    norm_in_field_qq,
    prop61_sol_ok,
    sqfree_rat,
)
from stage3_solver import _poly_coeffs_fixed_len, solve_2v_jacobi_pair, strict_upper_bound_roots, check_stage3_for_counts
from phase2_even import find_exact_farkas_rational, passes_t42_sub


def fast_exact_farkas(cols_int, rhs_int):
    """Exact Farkas check via HiGHS dual hint strictly verified in int arithmetic + Fraction fallback."""
    import numpy as np
    from scipy.optimize import linprog
    m = len(cols_int)
    s = len(rhs_int)
    if m > 0:
        res = linprog(np.array(rhs_int, dtype=np.float64), A_ub=-np.array(cols_int, dtype=np.float64),
                      b_ub=np.zeros(m), bounds=[(-1.0, 1.0)] * s, method="highs")
        if res.success and res.fun < -1e-7:
            for scale in [10**6, 10**9, 10**12]:
                c_int = [int(round(v * scale)) for v in res.x]
                if verify_farkas_int(cols_int, rhs_int, c_int):
                    return True, c_int
    return find_exact_farkas_rational(cols_int, rhs_int)


RESULTS_DIR = POLY_RESULTS_DIR
POLY_DIR = _POLY_DIR


def verify_farkas_int(cols_int, rhs_int, c_int):
    s = len(rhs_int)
    if len(c_int) != s:
        return False
    if sum(int(c_int[r]) * int(rhs_int[r]) for r in range(s)) >= 0:
        return False
    for col in cols_int:
        if sum(int(c_int[r]) * int(col[r]) for r in range(s)) < 0:
            return False
    return True


def build_cand_context(cand, n, d_dim, c_sh, is_19_74=False):
    w, x, z = sp.symbols("w x z")
    s = cand["s"]
    deck = [[int(v) for v in row] for row in cand["deck"]]
    Pw = sp.Poly(sum(cand["b"][j] * w ** (d_dim - j) for j in range(d_dim + 1)), w, domain=sp.ZZ)
    w0 = (-5 - c_sh) // 2
    Full_w = sp.Poly((w - w0) ** (n - d_dim), w, domain=sp.ZZ) * Pw
    Dw = sp.gcd(Full_w, Full_w.diff())
    if Dw.LC() < 0: Dw = -Dw
    quo, _ = sp.div(Full_w.diff(), Dw)
    rhs = [int(v) // 2 for v in quo.all_coeffs()]
    while len(rhs) < s: rhs = [0] + rhs
    chi_scale = (2 ** n) if is_19_74 else (2 ** (n - 1))
    g_scale = (2 ** (s - 2)) if is_19_74 else (2 ** (s - 1))
    if is_19_74:
        s_sh = (c_sh + 1) // 2
        deck = [row for row in deck if passes_t42_sub(Dw, sp.Poly(row, w, domain=sp.ZZ), n - 1, s_sh, z, w)]
    chi_S = sp.Poly(sp.expand(chi_scale * Full_w.as_expr().subs(w, (x - c_sh) / 2)), x, domain=sp.ZZ)
    Gcd_x = sp.gcd(chi_S, chi_S.diff())
    if Gcd_x.LC() < 0: Gcd_x = -Gcd_x
    Gcd2_x = sp.gcd(Gcd_x, Gcd_x.diff())
    if Gcd2_x.LC() < 0: Gcd2_x = -Gcd2_x
    facs_x = sp.factor_list(chi_S.as_expr())[1]
    Sim_x = sp.Poly(1, x, domain=sp.ZZ)
    Mult_rad_x = sp.Poly(1, x, domain=sp.ZZ)
    for fac, mult in facs_x:
        fp = sp.Poly(fac, x, domain=sp.ZZ)
        if mult == 1: Sim_x = Sim_x * fp
        else: Mult_rad_x = Mult_rad_x * fp
    g_list = [
        sp.Poly(sp.expand(g_scale * sum(row[k] * w ** (s - 1 - k) for k in range(s)).subs(w, (x - c_sh) / 2)), x, domain=sp.ZZ)
        for row in deck
    ]
    return w, x, s, deck, Pw, rhs, chi_S, Gcd_x, Gcd2_x, Sim_x, Mult_rad_x, g_list


def verify_stage3_cert_list(cand, n, d_dim, c_sh, certs, label="", is_19_74=False):
    if not certs:
        return 0
    w, x, s, deck, Pw, rhs, chi_S, Gcd_x, Gcd2_x, Sim_x, Mult_rad_x, g_list = build_cand_context(cand, n, d_dim, c_sh, is_19_74=is_19_74)
    deg_q = (n - 2) - Gcd2_x.degree()
    x_max_ub = strict_upper_bound_roots(chi_S, x)
    Q_cache = {}
    def get_q(a, b):
        kp = (a, b) if a <= b else (b, a)
        if kp not in Q_cache:
            res = solve_2v_jacobi_pair(g_list[kp[0]], g_list[kp[1]], Sim_x, Mult_rad_x, Gcd2_x, n, x, x_max_ub=x_max_ub)
            uniq = {}
            for s2v, q_uv, _ in res:
                key = tuple(int(v) for v in q_uv.all_coeffs())
                if key not in uniq: uniq[key] = _poly_coeffs_fixed_len(q_uv, deg_q + 1)
            Q_cache[kp] = list(uniq.values())
            Q_cache[(kp[1], kp[0])] = Q_cache[kp]
        return Q_cache[(a, b)]

    rhs_v_cache = {}
    verified = 0
    for cert in certs:
        v = cert["v_type"]
        cnts = cert["counts_n"]
        act_ids = [j for j, c in enumerate(cnts) if c > 0]
        if v not in rhs_v_cache:
            chi_Sv = Gcd_x * g_list[v]
            rhs_p, _ = sp.div(chi_Sv.diff(), Gcd2_x)
            rhs_v_cache[v] = _poly_coeffs_fixed_len(rhs_p, deg_q + 1)
        rhs_aug = list(rhs_v_cache[v])
        cols_int = []
        br = []
        empty_pair = False
        for b in act_ids:
            nb_rem = cnts[b] - (1 if b == v else 0)
            if nb_rem <= 0: continue
            sc = len(cols_int)
            q_items = get_q(v, b)
            if not q_items:
                empty_pair = True
            cols_int.extend(q_items)
            br.append((sc, len(cols_int), nb_rem))
        if "c_farkas" not in cert:
            if cert.get("method") == "stage3_exact_rref_no_int":
                killed_rref, _ = check_stage3_for_counts(chi_S, Gcd_x, Gcd2_x, Sim_x, Mult_rad_x, g_list, cnts, n, x)
                assert killed_rref, f"RREF cert failed on {label} v={v}"
            elif not empty_pair and cols_int:
                cols_aug = [list(c) for c in cols_int]
                for sc, ec, nb_rem in br:
                    for ci in range(len(cols_aug)):
                        cols_aug[ci].append(1 if sc <= ci < ec else 0)
                    rhs_aug.append(nb_rem)
                inf, _ = find_exact_farkas_rational(cols_aug, rhs_aug)
                assert inf, f"Non-farkas cert failed exact check on {label} v={v}"
            verified += 1
            continue
        cols_aug = [list(c) for c in cols_int]
        for sc, ec, nb_rem in br:
            for ci in range(len(cols_aug)):
                cols_aug[ci].append(1 if sc <= ci < ec else 0)
            rhs_aug.append(nb_rem)
        assert verify_farkas_int(cols_aug, rhs_aug, cert["c_farkas"]), f"Farkas fail on {label} v={v}"
        verified += 1
    return verified


def verify_sv_galois_cert_list(cand, n, d_dim, c_sh, certs, label=""):
    if not certs:
        return 0
    w, x, s, deck, Pw, rhs, chi_S, Gcd_x, Gcd2_x, Sim_x, Mult_rad_x, g_list = build_cand_context(cand, n, d_dim, c_sh)
    deg_q = (n - 2) - Gcd2_x.degree()
    x_max_ub = strict_upper_bound_roots(chi_S, x)
    Q_cache = {}
    def get_q_items(a, b):
        kp = (a, b) if a <= b else (b, a)
        if kp not in Q_cache:
            res = solve_2v_jacobi_pair(g_list[kp[0]], g_list[kp[1]], Sim_x, Mult_rad_x, Gcd2_x, n, x, x_max_ub=x_max_ub)
            uniq = {}
            for s2v, q_uv, _ in res:
                key = tuple(int(v) for v in q_uv.all_coeffs())
                if key not in uniq:
                    uniq[key] = {"q_poly": q_uv, "cs": _poly_coeffs_fixed_len(q_uv, deg_q + 1)}
            Q_cache[kp] = list(uniq.values())
            Q_cache[(kp[1], kp[0])] = Q_cache[kp]
        return Q_cache[(a, b)]

    v_cache = {}
    sq_cache = {}
    gal_cache = {}
    verified = 0
    for cert in certs:
        v = cert["v_type"]
        cnts = cert["counts_n"]
        act_ids = [j for j, c in enumerate(cnts) if c > 0]
        if v not in v_cache:
            chi_Sv = Gcd_x * g_list[v]
            Gv = sp.gcd(chi_Sv, chi_Sv.diff())
            if Gv.LC() < 0: Gv = -Gv
            sim_v = sorted([sp.Poly(f, x, domain=sp.ZZ) for f, m in sp.factor_list(chi_Sv.as_expr())[1] if m == 1], key=lambda p: p.degree())
            rhs_p, _ = sp.div(chi_Sv.diff(), Gcd2_x)
            rhs_cs = _poly_coeffs_fixed_len(rhs_p, deg_q + 1)
            v_cache[v] = (Gv, sim_v, rhs_cs)
        Gv, sim_v, rhs_cs = v_cache[v]
        assert sim_v, f"Empty sim_v for {label} v={v}"
        col_q_cs, col_gv_keys, block_eqs = [], [], []
        for b in act_ids:
            nb_rem = cnts[b] - (1 if b == v else 0)
            if nb_rem <= 0: continue
            sc = len(col_q_cs)
            for item in get_q_items(v, b):
                col_q_cs.append(item["cs"])
                gv_map = item.setdefault("gv_map", {})
                if v not in gv_map:
                    gv_u, _ = sp.div(Gcd2_x * item["q_poly"], Gv)
                    gv_map[v] = tuple(int(c) for c in gv_u.all_coeffs())
                col_gv_keys.append(gv_map[v])
            block_eqs.append((sc, len(col_q_cs), nb_rem))
        base_rows = [[col_q_cs[c][r_i] for c in range(len(col_q_cs))] for r_i in range(deg_q + 1)]
        base_rhs = list(rhs_cs)
        for sc, ec, nb_rem in block_eqs:
            base_rows.append([1 if sc <= c < ec else 0 for c in range(len(col_q_cs))])
            base_rhs.append(nb_rem)
        cones_v = [(list(range(len(col_q_cs))), [])]
        for qf in sim_v:
            q_mon = sp.Poly(qf, x, domain=sp.QQ).monic()
            q_key = tuple(qf.all_coeffs())
            nxt_v = []
            for sub_v, ex_v in cones_v:
                zv, norm_groups = [], {}
                for j in sub_v:
                    gk = col_gv_keys[j]
                    if (q_key, gk, "sf") not in sq_cache:
                        pj = sp.Poly(gk, x, domain=sp.QQ)
                        rem = sp.rem(pj, q_mon)
                        if rem.is_zero:
                            sq_cache[(q_key, gk, "sf")] = (0, None)
                        else:
                            nv = norm_in_field_qq(rem, q_mon, x) if q_mon.degree() > 1 else Fraction(rem.eval(-q_mon.nth(0)).p, rem.eval(-q_mon.nth(0)).q)
                            sq_cache[(q_key, gk, "sf")] = (sqfree_rat(nv), rem)
                    sf, _ = sq_cache[(q_key, gk, "sf")]
                    if sf == 0: zv.append(j)
                    else: norm_groups.setdefault(sf, []).append(j)
                if q_mon.degree() == 1:
                    bvs = list(norm_groups.values())
                else:
                    bvs = []
                    for sf, grp in norm_groups.items():
                        sub_b = []
                        for j in grp:
                            placed = False
                            gk_j = col_gv_keys[j]
                            for b in sub_b:
                                gk_b = col_gv_keys[b[0]]
                                pk = (q_key, gk_j, gk_b) if gk_j <= gk_b else (q_key, gk_b, gk_j)
                                if pk not in sq_cache:
                                    rj = sq_cache[(q_key, gk_j, "sf")][1]
                                    rb = sq_cache[(q_key, gk_b, "sf")][1]
                                    if q_mon.degree() == 2:
                                        sq_cache[pk] = is_square_quad_exact(sp.rem(rj * rb, q_mon), q_mon)
                                    else:
                                        sq_cache[pk] = is_square_in_field_exact((rj * rb).as_expr(), q_mon, x)
                                if sq_cache[pk]:
                                    b.append(j); placed = True; break
                            if not placed:
                                sub_b.append([j])
                        bvs.extend(sub_b)
                cand_groups = [sorted(zv + b) for b in bvs] if bvs else ([sorted(zv)] if zv else [])
                for idx_g, act_v in enumerate(cand_groups):
                    nex_v = list(ex_v)
                    if q_mon.degree() >= 2 and bvs:
                        b_cur = bvs[idx_g]
                        gk_rep = col_gv_keys[b_cur[0]]
                        uniq_gks = sorted({col_gv_keys[j] for j in b_cur})
                        ri = uniq_gks.index(gk_rep)
                        uniq_gks[0], uniq_gks[ri] = uniq_gks[ri], uniq_gks[0]
                        b_key = (q_key, tuple(uniq_gks))
                        if b_key not in gal_cache:
                            max_l = max(len(g) for g in uniq_gks)
                            pad = [[0] * (max_l - len(g)) + list(g) for g in uniq_gks]
                            gd = galois_rows_for_bucket(pad, list(range(len(uniq_gks))), qf, x)
                            gal_cache[b_key] = {uniq_gks[iu]: gd[iu] for iu in range(len(uniq_gks))}
                        gmap = gal_cache[b_key]
                        b_set = set(b_cur)
                        for g_i in range(q_mon.degree() * (q_mon.degree() + 1) // 2):
                            nex_v.append(([gmap[col_gv_keys[j]][g_i] if j in b_set else Fraction(0) for j in range(len(col_q_cs))], Fraction(0)))
                    cols_T = [[base_rows[r][c] for r in range(len(base_rows))] for c in act_v]
                    rhs_all = list(base_rhs)
                    for row_f, rhs_f in nex_v:
                        lcm_d = rhs_f.denominator
                        for j in act_v: lcm_d = math.lcm(lcm_d, row_f[j].denominator)
                        for loc_j, glob_j in enumerate(act_v): cols_T[loc_j].append(int(row_f[glob_j] * lcm_d))
                        rhs_all.append(int(rhs_f * lcm_d))
                    inf2, _ = fast_exact_farkas(cols_T, rhs_all)
                    if not inf2:
                        nxt_v.append((act_v, nex_v))
            cones_v = nxt_v
        assert not cones_v, f"Sv Galois cert failed on {label} v={v}"
        verified += 1
    return verified


def build_stage2_cones(cand, n, d_dim, c_sh):
    w, x, s, deck, Pw, rhs, *_ = build_cand_context(cand, n, d_dim, c_sh)
    simple_facs = sorted([sp.Poly(f, w, domain=sp.ZZ) for f, m in sp.factor_list(Pw.as_expr())[1] if m == 1], key=lambda p: p.degree())
    cones = [(list(range(len(deck))), [])]
    for q in simple_facs:
        nxt = []
        for sub, ex in cones:
            zeros, buckets = bucket_indices_exact(deck, sub, q, w)
            for b in buckets:
                act = sorted(zeros + b)
                nex = list(ex)
                if q.degree() >= 2:
                    gal = galois_rows_for_bucket(deck, b, q, w)
                    for g_i in range(q.degree() * (q.degree() + 1) // 2):
                        nex.append(([gal[j][g_i] if j in gal else Fraction(0) for j in range(len(deck))], Fraction(0)))
                cols_T = [list(deck[j]) for j in act]
                rhs_all = list(rhs)
                for row_f, rhs_f in nex:
                    lcm_d = rhs_f.denominator
                    for j in act: lcm_d = math.lcm(lcm_d, row_f[j].denominator)
                    for lj, gj in enumerate(act): cols_T[lj].append(int(row_f[gj] * lcm_d))
                    rhs_all.append(int(rhs_f * lcm_d))
                inf, _ = find_exact_farkas_rational(cols_T, rhs_all)
                if not inf:
                    nxt.append((act, nex))
        cones = nxt
    return cones


def verify_coupled_certs(cand, n, d_dim, c_sh, cones, coupled_certs, label=""):
    if not coupled_certs:
        return 0
    w, x, s, deck, Pw, rhs, chi_S, Gcd_x, Gcd2_x, Sim_x, Mult_rad_x, g_list = build_cand_context(cand, n, d_dim, c_sh)
    deg_q = (n - 2) - Gcd2_x.degree()
    x_max_ub = strict_upper_bound_roots(chi_S, x)
    Q_cache = {}
    def get_q(a, b):
        kp = (a, b) if a <= b else (b, a)
        if kp not in Q_cache:
            res = solve_2v_jacobi_pair(g_list[kp[0]], g_list[kp[1]], Sim_x, Mult_rad_x, Gcd2_x, n, x, x_max_ub=x_max_ub)
            uniq = {}
            for s2v, q_uv, _ in res:
                key = tuple(int(v) for v in q_uv.all_coeffs())
                if key not in uniq: uniq[key] = _poly_coeffs_fixed_len(q_uv, deg_q + 1)
            Q_cache[kp] = list(uniq.values())
            Q_cache[(kp[1], kp[0])] = Q_cache[kp]
        return Q_cache[(a, b)]

    def check_with_extra(v, cur_act, y_c, extra_rows):
        m_c = len(cur_act)
        v_loc = cur_act.index(v)
        cols_m = []
        for loc_b, b in enumerate(cur_act):
            cols_m.append(list(deck[b]) + [rf[b] for rf, _ in extra_rows] + [0] * (deg_q + 1) + [(-1 if k == loc_b else 0) for k in range(m_c)])
        for loc_b, b in enumerate(cur_act):
            for q_cs in get_q(v, b):
                cols_m.append([0] * (s + len(extra_rows)) + q_cs + [(1 if k == loc_b else 0) for k in range(m_c)])
        chi_Sv = Gcd_x * g_list[v]
        rhs_p, _ = sp.div(chi_Sv.diff(), Gcd2_x)
        rhs_q = _poly_coeffs_fixed_len(rhs_p, deg_q + 1)
        rhs_tot = [Fraction(vr) for vr in rhs] + [rf for _, rf in extra_rows] + [Fraction(vq) for vq in rhs_q] + [Fraction(-1 if k == v_loc else 0) for k in range(m_c)]
        rhs_sh = [rhs_tot[r] - Fraction(cols_m[v_loc][r]) for r in range(len(rhs_tot))]
        cols_int = [[] for _ in range(len(cols_m))]
        rhs_int = []
        for r in range(len(rhs_tot)):
            lcm_d = rhs_sh[r].denominator
            for cj in range(len(cols_m)): lcm_d = math.lcm(lcm_d, Fraction(cols_m[cj][r]).denominator)
            for cj in range(len(cols_m)): cols_int[cj].append(int(Fraction(cols_m[cj][r]) * lcm_d))
            rhs_int.append(int(rhs_sh[r] * lcm_d))
        return verify_farkas_int(cols_int, rhs_int, y_c)

    verified = 0
    for cc in coupled_certs:
        v = cc["v_pruned"]
        cur_act = cc["cur_act"]
        y_c = cc["c_farkas"]
        matched = [ex for act, ex in cones if set(cur_act).issubset(set(act))]
        assert matched and any(check_with_extra(v, cur_act, y_c, ex) for ex in matched), f"Coupled Farkas fail on {label} v={v}"
        verified += 1
    return verified


def main():
    # 1. Check zero banned legacy helpers in compute/poly/*.py
    banned_list = ["poly_" + "sig", "get_sols_" + "tight"]
    for p in POLY_DIR.glob("*.py"):
        txt = p.read_text()
        for banned in banned_list:
            assert banned not in txt, f"Found {banned} in {p}"
    print("[PASS] Zero occurrences of banned helpers in compute/poly/*.py")

    # 2. Check (19,74) Farkas certs
    d74 = load_json_auto("deck_19_74.json", RESULTS_DIR)
    r74 = load_json_auto("phase3_19_74_47_13_6_24.json", RESULTS_DIR)
    for idx_s, entry in r74["results"].items():
        idx = int(idx_s)
        if entry.get("stage3_certificates"):
            cnt = verify_stage3_cert_list(d74["candidates"][idx], d74["n"], d74["d"], d74["c"], entry["stage3_certificates"], f"19_74_{idx}", is_19_74=True)
            print(f"  [PASS] 19_74 idx={idx}: verified {cnt} Stage-3 Farkas duals")

    # 3. Check (18,59) Phase-3 result files
    d59 = load_json_auto("deck_18_59.json", RESULTS_DIR)
    n59, d59_dim, c59 = d59["n"], d59["d"], d59["c"]

    # Check clean_a
    ca = load_json_auto("phase3_18_59_clean_a.json", RESULTS_DIR)
    for idx_s, entry in ca["results"].items():
        idx = int(idx_s)
        if entry.get("stage3_certificates"):
            cnt = verify_stage3_cert_list(d59["candidates"][idx], n59, d59_dim, c59, entry["stage3_certificates"], f"18_59_{idx}")
            print(f"  [PASS] 18_59 idx={idx}: verified {cnt} Stage-3 Farkas duals")
        if entry.get("sv_galois_certificates") and entry.get("stage3_survivors_count", 0) == 0:
            sv_cnt = verify_sv_galois_cert_list(d59["candidates"][idx], n59, d59_dim, c59, entry["sv_galois_certificates"], f"18_59_{idx}")
            print(f"  [PASS] 18_59 idx={idx}: verified {sv_cnt} SvGalois certs")

    # Check clean_b if present
    try:
        cb = load_json_auto("phase3_18_59_clean_b.json", RESULTS_DIR)
    except FileNotFoundError:
        cb = None
    if cb is not None:
        for idx_s, entry in cb["results"].items():
            idx = int(idx_s)
            if entry.get("stage3_certificates"):
                cnt = verify_stage3_cert_list(d59["candidates"][idx], n59, d59_dim, c59, entry["stage3_certificates"], f"18_59_{idx}")
                print(f"  [PASS] 18_59 idx={idx}: verified {cnt} Stage-3 Farkas duals")
            if entry.get("sv_galois_certificates") and entry.get("stage3_survivors_count", 0) == 0:
                sv_cnt = verify_sv_galois_cert_list(d59["candidates"][idx], n59, d59_dim, c59, entry["sv_galois_certificates"], f"18_59_{idx}")
                print(f"  [PASS] 18_59 idx={idx}: verified {sv_cnt} SvGalois certs")
            if entry.get("coupled_certs"):
                cones = build_stage2_cones(d59["candidates"][idx], n59, d59_dim, c59)
                cc_cnt = verify_coupled_certs(d59["candidates"][idx], n59, d59_dim, c59, cones, entry["coupled_certs"], f"18_59_{idx}")
                print(f"  [PASS] 18_59 idx={idx}: verified {cc_cnt} Coupled Farkas duals")

    # Check 1164
    try:
        r1164 = load_json_auto("phase3_18_59_1164.json", RESULTS_DIR)
    except FileNotFoundError:
        r1164 = None
    if r1164 is not None:
        w, x, s, deck, Pw, rhs, *_ = build_cand_context(d59["candidates"][1164], n59, d59_dim, c59)
        cones1164 = build_stage2_cones(d59["candidates"][1164], n59, d59_dim, c59)
        cur_act_pass = list(cones1164[0][0])
        pruned_in_pass = set()
        ccs_with_act = []
        base_len = len(r1164["coupled_certs"][0]["c_farkas"]) - len(cur_act_pass)
        for cc in r1164["coupled_certs"]:
            if len(cc["c_farkas"]) != base_len + len(cur_act_pass):
                cur_act_pass = [v for v in cur_act_pass if v not in pruned_in_pass]
                pruned_in_pass = set()
            assert len(cc["c_farkas"]) == base_len + len(cur_act_pass)
            d_cc = dict(cc)
            if "cur_act" not in d_cc:
                d_cc["cur_act"] = list(cur_act_pass)
            pruned_in_pass.add(cc["v_pruned"])
            ccs_with_act.append(d_cc)
        cur_act_pass = [v for v in cur_act_pass if v not in pruned_in_pass]
        assert cur_act_pass == r1164["remaining_act_after_coupled"]
        cc_cnt = verify_coupled_certs(d59["candidates"][1164], n59, d59_dim, c59, cones1164, ccs_with_act, "18_59_1164")
        act = r1164["remaining_act_after_coupled"]
        cols_final = [list(deck[j]) for j in act]
        rhs_final = list(rhs)
        for rf, vf in cones1164[0][1]:
            lcm_d = vf.denominator
            for j in act: lcm_d = math.lcm(lcm_d, rf[j].denominator)
            for lj, gj in enumerate(act): cols_final[lj].append(int(rf[gj] * lcm_d))
            rhs_final.append(int(vf * lcm_d))
        assert verify_farkas_int(cols_final, rhs_final, r1164["final_stage2_farkas"])
        print(f"  [PASS] 18_59 idx=1164: verified {cc_cnt} Coupled + 1 Final Stage-2 Farkas dual")

    # Check 316
    r316 = load_json_auto("phase3_18_59_316.json", RESULTS_DIR)
    cnt = verify_stage3_cert_list(d59["candidates"][316], n59, d59_dim, c59, r316["stage3_certificates"], "18_59_316")
    sv_cnt = verify_sv_galois_cert_list(d59["candidates"][316], n59, d59_dim, c59, r316["sv_galois_certificates"], "18_59_316")
    print(f"  [PASS] 18_59 idx=316: verified {cnt} Stage-3 + {sv_cnt} SvGalois certs")

    # Check 705 cones 1..5 and cone 0
    r705_15 = load_json_auto("phase3_18_59_705_cones1_5.json", RESULTS_DIR)
    cones705 = build_stage2_cones(d59["candidates"][705], n59, d59_dim, c59)
    tot_cc = 0
    for ce in r705_15["cones_1_to_5"]:
        if ce.get("coupled_certs"):
            tot_cc += verify_coupled_certs(d59["candidates"][705], n59, d59_dim, c59, cones705, ce["coupled_certs"], f"18_59_705_c{ce['cone']}")
    print(f"  [PASS] 18_59 idx=705 cones 1..5: verified {tot_cc} Coupled Farkas duals")

    r705_0 = load_json_auto("phase3_18_59_705_cone0.json", RESULTS_DIR)
    cnt = verify_stage3_cert_list(d59["candidates"][705], n59, d59_dim, c59, r705_0["stage3_certificates"], "18_59_705_c0")
    sv_cnt = verify_sv_galois_cert_list(d59["candidates"][705], n59, d59_dim, c59, r705_0["sv_galois_certificates"], "18_59_705_c0")
    print(f"  [PASS] 18_59 idx=705 cone 0: verified {cnt} Stage-3 + {sv_cnt} SvGalois certs")

    # Check 441, 488, 692, 864 spectral/Gram/De Caen-Jacobi/CS kills
    r441_488_692 = load_json_auto("phase3_18_59_441_488_692.json", RESULTS_DIR)
    assert r441_488_692["441"]["status"] == "KILLED_E15_GRAM_ORTH" and r441_488_692["441"]["e15_v10_orth_survivors"] == 0
    assert r441_488_692["488"]["status"] == "KILLED_E11_SUBMATRIX_RANK"
    assert r441_488_692["692"]["status"] == "KILLED_DECAEN_JACOBI_F2_PARITY" and r441_488_692["692"]["unique_H"] == "4_C4_plus_P3_CaseB"
    r864 = load_json_auto("phase3_18_59_864.json", RESULTS_DIR)
    assert r864["status"] == "KILLED_E9_E13_CAUCHY_SCHWARZ" and r864["stage3_survivors_count"] == 3
    print("  [PASS] 18_59 idx={441, 488, 692, 864}: verified killed (verify_441_488_692.py + verify_864.py)")

    # Completeness across all 19 post-Theorem-7.1/7.2 survivors
    expected_19 = {103, 151, 228, 316, 319, 341, 364, 441, 488, 603, 651, 692, 705, 800, 864, 978, 997, 1113, 1164}
    killed_set = set()
    for idx_s, entry in ca["results"].items():
        if entry["status"].startswith("KILLED") and entry.get("stage3_survivors_count", 0) == 0:
            killed_set.add(int(idx_s))
    for idx_s, entry in cb["results"].items():
        if entry["status"].startswith("KILLED") and entry.get("stage3_survivors_count", 0) == 0:
            killed_set.add(int(idx_s))
    if r1164["status"] == "KILLED_STAGE2_COUPLED":
        killed_set.add(1164)
    if r316["status"] == "KILLED_STAGE3" and r316["stage3_survivors_count"] == 0:
        killed_set.add(316)
    if r705_0["survivors_count"] == 0 and all(ce["after_p61"] == 0 for ce in r705_15["cones_1_to_5"]):
        killed_set.add(705)
    killed_set.update([441, 488, 692, 864])
    assert expected_19.issubset(killed_set), f"Missing kills: {sorted(expected_19 - killed_set)}"
    print(f"[DONE] ALL 19/19 (18,59) post-Sec-7 candidates + (19,74) {{47,6,24}} VERIFIED KILLED (0 survivors)!")


if __name__ == "__main__":
    main()
