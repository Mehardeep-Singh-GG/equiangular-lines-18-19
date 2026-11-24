import hashlib
import json
import math
import multiprocessing as mp
import subprocess
import time
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog
import sympy as sp

from phase2_even import find_exact_farkas_rational
from run_stage3_18_59 import (
    bucket_indices_exact,
    exact_lp_bound_any,
    galois_rows_for_bucket,
    sv_kx_galois_check,
)
from stage3_solver import (
    _poly_coeffs_fixed_len,
    solve_2v_jacobi_pair,
    strict_upper_bound_roots,
)


def fast_exact_farkas(cols_int, rhs_int):
    """Exact Farkas certificate via HiGHS dual hint + strict Python int verification + Fraction fallback."""
    m = len(cols_int)
    s = len(rhs_int)
    A = np.array(cols_int, dtype=np.float64)
    b = np.array(rhs_int, dtype=np.float64)
    res = linprog(b, A_ub=-A, b_ub=np.zeros(m), bounds=[(-1.0, 1.0)] * s, method="highs")
    if res.success and res.fun < -1e-7:
        y = res.x
        for scale in [10**6, 10**9, 10**12]:
            c_int = [int(round(v * scale)) for v in y]
            if sum(c_int[r] * rhs_int[r] for r in range(s)) < 0 and all(
                sum(c_int[r] * cols_int[j][r] for r in range(s)) >= 0 for j in range(m)
            ):
                return True, c_int
        return find_exact_farkas_rational(cols_int, rhs_int)
    if res.success and res.fun > -1e-9:
        # Check exact feasibility before accepting feasible!
        return find_exact_farkas_rational(cols_int, rhs_int)
    return find_exact_farkas_rational(cols_int, rhs_int)


# Global worker context (populated before fork)
_CTX = {}


def _check_one_sol(sv):
    act = _CTX["act"]
    rhs_v_map = _CTX["rhs_v_map"]
    q_cs_map = _CTX["q_cs_map"]

    act_ids = [v for v in act if sv[v] > 0]
    act_sorted = sorted(act_ids, key=lambda v: sum(len(q_cs_map[(v, b)]) for b in act_ids))
    # Stage 3 Farkas
    for v in act_sorted:
        rhs_int = rhs_v_map[v]
        cols_int = []
        block_ranges = []
        for b in act_ids:
            nb_rem = sv[b] - (1 if b == v else 0)
            if nb_rem <= 0:
                continue
            sc = len(cols_int)
            cols_int.extend(q_cs_map[(v, b)])
            block_ranges.append((sc, len(cols_int), nb_rem))
        if not cols_int:
            return ("s3", {"method": "stage3_no_pairs", "v_type": v, "counts_n": sv})
        cols_aug = [list(c) for c in cols_int]
        rhs_aug = list(rhs_int)
        for sc, ec, nb_rem in block_ranges:
            for ci in range(len(cols_aug)):
                cols_aug[ci].append(1 if sc <= ci < ec else 0)
            rhs_aug.append(nb_rem)
        inf, c_farkas = fast_exact_farkas(cols_aug, rhs_aug)
        if inf:
            return ("s3", {"method": "stage3_farkas_exact", "v_type": v, "counts_n": sv, "c_farkas": c_farkas})

    # Sv K^x + Galois Farkas (lazy, only on ~2% that survive Stage-3!)
    chi_S = _CTX["chi_S"]
    Gcd_x = _CTX["Gcd_x"]
    Gcd2_x = _CTX["Gcd2_x"]
    Sim_x = _CTX["Sim_x"]
    Mult_rad_x = _CTX["Mult_rad_x"]
    g_list = _CTX["g_list"]
    Q_cache = _CTX["Q_cache"]
    n = _CTX["n"]
    x_sym = _CTX["x_sym"]
    k_sv, c_sv = sv_kx_galois_check(chi_S, Gcd_x, Gcd2_x, Sim_x, Mult_rad_x, g_list, sv, n, x_sym, Q_cache)
    if k_sv:
        return ("sv", c_sv)
    return ("surv", {"counts_n": sv})


def main():
    from pathlib import Path
    import sys
    _COMP_DIR = Path(__file__).resolve().parent.parent
    if str(_COMP_DIR) not in sys.path:
        sys.path.insert(0, str(_COMP_DIR))
    from _io import POLY_DIR, POLY_RESULTS_DIR, load_json_auto

    t0 = time.time()
    d59 = load_json_auto("deck_18_59.json")
    cand = d59["candidates"][705]
    n, d_dim, c_sh = d59["n"], d59["d"], d59["c"]
    w, x = sp.symbols("w x")
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

    chi_S = sp.Poly(sp.expand(2 ** (n - 1) * Full_w.as_expr().subs(w, (x - c_sh) / 2)), x, domain=sp.ZZ)
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
    g_list = [sp.Poly(sp.expand(2 ** (s - 1) * sum(row[k] * w ** (s - 1 - k) for k in range(s)).subs(w, (x - c_sh) / 2)), x, domain=sp.ZZ) for row in deck]

    act = [0, 6, 7, 22, 25, 34, 59, 68, 97, 102, 148, 216, 263, 294]
    m = len(act)
    sub_aug = [list(deck[j]) for j in act]
    bounds_all = []
    for j in range(m):
        obj = [1 if k == j else 0 for k in range(m)]
        lb = math.ceil(exact_lp_bound_any(sub_aug, rhs, obj, sense="min", n_max=n))
        ub = math.floor(exact_lp_bound_any(sub_aug, rhs, obj, sense="max", n_max=n))
        bounds_all.append((j, lb, ub))
    order = sorted(range(m), key=lambda j: -(bounds_all[j][2] - bounds_all[j][1]))
    M_ord = sp.Matrix([[sp.Rational(deck[act[j]][r]) for j in order] + [sp.Rational(rhs[r])] for r in range(s)])
    R, pivots = M_ord.rref()
    piv_set = set(pivots)
    free_ord = [c for c in range(m) if c not in piv_set]
    free_info = sorted([(c, bounds_all[order[c]][1], bounds_all[order[c]][2]) for c in free_ord], key=lambda t: t[2]-t[1])

    out = subprocess.check_output([str(POLY_DIR / "enum705")], text=True)
    sols = []
    free_cols_ord = [t[0] for t in free_info]
    piv_cols_ord = list(pivots)
    for line in out.splitlines():
        if not line.strip(): continue
        vals = [int(z) for z in line.split()]
        vec_ord = [0] * m
        for k, fc in enumerate(free_cols_ord): vec_ord[fc] = vals[k]
        for k, pc in enumerate(piv_cols_ord): vec_ord[pc] = vals[len(free_cols_ord) + k]
        fv = [0] * len(deck)
        for loc_j, orig_loc in enumerate(order): fv[act[orig_loc]] = vec_ord[loc_j]
        sols.append(fv)

    facs_w = [(sp.Poly(fac, w), mult) for fac, mult in sp.factor_list(Pw.as_expr())[1]]
    p61_data = []
    for fac, mf in facs_w:
        hits = [j for j in act if sp.rem(sp.Poly(deck[j], w), fac).is_zero]
        row_lbs = {}
        for k in range(1, n + 1):
            tr2_lb = max(0, (n - d_dim) - k) * 25
            for f2, m2 in facs_w:
                kept = m2 if f2 == fac else max(0, m2 - k)
                if kept > 0:
                    fx = sp.Poly(f2.as_expr().subs(w, (x - c_sh) / 2), x)
                    deg2 = fx.degree()
                    c1 = fx.coeff_monomial(x ** (deg2 - 1)) / fx.LC()
                    c2 = fx.coeff_monomial(x ** (deg2 - 2)) / fx.LC() if deg2 >= 2 else 0
                    tr2_lb += kept * int(c1**2 - 2 * c2)
            row_lbs[k] = tr2_lb <= (n - k) * (n - k - 1)
        p61_data.append((hits, row_lbs))
    after_p61 = [sv for sv in sols if all((sum(sv[j] for j in hits) == 0 or row_lbs[sum(sv[j] for j in hits)]) for hits, row_lbs in p61_data)]
    print(f"Loaded {len(sols)}, after_p61={len(after_p61)} ({time.time()-t0:.2f}s)", flush=True)

    deg_q = (n - 2) - Gcd2_x.degree()
    Q_cache = {}
    q_cs_map = {}
    x_max_ub = strict_upper_bound_roots(chi_S, x)
    for i1 in range(m):
        for i2 in range(i1, m):
            a, b = act[i1], act[i2]
            res = solve_2v_jacobi_pair(g_list[a], g_list[b], Sim_x, Mult_rad_x, Gcd2_x, n, x, x_max_ub=x_max_ub)
            uniq = {}
            for s2_val, q_uv, _ in res:
                key = tuple(int(val) for val in q_uv.all_coeffs())
                if key not in uniq: uniq[key] = {"q_poly": q_uv, "s2_vals": [s2_val]}
            Q_cache[(a, b)] = list(uniq.values())
            Q_cache[(b, a)] = Q_cache[(a, b)]
            q_cs_map[(a, b)] = [_poly_coeffs_fixed_len(it["q_poly"], deg_q + 1) for it in Q_cache[(a, b)]]
            q_cs_map[(b, a)] = q_cs_map[(a, b)]

    rhs_v_map = {}
    for v in act:
        chi_Sv = Gcd_x * g_list[v]
        rhs_p, _ = sp.div(chi_Sv.diff(), Gcd2_x)
        rhs_v_map[v] = _poly_coeffs_fixed_len(rhs_p, deg_q + 1)

    print(f"Q_cache ready in {time.time()-t0:.2f}s", flush=True)
    _CTX["act"] = act
    _CTX["rhs_v_map"] = rhs_v_map
    _CTX["q_cs_map"] = q_cs_map
    _CTX["chi_S"] = chi_S
    _CTX["Gcd_x"] = Gcd_x
    _CTX["Gcd2_x"] = Gcd2_x
    _CTX["Sim_x"] = Sim_x
    _CTX["Mult_rad_x"] = Mult_rad_x
    _CTX["g_list"] = g_list
    _CTX["Q_cache"] = Q_cache
    _CTX["n"] = n
    _CTX["x_sym"] = x

    s3_killed, sv_killed, survs = [], [], []
    with mp.get_context("fork").Pool(processes=6) as pool:
        for i, (kind, payload) in enumerate(pool.imap_unordered(_check_one_sol, after_p61, chunksize=100)):
            if kind == "s3": s3_killed.append(payload)
            elif kind == "sv": sv_killed.append(payload)
            else: survs.append(payload)
            if (i + 1) % 2000 == 0:
                print(f"  progress {i+1}/{len(after_p61)}: s3={len(s3_killed)}, sv={len(sv_killed)}, surv={len(survs)} ({time.time()-t0:.1f}s)", flush=True)

    print(f"DONE idx=705 cone 0: total={len(sols)}, p61={len(after_p61)}, s3={len(s3_killed)}, sv={len(sv_killed)}, surv={len(survs)} ({time.time()-t0:.2f}s)", flush=True)
    POLY_RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    out_p = str(POLY_RESULTS_DIR / "phase3_18_59_705_cone0.json")
    with open(out_p, "w") as f:
        json.dump({"index": 705, "cone": 0, "stage2_sols": len(sols), "after_p61": len(after_p61),
                   "stage3_killed": len(s3_killed), "sv_galois_killed": len(sv_killed),
                   "survivors_count": len(survs), "survivors": survs,
                   "stage3_certificates": s3_killed, "sv_galois_certificates": sv_killed}, f)
    print("Saved", out_p, hashlib.sha256(open(out_p, "rb").read()).hexdigest())


if __name__ == "__main__":
    main()
