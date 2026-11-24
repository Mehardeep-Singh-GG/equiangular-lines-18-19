"""
Exact Stage-2 K^x-bucketed enumeration + Stage-3 (2v-Jacobi + 1v derivative system)
for (19, 74) Phase-2 survivors {47, 13, 6, 24, 74, 134}.
"""

import hashlib
import json
import math
import time
from fractions import Fraction
import sympy as sp

from phase2_even import (
    passes_t42_sub,
    exact_lp_bound,
    find_exact_farkas_rational,
    is_square_in_field_exact,
)
from stage3_solver import check_stage3_for_counts


def bucket_deck_by_kx(deck_t42, q_fac_w, w):
    """Partition deck_t42 into zero-mod-q indices and square-class buckets in Q[w]/(q_fac_w)."""
    zeros = []
    buckets = []
    for j, row in enumerate(deck_t42):
        psi = sp.Poly(row, w, domain=sp.ZZ)
        rem = sp.rem(psi, q_fac_w)
        if rem.is_zero:
            zeros.append(j)
            continue
        placed = False
        for b in buckets:
            rep_psi = sp.Poly(deck_t42[b[0]], w, domain=sp.ZZ)
            if is_square_in_field_exact((psi * rep_psi).as_expr(), q_fac_w, w):
                b.append(j)
                placed = True
                break
        if not placed:
            buckets.append([j])
    return zeros, buckets


def enum_bucket_stage2_sols(deck_t42, active_cols, rhs, n):
    """Exact RREF + dual bounds over active_cols subset of deck_t42."""
    sub_deck = [deck_t42[j] for j in active_cols]
    m = len(sub_deck)
    s = len(rhs)
    cols_T = [
        [int(sub_deck[j][r]) for r in range(s)] for j in range(m)
    ]
    infeasible, f_cert = find_exact_farkas_rational(cols_T, rhs)
    if infeasible:
        return [], {"status": "farkas_infeasible", "c_farkas": f_cert}

    M = sp.Matrix([[sp.Rational(sub_deck[j][r]) for j in range(m)] + [sp.Rational(rhs[r])] for r in range(s)])
    R, pivots = M.rref()
    for r in range(R.rows):
        if all(R[r, c] == 0 for c in range(m)) and R[r, m] != 0:
            return [], {"status": "rref_inconsistent"}
    piv_set = set(pivots)
    free_cols = [c for c in range(m) if c not in piv_set]
    eqs = []
    for r, pc in enumerate(pivots):
        c0 = Fraction(R[r, m].p, R[r, m].q)
        coeffs = {fc: Fraction(R[r, fc].p, R[r, fc].q) for fc in free_cols if R[r, fc] != 0}
        eqs.append((pc, c0, coeffs))

    bounds = []
    for fc in free_cols:
        obj = [1 if j == fc else 0 for j in range(m)]
        lb, _ = exact_lp_bound(sub_deck, rhs, obj, sense="min", n_max=n)
        ub, _ = exact_lp_bound(sub_deck, rhs, obj, sense="max", n_max=n)
        lo = math.ceil(lb) if lb is not None else 0
        hi = math.floor(ub) if ub is not None else n
        if lo > hi:
            return [], {"status": "empty_dual_bounds"}
        bounds.append((fc, max(0, lo), min(n, hi)))
    bounds.sort(key=lambda t: t[2] - t[1])

    sols = []
    assign = {}

    def dfs(i):
        if i == len(bounds):
            vec_sub = [0] * m
            for fv, v in assign.items():
                vec_sub[fv] = v
            for pc, c0, coeffs in eqs:
                val = c0 - sum(cf * assign[fv] for fv, cf in coeffs.items())
                if val < 0 or val.denominator != 1:
                    return
                vec_sub[pc] = int(val)
            if sum(vec_sub) == n:
                full_vec = [0] * len(deck_t42)
                for loc_j, glob_j in enumerate(active_cols):
                    full_vec[glob_j] = vec_sub[loc_j]
                sols.append(full_vec)
            return
        fv, lo, hi = bounds[i]
        for v in range(lo, hi + 1):
            assign[fv] = v
            dfs(i + 1)

    dfs(0)
    return sols, {"status": "enumerated", "count": len(sols)}


def prop61_sol_ok(vec, deck_t42, Pw, n, d, c_shift, w, x):
    """Check Prop 6.1 trace-square bound for a single explicit solution vector vec."""
    facs = sp.factor_list(Pw.as_expr())[1]
    roots_info = [(sp.Poly(fac, w), mult) for fac, mult in facs]
    for fac, mf in roots_info:
        k = sum(vec[j] for j, row in enumerate(deck_t42) if sp.rem(sp.Poly(row, w), fac).is_zero)
        if k < 1:
            continue
        sz = n - k
        tr2_ub = sz * (sz - 1)
        tr2_lb = max(0, (n - d) - k) * 25
        for f2, m2 in roots_info:
            kept = m2 if f2 == fac else max(0, m2 - k)
            if kept > 0:
                fx = sp.Poly(f2.as_expr().subs(w, (x - c_shift) / 2), x)
                deg2 = fx.degree()
                c1 = fx.coeff_monomial(x ** (deg2 - 1)) / fx.LC()
                c2 = fx.coeff_monomial(x ** (deg2 - 2)) / fx.LC() if deg2 >= 2 else 0
                tr2_lb += kept * int(c1**2 - 2 * c2)
        if tr2_lb > tr2_ub:
            return False, (sp.sstr(fac.as_expr()), k, tr2_lb, tr2_ub)
    return True, None


def run():
    from pathlib import Path
    import sys
    _COMP_DIR = Path(__file__).resolve().parent.parent
    if str(_COMP_DIR) not in sys.path:
        sys.path.insert(0, str(_COMP_DIR))
    from _io import POLY_RESULTS_DIR, load_json_auto

    t_start = time.time()
    d74 = load_json_auto("deck_19_74.json")
    n, d_dim, c_sh = d74["n"], d74["d"], d74["c"]
    w0 = (-5 - c_sh) // 2
    s_sh = (c_sh + 1) // 2
    w, x, z = sp.symbols("w x z")

    target_indices = [47, 13, 6, 24]
    report = {"d": d_dim, "n": n, "targets": target_indices, "results": {}}

    for idx in target_indices:
        t0 = time.time()
        cand = d74["candidates"][idx]
        s = cand["s"]
        Pw = sp.Poly(sum(cand["b"][j] * w ** (d_dim - j) for j in range(d_dim + 1)), w, domain=sp.ZZ)
        Full_w = sp.Poly((w - w0) ** (n - d_dim), w, domain=sp.ZZ) * Pw
        Dw = sp.gcd(Full_w, Full_w.diff())
        if Dw.LC() < 0:
            Dw = -Dw
        quo, _ = sp.div(Full_w.diff(), Dw)
        RHS_poly = sp.Poly(2 * quo, w, domain=sp.ZZ)
        rhs = [int(v) for v in RHS_poly.all_coeffs()]
        while len(rhs) < s:
            rhs = [0] + rhs

        chi_S = sp.Poly(sp.expand(2 ** n * Full_w.as_expr().subs(w, (x - c_sh) / 2)), x, domain=sp.ZZ)
        Gcd_x = sp.gcd(chi_S, chi_S.diff())
        if Gcd_x.LC() < 0:
            Gcd_x = -Gcd_x
        Gcd2_x = sp.gcd(Gcd_x, Gcd_x.diff())
        if Gcd2_x.LC() < 0:
            Gcd2_x = -Gcd2_x

        facs_x = sp.factor_list(chi_S.as_expr())[1]
        Sim_x = sp.Poly(1, x, domain=sp.ZZ)
        Mult_rad_x = sp.Poly(1, x, domain=sp.ZZ)
        for fac, mult in facs_x:
            fp = sp.Poly(fac, x, domain=sp.ZZ)
            if mult == 1:
                Sim_x = Sim_x * fp
            else:
                Mult_rad_x = Mult_rad_x * fp

        deck_t42 = [row for row in cand["deck"] if passes_t42_sub(Dw, sp.Poly(row, w, domain=sp.ZZ), n - 1, s_sh, z, w)]
        g_list = [
            sp.Poly(sp.expand(2 ** (s - 2) * sum(int(row[k]) * w ** (s - 1 - k) for k in range(s)).subs(w, (x - c_sh) / 2)), x, domain=sp.ZZ)
            for row in deck_t42
        ]

        # K^x bucketing on simple factor of Pw
        simple_q = [sp.Poly(fac, w, domain=sp.ZZ) for fac, mult in sp.factor_list(Pw.as_expr())[1] if mult == 1][0]
        zeros, buckets = bucket_deck_by_kx(deck_t42, simple_q, w)
        print(f"\n=== (19,74) idx={idx} (s={s}, deck_t42={len(deck_t42)}, zeros={zeros}, buckets={buckets}) ===", flush=True)

        bucket_sols = []
        bucket_certs = []
        for b_idx, b in enumerate(buckets):
            active_cols = sorted(set(zeros) | set(b))
            sols, b_info = enum_bucket_stage2_sols(deck_t42, active_cols, rhs, n)
            print(f"  bucket {b_idx} ({b}): {b_info}", flush=True)
            bucket_certs.append({"bucket": b, "active_cols": active_cols, "info": b_info})
            for v_sol in sols:
                if v_sol not in bucket_sols:
                    bucket_sols.append(v_sol)

        # Prop 6.1 filter
        after_p61 = []
        p61_kills = []
        for v_sol in bucket_sols:
            ok, info61 = prop61_sol_ok(v_sol, deck_t42, Pw, n, d_dim, c_sh, w, x)
            if ok:
                after_p61.append(v_sol)
            else:
                p61_kills.append({"vec": v_sol, "prop61": info61})
        print(f"  Stage-2 K^x sols={len(bucket_sols)}, after Prop6.1={len(after_p61)} (killed {len(p61_kills)})", flush=True)

        Q_cache = {}
        stage3_survivors = []
        stage3_certs = []
        for s_i, v_sol in enumerate(after_p61):
            killed, cert = check_stage3_for_counts(
                chi_S, Gcd_x, Gcd2_x, Sim_x, Mult_rad_x, g_list, v_sol, n, x, Q_cache=Q_cache
            )
            if killed:
                stage3_certs.append(cert)
            else:
                stage3_survivors.append(cert)
                print(f"  SURVIVOR sol #{s_i}: {v_sol}", flush=True)

        dt = time.time() - t0
        status = "KILLED" if not stage3_survivors else "SURVIVED"
        print(f"  => idx={idx} {status} in {dt:.2f}s (stage3_killed={len(stage3_certs)}/{len(after_p61)}, stage3_survivors={len(stage3_survivors)})", flush=True)
        report["results"][str(idx)] = {
            "status": status,
            "s": s,
            "Sim_x": sp.sstr(Sim_x.as_expr()),
            "deck_t42_size": len(deck_t42),
            "zeros": zeros,
            "buckets": buckets,
            "bucket_certs": bucket_certs,
            "stage2_kx_sols": len(bucket_sols),
            "prop61_killed": len(p61_kills),
            "after_prop61_sols": len(after_p61),
            "stage3_killed": len(stage3_certs),
            "stage3_survivors_count": len(stage3_survivors),
            "stage3_survivors": stage3_survivors,
            "stage3_certificates": stage3_certs,
            "elapsed_sec": round(dt, 3),
        }

    POLY_RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    out_path = str(POLY_RESULTS_DIR / "phase3_19_74_47_13_6_24.json")
    with open(out_path, "w") as f:
        json.dump(report, f, indent=2)
    sha = hashlib.sha256(open(out_path, "rb").read()).hexdigest()
    print(f"\nSaved {out_path} (sha256={sha}), total elapsed={time.time() - t_start:.2f}s", flush=True)


if __name__ == "__main__":
    run()
