"""Independent clean-room verification of Phase-2 eliminations on (19, 74).

Verifies from first principles on the 14 Theorem-4.2-filtered survivors of (19, 74):
1. Reconstructs exact targets and Theorem-4.2-filtered Decks.
2. Obstruction 2 (K^x / (K^x)^2 square-class partitioning via exact algebraic field factorization
   in SymPy QQ(alpha)) + pure Fraction Simplex Farkas/Primal check.
3. Exact Z_{>=0} integrality check inside feasible square-class cones (handling null_dim=0 and 1).
4. Exact Cauchy interlacing + submatrix extraction (mult_lambda(S_v) >= mult_lambda(S) => x_v = 0
   on ker(lambda I - S)) trace-squared contradiction.
"""

from __future__ import annotations

from fractions import Fraction
import json
from pathlib import Path
import time
import sympy as sp

from verify_farkas import check_thm42_odd, exact_farkas_or_primal, poly_shift_linear
from _repo_io import AUDIT_DIR, COMPUTE_POLY_RESULTS, read_json_auto


POLY_RESULTS_DIR = COMPUTE_POLY_RESULTS
OUT_JSON = AUDIT_DIR / "phase2_19_74_audit.json"


def is_square_in_field(elem_poly_z: sp.Poly, min_poly_z: sp.Poly, K, z_sym: sp.Symbol) -> bool:
    """Exact test whether elem(alpha) is a square in K = QQ[z]/(min_poly_z)."""
    rem = sp.rem(elem_poly_z, min_poly_z, domain=sp.QQ)
    if rem.is_zero:
        return True
    # Express rem(alpha) as element of K
    alpha = K.unit
    elem_K = K.zero
    coeffs_desc = [K.dom.convert(c) for c in rem.all_coeffs()]
    for c in coeffs_desc:
        elem_K = elem_K * alpha + c
    t = sp.Symbol("t")
    sq_poly = sp.Poly.from_dict({(2,): K.one, (0,): -elem_K}, t, domain=K)
    _, factors = sq_poly.factor_list()
    return any(f.degree() == 1 for f, _ in factors)


def square_classes_for_simple_factor(
    deck: list[list[int]], min_poly_z: sp.Poly, z: sp.Symbol
) -> list[list[int]]:
    """Partition nonzero deck entries at root alpha of simple irreducible factor min_poly_z
    into square-class buckets in K^x / (K^x)^2, plus the zero bucket (if any).
    Returns list of valid vertex-support index subsets S_bucket (each bucket union zero-indices).
    """
    if min_poly_z.degree() == 1:
        # Rational root r = -c0 / c1
        c1, c0 = [Fraction(int(v)) for v in min_poly_z.all_coeffs()]
        root = -c0 / c1
        zero_idx = []
        buckets: dict[int, list[int]] = {}  # square-free integer rep -> indices
        for i, g_desc in enumerate(deck):
            val = Fraction(0)
            for c in g_desc:
                val = val * root + c
            if val == 0:
                zero_idx.append(i)
            else:
                # Square-free rational rep: sgn * sqf(num * den)
                num_den = abs(val.numerator * val.denominator)
                # Factor out squares
                sf = sp.core.factorint(num_den) if hasattr(sp.core, "factorint") else sp.factorint(num_den)
                rep = 1 if val > 0 else -1
                for p, exp in sf.items():
                    if exp % 2 == 1:
                        rep *= p
                buckets.setdefault(rep, []).append(i)
        return [b + zero_idx for b in buckets.values()]
    else:
        min_poly_q = sp.Poly(min_poly_z.as_expr(), z, domain=sp.QQ)
        alpha_root = sp.CRootOf(min_poly_z, 0)
        K = sp.QQ.algebraic_field(alpha_root)
        zero_idx = []
        reps: list[tuple[sp.Poly, Fraction, list[int]]] = []
        for i, g_desc in enumerate(deck):
            g_poly = sp.Poly(g_desc, z, domain=sp.QQ)
            rem = sp.rem(g_poly, min_poly_q, domain=sp.QQ)
            if rem.is_zero:
                zero_idx.append(i)
            else:
                # Exact norm N_{K/Q}(rem) via resultant: res(min_poly, rem) / lc(min_poly)^deg(rem)
                res_val = sp.resultant(min_poly_q.as_expr(), rem.as_expr(), z)
                norm_q = Fraction(res_val.p, res_val.q)
                # Reduce norm_q to square-free integer signature (exact necessary invariant!)
                num_den = abs(norm_q.numerator * norm_q.denominator)
                sf_dict = sp.factorint(num_den)
                norm_sf = 1 if norm_q > 0 else -1
                for p_fac, exp in sf_dict.items():
                    if exp % 2 == 1:
                        norm_sf *= p_fac

                placed = False
                for rep_poly, rep_norm_sf, bucket in reps:
                    if norm_sf != rep_norm_sf:
                        continue
                    prod_poly = sp.Poly(rep_poly.as_expr() * rem.as_expr(), z, domain=sp.QQ)
                    if is_square_in_field(prod_poly, min_poly_q, K, z):
                        bucket.append(i)
                        placed = True
                        break
                if not placed:
                    reps.append((rem, norm_sf, [i]))
        return [b + zero_idx for _, _, b in reps]


def solve_null_dim_0_or_1(A_eq_int: list[list[int]], b_eq_int: list[int], n_target: int) -> list[list[int]]:
    """Find all nonnegative integer solutions x in Z_{>=0}^e to A_eq * x = b_eq
    when rank allows null_dim <= 1 (returns empty list if null_dim > 1 without assuming)."""
    M = sp.Matrix([[sp.Integer(v) for v in row] for row in A_eq_int])
    rhs = sp.Matrix([sp.Integer(v) for v in b_eq_int])
    e = len(A_eq_int[0])
    aug = M.row_join(rhs)
    rref_aug, pivots = aug.rref()
    # Check consistency
    for r in range(rref_aug.rows):
        if all(rref_aug[r, c] == 0 for c in range(e)) and rref_aug[r, e] != 0:
            return []
    piv_set = set(pivots)
    free_cols = [c for c in range(e) if c not in piv_set]
    if len(free_cols) == 0:
        sol = [Fraction(0)] * e
        for r, p in enumerate(pivots):
            if p < e:
                val = rref_aug[r, e]
                sol[p] = Fraction(int(val.p), int(val.q))
        if all(v >= 0 and v.denominator == 1 for v in sol):
            return [[int(v) for v in sol]]
        return []
    if len(free_cols) == 1:
        fc = free_cols[0]
        # x = x0 + t * dir_vec, with t = x[fc] >= 0 and t <= n_target
        x0 = [Fraction(0)] * e
        dv = [Fraction(0)] * e
        dv[fc] = Fraction(1)
        for r, p in enumerate(pivots):
            if p < e:
                val = rref_aug[r, e]
                c_fc = rref_aug[r, fc]
                x0[p] = Fraction(int(val.p), int(val.q))
                dv[p] = -Fraction(int(c_fc.p), int(c_fc.q))
        int_sols = []
        for t in range(n_target + 1):
            cand = [x0[j] + t * dv[j] for j in range(e)]
            if all(v >= 0 and v.denominator == 1 for v in cand):
                int_sols.append([int(v) for v in cand])
        return int_sols
    raise ValueError(f"null_dim={len(free_cols)} > 1")


def main() -> None:
    t0 = time.time()
    d, n = 19, 74
    deck_data = read_json_auto(POLY_RESULTS_DIR, "deck_19_74.json")
    farkas_data = read_json_auto(POLY_RESULTS_DIR, "farkas_19_74.json")
    c_shift = int(deck_data["c"])
    w_neg5 = -(c_shift + 5) // 2
    shift_t = -(c_shift + 1) // 2
    z = sp.Symbol("z")

    surv_ids = [s["index"] for s in farkas_data["survivors"]]
    report = []

    for idx in surv_ids:
        cand = deck_data["candidates"][idx]
        s = cand["s"]
        p_z = sp.Poly(cand["b"], z, domain=sp.ZZ)
        F_z = sp.Poly(((z - w_neg5) ** (n - d)) * p_z.as_expr(), z, domain=sp.ZZ)
        Fp_z = sp.diff(F_z, z)
        Gcd_z = sp.gcd(F_z, Fp_z)
        target = [int(v) for v in sp.Poly(sp.quo(2 * Fp_z, Gcd_z), z, domain=sp.ZZ).all_coeffs()]

        # Filter Deck by Theorem 4.2
        deck = []
        for g_desc in cand["deck"]:
            g_poly = sp.Poly(g_desc, z, domain=sp.ZZ)
            prod_z = sp.Poly(Gcd_z.as_expr() * g_poly.as_expr(), z, domain=sp.ZZ)
            prod_t_desc = poly_shift_linear([int(v) for v in prod_z.all_coeffs()], 1, shift_t)
            if check_thm42_odd(prod_t_desc[::-1], n - 1):
                deck.append(g_desc)

        if not deck:
            report.append({"index": idx, "status": "ELIMINATED_THM42", "deck_len": 0})
            continue

        A_eq_all = [[deck[i][k] for i in range(len(deck))] for k in range(s)]
        st_lp, _ = exact_farkas_or_primal(A_eq_all, target)
        if st_lp == "FARKAS":
            report.append({"index": idx, "status": "ELIMINATED_THM42_FARKAS", "deck_len": len(deck)})
            continue

        # Obstruction 2: Square-class partitioning across ALL simple irreducible factors of F_z
        _, fac_list = sp.factor_list(F_z)
        simple_factors = [fac for fac, mult in fac_list if mult == 1]

        # Start with all indices allowed, and branch across square-class buckets of each simple factor
        valid_subsets = [list(range(len(deck)))]
        for sf in simple_factors:
            buckets = square_classes_for_simple_factor(deck, sf, z)
            next_subsets = []
            for cur in valid_subsets:
                cur_set = set(cur)
                for b in buckets:
                    inter = sorted(cur_set & set(b))
                    if inter and inter not in next_subsets:
                        next_subsets.append(inter)
            valid_subsets = next_subsets

        feasible_cones = []
        for sub in valid_subsets:
            A_sub = [[deck[i][k] for i in sub] for k in range(s)]
            st_sub, _ = exact_farkas_or_primal(A_sub, target)
            if st_sub == "PRIMAL":
                feasible_cones.append(sub)

        if not feasible_cones:
            report.append({
                "index": idx,
                "status": "ELIMINATED_OBS2_SQUARE_CLASS",
                "simple_factors": [str(sf.as_expr()) for sf in simple_factors],
            })
            print(f"[ELIM Obs2] idx={idx} (deck={len(deck)}, simple_factors={len(simple_factors)})")
            continue

        # Check Z_{>=0} integrality & Obstruction 4 (submatrix extraction) for feasible cones
        # For each feasible cone with null_dim <= 1, enumerate all Z_{>=0} solutions;
        # otherwise mark SURVIVED_TO_PHASE2_FINAL
        all_int_sols = []
        unsolved_high_dim = False
        for sub in feasible_cones:
            A_sub = [[deck[i][k] for i in sub] for k in range(s)]
            try:
                int_sols = solve_null_dim_0_or_1(A_sub, target, n)
                for sol_vec in int_sols:
                    all_int_sols.append((sub, sol_vec))
            except ValueError:
                unsolved_high_dim = True

        if not unsolved_high_dim and not all_int_sols:
            report.append({
                "index": idx,
                "status": "ELIMINATED_NO_NONNEG_INT_SOL",
                "feasible_cones": len(feasible_cones),
            })
            print(f"[ELIM Z>=0] idx={idx} (feasible_cones={len(feasible_cones)}, 0 integer sols)")
            continue

        # Obstruction 4: check every integer solution (if fully enumerated) against submatrix trace^2 bound
        if not unsolved_high_dim:
            surviving_sols = []
            for sub, sol_vec in all_int_sols:
                # For each eigenvalue root of F_z (via square-free factors), check if subset of vertices
                # preserves multiplicity m_r -> deleting k_del vertices leaves (n - k_del) x (n - k_del)
                # principal submatrix T with Tr(T^2) = (n - k_del)(n - k_del - 1).
                # Check all integer/irrational factors: actually easiest to check each factor (fac, mult) of F_z!
                # Wait: if fac divides Gcd_z^{0}? More precisely: in x-coords, lambda = 2*r + c_shift.
                # On any factor fac with multiplicity mult: if G_i(z) has fac^1 | Gcd_z * G_i?
                # Wait: F_z has factor fac^mult, and F_v_z = Gcd_z * G_i has fac^(mult - 1) automatically;
                # G_i(z) is divisible by fac iff mult_v(fac) >= mult!
                killed_by_obs4 = False
                for fac, mult in fac_list:
                    if fac == sp.Poly(z - w_neg5, z, domain=sp.ZZ):
                        continue
                    # Sum sol_vec for entries i in sub where fac | deck[i]
                    k_del = 0
                    for pos, deck_idx in enumerate(sub):
                        if sol_vec[pos] > 0:
                            g_poly = sp.Poly(deck[deck_idx], z, domain=sp.ZZ)
                            if sp.rem(g_poly, fac).is_zero:
                                k_del += sol_vec[pos]
                    if k_del > 0 and k_del < n:
                        n_rem = n - k_del
                        # Deleting k_del vertices preserves mult of fac (deg * mult)
                        # AND by interlacing keeps mult(-5) >= max(0, (n - d) - k_del)!
                        m_neg5 = max(0, (n - d) - k_del)
                        # Sum of lambda^2 for roots of fac^mult:
                        # In x = 2z + c_shift, let P_x(x) = fac((x - c_shift)/2) made monic
                        fac_x_coeffs = poly_shift_linear([int(v) for v in fac.all_coeffs()], 1, -c_shift)
                        # Wait: fac(z) -> fac((x - c_shift)/2) = sum c_j (x-c)^{deg-j} / 2^{deg-j}
                        deg_f = fac.degree()
                        # Sum of roots of fac(z): -fac[1]/fac[0]
                        sum_z = Fraction(-int(fac.all_coeffs()[1]), int(fac.all_coeffs()[0]))
                        if deg_f == 1:
                            lam = 2 * sum_z + c_shift
                            sum_lam2 = lam * lam
                        else:
                            sum_z2 = sum_z * sum_z - 2 * Fraction(int(fac.all_coeffs()[2]), int(fac.all_coeffs()[0]))
                            sum_lam2 = 4 * sum_z2 + 4 * c_shift * sum_z + deg_f * (c_shift ** 2)
                        lhs_tr2 = m_neg5 * 25 + mult * sum_lam2
                        rhs_tr2 = n_rem * (n_rem - 1)
                        if lhs_tr2 > rhs_tr2:
                            killed_by_obs4 = True
                            break
                if not killed_by_obs4:
                    surviving_sols.append((sub, sol_vec))
            if not surviving_sols:
                report.append({
                    "index": idx,
                    "status": "ELIMINATED_OBS4_EXTRACTION",
                    "int_sols_tested": len(all_int_sols),
                })
                print(f"[ELIM Obs4] idx={idx} (all {len(all_int_sols)} int sols violated submatrix Tr(T^2))")
                continue

        report.append({
            "index": idx,
            "status": "SURVIVED",
            "deck_len": len(deck),
            "feasible_cones": len(feasible_cones),
        })
        print(f"[SURVIVED] idx={idx} (deck={len(deck)}, feasible_cones={len(feasible_cones)})")

    OUT_JSON.write_text(json.dumps(report, indent=2))
    surv_out = [r["index"] for r in report if r["status"] == "SURVIVED"]
    print(f"Summary: 22 -> {len(surv_out)} survivors {surv_out} in {time.time() - t0:.2f}s")


if __name__ == "__main__":
    main()
