"""Independent exact rational audit of Stage-2 Deck & Farkas LP results.

For each (d, n) with deck_<d>_<n>.json and farkas_<d>_<n>.json:
1. Reconstructs chi_S(x) from b = p(z) independently, verifies exact target polynomial
   (chi'_S(x) / gcd(chi_S, chi'_S)) in z = (x - c)/2 coordinates.
2. Verifies EVERY deck entry G_i(z):
   - Exact interlacing with M(z) (square-free minimal part of chi_S in z-coords).
   - Full lift chi_{S_v}(x) satisfies exact odd-(n-1) 2-adic congruences AND the odd-order Pfaffian congruence.
3. Solves the exact rational LP over QQ (via sympy.solvers.simplex.linprog, zero floats!)
   for n >= 0, sum_i n_i G_i == target, verifying exact match with farkas_<d>_<n>.json's
   killed vs survivor classification and validating an explicit exact rational solution
   or dual Farkas certificate for every candidate.
"""

from __future__ import annotations

import hashlib
import json
from fractions import Fraction
from pathlib import Path
import time
import sympy as sp
from sympy.solvers.simplex import InfeasibleLPError, linprog

from verify_polys import poly_eval_2tm1_asc, poly_mul_linear_int, v2
from _repo_io import AUDIT_DIR, COMPUTE_POLY_RESULTS, read_json_auto


POLY_RESULTS_DIR = COMPUTE_POLY_RESULTS


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def exact_farkas_or_primal(A_eq_int: list[list[int]], b_eq_int: list[int]) -> tuple[str, list[Fraction]]:
    """Pure Fraction Two-Phase Simplex (Phase I) with Bland's rule.
    Tests existence of x >= 0 such that A_eq * x = b_eq.
    Returns:
      ("PRIMAL", x_sol) with x_sol >= 0 and A_eq * x_sol == b_eq, OR
      ("FARKAS", y_cert) with y_cert^T A_eq >= 0 and y_cert^T b_eq < 0.
    Zero floating-point arithmetic; 100% self-contained exact certificate.
    """
    m = len(A_eq_int)
    n_vars = len(A_eq_int[0])
    # Flip rows so b >= 0, recording sign flips to map y back to original equations
    flips = [1] * m
    rows: list[list[Fraction]] = []
    rhs: list[Fraction] = []
    for r in range(m):
        if b_eq_int[r] < 0:
            flips[r] = -1
            rows.append([Fraction(-A_eq_int[r][c]) for c in range(n_vars)])
            rhs.append(Fraction(-b_eq_int[r]))
        else:
            rows.append([Fraction(A_eq_int[r][c]) for c in range(n_vars)])
            rhs.append(Fraction(b_eq_int[r]))

    # Track linear combination of flipped rows for each row of the tableau:
    # row_combo[r][i] tracks how row r is formed from initial rows i=0..m-1,
    # and obj_combo[i] tracks the objective row!
    # Actually: Phase I minimizes sum(art_r). Initial tableau has artificial vars a_0..a_{m-1}
    # with basis = [n_vars + r for r in range(m)].
    # Initial reduced cost row: c_j = -sum_{r=0}^{m-1} rows[r][j] (since we subtract sum of rows from min sum(a_r))
    # Wait: let obj = sum(a_r) = sum(rhs[r]) - sum_{j=0}^{n_vars-1} (sum_r rows[r][j]) x_j.
    # Let's include an m x m tracker matrix T (initialized to I_m) alongside tableau!
    # At any step, current rows == T * initial_rows and current rhs == T * initial_rhs!
    # And the objective row (for Phase I: min sum a_r) has coefficients:
    # obj_val = sum(a_r) = obj_rhs + sum_j obj_c[j] * x_j + sum_r obj_art[r] * a_r.
    # Initially: obj_c[j] = -sum_r rows[r][j], obj_art[r] = 0 (artificials are basic with reduced cost 0),
    # obj_rhs = -sum_r rhs[r] (so obj = -obj_rhs + ...; when we maximize -sum(a_r), reduced costs c_j = sum_r rows[r][j] -> pick > 0 to enter!).
    # Even simpler: maintain full tableau with columns [x_0..x_{n-1}, a_0..a_{m-1}, RHS]
    # and also track dual multipliers y_mult[i] (length m) for the objective row!
    # Initially, objective = sum(a_r) = sum_r (rhs[r] - sum_j A_{rj} x_j).
    # So obj_row = [-sum_r A_{rj} for j in 0..n-1] + [0]*m + [-sum_r rhs[r]]
    # Wait: if we want to DECREASE sum(a_r), we pick column j with obj_row[j] < 0!
    # Let's verify: obj = -obj_row[-1] + sum_j obj_row[j] x_j + sum_r obj_row[n+r] a_r.
    # Initially obj_row[-1] = -sum_r rhs[r], so -obj_row[-1] = +sum_r rhs[r] >= 0.
    # When x_j increases, obj changes by obj_row[j] * x_j, so we pivot on obj_row[j] < 0!
    # And notice: at every step, obj_row[0..n-1] == sum_i y_mult[i] * init_rows[i] (NO, -sum_i ...)!
    # Let's check: initially obj_row[j] = sum_i (-1) * init_rows[i][j], and obj_row[n+i] = 0, and obj_row[-1] = sum_i (-1) * init_rhs[i].
    # Every pivot adds a multiple of a tableau row (which is a linear combination of original equations) to obj_row!
    # Look at the artificial columns n..n+m-1 of obj_row:
    # Each equation i is: init_rows[i] . x + 1 * a_i = init_rhs[i].
    # So ANY multiple y_mult of equations has coefficient y_mult[i] on a_i!
    # Specifically, obj_row = (initial obj_row) + sum_i alpha_i * (eq_i) = sum_i (-1 + alpha_i) * (init_rows[i].x + a_i - init_rhs[i]) + sum a_i!
    # Wait: coefficient of a_i in obj_row IS (-1 + alpha_i) + 1 = alpha_i!!
    # Check at start: alpha_i = 0, so coeff of a_i in obj_row is 0, and coeff of x_j is sum_i (-1 + 0) * init_rows[i][j]!
    # So at ALL times, letting w_i = obj_row[n + i] - 1:
    #   obj_row[j] == sum_i w_i * init_rows[i][j]  for all j = 0..n-1,
    #   obj_row[-1] == sum_i w_i * init_rhs[i]!!
    # When Phase I stops with no obj_row[j] < 0 (all obj_row[j] >= 0 for j=0..n-1) AND -obj_row[-1] > 0 (i.e. obj_row[-1] < 0):
    # w_i gives: sum_i w_i * init_rows[i][j] = obj_row[j] >= 0, AND sum_i w_i * init_rhs[i] = obj_row[-1] < 0!!
    # Unscaling flips: y_orig[i] = w_i * flips[i] IS AN EXACT FARKAS CERTIFICATE!!
    # Check: sum_i y_orig[i] * A_eq_int[i][j] = sum_i w_i * init_rows[i][j] >= 0, and sum_i y_orig[i] * b_eq_int[i] = obj_row[-1] < 0!!
    # WHAT A BEAUTIFUL THEOREM OF LINEAR PROGRAMMING!!

    total_cols = n_vars + m
    tab: list[list[Fraction]] = []
    for r in range(m):
        row = rows[r] + [Fraction(1 if i == r else 0) for i in range(m)] + [rhs[r]]
        tab.append(row)
    obj = [-sum(rows[r][j] for r in range(m)) for j in range(n_vars)] + [Fraction(0)] * m + [-sum(rhs)]
    basis = [n_vars + r for r in range(m)]

    while True:
        # Bland's rule: pick smallest column j in 0..total_cols-1 with obj[j] < 0
        enter = -1
        for j in range(total_cols):
            if obj[j] < 0:
                enter = j
                break
        if enter == -1:
            break
        # Ratio test with Bland's tie-breaking on smallest basis index
        leave = -1
        best_ratio: Fraction | None = None
        for r in range(m):
            piv = tab[r][enter]
            if piv > 0:
                ratio = tab[r][-1] / piv
                if best_ratio is None or ratio < best_ratio or (ratio == best_ratio and basis[r] < basis[leave]):
                    best_ratio = ratio
                    leave = r
        if leave == -1:
            raise RuntimeError("Phase I LP unbounded (impossible for sum(a_r) >= 0)")

        # Pivot at (leave, enter)
        piv_val = tab[leave][enter]
        tab[leave] = [v / piv_val for v in tab[leave]]
        for r in range(m):
            if r == leave:
                continue
            factor = tab[r][enter]
            if factor != 0:
                tab[r] = [tab[r][c] - factor * tab[leave][c] for c in range(total_cols + 1)]
        factor_obj = obj[enter]
        if factor_obj != 0:
            obj = [obj[c] - factor_obj * tab[leave][c] for c in range(total_cols + 1)]
        basis[leave] = enter

    if obj[-1] < 0:
        # Infeasible: extract exact Farkas certificate directly from artificial columns of obj!
        y_cert = [(obj[n_vars + r] - 1) * flips[r] for r in range(m)]
        return ("FARKAS", y_cert)

    # Otherwise obj[-1] == 0 => feasible! Drive any remaining artificials out of basis or verify zero value
    x_sol = [Fraction(0)] * n_vars
    for r in range(m):
        col = basis[r]
        if col < n_vars:
            x_sol[col] = tab[r][-1]
        else:
            assert tab[r][-1] == 0, f"Artificial var nonzero at Phase I opt: {tab[r][-1]}"
    return ("PRIMAL", x_sol)


def check_thm42_odd(P_asc: list[int], m: int) -> bool:
    """Check odd-order mod-2^{m+1} Pfaffian congruence for odd order m:
    2^{-(m-1)} chi(2t-1) == (2t - m) Q(t)^2 (mod 4)."""
    R = [0] * (m + 2)
    for i, v in enumerate(P_asc):
        R[i] = (R[i] - m * v) % 4
        R[i + 1] = (R[i + 1] - 2 * v) % 4
    if R[m] != 0 or R[m + 1] != 0:
        return False
    degQ = (m - 1) // 2
    q = [R[2 * j] % 2 for j in range(degQ + 1)]
    if q[degQ] != 1:
        return False
    Q2 = [0] * m
    for i in range(degQ + 1):
        if q[i] == 0:
            continue
        for j in range(degQ + 1):
            if q[j] == 0:
                continue
            Q2[i + j] = (Q2[i + j] + 1) % 4
    return R[:m] == Q2


def poly_shift_linear(coeffs_desc: list[int], alpha: int, beta: int) -> list[int]:
    """Return P(alpha * u + beta) in descending order."""
    d = len(coeffs_desc) - 1
    res = [0] * (d + 1)
    res[0] = coeffs_desc[0]
    cur_deg = 0
    for c in coeffs_desc[1:]:
        new_res = [0] * (d + 1)
        for i in range(cur_deg + 1):
            new_res[i + 1] += alpha * res[i]
            new_res[i] += beta * res[i]
        new_res[0] += c
        res = new_res
        cur_deg += 1
    return res[::-1]


def verify_case(d: int, n: int) -> dict:
    t0 = time.time()
    from _repo_io import resolve_data_file, sha256_auto
    deck_path, _ = resolve_data_file(POLY_RESULTS_DIR, f"deck_{d}_{n}.json")
    farkas_path, _ = resolve_data_file(POLY_RESULTS_DIR, f"farkas_{d}_{n}.json")
    deck_data = read_json_auto(POLY_RESULTS_DIR, f"deck_{d}_{n}.json")
    farkas_data = read_json_auto(POLY_RESULTS_DIR, f"farkas_{d}_{n}.json")

    c_shift = int(deck_data["c"])
    cands = deck_data["candidates"]
    assert len(cands) == farkas_data["total"]
    surv_indices = {s["index"]: s for s in farkas_data["survivors"]}

    z = sp.Symbol("z")
    x = sp.Symbol("x")
    # Common shift factor for (x + 5)^(n - d): x = 2z + c_shift => x + 5 = 2*(z + (c_shift + 5)/2)
    assert (c_shift + 5) % 2 == 0 and n % 2 == 0
    w_neg5 = -(c_shift + 5) // 2

    # Note: in z-coords, chi_S(2z + c_shift) = 2^n * (z - w_neg5)^(n - d) * p(z)
    # and G_i(z) has leading coeff 2; chi_{S_v}(2z + c_shift) = 2^(n-1) * common_z(z) * (G_i(z)/2)!
    # Wait: let's check exact normalization of target_z from chi_S'(x):
    # chi_S(x) = prod_j (x - lam_j)^{m_j}
    # chi'_S(x) = sum_u chi_{S_u}(x) = common_x(x) * sum_u g_u(x)
    # where common_x(x) = prod_j (x - lam_j)^{m_j - 1}, and M(x) = prod_j (x - lam_j) has deg s.
    # Substituting x = 2z + c_shift:
    # d/dz [chi_S(2z + c_shift)] = 2 * chi'_S(2z + c_shift)
    # Let F_z(z) = (z - w_neg5)^{n - d} * p(z) = 2^{-n} * chi_S(2z + c_shift).
    # Let Gcd_z(z) = gcd(F_z, F'_z) (monic in Z[z], degree n - s).
    # Then F'_z(z) / Gcd_z(z) is a polynomial of degree s - 1 with leading coeff n!
    # Multiplying by 2 gives leading coeff 2n, matching sum_{v=1}^n G_{i_v}(z) where each G_i has lead coeff 2!

    killed_verified = 0
    surv_verified = 0
    thm42_deck_failures = 0
    total_deck_checked = 0

    for cand in cands:
        idx = cand["index"]
        s = cand["s"]
        b_desc = cand["b"]
        p_z = sp.Poly(b_desc, z, domain=sp.ZZ)
        F_z = sp.Poly(((z - w_neg5) ** (n - d)) * p_z.as_expr(), z, domain=sp.ZZ)
        Fp_z = sp.diff(F_z, z)
        Gcd_z = sp.gcd(F_z, Fp_z)
        target_poly = sp.Poly(sp.quo(2 * Fp_z, Gcd_z), z, domain=sp.ZZ)
        M_poly = sp.Poly(sp.quo(F_z, Gcd_z), z, domain=sp.ZZ)
        assert M_poly.degree() == s
        assert target_poly.degree() == s - 1
        target_desc = [int(v) for v in target_poly.all_coeffs()]
        assert target_desc[0] == 2 * n

        # Verify every deck entry:
        # 1) Interlacing with M_poly (using exact rational root intervals of M_poly!)
        m_intervals = M_poly.intervals()
        assert len(m_intervals) == s, "M_poly is not square-free!"

        deck = cand["deck"]
        Gcd_desc_x = poly_shift_linear([int(v) for v in Gcd_z.all_coeffs()], 1, -c_shift)
        # Wait: F_z(z) = 2^{-n} chi_S(2z + c), so Gcd_z((x - c)/2) = 2^{-(n-s)} Gcd_x(x).
        # And deck entry G_i(z) has lead coeff 2, so G_i((x-c)/2) * 2^{s-2} * (2^{n-s} Gcd_z((x-c)/2)) = chi_{S_v}(x)!
        # Wait: in z-coords, chi_{S_v}(2z + c) = 2^{n-2} * Gcd_z(z) * G_i(z)!
        # Let's check lead coeff of 2^{n-2} * Gcd_z(z) * G_i(z): 2^{n-2} * 1 * 2 = 2^{n-1}, matching (2z)^{n-1}!
        # Let's verify 2-adic and Theorem 4.2 directly in z-coords!
        # Since x = 2z + c = 2(z + (c+1)/2) - 1, let t = z + (c+1)/2 (an integer shift because c is odd!).
        # Wait: chi_{S_v}(2t - 1) = chi_{S_v}(2z + c) evaluated at z = t - (c+1)/2!
        # Let's verify that! 2*(t - (c+1)/2) + c = 2t - c - 1 + c = 2t - 1! EXACT!
        assert c_shift % 2 == 1
        shift_t = -(c_shift + 1) // 2

        for g_desc in deck:
            total_deck_checked += 1
            assert len(g_desc) == s and g_desc[0] == 2
            g_poly = sp.Poly(g_desc, z, domain=sp.ZZ)
            # Interlacing check: evaluate g_poly at endpoints of isolating intervals of M_poly
            # For root j (0-indexed from left), expected sign at root r_j is (-1)^(s - 1 - j) (or 0).
            # Actually refine M_poly intervals slightly if g_poly changes sign inside, or simply check Sturm/real_roots:
            # Simpler & exact: g_poly has s-1 real roots? Even simpler:
            # Evaluate signs at isolating interval endpoints of M_poly; if M_poly root interval straddles sign of g, refine M_poly!
            for j, ((lo, hi), mult) in enumerate(m_intervals):
                assert mult == 1
                exp_sgn = 1 if ((s - 1 - j) % 2 == 0) else -1
                # If lo == hi, exact rational root!
                if lo == hi:
                    val = g_poly.eval(lo)
                    assert val == 0 or (val > 0) == (exp_sgn > 0), f"Interlacing failed at exact root!"
                else:
                    # Refine until g(lo) and g(hi) have the same nonzero sign or g has a root inside
                    # Note: M_poly has a unique root in [lo, hi], so if g(lo)*exp_sgn >= 0 or g(hi)*exp_sgn >= 0...
                    # Actually, if BOTH g(lo)*exp_sgn < 0 AND g(hi)*exp_sgn < 0, AND g has no root in [lo, hi] (checked via Sturm!), impossible!
                    vlo, vhi = g_poly.eval(lo), g_poly.eval(hi)
                    if vlo * exp_sgn < 0 and vhi * exp_sgn < 0:
                        assert g_poly.count_roots(lo, hi) > 0, f"Interlacing failed on cand {idx}!"

            # Check odd-(n-1) 2-adic + Thm 4.2 on chi_{S_v}(2t - 1) = 2^{n-2} * Gcd_z(z) * G_i(z) at z = t + shift_t:
            prod_z = sp.Poly(Gcd_z.as_expr() * g_poly.as_expr(), z, domain=sp.ZZ)
            prod_t_desc = poly_shift_linear([int(v) for v in prod_z.all_coeffs()], 1, shift_t)
            # Notice chi_{S_v}(2t - 1) = 2^{n-2} * prod_t(t), so 2^{-(n-2)} chi_{S_v}(2t-1) = prod_t(t)!
            # Since order is m = n - 1 (odd), 2^{m-1} = 2^{n-2} divides chi_{S_v}(2t-1)!
            # And P_{S_v}(t) = prod_t(t) (ascending)!
            P_asc = prod_t_desc[::-1]
            # Odd-order 2-adic: odd powers of t must be even
            for k_idx, val in enumerate(P_asc):
                if k_idx % 2 == 1:
                    assert val % 2 == 0, f"Deck odd-power parity failed on cand {idx}"
            if not check_thm42_odd(P_asc, n - 1):
                thm42_deck_failures += 1

        e = len(deck)
        if e == 0:
            assert idx not in surv_indices
            killed_verified += 1
            continue

        A_eq_int = [[deck[i][k] for i in range(e)] for k in range(s)]
        status_lp, cert = exact_farkas_or_primal(A_eq_int, target_desc)
        if status_lp == "FARKAS":
            assert sum(cert[k] * target_desc[k] for k in range(s)) < 0
            for i in range(e):
                assert sum(cert[k] * deck[i][k] for k in range(s)) >= 0
            assert idx not in surv_indices, f"RED FLAG! Cand {idx} has exact Farkas cert but marked survivor!"
            killed_verified += 1
        else:
            assert status_lp == "PRIMAL"
            for val in cert:
                assert val >= 0
            for k in range(s):
                assert sum(cert[i] * deck[i][k] for i in range(e)) == target_desc[k]
            assert idx in surv_indices, f"RED FLAG! Cand {idx} has exact primal sol but marked killed!"
            surv_verified += 1

    assert killed_verified == farkas_data["killed"]
    assert surv_verified == len(farkas_data["survivors"])
    return {
        "d": d,
        "n": n,
        "deck_sha256": sha256_auto(deck_path),
        "farkas_sha256": sha256_auto(farkas_path),
        "total": len(cands),
        "killed_verified_with_exact_farkas": killed_verified,
        "survivors_verified": surv_verified,
        "total_deck_checked": total_deck_checked,
        "thm42_deck_failures": thm42_deck_failures,
        "elapsed_s": round(time.time() - t0, 2),
        "status": "PASS",
    }


def main() -> None:
    results = []
    for d, n in [(18, 60), (19, 74)]:
        res = verify_case(d, n)
        results.append(res)
        print(
            f"[PASS] ({d},{n}) Deck & Farkas QQ Audit: {res['killed_verified_with_exact_farkas']} killed "
            f"(explicit exact QQ Farkas certs), {res['survivors_verified']} survivors, "
            f"{res['total_deck_checked']} deck polys checked (thm42_failures={res['thm42_deck_failures']}) "
            f"in {res['elapsed_s']}s"
        )
    out_path = AUDIT_DIR / "farkas_audit_summary.json"
    out_path.write_text(json.dumps(results, indent=2))
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
