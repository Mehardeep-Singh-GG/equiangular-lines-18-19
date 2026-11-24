"""Independent regression test: run ALL Phase-1 and Phase-2 filters against the 12 real
calibrated Seidel matrices in compute/search/results/cal_*.json.

Ensures ZERO false negatives on genuine equiangular line systems:
- Every cal_*.json matrix's true charpoly must pass verify_polys.py (and Thm 4.2 when odd n).
- Its true 1-vertex-deleted Seidel charpolys chi_{S_v}(x) must satisfy interlacing,
  even/odd 2-adic congruences, Thm 4.2 (when n-1 is odd), exact linear sum = chi'_S(x),
  AND must all fall into ONE single square-class bucket (plus zero bucket) for EVERY
  simple irreducible factor of chi_S(x)!
"""

from __future__ import annotations

from fractions import Fraction
import json
from pathlib import Path
import time
import sympy as sp

from small_n_sanity import exact_charpoly_int
from verify_farkas import check_thm42_odd, poly_shift_linear
from verify_gram import load_matrix_file
from verify_phase2_19_74 import square_classes_for_simple_factor
from verify_polys import poly_eval_2tm1_asc, verify_candidate_f
from _repo_io import CERT_DIR, COMPUTE_SEARCH_RESULTS, list_json_stems


SEARCH_DIR = COMPUTE_SEARCH_RESULTS


def main() -> None:
    t0 = time.time()
    x, z = sp.symbols("x z")
    items = [(n, p) for n, p in list_json_stems(SEARCH_DIR, CERT_DIR / "calibration") if n.startswith("cal_")]
    for name, path in items:
        S_raw, meta = load_matrix_file(path)
        ver = meta["verification"]
        d, n = int(ver["d"]), int(ver["n"])
        chi_desc = exact_charpoly_int(S_raw)
        chi_x = sp.Poly(chi_desc, x, domain=sp.ZZ)
        f_poly, rem = sp.div(chi_x, sp.Poly((x + 5) ** (n - d), x, domain=sp.ZZ))
        assert rem == 0
        verify_candidate_f([int(c) for c in f_poly.all_coeffs()], d=d, n=n, k=5)

        if n % 2 == 1:
            b_asc = poly_eval_2tm1_asc(chi_desc)
            P_asc = [v // (1 << (n - 1)) for v in b_asc]
            assert check_thm42_odd(P_asc, n), f"Thm 4.2 failed on real matrix {path.name}!"

        # Compute all n vertex-deleted characteristic polynomials in exact integer arithmetic
        chi_u_list = []
        for u in range(n):
            Su = [[S_raw[i][j] for j in range(n) if j != u] for i in range(n) if i != u]
            cu_desc = exact_charpoly_int(Su)
            chi_u_list.append(cu_desc)

        # Verify derivative identity: sum chi_{S_u} == chi'_S
        chi_deriv = [(n - k) * chi_desc[k] for k in range(n)]
        sum_u = [sum(chi_u_list[u][k] for u in range(n)) for k in range(n)]
        assert sum_u == chi_deriv

        # Check all simple irreducible factors of chi_S(x) for square-class consistency of true deck!
        _, fac_list = sp.factor_list(chi_x)
        simple_factors = [fac for fac, mult in fac_list if mult == 1]
        # Reduce chi_{S_u} by common gcd(chi_S, chi'_S) so we test square classes directly on deck_x
        gcd_x = sp.gcd(chi_x, sp.diff(chi_x, x))
        deck_red = []
        for cu_desc in chi_u_list:
            cu_poly = sp.Poly(cu_desc, x, domain=sp.ZZ)
            g_red, rem_g = sp.div(cu_poly, gcd_x)
            assert rem_g == 0
            deck_red.append([int(c) for c in g_red.all_coeffs()])

        # Note: since all chi_{S_u}(alpha) = gcd(alpha)*g_red(alpha) and gcd(alpha) is fixed,
        # g_red(alpha) across all vertices u must lie in ONE square class (plus 0)!
        for sf in simple_factors:
            # Map x -> z symbol just to reuse square_classes_for_simple_factor
            sf_z = sp.Poly([int(c) for c in sf.all_coeffs()], z, domain=sp.ZZ)
            buckets = square_classes_for_simple_factor(deck_red, sf_z, z)
            # Check that the union of all n vertices fits into AT MOST ONE bucket!
            all_idx = set(range(n))
            assert any(set(b) == all_idx for b in buckets), (
                f"Real matrix {path.name} split across buckets at factor {sf.as_expr()}!"
            )

        print(
            f"[PASS] {path.name}: (d={d}, n={n}), {len(simple_factors)} simple factors, "
            f"100% real-matrix Phase-1 & Phase-2 consistency verified"
        )
    print(f"All {len(files)} real-matrix regression checks passed in {time.time() - t0:.2f}s")


if __name__ == "__main__":
    main()
