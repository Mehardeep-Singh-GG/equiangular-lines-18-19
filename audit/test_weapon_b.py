"""Independent clean-room verification & regression test for Weapon B
(2-Adic Hensel Unit-Eigenvector Theorem for odd n).

Tests:
1. Exhaustive odd n=3, 5 and random odd n=7, 9, 11, 13, 15, 19 Seidel matrices.
2. ALL 9 real calibrated (18, 57) Seidel matrices in compute/search/results/cal_18_57_*.json.
"""

from __future__ import annotations

import itertools
import json
from pathlib import Path
import random
import time
import sympy as sp

from small_n_sanity import exact_charpoly_int
from verify_gram import load_matrix_file
from _repo_io import CERT_DIR, COMPUTE_SEARCH_RESULTS, list_json_stems


SEARCH_DIR = COMPUTE_SEARCH_RESULTS if COMPUTE_SEARCH_RESULTS.is_dir() else (CERT_DIR / "calibration")


def hensel_lift_root_mod_2k(q_desc: list[int], k_bits: int = 128) -> int:
    """Given monic q(x) in Z[x] with q(0) even and q'(0) odd, Hensel-lift the unique root in 2*Z_2 mod 2^k_bits."""
    assert q_desc[-1] % 2 == 0, f"q(0) is not even: {q_desc}"
    # q'(0) is q_desc[-2] (second-to-last coeff)
    assert len(q_desc) >= 2 and q_desc[-2] % 2 == 1, f"q'(0) is not odd: {q_desc}"

    deg = len(q_desc) - 1
    qp_desc = [(deg - i) * q_desc[i] for i in range(deg)]

    def eval_mod(desc: list[int], x_val: int, mod: int) -> int:
        acc = 0
        for c in desc:
            acc = (acc * x_val + c) % mod
        return acc

    r = 0
    prec = 2
    while prec < (1 << k_bits):
        next_prec = min(1 << k_bits, prec * prec)
        q_val = eval_mod(q_desc, r, next_prec)
        qp_val = eval_mod(qp_desc, r, next_prec)
        assert qp_val % 2 == 1
        inv_qp = pow(qp_val, -1, next_prec)
        r = (r - q_val * inv_qp) % next_prec
        prec = next_prec
    assert eval_mod(q_desc, r, 1 << k_bits) == 0
    return r


def verify_weapon_b_on_matrix(S: list[list[int]], label: str) -> dict:
    n = len(S)
    assert n % 2 == 1
    x = sp.Symbol("x")
    chi_desc = exact_charpoly_int(S)
    chi_poly = sp.Poly(chi_desc, x, domain=sp.ZZ)
    _, fac_list = sp.factor_list(chi_poly)

    # Find unique irreducible factor q_0 with q_0(0) even and q_0'(0) odd
    q0_cands = []
    for fac, mult in fac_list:
        cs = [int(c) for c in fac.all_coeffs()]
        if cs[-1] % 2 == 0 and len(cs) >= 2 and cs[-2] % 2 == 1:
            q0_cands.append((cs, mult))
    assert len(q0_cands) == 1, f"{label}: expected 1 q0 factor, got {q0_cands}"
    q0_desc, mult_q0 = q0_cands[0]
    assert mult_q0 == 1, f"{label}: q0 multiplicity {mult_q0} != 1!"

    K_BITS = 160
    MOD = 1 << K_BITS
    lam0 = hensel_lift_root_mod_2k(q0_desc, k_bits=K_BITS)
    q0_poly = sp.Poly(q0_desc, x, domain=sp.ZZ)

    def eval_mod(desc: list[int], val: int) -> int:
        acc = 0
        for c in desc:
            acc = (acc * val + c) % MOD
        return acc

    er_set = set()
    for u in range(n):
        Su = [[S[i][j] for j in range(n) if j != u] for i in range(n) if i != u]
        cu_desc = exact_charpoly_int(Su)
        cu_poly = sp.Poly(cu_desc, x, domain=sp.ZZ)
        assert not sp.rem(cu_poly, q0_poly).is_zero, f"{label}: q0 divides chi_S_{u}!"
        val = eval_mod(cu_desc, lam0)
        assert val != 0, f"{label}: v_2(chi_S_{u}(lam0)) >= {K_BITS}, increase K_BITS!"
        e_u = (val & -val).bit_length() - 1
        r_u = (val >> e_u) % 8
        er_set.add((e_u, r_u))

    assert len(er_set) == 1, f"{label}: Weapon B FAILED! Multiple (e, r_u mod 8) across vertices: {er_set}"
    e0, r0 = next(iter(er_set))

    # Verify chi'_S(lam0) == 2^e0 * r0 * n (mod 2^(e0+3))
    chi_p_desc = [(n - i) * chi_desc[i] for i in range(n)]
    chip_val = eval_mod(chi_p_desc, lam0)
    assert e0 + 3 <= K_BITS
    assert (chip_val - (n * r0 << e0)) % (1 << (e0 + 3)) == 0, f"{label}: chi'_S(lam0) congruence failed!"

    return {"q0_deg": len(q0_desc) - 1, "e": e0, "r_mod8": r0}


def main() -> None:
    t0 = time.time()
    random.seed(2026)

    # 1. Exhaustive n=3, 5 and random n=7..19
    small_cnt = 0
    for n in [3, 5]:
        pairs = [(i, j) for i in range(1, n) for j in range(i + 1, n)]
        for bits in itertools.product([1, -1], repeat=len(pairs)):
            S = [[0] * n for _ in range(n)]
            for i in range(1, n):
                S[0][i] = S[i][0] = 1
            for (i, j), b in zip(pairs, bits):
                S[i][j] = S[j][i] = b
            verify_weapon_b_on_matrix(S, f"n={n}")
            small_cnt += 1
    for n in [7, 9, 11, 13, 15, 19]:
        for tr in range(10):
            S = [[0] * n for _ in range(n)]
            for i in range(n):
                for j in range(i + 1, n):
                    S[i][j] = S[j][i] = random.choice([1, -1])
            verify_weapon_b_on_matrix(S, f"n={n}_tr={tr}")
            small_cnt += 1
    print(f"[PASS] Weapon B verified on {small_cnt} odd-n Seidel matrices (n=3..19)")

    # 2. ALL 9 real calibrated (18, 57) Seidel matrices
    cal_items = [(n, p) for n, p in list_json_stems(SEARCH_DIR, CERT_DIR / "calibration") if n.startswith("cal_18_57_")]
    assert len(cal_items) == 9, f"Expected 9 calibrated 18_57 matrices, got {len(cal_items)}"
    for name, path in cal_items:
        S_raw, _ = load_matrix_file(path)
        res = verify_weapon_b_on_matrix(S_raw, name)
        print(f"[PASS] {name}: Weapon B holds! q0_deg={res['q0_deg']}, e={res['e']}, r_mod8={res['r_mod8']}")

    print(f"ALL WEAPON B REGRESSION CHECKS PASSED in {time.time() - t0:.2f}s")


if __name__ == "__main__":
    main()
