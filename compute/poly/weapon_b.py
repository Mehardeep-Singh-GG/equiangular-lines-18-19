"""
Weapon B: 2-Adic Hensel Unit-Eigenvector Theorem for odd-n Seidel matrices.
100% exact integer / Z/2^K Z arithmetic (ZERO floating-point trust).

Theorem: For any Seidel matrix S of odd order n, chi_S(x) == x(x+1)^(n-1) (mod 2),
so chi_S has a unique simple root lambda_0 in 2*Z_2, lying in a unique multiplicity-1
irreducible factor q_0(x) | chi_S(x) with q_0(0) even and q_0'(0) odd.
Any primitive eigenvector v in Z_2^n satisfies (J_n - I_n)v == 0 (mod 2), forcing
v == 1 (mod 2), so v_u^2 == 1 (mod 8) for all u = 1..n.
Since chi_{S_u}(lambda_0) = C * v_u^2 with C = chi_S'(lambda_0) / ||v||_2^2 and
sum_u v_u^2 == n (mod 8), letting E = v_2(chi_S'(lambda_0)) and R = (chi_S'(lambda_0)/2^E) mod 8,
EVERY occurring vertex deletion S_u MUST satisfy:
  (1) q_0(x) does not divide chi_{S_u}(x),
  (2) v_2(chi_{S_u}(lambda_0)) == E, and
  (3) (chi_{S_u}(lambda_0) / 2^E) mod 8 == (R * pow(n, -1, 8)) mod 8.
"""
import glob
import json
import os
import sys
import sympy as sp
import numpy as np


def hensel_lift_root_2adic(q_coeffs_desc, K=64):
    """
    Given integer polynomial q(x) in descending powers with q(0) even and q'(0) odd,
    uniquely Hensel-lift the root lambda_0 == 0 (mod 2) modulo 2^K.
    """
    # Convert to ascending coefficients [c_0, c_1, ..., c_d]
    c = [int(v) for v in reversed(q_coeffs_desc)]
    assert c[0] % 2 == 0 and len(c) >= 2 and c[1] % 2 == 1, "q_0 must have q_0(0) even, q_0'(0) odd"
    # Newton iteration: lam <- lam - q(lam)/q'(lam) mod 2^prec
    lam = 0
    prec = 1
    while prec < K:
        next_prec = min(K, 2 * prec)
        mod = 1 << next_prec
        # Horner evaluation of q(lam) and q'(lam) mod 2^next_prec
        qv = 0
        qpv = 0
        for k in range(len(c) - 1, -1, -1):
            qv = (qv * lam + c[k]) % mod
            if k >= 1:
                qpv = (qpv * lam + k * c[k]) % mod
        assert qpv % 2 == 1
        inv_qp = pow(qpv, -1, mod)
        lam = (lam - qv * inv_qp) % mod
        prec = next_prec
    return lam


def eval_poly_mod_2k(coeffs_desc, lam, K):
    mod = 1 << K
    acc = 0
    for c in coeffs_desc:
        acc = (acc * lam + int(c)) % mod
    return acc


def exact_2adic_val_and_res8(poly_x, q0_poly, x_sym):
    """
    Exact (v_2(P(lambda_0)), (P(lambda_0) / 2^e) mod 8) where q0(lambda_0) == 0 in 2*Z_2.
    Returns None if q0 | poly_x (exact divisibility in Q[x]).
    Automatically doubles Hensel precision K until v_2 <= K - 4.
    """
    if sp.rem(poly_x, q0_poly).is_zero:
        return None
    p_cs = [int(v) for v in poly_x.all_coeffs()]
    q_cs = [int(v) for v in q0_poly.all_coeffs()]
    K = 64
    while True:
        lam = hensel_lift_root_2adic(q_cs, K)
        val = eval_poly_mod_2k(p_cs, lam, K)
        if val != 0:
            e = (val & -val).bit_length() - 1
            if e <= K - 4:
                r8 = (val >> e) & 7
                return (e, r8)
        K *= 2
        if K > 4096:
            raise RuntimeError("Hensel precision exceeded 4096 bits without stabilizing")


def find_q0_factor(chi_S_poly, x_sym):
    facs = sp.factor_list(chi_S_poly.as_expr())[1]
    cands = []
    for fac, mult in facs:
        fp = sp.Poly(fac, x_sym, domain=sp.ZZ)
        c0 = int(fp.eval(0))
        c1 = int(fp.diff().eval(0))
        if c0 % 2 == 0 and c1 % 2 == 1:
            assert mult == 1, f"q0 has mult {mult} != 1!"
            cands.append(fp)
    assert len(cands) == 1, f"Expected unique q0, got {len(cands)}: {cands}"
    return cands[0]


def test_real_matrices():
    from pathlib import Path
    _root = Path(__file__).resolve().parents[2]
    x = sp.Symbol("x")
    cal_dir = _root / "compute" / "search" / "results"
    if not list(cal_dir.glob("cal_18_57_*.json")):
        cal_dir = _root / "certificates" / "calibration"
    files = sorted(str(p) for p in cal_dir.glob("cal_18_57_*.json"))
    assert len(files) == 9
    for fp in files:
        obj = json.load(open(fp))
        S_np = np.array(obj["S"], dtype=int)
        n = S_np.shape[0]
        assert n == 57
        S = sp.Matrix(obj["S"])
        chi = sp.Poly(S.charpoly(x).as_expr(), x, domain=sp.ZZ)
        q0 = find_q0_factor(chi, x)
        chi_p = chi.diff()
        E, R = exact_2adic_val_and_res8(chi_p, q0, x)
        target_r = (R * pow(n, -1, 8)) & 7
        seen_vals = set()
        for u in range(n):
            Su = sp.Matrix(np.delete(np.delete(S_np, u, 0), u, 1))
            chi_u = sp.Poly(Su.charpoly(x).as_expr(), x, domain=sp.ZZ)
            res_u = exact_2adic_val_and_res8(chi_u, q0, x)
            assert res_u is not None, f"q0 divided chi_Su at {fp} u={u}"
            eu, ru = res_u
            seen_vals.add((eu, ru))
            assert (eu, ru) == (E, target_r), f"Weapon B MISMATCH at {fp} u={u}: got {(eu, ru)} != {(E, target_r)}"
        print(f"PASS {os.path.basename(fp)}: q0={q0.as_expr()}, target=(E={E}, r={target_r}), all 57/57 vertices matched!")


if __name__ == "__main__":
    if len(sys.argv) == 1 or sys.argv[1] == "--test-real":
        test_real_matrices()
