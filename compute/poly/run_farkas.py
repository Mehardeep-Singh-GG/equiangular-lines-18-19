import json
import sys
from fractions import Fraction
import numpy as np
import sympy as sp
from scipy.optimize import linprog

def poly_from_b_even(d, b_in):
    w = sp.Symbol('w')
    return sp.Poly(sum(b_in[j] * w**(d - j) for j in range(d + 1)), w, domain=sp.ZZ)

def verify_farkas_exact(A_int, rhs_int, c_int):
    # A_int: list of rows (one per Deck element), each length s
    # Check c_int . row >= 0 for all row in A_int, and c_int . rhs_int < 0
    for row in A_int:
        dot = sum(ci * ri for ci, ri in zip(c_int, row))
        if dot < 0:
            return False
    rhs_dot = sum(ci * ri for ci, ri in zip(c_int, rhs_int))
    return rhs_dot < 0

def solve_farkas(A_int, rhs_int):
    # A_int has shape (m, s): m Deck polynomials, s coefficients (w^(s-1) .. w^0)
    m = len(A_int)
    s = len(rhs_int)
    if m == 0:
        # Empty deck! Certificate is [1, 0, ..., 0] if rhs_int[0] > 0 -> take [-1, 0, ...]
        c_int = [-1] + [0] * (s - 1)
        assert verify_farkas_exact(A_int, rhs_int, c_int)
        return True, c_int, None

    A = np.array(A_int, dtype=np.float64) # m x s
    rhs = np.array(rhs_int, dtype=np.float64)

    # First check primal feasibility: A^T n = rhs, n >= 0
    res_p = linprog(np.zeros(m), A_eq=A.T, b_eq=rhs, bounds=(0, None), method='highs')
    if res_p.success:
        return False, None, res_p.x

    # Find exact Farkas certificate: min c . rhs s.t. A c >= 0, -1 <= c <= 1
    res_d = linprog(rhs, A_ub=-A, b_ub=np.zeros(m), bounds=(-1.0, 1.0), method='highs')
    if res_d.success and res_d.fun < -1e-9:
        c_flt = res_d.x
        for scale in [10**4, 10**6, 10**9, 10**12]:
            c_int = [int(round(v * scale)) for v in c_flt]
            if verify_farkas_exact(A_int, rhs_int, c_int):
                return True, c_int, None

    # Fallback: exact rational Farkas using sympy if near boundary!
    # Or perturb margin: A c >= eps? No, if A c >= 0 has a ray with c . rhs < 0,
    # try requiring c . rhs == -1 and min slack or check!
    res_d2 = linprog(np.zeros(s), A_ub=-A, b_ub=np.zeros(m), A_eq=[rhs], b_eq=[-1.0],
                     bounds=(-1e4, 1e4), method='highs')
    if res_d2.success:
        c_flt = res_d2.x
        for scale in [10**6, 10**9, 10**12, 10**15]:
            c_int = [int(round(v * scale)) for v in c_flt]
            if verify_farkas_exact(A_int, rhs_int, c_int):
                return True, c_int, None

    # If still not certified in exact arithmetic, report inconclusive (conservative!)
    return False, None, None

def main():
    in_deck = sys.argv[1]
    out_summary = sys.argv[2]
    data = json.load(open(in_deck))
    d, n, c_shift = data['d'], data['n'], data['c']
    w0 = (-5 - c_shift) // 2
    w = sp.Symbol('w')
    factor_w0 = sp.Poly((w - w0)**(n - d), w, domain=sp.ZZ)

    killed = 0
    certificates = []
    survivors = []
    for cand in data['candidates']:
        idx = cand['index']
        s = cand['s']
        b_in = cand['b']
        deck = cand['deck']

        Pw = poly_from_b_even(d, b_in)
        Full_w = factor_w0 * Pw
        Dw = sp.gcd(Full_w, Full_w.diff())
        # Compute exact RHS(w) = 2 * Full_w'(w) / Dw(w)
        quo, rem = sp.div(Full_w.diff(), Dw)
        assert rem.is_zero
        RHS_poly = sp.Poly(2 * quo, w, domain=sp.ZZ)
        rhs_coeffs = [int(v) for v in RHS_poly.all_coeffs()]
        # Pad on left if needed (degree is s-1, length s)
        while len(rhs_coeffs) < s:
            rhs_coeffs = [0] + rhs_coeffs
        assert len(rhs_coeffs) == s

        # Each deck element is [b0, b1, ..., b_{s-1}] (descending powers of w!)
        A_int = [[int(v) for v in row] for row in deck]
        ok, cert, primal_x = solve_farkas(A_int, rhs_coeffs)
        if ok:
            killed += 1
            certificates.append({'index': idx, 's': s, 'rhs': rhs_coeffs, 'farkas_cert': cert})
        else:
            survivors.append({
                'index': idx,
                's': s,
                'deck_size': len(deck),
                'b': b_in,
                'Hw_asc': cand['Hw_asc'],
                'primal_sample_n': [round(float(v), 4) for v in primal_x] if primal_x is not None else None,
            })
            print(f"SURVIVOR idx={idx} (s={s}, |Deck|={len(deck)}): b={b_in}")

    print(f"\nSummary for ({d},{n}): total={len(data['candidates'])}, Farkas-killed={killed}, survivors={len(survivors)}")
    with open(out_summary, 'w') as f:
        json.dump({'d': d, 'n': n, 'total': len(data['candidates']), 'killed': killed,
                   'certificates': certificates, 'survivors': survivors}, f, indent=2)

if __name__ == '__main__':
    main()
