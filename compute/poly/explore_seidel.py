import sympy as sp
import itertools
import random

def all_seidel_polys(n):
    # Fix first row to +1 (by switching equivalence, chi_S is invariant under switching!)
    # Wait: switching D S D has the SAME characteristic polynomial!
    # So we can fix the first row (entries 1..n-1) to all +1!
    # Remaining edges: (n-1)*(n-2)//2
    edges = [(i, j) for i in range(1, n) for j in range(i + 1, n)]
    m = len(edges)
    x = sp.Symbol('x')
    t = sp.Symbol('t')
    polys = set()
    for bits in range(1 << m):
        S = sp.zeros(n, n)
        for j in range(1, n):
            S[0, j] = S[j, 0] = 1
        for k, (i, j) in enumerate(edges):
            val = -1 if (bits >> k) & 1 else 1
            S[i, j] = S[j, i] = val
        p = sp.Poly(S.charpoly(x).as_expr(), x)
        polys.add(tuple(p.all_coeffs()))
    return polys

for n in [4, 5, 6]:
    polys = all_seidel_polys(n)
    x, t = sp.symbols('x t')
    print(f"=== n = {n}, distinct charpolys = {len(polys)} ===")
    # Check chi_S(2t - 1) / 2^(n-1) mod 2 and mod 4
    mod2_set = set()
    mod4_set = set()
    for coeffs in polys:
        p = sp.Poly(coeffs, x)
        q = sp.Poly(p.as_expr().subs(x, 2*t - 1), t)
        q_coeffs = q.all_coeffs()
        # check divisibility by 2^(n-1)
        divs = [c % (2**(n-1)) for c in q_coeffs]
        assert all(d == 0 for d in divs), f"Failed 2^(n-1) div for {coeffs}"
        r_coeffs = [c // (2**(n-1)) for c in q_coeffs]
        mod2_set.add(tuple(c % 2 for c in r_coeffs))
        mod4_set.add(tuple(c % 4 for c in r_coeffs))
    print(f"  distinct (chi(2t-1)/2^(n-1)) mod 2 ({len(mod2_set)}): {sorted(mod2_set)}")
    print(f"  distinct (chi(2t-1)/2^(n-1)) mod 4 ({len(mod4_set)}): {sorted(mod4_set)[:10]}")
