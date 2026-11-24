import sympy as sp
from fractions import Fraction
import math
import time

def exact_num_real_roots_sturm(coeffs):
    # coeffs in descending order: [a_0, a_1, ..., a_k], a_0 > 0
    # Wait: Sturm's theorem on squarefree part!
    # Actually sympy.Poly(coeffs, x).count_roots() counts distinct real roots,
    # to count with multiplicity we can check GCD or divide by GCD(p, p').
    # Wait: let's use exact Hankel / Sylvester / Sturm via sympy or pure Fraction!
    x = sp.Symbol('x')
    p = sp.Poly(coeffs, x, domain=sp.QQ)
    # To check ALL roots real (with multiplicity):
    # iteratively divide by gcd(p, p')? No! p has all roots real iff sqfree(p) has deg(sqfree) distinct real roots!
    # Even simpler: p.real_roots() is exact? Better: p_sq = p // gcd(p, p.diff()) -> count_roots() == p_sq.degree()!
    g = sp.gcd(p, p.diff())
    sq = p // g
    return sq.count_roots() == sq.degree()

def test_rolle_18_60():
    # For (18, 60), c=11: P(w) monic deg 18, sum w = 6, sum w^2 = 12
    # u_0 = 1, u_1 = -6, u_2 = 12
    d = 18
    u = [1, -6, 12]
    # Let's check exact bounds at step k=3!
    # F_k(w) = sum_{j=0}^k C(d-j, k-j) u_j w^{k-j}  (divided by 1)
    # Wait: P^{(d-k)}(w) / (d-k)! = sum_{j=0}^k C(d-j, d-k) u_j w^{k-j} = sum_{j=0}^k C(d-j, k-j) u_j w^{k-j}
    # Check: for j=0, C(d, k) w^k. For j=k, C(d-k, 0) u_k = u_k!
    # Let's compute bounds on u_3 using Rolle on F_3(w) = C(18,3) w^3 + C(17,2) u_1 w^2 + C(16,1) u_2 w + u_3
    # C(18,3) = 816, C(17,2)*(-6) = 136*(-6) = -816, C(16,1)*12 = 192
    # F_3(w) = 816 w^3 - 816 w^2 + 192 w + u_3
    # F_3'(w) = 2448 w^2 - 1632 w + 192 = 48 * (51 w^2 - 34 w + 4)
    # Disc = 34^2 - 4*51*4 = 1156 - 816 = 340
    # Let's check integer u_3 for which F_3 has 3 real roots!
    valid_u3 = []
    for u3 in range(-200, 200):
        coeffs = [math.comb(18, 3), math.comb(17, 2)*(-6), math.comb(16, 1)*12, u3]
        if exact_num_real_roots_sturm(coeffs):
            valid_u3.append(u3)
    print(f"Step k=3: valid u3 count = {len(valid_u3)}, range = [{min(valid_u3)}, {max(valid_u3)}]")

    # Also check how many u4 are valid for each u3!
    total_u4 = 0
    for u3 in valid_u3:
        # F_4(w) = C(18,4) w^4 + C(17,3)(-6) w^3 + C(16,2)(12) w^2 + C(15,1)(u3) w + u4
        # Wait: find range using float critical points + exact verify margins!
        c0 = math.comb(18, 4)
        c1 = math.comb(17, 3) * (-6)
        c2 = math.comb(16, 2) * 12
        c3 = math.comb(15, 1) * u3
        # derivative roots via numpy for quick range check (NOT pruning!)
        import numpy as np
        roots = np.roots([4*c0, 3*c1, 2*c2, c3])
        roots = sorted([r.real for r in roots])
        vals = [c0*r**4 + c1*r**3 + c2*r**2 + c3*r for r in roots]
        # for deg 4 (>0 leading), local mins at roots[0], roots[2], local max at roots[1]
        lo = math.floor(-vals[1]) - 2
        hi = math.ceil(-min(vals[0], vals[2])) + 2
        cnt = 0
        for u4 in range(lo, hi+1):
            if exact_num_real_roots_sturm([c0, c1, c2, c3, u4]):
                cnt += 1
        total_u4 += cnt
    print(f"Step k=4: total (u3, u4) pairs = {total_u4}")

test_rolle_18_60()
