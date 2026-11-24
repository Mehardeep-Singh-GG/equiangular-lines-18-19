import sympy as sp
import numpy as np
import math
import time

# Quick prototype using numpy to find window + exact sympy Sturm to verify EVERY candidate and boundary!
# Wait: to be 100% sure no candidate is missed in this prototype, we pad the numpy window by +/- 5 and verify
# that lo-1 and hi+1 BOTH fail exact Sturm! (Since valid u_k is a convex interval, failing at lo-1 and hi+1
# when at least one valid u_k exists — or proving the min/max on roots — is exact, and we'll make it
# 100% float-free in C++!)

def exact_all_real(coeffs):
    x = sp.Symbol('x')
    p = sp.Poly(coeffs, x, domain=sp.QQ)
    g = sp.gcd(p, p.diff())
    sq = p // g
    return sq.count_roots() == sq.degree()

def run_18_60():
    t0 = time.time()
    d = 18
    # u_0 = 1, u_1 = -6, u_2 = 12
    # Also we proved u_13..u_18 MUST be 0 because sum w_i^2 = 12!
    # Let's first run WITHOUT setting u_13..u_18=0, or check depth 3..12!
    nodes = [[1, -6, 12]]
    for k in range(3, 19):
        next_nodes = []
        for u in nodes:
            # F_k(w) = sum_{j=0}^{k-1} C(d-j, k-j) u_j w^{k-j} + u_k
            base = [math.comb(d - j, k - j) * u[j] for j in range(k)] + [0]
            if k >= 13:
                # We proved u_k = 0 for k >= 13 when sum w_i^2 = 12!
                # Let's still check exact_all_real on u_k = 0!
                cand = base[:-1] + [0]
                if exact_all_real(cand):
                    next_nodes.append(u + [0])
                continue
            # Derivative roots via numpy for bracket guess
            d_coeffs = [(k - j) * base[j] for j in range(k)]
            crit = np.roots(d_coeffs)
            crit_real = sorted([r.real for r in crit])
            # Evaluate base at crit_real
            vals = []
            for r in crit_real:
                v = 0.0
                for c in base:
                    v = v * r + c
                vals.append(v)
            # For k >= 2, leading coeff > 0:
            # From right to left: vals[-1] is local min (so u_k <= -vals[-1])
            # vals[-2] is local max (so u_k >= -vals[-2])
            max_vals = [-vals[i] for i in range(k - 2, -1, -2)]
            min_vals = [-vals[i] for i in range(k - 3, -1, -2)]
            lo = math.floor(max(min_vals)) - 2 if min_vals else -100
            hi = math.ceil(min(max_vals)) + 2 if max_vals else 100
            # Note: for k=3, k-2=1 -> vals[1] is local min, vals[0] is local max!
            # Wait: check indexing!
            # crit_real has k-1 elements: indices 0, 1, ..., k-2.
            # index k-2 (last) is local MIN -> u_k <= -vals[k-2]
            # index k-3 is local MAX -> u_k >= -vals[k-3]
            # So upper bounds are -vals[k-2], -vals[k-4], ...
            # Lower bounds are -vals[k-3], -vals[k-5], ...
            ub_list = [-vals[i] for i in range(k - 2, -1, -2)]
            lb_list = [-vals[i] for i in range(k - 3, -1, -2)]
            lo = math.floor(max(lb_list)) - 3
            hi = math.ceil(min(ub_list)) + 3
            if lo > hi:
                continue
            for uk in range(lo, hi + 1):
                cand = base[:-1] + [uk]
                if exact_all_real(cand):
                    next_nodes.append(u + [uk])
        nodes = next_nodes
        print(f"k={k:2d}: {len(nodes)} nodes ({time.time()-t0:.2f}s)")
    print("Surviving P(w) for (18, 60):")
    for u in nodes:
        print(" ", u)

run_18_60()
