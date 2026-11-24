"""Independent clean-room small-n sanity verification for Seidel matrices.

Verifies from first principles using exact integer/SymPy polynomial arithmetic:
1. Trace identities: Tr(S) = 0, Tr(S^2) = n(n-1), top 3 coefficients of chi_S(x).
2. Switching invariance: chi_{D S D}(x) == chi_S(x).
3. Exact 2-adic Seidel congruences on chi_S(2t - 1) for even and odd n,
   plus induced 2-adic congruences on g(y) = f(y - 5) when (x+5)^(n-d) | chi_S(x).
4. Exact Jacobi complementary principal submatrix identities on xI - S:
   - 1-vertex: sum_u chi_{S_u}(x) == chi'_S(x)
   - 2-vertex: chi_{S_u}(x)*chi_{S_v}(x) - chi_S(x)*chi_{S_{uv}}(x) == A_{uv}(x)^2
   - k-vertex (k=3): det(adj(xI - S)[K]) == chi_S(x)^(k-1) * chi_{S[K^c]}(x).

Exhaustive over all 2^C(n-1, 2) switching-canonical Seidel matrices for n=3..6 (1098 total),
using exact integer Faddeev-LeVerrier cross-checked against SymPy Bareiss charpoly/adjugate,
plus random & structured Seidel matrices for n=7..20.
"""

from __future__ import annotations

import itertools
import random
import time
import sympy as sp


def exact_charpoly_int(M: list[list[int]]) -> list[int]:
    """Exact integer characteristic polynomial det(xI - M) via Faddeev-LeVerrier.
    Returns descending coefficients [1, c_{n-1}, ..., c_0] in Z[x].
    Every division by k is exact in Z because charpoly of an integer matrix is in Z[x].
    """
    n = len(M)
    if n == 0:
        return [1]
    coeffs = [1]
    B = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
    for k in range(1, n + 1):
        # C = M * B
        C = [[sum(M[i][r] * B[r][j] for r in range(n)) for j in range(n)] for i in range(n)]
        tr = sum(C[i][i] for i in range(n))
        assert tr % k == 0
        ck = -tr // k
        coeffs.append(ck)
        if k < n:
            B = [[C[i][j] + (ck if i == j else 0) for j in range(n)] for i in range(n)]
    return coeffs


def poly_eval_shift_2t_m1(desc_coeffs: list[int]) -> list[int]:
    """Given P(x) in descending order, compute P(2t - 1) in ascending order [b_0, ..., b_n] in Z."""
    n = len(desc_coeffs) - 1
    # Expand via Horner's rule over lists in Z[t]
    res = [0] * (n + 1)
    res[0] = desc_coeffs[0]
    cur_deg = 0
    for c in desc_coeffs[1:]:
        # res = res * (2t - 1) + c
        new_res = [0] * (n + 1)
        for i in range(cur_deg + 1):
            new_res[i + 1] += 2 * res[i]
            new_res[i] -= res[i]
        new_res[0] += c
        res = new_res
        cur_deg += 1
    return res


def poly_div_linear(desc_coeffs: list[int], root: int) -> tuple[list[int], int]:
    """Exact synthetic division of P(x) by (x - root). Returns (quotient_desc, remainder)."""
    q = []
    rem = 0
    for c in desc_coeffs:
        val = c + rem * root
        q.append(val)
        rem = val
    remainder = q.pop()
    return q, remainder


def poly_shift_ym5(desc_coeffs: list[int]) -> list[int]:
    """Compute f(y - 5) in descending order using exact integer Horner arithmetic."""
    d = len(desc_coeffs) - 1
    # ascending representation of f(y - 5)
    res = [0] * (d + 1)
    res[0] = desc_coeffs[0]
    cur_deg = 0
    for c in desc_coeffs[1:]:
        new_res = [0] * (d + 1)
        for i in range(cur_deg + 1):
            new_res[i + 1] += res[i]
            new_res[i] -= 5 * res[i]
        new_res[0] += c
        res = new_res
        cur_deg += 1
    return res[::-1]


def v2(val: int) -> int:
    if val == 0:
        return 10**9
    val = abs(val)
    return (val & -val).bit_length() - 1


def verify_fast_int(S: list[list[int]]) -> dict:
    n = len(S)
    # 1. Structure & traces
    for i in range(n):
        assert S[i][i] == 0
        for j in range(i + 1, n):
            assert S[i][j] == S[j][i] and S[i][j] in (1, -1)

    chi = exact_charpoly_int(S)
    assert chi[0] == 1 and chi[1] == 0 and chi[2] == -n * (n - 1) // 2

    # 2. 2-adic congruences on chi_S(2t - 1)
    b_asc = poly_eval_shift_2t_m1(chi)
    assert b_asc[n] == 2**n
    assert b_asc[n - 1] == -n * (2 ** (n - 1))
    assert b_asc[n - 2] == 0
    if n % 2 == 0:
        for k, bk in enumerate(b_asc):
            assert v2(bk) >= n, f"Even n={n}: v2(b_{k})={v2(bk)} < {n}"
    else:
        for k, bk in enumerate(b_asc):
            req = n if (k % 2 == 1) else (n - 1)
            assert v2(bk) >= req, f"Odd n={n}: v2(b_{k})={v2(bk)} < {req}"

    # 3. Shifted g(y) congruence when (x+5) divides chi_S(x)
    cur = list(chi)
    mult_m5 = 0
    while True:
        q, rem = poly_div_linear(cur, -5)
        if rem == 0:
            mult_m5 += 1
            cur = q
        else:
            break
    for d in {n, n - mult_m5}:
        f_desc = list(chi)
        for _ in range(n - d):
            f_desc, rem = poly_div_linear(f_desc, -5)
            assert rem == 0
        a_desc = poly_shift_ym5(f_desc)
        for k, ak in enumerate(a_desc):
            if n % 2 == 0:
                assert v2(ak) >= k
            else:
                req = k if (k % 2 == 0) else (k - 1)
                assert v2(ak) >= req

    # 4. 1-vertex Jacobi: sum_u chi_{S_u}(x) == chi'_S(x)
    sum_u = [0] * n
    for u in range(n):
        Su = [[S[i][j] for j in range(n) if j != u] for i in range(n) if i != u]
        cu = exact_charpoly_int(Su)
        for k in range(n):
            sum_u[k] += cu[k]
    chi_deriv = [(n - k) * chi[k] for k in range(n)]
    assert sum_u == chi_deriv, "1-vertex Jacobi derivative identity failed!"

    return {"mult_m5": mult_m5, "chi": chi}


def verify_sympy_full(S_list: list[list[int]], check_k3: bool = False) -> dict:
    """Full SymPy verification: cross-checks exact_charpoly_int, switching invariance,
    2-vertex and 3-vertex Jacobi adjugate identities."""
    n = len(S_list)
    x = sp.Symbol("x")
    S = sp.Matrix(S_list)
    chi = sp.Poly(S.charpoly(x).as_expr(), x, domain=sp.ZZ)
    assert [int(c) for c in chi.all_coeffs()] == exact_charpoly_int(S_list)

    # Switching invariance
    D = sp.diag(*[random.choice([1, -1]) for _ in range(n)])
    chi_sw = sp.Poly((D * S * D).charpoly(x).as_expr(), x, domain=sp.ZZ)
    assert chi == chi_sw

    # Verify fast integer checks as well
    fast_res = verify_fast_int(S_list)

    # 2-vertex (and optional 3-vertex) Jacobi on xI - S
    M = x * sp.eye(n) - S
    chi_u = []
    for u in range(n):
        idx = [i for i in range(n) if i != u]
        chi_u.append(sp.Poly(S.extract(idx, idx).charpoly(x).as_expr(), x, domain=sp.ZZ))

    if n <= 8:
        adj_M = M.adjugate()
        for u in range(n):
            assert sp.Poly(adj_M[u, u], x, domain=sp.ZZ) == chi_u[u]
        for u in range(n):
            for v in range(u + 1, n):
                idx_uv = [i for i in range(n) if i not in (u, v)]
                cuv = sp.Poly(S.extract(idx_uv, idx_uv).charpoly(x).as_expr(), x, domain=sp.ZZ)
                auv = sp.Poly(adj_M[u, v], x, domain=sp.ZZ)
                assert chi_u[u] * chi_u[v] - chi * cuv == auv * auv
        if check_k3 and n >= 4:
            K = [0, 1, 2]
            Kc = [i for i in range(n) if i not in K]
            cKc = sp.Poly(S.extract(Kc, Kc).charpoly(x).as_expr(), x, domain=sp.ZZ)
            det_adj_K = sp.Poly(adj_M.extract(K, K).det(), x, domain=sp.ZZ)
            assert det_adj_K == (chi ** 2) * cKc
    else:
        # For n > 8, evaluate at n+1 integer points to verify polynomial identity exactness without slow symbolic det
        for u, v in [(0, 1), (0, n - 1), (n // 2 - 1, n // 2)]:
            idx_uv = [i for i in range(n) if i not in (u, v)]
            cuv = exact_charpoly_int([[S_list[i][j] for j in idx_uv] for i in idx_uv])
            cu_list = exact_charpoly_int([[S_list[i][j] for j in range(n) if j != u] for i in range(n) if i != u])
            cv_list = exact_charpoly_int([[S_list[i][j] for j in range(n) if j != v] for i in range(n) if i != v])
            # Evaluate LHS = chi_u(x)*chi_v(x) - chi(x)*chi_{uv}(x) at integer points x = 0..2n-2
            # Wait: LHS has degree <= 2n-2 and must equal A_{uv}(x)^2 at all points; check at 2n-1 points by exact integer det!
            rows = [i for i in range(n) if i != v]
            cols = [i for i in range(n) if i != u]
            for xv in range(-2, 2 * n - 3):
                # evaluate polynomials
                def eval_p(p_desc: list[int], val: int) -> int:
                    acc = 0
                    for c in p_desc:
                        acc = acc * val + c
                    return acc
                lhs_val = eval_p(cu_list, xv) * eval_p(cv_list, xv) - eval_p(fast_res["chi"], xv) * eval_p(cuv, xv)
                M_num = sp.Matrix([[xv if i == j else -S_list[i][j] for j in cols] for i in rows])
                auv_val = ((-1) ** (u + v)) * int(M_num.det())
                assert lhs_val == auv_val * auv_val, f"2-vertex Jacobi point check failed at x={xv}"

    return fast_res


def main() -> None:
    t0 = time.time()
    random.seed(20261123)
    total_checked = 0

    # Exhaustive for n=3, 4, 5, 6
    for n in [3, 4, 5, 6]:
        pairs = [(i, j) for i in range(1, n) for j in range(i + 1, n)]
        count = 0
        for bits in itertools.product([1, -1], repeat=len(pairs)):
            S = [[0] * n for _ in range(n)]
            for i in range(1, n):
                S[0][i] = S[i][0] = 1
            for (i, j), b in zip(pairs, bits):
                S[i][j] = S[j][i] = b
            if n <= 5 or count < 32:
                verify_sympy_full(S, check_k3=(n >= 4 and count < 10))
            else:
                verify_fast_int(S)
            count += 1
        total_checked += count
        print(f"[PASS] n={n}: exhaustively verified all {count} switching-canonical Seidel matrices")

    # Random n=7..20
    for n, trials in [(7, 50), (8, 30), (9, 20), (10, 15), (12, 10), (16, 5), (20, 3)]:
        for tr in range(trials):
            S = [[0] * n for _ in range(n)]
            for i in range(n):
                for j in range(i + 1, n):
                    b = random.choice([1, -1])
                    S[i][j] = S[j][i] = b
            if tr < 3:
                verify_sympy_full(S, check_k3=(n <= 8))
            else:
                verify_fast_int(S)
            total_checked += 1
        print(f"[PASS] n={n}: verified {trials} random Seidel matrices")

    # Structured Seidel matrices: C5+apex (n=6), Petersen (n=10), 2*C6 (n=12, mult(-5)>=1)
    C5_apex = [[0] * 6 for _ in range(6)]
    for i in range(1, 6):
        C5_apex[0][i] = C5_apex[i][0] = 1
    for i in range(1, 6):
        for j in range(i + 1, 6):
            diff = min((j - i) % 5, (i - j) % 5)
            C5_apex[i][j] = C5_apex[j][i] = -1 if diff == 1 else 1
    verify_sympy_full(C5_apex, check_k3=True)

    pet_edges = [
        (0,1),(1,2),(2,3),(3,4),(4,0),
        (5,7),(7,9),(9,6),(6,8),(8,5),
        (0,5),(1,6),(2,7),(3,8),(4,9),
    ]
    S_pet = [[0 if i == j else 1 for j in range(10)] for i in range(10)]
    for u, v in pet_edges:
        S_pet[u][v] = S_pet[v][u] = -1
    verify_sympy_full(S_pet)

    S_2C6 = [[0 if i == j else 1 for j in range(12)] for i in range(12)]
    for base in (0, 6):
        for k in range(6):
            u, v = base + k, base + (k + 1) % 6
            S_2C6[u][v] = S_2C6[v][u] = -1
    res_2c6 = verify_sympy_full(S_2C6)
    assert res_2c6["mult_m5"] >= 1
    total_checked += 3
    print(f"[PASS] Structured matrices (C5+apex n=6, Petersen n=10, 2*C6 n=12 with mult(-5)={res_2c6['mult_m5']})")
    print(f"ALL SMALL-N SANITY CHECKS PASSED ({total_checked} matrices) in {time.time() - t0:.2f}s")


if __name__ == "__main__":
    main()
