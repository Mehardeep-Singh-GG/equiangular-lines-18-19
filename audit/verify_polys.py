"""Independent clean-room exact verifier for candidate characteristic polynomials.

Verifies any candidate f(x) (where chi_S(x) = (x+5)^(n-d) * f(x)) or g(y) = f(y-5)
using ONLY exact integer and rational arithmetic (ZERO floating point):
1. Degree d, monic, integer coefficients.
2. Exact trace: sum(lambda_i) = 5(n-d) <=> sum(mu_i) = 5n <=> a_1 = -5n.
3. Exact sum-of-squares: sum(lambda_i^2) = n(n-1) - 25(n-d) <=> a_2 = 12*n*(n-1).
4. Exact totally-real >= -5 check via square-free decomposition + independent
   pure-QQ Sturm sequence (cross-checked against SymPy count_roots).
5. Exact 2-adic Seidel congruences on chi_S(2t - 1) and on g(y) coefficients a_k.
"""

from __future__ import annotations

import math
from fractions import Fraction
import sympy as sp


def eval_poly_q(coeffs_desc: list[Fraction], val: Fraction) -> Fraction:
    acc = Fraction(0)
    for c in coeffs_desc:
        acc = acc * val + c
    return acc


def _primitive_int(coeffs: list[int]) -> list[int]:
    """Divide integer polynomial by positive gcd of its coefficients (preserves all root signs!)."""
    g = 0
    for c in coeffs:
        g = math.gcd(g, abs(c))
        if g == 1:
            return coeffs
    if g <= 1:
        return coeffs
    return [c // g for c in coeffs]


def poly_prem_int(num: list[int], den: list[int]) -> list[int]:
    """Exact positive pseudo-remainder in Z[y]: multiplies num by den[0]^2 (positive!)
    at each elimination step so sign of remainder is strictly preserved (valid Sturm sequence!)."""
    num = list(num)
    while num and num[0] == 0:
        num.pop(0)
    while den and den[0] == 0:
        den.pop(0)
    assert den, "Division by zero polynomial"
    deg_d = len(den) - 1
    lc_d = den[0]
    while len(num) - 1 >= deg_d:
        lc_n = num[0]
        # Multiply num by |lc_d| (positive!) or lc_d^2? Wait:
        # num_new = |lc_d| * num - (sign(lc_d) * lc_n) * den * y^shift
        # Since |lc_d| > 0, sign of remainder is 100% preserved!
        abs_d = abs(lc_d)
        sgn_d = 1 if lc_d > 0 else -1
        factor_n = sgn_d * lc_n
        for i in range(len(den)):
            num[i] = abs_d * num[i] - factor_n * den[i]
        for i in range(len(den), len(num)):
            num[i] = abs_d * num[i]
        while num and num[0] == 0:
            num.pop(0)
        num = _primitive_int(num)
    return num


def sturm_chain_q(sqf_desc_int: list[int]) -> list[list[Fraction]]:
    """Build exact primitive integer Sturm chain (returned as Fractions for uniform evaluation)."""
    p0 = _primitive_int(list(sqf_desc_int))
    deg = len(p0) - 1
    if deg == 0:
        return [[Fraction(c) for c in p0]]
    p1 = _primitive_int([(deg - i) * c for i, c in enumerate(p0[:-1])])
    chain_int = [p0, p1]
    while len(chain_int[-1]) > 1:
        rem = poly_prem_int(chain_int[-2], chain_int[-1])
        if not rem:
            break
        chain_int.append([-c for c in rem])
    return [[Fraction(c) for c in p] for p in chain_int]


def sign_changes_at_neg_inf(chain: list[list[Fraction]]) -> int:
    signs = []
    for p in chain:
        deg = len(p) - 1
        lead = p[0]
        s = lead if (deg % 2 == 0) else -lead
        if s != 0:
            signs.append(1 if s > 0 else -1)
    return sum(1 for a, b in zip(signs, signs[1:]) if a != b)


def sign_changes_at_pos_inf(chain: list[list[Fraction]]) -> int:
    signs = []
    for p in chain:
        lead = p[0]
        if lead != 0:
            signs.append(1 if lead > 0 else -1)
    return sum(1 for a, b in zip(signs, signs[1:]) if a != b)


def sign_changes_at_point(chain: list[list[Fraction]], pt: Fraction) -> int:
    signs = []
    for p in chain:
        v = eval_poly_q(p, pt)
        if v != 0:
            signs.append(1 if v > 0 else -1)
    return sum(1 for a, b in zip(signs, signs[1:]) if a != b)


def count_real_roots_sqf(sqf_desc_int: list[int]) -> tuple[int, int]:
    """Return (total_real_roots, nonneg_real_roots) for a square-free integer poly."""
    deg = len(sqf_desc_int) - 1
    if deg == 0:
        return (0, 0)
    if deg == 1:
        root = Fraction(-sqf_desc_int[1], sqf_desc_int[0])
        return (1, 1 if root >= 0 else 0)
    chain = sturm_chain_q(sqf_desc_int)
    # Check that last poly is nonzero constant (square-free guarantee)
    if len(chain[-1]) != 1 or chain[-1][0] == 0:
        raise ValueError("Polynomial passed to count_real_roots_sqf is not square-free!")
    v_ninf = sign_changes_at_neg_inf(chain)
    v_pinf = sign_changes_at_pos_inf(chain)
    total_real = v_ninf - v_pinf

    # Check if 0 is a root
    has_zero = (sqf_desc_int[-1] == 0)
    if has_zero:
        # Divide out y and evaluate on stripped poly
        sub_total, sub_pos = count_real_roots_sqf(sqf_desc_int[:-1])
        assert sub_total + 1 == total_real
        return (total_real, sub_pos + 1)

    v_zero = sign_changes_at_point(chain, Fraction(0))
    pos_real = v_zero - v_pinf
    return (total_real, pos_real)


def v2(val: int) -> int:
    if val == 0:
        return 10**9
    val = abs(val)
    return (val & -val).bit_length() - 1


def poly_shift_f_to_g(f_desc: list[int]) -> list[int]:
    """Given f(x) in descending order, return g(y) = f(y - 5) in descending order."""
    d = len(f_desc) - 1
    res = [0] * (d + 1)
    res[0] = f_desc[0]
    cur_deg = 0
    for c in f_desc[1:]:
        new_res = [0] * (d + 1)
        for i in range(cur_deg + 1):
            new_res[i + 1] += res[i]
            new_res[i] -= 5 * res[i]
        new_res[0] += c
        res = new_res
        cur_deg += 1
    return res[::-1]


def poly_shift_g_to_f(g_desc: list[int]) -> list[int]:
    """Given g(y) in descending order, return f(x) = g(x + 5) in descending order."""
    d = len(g_desc) - 1
    res = [0] * (d + 1)
    res[0] = g_desc[0]
    cur_deg = 0
    for c in g_desc[1:]:
        new_res = [0] * (d + 1)
        for i in range(cur_deg + 1):
            new_res[i + 1] += res[i]
            new_res[i] += 5 * res[i]
        new_res[0] += c
        res = new_res
        cur_deg += 1
    return res[::-1]


def poly_mul_linear_int(desc: list[int], c: int) -> list[int]:
    """Multiply polynomial in descending order by (x + c)."""
    out = [desc[0]]
    for i in range(1, len(desc)):
        out.append(desc[i] + c * desc[i - 1])
    out.append(c * desc[-1])
    return out


def poly_eval_2tm1_asc(desc: list[int]) -> list[int]:
    """Exact integer Horner for P(2t - 1) in ascending order [b_0, ..., b_n]."""
    n = len(desc) - 1
    res = [0] * (n + 1)
    res[0] = desc[0]
    cur_deg = 0
    for c in desc[1:]:
        new_res = [0] * (n + 1)
        for i in range(cur_deg + 1):
            new_res[i + 1] += 2 * res[i]
            new_res[i] -= res[i]
        new_res[0] += c
        res = new_res
        cur_deg += 1
    return res


def verify_candidate_g(g_desc: list[int], d: int, n: int, k: int = 5, sympy_crosscheck: bool = True) -> dict:
    """Verify a candidate g(y) = f(y - k) in descending integer order."""
    assert k == 5, "Standardized for k=5 (alpha=1/5)"
    if len(g_desc) != d + 1:
        raise AssertionError(f"Degree mismatch: len={len(g_desc)} != {d+1}")
    if g_desc[0] != 1:
        raise AssertionError(f"Not monic: leading coeff = {g_desc[0]}")
    for c in g_desc:
        if not isinstance(c, int):
            raise AssertionError(f"Non-integer coefficient: {c}")

    # 1. Exact trace and sum-of-squares
    if g_desc[1] != -5 * n:
        raise AssertionError(f"a_1 = {g_desc[1]} != -5n = {-5 * n}")
    expected_a2 = 12 * n * (n - 1)
    if g_desc[2] != expected_a2:
        raise AssertionError(f"a_2 = {g_desc[2]} != 12*n*(n-1) = {expected_a2}")

    # 2. Exact 2-adic Seidel congruences on a_k
    for idx, ak in enumerate(g_desc):
        if n % 2 == 0:
            if v2(ak) < idx:
                raise AssertionError(f"Even n={n}: v2(a_{idx})={v2(ak)} < {idx}")
        else:
            req = idx if (idx % 2 == 0) else (idx - 1)
            if idx >= 1 and v2(ak) < req:
                raise AssertionError(f"Odd n={n}: v2(a_{idx})={v2(ak)} < {req}")

    # Also reconstruct chi_S(x) = (x+5)^(n-d) * g(x+5) in exact integer arithmetic and check chi_S(2t-1)
    f_desc = poly_shift_g_to_f(g_desc)
    chi_desc = list(f_desc)
    for _ in range(n - d):
        chi_desc = poly_mul_linear_int(chi_desc, k)
    assert chi_desc[0] == 1 and chi_desc[1] == 0 and chi_desc[2] == -n * (n - 1) // 2

    b_asc = poly_eval_2tm1_asc(chi_desc)
    for idx, bk in enumerate(b_asc):
        if n % 2 == 0:
            assert v2(bk) >= n
        else:
            assert v2(bk) >= (n if idx % 2 == 1 else n - 1)

    # 3. Exact totally-real >= 0 check via square-free decomposition + independent Sturm
    y = sp.Symbol("y")
    g_poly = sp.Poly(g_desc, y, domain=sp.ZZ)
    _, sqf_factors = sp.sqf_list(g_poly)
    mult_zero = 0
    for fac, mult in sqf_factors:
        fac_desc = [int(c) for c in fac.all_coeffs()]
        tot_r, nonneg_r = count_real_roots_sqf(fac_desc)
        deg_fac = fac.degree()
        if tot_r != deg_fac:
            raise AssertionError(
                f"Not totally real: factor {fac_desc} deg={deg_fac} has {tot_r} real roots"
            )
        if nonneg_r != deg_fac:
            raise AssertionError(
                f"Negative root (< -5 for S): factor {fac_desc} deg={deg_fac} has {nonneg_r} roots >= 0"
            )
        if sympy_crosscheck:
            assert fac.count_roots() == deg_fac
            assert fac.count_roots(inf=0) == deg_fac
        if fac_desc[-1] == 0:
            mult_zero += mult

    return {
        "d": d,
        "n": n,
        "rank_5I_plus_S": d - mult_zero,
        "extra_m5_mult": mult_zero,
        "g_desc": g_desc,
        "f_desc": f_desc,
        "sqf_factors": [([int(c) for c in fac.all_coeffs()], int(m)) for fac, m in sqf_factors],
    }


def verify_candidate_f(f_desc: list[int], d: int, n: int, k: int = 5) -> dict:
    g_desc = poly_shift_f_to_g(f_desc)
    return verify_candidate_g(g_desc, d=d, n=n, k=k)
