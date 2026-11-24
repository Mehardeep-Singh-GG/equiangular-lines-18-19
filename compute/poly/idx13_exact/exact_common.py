"""Shared zero-float-trust exact rational, radical, interval, LDL^T, and Farkas helpers
for (19, 74) idx=13 (`S3`, `S2`, and `S1`).

All algebraic identities, pseudoinverses, Gram products, squarefree radical splits,
enclosing sqrt intervals, PSD witnesses, nullspaces, and LP Farkas dual certificates
are computed and/or verified strictly in exact `Fraction` / `int` arithmetic.
"""
from __future__ import annotations

import math
from fractions import Fraction
from typing import Iterable, Sequence

import numpy as np
import sympy as sp
from scipy.optimize import linprog


def to_frac(x) -> Fraction:
    if isinstance(x, Fraction):
        return x
    if isinstance(x, (int, np.integer)):
        return Fraction(int(x))
    return Fraction(x)


def lcm_list(ints: Iterable[int]) -> int:
    res = 1
    for v in ints:
        res = math.lcm(res, abs(int(v)))
    return res


def pinv_qq(M_rows: Sequence[Sequence]) -> tuple[list[list[Fraction]], int, list[int]]:
    """Compute exact rational Moore-Penrose pseudoinverse M^+ in Q^{m x m},
    exact rank, and RREF pivot indices `piv` giving col(M) isomorphism v -> v[piv].
    Verifies M * M^+ * M == M and (M * M^+)^T == M * M^+ in exact Fraction.
    """
    m = len(M_rows)
    M_sp = sp.Matrix([[sp.Rational(to_frac(v)) for v in row] for row in M_rows])
    Mp_sp = M_sp.pinv()
    _, piv = M_sp.rref()
    piv_list = list(piv)
    rk = len(piv_list)

    M_f = [[to_frac(M_rows[i][j]) for j in range(m)] for i in range(m)]
    Mp_f = [[Fraction(int(Mp_sp[i, j].p), int(Mp_sp[i, j].q)) for j in range(m)] for i in range(m)]

    # Verify M * Mp symmetric and M * Mp * M == M
    MMp = [
        [sum(M_f[i][k] * Mp_f[k][j] for k in range(m)) for j in range(m)]
        for i in range(m)
    ]
    for i in range(m):
        for j in range(m):
            if MMp[i][j] != MMp[j][i]:
                raise AssertionError(f"M*Mp not symmetric at ({i},{j})")
            recon = sum(MMp[i][k] * M_f[k][j] for k in range(m))
            if recon != M_f[i][j]:
                raise AssertionError(f"M*Mp*M != M at ({i},{j})")
    return Mp_f, rk, piv_list


def mat_mul_qq(A: Sequence[Sequence[Fraction]], B: Sequence[Sequence[Fraction]]) -> list[list[Fraction]]:
    r, k_dim, c = len(A), len(B), len(B[0])
    return [[sum(A[i][k] * B[k][j] for k in range(k_dim)) for j in range(c)] for i in range(r)]


def mat_vec_qq(A: Sequence[Sequence[Fraction]], v: Sequence[Fraction]) -> list[Fraction]:
    return [sum(row[j] * v[j] for j in range(len(v))) for row in A]


def dot_qq(u: Sequence[Fraction], v: Sequence[Fraction]) -> Fraction:
    return sum(a * b for a, b in zip(u, v))


def build_adj_paths_cycles(paths: Sequence[int], cyc_lens: Sequence[int]) -> list[list[int]]:
    n = sum(paths) + sum(cyc_lens)
    A = [[0] * n for _ in range(n)]
    off = 0
    for kp in paths:
        for i in range(kp - 1):
            A[off + i][off + i + 1] = 1
            A[off + i + 1][off + i] = 1
        off += kp
    for L in cyc_lens:
        for i in range(L):
            A[off + i][off + (i + 1) % L] = 1
            A[off + (i + 1) % L][off + i] = 1
        off += L
    return A


def cycle_gram_setup_qq(part: Sequence[int]) -> dict:
    """Exact QQ setup for S1 cycle partition M = 2*(2I - A)."""
    n = sum(part)
    A = build_adj_paths_cycles([], part)
    M = [[Fraction(4 if i == j else (-2 if A[i][j] else 0)) for j in range(n)] for i in range(n)]
    Mp, rk, piv = pinv_qq(M)
    W_full = [[Fraction(20) * M[i][j] - sum(M[i][k] * M[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
    W_piv = [[W_full[i][j] for j in piv] for i in piv]
    return {
        "n": n,
        "A": A,
        "M": M,
        "Mp": Mp,
        "rank": rk,
        "piv": piv,
        "W_full": W_full,
        "W_piv": W_piv,
    }


def sf_decomp(q: Fraction) -> tuple[Fraction, int]:
    """Exact factorization sqrt(q) = c * sqrt(d) where d = 0 (if q==0)
    or d >= 1 is squarefree integer and c > 0 in Q. Verified c^2 * d == q.
    """
    q = to_frac(q)
    if q < 0:
        raise ValueError(f"sf_decomp called with negative q={q}")
    if q == 0:
        return Fraction(0), 0
    num, den = q.numerator, q.denominator
    prod = num * den
    sq = 1
    p = 2
    while p * p <= prod:
        while prod % (p * p) == 0:
            prod //= (p * p)
            sq *= p
        p += 1 if p == 2 else 2
    c = Fraction(sq, den)
    if c * c * prod != q:
        raise AssertionError(f"sf_decomp self-check failed for q={q}")
    return c, prod


def sqrt_interval_qq(q: Fraction, prec_bits: int = 80) -> tuple[Fraction, Fraction]:
    """Exact rational enclosure [lo, hi] for sqrt(q), q >= 0, verified lo^2 <= q <= hi^2."""
    q = to_frac(q)
    if q < 0:
        raise ValueError(f"sqrt_interval_qq called with negative q={q}")
    if q == 0:
        return Fraction(0), Fraction(0)
    s = math.isqrt((q.numerator << (2 * prec_bits)) // q.denominator)
    lo = Fraction(s, 1 << prec_bits)
    if lo * lo == q:
        return lo, lo
    hi = Fraction(s + 1, 1 << prec_bits)
    if not (0 <= lo <= hi and lo * lo <= q <= hi * hi):
        raise AssertionError(f"sqrt_interval_qq self-check failed for q={q}")
    return lo, hi


def iv_mul(a: tuple[Fraction, Fraction], b: tuple[Fraction, Fraction]) -> tuple[Fraction, Fraction]:
    p = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    return min(p), max(p)


def iv_add(a: tuple[Fraction, Fraction], b: tuple[Fraction, Fraction]) -> tuple[Fraction, Fraction]:
    return a[0] + b[0], a[1] + b[1]


def iv_overlaps(a: tuple[Fraction, Fraction], b: tuple[Fraction, Fraction]) -> bool:
    return a[0] <= b[1] and b[0] <= a[1]


def ldlt_psd_witness_qq(M_rows: Sequence[Sequence[Fraction]]) -> tuple[bool, list[Fraction] | None]:
    """Exact Fraction pivoted LDL^T check for symmetric PSD matrix M.
    Returns (True, None) iff M >= 0; otherwise returns (False, w) with explicit
    rational vector w such that w^T M w < 0 (verified in exact Fraction).
    """
    n = len(M_rows)
    M = [[to_frac(M_rows[i][j]) for j in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if M[i][j] != M[j][i]:
                raise AssertionError(f"Non-symmetric matrix in ldlt_psd_witness_qq at ({i},{j})")

    A = [row[:] for row in M]
    perm = list(range(n))
    L = [[Fraction(1 if i == j else 0) for j in range(n)] for i in range(n)]
    D = [Fraction(0)] * n

    for k in range(n):
        # Find pivot on diagonal [k..n-1]
        best = k
        best_val = abs(A[k][k])
        for i in range(k + 1, n):
            if abs(A[i][i]) > best_val:
                best = i
                best_val = abs(A[i][i])
        if best_val == 0:
            # All remaining diagonal entries are 0; check if any remaining off-diagonal is nonzero
            for i in range(k, n):
                for j in range(i + 1, n):
                    if A[i][j] != 0:
                        # Build e_i - sgn * e_j in pivoted space: z^T A z = 2 * s * A[i][j] < 0
                        # Lift back through L^T z_perm = e_i + alpha * e_j
                        rhs = [Fraction(0)] * n
                        rhs[i] = Fraction(1)
                        rhs[j] = Fraction(-1) if A[i][j] > 0 else Fraction(1)
                        z = [Fraction(0)] * n
                        for idx in range(n - 1, -1, -1):
                            val = rhs[idx] - sum(L[r][idx] * z[r] for r in range(idx + 1, n))
                            z[idx] = val
                        w = [Fraction(0)] * n
                        for pos, orig in enumerate(perm):
                            w[orig] = z[pos]
                        quad = sum(w[r] * M[r][c] * w[c] for r in range(n) for c in range(n))
                        assert quad < 0
                        return False, w
            return True, None

        if best != k:
            A[k], A[best] = A[best], A[k]
            for r in range(n):
                A[r][k], A[r][best] = A[r][best], A[r][k]
            perm[k], perm[best] = perm[best], perm[k]
            for c in range(k):
                L[k][c], L[best][c] = L[best][c], L[k][c]

        piv_val = A[k][k]
        D[k] = piv_val
        if piv_val < 0:
            # Back-solve L^T z = e_k => z^T A_orig_perm z = piv_val < 0
            z = [Fraction(0)] * n
            z[k] = Fraction(1)
            for idx in range(k - 1, -1, -1):
                z[idx] = -sum(L[r][idx] * z[r] for r in range(idx + 1, k + 1))
            w = [Fraction(0)] * n
            for pos, orig in enumerate(perm):
                w[orig] = z[pos]
            quad = sum(w[r] * M[r][c] * w[c] for r in range(n) for c in range(n))
            assert quad < 0
            return False, w

        inv_piv = Fraction(1) / piv_val
        for i in range(k + 1, n):
            factor = A[i][k] * inv_piv
            L[i][k] = factor
            if factor != 0:
                for j in range(k + 1, n):
                    A[i][j] -= factor * A[k][j]
        for i in range(k + 1, n):
            A[i][k] = Fraction(0)
            A[k][i] = Fraction(0)
    return True, None


def nullspace_qq(M_rows: Sequence[Sequence[Fraction]]) -> list[list[Fraction]]:
    """Exact rational nullspace basis via SymPy RREF, verified M * w == 0 in Fraction."""
    m = len(M_rows)
    n = len(M_rows[0]) if m else 0
    M_sp = sp.Matrix([[sp.Rational(to_frac(v)) for v in row] for row in M_rows])
    ns_sp = M_sp.nullspace()
    basis = [[Fraction(int(vec[i, 0].p), int(vec[i, 0].q)) for i in range(n)] for vec in ns_sp]
    M_f = [[to_frac(M_rows[i][j]) for j in range(n)] for i in range(m)]
    for w in basis:
        for i in range(m):
            if dot_qq(M_f[i], w) != 0:
                raise AssertionError("nullspace_qq self-check failed")
    return basis


def untrusted_psd_test_vectors(M_rows: Sequence[Sequence[Fraction]], W_rows: Sequence[Sequence[Fraction]], scale: int = 1000) -> list[tuple[list[int], Fraction]]:
    """Use float eigh(M) SOLELY as an untrusted hint to propose integer test vectors w in Z^m
    and compute the exact rational upper bound rhs = w^T W w for sum (w^T v_k)^2 <= w^T W w.
    Any valid W - sum v_k v_k^T >= 0 implies this exact inequality for EVERY w in Z^m.
    """
    M_np = np.array([[float(to_frac(v)) for v in row] for row in M_rows], dtype=float)
    ev, U = np.linalg.eigh(M_np)
    out = []
    for mode in range(len(ev)):
        if ev[mode] > 1e-8:
            w = [int(round(float(U[i, mode]) * scale)) for i in range(len(ev))]
            if any(w):
                rhs = Fraction(0)
                for i in range(len(w)):
                    wi = w[i]
                    if wi:
                        rhs += wi * sum(w[j] * to_frac(W_rows[i][j]) for j in range(len(w)) if w[j])
                out.append((w, rhs))
    return out


def verify_farkas_cert(
    A_eq: Sequence[Sequence[Fraction]],
    b_eq: Sequence[Fraction],
    fix_indices: Sequence[int],
    y_eq: Sequence[Fraction],
    A_ub: Sequence[Sequence[Fraction]] | None = None,
    b_ub: Sequence[Fraction] | None = None,
    y_ub: Sequence[Fraction] | None = None,
) -> tuple[bool, Fraction]:
    """Exact pure-Fraction verification of Farkas infeasibility for:
       A_eq x = b_eq, [A_ub x <= b_ub], x_j = 1 (j in fix), 0 <= x_j <= 1 (j not in fix).
    Checks y_ub >= 0 and lhs_min - rhs > 0 where u = y_eq^T A_eq + y_ub^T A_ub,
    rhs = y_eq^T b_eq + y_ub^T b_ub, lhs_min = sum_{j in fix} u_j + sum_{j not in fix} min(0, u_j).
    Returns (valid, gap).
    """
    m_eq = len(A_eq)
    n = len(A_eq[0]) if m_eq else 0
    fix_set = set(fix_indices)
    if y_ub is not None:
        if any(w < 0 for w in y_ub):
            return False, Fraction(0)

    u = [Fraction(0)] * n
    rhs = Fraction(0)
    for i in range(m_eq):
        yi = y_eq[i]
        if yi != 0:
            rhs += yi * b_eq[i]
            row = A_eq[i]
            for j in range(n):
                if row[j] != 0:
                    u[j] += yi * row[j]
    if A_ub is not None and b_ub is not None and y_ub is not None:
        for i in range(len(A_ub)):
            wi = y_ub[i]
            if wi != 0:
                rhs += wi * b_ub[i]
                row = A_ub[i]
                for j in range(n):
                    if row[j] != 0:
                        u[j] += wi * row[j]

    lhs_min = Fraction(0)
    for j in range(n):
        if j in fix_set:
            lhs_min += u[j]
        elif u[j] < 0:
            lhs_min += u[j]
    gap = lhs_min - rhs
    return (gap > 0), gap


def _dense_to_frac_mat(rows):
    return [[to_frac(v) for v in row] for row in rows]


def certify_eq_lp_farkas(
    A_eq_rows,
    b_eq_vals,
    fix_indices: Sequence[int],
    A_ub_rows=None,
    b_ub_vals=None,
    denom_limits: tuple[int | None, ...] = (10**3, 10**4, 10**6, 10**9, None),
) -> tuple[bool, dict | None]:
    """Check LP infeasibility via HiGHS dual LP and certify an exact rational Farkas vector.
    Never returns True unless `verify_farkas_cert(...)` proves exact Fraction `gap > 0`.
    """
    m_eq = len(A_eq_rows)
    n = len(A_eq_rows[0]) if m_eq else 0
    fix_set = set(fix_indices)
    nonfix = [j for j in range(n) if j not in fix_set]

    A_eq_np = np.array([[float(v) for v in row] for row in A_eq_rows], dtype=float)
    b_eq_np = np.array([float(v) for v in b_eq_vals], dtype=float)
    bnds = [(1.0, 1.0) if j in fix_set else (0.0, 1.0) for j in range(n)]

    if A_ub_rows is not None and len(A_ub_rows) > 0:
        A_ub_np = np.array([[float(v) for v in row] for row in A_ub_rows], dtype=float)
        b_ub_np = np.array([float(v) for v in b_ub_vals], dtype=float)
        res = linprog(np.zeros(n), A_ub=A_ub_np, b_ub=b_ub_np, A_eq=A_eq_np, b_eq=b_eq_np, bounds=bnds, method="highs")
    else:
        A_ub_np = None
        b_ub_np = None
        res = linprog(np.zeros(n), A_eq=A_eq_np, b_eq=b_eq_np, bounds=bnds, method="highs")

    if res.success:
        return False, None

    # Solve explicit Farkas dual LP using sparse identity to avoid dense memory blowup
    from scipy import sparse
    m_ub = len(A_ub_rows) if A_ub_rows is not None else 0
    nf = len(nonfix)
    # Variables: [y_eq (m_eq in [-1,1]), y_ub (m_ub in [0,1]), t (nf >= 0)]
    c_y = b_eq_np - (A_eq_np[:, list(fix_set)].sum(axis=1) if fix_set else np.zeros(m_eq))
    if m_ub > 0:
        c_w = b_ub_np - (A_ub_np[:, list(fix_set)].sum(axis=1) if fix_set else np.zeros(m_ub))
        c_dual = np.concatenate([c_y, c_w, np.ones(nf)])
        A_nf_ub = sparse.hstack([
            sparse.csc_matrix(-A_eq_np[:, nonfix].T),
            sparse.csc_matrix(-A_ub_np[:, nonfix].T),
            -sparse.eye(nf, format="csc"),
        ], format="csc")
        bnds_dual = [(-1.0, 1.0)] * m_eq + [(0.0, 1.0)] * m_ub + [(0.0, None)] * nf
    else:
        c_dual = np.concatenate([c_y, np.ones(nf)])
        A_nf_ub = sparse.hstack([
            sparse.csc_matrix(-A_eq_np[:, nonfix].T),
            -sparse.eye(nf, format="csc"),
        ], format="csc")
        bnds_dual = [(-1.0, 1.0)] * m_eq + [(0.0, None)] * nf

    rd = linprog(c_dual, A_ub=A_nf_ub, b_ub=np.zeros(nf), bounds=bnds_dual, method="highs")
    if rd.status != 0 or rd.fun >= -1e-9:
        return False, None

    A_eq_q = _dense_to_frac_mat(A_eq_rows)
    b_eq_q = [to_frac(v) for v in b_eq_vals]
    A_ub_q = _dense_to_frac_mat(A_ub_rows) if m_ub > 0 else None
    b_ub_q = [to_frac(v) for v in b_ub_vals] if m_ub > 0 else None

    y_raw = rd.x[:m_eq]
    w_raw = rd.x[m_eq:m_eq + m_ub] if m_ub > 0 else []

    for lim in denom_limits:
        if lim is None:
            y_q = [Fraction(float(v)) for v in y_raw]
            w_q = [max(Fraction(0), Fraction(float(v))) for v in w_raw] if m_ub > 0 else None
        else:
            y_q = [Fraction(float(v)).limit_denominator(lim) for v in y_raw]
            w_q = [max(Fraction(0), Fraction(float(v)).limit_denominator(lim)) for v in w_raw] if m_ub > 0 else None
        ok, gap = verify_farkas_cert(A_eq_q, b_eq_q, fix_indices, y_q, A_ub_q, b_ub_q, w_q)
        if ok:
            cert = {
                "y_eq": [(i, str(v.numerator), str(v.denominator)) for i, v in enumerate(y_q) if v != 0],
                "y_ub": [(i, str(v.numerator), str(v.denominator)) for i, v in enumerate(w_q) if v != 0] if w_q else [],
                "gap": [str(gap.numerator), str(gap.denominator)],
            }
            return True, cert

    return False, None


def verify_farkas_cert_scaled(
    A_num_np: np.ndarray,
    row_scales_q: Sequence[Fraction],
    b_eq_q: Sequence[Fraction],
    fix_indices: Sequence[int],
    y_q: Sequence[Fraction],
) -> tuple[bool, Fraction]:
    """Exact overflow-free integer/Fraction verification for row-scaled A_eq = diag(row_scales_q) * A_num_np."""
    m_eq, n = A_num_np.shape
    fix_set = set(fix_indices)
    act = [(i, y_q[i] * row_scales_q[i], y_q[i]) for i in range(m_eq) if y_q[i] != 0]
    if not act:
        return False, Fraction(0)
    L_y = lcm_list(ye.denominator for _, ye, _ in act)
    b_den = lcm_list((yo * b_eq_q[i]).denominator for i, _, yo in act)
    M_scale = L_y * b_den

    z_ints = [(i, int(ye * M_scale)) for i, ye, _ in act]
    max_z = max(abs(zi) for _, zi in z_ints)
    max_A = int(np.max(np.abs(A_num_np))) if A_num_np.size else 0
    if max_z * max_A * len(z_ints) * max(1, n) < 10**18:
        u_arr = np.zeros(n, dtype=np.int64)
        for i, zi in z_ints:
            u_arr += np.int64(zi) * A_num_np[i]
        lhs_fix = sum(int(u_arr[j]) for j in fix_set)
        neg_mask = u_arr < 0
        # Add negative non-fixed entries
        if fix_set:
            neg_mask[list(fix_set)] = False
        lhs_min = lhs_fix + int(np.sum(u_arr[neg_mask], dtype=np.int64))
    else:
        u_obj = np.zeros(n, dtype=object)
        for i, zi in z_ints:
            u_obj += A_num_np[i].astype(object) * zi
        lhs_min = sum(int(u_obj[j]) for j in fix_set) + sum(
            int(u_obj[j]) for j in range(n) if j not in fix_set and u_obj[j] < 0
        )

    rhs_int = sum(int(yo * b_eq_q[i] * M_scale) for i, _, yo in act)
    if lhs_min > rhs_int:
        return True, Fraction(lhs_min - rhs_int, M_scale)
    return False, Fraction(0)


def certify_eq_lp_farkas_scaled(
    A_num_np: np.ndarray,
    row_scales_q: Sequence[Fraction],
    b_eq_q: Sequence[Fraction],
    fix_indices: Sequence[int],
    denom_limits: tuple[int | None, ...] = (10**3, 10**4, 10**6, 10**9, None),
) -> tuple[bool, dict | None]:
    """Fast vectorized LP + exact zero-trust Farkas dual verification for row-scaled integer matrices."""
    from scipy import sparse
    m_eq, n = A_num_np.shape
    fix_set = set(fix_indices)
    nonfix = [j for j in range(n) if j not in fix_set]

    rscale_flt = np.array([float(s) for s in row_scales_q], dtype=float)
    A_eq_np = A_num_np * rscale_flt[:, None]
    b_eq_np = np.array([float(b) for b in b_eq_q], dtype=float)
    bnds = [(1.0, 1.0) if j in fix_set else (0.0, 1.0) for j in range(n)]

    res = linprog(np.zeros(n), A_eq=A_eq_np, b_eq=b_eq_np, bounds=bnds, method="highs")
    if res.success:
        return False, None

    nf = len(nonfix)
    c_y = b_eq_np - (A_eq_np[:, list(fix_set)].sum(axis=1) if fix_set else np.zeros(m_eq))
    c_dual = np.concatenate([c_y, np.ones(nf)])
    A_nf_ub = sparse.hstack([
        sparse.csc_matrix(-A_eq_np[:, nonfix].T),
        -sparse.eye(nf, format="csc"),
    ], format="csc")
    bnds_dual = [(-1.0, 1.0)] * m_eq + [(0.0, None)] * nf
    rd = linprog(c_dual, A_ub=A_nf_ub, b_ub=np.zeros(nf), bounds=bnds_dual, method="highs")
    if rd.status != 0 or rd.fun >= -1e-9:
        return False, None

    y_raw = rd.x[:m_eq]
    for lim in denom_limits:
        if lim is None:
            y_q = [Fraction(float(v)) for v in y_raw]
        else:
            y_q = [Fraction(float(v)).limit_denominator(lim) for v in y_raw]
        ok, gap = verify_farkas_cert_scaled(A_num_np, row_scales_q, b_eq_q, fix_indices, y_q)
        if ok:
            cert = {
                "y_eq": [(i, str(v.numerator), str(v.denominator)) for i, v in enumerate(y_q) if v != 0],
                "y_ub": [],
                "gap": [str(gap.numerator), str(gap.denominator)],
            }
            return True, cert
    return False, None


def reconstruct_sparse_fracs(sparse_entries: Sequence, length: int) -> list[Fraction]:
    vec = [Fraction(0)] * length
    for i, num_s, den_s in sparse_entries:
        vec[int(i)] = Fraction(int(num_s), int(den_s))
    return vec


def clear_linear_eq_to_ints(coeffs: Sequence[Fraction], rhs: Fraction) -> tuple[list[int], int]:
    """Scale rational equality sum coeffs[k] x_k = rhs by exact LCM of denominators to exact integers."""
    denoms = [to_frac(rhs).denominator] + [to_frac(c).denominator for c in coeffs if c != 0]
    L = lcm_list(denoms)
    c_int = [int(to_frac(c) * L) for c in coeffs]
    rhs_int = int(to_frac(rhs) * L)
    g = math.gcd(abs(rhs_int), *(abs(c) for c in c_int if c != 0))
    if g > 1:
        c_int = [c // g for c in c_int]
        rhs_int //= g
    return c_int, rhs_int


# ---------------------------------------------------------------------------
# Shared Exact QQ Helpers for S1 Cycle Partitions (24, 48, 0, 2)
# ---------------------------------------------------------------------------

def aut_perms_cycles(part: Sequence[int]) -> list[list[int]]:
    """Exact automorphism group of disjoint cycles of lengths `part`."""
    import itertools
    c_groups = []
    off = 0
    for L in part:
        c_groups.append((L, [[off + ((s - i if rev else s + i) % L) for i in range(L)]
                             for s in range(L) for rev in (False, True)]))
        off += L
    by_L = {}
    for ci, (L, _) in enumerate(c_groups):
        by_L.setdefault(L, []).append(ci)
    perms = []
    for bperm in itertools.product(*(list(itertools.permutations(idxs)) for idxs in by_L.values())):
        cmap = [0] * len(c_groups)
        for idxs, pi_d in zip(by_L.values(), bperm):
            for src, dst in zip(idxs, pi_d):
                cmap[src] = dst
        for cs in itertools.product(*(c_groups[cmap[ci]][1] for ci in range(len(c_groups)))):
            p = []
            for seg in cs:
                p.extend(seg)
            perms.append(p)
    return perms


def s1_load_vectors_qq(part: Sequence[int]) -> dict:
    """Enumerate all valid balanced cycle vectors in S1 (`part`), computing exact QQ
    quadratic forms Q(v) = v^T M^+ v and integer-scaled pairwise inner products g(u, v) = G_int[u, v] / L_mp.
    """
    import itertools
    setup = cycle_gram_setup_qq(part)
    Mp = setup["Mp"]
    # Exact common denominator of Mp
    L_mp = lcm_list(v.denominator for row in Mp for v in row)
    Mp_int = np.array([[int(Mp[i][j] * L_mp) for j in range(16)] for i in range(16)], dtype=np.int64)

    cyc_vecs = []
    for L in part:
        cyc_vecs.append([tuple(-1 if i in c else 1 for i in range(L))
                         for c in itertools.combinations(range(L), L // 2)])

    # Precompute cyclewise Q_c as exact int numerator over L_mp
    cyc_qs_int = []
    off = 0
    for ci, L in enumerate(part):
        Mp_sub = Mp_int[off:off + L, off:off + L]
        qs = []
        for vc in cyc_vecs[ci]:
            v_arr = np.array(vc, dtype=np.int64)
            qs.append(int(v_arr @ Mp_sub @ v_arr))
        cyc_qs_int.append(qs)
        off += L

    min_qs = [min(qs) for qs in cyc_qs_int]
    # 9/2 = (9 * L_mp) // 2 (note L_mp is always even for cycle partitions: divisible by 32)
    assert (9 * L_mp) % 2 == 0 and 4 * L_mp == (8 * L_mp) // 2
    lim_9_2 = (9 * L_mp) // 2
    lim_4 = 4 * L_mp

    vecs = []
    q_ints = []
    t = len(part)

    def rec(ci, cq, cur_v):
        if ci == t:
            if cq <= lim_9_2:
                vecs.append(cur_v)
                q_ints.append(cq)
            return
        rem_min = sum(min_qs[ci + 1:])
        for vc, qc in zip(cyc_vecs[ci], cyc_qs_int[ci]):
            if cq + qc + rem_min <= lim_9_2:
                rec(ci + 1, cq + qc, cur_v + vc)

    rec(0, 0, ())
    V_mat = np.array(vecs, dtype=np.int64)  # N x 16 exact ints in {-1, +1}
    # Check max product magnitude so int64 G_mat never overflows: <= 16^2 * max|Mp_int|
    max_mp = int(np.max(np.abs(Mp_int)))
    assert 256 * max_mp < 10**12
    G_int = V_mat @ Mp_int @ V_mat.T  # exact N x N integer matrix: g(i, j) = G_int[i, j] / L_mp
    # Sanity check diagonal matches q_ints and verify max(res_c) < 8/3 (<= 2 copies per profile!)
    res_c_list = [Fraction(9, 2) - Fraction(q, L_mp) for q in q_ints]
    assert max(res_c_list) < Fraction(8, 3), f"Expected max(res_c) < 8/3, got {max(res_c_list)}"
    for i in range(len(vecs)):
        assert int(G_int[i, i]) == q_ints[i]

    setup.update({
        "part": tuple(part),
        "L_mp": L_mp,
        "Mp_int": Mp_int,
        "vecs": vecs,
        "V_mat": V_mat,
        "q_ints": q_ints,
        "Q_frac": [Fraction(q, L_mp) for q in q_ints],
        "res_c": [Fraction(9, 2) - Fraction(q, L_mp) for q in q_ints],
        "G_int": G_int,
        "b_indices": [i for i, q in enumerate(q_ints) if q <= lim_4],
        "psd_tests": untrusted_psd_test_vectors(setup["M"], setup["W_full"], scale=200),
    })
    return setup


def s1_solve_case0_qq(data: dict) -> dict:
    """Case 0: all C0 vectors have res(v) == 0 (`Q(v) == 9/2`), exact C0-alone CP-SAT."""
    from ortools.sat.python import cp_model
    L_mp = data["L_mp"]
    G_int = data["G_int"]
    V_mat = data["V_mat"]
    z_c = [i for i, r in enumerate(data["res_c"]) if r == 0]
    nz = len(z_c)
    assert (3 * L_mp) % 2 == 0
    tgt_pos = L_mp // 2
    tgt_neg = -(3 * L_mp) // 2

    m0 = cp_model.CpModel()
    xc0 = [m0.NewBoolVar(f"c{i}") for i in range(nz)]
    m0.Add(sum(xc0) == 24)
    for w in range(16):
        m0.Add(sum(int(V_mat[z_c[k], w]) * xc0[k] for k in range(nz)) == 0)
    for a in range(nz):
        ia = z_c[a]
        nbs = []
        for b in range(nz):
            if a == b:
                continue
            ib = z_c[b]
            gval = int(G_int[ia, ib])
            is_pos = (gval == tgt_pos)
            is_neg = (gval == tgt_neg)
            if is_neg:
                nbs.append(xc0[b])
            if b > a and not (is_pos or is_neg):
                m0.Add(xc0[a] + xc0[b] <= 1)
        m0.Add(sum(nbs) >= 8 - 24 * (1 - xc0[a]))
        m0.Add(sum(nbs) <= 8 + 24 * (1 - xc0[a]))
    for w_vec, rhs_f in data["psd_tests"]:
        rhs_int = int(rhs_f)  # exact integer for integer W_full
        assert rhs_f == rhs_int
        vals = [int(sum(w_vec[r] * int(V_mat[z_c[k], r]) for r in range(16))) ** 2 for k in range(nz)]
        m0.Add(sum(vals[k] * xc0[k] for k in range(nz)) <= rhs_int)

    sv0 = cp_model.CpSolver()
    sv0.parameters.max_time_in_seconds = 30.0
    st0 = sv0.Solve(m0)
    if st0 != cp_model.INFEASIBLE:
        raise AssertionError(f"Case 0 unexpected CP-SAT status {sv0.StatusName(st0)}")
    return {"z_count": nz, "status": "INFEASIBLE", "wall_sec": round(sv0.WallTime(), 4)}


def s1_peel_2d(cneg, cpos, cadj, cb_ok, bm2, b0, badj, bcross, init_ic, init_ib, req_ic=()):
    alc = np.zeros(cneg.shape[0], dtype=bool)
    alc[list(init_ic)] = True
    alb = np.zeros(bm2.shape[0], dtype=bool)
    alb[list(init_ib)] = True
    for _ in range(30):
        nc = alc & (cneg[:, alc].sum(axis=1) >= 8) & (cpos[:, alc].sum(axis=1) >= 15) & (cb_ok[:, alb].sum(axis=1) >= 32)
        nb = alb & (bm2[:, alb].sum(axis=1) >= 2) & (b0[:, alb].sum(axis=1) >= 13) & (cb_ok[alc, :].sum(axis=0) >= 24) & (bcross[:, alb].sum(axis=1) >= 16)
        for ri in req_ic:
            if not nc[ri]:
                return np.array([], dtype=int), np.array([], dtype=int)
        if np.array_equal(nc, alc) and np.array_equal(nb, alb):
            break
        alc, alb = nc, nb
    return np.where(alc)[0], np.where(alb)[0]


def s1_o2_build_branch_qq(data: dict, s0: int) -> dict:
    """Exact QQ O(2) branch around outer orbit representative s0 (res[s0] > 0).
    Zero square roots or tolerances: represents each candidate with exact
    (v_idx, A_frac, rem1_frac, q_frac, sf_int, sgn).
    """
    L_mp = data["L_mp"]
    G_int = data["G_int"]
    res_c = data["res_c"]
    Q_frac = data["Q_frac"]
    d0 = res_c[s0]
    assert d0 > 0

    # Candidate lists: tuple (orig_v_idx, A, rem1, q_sf, sf_d, sgn)
    # s0 itself sits at C-index 0 with a_{s0} = sqrt(d0) => A_{s0} = d0, rem1 = 0
    c_cands = [(s0, d0, Fraction(0), Fraction(0), 0, 0)]
    tgts_c = (Fraction(1, 2), Fraction(-3, 2))
    twin_count = 0
    for j in range(len(res_c)):
        if res_c[j] > d0:
            continue
        g0 = Fraction(int(G_int[s0, j]), L_mp)
        rj = res_c[j]
        for tgt in tgts_c:
            A = tgt - g0
            rem1 = rj - (A * A) / d0
            if rem1 < 0:
                continue
            if j == s0:
                twin_count += 1
            q_sf, sf_d = sf_decomp(rem1)
            if sf_d == 0:
                c_cands.append((j, A, rem1, q_sf, 0, 0))
            else:
                c_cands.append((j, A, rem1, q_sf, sf_d, 1))
                c_cands.append((j, A, rem1, q_sf, sf_d, -1))
    if d0 < 2:
        assert twin_count == 0

    b_cands = []
    tgts_b = (Fraction(1), Fraction(-1))
    for bi in data["b_indices"]:
        g0 = Fraction(int(G_int[s0, bi]), L_mp)
        rb = Fraction(4) - Q_frac[bi]
        for tgt in tgts_b:
            A = tgt - g0
            rem1 = rb - (A * A) / d0
            if rem1 < 0:
                continue
            q_sf, sf_d = sf_decomp(rem1)
            if sf_d == 0:
                b_cands.append((bi, A, rem1, q_sf, 0, 0))
            else:
                b_cands.append((bi, A, rem1, q_sf, sf_d, 1))
                b_cands.append((bi, A, rem1, q_sf, sf_d, -1))

    # Precompute integer-scaled exact adjacency matrices!
    # Clear common denominator per pair formula: M_xy = g_xy + A_x A_y / d0 + sgn_x sgn_y q_x q_y sf_d
    # Fast exact computation in int using L_all = lcm(L_mp, d0*(denom_A)^2, denom(q^2*sf_d))!
    all_c_b = c_cands + b_cands
    den_list = [L_mp, d0.denominator]
    for _, A, rem1, q_sf, sf_d, _ in all_c_b:
        den_list.append(A.denominator)
        den_list.append(q_sf.denominator)
    # Build integer numerators for A over L_A and q over L_q
    L_A = lcm_list(c[1].denominator for c in all_c_b)
    L_q = lcm_list(c[3].denominator for c in all_c_b)
    # Exact common scale M_xy * S_M where S_M = L_mp * d0.numerator * (L_A**2) * (L_q**2) * ... wait:
    # A_x*A_y / d0 has denominator dividing L_A^2 * d0.numerator!
    S_M = lcm_list([L_mp, d0.numerator * L_A * L_A, L_q * L_q])

    def prep_arrays(cands):
        nc = len(cands)
        v_idx = np.array([c[0] for c in cands], dtype=np.int64)
        A_num = np.array([int(c[1] * L_A) for c in cands], dtype=np.int64)
        q_num = np.array([int(c[3] * L_q) for c in cands], dtype=np.int64)
        sf_d = np.array([c[4] for c in cands], dtype=np.int64)
        sgn = np.array([c[5] for c in cands], dtype=np.int64)
        return v_idx, A_num, q_num, sf_d, sgn

    # Wait: check product bounds fit safely in Python object / int64!
    cv_i, cA_n, cq_n, c_sf, c_sgn = prep_arrays(c_cands)
    bv_i, bA_n, bq_n, b_sf, b_sgn = prep_arrays(b_cands)

    # Exact rational targets scaled by S_M
    assert (S_M % 2 == 0) and (S_M % L_mp == 0) and ((S_M * d0.denominator) % (d0.numerator * L_A * L_A) == 0)
    k_g = S_M // L_mp
    k_A = (S_M * d0.denominator) // (d0.numerator * L_A * L_A)
    assert S_M % (L_q * L_q) == 0
    k_q = S_M // (L_q * L_q)

    def max_abs_check(A1, A2, q1, q2, sf1):
        ma = int(np.max(np.abs(A1))) * int(np.max(np.abs(A2))) * k_A if len(A1) and len(A2) else 0
        mq = int(np.max(np.abs(q1))) * int(np.max(np.abs(q2))) * int(np.max(sf1)) * k_q if len(q1) and len(sf1) else 0
        mg = int(np.max(np.abs(G_int))) * k_g
        assert mg + ma + mq < 10**15

    max_abs_check(cA_n, cA_n, cq_n, cq_n, c_sf)
    max_abs_check(bA_n, bA_n, bq_n, bq_n, b_sf)
    max_abs_check(cA_n, bA_n, cq_n, bq_n, c_sf)

    def rational_block(vi1, A1, q1, sf1, sg1, vi2, A2, q2, sf2, sg2):
        # Returns boolean mask where M_xy is rational AND matrix M_scaled of exact int64
        g_blk = G_int[np.ix_(vi1, vi2)] * k_g
        a_blk = np.outer(A1, A2) * k_A
        b_blk = np.outer(sg1 * q1 * sf1, sg2 * q2) * k_q
        rat_ok = (sf1[:, None] == 0) | (sf2[None, :] == 0) | (sf1[:, None] == sf2[None, :])
        return rat_ok, g_blk + a_blk + b_blk

    rat_cc, M_cc = rational_block(cv_i, cA_n, cq_n, c_sf, c_sgn, cv_i, cA_n, cq_n, c_sf, c_sgn)
    cpos = rat_cc & (M_cc == S_M // 2)
    cneg = rat_cc & (M_cc == -(3 * S_M) // 2)
    np.fill_diagonal(cpos, False)
    np.fill_diagonal(cneg, False)
    cadj = cpos | cneg

    rat_bb, M_bb = rational_block(bv_i, bA_n, bq_n, b_sf, b_sgn, bv_i, bA_n, bq_n, b_sf, b_sgn)
    bm2 = rat_bb & (M_bb == -2 * S_M)
    b0 = rat_bb & (M_bb == 0)
    np.fill_diagonal(bm2, False)
    np.fill_diagonal(b0, False)
    badj = bm2 | b0
    bcross = rat_bb & ((M_bb == S_M) | (M_bb == -S_M))

    rat_cb, M_cb = rational_block(cv_i, cA_n, cq_n, c_sf, c_sgn, bv_i, bA_n, bq_n, b_sf, b_sgn)
    cb_ok = rat_cb & ((M_cb == S_M) | (M_cb == -S_M))

    return {
        "d0": d0,
        "c_cands": c_cands,
        "b_cands": b_cands,
        "cpos": cpos,
        "cneg": cneg,
        "cadj": cadj,
        "bm2": bm2,
        "b0": b0,
        "badj": badj,
        "bcross": bcross,
        "cb_ok": cb_ok,
    }


def s1_o2_gram_lp_data_qq(data: dict, br: dict, sub_ic, sub_ib) -> tuple[list[list[Fraction]], list[Fraction]]:
    """Build exact QQ Gram + ZeroSum equality system (A_eq, b_eq) in O(2) using
    W_piv = (20M - M^2)[piv, piv], A_k, rem1_k, and squarefree-split b_k.
    """
    piv = data["piv"]
    rk = len(piv)
    W_piv = data["W_piv"]
    V_mat = data["V_mat"]
    c_cands = br["c_cands"]
    b_cands = br["b_cands"]
    d0 = br["d0"]

    c_items = [c_cands[int(k)] for k in sub_ic]
    b_items = [b_cands[int(k)] for k in sub_ib]
    nc = len(c_items)
    nb = len(b_items)
    nvar = nc + nb

    # Extract pivot rows for C and B
    c_u = [[Fraction(int(V_mat[it[0], w])) for w in piv] for it in c_items]
    b_u = [[Fraction(int(V_mat[it[0], w])) for w in piv] for it in b_items]

    rows = []
    rhs = []

    # 1. Sizes
    rows.append([Fraction(1)] * nc + [Fraction(0)] * nb)
    rhs.append(Fraction(24))
    rows.append([Fraction(0)] * nc + [Fraction(1)] * nb)
    rhs.append(Fraction(32))

    # 2. Zero-sums on piv coordinates (equivalent to all 16 since cycle sum == 0)
    for pi in range(rk):
        rows.append([c_u[k][pi] for k in range(nc)] + [Fraction(0)] * nb)
        rhs.append(Fraction(0))
        rows.append([Fraction(0)] * nc + [b_u[k][pi] for k in range(nb)])
        rhs.append(Fraction(0))

    # 3. Off-diagonal piv Gram (u_i u_j == W_piv[i, j], i < j; note diagonal is identically 56 == W_piv[i,i])
    for i in range(rk):
        for j in range(i + 1, rk):
            rows.append([c_u[k][i] * c_u[k][j] for k in range(nc)] + [b_u[k][i] * b_u[k][j] for k in range(nb)])
            rhs.append(W_piv[i][j])

    # 4. A-axis equations: sum u_i A = 0, sum A^2 = 20 * d0
    for i in range(rk):
        rows.append([c_u[k][i] * c_items[k][1] for k in range(nc)] + [b_u[k][i] * b_items[k][1] for k in range(nb)])
        rhs.append(Fraction(0))
    rows.append([c_items[k][1] ** 2 for k in range(nc)] + [b_items[k][1] ** 2 for k in range(nb)])
    rhs.append(Fraction(20) * d0)

    # 5. b-axis norm: sum rem1 = 20
    rows.append([c_items[k][2] for k in range(nc)] + [b_items[k][2] for k in range(nb)])
    rhs.append(Fraction(20))

    # 6. Squarefree-split b cross equations (sound for all {0,1} vectors via Q-indep of sqrt(d))
    sf_active = sorted({it[4] for it in c_items + b_items if it[4] != 0})
    for d in sf_active:
        c_bcoeff = [c_items[k][5] * c_items[k][3] if c_items[k][4] == d else Fraction(0) for k in range(nc)]
        b_bcoeff = [b_items[k][5] * b_items[k][3] if b_items[k][4] == d else Fraction(0) for k in range(nb)]
        for i in range(rk):
            rows.append([c_u[k][i] * c_bcoeff[k] for k in range(nc)] + [b_u[k][i] * b_bcoeff[k] for k in range(nb)])
            rhs.append(Fraction(0))
        rows.append([c_items[k][1] * c_bcoeff[k] for k in range(nc)] + [b_items[k][1] * b_bcoeff[k] for k in range(nb)])
        rhs.append(Fraction(0))

    return rows, rhs


def s1_solve_cp_o2_qq(data: dict, br: dict, sub_ic, sub_ib, fix_c, max_t: float = 30.0) -> tuple[bool, str]:
    """Exact zero-slack integer CP-SAT killer for O(2) S1 branches."""
    from ortools.sat.python import cp_model
    V_mat = data["V_mat"]
    c_cands = br["c_cands"]
    b_cands = br["b_cands"]
    cneg, cadj, cb_ok = br["cneg"], br["cadj"], br["cb_ok"]
    bm2, badj, bcross = br["bm2"], br["badj"], br["bcross"]
    nc, nb = len(sub_ic), len(sub_ib)

    cneg_s = cneg[np.ix_(sub_ic, sub_ic)]
    cadj_s = cadj[np.ix_(sub_ic, sub_ic)]
    c_vidxs = [c_cands[int(k)][0] for k in sub_ic]

    # 1) C0-alone exact CP-SAT with exact PSD integer test inequalities
    m0 = cp_model.CpModel()
    xc0 = [m0.NewBoolVar(f"c{i}") for i in range(nc)]
    m0.Add(sum(xc0) == 24)
    for fi in fix_c:
        m0.Add(xc0[fi] == 1)
    for w in range(16):
        m0.Add(sum(int(V_mat[c_vidxs[k], w]) * xc0[k] for k in range(nc)) == 0)
    for a in range(nc):
        for b in np.where(~cadj_s[a, a + 1:])[0] + a + 1:
            m0.Add(xc0[a] + xc0[b] <= 1)
        nbs = [xc0[b] for b in np.where(cneg_s[a])[0]]
        m0.Add(sum(nbs) >= 8 - 24 * (1 - xc0[a]))
        m0.Add(sum(nbs) <= 8 + 24 * (1 - xc0[a]))
    for w_vec, rhs_f in data["psd_tests"]:
        rhs_int = int(rhs_f)
        vals = [int(sum(w_vec[r] * int(V_mat[c_vidxs[k], r]) for r in range(16))) ** 2 for k in range(nc)]
        m0.Add(sum(vals[k] * xc0[k] for k in range(nc)) <= rhs_int)

    sv0 = cp_model.CpSolver()
    sv0.parameters.max_time_in_seconds = 5.0
    sv0.parameters.num_search_workers = 8
    st0 = sv0.Solve(m0)
    if st0 == cp_model.INFEASIBLE:
        return True, f"C0_ALONE_INFEASIBLE({sv0.WallTime():.2f}s)"

    # 2) Full C0 + B2 + B3 with exact lcm-cleared equalities (0 slack!)
    b_vidxs = [b_cands[int(k)][0] for k in sub_ib]
    cb_s = cb_ok[np.ix_(sub_ic, sub_ib)]
    badj_s = badj[np.ix_(sub_ib, sub_ib)]
    bm2_s = bm2[np.ix_(sub_ib, sub_ib)]
    bcross_s = bcross[np.ix_(sub_ib, sub_ib)]

    m = cp_model.CpModel()
    xc = [m.NewBoolVar(f"c{i}") for i in range(nc)]
    xb2 = [m.NewBoolVar(f"b2_{i}") for i in range(nb)]
    xb3 = [m.NewBoolVar(f"b3_{i}") for i in range(nb)]
    m.Add(sum(xc) == 24)
    m.Add(sum(xb2) == 16)
    m.Add(sum(xb3) == 16)
    for fi in fix_c:
        m.Add(xc[fi] == 1)
    for k in range(nb):
        m.Add(xb2[k] + xb3[k] <= 1)
    m.Add(sum(k * xb2[k] for k in range(nb)) <= sum(k * xb3[k] for k in range(nb)))
    for w in range(16):
        m.Add(sum(int(V_mat[c_vidxs[k], w]) * xc[k] for k in range(nc)) == 0)
        m.Add(sum(int(V_mat[b_vidxs[k], w]) * xb2[k] for k in range(nb)) == 0)
        m.Add(sum(int(V_mat[b_vidxs[k], w]) * xb3[k] for k in range(nb)) == 0)
    for a in range(nc):
        for b in np.where(~cadj_s[a, a + 1:])[0] + a + 1:
            m.Add(xc[a] + xc[b] <= 1)
        nbs = [xc[b] for b in np.where(cneg_s[a])[0]]
        m.Add(sum(nbs) >= 8 - 24 * (1 - xc[a]))
        m.Add(sum(nbs) <= 8 + 24 * (1 - xc[a]))
        for k in np.where(~cb_s[a])[0]:
            m.Add(xc[a] + xb2[k] + xb3[k] <= 1)
    for k1 in range(nb):
        for k2 in np.where(~badj_s[k1, k1 + 1:])[0] + k1 + 1:
            m.Add(xb2[k1] + xb2[k2] <= 1)
            m.Add(xb3[k1] + xb3[k2] <= 1)
        for k2 in np.where(~bcross_s[k1, k1 + 1:])[0] + k1 + 1:
            m.Add(xb2[k1] + xb3[k2] <= 1)
            m.Add(xb3[k1] + xb2[k2] <= 1)
        nbs2 = [xb2[k2] for k2 in np.where(bm2_s[k1])[0]]
        m.Add(sum(nbs2) >= 2 - 16 * (1 - xb2[k1]))
        m.Add(sum(nbs2) <= 2 + 16 * (1 - xb2[k1]))
        nbs3 = [xb3[k2] for k2 in np.where(bm2_s[k1])[0]]
        m.Add(sum(nbs3) >= 2 - 16 * (1 - xb3[k1]))
        m.Add(sum(nbs3) <= 2 + 16 * (1 - xb3[k1]))

    # Exact rational Gram equalities cleared by lcm -> exact == in CP-SAT
    A_eq_q, b_eq_q = s1_o2_gram_lp_data_qq(data, br, sub_ic, sub_ib)
    for row_q, rhs_q in zip(A_eq_q[2 + 2 * len(data["piv"]):], b_eq_q[2 + 2 * len(data["piv"]):]):
        c_ints, rhs_int = clear_linear_eq_to_ints(row_q, rhs_q)
        max_sum = sum(abs(v) for v in c_ints) + abs(rhs_int)
        assert max_sum < 10**15
        expr = sum(c_ints[k] * xc[k] for k in range(nc) if c_ints[k]) + sum(
            c_ints[nc + k] * (xb2[k] + xb3[k]) for k in range(nb) if c_ints[nc + k]
        )
        m.Add(expr == rhs_int)

    sv = cp_model.CpSolver()
    sv.parameters.max_time_in_seconds = max_t
    sv.parameters.num_search_workers = 8
    st = sv.Solve(m)
    return (st == cp_model.INFEASIBLE), f"FULL={sv.StatusName(st)}({sv.WallTime():.2f}s)"


def _exact_cand_key_o2(V_mat, c_cands, L_mp, G_int, k_idx: int, req_indices: Sequence[int], perm: Sequence[int]):
    """Exact Stab invariant key for O(2) candidate k_idx with fixed anchors req_indices."""
    it = c_cands[k_idx]
    vi, A_k, rem1_k, q_k, sf_d, sgn = it
    tv = V_mat[vi]
    tv_p = tuple(int(tv[p]) for p in perm)
    dots = tuple(int(G_int[c_cands[r][0], vi]) for r in req_indices)
    # Note A_k, rem1_k, sgn completely determine candidate residual coords modulo g(r, k)
    return (tv_p, dots, (A_k.numerator, A_k.denominator), (rem1_k.numerator, rem1_k.denominator), sf_d, sgn)


def s1_o2_run_exact(part: Sequence[int], save_certs: bool = True) -> dict:
    """Complete zero-float-trust O(2) exact certification for S1 partition `part` (`(6,6,4)` or `(8,4,4)`)."""
    import json, os, time
    t_start = time.time()
    data = s1_load_vectors_qq(part)
    V_mat = data["V_mat"]
    L_mp = data["L_mp"]
    G_int = data["G_int"]
    res_c = data["res_c"]

    case0 = s1_solve_case0_qq(data)
    print(f"[{part}] Case 0: {case0}")

    perms = aut_perms_cycles(part)
    orbs = {}
    for i, r in enumerate(res_c):
        if r <= 0:
            continue
        tv = V_mat[i]
        can = min(tuple(int(tv[p]) for p in perm) for perm in perms)
        orbs.setdefault(can, []).append(i)
    orb_reps = sorted([lst[0] for lst in orbs.values()], key=lambda idx: (-res_c[idx], idx))

    farkas_certs = []
    cp_kills = []
    stats = {"orbs": len(orb_reps), "peel": 0, "lp": 0, "cp": 0, "surv": 0}
    all_dead = True

    def kill_lp_or_s2_cp(br, sub_ic, sub_ib, fix_vals, stab, tag_prefix):
        sub_ic_list = [int(x) for x in sub_ic]
        fix_pos = [sub_ic_list.index(v) for v in fix_vals]
        A_eq_q, b_eq_q = s1_o2_gram_lp_data_qq(data, br, sub_ic_list, sub_ib)
        dead_lp, cert = certify_eq_lp_farkas(A_eq_q, b_eq_q, fix_pos)
        if dead_lp:
            stats["lp"] += 1
            farkas_certs.append({
                "tag": tag_prefix,
                "nc": len(sub_ic_list),
                "nb": len(sub_ib),
                "n_eq": len(A_eq_q),
                "fix": fix_pos,
                "cert": cert,
            })
            return True

        # Cumulative Stab(fix_vals) orbit split on N_{-1.5}(s0)
        c_cands = br["c_cands"]
        cneg, cadj, cb_ok = br["cneg"], br["cadj"], br["cb_ok"]
        bm2, b0, badj, bcross = br["bm2"], br["b0"], br["badj"], br["bcross"]
        req_base = tuple(fix_vals)
        neg0_pool = [k for k in sub_ic_list if k not in req_base and cneg[0, k]]
        neg_orbs = {}
        for k in neg0_pool:
            can = min(_exact_cand_key_o2(V_mat, c_cands, L_mp, G_int, k, req_base, perm) for perm in stab)
            neg_orbs.setdefault(can, []).append(k)
        cur_c = set(sub_ic_list)
        for s2i, s2_lst in enumerate(neg_orbs.values()):
            s2 = s2_lst[0]
            if s2 not in cur_c:
                continue
            cand_c = [k for k in cur_c if k in req_base or k == s2 or cadj[s2, k]]
            cand_b = [k for k in sub_ib if cb_ok[s2, k]]
            sic2, sib2 = s1_peel_2d(cneg, br["cpos"], cadj, cb_ok, bm2, b0, badj, bcross,
                                    cand_c, cand_b, req_ic=req_base + (s2,))
            if len(sic2) < 24 or len(sib2) < 32:
                stats["peel"] += 1
            else:
                sic2_list = [int(x) for x in sic2]
                fc2 = [sic2_list.index(v) for v in req_base + (s2,)]
                A2, b2 = s1_o2_gram_lp_data_qq(data, br, sic2_list, sib2)
                d2, cert2 = certify_eq_lp_farkas(A2, b2, fc2)
                if d2:
                    stats["lp"] += 1
                    farkas_certs.append({
                        "tag": f"{tag_prefix}_s2_{s2i}",
                        "nc": len(sic2_list),
                        "nb": len(sib2),
                        "n_eq": len(A2),
                        "fix": fc2,
                        "cert": cert2,
                    })
                else:
                    d_cp, msg_cp = s1_solve_cp_o2_qq(data, br, sic2_list, sib2, fc2, max_t=30.0)
                    if d_cp:
                        stats["cp"] += 1
                        cp_kills.append({"tag": f"{tag_prefix}_s2_{s2i}", "nc": len(sic2_list), "nb": len(sib2), "msg": msg_cp})
                    else:
                        stats["surv"] += 1
                        print(f"    SURV {tag_prefix} s2={s2i}: {msg_cp}")
                        return False
            for k in s2_lst:
                cur_c.discard(k)
        return True

    for oi, s0 in enumerate(orb_reps):
        t0 = time.time()
        br = s1_o2_build_branch_qq(data, s0)
        c_cands, b_cands = br["c_cands"], br["b_cands"]
        cneg, cpos, cadj, cb_ok = br["cneg"], br["cpos"], br["cadj"], br["cb_ok"]
        bm2, b0, badj, bcross = br["bm2"], br["b0"], br["badj"], br["bcross"]
        ic, ib = s1_peel_2d(cneg, cpos, cadj, cb_ok, bm2, b0, badj, bcross,
                            range(len(c_cands)), range(len(b_cands)), req_ic=(0,))
        if len(ic) < 24 or len(ib) < 32:
            stats["peel"] += 1
            print(f"[{part}] orb {oi}: PEEL({len(ic)},{len(ib)}) -> DEAD")
            continue

        tv0 = V_mat[s0]
        stab_s0 = [perm for perm in perms if all(tv0[perm[q]] == tv0[q] for q in range(16))]

        if len(ic) <= 360:
            ic_list = [int(x) for x in ic]
            A_q, b_q = s1_o2_gram_lp_data_qq(data, br, ic_list, ib)
            d, cert = certify_eq_lp_farkas(A_q, b_q, [ic_list.index(0)])
            if d:
                stats["lp"] += 1
                farkas_certs.append({"tag": f"orb{oi}", "nc": len(ic_list), "nb": len(ib), "n_eq": len(A_q), "fix": [ic_list.index(0)], "cert": cert})
                print(f"[{part}] orb {oi}: FARKAS_DEAD(nc={len(ic)},nb={len(ib)},gap~{int(cert['gap'][0])/int(cert['gap'][1]):.3f})")
                continue

        # Case B0: sf_d == 0
        z_sub = [int(k) for k in ic if c_cands[int(k)][4] == 0]
        if len(z_sub) >= 24:
            sic0, sib0 = s1_peel_2d(cneg, cpos, cadj, cb_ok, bm2, b0, badj, bcross, z_sub, ib, req_ic=(0,))
            if len(sic0) < 24 or len(sib0) < 32:
                stats["peel"] += 1
            else:
                if not kill_lp_or_s2_cp(br, sic0, sib0, (0,), stab_s0, f"orb{oi}_B0"):
                    all_dead = False

        # Case B1: sgn == +1 (up to b -> -b reflection)
        nz = [int(k) for k in ic if c_cands[int(k)][5] == 1 and int(k) != 0]
        sub_orbs = {}
        for k in nz:
            can = min(_exact_cand_key_o2(V_mat, c_cands, L_mp, G_int, k, (0,), perm) for perm in stab_s0)
            sub_orbs.setdefault(can, []).append(k)
        for soi, lst in enumerate(sub_orbs.values()):
            s1 = lst[0]
            cand_c = [int(k) for k in ic if int(k) == 0 or int(k) == s1 or cadj[s1, int(k)]]
            cand_b = [int(k) for k in ib if cb_ok[s1, int(k)]]
            sub_ic, sub_ib = s1_peel_2d(cneg, cpos, cadj, cb_ok, bm2, b0, badj, bcross, cand_c, cand_b, req_ic=(0, s1))
            if len(sub_ic) < 24 or len(sub_ib) < 32:
                stats["peel"] += 1
                continue
            tv1 = V_mat[c_cands[s1][0]]
            stab_01 = [p for p in stab_s0 if all(tv1[p[q]] == tv1[q] for q in range(16))]
            if not kill_lp_or_s2_cp(br, sub_ic, sub_ib, (0, s1), stab_01, f"orb{oi}_B1_{soi}"):
                all_dead = False
        print(f"[{part}] orb {oi}/{len(orb_reps)} ({len(sub_orbs)} B1, {time.time()-t0:.1f}s) stats={stats}")

    elapsed = round(time.time() - t_start, 2)
    out = {
        "module": f"s1_{'_'.join(map(str, part))}",
        "part": list(part),
        "all_dead": all_dead and stats["surv"] == 0,
        "case0": case0,
        "stats": stats,
        "n_farkas_certs": len(farkas_certs),
        "n_cp_kills": len(cp_kills),
        "elapsed_sec": elapsed,
    }
    if save_certs:
        res_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
        os.makedirs(res_dir, exist_ok=True)
        out_path = os.path.join(res_dir, f"s1_{'_'.join(map(str, part))}_certs.json")
        with open(out_path, "w") as f:
            json.dump({**out, "farkas_certs": farkas_certs, "cp_kills": cp_kills}, f)
        out["cert_path"] = out_path
    print(f">>> [{part}] ALL_DEAD={out['all_dead']} in {elapsed:.1f}s | {stats} <<<")
    return out

