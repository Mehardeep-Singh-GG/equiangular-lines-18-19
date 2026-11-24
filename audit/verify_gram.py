"""Independent clean-room exact rational verifier for Seidel and Gram matrices.

Given a Seidel matrix S (or Gram matrix G = k*I + S, default k=5), verifies in exact
SymPy integer/rational arithmetic (zero floating point):
1. Symmetry, zero diagonal on S, off-diagonal entries of S in {+1, -1}.
2. Exact rational rank(G) <= d (using SymPy bareiss/RREF over QQ).
3. Exact PSD proof of G via pivot principal submatrix G[P, P]:
   - Exact LDL^T decomposition over QQ with strictly positive diagonal D_ii > 0, AND
   - Exact Sylvester leading principal minors > 0 on G[P, P], AND
   - Exact reconstruction G == (L^T X)^T D (L^T X) entry-by-entry in QQ.
4. Exact characteristic polynomial chi_S(x) and divisibility by (x + k)^(n - d).
"""

from __future__ import annotations

import json
from pathlib import Path
import sympy as sp


def verify_seidel_and_gram(
    S_raw: list[list[int]],
    expected_d: int,
    k: int = 5,
    expected_n: int | None = None,
) -> dict:
    n = len(S_raw)
    if expected_n is not None and n != expected_n:
        raise AssertionError(f"Expected n={expected_n}, got n={n}")
    for row in S_raw:
        if len(row) != n:
            raise AssertionError(f"Non-square matrix: row len {len(row)} != {n}")

    # 1. Exact Seidel structure
    for i in range(n):
        if int(S_raw[i][i]) != 0:
            raise AssertionError(f"Non-zero diagonal at ({i},{i}): {S_raw[i][i]}")
        for j in range(i + 1, n):
            v_ij = int(S_raw[i][j])
            v_ji = int(S_raw[j][i])
            if v_ij != v_ji:
                raise AssertionError(f"Asymmetric at ({i},{j}): {v_ij} != {v_ji}")
            if v_ij not in (1, -1):
                raise AssertionError(f"Invalid off-diagonal entry at ({i},{j}): {v_ij}")

    S = sp.Matrix([[sp.Integer(int(x)) for x in row] for row in S_raw])
    G = k * sp.eye(n) + S

    # 2. Exact rational RREF -> pivot columns and exact rank
    _, pivots = G.rref()
    r = len(pivots)
    if r > expected_d:
        raise AssertionError(f"Rank too large: rank(G) = {r} > d = {expected_d}")

    # 3. Exact PSD certificate on principal submatrix G[P, P]
    P = list(pivots)
    if r > 0:
        G_PP = G.extract(P, P)
        # Sylvester leading principal minors strictly > 0
        for m in range(1, r + 1):
            minor_det = G_PP[:m, :m].det()
            if minor_det <= 0:
                raise AssertionError(
                    f"Leading principal minor {m} of G[P,P] is {minor_det} <= 0"
                )
        # Exact LDL^T over QQ
        L, D = G_PP.LDLdecomposition()
        for i in range(r):
            if D[i, i] <= 0:
                raise AssertionError(f"LDL diagonal D[{i},{i}] = {D[i,i]} <= 0")
        if L * D * L.T != G_PP:
            raise AssertionError("LDLdecomposition reconstruction failed on G[P,P]")

        # Exact rational reconstruction of ALL of G: G_PP * X = G[P, :]
        G_P_all = G.extract(P, list(range(n)))
        X = G_PP.LUsolve(G_P_all)
        V = L.T * X  # r x n over QQ
        G_rec = V.T * D * V
        if G_rec != G:
            raise AssertionError("Exact rational Gram reconstruction V^T D V != G!")

    # 4. Characteristic polynomial check (optional or exact if requested)
    x = sp.Symbol("x")
    chi = sp.Poly(S.charpoly(x).as_expr(), x, domain=sp.ZZ)
    if n > expected_d:
        factor = sp.Poly((x + k) ** (n - expected_d), x, domain=sp.ZZ)
        f_poly, rem = sp.div(chi, factor)
        if rem != 0:
            raise AssertionError(
                f"(x+{k})^{n-expected_d} does not divide chi_S(x); remainder={rem}"
            )
    else:
        f_poly = chi

    return {
        "n": n,
        "d": expected_d,
        "k": k,
        "rank": r,
        "trace_S": int(S.trace()),
        "trace_S2": int((S * S).trace()),
        "f_coeffs_desc": [int(c) for c in f_poly.all_coeffs()],
    }


def load_matrix_file(path: Path) -> tuple[list[list[int]], dict]:
    text = path.read_text().strip()
    if path.suffix == ".json":
        data = json.loads(text)
        if isinstance(data, dict):
            for key in ("seidel", "S", "matrix", "seidel_matrix"):
                if key in data:
                    return data[key], data
            raise ValueError(f"No matrix key found in {path}")
        return data, {}
    # Plain text whitespace-separated matrix
    rows = []
    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        rows.append([int(tok) for tok in line.split()])
    return rows, {}
