"""Exact integer/rational verification for equiangular line systems (alpha = 1/5).

Zero floating-point trust: all checks use SymPy exact integers/rationals.
"""

from __future__ import annotations
import json
from pathlib import Path
from typing import Dict, List, Optional, Tuple
import sympy as sp


def verify_seidel_system(
    S_input: List[List[int]],
    d: int,
    compute_charpoly: bool = True,
) -> Dict:
    """Verify in exact integer/rational arithmetic that S is a Seidel matrix
    representing n equiangular lines in R^d with alpha = 1/5 (G = 5I + S >= 0, rank <= d).

    Returns a dictionary with verification details and raises AssertionError if invalid.
    """
    n = len(S_input)
    assert n > 0, "Empty matrix"
    for i in range(n):
        assert len(S_input[i]) == n, f"Row {i} has length {len(S_input[i])} != {n}"
        for j in range(n):
            val = int(S_input[i][j])
            assert val == S_input[i][j], f"Non-integer entry at ({i},{j})"
            if i == j:
                assert val == 0, f"Diagonal entry ({i},{i}) = {val} != 0"
            else:
                assert val in (-1, 1), f"Off-diagonal entry ({i},{j}) = {val} not in {{-1,+1}}"
                assert S_input[i][j] == S_input[j][i], f"Not symmetric at ({i},{j})"

    S = sp.Matrix(S_input)
    G = 5 * sp.eye(n) + S

    # Find exact column basis B via RREF (exact rational arithmetic)
    rref_mat, pivots = G.rref()
    r = len(pivots)
    assert r <= d, f"rank(5I + S) = {r} > d = {d}"

    B = list(pivots)
    G_BB = G[B, B]

    # Exact PSD proof on G_BB via exact LDL^T decomposition
    L, D = G_BB.LDLdecomposition()
    assert L.shape == (r, r) and D.shape == (r, r)
    assert L * D * L.T == G_BB, "LDL^T reconstruction mismatch"
    diag_D = [D[k, k] for k in range(r)]
    assert all(val > 0 for val in diag_D), f"Non-positive pivot in D: {diag_D}"

    # Verify G factors exactly through B: G = M * G_BB * M^T where M = G[:, B] * G_BB^{-1}
    # Since pivots are from RREF of symmetric G, G_BB is invertible (proven by D > 0),
    # and rank(G) = r = len(B), we explicitly verify G[:, B] * G_BB^{-1} * G[B, :] == G.
    G_BB_inv = G_BB.inv()
    G_colB = G[:, B]
    G_rowB = G[B, :]
    assert G_colB * G_BB_inv * G_rowB == G, "Rank factorization G = G[:,B] G_BB^{-1} G[B,:] failed!"

    result = {
        "n": n,
        "d": d,
        "rank": r,
        "psd_verified": True,
        "basis_indices": B,
        "det_G_BB": int(G_BB.det()),
    }

    if compute_charpoly:
        x = sp.Symbol("x")
        # Factor charpoly over QQ/ZZ
        # Note: computing charpoly of 72x72 in SymPy: use Berkowitz or charpoly(x) on ZZ matrix
        cp = sp.Poly(S.charpoly(x).as_expr(), x, domain="ZZ")
        factors = sp.factor_list(cp.as_expr())
        result["charpoly_str"] = str(sp.factor(cp.as_expr()))
        result["charpoly_factors"] = [
            (str(f), int(mult)) for f, mult in factors[1]
        ]

    return result


def verify_vectors_gram(
    vectors: List[List[int]],
    norm_sq: int,
    allowed_ips: Tuple[int, int],
    d: int,
    compute_charpoly: bool = True,
) -> Tuple[List[List[int]], Dict]:
    """Given integer vectors in Z^m (or Q^m) of squared norm `norm_sq` and pairwise
    inner products in `allowed_ips` = (-a, +a) with a/norm_sq = 1/5,
    build the exact Seidel matrix S and verify it in dimension d.
    """
    n = len(vectors)
    m = len(vectors[0])
    a_neg, a_pos = allowed_ips
    assert a_neg == -a_pos and 5 * a_pos == norm_sq, "Invalid inner product scaling for alpha=1/5"

    # Compute exact Gram matrix of vectors
    V = sp.Matrix(vectors)  # n x m
    Gram = V * V.T
    S = [[0] * n for _ in range(n)]
    for i in range(n):
        assert Gram[i, i] == norm_sq, f"Vector {i} has norm^2 {Gram[i,i]} != {norm_sq}"
        for j in range(i + 1, n):
            ip = Gram[i, j]
            if ip == a_pos:
                S[i][j] = S[j][i] = 1
            elif ip == a_neg:
                S[i][j] = S[j][i] = -1
            else:
                raise AssertionError(f"Pair ({i},{j}) has invalid inner product {ip}")

    info = verify_seidel_system(S, d=d, compute_charpoly=compute_charpoly)
    return S, info


def save_verified_matrix(
    out_path: Path,
    name: str,
    S: List[List[int]],
    verification: Dict,
    metadata: Optional[Dict] = None,
) -> None:
    out_path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "name": name,
        "verification": verification,
        "metadata": metadata or {},
        "S": S,
    }
    out_path.write_text(json.dumps(payload, indent=2))
