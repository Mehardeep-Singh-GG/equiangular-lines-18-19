"""Exhaustive Fourier-domain search for Z_p-equivariant Seidel matrices S
for (d=18, n=58) and (d=19, n=73) with rank(5I + S) <= d and 5I + S >= 0.

Decomposes n = c + k * p (c fixed points, k orbits of prime size p):
- Trivial character block: (c + k) x (c + k)
- (p - 1) nontrivial character blocks (galois conjugates): k x k Hermitian!
If each nontrivial k x k block has rank <= r_nt (e.g., r_nt = 1),
every 2x2 minor vanishes in Z[zeta_p] and every diagonal >= 0 across ALL Galois embeddings!
"""

from __future__ import annotations
import itertools
import time
from typing import Dict, List, Tuple
import numpy as np


def check_zp_rank1_blocks(d: int, n: int, p: int, k: int, c: int):
    """Exact search for Z_p-equivariant Seidel matrices with rank-1 nontrivial k x k blocks.
    For a rank-1 Hermitian k x k PSD block G_hat(zeta) = 5 I_k + B_hat(zeta):
      1. Diagonal entry d_a(j) = 5 + sum_{t=1}^{(p-1)/2} 2*s_t*cos(2*pi*j*t/p) >= 0 for all j=1..(p-1)/2.
      2. For each pair (a, b), |b_{ab}(j)|^2 == d_a(j) * d_b(j) for ALL j=1..(p-1)/2!
      3. Rank compatibility: nontrivial blocks contribute (p-1)*1 = p-1 to rank,
         trivial block (c+k)x(c+k) can contribute <= c+k, wait:
         nullity >= n - d  =>  trivial nullity >= (n - d) - (p - 1)*(k - 1).
    """
    half_p = (p - 1) // 2
    angles = 2.0 * np.pi / p
    # Precompute cos table for j=1..half_p, t=1..half_p
    cos_tab = np.array([[2.0 * np.cos(angles * j * t) for t in range(1, half_p + 1)] for j in range(1, half_p + 1)])

    # Find ALL valid diagonal circulant signs s in {-1,+1}^half_p with d(j) >= -1e-9 for all j
    valid_diags = []
    for bits in itertools.product([-1, 1], repeat=half_p):
        s_vec = np.array(bits, dtype=np.float64)
        dj = 5.0 + cos_tab @ s_vec
        if np.all(dj >= -1e-9):
            valid_diags.append((bits, dj))

    print(f"  [n={n}, d={d}: p={p}, k={k}, c={c}] valid symmetric diag blocks (out of {1<<half_p}): {len(valid_diags)}")
    if not valid_diags:
        return

    # Precompute all 2^p off-diagonal circulants b in {-1,+1}^p and their |b(j)|^2 spectra
    zeta = np.exp(1j * angles * np.arange(1, half_p + 1))
    # Matrix Z_{j, t} = zeta_j^t for j=1..half_p, t=0..p-1
    Z = np.array([[np.exp(1j * angles * j * t) for t in range(p)] for j in range(1, half_p + 1)])
    all_b = np.array(list(itertools.product([-1, 1], repeat=p)), dtype=np.float64)  # 2^p x p
    B_hat = all_b @ Z.T  # 2^p x half_p complex
    B_abs2 = np.real(B_hat * np.conj(B_hat))  # 2^p x half_p

    # Check for each pair of valid_diags (i1 <= i2) whether ANY b matches |b(j)|^2 == d1(j)*d2(j)
    # Wait: use rounded integer key (round(val * 10^6)) for fast matching, then exact check!
    spec_map: Dict[Tuple[int, ...], List[int]] = {}
    for idx in range(len(all_b)):
        key = tuple(int(round(v * 1e5)) for v in B_abs2[idx])
        spec_map.setdefault(key, []).append(idx)

    compatible_pairs = 0
    for i1, (b1, d1) in enumerate(valid_diags):
        for i2, (b2, d2) in enumerate(valid_diags):
            if i2 < i1:
                continue
            target = d1 * d2
            tkey = tuple(int(round(v * 1e5)) for v in target)
            matches = spec_map.get(tkey, [])
            if matches:
                compatible_pairs += 1
                print(f"    MATCH! diag {b1} x {b2} -> {len(matches)} off-diag circulants! d1={np.round(d1,3)}, d2={np.round(d2,3)}")
    print(f"    Total compatible diag pairs with rank-1 off-diag: {compatible_pairs}")


def main():
    print("=== EXHAUSTIVE FOURIER SEARCH FOR Z_p-EQUIVARIANT RANK-1-BLOCK SEIDEL MATRICES ===")
    # Check d=18, n=58 decompositions n = c + k*p with (p-1)*(k-1) <= 40 and p-1 + c + k >= 18
    for p, k, c in [
        (11, 5, 3),   # 3 + 55 = 58, rank = 10 + <=8 = 18
        (11, 4, 14),  # 14 + 44 = 58, nontrivial nullity = 30, trivial 18x18 needs 10 zeros
        (7, 8, 2),    # 2 + 56 = 58, nontrivial nullity = 42 > 40 (needs 1 rank-2 block or rank-2 blocks)
        (7, 7, 9),    # 9 + 49 = 58, nontrivial nullity = 36, trivial 16x16 needs 4 zeros
        (13, 4, 6),   # 6 + 52 = 58, nontrivial nullity = 36, trivial 10x10 needs 4 zeros
        (19, 3, 1),   # 1 + 57 = 58, nontrivial nullity = 36, trivial 4x4 needs 4 zeros (impossible unless 0 block)
        (5, 11, 3),   # 3 + 55 = 58, nontrivial nullity = 40, trivial 14x14
    ]:
        check_zp_rank1_blocks(18, 58, p, k, c)

    print()
    # Check d=19, n=73 decompositions n = c + k*p
    for p, k, c in [
        (7, 10, 3),   # 3 + 70 = 73, nontrivial nullity = 54, trivial 13x13
        (11, 6, 7),   # 7 + 66 = 73, nontrivial nullity = 50, trivial 13x13 needs 4 zeros
        (13, 5, 8),   # 8 + 65 = 73, nontrivial nullity = 48, trivial 13x13 needs 6 zeros
        (13, 6, -5),  # invalid
        (5, 14, 3),   # 3 + 70 = 73, nontrivial nullity = 52, trivial 17x17 needs 2 zeros
    ]:
        if c >= 0:
            check_zp_rank1_blocks(19, 73, p, k, c)


if __name__ == "__main__":
    main()
