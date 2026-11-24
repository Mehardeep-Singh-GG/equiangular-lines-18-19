"""De Caen-Jacobi exact resolvent attack at x = 15 on (19, 74) idx=13:
  S1: (24, 48, 0, 2)
  S2: (25, 45, 3, 1)
  S3: (26, 42, 6, 0)

Resolvent identity:
  R(x) = (xI - S)^{-1}
       = ((x-10)I + S) / ((x+5)(x-15))
         - 64 / ((x+5)(x-15)(x-11)) E_11
         + 44 / ((x+5)(x-15)(x-17)) E_17.

Let M(x) = (x+5)(x-15) R(x)[V].
For any V of size m, det(xI - S[V^c]) = (x+5)^{55-m} (x-11)^3 (x-15)^{15-m} (x-17) det(M(x)) in Z[x].
Hence for m > 15, ord_{x=15}(det M(x)) >= m - 15!
"""
from __future__ import annotations
import itertools
import sympy as sp
import numpy as np


def partitions_min3(n: int, min_part: int = 3):
    if n == 0:
        yield []
        return
    for k in range(min_part, n + 1):
        for rest in partitions_min3(n - k, k):
            yield [k] + rest


def cycle_union_adj(parts: list[int]) -> np.ndarray:
    n = sum(parts)
    A = np.zeros((n, n), dtype=int)
    off = 0
    for L in parts:
        for i in range(L):
            A[off + i, off + (i + 1) % L] = 1
            A[off + (i + 1) % L, off + i] = 1
        off += L
    return A


def attack_S1_Ba():
    print("=== S1 = (24, 48, 0, 2): Testing all 21 cycle-partitions of B_a (size 16) ===")
    parts_list = list(partitions_min3(16, 3))
    print(f"Total partitions of 16 into parts >= 3: {len(parts_list)}")

    # Generate all 12870 vectors b in {+-1}^16 with sum(b) = 0
    # Wait: by symmetry, fix b[0] = +1 (up to global sign b -> -b, wait b^T P b and b1^T P b2 are invariant under negating both,
    # Wait: W_{uv} is NOT invariant if we negate one b_u; wait we can keep all 12870! 12870 is tiny in numpy!)
    from itertools import combinations
    b_list = []
    for ones in combinations(range(16), 8):
        v = -np.ones(16, dtype=np.int64)
        v[list(ones)] = 1
        b_list.append(v)
    B_all = np.array(b_list, dtype=np.float64)  # 12870 x 16

    for parts in parts_list:
        t = len(parts)
        A = cycle_union_adj(parts).astype(np.float64)
        # M(15) on 1_16^perp (+) C_0 is [[2(2I-A)|_{1^perp}, B^{(a)T}], [B^{(a)}, 5I+W00 - 1/2 J_24]].
        # Wait: let's check EXACTLY for V = B_a U {u} (|V| = 17, pole order >= 2 at x=15)!
        # Let's compute exact rational M(x) = M0 + (x-15)*M1 + ...?
        # No, let's check nullity of M(15) on 17x17 matrix [[S_Ba + 5I - 16/3*1/16? Wait: let's write M(15) cleanly!]
        # M(15) on B_a U {u}:
        #   - On B_a x B_a: 5I + S[B_a] - 16 E_11[B_a] - 22 E_17[B_a]
        #                 = 5I + (J - I - 2A) - 16*(1/24)J - 22*(1/66)J
        #                 = 4I - 2A (since 1 - 2/3 - 1/3 = 0!!)
        #   - On B_a x {u}: b (since E_11[B_a, u]=0, E_17[B_a, u]=0!)
        #   - On {u} x {u}: 5 - 16*(1/32) = 9/2!
        # Wait: notice M(15) on B_a U {u} is literally [[2*(2I - A), b], [b^T, 9/2]]!
        # And remember M(15) has kernel >= 1 from 1_16 (since (2I-A)1_16 = 0 and b^T 1_16 = 0)!
        # So ord_{x=15}(det M(x)) >= 2 holds for EVERY u in C_0 if and only if:
        #   Case t=1: det of 16x16 block (1_16^perp (+) e_u) == 0, i.e., b^T (2I - A)^+ b = 9!
        #   Case t=2: nullity of (2I-A)|_{1^perp} is 1, so we need EITHER:
        #     (i) b orthogonal to ker(2I-A) AND b^T (2I-A)^+ b = 9, OR
        #     (ii) Wait! If b is NOT orthogonal to ker(2I-A), then [[0, beta], [beta, ...]] has rank 2, so nullity drops from 2 to 1!
        #          Wait: can ord_{x=15}(det M(x)) STILL be >= 2 when nullity is 1?!
        #          Check: if nullity of M(15) is 1 (ONLY 1_16 is in ker M(15)), then ord >= 2 iff M'(15) restricted to ker(M(15)) vanishes!
        #          Let's check M'(15)[1_16, 1_16]!!
        #          M(x) = ((x-10)I + S) - 64/(x-11) E_11 + 44/(x-17) E_17.
        #          M'(15) = I + 64/16 E_11 - 44/4 E_17 = I + 4 E_11 - 11 E_17.
        #          On 1_16 (unit vector v1 = 1_16 / 4):
        #            v1^T M'(15) v1 = 1 + 4*(16/24) - 11*(16/66) = 1 + 8/3 - 8/3 = 1 != 0!!
        #          WAIT A SECOND!! v1^T M'(15) v1 = +1 != 0 ALWAYS!!
        #          THAT PROVES nullity(M(15)) == 1 implies ord_{x=15}(det M(x)) == 1 (IMPOSSIBLE)!
        #          THEREFORE, nullity(M(15)) MUST BE >= 2 FOR EVERY u in C_0!!
        #
        # Wait: what if t >= 3? Then ker(2I-A)|_{1^perp} already has dim t-1 >= 2!
        # Wait: EVEN FOR t >= 2, we also have V = B_a U {u, v} (|V|=18 -> nullity >= 3? Wait: let's check!)
        # Wait: for t >= 3, M'(15) on ker(2I-A)|_{1^perp} is I! So each vector in ker(M(15)) gives ord 1!
        # Wait: on V = B_a U C_0 (|V|=40), M(15) has nullity >= 25 (since 40 - 15 = 25)!
        # Wait: let's first count how many b in B_all make nullity([[2*(2I-A), b], [b^T, 9/2]]) >= 2!
        eigvals, eigvecs = np.linalg.eigh(2.0 * np.eye(16) - A)
        ker_idx = np.where(np.abs(eigvals) < 1e-8)[0]
        nz_idx = np.where(np.abs(eigvals) >= 1e-8)[0]
        # Basis of ker on 1_16^perp:
        P_pinv = (eigvecs[:, nz_idx] / eigvals[nz_idx]) @ eigvecs[:, nz_idx].T
        # Check for each b:
        #   - proj onto ker (besides 1_16): (U_ker^T b) has norm > 0?
        #   - Wait: if t == 1, ker is ONLY 1_16, so nullity >= 2 iff b^T P_pinv b == 9!
        #   - If t == 2, ker has dim 2 (1_16 + one vector k1). Nullity of [[2(2I-A), b], [b^T, 9/2]] >= 3?
        #     Wait: M(15) has 1_16 in ker, so total nullity >= 2 ALWAYS if k1^T b == 0? No!
        #     If k1^T b != 0, then k1 and b form a 2x2 invertible block [[0, k1^T b], [k1^T b, ...]], leaving ONLY 1_16 in ker (nullity 1 -> IMPOSSIBLE!!)!
        #     SO FOR t == 2, k1^T b MUST BE 0!!
        #     Wait: AND if k1^T b == 0, then ker(M(15)) has dim 2 (1_16 and k1)! What about V = B_a U {u, v} (|V|=18, order >= 3)?
        #     On V = B_a U {u, v}, nullity >= 3! Unless BOTH b_u and b_v satisfy Schur complement = 9 AND pairwise = 2*W_{uv}-1?
        #     Wait: check! For ANY V = B_a U C_0 (|V| = 40), M(15) has kernel >= 25 (rank <= 15)!
        #     Wait: if rank(B_0|_{ker(2I-A)}) = c (where c <= t-1), then rank of [[2(2I-A), B_0], [B_0^T, M_00]] >= (16-t) + 2c!
        #     Even better, check how many b in B_all satisfy (1) k^T b == 0 for all k in ker(2I-A), AND (2) b^T P_pinv b == 9!
        vals_quad = np.sum((B_all @ P_pinv) * B_all, axis=1)
        exact_9 = np.sum(np.abs(vals_quad - 9.0) < 1e-6)
        if t == 2:
            # Find k1 in ker orthogonal to 1_16
            V_ker = eigvecs[:, ker_idx]
            # Project out 1_16
            u0 = np.ones((16, 1)) / 4.0
            V_ker_perp = V_ker - u0 @ (u0.T @ V_ker)
            _, _, vt = np.linalg.svd(V_ker_perp.T)
            k1 = V_ker_perp @ np.array([1.0, 0.0])
            if np.linalg.norm(k1) < 1e-6:
                k1 = V_ker_perp @ np.array([0.0, 1.0])
            ok_k1 = np.abs(B_all @ k1) < 1e-6
            n_k1 = np.sum(ok_k1)
            n_both = np.sum(ok_k1 & (np.abs(vals_quad - 9.0) < 1e-6))
            print(f"  parts={str(parts):20s} t={t}: |b^T P b == 9| = {exact_9}, |k1^T b == 0| = {n_k1}, both = {n_both}")
        else:
            # Wait: for t >= 3, check how many b satisfy (b^T P_pinv b == 9 AND ker_perp^T b == 0) too!
            if t == 1:
                print(f"  parts={str(parts):20s} t={t}: |b^T P b == 9| = {exact_9}")
                # Check compatibility graph on those b vectors!
                idx9 = np.where(np.abs(vals_quad - 9.0) < 1e-6)[0]
                if len(idx9) > 0:
                    B9 = B_all[idx9]
                    G9 = B9 @ P_pinv @ B9.T
                    # Check entries close to +1 or -3
                    is_p1 = np.abs(G9 - 1.0) < 1e-6
                    is_m3 = np.abs(G9 + 3.0) < 1e-6
                    compat = is_p1 | is_m3
                    np.fill_diagonal(compat, False)
                    max_deg = np.max(np.sum(compat, axis=1))
                    print(f"    -> t=1 compat graph: {len(idx9)} nodes, max_deg={max_deg}")
            else:
                V_ker = eigvecs[:, ker_idx]
                u0 = np.ones(16) / 4.0
                # Check min/max of vals_quad
                print(f"  parts={str(parts):20s} t={t}: |b^T P b == 9| = {exact_9}, range=[{vals_quad.min():.2f}, {vals_quad.max():.2f}]")


if __name__ == "__main__":
    attack_S1_Ba()
