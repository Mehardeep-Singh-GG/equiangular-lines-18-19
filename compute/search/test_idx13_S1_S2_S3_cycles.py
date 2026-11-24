"""Check exact PSD rank <= 15 constraints on 20*E_15[B_a U C_0] for S1, S2, S3!
For S1 (even cycle partitions of 16), enumerate ALL b in {+-1}^16 with zero sum on every cycle
and b^T P b <= 9, and check rank(S_C) <= t - 1!
Also check exact S2 and S3 cycle/degree/sum constraints on B_a!
"""
from __future__ import annotations
import itertools
import numpy as np


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


def zero_sum_vecs_on_parts(parts: list[int]) -> np.ndarray:
    """All {+-1} vectors with zero sum on each part (only even parts!)."""
    blocks = []
    for L in parts:
        assert L % 2 == 0
        sub = []
        for ones in itertools.combinations(range(L), L // 2):
            v = -np.ones(L, dtype=np.float64)
            v[list(ones)] = 1.0
            sub.append(v)
        blocks.append(np.array(sub))
    # Cartesian product
    cur = blocks[0]
    for blk in blocks[1:]:
        n1, d1 = cur.shape
        n2, d2 = blk.shape
        c1 = np.repeat(cur, n2, axis=0)
        c2 = np.tile(blk, (n1, 1))
        cur = np.hstack([c1, c2])
    return cur


def check_S1_even_partitions():
    print("=== S1=(24,48,0,2): Checking ALL 7 even-cycle partitions of 16 ===")
    even_parts = [
        [16],
        [4, 12],
        [6, 10],
        [8, 8],
        [4, 4, 8],
        [4, 6, 6],
        [4, 4, 4, 4],
    ]
    for parts in even_parts:
        t = len(parts)
        A = cycle_union_adj(parts).astype(np.float64)
        ev, evec = np.linalg.eigh(2.0 * np.eye(16) - A)
        nz = np.where(np.abs(ev) > 1e-8)[0]
        P = (evec[:, nz] / ev[nz]) @ evec[:, nz].T
        B_cand = zero_sum_vecs_on_parts(parts)
        qvals = np.sum((B_cand @ P) * B_cand, axis=1)
        ok_idx = np.where(qvals <= 9.0 + 1e-7)[0]
        print(f"  parts={str(parts):14s} t={t}: total zero-sum={len(B_cand):5d}, b^T P b <= 9: {len(ok_idx):4d} (min={qvals.min():.3f}, eq9={np.sum(np.abs(qvals-9.0)<1e-6)})")
        if len(ok_idx) > 0 and t == 2:
            # Check pairwise compatibility:
            # S_C = (5I + W00 - 1/2 J) - 1/2 B^T P B >= 0 of rank <= 1 (so S_C = v v^T)!
            # Notice diag(S_C)_u = (9 - b_u^T P b_u)/2 = v_u^2, and off-diag (S_C)_{uw} = W_{uw} - 1/2 - 1/2 b_u^T P b_w = v_u v_w!
            # Wait: W_{uw} in {+1, -1}, so (b_u^T P b_w + 2 v_u v_w) MUST equal 2 W_{uw} - 1 in {+1, -3}!!
            # Wait: since v_u = +- sqrt((9 - q_u)/2), check EVERY pair (u, w) with ALL 4 sign choices of (v_u, v_w)!
            B_ok = B_cand[ok_idx]
            q_ok = qvals[ok_idx]
            v_mag = np.sqrt(np.maximum(0.0, (9.0 - q_ok) / 2.0))
            G = B_ok @ P @ B_ok.T
            # For pair (i, j): check if G[i,j] + 2*v_mag[i]*v_mag[j] in {+1, -3} OR G[i,j] - 2*v_mag[i]*v_mag[j] in {+1, -3}!
            vp = 2.0 * np.outer(v_mag, v_mag)
            c1 = (np.abs(G + vp - 1.0) < 1e-6) | (np.abs(G + vp + 3.0) < 1e-6)
            c2 = (np.abs(G - vp - 1.0) < 1e-6) | (np.abs(G - vp + 3.0) < 1e-6)
            compat = c1 | c2
            np.fill_diagonal(compat, False)
            print(f"    -> t=2 compat nodes={len(ok_idx)}, max_deg={compat.sum(axis=1).max()}")
            # Wait: remember B^{(a)} also needs column sums = 0? Not necessarily per B^{(a)}, wait: 1_{24}^T S_C 1_{24} = 0 => sum_u v_u = 0!
            # Check if ANY 24-clique exists via degree peeling (deg >= 23 needed for a 24-clique!)
            alive = np.ones(len(ok_idx), dtype=bool)
            while True:
                degs = compat[np.ix_(alive, alive)].sum(axis=1)
                bad = degs < 23
                if not np.any(bad):
                    break
                idx_alive = np.where(alive)[0]
                alive[idx_alive[bad]] = False
                if alive.sum() == 0:
                    break
            print(f"    -> after 23-core peeling: {alive.sum()} vertices survive!")
        elif len(ok_idx) > 0 and t >= 3:
            # Check trace / average bound!
            # Remember Tr(S_C) = Tr(5I + W00 - 1/2 J) - 1/2 sum_{u=1}^{24} b_u^T P b_u
            # = (24*5 + 0 - 12) - 1/2 sum q_u = 108 - 1/2 sum q_u!
            # Wait: what is Tr(S_C) vs rank(S_C) <= t - 1?!
            # Also what is Tr(10I + 2W00 - J) = 216, and each diag of B^T P B is q_u <= 9!
            # Wait: notice sum q_u = Tr(B^T P B) <= 24 * max_q, and S_C >= 0 has rank <= t-1.
            # Wait: what is max eigenvalue of 5I + W00 - 1/2 J? Up to 20 (from E_15)!
            # Check which qvals occur!
            uniq_q = np.unique(np.round(q_ok, 4))
            print(f"    -> unique qvals <= 9 ({len(uniq_q)}): {uniq_q[:15]}")


if __name__ == "__main__":
    check_S1_even_partitions()
