"""Test S1, S2, S3 of (19, 74) idx=13 using exact 20*E_15[V] >= 0 and rank <= 15 bounds:
1. For S1=(24,48,0,2):
   - Check t=2 ([4,12], [6,10], [8,8]) with EXACT signed v_u (S_C = v v^T) and max-clique / CP-SAT!
   - Check Z_{12} (B_a <-> B_b) compatibility: z^T P_1 z <= 8 and max-clique / rank(S_22) <= t_1 - 1!
2. For S2=(25,45,3,1) and S3=(26,42,6,0):
   - Verify exact E_11, E_17, and 20*E_15 on B_a U C_2 and check row sums / graph constraints!
"""
from __future__ import annotations
import itertools
import numpy as np
from ortools.sat.python import cp_model


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
    blocks = []
    for L in parts:
        sub = []
        for ones in itertools.combinations(range(L), L // 2):
            v = -np.ones(L, dtype=np.float64)
            v[list(ones)] = 1.0
            sub.append(v)
        blocks.append(np.array(sub))
    cur = blocks[0]
    for blk in blocks[1:]:
        n1, _ = cur.shape
        n2, _ = blk.shape
        cur = np.hstack([np.repeat(cur, n2, axis=0), np.tile(blk, (n1, 1))])
    return cur


def test_S1_t2_signed_and_Z12():
    print("=== Testing S1 B_a <-> B_b (z^T P z <= 8) across all 6 remaining even partitions ===")
    even_parts = [
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
        idx8 = np.where(qvals <= 8.0 + 1e-7)[0]
        print(f"  parts={str(parts):14s} t={t}: |z^T P z <= 8| = {len(idx8)} / {len(B_cand)}")
        if t == 2:
            # Also check exact signed compatibility for V = B_a U C_0 (size 24 clique)
            idx9 = np.where(qvals <= 9.0 + 1e-7)[0]
            B_ok = B_cand[idx9]
            q_ok = qvals[idx9]
            v_mag = np.sqrt(np.maximum(0.0, (9.0 - q_ok) / 2.0))
            G = B_ok @ P @ B_ok.T
            # Expand to signed nodes: if v_mag[i] > 1e-6, create +v and -v!
            nodes_v = []
            nodes_b = []
            for i in range(len(idx9)):
                if v_mag[i] < 1e-6:
                    nodes_v.append(0.0)
                    nodes_b.append(i)
                else:
                    nodes_v.append(+v_mag[i])
                    nodes_b.append(i)
                    nodes_v.append(-v_mag[i])
                    nodes_b.append(i)
            nodes_v = np.array(nodes_v)
            nodes_b = np.array(nodes_b)
            # Check pairwise W_{ij} = (G[bi, bj] + 2*vi*vj + 1)/2 in {-1, +1}
            # AND remember W_{00} * 1 = 7 * 1 (each node needs 15 +1s and 8 -1s!)
            # Wait: also 0 <= S_C <= 20I => ||v||^2 = sum v_u^2 <= 20 => sum q_u >= 176!
            G_full = G[np.ix_(nodes_b, nodes_b)] + 2.0 * np.outer(nodes_v, nodes_v)
            is_p1 = np.abs(G_full - 1.0) < 1e-6
            is_m3 = np.abs(G_full + 3.0) < 1e-6
            np.fill_diagonal(is_p1, False)
            np.fill_diagonal(is_m3, False)
            # Every vertex in a 24-clique must have >= 15 neighbors with +1 AND >= 8 neighbors with -3!
            alive = np.ones(len(nodes_v), dtype=bool)
            while True:
                p1_deg = is_p1[np.ix_(alive, alive)].sum(axis=1)
                m3_deg = is_m3[np.ix_(alive, alive)].sum(axis=1)
                bad = (p1_deg < 15) | (m3_deg < 8)
                if not np.any(bad):
                    break
                ia = np.where(alive)[0]
                alive[ia[bad]] = False
                if alive.sum() == 0:
                    break
            print(f"    -> t=2 signed (15p1, 8m3)-core: {alive.sum()} / {len(nodes_v)} nodes survive!")


def check_S2_S3_Ba_structure():
    print("\n=== Checking S2=(25,45,3,1) and S3=(26,42,6,0) B_a structure ===")
    # For S2: 15 vertices in B_a. Each vertex in B_a has r_1 in {10, 14} -> deg in A_a in {2, 0}!
    # Wait: if r_1 = 10 for some vertices and 14 for others, remember A_a has deg 0 or 2 ONLY -> disjoint union of even cycles + isolated vertices!
    # Wait: what about isolated vertices (deg 0 in A_a)? Let e_v be an isolated vertex in A_a!
    # For an isolated vertex v in B_a: in 20*E_15[B_a], row v has ONLY (4, 0, 0, ...) -> v is in im(2I-A_a) with eigenvalue 2 of (2I-A_a) (4 in 20*E_15)!
    # Wait: check ALL 3 rows of C_2 = {y1, y2, y3} in S2!
    # Remember E_17[y_a] = 4/66, E_11[y_a] = 7/96 = 1/32 + 1/24, E_11[B_a, y_a] = +1/24, E_11[B_a, y_b] = -1/48.
    # Let's check 20*E_15[y_a, y_a] = 5 - 16*(7/96) - 22*(4/66) = 5 - 7/6 - 4/3 = 5 - 5/2 = 5/2!
    # And for u in B_a, 20*E_15[u, y_a] = S[u, y_a] - 16*(1/24) - 22*(2/66) = S[u, y_a] - 2/3 - 2/3 = S[u, y_a] - 4/3!
    # Wait: for ANY vertex v in B_a with r_1(v) = 14 (isolated in A_a), recall we proved r_1(v) = 14 <=> t_1 + t_2 + t_3 = -3 <=> t_1 = t_2 = t_3 = -1!
    # Let's check 20*E_15[B_a U {y_1, y_2, y_3}] when isolated vertices exist or cycles exist!
    # Notice: for an even cycle C_L of A_a (L >= 4), sum of S[u, y_a] over u in C_L MUST BE (4/3)*L?!
    # WAIT A SECOND!! STOP!! CHECK THAT RIGHT NOW!!
    # In 20*E_15[B_a U C_2], 1_{C_L} (the vector = 1 on cycle C_L, 0 elsewhere in B_a) IS IN ker(2I - A_a)!!
    # Because 20*E_15[B_a U C_2] is PSD, ker(20*E_15[B_a]) MUST BE ORTHOGONAL TO ALL COLUMNS OF 20*E_15[B_a, C_2]!!
    # Compute 20*E_15[u, y_a] = S_{u, y_a} - 4/3 (since E_11[B_a, y_a]=1/24 and E_17[B_a, y_a]=2/66, WAIT check sign of E_11[B_a, y_a]!!):
    # Wait: in S2, 16*(+1/24) + 22*(+2/66) = +2/3 + 2/3 = +4/3, OR could (E_11)_{u, y_a} be -1/24?! No, q_{y_a} can be on +u_a or -u_a!
    # Wait: (E_11)_{u, y_a} = +-1/24 (fixed per y_a: if y_a is on u_a -> +1/24; if on -u_a? Wait: Q_1^T Q_1 + Q_2^{(2)T} Q_2^{(2)} = I_2 has 15 vectors on each ray u_a, and 1 vector on each ray -> wait, u_a u_a^T = (-u_a)(-u_a)^T, so y_a could be on +u_a or -u_a!).
    # Wait: whether it's +1/24 or -1/24, 16*(+-1/24) + 22*(+2/66) = +-2/3 + 2/3 in {0, 4/3}!!
    # HOLD EVERYTHING!!
    # Look at BOTH cases:
    # - If 20*E_15[u, y_a] = S_{u, y_a} - 4/3: since S_{u, y_a} in {+-1}, sum_{u in C_L} (S_{u, y_a} - 4/3) = (sum S) - (4/3) L <= L - (4/3) L = -(1/3) L < 0!!
    #   THAT CANNOT BE ZERO FOR ANY CYCLE C_L OF LENGTH L >= 1!!
    # - Wait: what if (E_11)_{u, y_a} = -1/24 (`q_{y_a}` is on `-u_a`, opposite to `B_a`)?!
    #   Then 16*(-1/24) + 22*(2/66) = -2/3 + 2/3 = 0, so 20*E_15[u, y_a] = S_{u, y_a}! Then sum_{u in C_L} S_{u, y_a} = 0 (possible if L even!).
    #   AND CHECK (S Q^{(2)})_{y_a} = 11 (q_{y_a})!! Remember earlier when we set y_a on +u_a! Let's check BOTH signs in Python!
    print("  Checking sign of q_{y_a} in S2 (must satisfy (E_11)_{u, y_a} and S Q^{(2)} = 11 Q^{(2)})!")
    print("  If q_{y_a} = +u_a: 20*E_15[u, y_a] = S[u, y_a] - 4/3 -> sum over ANY cycle C_L <= -L/3 < 0 -> IMPOSSIBLE for ANY cycle in B_a!")
    print("  Wait: what if B_a has NO cycles (15 isolated vertices)? Then r_1(v) = 14 for ALL 15 vertices => t_1=t_2=t_3=-1 (sum_{B_a} S[u, y_a] = -15)!")
    print("  And for y_b (b != a): (E_11)_{u, y_b} = +-1/48 => 16*(+-1/48) + 22*(2/66) = 2/3 +- 1/3 in {1/3, 1}!")
    print("  Look at 20*E_15[u, y_b] = S_{u, y_b} - 1/3 or S_{u, y_b} - 1: sum over C_L CANNOT be 0 if L is not divisible by 3 (for 1/3), or NEVER 0 (for 1, unless S_{u,y_b} = +1 ALL on C_L)!")


if __name__ == "__main__":
    test_S1_t2_signed_and_Z12()
    check_S2_S3_Ba_structure()
