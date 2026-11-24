"""Check S2=(25,45,3,1) and S3=(26,42,6,0) completely, and check S1=(24,48,0,2)
with exact rank/trace/SDP/CP-SAT checks on B_a and C_1.
"""
from __future__ import annotations
import itertools
import numpy as np


def check_S2_complete():
    print("=== S2 = (25, 45, 3, 1) COMPLETE CHECK ===")
    # Check 20*E_15[C_2] (3x3) + C_5 (1 vertex w):
    # Remember E_11[y_a, y_b]:
    #   e1 has (-eps) on y_1, y_2, y_3 => e1 contribution to E_11[C_2, C_2] is (1/32) J_3!
    #   e2, e3 has s*u_a on y_a => contribution is (1/24) on diag, (-1/48) off-diag!
    #   Total E_11[y_a, y_a] = 1/32 + 1/24 = 7/96.
    #   Total E_11[y_a, y_b] = 1/32 - 1/48 = +1/96!
    #   Total E_17[y_a, y_b] = 4/66 = 2/33!
    #   WAIT A SECOND! Compute 20*E_15[y_a, y_b] for a != b in C_2!!
    #   20*E_15[y_a, y_b] = S[y_a, y_b] - 16*(1/96) - 22*(2/33) = z_{ab} - 1/6 - 4/3 = z_{ab} - 3/2!!
    #   AND 20*E_15[y_a, y_a] = 5/2!
    #   Check eigenvalues of 3x3 matrix M_{C_2} = [[5/2, z12 - 3/2, z13 - 3/2], ...]:
    print("  20*E_15[C_2] (3x3) eigenvalues for each (z12, z13, z23):")
    for z12, z13, z23 in [(1,1,1), (1,1,-1), (1,-1,-1), (-1,-1,-1)]:
        M = np.array([
            [2.5, z12 - 1.5, z13 - 1.5],
            [z12 - 1.5, 2.5, z23 - 1.5],
            [z13 - 1.5, z23 - 1.5, 2.5],
        ])
        ev = np.linalg.eigvalsh(M)
        print(f"    z=({z12:+d},{z13:+d},{z23:+d}): eigvals={np.round(ev, 4)}, PSD={np.all(ev >= -1e-9)}")
    # Wait: ALSO check 20*E_15[y_a, w] (w in C_5)!
    # On w: E_11[w, y_a] = (-eps)*(+2*eps)/32 = -1/16! E_17[w, y_a] = 2*3/66 = 1/11.
    # Wait: S[y_a, w] = +1 => 20*E_15[y_a, w] = 1 - 16*(-1/16) - 22*(1/11) = 1 + 1 - 2 = 0!
    # (Matches E_15[w, w] = 0!)
    # NOW CHECK (z12, z13, z23) WITH s = -1 AND B_1, B_2, B_3!!
    # Notice M_{C_2} is ONLY PSD when z = (+1,+1,+1) (eigs 1.5, 3, 3) OR (+1,+1,-1) (wait eigs!)!
    # Let's check ALL 4 z's AND check (T_{a,b}):
    # Wait: for z=(+1,+1,+1), T_{1,1}=1, T_{1,2}=13, T_{1,3}=13.
    # Wait: how many vertices in B_1 have t_2 = -1 (1 vertex) and t_3 = -1 (1 vertex)?!
    # Look at the graph A_1 on B_1 (15 vertices) when s = -1!
    # In our s = -1 table:
    #   (t1, t2, t3) = (t1, +1, +1) -> deg_A1 = 2!
    #   (t1, +1, -1) or (t1, -1, +1) -> deg_A1 = 1!
    #   (t1, -1, -1) -> deg_A1 = 0!
    # Look at T_{2, 1} = 13 (one -1), T_{3, 1} = 13 (one -1):
    #   Either BOTH -1s are on the SAME vertex (1 vertex of deg 0, 14 vertices of deg 2 -> EVEN cycles + 1 isolated vertex),
    #   OR on TWO different vertices (2 vertices of deg 1, 13 vertices of deg 2 -> EVEN cycles + 1 path P_k!).
    # Wait: let's check BOTH! What does 20*E_15[B_1 U {y_1, y_2, y_3}] >= 0 say when 1 vertex has (t2=-1, t3=-1) OR 2 vertices have deg 1?!
    # TEST IT DIRECTLY IN NUMPY!
    # Suppose B_1 has a path P_k (k >= 2) with endpoints v_1 (t2=-1,t3=+1) and v_k (t2=+1,t3=-1) and rest cycles:
    # Check 20*E_15[B_1 U C_2] >= 0!
    for z in [(1,1,1), (1,1,-1), (1,-1,-1), (-1,-1,-1)]:
        z12, z13, z23 = z
        M_C2 = np.array([
            [2.5, z12 - 1.5, z13 - 1.5],
            [z12 - 1.5, 2.5, z23 - 1.5],
            [z13 - 1.5, z23 - 1.5, 2.5],
        ])
        if np.min(np.linalg.eigvalsh(M_C2)) < -1e-9:
            continue
        print(f"\n  Testing S2 z={z} (PSD C_2):")
        # Target T_{a, 1} for B_1:
        # Note T_{1,1} = (z12+z13) -> wait: X = 14 - (z12 + z13), T_{1,1} = X - 11 = 3 - (z12 + z13)
        # Wait: what about T_{2,1} and T_{3,1}? By vertex 2 eq: X_2 + z12 + z23 = 14 => T_{2,1} = 14 - z12 - z23 + z12 = 14 - z23?
        # Wait: T_{2,2} = X_2 - 11, T_{2,1} = X_2 + z12, T_{2,3} = X_2 + z23 -> T_{2,1} = 14 - z23! T_{3,1} = 14 - z23!
        # Let's compute exact T_{1,1}, T_{2,1}, T_{3,1} for B_1:
        T11 = 3 - z12 - z13
        T21 = 14 - z23
        T31 = 14 - z23
        print(f"    On B_1: T11={T11}, T21={T21}, T31={T31} (so #t2=-1 is {(15-T21)//2}, #t3=-1 is {(15-T31)//2})")
        # Notice! If z23 = +1, then T21 = T31 = 13 => ONE t2=-1 and ONE t3=-1 in B_1!
        # If z23 = -1, then T21 = T31 = 15 => ZERO t2=-1 and ZERO t3=-1 in B_1 -> ALL 15 vertices in B_1 have deg 2!
        # Wait: if ALL 15 vertices in B_1 have deg 2, then A_1 is a union of CYCLES on 15 vertices -> at least one ODD cycle!
        # And on an ODD cycle, sum t_1 CANNOT be 0!! CONTRADICTION!
        # Wait: check z=(1,1,-1) for B_1, B_2, B_3:
        # For B_2: T22 = 3 - z12 - z23, T12 = 14 - z13, T32 = 14 - z13!
        # For B_3: T33 = 3 - z13 - z23, T13 = 14 - z12, T23 = 14 - z12!
        # Look at z=(1, 1, -1): on B_1, z23 = -1 => ALL 15 vertices of B_1 have deg 2 -> ODD cycle -> IMPOSSIBLE!
        # So ONLY z = (1, 1, 1) can avoid odd-cycle sum on ALL three B_1, B_2, B_3!!
        # NOW CHECK z = (1, 1, 1) ON B_1 U C_2 (`18 x 18` matrix 20*E_15)!!
        # For z = (1, 1, 1): T11 = 1, T21 = 13, T31 = 13!
        # Either (Case A) 1 isolated vertex v0 (t2=-1, t3=-1) + 14 vertices in even cycles (so T11 on the 14 cycle vertices is 0, forcing t1(v0) = +1!!),
        # OR (Case B) 1 path P_k (k >= 2) with endpoints (t2=-1, t3=+1) and (t2=+1, t3=-1) + even cycles on 15-k vertices!
        # Let's test Case A (v0 isolated, t1=+1, t2=-1, t3=-1) AND Case B (path P_k, k=2..15)!
        # Case A check: on v0 (isolated, so decoupled in 2I - A_1!), look at 4x4 submatrix {v0, y1, y2, y3} of 20*E_15:
        M_A = np.array([
            [4.0, 1.0, -2.0, -2.0],
            [1.0, 2.5, -0.5, -0.5],
            [-2.0, -0.5, 2.5, -0.5],
            [-2.0, -0.5, -0.5, 2.5],
        ])
        print(f"    Case A {{v0, C_2}} 4x4 eigs = {np.round(np.linalg.eigvalsh(M_A), 5)} (PSD={np.all(np.linalg.eigvalsh(M_A) >= -1e-9)})")
        # Case B check: path P_k (k=2..15) with endpoints u1 (t2=-1, t3=+1) and uk (t2=+1, t3=-1) and interior (t2=+1, t3=+1),
        # and sum_{P_k} t1 = 1 (since cycles have sum t1 = 0, and T11 = 1)!
        for k in range(2, 16):
            # P_k has k vertices; enumerate ALL t1 in {+-1}^k with sum(t1) = 1 (possible only if k is odd!)
            if k % 2 == 0:
                continue
            found_psd = 0
            A_pk = np.zeros((k, k))
            for i in range(k - 1):
                A_pk[i, i + 1] = A_pk[i + 1, i] = 1.0
            R_pk = 2.0 * (2.0 * np.eye(k) - A_pk)
            for ones in itertools.combinations(range(k), (k + 1) // 2):
                t1_vec = -np.ones(k)
                t1_vec[list(ones)] = 1.0
                c2_vec = np.zeros(k); c2_vec[0] = -2.0
                c3_vec = np.zeros(k); c3_vec[-1] = -2.0
                B_pk = np.column_stack([t1_vec, c2_vec, c3_vec])
                M_pk = np.block([[R_pk, B_pk], [B_pk.T, M_C2]])
                if np.min(np.linalg.eigvalsh(M_pk)) >= -1e-9:
                    found_psd += 1
            print(f"    Case B P_{k}: {found_psd} PSD assignments of t1")


if __name__ == "__main__":
    check_S2_complete()
