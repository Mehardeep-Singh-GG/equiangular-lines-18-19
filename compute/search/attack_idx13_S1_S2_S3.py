"""Exact check on S2=(25,45,3,1) and S3=(26,42,6,0) via 20*E_15 + E_11 + E_17,
and exact check on S1=(24,48,0,2) via M_{123} = 20*E_15[C_1] (rank <= 15, 0 <= M <= 20I)
and S_C = (5I + W00 - 1/2 J) - 1/2 B^T P B (rank <= t-1)!
"""
from __future__ import annotations
import itertools
import numpy as np


def check_S2():
    print("=== EXACT CHECK ON S2 = (25, 45, 3, 1) ===")
    # E_17: v_17 = (0 on C_0, 1 on C_1, 2 on C_2, 3 on C_5) / sqrt(66)
    # E_11 = Q Q^T:
    #   e1 = (+1 on C_0, 0 on C_1, sigma_y in {+-1} on C_2, +2*eps on w) / sqrt(32)
    #   S[C_1, w] = +1, S[C_2, w] = +1.
    #   (S e1)_w = 22*eps = 25*eps_0 + sum_{y in C_2} sigma_y => eps_0 = eps, sigma_y = -eps for ALL y in C_2!
    #   (S e1)_{y_a} = 11*(-eps) => check!
    #   e2, e3: Q_1 has 15 on u_1, 15 on u_2, 15 on u_3 (norm 1/sqrt(24));
    #           Q_2^{(2)} has q_{y_a} = s_a * u_a (s_a in {+-1}, norm 1/sqrt(24)).
    #           Note: since E_11^2 = E_11, e1 must be orthogonal to e2, e3:
    #           sum_{y in C_2} (-eps) * s_a * u_a = 0 => s_1 u_1 + s_2 u_2 + s_3 u_3 = 0 => s_1 = s_2 = s_3 =: s in {+1, -1}!!
    #   HOLD EVERYTHING! s_1 = s_2 = s_3 = s is FORCED by E_11^2 = E_11 (e1 perp e2, e3)!!
    print("  Orthogonality e1 perp (e2, e3) forces s_1 = s_2 = s_3 = s in {+1, -1}!")
    for s in (+1, -1):
        # For v in B_1: let r_1, r_2, r_3 be row sums to B_1, B_2, B_3; t_a = S[v, y_a] in {+-1}; S[v, w] = +1.
        # (S v_17)_v = 17 => r_1 + r_2 + r_3 + 2*(t_1 + t_2 + t_3) + 3 = 17 => r_1 + r_2 + r_3 + 2*(t_1 + t_2 + t_3) = 14
        # (S Q^{(2)})_v = 11 u_1 => (r_1 + s*t_1) u_1 + (r_2 + s*t_2) u_2 + (r_3 + s*t_3) u_3 = 11 u_1
        #   => r_2 + s*t_2 = r_3 + s*t_3, and r_1 + s*t_1 - (r_2 + s*t_2) = 11.
        # Notice r_1 is EVEN (14 neighbors in B_1), r_2, r_3 are ODD (15 neighbors).
        # Let x_a = r_a + s*t_a. Then x_2 = x_3 (EVEN), x_1 = x_2 + 11 (ODD).
        # Sum: x_1 + x_2 + x_3 = 3*x_2 + 11 = (r_1 + r_2 + r_3) + s*(t_1 + t_2 + t_3) = 14 + (s - 2)*(t_1 + t_2 + t_3).
        # Thus 3*x_2 = 3 + (s - 2)*(t_1 + t_2 + t_3), with x_2 EVEN!
        # Also deg in A_1 is (14 - r_1)/2 in {0, 1, 2}?! Wait: A_1 has lambda_max <= 2! Can deg in A_1 be 1 (path/matching)??
        # WAIT A SECOND! We haven't restricted deg in A_1 to {0, 2}! ANY deg in 0..14 gives r_1 = 14 - 2*deg <= 14!
        # Wait: what is E_15[v, v]?! E_15[v, v] = 1/5 => 20*E_15[v, v] = 4, and 20*E_15[B_1] = 2(2I - A_1) >= 0!
        # Look at sum_{y in C_2} 20*E_15[v, y_a]:
        # Remember for u in B_1, y_a in C_2:
        #   20*E_15[u, y_a] = S[u, y_a] - 16*(E_11)_{u, y_a} - 22*(E_17)_{u, y_a}.
        #   (E_11)_{u, y_1} = s/24, (E_11)_{u, y_2} = -s/48, (E_11)_{u, y_3} = -s/48!
        #   (E_17)_{u, y_a} = 2/66 = 1/33.
        #   So 20*E_15[u, y_1] = t_1 - 2s/3 - 2/3; 20*E_15[u, y_2] = t_2 + s/3 - 2/3; 20*E_15[u, y_3] = t_3 + s/3 - 2/3!
        # Now check (S Q^{(2)})_{y_1} = 11 * s * u_1 and (S v_17)_{y_1} = 34!
        valid_t = []
        for t1, t2, t3 in itertools.product([-1, 1], repeat=3):
            tsum = t1 + t2 + t3
            rhs3 = 3 + (s - 2) * tsum
            if rhs3 % 3 != 0:
                continue
            x2 = rhs3 // 3
            if x2 % 2 != 0:
                continue
            x1 = x2 + 11
            r1 = x1 - s * t1
            r2 = x2 - s * t2
            r3 = x2 - s * t3
            deg_A1 = (14 - r1) // 2
            # Since 2I - A_1 >= 0, max degree in A_1 is <= 4 (only 4 for K_{1,4}, or <=2 for cycles/paths/D_n!)
            # Actually in 2I - A_1 >= 0, (2I - A_1)[N[v], N[v]] >= 0 requires deg <= 4!
            if 0 <= deg_A1 <= 4 and abs(r2) <= 15 and abs(r3) <= 15:
                valid_t.append(((t1, t2, t3), r1, deg_A1, r2, r3))
        print(f"  s={s:+d}: valid (t1,t2,t3, r1, deg_A1, r2, r3):")
        for item in valid_t:
            print("   ", item)


def check_S3():
    print("\n=== EXACT CHECK ON S3 = (26, 42, 6, 0) ===")
    # C_0 (26), C_1 (42 = 14+14+14), C_2 (6).
    # E_11 = Q Q^T:
    #   e1 = (+1 on C_0, 0 on C_1, alpha_y in {+-1} on C_2) / sqrt(32)
    #   e2, e3: Q_1 has 14 on u_1, 14 on u_2, 14 on u_3 (norm 1/sqrt(24));
    #           Q_2^{(2)} has 6 vectors of norm 1/sqrt(24) summing to 0 and giving (2/24)*... -> (2+2+2) on rays u_1, u_2, u_3!
    # Wait: E_11[C_2, C_2] has rank 3, with e1 perp (e2, e3) => on EACH ray u_a (2 vertices y_{a,1}, y_{a,2}),
    # can q_{y_{a,1}} and q_{y_{a,2}} be (+u_a, +u_a) or (+u_a, -u_a) or (-u_a, -u_a)?
    # Since sum_{C_2} alpha_y * q_y = 0 (e1 perp e2, e3) and sum_{C_2} q_y = ?
    # Wait: Q^T Q = I_3, Q has 3 cols. Does Q_2^{(2)} have sum 0? YES, because Q_1^T 1 = 0 and Q^T 1? Wait: 1 is NOT necessarily orthogonal to Q!
    # Wait: in S3, v_17 = (0 on C_0, 1 on C_1, 2 on C_2) / sqrt(66) MUST be orthogonal to e2, e3!
    # Since Q_1^T 1_{42} = 0, (v_17)^T Q^{(2)} = 0 => 2 * sum_{y in C_2} q_y = 0 => sum_{y in C_2} q_y = 0!
    # So C_2 = {y_1a, y_1b, y_2a, y_2b, y_3a, y_3b} with s_{1a} + s_{1b} = s_{2a} + s_{2b} = s_{3a} + s_{3b} (same sum c in {-2, 0, +2})!
    # AND e1 perp (e2, e3) => alpha_{a1} s_{a1} + alpha_{a2} s_{a2} is equal for a=1,2,3!
    # Check all valid (alpha, s) patterns on C_2 and check (S v_17)_v = 17, (S Q^{(2)})_v = 11 u_1 on v in B_1 (size 14)!
    for c_sum in (-2, 0, 2):
        if c_sum == 2: s_pairs = [(1, 1)] * 3
        elif c_sum == -2: s_pairs = [(-1, -1)] * 3
        else: s_pairs = [(1, -1)] * 3
        # Actually if s_pairs = [(1,-1)]*3, wait: (S v_17)_v = 17 on v in B_1:
        # r_1 + r_2 + r_3 + 2 * sum_{C_2} S[v, y] = 17. Notice r_1 is ODD (13 neighbors in B_1), r_2, r_3 are EVEN (14 neighbors)!
        # So r_1 + r_2 + r_3 is ODD -> ODD + EVEN = ODD = 17! Parity checks!
        # Let's check r_1 = 13 - 2*deg_A1 for possible t values!
        print(f"  c_sum={c_sum}: s_pairs={s_pairs}")
        # For each pair (s_{a1}, s_{a2}), let T_a = t_{a1} + t_{a2}, W_a = s_{a1} t_{a1} + s_{a2} t_{a2}.
        # r_1 + r_2 + r_3 + 2*(T_1+T_2+T_3) = 17
        # r_1 + W_1 - (r_2 + W_2) = 11, r_2 + W_2 = r_3 + W_3.
        # => 3*(r_2 + W_2) + 11 = 17 + (W_1+W_2+W_3) - 2*(T_1+T_2+T_3)
        # => 3*(r_2 + W_2) = 6 + sum W_a - 2 sum T_a!
        valid_degs = set()
        for ts in itertools.product([-1, 1], repeat=6):
            T = [ts[0]+ts[1], ts[2]+ts[3], ts[4]+ts[5]]
            W = [s_pairs[a][0]*ts[2*a] + s_pairs[a][1]*ts[2*a+1] for a in range(3)]
            rhs = 6 + sum(W) - 2 * sum(T)
            if rhs % 3 != 0: continue
            x2 = rhs // 3
            if x2 % 2 != 0: continue  # r_2, W_2 both even => x2 even
            x1 = x2 + 11
            r1 = x1 - W[0]
            deg = (13 - r1) // 2
            if 0 <= deg <= 4:
                valid_degs.add(deg)
        print(f"    -> valid deg_A1 in [0..4]: {sorted(valid_degs)}")


def check_S1_M123_rank15():
    print("\n=== S1=(24,48,0,2): Testing C_4+C_4+C_4+C_4 on B_1, B_2, B_3 for M_{123} rank<=15 ===")
    # Check if 20*E_15[B_1 U B_2] can even have rank <= 15 for [4,4,4,4] + [4,4,4,4] or mixed partitions!
    # Wait: for ANY partition parts1 of 16 (t1 cycles) and parts2 of 16 (t2 cycles):
    # M_{12} = [[2(2I-A_1), Z_12], [Z_12^T, 2(2I-A_2)]] >= 0 has rank <= 15.
    # Let's test via alternating projections whether ANY Z_12 (16x16 +-1 with zero cycle sums)
    # makes 2(2I-A_2) - Z_12^T R_1^+ Z_12 >= 0 of rank <= t_1 - 1!
    parts_list = [[4, 12], [8, 8], [4, 4, 8], [4, 6, 6], [4, 4, 4, 4]]
    from test_idx13_S1_S2_S3_cycles import cycle_union_adj
    rng = np.random.default_rng(123)
    for p1 in parts_list:
        A1 = cycle_union_adj(p1).astype(float)
        R1 = 2.0 * (2.0 * np.eye(16) - A1)
        ev1, V1 = np.linalg.eigh(R1)
        nz1 = np.where(ev1 > 1e-8)[0]
        R1p = (V1[:, nz1] / ev1[nz1]) @ V1[:, nz1].T
        t1 = len(p1)
        # Basis for cycles of A1 (kernel of R1)
        z1 = np.where(ev1 <= 1e-8)[0]
        K1 = V1[:, z1]  # 16 x t1
        for p2 in parts_list:
            if p2 < p1: continue
            A2 = cycle_union_adj(p2).astype(float)
            R2 = 2.0 * (2.0 * np.eye(16) - A2)
            ev2, V2 = np.linalg.eigh(R2)
            z2 = np.where(ev2 <= 1e-8)[0]
            K2 = V2[:, z2]  # 16 x t2
            t2 = len(p2)
            # Check max rank of R1 + R2 - ... wait: M_12 (32x32) has target rank <= 15, >= 0, <= 20 I!
            # Wait: 0 <= M_12 <= 20 I is necessary for M_12 to be 20*E_15[B_1 U B_2]!
            # Let's run quick alternating projections on 32x32 M_12:
            best_neg = 1e9
            best_disc = 1e9
            for trial in range(5):
                Z = rng.choice([-1.0, 1.0], size=(16, 16))
                for it in range(500):
                    M = np.block([[R1, Z], [Z.T, R2]])
                    ev, U = np.linalg.eigh(M)
                    # Keep top 15 eigenvalues clipped to [0, 20], zero bottom 17!
                    ev_proj = ev.copy()
                    ev_proj[:17] = 0.0
                    ev_proj[17:] = np.clip(ev_proj[17:], 0.0, 20.0)
                    M_proj = (U * ev_proj) @ U.T
                    Z = np.clip(M_proj[:16, 16:], -1.0, 1.0)
                    # Project Z onto K1^T Z = 0 and Z K2 = 0
                    Z = Z - K1 @ (K1.T @ Z)
                    Z = Z - (Z @ K2) @ K2.T
                M = np.block([[R1, Z], [Z.T, R2]])
                ev = np.linalg.eigvalsh(M)
                rank_err = np.sum(ev[:17]**2)
                disc_err = np.mean(np.abs(np.abs(Z) - 1.0))
                if rank_err + disc_err < best_neg:
                    best_neg = rank_err + disc_err
                    best_r = rank_err; best_d = disc_err
            print(f"  p1={str(p1):12s} p2={str(p2):12s} (t1+t2={t1+t2}): rank_err={best_r:.4e}, disc_err={best_d:.4f}")


if __name__ == "__main__":
    check_S2()
    check_S3()
    check_S1_M123_rank15()
