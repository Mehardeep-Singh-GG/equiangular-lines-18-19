"""Exact exhaustive proof/check for S1=(24,48,0,2) t_1=2 partitions [4, 12] and [8, 8]:
Every column of Z_{12} (16 columns) gives a signed node (z, +-w) with w = sqrt(4 - 0.5*z^T P_1 z),
and two nodes (i, j) are compatible iff:
  z_i^T P_1 z_j + 2 w_i w_j == 0   (non-adjacent in A_2, must have >= 13 such neighbors)
  OR == -4                         (adjacent in A_2, must have >= 2 such neighbors)
Also check same-cycle / opposite-cycle constraints and sum(w_i^2) <= 8!
"""
from __future__ import annotations
import numpy as np
from test_idx13_S1_S2_S3_cycles import cycle_union_adj, zero_sum_vecs_on_parts


def exact_check_t2_Z12():
    for parts in ([4, 12], [8, 8]):
        print(f"\n=== Exact Z_12 check for p1={parts} (t1=2) ===")
        A = cycle_union_adj(parts).astype(np.float64)
        ev, evec = np.linalg.eigh(2.0 * np.eye(16) - A)
        nz = np.where(np.abs(ev) > 1e-8)[0]
        P = (evec[:, nz] / ev[nz]) @ evec[:, nz].T
        B_cand = zero_sum_vecs_on_parts(parts)
        qvals = np.sum((B_cand @ P) * B_cand, axis=1)
        idx8 = np.where(qvals <= 8.0 + 1e-7)[0]
        B_ok = B_cand[idx8]
        q_ok = qvals[idx8]
        w_mag = np.sqrt(np.maximum(0.0, 4.0 - 0.5 * q_ok))
        G = B_ok @ P @ B_ok.T

        nodes_w = []
        nodes_b = []
        for i in range(len(idx8)):
            if w_mag[i] < 1e-6:
                nodes_w.append(0.0)
                nodes_b.append(i)
            else:
                nodes_w.append(+w_mag[i])
                nodes_b.append(i)
                nodes_w.append(-w_mag[i])
                nodes_b.append(i)
        nodes_w = np.array(nodes_w)
        nodes_b = np.array(nodes_b)
        M = G[np.ix_(nodes_b, nodes_b)] + 2.0 * np.outer(nodes_w, nodes_w)
        is_0 = np.abs(M - 0.0) < 1e-6
        is_m4 = np.abs(M + 4.0) < 1e-6
        np.fill_diagonal(is_0, False)
        np.fill_diagonal(is_m4, False)

        alive = np.ones(len(nodes_w), dtype=bool)
        while True:
            d0 = is_0[np.ix_(alive, alive)].sum(axis=1)
            dm4 = is_m4[np.ix_(alive, alive)].sum(axis=1)
            bad = (d0 < 13) | (dm4 < 2)
            if not np.any(bad):
                break
            ia = np.where(alive)[0]
            alive[ia[bad]] = False
            if alive.sum() == 0:
                break
        print(f"  Total signed nodes: {len(nodes_w)}, after (13-zero, 2-neg4)-core peeling: {alive.sum()}")
        if alive.sum() > 0:
            ia = np.where(alive)[0]
            print("  Surviving qvals:", np.unique(np.round(q_ok[nodes_b[ia]], 4)))
            # Check if a 16-clique of 2-regular graph of -4 edges exists among surviving nodes using CP-SAT!
            from ortools.sat.python import cp_model
            sub_0 = is_0[np.ix_(ia, ia)]
            sub_m4 = is_m4[np.ix_(ia, ia)]
            m = len(ia)
            model = cp_model.CpModel()
            x_var = [model.NewBoolVar(f"x_{k}") for k in range(m)]
            model.Add(sum(x_var) == 16)
            # sum w^2 <= 8 => sum (8 - q_k) x_k <= 16
            # Multiply by 12 to make integer
            w2_12 = [int(round(12 * (nodes_w[ia[k]] ** 2))) for k in range(m)]
            model.Add(sum(w2_12[k] * x_var[k] for k in range(m)) <= 8 * 12)
            for i in range(m):
                for j in range(i + 1, m):
                    if not (sub_0[i, j] or sub_m4[i, j]):
                        model.Add(x_var[i] + x_var[j] <= 1)
                # If x_i == 1, exactly 2 neighbors in sub_m4!
                m4_nbrs = [x_var[j] for j in range(m) if sub_m4[i, j]]
                model.Add(sum(m4_nbrs) >= 2 - 16 * (1 - x_var[i]))
                model.Add(sum(m4_nbrs) <= 2 + 16 * (1 - x_var[i]))
            sv = cp_model.CpSolver()
            sv.parameters.max_time_in_seconds = 10.0
            status = sv.Solve(model)
            print(f"  CP-SAT 16-vertex 2-reg check status: {sv.StatusName(status)}")
            if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
                chosen = [ia[k] for k in range(m) if sv.Value(x_var[k])]
                print("  FOUND Z_12! qvals=", q_ok[nodes_b[chosen]])
                # Check if A_2 is a valid even-cycle partition!
                adj_A2 = is_m4[np.ix_(chosen, chosen)].astype(int)
                # Find cycle lengths
                vis = [False] * 16
                cyc = []
                for s in range(16):
                    if not vis[s]:
                        L = 0
                        cur = s
                        prev = -1
                        while not vis[cur]:
                            vis[cur] = True
                            L += 1
                            nbrs = [j for j in range(16) if adj_A2[cur, j] and j != prev]
                            if not nbrs: break
                            prev = cur
                            cur = nbrs[0]
                        cyc.append(L)
                print("  Cycle lengths of induced A_2:", sorted(cyc))


if __name__ == "__main__":
    exact_check_t2_Z12()
