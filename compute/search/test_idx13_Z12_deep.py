"""Inspect exact Z_{12} from p1=[4, 12] and p1=[8, 8] (with S_{22}=0, A_2=[4,4,4,4]),
check 0 <= M_{12} <= 20 I, and search for Z_{13} (M_{123} rank <= 15, <= 20 I) and C_0 (24 vertices)!
"""
from __future__ import annotations
import numpy as np
from ortools.sat.python import cp_model
from test_idx13_S1_S2_S3_cycles import cycle_union_adj, zero_sum_vecs_on_parts


def find_and_check_Z12(parts):
    print(f"\n=== Inspecting Z_12 for p1={parts} ===")
    A1 = cycle_union_adj(parts).astype(np.float64)
    R1 = 2.0 * (2.0 * np.eye(16) - A1)
    ev1, evec1 = np.linalg.eigh(R1)
    nz1 = np.where(ev1 > 1e-8)[0]
    P1 = (evec1[:, nz1] / (ev1[nz1] / 2.0)) @ evec1[:, nz1].T  # (2I - A1)^+
    R1p = 0.5 * P1

    B_cand = zero_sum_vecs_on_parts(parts)
    qvals = np.sum((B_cand @ P1) * B_cand, axis=1)
    idx8 = np.where(np.abs(qvals - 8.0) < 1e-6)[0]
    print(f"  Number of zero-sum vectors with q == 8: {len(idx8)}")
    if len(idx8) == 0:
        return
    B8 = B_cand[idx8]
    G = B8 @ P1 @ B8.T
    is_0 = np.abs(G) < 1e-6
    is_m4 = np.abs(G + 4.0) < 1e-6
    np.fill_diagonal(is_0, False)
    np.fill_diagonal(is_m4, False)

    m = len(idx8)
    model = cp_model.CpModel()
    x_var = [model.NewBoolVar(f"x_{k}") for k in range(m)]
    model.Add(sum(x_var) == 16)
    for i in range(m):
        for j in range(i + 1, m):
            if not (is_0[i, j] or is_m4[i, j]):
                model.Add(x_var[i] + x_var[j] <= 1)
        m4_nbrs = [x_var[j] for j in range(m) if is_m4[i, j]]
        model.Add(sum(m4_nbrs) >= 2 - 16 * (1 - x_var[i]))
        model.Add(sum(m4_nbrs) <= 2 + 16 * (1 - x_var[i]))
    sv = cp_model.CpSolver()
    status = sv.Solve(model)
    if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        print("  No Z_12 with S_22=0!")
        return
    chosen = [k for k in range(m) if sv.Value(x_var[k])]
    Z12 = B8[chosen].T  # 16 x 16
    adj_A2 = is_m4[np.ix_(chosen, chosen)].astype(float)
    R2 = 2.0 * (2.0 * np.eye(16) - adj_A2)
    M12 = np.block([[R1, Z12], [Z12.T, R2]])
    ev12 = np.linalg.eigvalsh(M12)
    print(f"  M12 rank={np.sum(np.abs(ev12) > 1e-6)}, eigs={np.round(ev12[ev12 > 1e-6], 4)}")
    print(f"  max_eig(M12) = {ev12.max():.4f} (need <= 20.0!)")

    # Wait: if S_22 == 0, then in M_{123} = [[R1, Z12, Z13], [Z12^T, R2, Z23], [Z13^T, Z23^T, R3]]:
    # Since S_22 = R2 - Z12^T R1^+ Z12 == 0, ANY Z13 must make:
    #   Z23 == Z12^T R1^+ Z13  (MUST BE IN {+-1}^{16 x 16}!!)
    # Let's check which columns z in B_cand (zero-sum on p1!) make Z12^T R1^+ z in {+-1}^16!!
    C_mat = Z12.T @ R1p @ B_cand.T  # 16 x |B_cand|
    # Check entries close to +-1!
    is_pm1_col = np.all(np.abs(np.abs(C_mat) - 1.0) < 1e-6, axis=0)
    n_pm1 = np.sum(is_pm1_col)
    print(f"  Columns z in B_cand with Z12^T R1^+ z in {{+-1}}^16: {n_pm1} / {len(B_cand)}")
    if n_pm1 > 0:
        Z13_cands = B_cand[is_pm1_col]
        Z23_cands = C_mat[:, is_pm1_col].T
        q3 = qvals[is_pm1_col]
        print(f"    Their qvals = {np.unique(np.round(q3, 4))}")

    # Also check how many columns b in B_cand (zero-sum on p1) have Z12^T R1^+ b in {+-1}^16?
    # Wait: for C_0 (b_u), M_{1, C0} has S_{C0, B_2} = B^{(2)} = Z12^T R1^+ B^{(1)} - ... (wait for C_0, E_11=0, E_17=0 so 20*E_15[u, B_2] = b^{(2)}_u,
    # Wait: M_{1, 2, C0} has S_{22} == 0 => 20*E_15[B_2, C_0] = Z12^T R1^+ B^{(1)}!! Since 20*E_15[B_2, C_0] = B^{(2)} is +-1,
    # EVERY column b_u of B^{(1)} MUST ALSO satisfy Z12^T R1^+ b_u in {+-1}^16!!
    # Wait: what if S_{22} != 0 (i.e. rank(S_{22}) = 1)? Let's check THAT too!


if __name__ == "__main__":
    find_and_check_Z12([4, 12])
    find_and_check_Z12([8, 8])
