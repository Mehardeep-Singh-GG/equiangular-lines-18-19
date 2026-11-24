"""Probe realizability vs impossibility of the 3 last (19, 74) idx=13 solutions:
  S1: (24, 48, 0, 2)
  S2: (25, 45, 3, 1)
  S3: (26, 42, 6, 0)

First check:
1. Does ANY 8-regular graph A on 24 vertices exist with lambda_2(A) <= 2 and mult_A(2) >= 8
   (equivalently W = J - I - 2A has W*1=7*1, Spec(W|1^perp) subset [-5, 15], mult_W(-5) >= 8)?
   Wait: also check rank(B_1, B_2, B_3) and exact trace/4th-moment bounds on W_{00} and X_{11}!
2. Test direct Gram / Seidel optimization & exact CP-SAT on S1, S2, S3 with all proved block locks!
"""
from __future__ import annotations
import numpy as np
from ortools.sat.python import cp_model


def check_24_8reg_graphs():
    print("=== Checking 8-regular 24-vertex graphs with lambda_2 <= 2, mult(2) >= 8 ===")
    # Try simple symmetric/circulant/Cayley/product candidates and SA/tabu search
    rng = np.random.default_rng(42)

    # First check circulants on Z_24 and Cayley graphs on small groups of order 24,
    # AND run fast 2-switch (edge-swap preserving 8-regularity) simulated annealing minimizing:
    # loss = sum_{lam > 2} (lam - 2)^2 + penalty if mult(2) < 8 (actually maximize sum of 8 largest eigs -> 16, i.e., minimize sum_{i=1}^8 (lam_i - 2)^2 + sum_{lam_i > 2} ...)
    # Wait: if all 23 nontrivial eigs <= 2 AND top 8 of them = 2, then sum of top 9 eigs (incl lam_0=8) = 8 + 8*2 = 24!
    def sa_search(seed: int, steps: int = 15000):
        r = np.random.default_rng(seed)
        # Start from random 8-regular graph via configuration model / greedy
        while True:
            stubs = np.repeat(np.arange(24), 8)
            r.shuffle(stubs)
            A = np.zeros((24, 24), dtype=int)
            ok = True
            for k in range(0, len(stubs), 2):
                u, v = stubs[k], stubs[k + 1]
                if u == v or A[u, v] == 1:
                    ok = False
                    break
                A[u, v] = A[v, u] = 1
            if ok:
                break

        def eval_A(mat):
            evals = np.linalg.eigvalsh(mat.astype(float))
            # evals sorted ascending; evals[-1] = 8.0
            nt = evals[:-1]
            above2 = np.sum(np.maximum(0.0, nt - 2.0) ** 2)
            top8 = nt[-8:]
            gap8 = np.sum((top8 - 2.0) ** 2)
            # Also check H = 16I - 6A - A^2 + 4J: entries off-diag must satisfy |H_ij| <= 12
            A2 = mat @ mat
            H = 16 * np.eye(24) - 6 * mat - A2 + 4 * np.ones((24, 24))
            np.fill_diagonal(H, 0.0)
            h_viol = np.sum(np.maximum(0.0, np.abs(H) - 12.0) ** 2)
            return above2 * 10.0 + gap8 + h_viol * 10.0, evals

        cur_loss, cur_ev = eval_A(A)
        best_loss, best_A, best_ev = cur_loss, A.copy(), cur_ev
        edges = np.argwhere(np.triu(A) == 1)
        for step in range(steps):
            # Pick 2 edges (u1, v1), (u2, v2) and swap to (u1, u2), (v1, v2) or (u1, v2), (v1, u2)
            i1, i2 = r.integers(0, len(edges), size=2)
            if i1 == i2:
                continue
            u1, v1 = edges[i1]
            u2, v2 = edges[i2]
            if len({u1, v1, u2, v2}) < 4:
                continue
            if r.random() < 0.5:
                a1, b1, a2, b2 = u1, u2, v1, v2
            else:
                a1, b1, a2, b2 = u1, v2, v1, u2
            if A[a1, b1] or A[a2, b2]:
                continue
            A[u1, v1] = A[v1, u1] = 0
            A[u2, v2] = A[v2, u2] = 0
            A[a1, b1] = A[b1, a1] = 1
            A[a2, b2] = A[b2, a2] = 1
            new_loss, new_ev = eval_A(A)
            T = max(0.005, 0.5 * (1.0 - step / steps))
            if new_loss <= cur_loss or r.random() < np.exp(-(new_loss - cur_loss) / T):
                cur_loss, cur_ev = new_loss, new_ev
                edges[i1] = [min(a1, b1), max(a1, b1)]
                edges[i2] = [min(a2, b2), max(a2, b2)]
                if new_loss < best_loss:
                    best_loss, best_A, best_ev = new_loss, A.copy(), new_ev
                    if best_loss < 1e-8:
                        return best_loss, best_A, best_ev
            else:
                A[a1, b1] = A[b1, a1] = 0
                A[a2, b2] = A[b2, a2] = 0
                A[u1, v1] = A[v1, u1] = 1
                A[u2, v2] = A[v2, u2] = 1
        return best_loss, best_A, best_ev

    for s in range(10):
        loss, A, ev = sa_search(s, 8000)
        print(f"  seed {s}: best_loss={loss:.6f}, top10_eigs={np.round(ev[-10:], 4)}")
        if loss < 1e-6:
            print("  FOUND exact 24-vertex 8-reg graph A! Spec(A)=", np.round(ev, 4))
            # Check H = 16I - 6A - A^2 + 4J
            A2 = A @ A
            H = 16 * np.eye(24, dtype=int) - 6 * A - A2 + 4 * np.ones((24, 24), dtype=int)
            print("  H min/max offdiag:", H[np.eye(24)==0].min(), H[np.eye(24)==0].max(), "rank(H)=", np.linalg.matrix_rank(H))
            # Check if 4*H = B*B^T has 48 cols in {+-1}^24? Wait: B = [B1, B2, B3] (each 24x16)!
            break


def check_full_74_rank_search():
    """Quick spectral Gram / tabu check on S1 (24, 48, 0, 2) with exact fixed blocks!"""
    print("\n=== Checking full S1=(24,48,0,2) via constrained Seidel tabu ===")
    # Wait: on S1, W_{00} is 24x24 (row sum 7), B=[B1,B2,B3] (each 24x16 row/col sum 0),
    # C_1 = B1+B2+B3 (each Ba 2-reg on 16, Ba-Bb row/col sum 0), C_5={w1,w2} fixed!
    # Let's see what min lambda_55(S) or trace((S+5I)_negative^2) can reach!
    # Wait: better yet, check if S + 5I >= 0 with rank <= 19 is approached!
    # Even faster: test L-BFGS / alternating projection of 74x74 PSD rank-19 matrix G = 5I + S!
    rng = np.random.default_rng(7)
    # Build initial S respecting fixed C_5 and block signs
    S = np.ones((74, 74))
    np.fill_diagonal(S, 0.0)
    # C0 = 0..24, C1 = 24..72 (B1=24..40, B2=40..56, B3=56..72), w1=72, w2=73
    S[:24, 72] = S[72, :24] = 1.0
    S[:24, 73] = S[73, :24] = -1.0
    S[24:72, 72:74] = S[72:74, 24:72] = 1.0
    S[72, 73] = S[73, 72] = 1.0

    # Target spectrum of S: 17^1, 15^15, 11^3, -5^55 -> target G = 5I + S has 22^1, 20^15, 16^3, 0^55
    # Alternating projections between:
    #   (1) exact fixed structure + symmetric zero-diag in [-1, 1] (or discrete +-1)
    #   (2) rank-19 projection onto {22^1, 20^15, 16^3, 0^55}!
    # Actually let's project onto rank<=19 PSD cone!
    for trial in range(5):
        M = rng.normal(0, 1, (74, 74))
        M = 0.5 * (M + M.T)
        np.fill_diagonal(M, 0.0)
        M[:24, 72] = M[72, :24] = 1.0
        M[:24, 73] = M[73, :24] = -1.0
        M[24:72, 72:74] = M[72:74, 24:72] = 1.0
        M[72, 73] = M[73, 72] = 1.0
        for it in range(2000):
            # Project onto target spectrum 17^1, 15^15, 11^3, -5^55
            ev, vec = np.linalg.eigh(M)
            tgt = np.array([-5.0]*55 + [11.0]*3 + [15.0]*15 + [17.0]*1)
            M = (vec * tgt) @ vec.T
            M = 0.5 * (M + M.T)
            # Project onto discrete/box + exact linear locks
            np.fill_diagonal(M, 0.0)
            M = np.clip(M, -1.0, 1.0)
            M[:24, 72] = M[72, :24] = 1.0
            M[:24, 73] = M[73, :24] = -1.0
            M[24:72, 72:74] = M[72:74, 24:72] = 1.0
            M[72, 73] = M[73, 72] = 1.0
        ev = np.linalg.eigvalsh(M)
        disc_err = np.mean(np.abs(np.abs(M[np.triu_indices(74, 1)]) - 1.0))
        spec_err = np.linalg.norm(ev - tgt)
        print(f"  AltProj trial {trial}: disc_err={disc_err:.6f}, spec_err={spec_err:.6f}")


if __name__ == "__main__":
    check_24_8reg_graphs()
    check_full_74_rank_search()
