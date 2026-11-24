"""Continuous Gram-factorization L-BFGS + Discrete Seidel Rounding & Polishing.

Minimizes Phi(V) = sum_i (||v_i||^2 - 5)^2 + sum_{i<j} ((v_i^T v_j)^2 - 1)^2
over V in R^{d x n}. Whenever Phi(V) gets small, rounds S = sgn(V^T V - 5I)
and verifies exact rank(5I+S) <= d and PSD via SymPy.
"""

from __future__ import annotations
import json
import time
from pathlib import Path
from typing import Optional
import numpy as np
from scipy.optimize import minimize

from verify import verify_seidel_system, save_verified_matrix


BASE_DIR = Path(__file__).resolve().parent
RESULTS_DIR = BASE_DIR / "results"


def phi_and_grad(V_flat: np.ndarray, d: int, n: int):
    V = V_flat.reshape(d, n)
    G = V.T @ V  # n x n
    diag_err = np.diag(G) - 5.0
    # Off-diagonal error: (G_ij^2 - 1)
    G2m1 = G * G - 1.0
    np.fill_diagonal(G2m1, 0.0)

    # Phi = sum(diag_err^2) + 0.5 * sum_{i!=j} (G_ij^2 - 1)^2
    val = float(np.sum(diag_err * diag_err) + 0.5 * np.sum(G2m1 * G2m1))

    # dPhi/dG_ii = 2 * diag_err_i
    # dPhi/dG_ij (i!=j) = 2 * (G_ij^2 - 1) * G_ij (since symmetric sum 0.5*2 = 1, and G=V^T V gives dPhi/dV = 2 V * dPhi/dG)
    H = 2.0 * G2m1 * G
    np.fill_diagonal(H, 2.0 * diag_err)
    grad = 2.0 * (V @ H)
    return val, grad.ravel()


def check_rounded_seidel(V: np.ndarray, d: int) -> tuple[float, np.ndarray]:
    G = V.T @ V
    n = G.shape[0]
    S = np.where(G >= 0.0, 1, -1).astype(np.int64)
    np.fill_diagonal(S, 0)
    G_int = 5.0 * np.eye(n) + S.astype(np.float64)
    w = np.linalg.eigvalsh(G_int)
    k_null = n - d
    e = float(np.sum(w[:k_null] ** 2) + np.sum(w[k_null:][w[k_null:] < 0.0] ** 2))
    return e, S


def run_gram_opt(
    d: int,
    n: int,
    restarts: int = 32,
    maxiter: int = 1200,
    seed: int = 42,
    V_seed_sub: Optional[np.ndarray] = None,
) -> dict:
    rng = np.random.default_rng(seed)
    best_phi = 1e18
    best_e = 1e18
    solved = False
    t0 = time.time()

    for r in range(restarts):
        if V_seed_sub is not None and V_seed_sub.shape == (d, n - 1):
            V0 = np.empty((d, n), dtype=np.float64)
            V0[:, : n - 1] = V_seed_sub + rng.normal(0.0, 0.05 if r > 0 else 0.0, size=(d, n - 1))
            v_new = rng.normal(size=d)
            v_new *= np.sqrt(5.0) / np.linalg.norm(v_new)
            V0[:, n - 1] = v_new
        else:
            V0 = rng.normal(size=(d, n))
            V0 *= np.sqrt(5.0) / np.linalg.norm(V0, axis=0, keepdims=True)

        res = minimize(
            phi_and_grad,
            V0.ravel(),
            args=(d, n),
            method="L-BFGS-B",
            jac=True,
            options={"maxiter": maxiter, "ftol": 1e-13, "gtol": 1e-9},
        )
        phi_val = float(res.fun)
        V_opt = res.x.reshape(d, n)
        e_disc, S_disc = check_rounded_seidel(V_opt, d)
        if phi_val < best_phi:
            best_phi = phi_val
        if e_disc < best_e:
            best_e = e_disc

        if e_disc < 1e-6:
            # Verify in exact SymPy!
            info = verify_seidel_system(S_disc.tolist(), d=d, compute_charpoly=(d >= 18))
            print(f"  [SOLVED!] (d={d}, n={n}) restart={r} phi={phi_val:.2e} E_disc={e_disc:.2e} SymPy rank={info['rank']} PSD={info['psd_verified']}")
            solved = True
            if (d == 18 and n >= 58) or (d == 19 and n >= 73):
                save_verified_matrix(RESULTS_DIR / f"DISCOVERY_gram_{d}_{n}.json", f"DISCOVERY_gram_{d}_{n}", S_disc.tolist(), info)
            break

    dt = time.time() - t0
    print(f"Gram L-BFGS (d={d}, n={n}, restarts={restarts}): time={dt:.2f}s best_phi={best_phi:.6f} best_disc_E={best_e:.6f} solved={solved}")
    return {"d": d, "n": n, "best_phi": best_phi, "best_e": best_e, "solved": solved}


def factor_from_seidel(S: list, d: int) -> np.ndarray:
    """Get numerical V in R^{d x n} from exact Seidel S (5I+S = V^T V)."""
    n = len(S)
    G = 5.0 * np.eye(n) + np.array(S, dtype=np.float64)
    w, U = np.linalg.eigh(G)
    idx = np.argsort(w)[::-1][:d]
    w_pos = np.maximum(w[idx], 0.0)
    return (U[:, idx] * np.sqrt(w_pos)).T


if __name__ == "__main__":
    print("=== Positive Control: (14, 28) and (15, 36) ===")
    run_gram_opt(14, 28, restarts=16, maxiter=1000)
    run_gram_opt(15, 36, restarts=16, maxiter=1200)
