"""Python driver for the exact __int128 C++20 1-vertex extender (`extender`)."""

from __future__ import annotations
import json
import subprocess
import time
from pathlib import Path
from typing import Dict, List, Optional, Tuple
import sympy as sp

from verify import verify_seidel_system, save_verified_matrix


BASE_DIR = Path(__file__).resolve().parent
EXTENDER_BIN = BASE_DIR / "extender"
RESULTS_DIR = BASE_DIR / "results"


def prepare_query(S: List[List[int]]) -> Tuple[int, int, int, List[int], List[int], List[int], List[int], sp.Matrix]:
    """Compute exact (n, r, L, M_flat, C_flat, B, Bc, G_BB_inv) from Seidel matrix S."""
    n = len(S)
    S_mat = sp.Matrix(S)
    G = 5 * sp.eye(n) + S_mat
    _, pivots = G.rref()
    B = list(pivots)
    r = len(B)
    Bc = [i for i in range(n) if i not in set(B)]

    G_BB = G[B, B]
    G_BB_inv = G_BB.inv()
    # Exact common denominator of G_BB_inv (also clears denominators in G_{Bc,B} * G_BB^{-1})
    denoms = [sp.fraction(val)[1] for val in G_BB_inv]
    L = int(sp.ilcm(*denoms))

    M_mat = L * G_BB_inv
    C_mat = L * (G[Bc, B] * G_BB_inv)

    M_flat = [int(M_mat[i, j]) for i in range(r) for j in range(r)]
    C_flat = [int(C_mat[i, j]) for i in range(n - r) for j in range(r)]
    bound = 10**17
    assert 0 < L < bound, f"L={L} exceeds __int128 safety bound"
    assert all(abs(v) < bound for v in M_flat), "M entry exceeds __int128 safety bound"
    assert all(abs(v) < bound for v in C_flat), "C entry exceeds __int128 safety bound"
    return n, r, L, M_flat, C_flat, B, Bc, G_BB_inv


def run_extender_batch(seidel_matrices: List[List[List[int]]]) -> List[Dict]:
    """Run C++20 exact extender on a batch of Seidel matrices."""
    prepared = [prepare_query(S) for S in seidel_matrices]
    lines = []
    for n, r, L, M_flat, C_flat, _, _, _ in prepared:
        lines.append(f"{n} {r} {L}")
        lines.append(" ".join(map(str, M_flat)))
        if C_flat:
            lines.append(" ".join(map(str, C_flat)))
    lines.append("0")
    stdin_data = "\n".join(lines) + "\n"

    proc = subprocess.run(
        [str(EXTENDER_BIN)],
        input=stdin_data,
        text=True,
        capture_output=True,
        check=True,
    )

    results: List[Dict] = []
    cur: Optional[Dict] = None
    for line in proc.stdout.splitlines():
        parts = line.split()
        if not parts:
            continue
        if parts[0] == "QUERY_BEGIN":
            qidx = int(parts[1])
            n, r, L, _, _, B, Bc, G_BB_inv = prepared[qidx]
            cur = {
                "query_idx": qidx,
                "n": n,
                "r": r,
                "L": L,
                "B": B,
                "Bc": Bc,
                "G_BB_inv": G_BB_inv,
                "hits_eq_5": [],
                "hits_lt_5": [],
            }
        elif parts[0] == "HIT":
            assert cur is not None
            q = int(parts[1])
            L_val = int(parts[2])
            assert L_val == cur["L"]
            n = cur["n"]
            r = cur["r"]
            vals = [int(v) for v in parts[3:]]
            assert len(vals) == n
            xB = vals[:r]
            xBc = vals[r:]
            # Reconstruct x in original vertex order 0..n-1
            x = [0] * n
            for idx, b_pos in enumerate(cur["B"]):
                x[b_pos] = xB[idx]
            for idx, bc_pos in enumerate(cur["Bc"]):
                x[bc_pos] = xBc[idx]
            entry = {"q": q, "L": L_val, "x": x, "xB": xB}
            if q == 5 * L_val:
                cur["hits_eq_5"].append(entry)
            else:
                assert q < 5 * L_val
                cur["hits_lt_5"].append(entry)
        elif parts[0] == "QUERY_END":
            assert cur is not None
            cur["num_colspace_pm1"] = int(parts[1])
            cur["num_le_5L"] = int(parts[2])
            cur["num_eq_5L"] = int(parts[3])
            results.append(cur)
            cur = None

    assert len(results) == len(seidel_matrices)
    return results


def extend_matrix(S: List[List[int]], x: List[int]) -> List[List[int]]:
    n = len(S)
    out = [row[:] + [x[i]] for i, row in enumerate(S)]
    out.append(x[:] + [0])
    return out


def validate_positive_controls() -> None:
    print("=== POSITIVE CONTROLS FOR EXACT 1-VERTEX EXTENDER ===")
    # 1. GSY21_F1 minus vertex 0 -> must recover vertex 0 extension in R^18
    f1 = json.loads((RESULTS_DIR / "cal_18_57_gsy21_f1.json").read_text())["S"]
    f1_sub = [row[1:] for row in f1[1:]]
    res_f1_sub = run_extender_batch([f1_sub])[0]
    print(f"GSY21_F1[:-1] (n=56, r={res_f1_sub['r']}): colspace_pm1={res_f1_sub['num_colspace_pm1']}, eq_5={len(res_f1_sub['hits_eq_5'])}, lt_5={len(res_f1_sub['hits_lt_5'])}")
    assert len(res_f1_sub["hits_eq_5"]) >= 1
    S_rec = extend_matrix(f1_sub, res_f1_sub["hits_eq_5"][0]["x"])
    info_rec = verify_seidel_system(S_rec, d=18, compute_charpoly=False)
    assert info_rec["rank"] == 18 and info_rec["psd_verified"]

    # 2. Asche_19_72 minus vertex 0 -> must recover vertex 0 extension in R^19
    a72 = json.loads((RESULTS_DIR / "cal_19_72_asche.json").read_text())["S"]
    a72_sub = [row[1:] for row in a72[1:]]
    res_a72_sub = run_extender_batch([a72_sub])[0]
    print(f"Asche_19_72[:-1] (n=71, r={res_a72_sub['r']}): colspace_pm1={res_a72_sub['num_colspace_pm1']}, eq_5={len(res_a72_sub['hits_eq_5'])}, lt_5={len(res_a72_sub['hits_lt_5'])}")
    assert len(res_a72_sub["hits_eq_5"]) >= 1
    S_rec72 = extend_matrix(a72_sub, res_a72_sub["hits_eq_5"][0]["x"])
    info_rec72 = verify_seidel_system(S_rec72, d=19, compute_charpoly=False)
    assert info_rec72["rank"] == 19 and info_rec72["psd_verified"]


def test_calibrated_models() -> None:
    print("\n=== 1-VERTEX EXTENSION TESTS ON ALL CALIBRATED SYSTEMS ===")
    files = sorted(RESULTS_DIR.glob("cal_*.json"))
    mats = [json.loads(f.read_text()) for f in files]
    t0 = time.time()
    results = run_extender_batch([m["S"] for m in mats])
    dt = time.time() - t0
    print(f"Tested {len(mats)} calibrated matrices in {dt:.3f}s:")
    for m, res in zip(mats, results):
        print(
            f"  {m['name']:22s} (n={res['n']}, r={res['r']}): "
            f"colspace_pm1={res['num_colspace_pm1']:4d}, "
            f"same_dim_ext(q=5)={len(res['hits_eq_5'])}, "
            f"next_dim_ext(q<5)={len(res['hits_lt_5'])}"
        )


if __name__ == "__main__":
    validate_positive_controls()
    test_calibrated_models()
