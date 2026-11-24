"""Run Gram L-BFGS + Discrete Seidel Rounding on (18, 58) and (19, 73)
from random starts and perturbed 57-line / 72-line seed matrices.
"""

from __future__ import annotations
import json
from pathlib import Path
from gram_opt import factor_from_seidel, run_gram_opt


RESULTS_DIR = Path(__file__).resolve().parent / "results"


def main():
    print("=== GRAM L-BFGS FRONTIER: (18, 58) ===")
    run_gram_opt(18, 58, restarts=32, maxiter=1000, seed=1001)
    for fname in ["cal_18_57_gsy21_f1.json", "cal_18_57_a5_3_a1_4_spec1_111.json", "cal_18_57_a9_2_a1.json"]:
        S57 = json.loads((RESULTS_DIR / fname).read_text())["S"]
        V57 = factor_from_seidel(S57, 18)
        print(f"Seeded from {fname}:")
        run_gram_opt(18, 58, restarts=24, maxiter=1000, seed=1002, V_seed_sub=V57)

    print("\n=== GRAM L-BFGS FRONTIER: (19, 73) ===")
    run_gram_opt(19, 73, restarts=24, maxiter=1000, seed=2001)
    S72 = json.loads((RESULTS_DIR / "cal_19_72_asche.json").read_text())["S"]
    V72 = factor_from_seidel(S72, 19)
    print("Seeded from cal_19_72_asche.json:")
    run_gram_opt(19, 73, restarts=24, maxiter=1000, seed=2002, V_seed_sub=V72)


if __name__ == "__main__":
    main()
