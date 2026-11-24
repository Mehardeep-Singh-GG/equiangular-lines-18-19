"""Zero-float-trust exact certification for S1 (6, 6, 4) of (19, 74) idx=13."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from exact_common import s1_o2_run_exact


def run(save_certs: bool = True) -> dict:
    return s1_o2_run_exact((6, 6, 4), save_certs=save_certs)


if __name__ == "__main__":
    res = run(save_certs=True)
    if not res["all_dead"]:
        sys.exit(1)
