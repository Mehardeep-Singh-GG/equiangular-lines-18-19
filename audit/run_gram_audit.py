"""Independent exact-arithmetic audit runner for calibrated Seidel/Gram matrices."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import time

from verify_gram import load_matrix_file, verify_seidel_and_gram
from verify_polys import verify_candidate_f
from _repo_io import AUDIT_DIR, CERT_DIR, COMPUTE_SEARCH_RESULTS, list_json_stems, sha256_auto


RESULTS_DIR = COMPUTE_SEARCH_RESULTS
OUT_SUMMARY = AUDIT_DIR / "gram_audit_summary.json"


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def infer_dn(path: Path, meta: dict) -> tuple[int, int]:
    ver = meta.get("verification", {})
    if "d" in ver and "n" in ver:
        return int(ver["d"]), int(ver["n"])
    if "d" in meta and "n" in meta:
        return int(meta["d"]), int(meta["n"])
    parts = path.stem.split("_")
    for i in range(len(parts) - 1):
        if parts[i].isdigit() and parts[i + 1].isdigit():
            return int(parts[i]), int(parts[i + 1])
    raise ValueError(f"Cannot infer (d, n) from {path}")


def main() -> None:
    t0 = time.time()
    items = list_json_stems(RESULTS_DIR, CERT_DIR / "calibration")
    if not items:
        print("No matrix JSON files found in compute/search/results/ or certificates/calibration/")
        return

    records = []
    for name, path in items:
        digest = sha256_auto(path)
        S_raw, meta = load_matrix_file(path)
        d, n = infer_dn(path, meta)
        res = verify_seidel_and_gram(S_raw, expected_d=d, k=5, expected_n=n)
        poly_res = verify_candidate_f(res["f_coeffs_desc"], d=d, n=n, k=5)

        # Cross-check against claimed metadata without trusting it
        claimed = meta.get("verification", {})
        if claimed:
            if "rank" in claimed and int(claimed["rank"]) != res["rank"]:
                raise AssertionError(
                    f"{name}: claimed rank {claimed['rank']} != verified {res['rank']}"
                )
        rec = {
            "file": name,
            "sha256": digest,
            "d": d,
            "n": n,
            "rank": res["rank"],
            "trace_S": res["trace_S"],
            "trace_S2": res["trace_S2"],
            "extra_m5_mult": poly_res["extra_m5_mult"],
            "f_coeffs_desc": res["f_coeffs_desc"],
            "sqf_factors": poly_res["sqf_factors"],
            "status": "PASS",
        }
        records.append(rec)
        print(
            f"[PASS] {name}: (d={d}, n={n}), exact rank={res['rank']}, "
            f"extra (-5) mult={poly_res['extra_m5_mult']}, sha256={digest[:16]}..."
        )

    OUT_SUMMARY.write_text(json.dumps(records, indent=2))
    print(f"Verified {len(records)} matrix files in {time.time() - t0:.2f}s -> {OUT_SUMMARY}")


if __name__ == "__main__":
    main()
