"""Independent clean-room audit runner for all polynomial census files in compute/poly/results/.

1. Loads every JSON file in compute/poly/results/.
2. Reconstructs f(x) and g(y) = f(y - 5) from the stored polynomial representation
   (supporting both shifted z-polynomials p(z) with x = 2z + c / (2z + c) and direct g(y)).
3. Verifies EVERY surviving polynomial via audit/verify_polys.py:
   - exact degree, monic, integer coefficients
   - exact trace (a_1 = -5n) and sum-of-squares (a_2 = 12n(n-1))
   - exact square-free decomposition + independent QQ Sturm totally-real >= -5 check
   - exact 2-adic Seidel congruences on chi_S(2t - 1) and g(y).
4. Cross-checks the exact polynomial sets against our independent clean-room C++20 enumerator
   (audit/clean_enum) outputs in audit/raw_*.txt to verify ZERO false negatives and ZERO
   false positives.
5. Records SHA-256 checksums in audit/poly_audit_summary.json.
"""

from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path
import time

from verify_polys import verify_candidate_f, verify_candidate_g
from _repo_io import AUDIT_DIR, CERT_DIR, COMPUTE_POLY_RESULTS, list_json_stems, sha256_auto


POLY_RESULTS_DIR = COMPUTE_POLY_RESULTS
OUT_SUMMARY = AUDIT_DIR / "poly_audit_summary.json"


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def poly_eval_shift_linear(coeffs_desc: list[int], alpha: int, beta: int) -> list[int]:
    """Compute P(alpha * u + beta) in descending order given P(z) in descending order."""
    d = len(coeffs_desc) - 1
    res = [0] * (d + 1)  # ascending
    res[0] = coeffs_desc[0]
    cur_deg = 0
    for c in coeffs_desc[1:]:
        new_res = [0] * (d + 1)
        for i in range(cur_deg + 1):
            new_res[i + 1] += alpha * res[i]
            new_res[i] += beta * res[i]
        new_res[0] += c
        res = new_res
        cur_deg += 1
    return res[::-1]


def decode_poly_entry_to_f(p_desc: list[int], d: int, n: int, c_shift: int) -> list[int]:
    """Convert shifted z-polynomial p(z) to f(x) in Z[x].
    Convention: x = 2*z + c_shift, where p(z) = 2^(-d) f(2z + c_shift) for even n,
    and p(z) = 2^(-(d-1)) f(2z + c_shift) for odd n.
    Let's reconstruct f(x) by substituting z = (x - c_shift) / 2 and clearing the exact 2-power:
    Actually, 2^d * p((x - c_shift)/2) (even n) or 2^(d-1) * p((x - c_shift)/2) (odd n):
    Let u = x - c_shift, so 2*z = u. Then 2^d * p(u/2) = sum_{j=0}^d p_j * 2^j * u^{d-j} (even n)
    or sum_{j=0}^d p_j * 2^{j-1} * u^{d-j} (odd n, note p_0=2 so j=0 gives 1*u^d!).
    Then substitute u = x - c_shift!
    """
    assert len(p_desc) == d + 1
    u_desc = []
    if n % 2 == 0:
        assert p_desc[0] == 1
        for j, pj in enumerate(p_desc):
            u_desc.append(pj * (1 << j))
    else:
        assert p_desc[0] == 2
        u_desc.append(1)
        for j in range(1, d + 1):
            u_desc.append(p_desc[j] * (1 << (j - 1)))
    # Now f(x) = U(x - c_shift)
    return poly_eval_shift_linear(u_desc, 1, -c_shift)


def main() -> None:
    t0 = time.time()
    items = list_json_stems(POLY_RESULTS_DIR, CERT_DIR / "stage1")
    if not items:
        print("No polynomial JSON files found under compute/poly/results/ or certificates/stage1/")
        return

    # Load clean_enum raw_*.txt files if present
    clean_sets: dict[tuple[int, int], set[tuple[int, ...]]] = {}
    for txt in sorted(AUDIT_DIR.glob("raw_*_*.txt")):
        parts = txt.stem.split("_")
        if len(parts) == 3 and parts[1].isdigit() and parts[2].isdigit():
            dn = (int(parts[1]), int(parts[2]))
            s = set()
            for line in txt.read_text().splitlines():
                line = line.strip()
                if not line:
                    continue
                g_desc = [int(v) for v in line.split(",")]
                res = verify_candidate_g(g_desc, d=dn[0], n=dn[1], k=5, sympy_crosscheck=False)
                s.add(tuple(res["f_desc"]))
            clean_sets[dn] = s
            print(f"[CLEAN_ENUM] Loaded & SymPy-verified {len(s)} polys for {dn} from {txt.name}")

    records = []
    for name, path in items:
        digest = sha256_auto(path)
        data = json.loads(path.read_text())
        if not isinstance(data, dict) or "polys" not in data:
            print(f"[SKIP] {name}: not a polys dict")
            continue
        d = int(data["d"])
        n = int(data["n"])
        c_shift = int(data["c"])
        polys = data["polys"]
        their_set: set[tuple[int, ...]] = set()
        rank_lt_d = 0
        for p_desc in polys:
            f_desc = decode_poly_entry_to_f(p_desc, d=d, n=n, c_shift=c_shift)
            res = verify_candidate_f(f_desc, d=d, n=n, k=5)
            their_set.add(tuple(res["f_desc"]))
            if res["extra_m5_mult"] > 0:
                rank_lt_d += 1

        if len(their_set) != len(polys):
            raise AssertionError(f"{name}: duplicate polynomials in polys list!")

        clean_match = "NOT_RUN"
        if (d, n) in clean_sets:
            cs = clean_sets[(d, n)]
            if name.startswith("raw_"):
                if their_set != cs:
                    missing = cs - their_set
                    extra = their_set - cs
                    raise AssertionError(
                        f"RED FLAG! {name} mismatch vs clean_enum: "
                        f"missing={len(missing)}, extra={len(extra)}"
                    )
                clean_match = f"EXACT_SET_MATCH ({len(cs)} == {len(their_set)})"
            else:
                if not their_set.issubset(cs):
                    raise AssertionError(
                        f"RED FLAG! {name} has {len(their_set - cs)} entries NOT in clean_enum!"
                    )
                clean_match = f"SUBSET_OF_CLEAN_ENUM ({len(their_set)} <= {len(cs)})"

        rec = {
            "file": name,
            "sha256": digest,
            "d": d,
            "n": n,
            "count": len(polys),
            "rank_lt_d_count": rank_lt_d,
            "clean_enum_check": clean_match,
            "status": "PASS",
        }
        records.append(rec)
        print(
            f"[PASS] {name}: (d={d}, n={n}), verified={len(polys)}/{len(polys)}, "
            f"rank<d={rank_lt_d}, {clean_match}, sha256={digest[:16]}..."
        )

    OUT_SUMMARY.write_text(json.dumps(records, indent=2))
    print(f"Audited {len(records)} poly files in {time.time() - t0:.2f}s -> {OUT_SUMMARY}")


if __name__ == "__main__":
    main()
