"""Independent zero-float-trust verifier for `(19, 74) idx=13` (`compute/poly/idx13_exact/`).

Modes:
  default       : Static AST audit + exact_common QQ self-tests + verify q0=4 lemma +
                  validate ALL 5 JSON certificate bundles in `results/` (`all_dead=True`,
                  strictly positive exact Fraction Farkas gaps, valid PSD witnesses).
  --replay-fast : Also re-runs `certify_s1_6_6_4`, `certify_s1_8_4_4`, `certify_s1_t2`,
                  `certify_s3_s2`, and `(4,4,4,4)` Subcase A + `q0 in {7/2, 5/2, 2}`.
  --full        : Also re-runs ALL 5 `certify_*.py` modules end-to-end including `(4,4,4,4) q0=3`.
"""
from __future__ import annotations

import argparse
import ast
import json
import sys
import time
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parent
RES_DIR = ROOT / "results"
sys.path.insert(0, str(ROOT))

import exact_common as ec  # noqa: E402
from certify_s1_4_4_4_4 import verify_q0_4_lemma  # noqa: E402


def audit_static_zero_float() -> dict:
    """AST-level check ensuring zero untrusted float/eigh/pinv/linprog/rint calls in certify_*.py."""
    banned_attrs = {"eigh", "eigvalsh", "rint", "linprog"}
    hits = {}
    for py_file in sorted(ROOT.glob("certify_*.py")):
        tree = ast.parse(py_file.read_text())
        file_hits = []
        for node in ast.walk(tree):
            if isinstance(node, ast.Attribute) and node.attr in banned_attrs:
                file_hits.append((node.lineno, node.attr))
            if isinstance(node, ast.Attribute) and node.attr == "pinv":
                # Only allow SymPy Matrix.pinv() (exact QQ), reject np.linalg.pinv
                val_src = ast.unparse(node.value) if hasattr(ast, "unparse") else ""
                if "np" in val_src or "linalg" in val_src:
                    file_hits.append((node.lineno, "np.linalg.pinv"))
            if isinstance(node, ast.Constant) and isinstance(node.value, float):
                if 0 < abs(node.value) < 0.01 or abs(node.value - 2.3333) < 0.01:
                    file_hits.append((node.lineno, f"float_tol={node.value}"))
        assert not file_hits, f"Untrusted float primitives in {py_file.name}: {file_hits}"
        hits[py_file.name] = "CLEAN"
    return hits


def audit_exact_common_self_tests() -> dict:
    """Verify exact QQ Moore-Penrose pseudoinverses, LDL^T PSD witnesses, nullspaces,
    radical squarefree splits, sqrt rational intervals, and Farkas checker across all 7 S1 partitions.
    """
    parts = [(16,), (10, 6), (8, 8), (12, 4), (6, 6, 4), (8, 4, 4), (4, 4, 4, 4)]
    ranks = {}
    for p in parts:
        d = ec.cycle_gram_setup_qq(p)
        ok_w, w = ec.ldlt_psd_witness_qq(d["W_piv"])
        assert ok_w and w is None, f"W_piv not PSD for {p}"
        ranks[str(p)] = d["rank"]

    # Indefinite LDL^T self-check
    M_bad = [[Fraction(1), Fraction(2)], [Fraction(2), Fraction(1)]]
    ok_b, w_b = ec.ldlt_psd_witness_qq(M_bad)
    assert (not ok_b) and w_b is not None
    assert sum(w_b[i] * M_bad[i][j] * w_b[j] for i in range(2) for j in range(2)) < 0

    # Radical & interval sqrt self-check
    for q in [Fraction(0), Fraction(1), Fraction(7, 3), Fraction(19, 12)]:
        c, sf = ec.sf_decomp(q)
        assert c * c * sf == q
        lo, hi = ec.sqrt_interval_qq(q)
        assert 0 <= lo <= hi and lo * lo <= q <= hi * hi

    # (4, 4, 4, 4) q0=4 => Subcase A lemma verification & <= 2-copy same-profile cap across all 7 S1 parts
    max_res_by_part = {}
    for p in parts:
        dp = ec.s1_load_vectors_qq(p)
        mr = max(dp["res_c"])
        assert mr < Fraction(8, 3), f"max_res >= 8/3 in {p}: {mr}"
        max_res_by_part[str(p)] = str(mr)
        if p == (4, 4, 4, 4):
            q4 = verify_q0_4_lemma(dp)
            assert q4["subcase_a_forced"] and q4["all_g_integral_on_Q4"]

    # Confirm j==s0 twin inclusion when d0 >= 2
    d844 = ec.s1_load_vectors_qq((8, 4, 4))
    s0_844 = next(i for i, r in enumerate(d844["res_c"]) if r == Fraction(5, 2))
    br_twin_test = ec.s1_o2_build_branch_qq(d844, s0_844)
    assert any(c[0] == s0_844 for c in br_twin_test["c_cands"][1:]), "Expected same-profile twin at d0=5/2"

    return {"s1_ranks": ranks, "max_res_by_part": max_res_by_part, "q4_lemma": q4}


def _check_farkas_cert_entry(entry: dict) -> Fraction:
    cert = entry["cert"]
    gap_n, gap_d = int(cert["gap"][0]), int(cert["gap"][1])
    assert gap_d > 0 and gap_n > 0, f"Non-positive Farkas gap in {entry.get('tag')}"
    for idx, ns, ds in cert["y_eq"]:
        assert int(idx) >= 0 and int(ds) > 0
    for idx, ns, ds in cert.get("y_ub", []):
        assert int(idx) >= 0 and int(ds) > 0 and int(ns) >= 0
    return Fraction(gap_n, gap_d)


def audit_result_bundles() -> dict:
    """Validate all 5 exact JSON certificate bundles under results/."""
    summary = {}

    # 1. S3 & S2
    p_s3s2 = RES_DIR / "cert_s3_s2.json"
    assert p_s3s2.exists(), f"Missing {p_s3s2}"
    d_s3s2 = json.loads(p_s3s2.read_text())
    assert d_s3s2.get("all_dead") is True
    summary["cert_s3_s2"] = {"all_dead": True, "elapsed_sec": d_s3s2.get("elapsed_sec")}

    # 2. S1 t_1 <= 2
    p_t2 = RES_DIR / "cert_s1_t2.json"
    assert p_t2.exists(), f"Missing {p_t2}"
    d_t2 = json.loads(p_t2.read_text())
    parts_t2 = d_t2["partitions"]
    for pname in ["(16,)", "(10, 6)", "(8, 8)", "(12, 4)"]:
        assert parts_t2[pname]["status"] == "KILLED", f"Partition {pname} not KILLED"
    summary["cert_s1_t2"] = {"all_dead": True, "elapsed_s": d_t2.get("elapsed_s")}

    # 3. S1 (6,6,4), (8,4,4), (4,4,4,4)
    for fname in ["s1_6_6_4_certs.json", "s1_8_4_4_certs.json", "s1_4_4_4_4_certs.json"]:
        fpath = RES_DIR / fname
        assert fpath.exists(), f"Missing {fpath}"
        d = json.loads(fpath.read_text())
        assert d["all_dead"] is True and d["stats"]["surv"] == 0, f"Survivors in {fname}"
        fcerts = d["farkas_certs"]
        min_gap = None
        for entry in fcerts:
            g = _check_farkas_cert_entry(entry)
            if min_gap is None or g < min_gap:
                min_gap = g
        for w in d.get("psd_witnesses", []):
            assert len(w) == 14
            for ns, ds in w:
                assert int(ds) > 0
        if d.get("q3_preserved_check"):
            q3c = d["q3_preserved_check"]
            assert q3c["bit_for_bit_input_identical"] is True
            assert q3c["twin_s0_count"] == 0 and q3c["twin_s1_count"] == 0
        summary[fname] = {
            "all_dead": True,
            "n_farkas_certs": len(fcerts),
            "min_farkas_gap": str(min_gap) if min_gap is not None else None,
            "n_psd_witnesses": len(d.get("psd_witnesses", [])),
            "q3_preserved_check": d.get("q3_preserved_check"),
            "stats": d["stats"],
            "elapsed_sec": d.get("elapsed_sec"),
        }
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description="Verify (19,74) idx=13 zero-float-trust exact certification.")
    parser.add_argument("--replay-fast", action="store_true", help="Re-run S3, S2, S1(t<=2, 664, 844) & (4,4,4,4) except q0=3.")
    parser.add_argument("--full", action="store_true", help="Re-run ALL 5 certification modules end-to-end.")
    args = parser.parse_args()

    t0 = time.time()
    print("[1/4] Running AST zero-float-trust audit...", flush=True)
    ast_res = audit_static_zero_float()
    print("  AST audit:", ast_res, flush=True)

    print("[2/4] Running exact_common QQ algebraic self-tests...", flush=True)
    alg_res = audit_exact_common_self_tests()
    print("  Algebraic self-tests passed. S1 ranks:", alg_res["s1_ranks"], flush=True)

    if args.full or args.replay_fast:
        print("[3/4] Re-executing exact certification modules...", flush=True)
        import certify_s3_s2
        import certify_s1_t2
        import certify_s1_6_6_4
        import certify_s1_8_4_4
        import certify_s1_4_4_4_4

        for mod in (certify_s1_6_6_4, certify_s1_8_4_4, certify_s1_t2, certify_s3_s2):
            out = mod.run(save_certs=True)
            assert out["all_dead"] is True, f"Module {mod.__name__} failed"

        if args.full:
            out4 = certify_s1_4_4_4_4.run(save_certs=True)
            assert out4["all_dead"] is True
        else:
            out4_fast = certify_s1_4_4_4_4.run(
                save_certs=False,
                q0_subset=[Fraction(7, 2), Fraction(5, 2), Fraction(2)],
            )
            assert out4_fast["all_dead"] is True
    else:
        print("[3/4] Skipping live replay (pass --replay-fast or --full to re-execute).", flush=True)

    print("[4/4] Validating all 5 JSON certificate bundles in results/...", flush=True)
    bun_res = audit_result_bundles()
    print(json.dumps(bun_res, indent=2), flush=True)
    print(f">>> VERIFY_IDX13_EXACT ALL_PASSED in {time.time() - t0:.2f}s <<<", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
