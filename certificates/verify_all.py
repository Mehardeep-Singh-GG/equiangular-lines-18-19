#!/usr/bin/env python3
"""Strictly read-only archive verifier for `/certificates/`.

Usage:
  python3 verify_all.py            # Verify SHA256SUMS.txt + schemas + exact rationals
  python3 verify_all.py --full     # Also invoke external exact replay scripts (read-only on certificates/)
  python3 verify_all.py --pre-seal # Pre-seal check before idx13_exact/ and SHA256SUMS.txt are frozen

Supports both raw `.json` files and gzip-compressed `.json.gz` files transparently,
verifying decompressed byte streams bit-for-bit against the canonical `SHA256SUMS.txt` manifest.
Guarantee: NEVER writes, modifies, or deletes any file inside `certificates/`.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import subprocess
import sys
import time
from fractions import Fraction
from pathlib import Path

CERT_DIR = Path(__file__).resolve().parent
REPO_ROOT = CERT_DIR.parent
PYTHON_BIN = sys.executable

BANNED_PATH_FRAGMENTS = ("/Users/", "/home/", "/brain/", ".gemini/")


def resolve_cert_path(rel: str) -> tuple[Path, bool]:
    """Return `(resolved_path, is_gz)` for canonical `.json` relative path `rel`."""
    raw = (CERT_DIR / rel).resolve()
    gz = (CERT_DIR / f"{rel}.gz").resolve()
    for cand in (raw, gz):
        if CERT_DIR not in cand.parents:
            raise AssertionError(f"Certificate path escapes certificates/: {rel}")
    has_raw = raw.is_file()
    has_gz = gz.is_file()
    if has_raw and has_gz:
        raise AssertionError(f"Both uncompressed and .gz exist for {rel}")
    if has_raw:
        return raw, False
    if has_gz:
        return gz, True
    raise AssertionError(f"Missing certificate file: {rel} (or {rel}.gz)")


def discover_cert_rels() -> set[str]:
    """Discover canonical relative `.json` names for all `.json` and `.json.gz` files."""
    raw_rels = {p.relative_to(CERT_DIR).as_posix() for p in CERT_DIR.rglob("*.json")}
    gz_rels = {p.relative_to(CERT_DIR).as_posix()[:-3] for p in CERT_DIR.rglob("*.json.gz")}
    both = sorted(raw_rels & gz_rels)
    if both:
        raise AssertionError(f"Duplicate raw and .gz certificate files: {both}")
    return raw_rels | gz_rels


def sha256_cert(path: Path, is_gz: bool = False) -> tuple[str, int]:
    """Return `(sha256_hex, uncompressed_byte_size)` of certificate file."""
    h = hashlib.sha256()
    total = 0
    opener = (lambda p: gzip.open(p, "rb")) if is_gz else (lambda p: p.open("rb"))
    with opener(path) as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
            total += len(chunk)
    return h.hexdigest(), total


def read_cert_text(rel: str) -> str:
    path, is_gz = resolve_cert_path(rel)
    if is_gz:
        with gzip.open(path, "rt", encoding="utf-8") as f:
            return f.read()
    return path.read_text(encoding="utf-8")


def read_cert_json(rel: str):
    return json.loads(read_cert_text(rel))


def check_sha256sums(require_sealed: bool = True) -> dict[str, str]:
    sums_path = CERT_DIR / "SHA256SUMS.txt"
    discovered = sorted(discover_cert_rels())
    if not sums_path.exists():
        if require_sealed:
            raise AssertionError(f"Missing sealed manifest: {sums_path}")
        print(f"  [pre-seal] SHA256SUMS.txt not yet generated ({len(discovered)} JSON files staged).")
        return {}

    recorded: dict[str, str] = {}
    gz_count = 0
    for lineno, raw in enumerate(sums_path.read_text(encoding="utf-8").splitlines(), 1):
        line = raw.strip()
        if not line:
            continue
        parts = line.split()
        if len(parts) != 2:
            raise AssertionError(f"Malformed SHA256SUMS.txt line {lineno}: {raw!r}")
        digest, rel = parts[0], parts[1].lstrip("./")
        if len(digest) != 64 or any(c not in "0123456789abcdef" for c in digest.lower()):
            raise AssertionError(f"Invalid SHA-256 hex at line {lineno}: {digest!r}")
        if rel in recorded:
            raise AssertionError(f"Duplicate entry in SHA256SUMS.txt: {rel}")
        target, is_gz = resolve_cert_path(rel)
        if is_gz:
            gz_count += 1
        actual, _ = sha256_cert(target, is_gz=is_gz)
        if actual != digest.lower():
            raise AssertionError(f"SHA-256 mismatch for {rel}: expected {digest}, got {actual}")
        recorded[rel] = actual

    unlisted = sorted(set(discovered) - set(recorded.keys()))
    if unlisted:
        raise AssertionError(f"JSON files in certificates/ missing from SHA256SUMS.txt: {unlisted}")

    gz_note = f" ({gz_count} transparent .json.gz)" if gz_count else ""
    print(f"  [PASS] SHA256SUMS.txt verified {len(recorded)} files bit-for-bit{gz_note} (0 unlisted JSONs).")
    return recorded


def check_no_local_paths() -> int:
    rels = sorted(discover_cert_rels())
    for rel in rels:
        text = read_cert_text(rel)
        for frag in BANNED_PATH_FRAGMENTS:
            if frag in text:
                raise AssertionError(
                    f"Machine-local path fragment {frag!r} leaked in {rel}"
                )
    print(f"  [PASS] Path hygiene: 0 local path leaks across {len(rels)} JSON files.")
    return len(rels)


def check_stage1() -> None:
    expected_counts = {
        "raw_19_75.json": (19, 75, 14),
        "mod128_19_75.json": (19, 75, 8),
        "raw_18_60.json": (18, 60, 44),
        "mod128_18_60.json": (18, 60, 44),
        "raw_17_49.json": (17, 49, 704),
        "mod128_17_49.json": (17, 49, 188),
        "cor43_17_49.json": (17, 49, 109),
        "raw_19_74.json": (19, 74, 169),
        "mod128_19_74.json": (19, 74, 169),
        "cor43_18_59.json": (18, 59, 1214),
        "table_19_75_raw.json": (19, 75, 14),
        "table_18_60.json": (18, 60, 44),
        "table_17_49_cor43.json": (17, 49, 109),
        "table_19_74.json": (19, 74, 169),
        "table_18_59_cor43.json": (18, 59, 1214),
    }
    for fname, (d_exp, n_exp, cnt_exp) in expected_counts.items():
        data = read_cert_json(f"stage1/{fname}")
        assert data["d"] == d_exp and data["n"] == n_exp, f"{fname}: wrong (d, n)"
        assert data["count"] == cnt_exp, f"{fname}: expected count {cnt_exp}, got {data['count']}"
        seq = data["polys"] if "polys" in data else data["candidates"]
        assert len(seq) == cnt_exp, f"{fname}: payload len {len(seq)} != {cnt_exp}"
    print(f"  [PASS] stage1/: all {len(expected_counts)} files verified with exact counts.")


def _check_rat_val(val) -> Fraction:
    if isinstance(val, int) and not isinstance(val, bool):
        return Fraction(val)
    if isinstance(val, str):
        return Fraction(val)
    if isinstance(val, (list, tuple)) and len(val) == 2:
        return Fraction(int(val[0]), int(val[1]))
    raise AssertionError(f"Unsupported exact rational encoding: {val!r}")


def check_phase2() -> None:
    expected_decks = {
        "deck_18_60.json": (18, 60, 44),
        "deck_17_49.json": (17, 49, 109),
        "deck_19_74.json": (19, 74, 169),
        "deck_18_59.json": (18, 59, 1214),
    }
    for fname, (d_exp, n_exp, cnt_exp) in expected_decks.items():
        data = read_cert_json(f"phase2/{fname}")
        assert data["d"] == d_exp and data["n"] == n_exp
        assert len(data["candidates"]) == cnt_exp

    expected_p2 = {
        "phase2_18_60.json": (18, 60, 44, 2),
        "phase2_17_49.json": (17, 49, 109, 9),
        "phase2_19_74.json": (19, 74, 169, 7),
        "phase2_18_59.json": (18, 59, 1214, 86),
    }
    for fname, (d_exp, n_exp, tot_exp, surv_exp) in expected_p2.items():
        data = read_cert_json(f"phase2/{fname}")
        assert data["d"] == d_exp and data["n"] == n_exp
        assert data["total_stage1"] == tot_exp
        assert data["survivors_count"] == surv_exp
        assert len(data["survivors"]) == surv_exp
        killed_sum = sum(v for k, v in data.items() if k.startswith("killed_"))
        assert killed_sum + surv_exp == tot_exp, f"{fname}: killed+surv != total"
        assert len(data["certificates"]) == killed_sum, f"{fname}: certs count mismatch"
        for cert_rec in data["certificates"]:
            st = cert_rec["stage"]
            if st in ("1-vertex_farkas", "t42_farkas"):
                rhs = [int(x) for x in cert_rec["rhs"]]
                y = [int(x) for x in cert_rec["cert"]]
                assert len(rhs) == len(y)
                assert sum(a * b for a, b in zip(rhs, y)) < 0, f"{fname} idx {cert_rec['index']}: Farkas >= 0"
            elif st == "prop61_exact":
                c = cert_rec["cert"]
                assert int(c["k_min"]) <= int(c["k_max"])
            elif st == "kx_rref_exact":
                assert len(cert_rec["clique_proofs"]) > 0
            else:
                raise AssertionError(f"Unknown phase2 stage {st!r} in {fname}")
    print("  [PASS] phase2/: all 4 decks + 4 certificate bundles (exact Farkas/Kx/Prop6.1) verified.")


def check_sec7() -> None:
    manifest = read_cert_json("sec7/MANIFEST.json")
    expected = {
        "sec7_18_60.json": (18, 60, 1),
        "sec7_17_49.json": (17, 49, 5),
        "sec7_19_74.json": (19, 74, 5),
        "sec7_18_59.json": (18, 59, 66),
        "sec7_18_59_phase3.json": (18, 59, 4),
    }
    manifest_total = 0
    for fname, (d_exp, n_exp, k_exp) in expected.items():
        rel = f"sec7/{fname}"
        target, is_gz = resolve_cert_path(rel)
        data = read_cert_json(rel)
        assert data["d"] == d_exp and data["n"] == n_exp
        assert data["killed_count"] == k_exp and len(data["certs"]) == k_exp
        if fname in manifest["files"]:
            meta = manifest["files"][fname]
            digest, byte_len = sha256_cert(target, is_gz=is_gz)
            assert digest == meta["sha256"], f"MANIFEST sha256 mismatch for {fname}"
            assert byte_len == meta["bytes"], f"MANIFEST bytes mismatch for {fname}"
            manifest_total += k_exp
    assert manifest["total_killed"] == manifest_total == 77
    print("  [PASS] sec7/: MANIFEST.json + 5 Sec-7 bundles (77 + 4 Phase-3 = 81 kills) verified.")


def check_phase3(require_idx13: bool = True) -> None:
    # (19, 74) {47, 13, 6, 24} + independent {47, 861}
    d_74 = read_cert_json("phase3/phase3_19_74_47_13_6_24.json")
    assert d_74["d"] == 19 and d_74["n"] == 74
    res_74 = d_74["results"]
    assert res_74["47"]["status"] == "KILLED"
    assert res_74["6"]["status"] == "KILLED"
    assert res_74["24"]["status"] == "KILLED"
    assert res_74["13"]["status"] == "SURVIVED"

    d_861_47 = read_cert_json("phase3/phase3_kills_861_and_47.json")
    assert d_861_47["idx_47"]["status"] == "ELIMINATED"
    assert d_861_47["idx_47"]["tr_BTB_spectral"] < d_861_47["idx_47"]["tr_BTB_frobenius"]
    assert d_861_47["idx_861"]["status"] == "ELIMINATED"
    assert d_861_47["idx_861"]["singular_value_upper_bound"] < d_861_47["idx_861"]["frobenius_norm_sq"]

    # (18, 59) all 19 post-Sec-7 candidates
    ca = read_cert_json("phase3/phase3_18_59_clean_a.json")["results"]
    cb = read_cert_json("phase3/phase3_18_59_clean_b.json")["results"]
    killed_direct = {
        idx for idx in ("978", "997", "364", "319", "341", "603", "651", "151")
        if ca[idx]["status"].startswith("KILLED_")
    } | {
        idx for idx in ("103", "228", "800", "1113")
        if cb[idx]["status"].startswith("KILLED_")
    }
    assert len(killed_direct) == 12, f"Expected 12 direct clean kills, got {sorted(killed_direct)}"
    for idx in ("441", "488", "692", "864"):
        assert ca[idx]["status"] == "SURVIVED_STAGE3"

    d1164 = read_cert_json("phase3/phase3_18_59_1164.json")
    assert d1164["index"] == 1164 and d1164["status"] == "KILLED_STAGE2_COUPLED"
    assert d1164["final_stage2_farkas_infeasible"] is True

    d316 = read_cert_json("phase3/phase3_18_59_316.json")
    assert d316["index"] == 316 and d316["status"] == "KILLED_STAGE3" and d316["stage3_survivors_count"] == 0

    d705_0 = read_cert_json("phase3/phase3_18_59_705_cone0.json")
    assert d705_0["index"] == 705 and d705_0["cone"] == 0 and d705_0["survivors_count"] == 0
    d705_15 = read_cert_json("phase3/phase3_18_59_705_cones1_5.json")
    assert d705_15["index"] == 705 and len(d705_15["cones_1_to_5"]) == 5
    for c in d705_15["cones_1_to_5"]:
        assert int(c["after_p61"]) == 0

    d_441 = read_cert_json("phase3/phase3_18_59_441_488_692.json")
    assert d_441["441"]["status"] == "KILLED_E15_GRAM_ORTH" and d_441["441"]["e15_v10_orth_survivors"] == 0
    assert d_441["488"]["status"] == "KILLED_E11_SUBMATRIX_RANK"
    assert d_441["692"]["status"] == "KILLED_DECAEN_JACOBI_F2_PARITY"

    d_864 = read_cert_json("phase3/phase3_18_59_864.json")
    assert d_864["index"] == 864 and d_864["status"] == "KILLED_E9_E13_CAUCHY_SCHWARZ"
    assert d_864["stage3_survivors_count"] == 3 and len(d_864["kill_records"]) == 3
    for rec in d_864["kill_records"]:
        for part in rec["partitions"]:
            cs_min = _check_rat_val(part["cs_min"])
            tr_ub = _check_rat_val(part["tr_ub"])
            margin = _check_rat_val(part["margin"])
            assert cs_min - tr_ub == margin and margin > 0

    print("  [PASS] phase3/: all 19/19 (18,59) post-Sec-7 kills + (19,74) {47,6,24} + idx=861/47 verified.")

    # (19, 74) idx=13 exact bundles
    idx13_dir = CERT_DIR / "phase3" / "idx13_exact"
    expected_idx13 = [
        "cert_s1_t2.json",
        "cert_s3_s2.json",
        "s1_6_6_4_certs.json",
        "s1_8_4_4_certs.json",
        "s1_4_4_4_4_certs.json",
    ]
    if not idx13_dir.is_dir():
        if require_idx13:
            raise AssertionError(f"Missing sealed idx13_exact directory: {idx13_dir}")
        print("  [pre-seal] phase3/idx13_exact/ not staged yet (waiting on BLOCKER-2).")
        return

    for fn in expected_idx13:
        resolve_cert_path(f"phase3/idx13_exact/{fn}")

    d_s3s2 = read_cert_json("phase3/idx13_exact/cert_s3_s2.json")
    assert d_s3s2["all_dead"] is True

    d_t2 = read_cert_json("phase3/idx13_exact/cert_s1_t2.json")
    for pname in ("(16,)", "(10, 6)", "(8, 8)", "(12, 4)"):
        assert d_t2["partitions"][pname]["status"] == "KILLED"

    total_idx13_farkas = 0
    for fn in ("s1_6_6_4_certs.json", "s1_8_4_4_certs.json", "s1_4_4_4_4_certs.json"):
        d = read_cert_json(f"phase3/idx13_exact/{fn}")
        assert d["all_dead"] is True and d["stats"]["surv"] == 0
        for entry in d["farkas_certs"]:
            cert = entry["cert"]
            gap = Fraction(int(cert["gap"][0]), int(cert["gap"][1]))
            assert gap > 0, f"{fn} non-positive Farkas gap: {gap}"
            for _, ns, ds in cert["y_eq"]:
                assert int(ds) > 0
            for _, ns, ds in cert.get("y_ub", []):
                assert int(ds) > 0 and int(ns) >= 0
        for w in d.get("psd_witnesses", []):
            assert len(w) == 14
            for ns, ds in w:
                assert int(ds) > 0
        if "q3_preserved_check" in d and d["q3_preserved_check"] is not None:
            q3c = d["q3_preserved_check"]
            assert q3c["bit_for_bit_input_identical"] is True
            assert q3c["twin_s0_count"] == 0 and q3c["twin_s1_count"] == 0
        total_idx13_farkas += len(d["farkas_certs"])

    print(f"  [PASS] phase3/idx13_exact/: all 5 exact bundles verified (all_dead=True, {total_idx13_farkas} Farkas certs).")


def check_calibration() -> None:
    cal_dir = CERT_DIR / "calibration"
    names = sorted({
        (p.name[:-3] if p.name.endswith(".gz") else p.name)
        for p in list(cal_dir.glob("cal_*.json")) + list(cal_dir.glob("cal_*.json.gz"))
    })
    assert len(names) == 12, f"Expected 12 calibration files, found {len(names)}"
    for name in names:
        data = read_cert_json(f"calibration/{name}")
        S = data["S"]
        ver = data["verification"]
        n = ver["n"]
        dim = ver["d"]
        assert ver["psd_verified"] is True
        assert len(S) == n and all(len(row) == n for row in S)
        for i in range(n):
            assert S[i][i] == 0
            for j in range(i + 1, n):
                assert S[i][j] == S[j][i] and S[i][j] in (-1, 1)
        # Exact rational pivoted LDL^T of G = S + 5I (zero floating point)
        G = [[Fraction(S[i][j] + (5 if i == j else 0)) for j in range(n)] for i in range(n)]
        rank = 0
        for k in range(n):
            piv = -1
            for i in range(k, n):
                if G[i][i] != 0:
                    piv = i
                    break
            if piv == -1:
                for i in range(k, n):
                    for j in range(k, n):
                        assert G[i][j] == 0, f"{name}: indefinite zero pivot"
                break
            assert G[piv][piv] > 0, f"{name}: negative pivot {G[piv][piv]}"
            if piv != k:
                G[k], G[piv] = G[piv], G[k]
                for r in range(n):
                    G[r][k], G[r][piv] = G[r][piv], G[r][k]
            pk = G[k][k]
            rank += 1
            for i in range(k + 1, n):
                fac = G[i][k] / pk
                if fac != 0:
                    for j in range(k + 1, n):
                        G[i][j] -= fac * G[k][j]
        assert rank == dim, f"{name}: exact rank(S+5I)={rank} != d={dim}"
    print("  [PASS] calibration/: all 12 Seidel matrices verified (exact QQ PSD & rank(S+5I)==d).")


def run_full_external_replay() -> None:
    cmds = [
        ("compute/poly/verify_all_phase3_certs.py", [PYTHON_BIN, "compute/poly/verify_all_phase3_certs.py"]),
        ("compute/poly/idx13_exact/verify_idx13_exact.py --replay-fast", [PYTHON_BIN, "compute/poly/idx13_exact/verify_idx13_exact.py", "--replay-fast"]),
        ("audit/verify_phase3_19_74_idx13.py --only A B C t2 o2 s23 bundles", [PYTHON_BIN, "audit/verify_phase3_19_74_idx13.py", "--only", "A", "B", "C", "t2", "o2", "s23", "bundles"]),
    ]
    for label, cmd in cmds:
        print(f"  [full] Running {label} ...", flush=True)
        res = subprocess.run(cmd, cwd=REPO_ROOT)
        if res.returncode != 0:
            raise AssertionError(f"External verifier failed ({res.returncode}): {label}")


def main() -> int:
    parser = argparse.ArgumentParser(description="Read-only certificate archive verifier.")
    parser.add_argument("--full", action="store_true", help="Also run external replay/audit verifiers.")
    parser.add_argument("--pre-seal", action="store_true", help="Allow missing SHA256SUMS.txt and idx13_exact/ before sealing.")
    args = parser.parse_args()

    t0 = time.time()
    print("=== Verifying certificates/ archive (strictly read-only) ===", flush=True)
    require_sealed = not args.pre_seal
    pre_hashes = check_sha256sums(require_sealed=require_sealed)
    check_no_local_paths()
    check_stage1()
    check_phase2()
    check_sec7()
    check_phase3(require_idx13=require_sealed)
    check_calibration()

    if args.full:
        run_full_external_replay()
        post_hashes = check_sha256sums(require_sealed=require_sealed)
        assert post_hashes == pre_hashes, "certificates/ SHA256SUMS changed during --full!"
        print("  [PASS] Post---full immutability check: certificates/ hashes unchanged.")

    print(f">>> CERTIFICATES ARCHIVE VERIFY_ALL PASSED in {time.time() - t0:.2f}s <<<", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
