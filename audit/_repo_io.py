"""Self-contained repository path and JSON/gzip loader for standalone verification scripts in `audit/`."""
from __future__ import annotations

import gzip
import hashlib
import json
from pathlib import Path
from typing import Any

AUDIT_DIR = Path(__file__).resolve().parent
REPO_ROOT = AUDIT_DIR.parent
CERT_DIR = REPO_ROOT / "certificates"
COMPUTE_POLY_RESULTS = REPO_ROOT / "compute" / "poly" / "results"
COMPUTE_SEARCH_RESULTS = REPO_ROOT / "compute" / "search" / "results"


def _cert_search_dirs() -> list[Path]:
    return [
        COMPUTE_POLY_RESULTS,
        COMPUTE_SEARCH_RESULTS,
        CERT_DIR / "stage1",
        CERT_DIR / "phase2",
        CERT_DIR / "sec7",
        CERT_DIR / "phase3",
        CERT_DIR / "phase3" / "idx13_exact",
        CERT_DIR / "calibration",
    ]


def resolve_data_file(base_dir: Path | None, filename: str) -> tuple[Path, bool]:
    """Find `filename` (raw or `.json.gz`) in `base_dir` or fallback `certificates/` directories."""
    candidates: list[Path] = []
    if base_dir is not None:
        candidates.append(base_dir / filename)
    for d in _cert_search_dirs():
        cand = d / filename
        if cand not in candidates:
            candidates.append(cand)

    for cand in candidates:
        if cand.is_file():
            return cand, cand.name.endswith(".gz")
        gz = cand.with_name(cand.name + ".gz")
        if gz.is_file():
            return gz, True
    raise FileNotFoundError(f"Could not locate {filename!r} (or .gz) under compute/ or certificates/")


def read_text_auto(base_dir: Path | None, filename: str) -> str:
    path, is_gz = resolve_data_file(base_dir, filename)
    if is_gz:
        with gzip.open(path, "rt", encoding="utf-8") as f:
            return f.read()
    return path.read_text(encoding="utf-8")


def read_json_auto(base_dir: Path | None, filename: str) -> Any:
    return json.loads(read_text_auto(base_dir, filename))


def sha256_auto(path: Path) -> str:
    h = hashlib.sha256()
    if path.name.endswith(".gz"):
        with gzip.open(path, "rb") as f:
            for chunk in iter(lambda: f.read(65536), b""):
                h.update(chunk)
    else:
        with path.open("rb") as f:
            for chunk in iter(lambda: f.read(65536), b""):
                h.update(chunk)
    return h.hexdigest()


def list_json_stems(*dirs: Path) -> list[tuple[str, Path]]:
    """Return unique sorted `(canonical_json_filename, resolved_path)` across given directories."""
    found: dict[str, Path] = {}
    for d in dirs:
        if not d.is_dir():
            continue
        for p in sorted(d.iterdir()):
            if p.is_file() and p.name.endswith(".json"):
                found.setdefault(p.name, p)
            elif p.is_file() and p.name.endswith(".json.gz"):
                found.setdefault(p.name[:-3], p)
    return sorted(found.items())
