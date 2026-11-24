"""Portable repository path and JSON/gzip loader for `compute/` scripts."""
from __future__ import annotations

import gzip
import json
from pathlib import Path
from typing import Any

COMPUTE_DIR = Path(__file__).resolve().parent
REPO_ROOT = COMPUTE_DIR.parent
POLY_DIR = COMPUTE_DIR / "poly"
POLY_RESULTS_DIR = POLY_DIR / "results"
SEARCH_DIR = COMPUTE_DIR / "search"
SEARCH_RESULTS_DIR = SEARCH_DIR / "results"
CERT_DIR = REPO_ROOT / "certificates"


def load_json_auto(filename: str, primary_dir: Path | None = None) -> Any:
    """Load JSON (or transparent `.json.gz`) from `primary_dir` or `certificates/`."""
    search_dirs: list[Path] = []
    if primary_dir is not None:
        search_dirs.append(primary_dir)
    search_dirs.extend([
        POLY_RESULTS_DIR,
        SEARCH_RESULTS_DIR,
        CERT_DIR / "stage1",
        CERT_DIR / "phase2",
        CERT_DIR / "sec7",
        CERT_DIR / "phase3",
        CERT_DIR / "phase3" / "idx13_exact",
        CERT_DIR / "calibration",
    ])
    for d in search_dirs:
        p = d / filename
        if p.is_file():
            return json.loads(p.read_text(encoding="utf-8"))
        gz = d / f"{filename}.gz"
        if gz.is_file():
            with gzip.open(gz, "rt", encoding="utf-8") as f:
                return json.load(f)
    raise FileNotFoundError(f"Could not locate {filename!r} (or .gz) in compute/ or certificates/")
