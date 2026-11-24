#!/usr/bin/env python3
"""Decompress `.json.gz` bundles in `certificates/` for standalone replay/audit scripts.

Note: `certificates/verify_all.py` verifies both `.json` and `.json.gz` directly
in memory without requiring decompression. Only run this helper if external scripts
require uncompressed `.json` files on disk, and remove/re-compress afterwards if
maintaining strict read-only `.json.gz` layout.
"""
from __future__ import annotations

import gzip
import shutil
from pathlib import Path

CERT_DIR = Path(__file__).resolve().parent


def main() -> int:
    gz_files = sorted(CERT_DIR.rglob("*.json.gz"))
    if not gz_files:
        print("No .json.gz files found; all certificates are already uncompressed.")
        return 0
    for gz_path in gz_files:
        raw_path = gz_path.with_suffix("")
        print(f"Unpacking {gz_path.relative_to(CERT_DIR)} -> {raw_path.relative_to(CERT_DIR)} ...", flush=True)
        with gzip.open(gz_path, "rb") as src, raw_path.open("wb") as dst:
            shutil.copyfileobj(src, dst)
        gz_path.unlink()
    print(f"Unpacked {len(gz_files)} archive(s). Run `python3 certificates/verify_all.py` to verify SHA256SUMS.txt.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
