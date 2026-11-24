# Equiangular Lines in Dimensions 18 and 19

[![Verify Lean 4 Proofs & Exact Certificates](https://github.com/Mehardeep-Singh-GG/equiangular-lines-18-19/actions/workflows/verify.yml/badge.svg)](https://github.com/Mehardeep-Singh-GG/equiangular-lines-18-19/actions/workflows/verify.yml)
![Lean 4](https://img.shields.io/badge/Lean-v4.36.0-blue)
![Axioms](https://img.shields.io/badge/axioms-standard%20only%20(127%20decls)-brightgreen)
![Certificates](https://img.shields.io/badge/certificates-56%2F56%20exact%20QQ%2FZZ-success)
![License](https://img.shields.io/badge/license-MIT%20%2B%20CC--BY--4.0-lightgrey)

**Author:** Mehardeep Singh (`Sri Chaitanya Educational Institutions`, India)  
**Contact:** `mehardeep.sim@gmail.com`  
**Repository:** https://github.com/Mehardeep-Singh-GG/equiangular-lines-18-19 (`v1.0.0`)

This repository contains the manuscripts, Lean 4 formalization, zero-floating-point C++20/Python verification programs, and frozen 56-file exact integer/rational certificate archive establishing upper bounds on $N(d)$, the maximum cardinality of a system of equiangular lines in $\mathbb{R}^d$:

- **Dimension 18 (Unconditional):** $N(18) \le 58$, narrowing $N(18)$ to $\{57, 58\}$. No configuration of $59$ equiangular lines exists in $\mathbb{R}^{18}$.
- **Dimension 19 (Exact Equivalence & Bound):** Unconditionally, a system of $74$ equiangular lines exists in $\mathbb{R}^{19}$ if and only if there exists a strongly regular graph $\mathrm{SRG}(75, 32, 10, 16)$. Combined with the theorem of Azarija and Marc (*Linear Algebra Appl.* **557**, 2018, 62–83) ruling out $\mathrm{SRG}(75, 32, 10, 16)$, this proves $N(19) \le 73$ and narrows $N(19)$ to $\{72, 73\}$.
- **Open Boundary Cases:** $(18, 58)$ and $(19, 73)$ remain open (explicit bounded constructive and local-neighborhood searches reported alongside the proofs do not establish nonexistence).

---

## Quick Verification

### 1. Verify the 56-file exact certificate archive (< 5 seconds)
Requires Python 3.10+ (standard library only, strictly read-only on `certificates/`):

```bash
python3 certificates/verify_all.py
```

This verifies every decompressed certificate stream bit-for-bit against the canonical manifest [`certificates/SHA256SUMS.txt`](certificates/SHA256SUMS.txt) (manifest SHA-256: `d9c57ae07182ef861e53093990aa8542355a3c750098dfe6cde958a64a046d33`), checks path hygiene (`0` local path leaks), validates all polynomial enumerations, exact integer/rational Farkas duals (including all $54{,}427$ rational Farkas duals for candidate $p_{13}$), Eulerian/Galois certificates, higher-order spectral eliminations, and exact $\mathbb{Q}$-pivoted $LDL^T$ PSD verification of all $12$ calibrated extremal Seidel matrices.

*(Five large JSON certificates are stored as `.json.gz` so every file stays well under GitHub's 100 MB limit while preserving exact decompressed hashes; `verify_all.py` reads `.json` and `.json.gz` transparently. Run `python3 certificates/unpack_gz.py` only if you need raw uncompressed `.json` files on disk for external scripts.)*

### 2. Run the Lean 4 formal verification & 127-declaration axiom audit
Requires [elan](https://github.com/leanprover/elan) (pinned to `leanprover/lean4:v4.36.0` and Mathlib `v4.36.0` via [`lean/lean-toolchain`](lean/lean-toolchain) and [`lean/lake-manifest.json`](lean/lake-manifest.json)):

```bash
cd lean
lake exe cache get
lake build
lake env lean EquiangularLines/Audit.lean
```

Every theorem verified by `Audit.lean` (`127` exported declarations across `20` `.lean` files, `20,765` lines) uses zero `sorry`, zero `native_decide`, zero custom axioms, and depends strictly on standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`)—including pure-kernel `by decide` verification of all `147/147` one-vertex Farkas certificates for $(19, 74)$ across `Certs19_74A/B/C.lean`.

### 3. Build C++20 enumerators and run Python reproduction / audits
```bash
pip install -r requirements.txt
make -C compute core
```

Independent clean-room verification scripts live in `audit/` (sharing zero source code or imports with `compute/`).

---

## Repository Layout

| Path | Contents |
|---|---|
| `papers/mrl/` | Short research letter (`main.tex`, `refs.bib`, compiled `main.pdf`, 13 pp.) |
| `papers/full/` | Full archival monograph with Appendices A–D (`main.tex`, `refs.bib`, compiled `main.pdf`, 51 pp.) |
| `lean/` | Lean 4 formalization (`lean/EquiangularLines/`, `Audit.lean`, `Main.lean`, `20,765` lines, `127` audited declarations) |
| `certificates/` | Frozen 56-file exact certificate archive (`stage1/`, `phase2/`, `sec7/`, `phase3/`, `phase3/idx13_exact/`, `calibration/`), canonical `SHA256SUMS.txt`, and `verify_all.py` |
| `compute/poly/` | Zero-float C++20 polynomial enumerators (`enum_polys_v4.cpp`, `stage2_deck_par.cpp`, `stage2_deck_odd_v3.cpp`), Python rational Farkas/$K^\times$/Galois provers, and `idx13_exact/` |
| `compute/search/` | Calibration matrix constructors and bounded constructive / local-neighborhood searches for $(18, 58)$ and $(19, 73)$ |
| `audit/` | Independent C++20 and exact SymPy/`Fraction` verification suite (`verify_polys.py`, `verify_farkas.py`, `verify_phase2_certs.py`, `verify_sec7_certs.py`, `verify_phase3_18_59_endgame.py`, `verify_phase3_19_74_idx13.py`, etc.) |
| `.github/workflows/verify.yml` | GitHub Actions CI verifying `SHA256SUMS.txt`, `certificates/verify_all.py`, C++20 builds, and the full 127-declaration Lean 4 axiom audit |

---

## Mathematical Results & Lean 4 Scope Boundary

Two main algebraic obstructions drive the elimination alongside exact vertex-deletion interlacing and De Caen–Jacobi resolvent analysis:
1. **Odd-order mod-$2^{n+1}$ Pfaffian congruence:** For any symmetric Seidel matrix $S$ of odd order $n \ge 1$,
   $$\frac{1}{2^{n-1}}\chi_S(2z - 1) \equiv (2z - n)\,Q_0(z)^2 \pmod{4}$$
   for a monic polynomial $Q_0(z) \in \mathbb{Z}[z]$ of degree $(n-1)/2$.
2. **Generalized Galois orthogonality & Eulerian switching gauge:** Strictly unique odd-$n$ Eulerian gauge $S_\varepsilon \mathbf{1} \equiv (n-1)\mathbf{1} \pmod 4$ and $\binom{e+1}{2}$ rational trace-orthogonality constraints over degree-$e$ simple number-field factors.

For complete transparency, `EquiangularLines/Main.lean` separates:
- **Unconditionally formalized in Lean 4:** Angle forcing $\alpha = 1/5$, spectral factorization, mod-$2^{n+1}$ Pfaffian theorem, multiplicity bounds, odd-$n$ Eulerian gauge, generalized Galois orthogonality, multiplicity-preserving submatrix extraction, bidirectional equivalence $p_{136} \Leftrightarrow \mathrm{SRG}(75, 32, 10, 16)$, spectral refutations (`idx47_eliminated`, `idx861_eliminated`, `idx488_rank_obstruction`), resolvent pole cancellation (`idx13_pole_cancellation_at_15`), Farkas soundness, and in-kernel `by decide` verification of all `147/147` one-vertex Farkas certificates for $(19, 74)$.
- **Explicit hypotheses (`Main.lean`):** Nonexistence of $\mathrm{SRG}(75, 32, 10, 16)$ (Azarija–Marc 2018, invoked only for $(19, 74)$) and finite-census exhaustion `hexh` covering the externally verified exact C++/Python enumerations and certificates in `certificates/`.

---

## Citing This Work

Please see [`CITATION.cff`](CITATION.cff) or use the GitHub *"Cite this repository"* button.

```bibtex
@misc{Singh2026Equiangular1819,
  author       = {Singh, Mehardeep},
  title        = {Upper bounds on real equiangular lines in dimensions 18 and 19: 2-adic Pfaffian congruences, Galois orthogonality, and exact spectral certificates},
  year         = {2026},
  howpublished = {GitHub release v1.0.0},
  url          = {https://github.com/Mehardeep-Singh-GG/equiangular-lines-18-19}
}
```
