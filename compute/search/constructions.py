"""Reconstruct and verify known maximal/record equiangular line systems (alpha = 1/5):
- n=48 in R^17: Netto triple system (GKMS16 Ex 5.10) & A_5^3 + A_1^4 (MSY26 Rem 6.2)
- n=57 in R^18: Greaves-Syatriadi-Yatsyna F1..F4 (arXiv:2104.04330),
                Lin-Munemasa-Taniguchi-Yoshino (A_9^2 + A_1, arXiv:2503.06377),
                Munemasa-Szollosi-Yoshino (A_5^3 + A_1^4, arXiv:2606.10421)
- n=72 in R^19: Asche's lines from Witt design S(5,8,24) (GKMS16 Ex 5.13)
"""

from __future__ import annotations
import re
from pathlib import Path
from typing import Dict, List, Tuple
import sympy as sp

from verify import verify_seidel_system, verify_vectors_gram, save_verified_matrix


BASE_DIR = Path(__file__).resolve().parent
REFS_DIR = BASE_DIR / "refs"
RESULTS_DIR = BASE_DIR / "results"


# ==============================================================================
# 1. Netto Triple System: n = 48 in R^17
# ==============================================================================
def build_netto_48() -> Tuple[List[List[int]], Dict]:
    """GKMS16 Example 5.10: Netto triple system on Z_19."""
    blocks = set()
    for i in range(3):
        p = pow(4, i, 19)
        for j in range(19):
            b = frozenset(((p + j) % 19, (7 * p + j) % 19, (11 * p + j) % 19))
            assert len(b) == 3
            blocks.add(b)
    assert len(blocks) == 57
    # Exclude blocks containing 0 (using 0-indexed instead of 1-indexed)
    filtered = sorted([sorted(b) for b in blocks if 0 not in b])
    assert len(filtered) == 48

    # v_B = 6 e_B + e_0 - e_X, norm^2 = 90, inner products in {-18, +18}
    vectors = []
    for b in filtered:
        v = [-1] * 19
        v[0] += 1  # = 0
        for idx in b:
            v[idx] += 6  # = 5
        vectors.append(v)

    S, info = verify_vectors_gram(vectors, norm_sq=90, allowed_ips=(-18, 18), d=17)
    return S, info


# ==============================================================================
# 2. Witt Design S(5,8,24) & Asche's 72 lines in R^19 (plus 276 in R^23)
# ==============================================================================
def build_golay_octads() -> List[frozenset]:
    """Construct the extended binary Golay code G_24 and return its 759 octads."""
    # Generator matrix [I_12 | A] where A has 0 on top-left, 1s on border,
    # and 11x11 circulant with 1s at 0 and non-quadratic residues mod 11.
    qr11 = {(x * x) % 11 for x in range(1, 11)}  # {1,3,4,5,9}
    nqr_or_0 = set(range(11)) - qr11             # {0,2,6,7,8,10}

    rows = []
    # Row 0: [e_0 | 0, 1, 1, ..., 1]
    r0 = [0] * 24
    r0[0] = 1
    for c in range(13, 24):
        r0[c] = 1
    rows.append(r0)
    # Rows 1..11
    for i in range(11):
        r = [0] * 24
        r[1 + i] = 1
        r[12] = 1
        for j in range(11):
            if ((j - i) % 11) in nqr_or_0:
                r[13 + j] = 1
        rows.append(r)

    # Generate all 4096 codewords
    octads = []
    weights = set()
    for mask in range(1 << 12):
        cw = [0] * 24
        for bit in range(12):
            if (mask >> bit) & 1:
                row = rows[bit]
                for k in range(24):
                    cw[k] ^= row[k]
        w = sum(cw)
        weights.add(w)
        if w == 8:
            octads.append(frozenset(k for k in range(24) if cw[k] == 1))

    assert weights == {0, 8, 12, 16, 24}, f"Bad Golay weights: {weights}"
    assert len(octads) == 759, f"Expected 759 octads, got {len(octads)}"
    return octads


def build_asche_72() -> Tuple[List[List[int]], Dict]:
    """GKMS16 Example 5.13 (Asche's lines): 72 lines in R^19 from S(5,8,24)."""
    octads = build_golay_octads()
    # Ground set {0..23} (corresponding to {1..24} in GKMS16)
    # Find B1, B2 not containing 0 with B1 & B2 == {1, 2}
    no0 = [b for b in octads if 0 not in b]
    pair = None
    for i, b1 in enumerate(no0):
        if 1 in b1 and 2 in b1:
            for b2 in no0[i + 1:]:
                if (b1 & b2) == frozenset({1, 2}):
                    pair = (b1, b2)
                    break
        if pair is not None:
            break
    assert pair is not None, "Could not find B1, B2 with B1 & B2 = {1,2} and 0 not in B1, B2"
    B1, B2 = pair

    # Vectors v_B = 4 e_B - 4 e_0 - e_X for 0 in B
    # Orthogonal to e_0 - e_1, e_0 - e_2  <=>  1 not in B and 2 not in B
    # Orthogonal to v_B1 and v_B2          <=>  |B1 & B| == 2 and |B2 & B| == 2
    selected = [
        b for b in octads
        if (0 in b) and (1 not in b) and (2 not in b)
        and len(b & B1) == 2 and len(b & B2) == 2
    ]
    assert len(selected) == 72, f"Expected 72 octads for Asche's lines, got {len(selected)}"

    vectors = []
    for b in selected:
        v = [-1] * 24
        for idx in b:
            v[idx] += 4
        v[0] -= 4
        vectors.append(v)

    # Note: for n=72, compute charpoly too!
    S, info = verify_vectors_gram(vectors, norm_sq=80, allowed_ips=(-16, 16), d=19, compute_charpoly=True)
    return S, info


# ==============================================================================
# 3. Greaves-Syatriadi-Yatsyna F1..F4 (arXiv:2104.04330): n = 57 in R^18
# ==============================================================================
def parse_gsy_matrices() -> List[Tuple[str, List[List[int]]]]:
    """Parse F1, F2, F3, F4 (18 x 57 integer matrices) from 2104.04330.tex."""
    tex = (REFS_DIR / "2104.04330" / "2104.04330.tex").read_text()
    blocks = re.findall(r"\\begin\{smallmatrix\}(.*?)\\end\{smallmatrix\}", tex, flags=re.S)
    assert len(blocks) == 4, f"Expected 4 smallmatrix blocks, got {len(blocks)}"
    out = []
    for idx, blk in enumerate(blocks, start=1):
        rows = []
        for raw_row in blk.strip().split(r"\cr"):
            raw_row = raw_row.strip()
            if not raw_row:
                continue
            tokens = [t.strip() for t in raw_row.split("&")]
            row = []
            for t in tokens:
                if t == "+":
                    row.append(1)
                elif t == "-":
                    row.append(-1)
                else:
                    row.append(int(t))
            assert len(row) == 57, f"F{idx} row len {len(row)} != 57"
            rows.append(row)
        assert len(rows) == 18, f"F{idx} num rows {len(rows)} != 18"
        # Transpose so each item is a 18-dim column vector
        cols = [[rows[r][c] for r in range(18)] for c in range(57)]
        out.append((f"GSY21_F{idx}", cols))
    return out


# ==============================================================================
# 4. Lin-Munemasa-Taniguchi-Yoshino (arXiv:2503.06377): A_9^2 + A_1 -> n = 57 in R^18
# ==============================================================================
def _edge_coloring_K10_from_1fact(matching_extra: List[Tuple[int, int]]) -> List[List[Tuple[int, int]]]:
    """Canonical 1-factorization of K_10 (vertices 0..9):
    F_k for k in 0..8 pairs (k, 9) and (k-t, k+t) mod 9 for t=1..4.
    Return Y_0..Y_9 where Y_i = F_i \\ M_extra for i < 9 and Y_9 = M_extra.
    """
    F = []
    for k in range(9):
        m = [(min(k, 9), max(k, 9))]
        for t in range(1, 5):
            a = (k - t) % 9
            b = (k + t) % 9
            m.append((min(a, b), max(a, b)))
        F.append(set(m))
    extra_set = set((min(a, b), max(a, b)) for a, b in matching_extra)
    Y = [sorted(f - extra_set) for f in F] + [sorted(extra_set)]
    # Verify partition of all 45 edges
    all_edges = [e for y in Y for e in y]
    assert len(all_edges) == 45 and len(set(all_edges)) == 45
    return Y


def build_a9a9a1_57(matching_extra: List[Tuple[int, int]] = None, empty_first: bool = False) -> Tuple[List[List[int]], Dict]:
    """Construct a 57-line system in R^18 from A_9 + A_9 + A_1 (arXiv:2503.06377).
    Embeds into Z^22 (10 + 10 + 2) via 2*gamma - r (orthogonal to (1^10,0,0), (0,1^10,0), (0,0,1,1), r).
    Wait: r = (0, 0, 2*alpha_1) = (0, 0, 1, -1).
    Let's work in scaled integer coordinates (multiply by 10):
      10*(2*gamma - r) has integer entries!
      Let's check:
      2*v_5(I) - r = (1 - 2*sum_{i in I} e_i, 0, 0) (in R^10 x R^10 x R^2),
      Wait: 2*alpha_1 - 2*alpha_1 = 0!
      Yes! 2*(1/2, -1/2) - (1, -1) = (0, 0)!
      And for v_1(i,j,k):
      2*v_1(i,j,k) - r = (1/5 * 1 - 2*e_i, 2/5 * 1 - 2*e_j - 2*e_k, 0)!
      Multiply by 5 to make ALL coordinates integers in Z^20:
      w_5(I) = (5 * 1 - 10 * sum_{i in I} e_i, 0) in Z^20
      w_1(i,j,k) = (1 - 10 * e_i, 2 - 10 * e_j - 10 * e_k) in Z^20!
      Let's check norms and inner products!
      ||w_5(I)||^2 = 5*(5^2) + 5*((-5)^2) = 250!
      ||w_1(i,j,k)||^2 = (9*(-9)? wait: 1 coord is -9, 9 coords are +1 => 81+9=90) + (2 coords are -8, 8 coords are +2 => 2*64 + 8*4 = 128+32=160) => 90 + 160 = 250!
      Pairwise inner products of w's MUST be in {-50, +50} (ratio +-1/5)!
    """
    # I_0 from Definition 5.2 (0-indexed: subtract 1 from 1..10)
    I_0_one_based = [
        [2, 3, 4, 5, 7], [2, 3, 4, 6, 8], [2, 3, 4, 9, 10],
        [1, 3, 4, 8, 10], [1, 3, 4, 5, 9], [1, 3, 4, 6, 7],
        [1, 2, 4, 7, 9], [1, 2, 4, 6, 10], [1, 2, 4, 5, 8],
        [1, 2, 3, 5, 6], [1, 2, 3, 8, 9], [1, 2, 3, 7, 10],
    ]
    I_0 = [[x - 1 for x in blk] for blk in I_0_one_based]

    if matching_extra is None:
        matching_extra = [(0, 1), (2, 3), (4, 5), (6, 7), (8, 9)]
    Y = _edge_coloring_K10_from_1fact(matching_extra)
    if empty_first:
        Y = [Y[-1]] + Y[:-1]

    vectors = []
    for blk in I_0:
        v = [5] * 10 + [0] * 10
        for idx in blk:
            v[idx] = -5
        vectors.append(v)

    for i in range(10):
        for j, k in Y[i]:
            v = [1] * 10 + [2] * 10
            v[i] = -9
            v[10 + j] = -8
            v[10 + k] = -8
            vectors.append(v)

    assert len(vectors) == 57
    S, info = verify_vectors_gram(vectors, norm_sq=250, allowed_ips=(-50, 50), d=18)
    return S, info


# ==============================================================================
# 5. Munemasa-Szollosi-Yoshino (arXiv:2606.10421): A_5^3 + A_1^4 -> n=57 (R^18) & n=48 (R^17)
# ==============================================================================
def _latin_square_6_cyclic() -> List[List[int]]:
    return [[(i + j) % 6 for j in range(6)] for i in range(6)]


def _latin_square_6_alt() -> List[List[int]]:
    # Non-cyclic main class Latin square of order 6
    return [
        [0, 1, 2, 3, 4, 5],
        [1, 0, 3, 2, 5, 4],
        [2, 4, 0, 5, 1, 3],
        [3, 5, 4, 0, 2, 1],
        [4, 2, 5, 1, 3, 0],
        [5, 3, 1, 4, 0, 2],
    ]


def build_a5_3_a1_4(
    latin: List[List[int]] = None,
    clique_types: Tuple[int, int, int] = (1, 1, 1),
    for_48_in_17: bool = False,
) -> Tuple[List[List[int]], Dict]:
    """Construct 57 lines in R^18 (or 48 lines in R^17) from A_5^3 + A_1^4 (arXiv:2606.10421).
    Let's embed 2*x - r in integer coordinates (multiply by 6 so all entries are integers!):
      Recall alpha_5^{(i)} = 1/6 * 1 - e_i, alpha_1 = (1/2, -1/2), r = (0,0,0,0,0,0, 2*alpha_1).
      Note 2*alpha_1 - 2*alpha_1 = 0 in the 7th block (A_1), and in the other 3 A_1 blocks (blocks 4,5,6):
        2 * (eps * alpha_1) = eps * (1, -1) -> drop the redundant second coord, or keep in Z^24 (3*6 + 3*2)!
      Wait: in Z^24 (first 18 coords = three A_5 blocks, next 6 coords = three A_1 blocks),
      multiply (2*x - r) by 3:
      - x_{i1, i2, i3}: 3 * 2 * (alpha_5^{(i1)}, alpha_5^{(i2)}, alpha_5^{(i3)}, 0,0,0)
        Wait: 6 * alpha_5^{(i)} = 1 - 6 * e_i -> entries in {+1, -5}.
        Norm^2 = 3 * (5 * 1^2 + 1 * (-5)^2) = 3 * 30 = 90!
      - x^{(1)}_{I, eps1, eps2}: alpha_I = 1/2 * 1 - sum_{i in I} e_i -> 6 * alpha_I has +3 on I^c and -3 on I.
        Norm^2 in first A_5 block = 6 * 3^2 = 54.
        In A_1 blocks 5 and 6: 3 * 2 * eps * (1/2, -1/2) = eps * (3, -3). Each A_1 block contributes 3^2 + 3^2 = 18.
        Total norm^2 = 54 + 18 + 18 = 90!
      All vectors in Z^24 have norm^2 = 90, and inner products in {-18, +18}!
    """
    if latin is None:
        latin = _latin_square_6_cyclic()

    # Pasch 4-set (0-indexed: {0,2,4}, {0,3,5}, {1,2,5}, {1,3,4})
    pasch = [
        (frozenset({0, 2, 4}), -1),
        (frozenset({0, 3, 5}), -1),
        (frozenset({1, 2, 5}), -1),
        (frozenset({1, 3, 4}), -1),
    ]
    c1_extra = [
        (frozenset({0, 1, 2}), 1),
        (frozenset({2, 3, 4}), 1),
        (frozenset({4, 5, 0}), 1),
    ]
    c2_extra = [
        (frozenset({0, 1, 5}), 1),
        (frozenset({2, 3, 1}), 1),
        (frozenset({4, 5, 3}), 1),
    ]

    def get_clique(ct: int):
        if for_48_in_17:
            return pasch
        if ct == 1:
            return pasch + c1_extra
        elif ct == 2:
            return pasch + c2_extra
        elif ct == -1:
            return [(s, -e) for s, e in pasch + c1_extra]
        elif ct == -2:
            return [(s, -e) for s, e in pasch + c2_extra]
        raise ValueError(ct)

    vectors = []
    # omega_0: 36 vectors
    for i1 in range(6):
        for i2 in range(6):
            i3 = latin[i1][i2]
            v = [1] * 18 + [0] * 6
            v[i1] = -5
            v[6 + i2] = -5
            v[12 + i3] = -5
            vectors.append(v)

    # omega_1, omega_2, omega_3
    # Note A_1 coordinates (blocks 4,5,6 -> indices 18..23):
    # beta_1: (0, eps1*alpha_1, eps2*alpha_1) -> indices (20,21) and (22,23)
    # beta_2: (eps2*alpha_1, 0, eps1*alpha_1) -> indices (18,19) and (22,23)
    # beta_3: (eps1*alpha_1, eps2*alpha_1, 0) -> indices (18,19) and (20,21)
    a1_slots = [
        (20, 22),  # i=1: eps1 at slot 5 (20,21), eps2 at slot 6 (22,23)
        (22, 18),  # i=2: eps1 at slot 6 (22,23), eps2 at slot 4 (18,19)
        (18, 20),  # i=3: eps1 at slot 4 (18,19), eps2 at slot 5 (20,21)
    ]
    for block_idx in range(3):
        clique = get_clique(clique_types[block_idx])
        s1, s2 = a1_slots[block_idx]
        for subset, eps1 in clique:
            eps2 = 1
            v = [0] * 24
            base = 6 * block_idx
            for k in range(6):
                v[base + k] = -3 if k in subset else 3
            v[s1] = 3 * eps1
            v[s1 + 1] = -3 * eps1
            v[s2] = 3 * eps2
            v[s2 + 1] = -3 * eps2
            vectors.append(v)

    d = 17 if for_48_in_17 else 18
    S, info = verify_vectors_gram(vectors, norm_sq=90, allowed_ips=(-18, 18), d=d)
    return S, info


def run_calibration() -> None:
    print("=== CALIBRATION: Known Optimal/Record Equiangular Line Systems ===")
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)

    # 1. Netto 48 in R^17
    S_netto, info_netto = build_netto_48()
    print(f"[R^17, n=48] Netto triple system: rank={info_netto['rank']}, PSD={info_netto['psd_verified']}, charpoly={info_netto['charpoly_str']}")
    save_verified_matrix(RESULTS_DIR / "cal_17_48_netto.json", "Netto_17_48", S_netto, info_netto, {"source": "GKMS16 Ex 5.10"})

    # 2. A_5^3 + A_1^4 48 in R^17
    S_48_a5, info_48_a5 = build_a5_3_a1_4(for_48_in_17=True)
    print(f"[R^17, n=48] MSY26 A5^3+A1^4: rank={info_48_a5['rank']}, PSD={info_48_a5['psd_verified']}, charpoly={info_48_a5['charpoly_str']}")
    save_verified_matrix(RESULTS_DIR / "cal_17_48_a5_3_a1_4.json", "MSY26_17_48", S_48_a5, info_48_a5, {"source": "arXiv:2606.10421 Rem 6.2"})

    # 3. GSY21 F1..F4 (57 in R^18)
    for name, cols in parse_gsy_matrices():
        S, info = verify_vectors_gram(cols, norm_sq=10, allowed_ips=(-2, 2), d=18)
        print(f"[R^18, n=57] {name}: rank={info['rank']}, PSD={info['psd_verified']}, charpoly={info['charpoly_str']}")
        save_verified_matrix(RESULTS_DIR / f"cal_18_57_{name.lower()}.json", name, S, info, {"source": "arXiv:2104.04330"})

    # 4. LMTY25 A_9^2 + A_1 (57 in R^18): generic matching + both 6-eigenvalue cyclic choices
    S_a9, info_a9 = build_a9a9a1_57()
    print(f"[R^18, n=57] LMTY25 A9^2+A1: rank={info_a9['rank']}, PSD={info_a9['psd_verified']}, charpoly={info_a9['charpoly_str']}")
    save_verified_matrix(RESULTS_DIR / "cal_18_57_a9_2_a1.json", "LMTY25_18_57", S_a9, info_a9, {"source": "arXiv:2503.06377"})

    S_a9_6l, info_a9_6l = build_a9a9a1_57(matching_extra=[])
    print(f"[R^18, n=57] LMTY25 6ev_last: rank={info_a9_6l['rank']}, PSD={info_a9_6l['psd_verified']}, charpoly={info_a9_6l['charpoly_str']}")
    save_verified_matrix(RESULTS_DIR / "cal_18_57_a9_2_a1_6ev_last.json", "LMTY25_6ev_last", S_a9_6l, info_a9_6l, {"source": "arXiv:2503.06377 Ex 7.1"})

    S_a9_6f, info_a9_6f = build_a9a9a1_57(matching_extra=[], empty_first=True)
    print(f"[R^18, n=57] LMTY25 6ev_first: rank={info_a9_6f['rank']}, PSD={info_a9_6f['psd_verified']}, charpoly={info_a9_6f['charpoly_str']}")
    save_verified_matrix(RESULTS_DIR / "cal_18_57_a9_2_a1_6ev_first.json", "LMTY25_6ev_first", S_a9_6f, info_a9_6f, {"source": "arXiv:2503.06377 Ex 7.1"})

    # 5. MSY26 A_5^3 + A_1^4 (57 in R^18, both spectral types)
    for tag, cts in [("spec1_111", (1, 1, 1)), ("spec2_11m1", (1, 1, -1))]:
        S_a5, info_a5 = build_a5_3_a1_4(clique_types=cts)
        print(f"[R^18, n=57] MSY26 {tag}: rank={info_a5['rank']}, PSD={info_a5['psd_verified']}, charpoly={info_a5['charpoly_str']}")
        save_verified_matrix(RESULTS_DIR / f"cal_18_57_a5_3_a1_4_{tag}.json", f"MSY26_{tag}", S_a5, info_a5, {"source": "arXiv:2606.10421", "clique_types": list(cts)})

    # 6. Asche's 72 in R^19
    S_72, info_72 = build_asche_72()
    print(f"[R^19, n=72] Asche's lines: rank={info_72['rank']}, PSD={info_72['psd_verified']}, charpoly={info_72['charpoly_str']}")
    save_verified_matrix(RESULTS_DIR / "cal_19_72_asche.json", "Asche_19_72", S_72, info_72, {"source": "GKMS16 Ex 5.13"})


if __name__ == "__main__":
    run_calibration()
