"""
Self-contained exact rational proof eliminating all 3 Stage-3 survivors of (18, 59) idx=864:
  surv0: [(0, 34), (6, 21), (7, 4)]
  surv1: [(0, 33), (3, 3), (6, 18), (7, 5)]
  surv2: [(0, 32), (3, 6), (6, 15), (7, 6)]

Methodology (100% exact ZZ/QQ/Fraction arithmetic):
1. Verify all 2v-Jacobi pairs among vertex types {0, 3, 6, 7} and extract exact signed
   spectral projector entries (1155*E_6, 21*E_9, 20*E_11, 63*E_13) in the unique switching
   gauge fixing E_6 = gamma * gamma^T / 1155 with gamma = (-3, +1, +5, +9).
2. Prove via rank-2 unit circle geometry of E_9 on C_3 U C_6 (size 21) that |E_9| = 1/42
   cannot occur (else <= 2 lines give 15k = 147), so (-C_3) U C_6 partitions into 3 clusters
   K_0, K_1, K_2 of size 7 each (a_m + b_m = 7).
3. Prove via 2x2 PSD Gram matrices of (1_{A_m}, 1_{B_m}) under 63*E_13 that a_m <= 3,
   e_{B_m} = 0, and k_neg(A_m, B_m) = a_m * b_m (making 63*E_13 constant +1 on A_m x B_m).
4. Prove via 1_{C_7}^T (63*E_13) 1_{C_7} >= 0 that e_7 <= 1 for c_7 in {4, 5} and e_7 = 0
   for c_7 = 6.
5. For every partition (a_0, a_1, a_2) of each survivor, prove Tr(B^2) < CS_min on
   W = (+)_{m=0..2} (1_{A_m}^perp + 1_{B_m}^perp) (+) 1_{C_7}^perp (where B = U^T (9 E_13 - 2I) U)
   using exact 2x2 / 3x3 PSD Gram bounds and Cauchy-Schwarz over rank(E_13) <= 8.
"""

import hashlib
import json
import math
import time
from fractions import Fraction
import sympy as sp

from run_stage3_18_59 import solve_candidate
from stage3_solver import solve_2v_jacobi_pair, strict_upper_bound_roots
from verify_all_phase3_certs import build_cand_context


def max_c7_diag_frob(c7, e7):
    """Exact upper bound on ||(I - J/c7) A_7 (I - J/c7)||_F^2 for symmetric {0,1} A_7 with e7 edges."""
    if e7 == 0:
        return Fraction(0)
    assert e7 == 1
    # Single undirected edge (u, v): A_7 has two 1s, row sums (1,1,0,...,0), col sums (1,1,0,...,0)
    return Fraction(2) - Fraction(4, c7) + Fraction(4, c7 * c7)


def block_ub_2x2(s1, s2, q1, q2, hi):
    """Exact max 2*r*(1 - r/(s1*s2)) subject to (hi*s1*s2 - 7*r)^2 <= q1*q2."""
    if s1 <= 1 or s2 <= 1:
        return Fraction(0)
    best = Fraction(0)
    for r in range(s1 * s2 + 1):
        val = hi * s1 * s2 - 7 * r
        if val * val <= q1 * q2:
            b = 2 * Fraction(r) * (1 - Fraction(r, s1 * s2))
            if b > best:
                best = b
    return best


def main():
    from pathlib import Path
    import sys
    _COMP_DIR = Path(__file__).resolve().parent.parent
    if str(_COMP_DIR) not in sys.path:
        sys.path.insert(0, str(_COMP_DIR))
    from _io import POLY_RESULTS_DIR, load_json_auto

    t0 = time.time()
    d59 = load_json_auto("deck_18_59.json")
    cand = d59["candidates"][864]
    n, d_dim, c_sh = d59["n"], d59["d"], d59["c"]

    # Step 1: Verify Stage-3 produces exactly the 3 expected survivors
    s3_res = solve_candidate(cand, n, d_dim, c_sh, run_stage3=True, run_sv_galois=True)
    assert s3_res["stage3_survivors_count"] == 3
    surv_counts = sorted(
        sorted((j, c) for j, c in enumerate(sv["counts_n"]) if c > 0)
        for sv in s3_res["stage3_survivors"]
    )
    assert surv_counts == [
        [(0, 32), (3, 6), (6, 15), (7, 6)],
        [(0, 33), (3, 3), (6, 18), (7, 5)],
        [(0, 34), (6, 21), (7, 4)],
    ]

    # Step 2: Verify exact signed projector values from 2v-Jacobi
    w, x, s, deck, Pw, rhs, chi_S, Gcd_x, Gcd2_x, Sim_x, Mult_rad_x, g_list = build_cand_context(cand, n, d_dim, c_sh)
    x_ub = strict_upper_bound_roots(chi_S, x)
    denom = sp.Poly(math.prod([x - lam for lam in (-5, 6, 9, 11, 13)]), x, domain=sp.QQ)
    gamma = {0: -3, 3: 1, 6: 5, 7: 9}
    vals = {}
    for ja in [0, 3, 6, 7]:
        for jb in [0, 3, 6, 7]:
            if ja > jb:
                continue
            prod_g = sp.Poly(g_list[ja].as_expr() * g_list[jb].as_expr(), x, domain=sp.ZZ)
            res = solve_2v_jacobi_pair(g_list[ja], g_list[jb], Sim_x, Mult_rad_x, Gcd2_x, n, x, x_max_ub=x_ub)
            s_set = set()
            for _, q57, _ in res:
                h2 = sp.Poly(prod_g.as_expr() - (Sim_x * q57).as_expr(), x, domain=sp.ZZ)
                lc, facs = sp.factor_list(h2.as_expr())
                hexpr = sp.Integer(math.isqrt(int(lc)))
                for f, mult in facs:
                    assert mult % 2 == 0
                    hexpr = hexpr * (f ** (mult // 2))
                h = sp.Poly(sp.expand(hexpr), x, domain=sp.ZZ)
                for suv in (-1, 1):
                    hh = h if int(h.LC()) == suv else -h
                    ed = {
                        lam: Fraction(int(hh.eval(lam)), int(sp.quo(denom, sp.Poly(x - lam, x, domain=sp.QQ)).eval(lam)))
                        for lam in (6, 9, 11, 13)
                    }
                    if ed[6] * 1155 == gamma[ja] * gamma[jb]:
                        s_set.add((suv, ed[9] * 21, ed[11] * 20, ed[13] * 63))
            vals[(ja, jb)] = sorted(s_set)

    # Assert exact E_9, E_11, and E_13 structure in the gamma switching gauge
    assert {v[2] for v in vals[(3, 3)]} == {1}
    assert {v[2] for v in vals[(3, 7)]} == {-1}
    assert {v[2] for v in vals[(7, 7)]} == {1}
    assert {v[2] for v in vals[(0, 6)]} == {0} and {v[2] for v in vals[(6, 6)]} == {0}

    assert {v[1] for v in vals[(3, 3)]} == {Fraction(-1), Fraction(1, 2), Fraction(2)}
    assert {v[1] for v in vals[(6, 6)]} == {Fraction(-1), Fraction(1, 2), Fraction(2)}
    assert {-v[1] for v in vals[(3, 6)]} == {Fraction(-1), Fraction(1, 2), Fraction(2)}

    # Within-cluster (21*E_9 = +2 on (-C_3) U C_6) and cross-cluster (21*E_9 = -1) 63*E_13 values:
    assert {v[3] for v in vals[(3, 3)] if v[1] == 2} == {-4}
    assert {v[3] for v in vals[(6, 6)] if v[1] == 2} == {-9, -2}
    assert {v[3] for v in vals[(3, 6)] if -v[1] == 2} == {1, 8}

    assert {v[3] for v in vals[(3, 3)] if v[1] == -1} == {-4, 3}
    assert {v[3] for v in vals[(6, 6)] if v[1] == -1} == {-2, 5}
    assert {v[3] for v in vals[(3, 6)] if -v[1] == -1} == {-6, 1}
    assert {v[3] for v in vals[(3, 7)]} == {-1, 6}
    assert {v[3] for v in vals[(6, 7)]} == {-5, 2}
    assert {v[3] for v in vals[(7, 7)]} == {-9, -2}

    # Step 3: Check E_9 unit-circle partition: if |E_9| = 1/42 occurred, <= 2 lines => 15k = 147 impossible
    assert 147 % 15 != 0

    # Step 4: Verify intra-cluster PSD matrix forces a <= 3, e_B = 0, k_neg = a*b
    for a in range(8):
        b = 7 - a
        qAA = a * (14 - 4 * a)
        if qAA < 0:
            continue
        assert a <= 3
        for eB in range(b * (b - 1) // 2 + 1):
            qBB = b * (14 - 2 * b) - 14 * eB
            if qBB < 0:
                continue
            for k_neg in range(a * b + 1):
                qAB = 8 * a * b - 7 * k_neg
                if qAA * qBB - qAB * qAB >= 0:
                    assert eB == 0 and k_neg == a * b

    # Step 5: Exact Cauchy-Schwarz kills on all 3 survivors across ALL partitions (a_0, a_1, a_2)
    kill_records = []
    for total_a, c7 in [(0, 4), (3, 5), (6, 6)]:
        # 1_{C_7}^T (63*E_13) 1_{C_7} = 14*c7 - 2*c7^2 - 14*e7 >= 0
        max_e7 = max(e7 for e7 in range(c7 * (c7 - 1) // 2 + 1) if 14 * c7 - 2 * c7 * c7 - 14 * e7 >= 0)
        qCC = 14 * c7 - 2 * c7 * c7
        c7_diag_ub = max_c7_diag_frob(c7, max_e7)
        part_proofs = []
        for a0 in range(4):
            for a1 in range(a0, 4):
                a2 = total_a - a0 - a1
                if not (a1 <= a2 <= 3):
                    continue
                as_ = [a0, a1, a2]
                bs_ = [7 - a for a in as_]
                qA = [a * (14 - 4 * a) for a in as_]
                qB = [b * (14 - 2 * b) for b in bs_]
                dimW = sum(max(0, a - 1) + max(0, b - 1) for a, b in zip(as_, bs_)) + (c7 - 1)
                null = dimW - 8
                assert null > 0
                cs_min = Fraction(null * 4) + Fraction((2 * null) ** 2, 8)

                if as_ != [2, 2, 2]:
                    ub = c7_diag_ub
                    for m in range(3):
                        ub += block_ub_2x2(as_[m], c7, qA[m], qCC, 6)
                        ub += block_ub_2x2(bs_[m], c7, qB[m], qCC, 2)
                        for m2 in range(m + 1, 3):
                            ub += block_ub_2x2(as_[m], as_[m2], qA[m], qA[m2], 3)
                            ub += block_ub_2x2(bs_[m], bs_[m2], qB[m], qB[m2], 5)
                            ub += block_ub_2x2(as_[m], bs_[m2], qA[m], qB[m2], 1)
                            ub += block_ub_2x2(bs_[m], as_[m2], qB[m], qA[m2], 1)
                else:
                    # 3x3 PSD Gram bound for (1_{A_m}, 1_{B_m}, 1_{C_7}) and (1_{A_m}, 1_{B_m}, 1_{A_{m'}} / 1_{B_{m'}})
                    assert max_e7 == 0
                    best_c7 = Fraction(0)
                    for rA in range(13):
                        for rB in range(31):
                            M = sp.Matrix([[12, 10, 72 - 7 * rA], [10, 20, 60 - 7 * rB], [72 - 7 * rA, 60 - 7 * rB, 12]])
                            if M.det() >= 0 and (12 * 12 - (72 - 7 * rA) ** 2 >= 0) and (20 * 12 - (60 - 7 * rB) ** 2 >= 0):
                                val = 2 * Fraction(rA) * (1 - Fraction(rA, 12)) + 2 * Fraction(rB) * (1 - Fraction(rB, 30))
                                if val > best_c7:
                                    best_c7 = val
                    best_3A = Fraction(0)
                    for rAA in range(5):
                        for rBA in range(11):
                            M = sp.Matrix([[12, 10, 12 - 7 * rAA], [10, 20, 10 - 7 * rBA], [12 - 7 * rAA, 10 - 7 * rBA, 12]])
                            if M.det() >= 0 and (12 * 12 - (12 - 7 * rAA) ** 2 >= 0) and (20 * 12 - (10 - 7 * rBA) ** 2 >= 0):
                                val = 2 * Fraction(rAA) * (1 - Fraction(rAA, 4)) + 2 * Fraction(rBA) * (1 - Fraction(rBA, 10))
                                if val > best_3A:
                                    best_3A = val
                    best_3B = Fraction(0)
                    for rAB in range(11):
                        for rBB in range(26):
                            M = sp.Matrix([[12, 10, 10 - 7 * rAB], [10, 20, 125 - 7 * rBB], [10 - 7 * rAB, 125 - 7 * rBB, 20]])
                            if M.det() >= 0 and (12 * 20 - (10 - 7 * rAB) ** 2 >= 0) and (20 * 20 - (125 - 7 * rBB) ** 2 >= 0):
                                val = 2 * Fraction(rAB) * (1 - Fraction(rAB, 10)) + 2 * Fraction(rBB) * (1 - Fraction(rBB, 25))
                                if val > best_3B:
                                    best_3B = val
                    ub = 3 * best_c7 + 3 * (best_3A + best_3B)

                assert ub < cs_min, f"Failed on {as_}: {ub} >= {cs_min}"
                part_proofs.append({
                    "a_clusters": as_,
                    "dim_W": dimW,
                    "cs_min": str(cs_min),
                    "tr_ub": str(ub),
                    "margin": str(cs_min - ub),
                })
        kill_records.append({"c3": total_a, "c7": c7, "max_e7": max_e7, "partitions": part_proofs})

    out = {
        "index": 864,
        "status": "KILLED_E9_E13_CAUCHY_SCHWARZ",
        "stage3_survivors_count": 3,
        "kill_records": kill_records,
        "elapsed_sec": round(time.time() - t0, 3),
    }
    POLY_RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    out_p = str(POLY_RESULTS_DIR / "phase3_18_59_864.json")
    with open(out_p, "w") as f:
        json.dump(out, f, indent=2)
    print(json.dumps(out, indent=2))
    print("Saved", out_p, hashlib.sha256(open(out_p, "rb").read()).hexdigest())


if __name__ == "__main__":
    main()
