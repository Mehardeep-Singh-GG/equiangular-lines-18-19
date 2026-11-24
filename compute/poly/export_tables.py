"""
Export standardized machine-readable polynomial census tables for all solved (d, n) cases.
Converts shifted w-polynomials P(w) / Q(w) into exact f(x), h(y)=f(y-5), factored f(x),
and verifies exact traces Tr(S)=0 and Tr(S^2)=n(n-1) in pure integer arithmetic.
"""
import json
import os
import sys
import sympy as sp

from pathlib import Path
_COMP_DIR = Path(__file__).resolve().parent.parent
if str(_COMP_DIR) not in sys.path:
    sys.path.insert(0, str(_COMP_DIR))
from _io import POLY_RESULTS_DIR

RESULTS_DIR = str(POLY_RESULTS_DIR)

def export_case(filename, out_name):
    path = os.path.join(RESULTS_DIR, filename)
    if not os.path.exists(path):
        print(f"Skipping {filename} (not found)")
        return None
    data = json.load(open(path))
    d, n, c = data["d"], data["n"], data["c"]
    n_even = (n % 2 == 0)
    w, x, y = sp.symbols("w x y")
    entries = []
    for idx, b in enumerate(data["polys"]):
        assert len(b) == d + 1
        # P(w) or Q(w) in descending powers of w
        W_poly = sum(int(b[j]) * w**(d - j) for j in range(d + 1))
        scale = 2**d if n_even else 2**(d - 1)
        f_expr = sp.expand(scale * W_poly.subs(w, (x - c) / 2))
        f_poly = sp.Poly(f_expr, x, domain=sp.ZZ)
        assert f_poly.degree() == d and f_poly.LC() == 1
        h_poly = sp.Poly(f_expr.subs(x, y - 5), y, domain=sp.ZZ)
        f_coeffs = [int(v) for v in f_poly.all_coeffs()]
        h_coeffs = [int(v) for v in h_poly.all_coeffs()]
        # Verify traces: sum(roots(f)) = 5*(n-d) => f_coeffs[1] = -5*(n-d)
        assert f_coeffs[1] == -5 * (n - d), f"Trace mismatch at {idx}"
        assert h_coeffs[1] == -5 * n
        assert h_coeffs[2] == 12 * n * (n - 1)
        facs = sp.factor_list(f_expr)[1]
        fac_str = " * ".join(
            f"({sp.sstr(fac)})" + (f"^{mult}" if mult > 1 else "")
            for fac, mult in sorted(facs, key=lambda t: (sp.Poly(t[0], x).degree(), str(t[0])))
        )
        entries.append({
            "index": idx,
            "w_coeffs_desc": [int(v) for v in b],
            "f_coeffs_desc": f_coeffs,
            "h_coeffs_desc": h_coeffs,
            "chi_S_factored": f"(x + 5)^{n - d} * {fac_str}",
        })
    out_path = os.path.join(RESULTS_DIR, out_name)
    out_obj = {
        "d": d,
        "n": n,
        "c_shift": c,
        "n_even": n_even,
        "count": len(entries),
        "candidates": entries,
    }
    with open(out_path, "w") as f:
        json.dump(out_obj, f, indent=2)
    print(f"Exported {out_path}: ({d}, {n}) count={len(entries)}")
    return out_path

if __name__ == "__main__":
    targets = [
        ("raw_19_75.json", "table_19_75_raw.json"),
        ("raw_18_60.json", "table_18_60.json"),
        ("cor43_17_49.json", "table_17_49_cor43.json"),
        ("mod128_19_74.json", "table_19_74.json"),
        ("cor43_18_59.json", "table_18_59_cor43.json"),
        ("raw_18_58.json", "table_18_58.json"),
        ("cor43_19_73.json", "table_19_73_cor43.json"),
    ]
    for src, dst in targets:
        export_case(src, dst)
