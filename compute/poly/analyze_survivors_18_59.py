import json
import sympy as sp
from fractions import Fraction
from run_stage3_18_59 import solve_candidate, bucket_indices_exact, galois_rows_for_bucket
from stage3_solver import solve_2v_jacobi_pair, strict_upper_bound_roots


def analyze_surv(cand, counts_n, n, d_dim, c_sh):
    w, x = sp.symbols("w x")
    idx = cand["index"]
    s = cand["s"]
    deck = [[int(v) for v in row] for row in cand["deck"]]
    Pw = sp.Poly(sum(cand["b"][j] * w ** (d_dim - j) for j in range(d_dim + 1)), w, domain=sp.ZZ)
    w0 = (-5 - c_sh) // 2
    Full_w = sp.Poly((w - w0) ** (n - d_dim), w, domain=sp.ZZ) * Pw
    chi_S = sp.Poly(sp.expand(2 ** (n - 1) * Full_w.as_expr().subs(w, (x - c_sh) / 2)), x, domain=sp.ZZ)
    Gcd_x = sp.gcd(chi_S, chi_S.diff())
    if Gcd_x.LC() < 0:
        Gcd_x = -Gcd_x
    Gcd2_x = sp.gcd(Gcd_x, Gcd_x.diff())
    if Gcd2_x.LC() < 0:
        Gcd2_x = -Gcd2_x

    facs_x = sp.factor_list(chi_S.as_expr())[1]
    Sim_x = sp.Poly(1, x, domain=sp.ZZ)
    Mult_rad_x = sp.Poly(1, x, domain=sp.ZZ)
    for fac, mult in facs_x:
        fp = sp.Poly(fac, x, domain=sp.ZZ)
        if mult == 1:
            Sim_x = Sim_x * fp
        else:
            Mult_rad_x = Mult_rad_x * fp

    act = [(j, c) for j, c in enumerate(counts_n) if c > 0]
    print(f"\n==================== IDX {idx} counts={act} ====================")
    print("  chi_S factors:", [(sp.sstr(f), m) for f, m in facs_x])
    g_list = [
        sp.Poly(sp.expand(2 ** (s - 1) * sum(row[k] * w ** (s - 1 - k) for k in range(s)).subs(w, (x - c_sh) / 2)), x, domain=sp.ZZ)
        for row in deck
    ]
    x_max_ub = strict_upper_bound_roots(chi_S, x)

    # Check Theorem 7.1 M, N on simple factors and full eigenspace projections E_fac(v, u)
    # Wait: E_fac = chi_S / fac ... wait for simple factor fac(x) with mult 1:
    # Let phi_f(x) = chi_S(x) / fac(x). At root lam of fac, chi_S'(lam) = phi_f(lam)*fac'(lam)
    # and E_fac[v, v] = g_v(lam) * Gcd_x(lam) / chi_S'(lam) = [g_v(lam) * Gcd_x(lam) / phi_f(lam)] / fac'(lam)
    # Wait: phi_f(x) = (chi_S / (Gcd_x * fac)) * Gcd_x = (Sim_x / fac) * Gcd_x!
    # So E_fac[v, v] = g_v(lam) / (chi_S'(lam) / Gcd_x(lam)) = g_v(lam) / (fac'(lam) * (Sim_x/fac)(lam))!
    # And for off-diagonal E_fac[u, v] with Q_uv = Gcd2_x * q_uv:
    # Wait: S_{uv} entry -> adjugate[u, v] = - s_uv * Gcd2_x * q_uv(lam) ... wait let's check sign!
    # Off-diagonal (xI - S)^{-1}_{uv} = chi_{S_{uv}}(x) / chi_S(x), where (xI - S) adj(xI - S) = chi_S I.
    # Let's check exact residue: for lam root of fac (mult 1):
    # (adj(lam I - S))_{uv} / chi_S'(lam) = E_fac[u, v].
    # Note adj(x I - S)_{uv} = s_{uv} * Gcd2_x(x) * q_{uv}(x) (Wait: sign of off-diagonal cofactor!
    # For 2x2: (xI - S) = [[x, -s], [-s, x]], adj = [[x, s], [s, x]], so adj_{01} = +s_{01}!
    # Let's verify sign on 2x2: E_{1} = [[1/2, 1/2], [1/2, 1/2]], adj(1*I - S)_{01}/chi'(1) = s / 2 = +1/2!
    # Wait: what is chi_{S_{uv}} vs s_{uv} Gcd2_x q_{uv}? Let's check solve_2v_jacobi_pair convention!)
    for i1 in range(len(act)):
        u, cu = act[i1]
        for i2 in range(i1, len(act)):
            v, cv = act[i2]
            if u == v and cu < 2:
                continue
            res = solve_2v_jacobi_pair(g_list[u], g_list[v], Sim_x, Mult_rad_x, Gcd2_x, n, x, x_max_ub=x_max_ub)
            # group by q_uv
            uniq = {}
            for s2_val, q_uv, _ in res:
                key = tuple(int(val) for val in q_uv.all_coeffs())
                uniq.setdefault(key, []).append(s2_val)
            print(f"  2v({u},{v}) [sizes {cu},{cv}]: {len(uniq)} distinct q_uv ({len(res)} total (s2,q))")
            for k_i, (q_key, s2s) in enumerate(uniq.items()):
                q_p = sp.Poly(q_key, x, domain=sp.ZZ)
                print(f"    opt {k_i}: s2={s2s}, deg(q)={q_p.degree()}, q={sp.sstr(q_p.as_expr())}")


from pathlib import Path
import sys
_COMP_DIR = Path(__file__).resolve().parent.parent
if str(_COMP_DIR) not in sys.path:
    sys.path.insert(0, str(_COMP_DIR))
from _io import load_json_auto

d59 = load_json_auto("deck_18_59.json")
n, d_dim, c_sh = d59["n"], d59["d"], d59["c"]
for idx in [692, 441, 488]:
    res = solve_candidate(d59["candidates"][idx], n, d_dim, c_sh, run_stage3=True, run_sv_galois=True)
    for si, surv in enumerate(res["stage3_survivors"]):
        print(f"\n>>> IDX {idx} SURV {si} <<<")
        analyze_surv(d59["candidates"][idx], surv["counts_n"], n, d_dim, c_sh)
