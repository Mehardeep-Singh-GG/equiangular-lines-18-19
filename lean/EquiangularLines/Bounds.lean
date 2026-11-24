module

public import EquiangularLines.Seidel
public import EquiangularLines.LemmensSeidel
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.Data.ZMod.Basic

/-!
# Fundamental Bounds on Equiangular Lines

This module establishes the classical upper bounds and spectral restrictions:
1. **Gerzon bound**: `n ≤ d * (d + 1) / 2`.
2. **Relative bound**: `(n : ℝ) * (1 - d * α ^ 2) ≤ d * (1 - α ^ 2)`.
3. **Neumann's theorem**: for `n > 2 * d`, `1 / α` is an odd integer `k ≥ 3`.
4. **Lemmens–Seidel bound**: re-exported `n ≤ 2 * (d - 1)` for `α = 1 / 3` and `d ≥ 15`.
5. **Phase 1 frontier theorem**: for `(d, n) ∈ {(18, 59), (18, 58), (19, 74), (19, 73)}`,
   any equiangular system forces `α = 1 / 5`, a Seidel matrix `S` with `5I + S ≥ 0` and
   `rank(5I + S) ≤ d`, and `(X + 5) ^ (n - d) ∣ S.charpoly`.
-/

@[expose] public section

namespace EquiangularLines

open Matrix Polynomial
open scoped InnerProductSpace

section Gerzon

private lemma card_upper_triangle (d : ℕ) :
    Fintype.card {p : Fin d × Fin d // p.1 ≤ p.2} = d * (d + 1) / 2 := by
  let S_le : Finset (Fin d × Fin d) := Finset.univ.filter (fun p => p.1 ≤ p.2)
  let S_ge : Finset (Fin d × Fin d) := Finset.univ.filter (fun p => p.2 ≤ p.1)
  have hcard_le : Fintype.card {p : Fin d × Fin d // p.1 ≤ p.2} = S_le.card := by
    rw [Fintype.card_subtype]
  have hswap : S_le.card = S_ge.card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp
      simpa [S_le, S_ge] using (Finset.mem_filter.mp hp).2
    · intro a _ b _ hab
      exact Prod.ext (Prod.ext_iff.mp hab).2 (Prod.ext_iff.mp hab).1
    · intro p hp
      exact ⟨(p.2, p.1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩, rfl⟩
  have hunion : S_le ∪ S_ge = Finset.univ := by
    ext p
    simp only [S_le, S_ge, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun _ => trivial, fun _ => le_total p.1 p.2⟩
  have hinter : S_le ∩ S_ge = Finset.univ.filter (fun p : Fin d × Fin d => p.1 = p.2) := by
    ext p
    simp only [S_le, S_ge, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨h1, h2⟩ => le_antisymm h1 h2, fun h => ⟨h.le, h.ge⟩⟩
  have hdiag : (Finset.univ.filter (fun p : Fin d × Fin d => p.1 = p.2)).card = d := by
    refine (Finset.card_bij (fun (p : Fin d × Fin d) _ => p.1) ?_ ?_ ?_).trans (Finset.card_fin d)
    · intro p _; exact Finset.mem_univ _
    · intro a ha b hb hab
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      exact Prod.ext hab (ha'.symm.trans (hab.trans hb'))
    · intro i _
      exact ⟨(i, i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩
  have hinc := Finset.card_union_add_card_inter S_le S_ge
  rw [hunion, hinter, hdiag, Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at hinc
  have hsq : d * d + d = d * (d + 1) := by ring
  rw [hcard_le]
  omega

/-- **Gerzon bound**: any equiangular system of `n` lines in `ℝ^d` satisfies `n ≤ d * (d + 1) / 2`. -/
theorem gerzon_bound {d n : ℕ} {α : ℝ} {v : Fin n → EuclideanSpace ℝ (Fin d)}
    (hv : IsEquiangularSystem d n α v) : n ≤ d * (d + 1) / 2 := by
  let symSub : Submodule ℝ (Matrix (Fin d) (Fin d) ℝ) :=
    { carrier := {M | Mᵀ = M}
      zero_mem' := Matrix.transpose_zero
      add_mem' := fun {A B} hA hB => by change (A + B)ᵀ = A + B; rw [Matrix.transpose_add, hA, hB]
      smul_mem' := fun c {M} hM => by change (c • M)ᵀ = c • M; rw [Matrix.transpose_smul, hM] }
  let Q : Fin n → symSub := fun i =>
    ⟨Matrix.of fun a b => v i a * v i b, by
      ext a b
      simp only [Matrix.transpose_apply, Matrix.of_apply]
      ring⟩
  have htrace_Q : ∀ i j : Fin n, ((Q i).1 * (Q j).1).trace = ⟪v i, v j⟫_ℝ ^ 2 := by
    intro i j
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Q, Matrix.of_apply]
    have hinner : ⟪v i, v j⟫_ℝ = ∑ a : Fin d, v i a * v j a := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [mul_comm]
    rw [hinner, sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hli : LinearIndependent ℝ Q := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hM0 : (∑ i : Fin n, c i • (Q i).1) = 0 := by
      simpa using congrArg Subtype.val hc
    have htr0 : ((∑ i : Fin n, c i • (Q i).1) * (∑ j : Fin n, c j • (Q j).1)).trace = 0 := by
      rw [hM0, Matrix.zero_mul, Matrix.trace_zero]
    have hexp : ((∑ i : Fin n, c i • (Q i).1) * (∑ j : Fin n, c j • (Q j).1)).trace =
        ∑ i : Fin n, ∑ j : Fin n, c i * c j * ⟪v i, v j⟫_ℝ ^ 2 := by
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum, Matrix.trace_sum, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.trace_smul, smul_eq_mul, htrace_Q]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have hquad : (∑ i : Fin n, ∑ j : Fin n, c i * c j * ⟪v i, v j⟫_ℝ ^ 2) =
        (1 - α ^ 2) * (∑ i : Fin n, c i ^ 2) + α ^ 2 * (∑ i : Fin n, c i) ^ 2 := by
      have hterm : ∀ i j : Fin n,
          c i * c j * ⟪v i, v j⟫_ℝ ^ 2 =
            (if i = j then (1 - α ^ 2) * (c i ^ 2) else 0) + α ^ 2 * (c i * c j) := by
        intro i j
        by_cases hij : i = j
        · subst hij
          rw [real_inner_self_eq_norm_sq, hv.2.2.1 i]
          simp only [ite_true]
          ring
        · have habs := hv.2.2.2 i j hij
          have hsq : ⟪v i, v j⟫_ℝ ^ 2 = α ^ 2 := by
            rw [← sq_abs ⟪v i, v j⟫_ℝ, habs]
          simp only [hij, ite_false, hsq]
          ring
      simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq]
      simp only [Finset.mem_univ, ite_true]
      have hsum_prod : (∑ i : Fin n, ∑ j : Fin n, α ^ 2 * (c i * c j)) =
          α ^ 2 * (∑ i : Fin n, c i) ^ 2 := by
        rw [sq (∑ i : Fin n, c i), Finset.sum_mul]
        simp_rw [Finset.mul_sum]
      rw [hsum_prod, ← Finset.mul_sum]
    rw [hexp, hquad] at htr0
    have h1 : 0 < 1 - α ^ 2 := by
      nlinarith [hv.1, hv.2.1]
    have h2 : 0 ≤ α ^ 2 * (∑ i : Fin n, c i) ^ 2 := by positivity
    have hsum_sq_nonneg : 0 ≤ ∑ i : Fin n, c i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hsum_sq_zero : ∑ i : Fin n, c i ^ 2 = 0 := by nlinarith
    intro i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (c j))).mp
      hsum_sq_zero i (Finset.mem_univ i)
    exact sq_eq_zero_iff.mp hi
  let upper : symSub →ₗ[ℝ] ({p : Fin d × Fin d // p.1 ≤ p.2} → ℝ) :=
    { toFun := fun M p => M.1 p.1.1 p.1.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hker_upper : LinearMap.ker upper = ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨M, hM⟩ hker
    rw [Submodule.mem_bot]
    apply Subtype.ext
    ext a b
    change M a b = 0
    rcases le_total a b with hab | hba
    · exact congr_fun hker ⟨(a, b), hab⟩
    · have hMab : M a b = M b a := (congr_fun (congr_fun hM a) b).symm
      rw [hMab]
      exact congr_fun hker ⟨(b, a), hba⟩
  have hfin_sym : Module.finrank ℝ symSub ≤ d * (d + 1) / 2 := by
    have hle := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp hker_upper)
    rw [Module.finrank_fintype_fun_eq_card, card_upper_triangle] at hle
    exact hle
  have hcard_le := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at hcard_le
  exact hcard_le.trans hfin_sym

end Gerzon

section RelativeBound

private lemma trace_mul_self_eq_sum_sq_eigenvalues {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.IsHermitian) :
    (M * M).trace = ∑ i : Fin n, hM.eigenvalues i ^ 2 := by
  let U : Matrix (Fin n) (Fin n) ℝ := hM.eigenvectorUnitary
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal hM.eigenvalues
  have hspec : M = U * D * star U := by
    simpa [U, D, Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id, Function.comp_def] using
      hM.spectral_theorem
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self hM.eigenvectorUnitary
  have hM2 : M * M = U * (D * D) * star U := by
    calc M * M = (U * D * star U) * (U * D * star U) := by rw [hspec]
      _ = U * D * (star U * U) * D * star U := by simp only [Matrix.mul_assoc]
      _ = U * (D * D) * star U := by rw [hUU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [hM2, Matrix.trace_mul_cycle, hUU, Matrix.one_mul]
  simp only [D, Matrix.diagonal_mul_diagonal, Matrix.trace, Matrix.diag_apply,
    Matrix.diagonal_apply_eq, sq]

/-- **Relative bound (division-free form)**:
`(n : ℝ) * (1 - (d : ℝ) * α ^ 2) ≤ (d : ℝ) * (1 - α ^ 2)`. -/
theorem relative_bound_mul {d n : ℕ} {α : ℝ} {v : Fin n → EuclideanSpace ℝ (Fin d)}
    (hv : IsEquiangularSystem d n α v) :
    (n : ℝ) * (1 - (d : ℝ) * α ^ 2) ≤ (d : ℝ) * (1 - α ^ 2) := by
  cases n with
  | zero =>
    have h1 : 0 ≤ 1 - α ^ 2 := by nlinarith [hv.1, hv.2.1]
    simp only [Nat.cast_zero, zero_mul]
    exact mul_nonneg (Nat.cast_nonneg d) h1
  | succ m =>
    let G := gramMatrix v
    have hG_psd : G.PosSemidef := gramMatrix_posSemidef v
    have hG_herm : G.IsHermitian := hG_psd.isHermitian
    have hG_rank : G.rank ≤ d := gramMatrix_rank_le v
    have htr : G.trace = (m + 1 : ℝ) := by
      have hdiag : ∀ i : Fin (m + 1), G i i = 1 := fun i => by
        simp [G, gramMatrix, hv.2.2.1 i]
      simp [Matrix.trace, hdiag]
    have htr2 : (G * G).trace = (m + 1 : ℝ) + (m + 1 : ℝ) * (m : ℝ) * α ^ 2 := by
      have hsym : ∀ i j : Fin (m + 1), G i j * G j i = if i = j then 1 else α ^ 2 := by
        intro i j
        by_cases hij : i = j
        · subst hij
          simp [G, gramMatrix, hv.2.2.1 i]
        · have habs := hv.2.2.2 i j hij
          have hsq : ⟪v i, v j⟫_ℝ ^ 2 = α ^ 2 := by
            rw [← sq_abs ⟪v i, v j⟫_ℝ, habs]
          simp only [G, gramMatrix, Matrix.of_apply, hij, ite_false, real_inner_comm (v i) (v j)]
          simpa [sq] using hsq
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, hsym]
      have hrow : ∀ i : Fin (m + 1),
          (∑ j : Fin (m + 1), if i = j then (1 : ℝ) else α ^ 2) = 1 + (m : ℝ) * α ^ 2 := by
        intro i
        have hsplit : (∑ j : Fin (m + 1), if i = j then (1 : ℝ) else α ^ 2) =
            (∑ j : Fin (m + 1), if j = i then (1 : ℝ) else 0) +
            ∑ j : Fin (m + 1), if j ≠ i then α ^ 2 else 0 := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases hij : i = j
          · subst hij; simp
          · simp [hij, Ne.symm hij]
        rw [hsplit, Finset.sum_ite_eq']
        simp only [Finset.mem_univ, ite_true]
        have hfilt : (∑ j : Fin (m + 1), if j ≠ i then α ^ 2 else 0) =
            (Finset.univ.filter (fun j : Fin (m + 1) => j ≠ i)).card • α ^ 2 := by
          rw [← Finset.sum_filter, Finset.sum_const]
        have hcard : (Finset.univ.filter (fun j : Fin (m + 1) => j ≠ i)).card = m := by
          rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_fin]
          omega
        rw [hfilt, hcard, nsmul_eq_mul]
      rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      push_cast
      ring
    let S : Finset (Fin (m + 1)) := Finset.univ.filter (fun i => hG_herm.eigenvalues i ≠ 0)
    have hS_card : S.card ≤ d := by
      have hcard : S.card = G.rank := by
        rw [hG_herm.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
      omega
    have hsum_eig : G.trace = ∑ i ∈ S, hG_herm.eigenvalues i := by
      rw [hG_herm.trace_eq_sum_eigenvalues]
      simp only [RCLike.ofReal_real_eq_id, id_eq]
      symm
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : hG_herm.eigenvalues i = 0 <;> simp [h]
    have hsum_eig2 : (G * G).trace = ∑ i ∈ S, hG_herm.eigenvalues i ^ 2 := by
      rw [trace_mul_self_eq_sum_sq_eigenvalues hG_herm]
      symm
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : hG_herm.eigenvalues i = 0 <;> simp [h]
    have hcs : (∑ i ∈ S, hG_herm.eigenvalues i) ^ 2 ≤
        (S.card : ℝ) * ∑ i ∈ S, hG_herm.eigenvalues i ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have htr_sq : (m + 1 : ℝ) ^ 2 ≤ (d : ℝ) * ((m + 1 : ℝ) + (m + 1 : ℝ) * (m : ℝ) * α ^ 2) := by
      have hS_le : (S.card : ℝ) ≤ (d : ℝ) := by exact_mod_cast hS_card
      have hnn : 0 ≤ ∑ i ∈ S, hG_herm.eigenvalues i ^ 2 :=
        Finset.sum_nonneg fun i _ => sq_nonneg _
      have h1 : (S.card : ℝ) * ∑ i ∈ S, hG_herm.eigenvalues i ^ 2 ≤
          (d : ℝ) * ∑ i ∈ S, hG_herm.eigenvalues i ^ 2 :=
        mul_le_mul_of_nonneg_right hS_le hnn
      have hcomb := hcs.trans h1
      rwa [← hsum_eig, htr, ← hsum_eig2, htr2] at hcomb
    have hm_pos : (0 : ℝ) < (m + 1 : ℝ) := by positivity
    have hdiv : (m + 1 : ℝ) ≤ (d : ℝ) * (1 + (m : ℝ) * α ^ 2) := by
      nlinarith
    push_cast
    linarith

/-- **Relative bound**: if `d * α ^ 2 < 1`, then `n ≤ d * (1 - α ^ 2) / (1 - d * α ^ 2)`. -/
theorem relative_bound {d n : ℕ} {α : ℝ} {v : Fin n → EuclideanSpace ℝ (Fin d)}
    (hv : IsEquiangularSystem d n α v) (hdα : (d : ℝ) * α ^ 2 < 1) :
    (n : ℝ) ≤ (d : ℝ) * (1 - α ^ 2) / (1 - (d : ℝ) * α ^ 2) :=
  (le_div_iff₀ (sub_pos.mpr hdα)).mpr (relative_bound_mul hv)

end RelativeBound

section Neumann

private lemma pow_dvd_of_pow_map_dvd {μ : ℝ} {m : ℕ} {P : ℚ[X]} (hP : P ≠ 0)
    (hInt : IsIntegral ℚ μ)
    (hdvd : (X - C μ) ^ m ∣ P.map (algebraMap ℚ ℝ)) :
    (minpoly ℚ μ) ^ m ∣ P := by
  induction m generalizing P with
  | zero => simp
  | succ m ih =>
    have hd1 : (X - C μ) ∣ P.map (algebraMap ℚ ℝ) :=
      dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero m)) hdvd
    have hroot : (P.map (algebraMap ℚ ℝ)).eval μ = 0 :=
      Polynomial.dvd_iff_isRoot.mp hd1
    have haeval : Polynomial.aeval μ P = 0 := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map]
      exact hroot
    have hmin_dvd : minpoly ℚ μ ∣ P := minpoly.dvd ℚ μ haeval
    rcases hmin_dvd with ⟨R, rfl⟩
    have hR0 : R ≠ 0 := right_ne_zero_of_mul hP
    have hmin0 : minpoly ℚ μ ≠ 0 := minpoly.ne_zero hInt
    have hmul_ne : (minpoly ℚ μ).map (algebraMap ℚ ℝ) * R.map (algebraMap ℚ ℝ) ≠ 0 :=
      mul_ne_zero (Polynomial.map_ne_zero hmin0) (Polynomial.map_ne_zero hR0)
    have hsep : ((minpoly ℚ μ).map (algebraMap ℚ ℝ)).Separable :=
      ((minpoly.irreducible hInt).separable).map
    have hrm_min : Polynomial.rootMultiplicity μ ((minpoly ℚ μ).map (algebraMap ℚ ℝ)) ≤ 1 :=
      Polynomial.rootMultiplicity_le_one_of_separable hsep μ
    have hrm_prod : m + 1 ≤ Polynomial.rootMultiplicity μ
        ((minpoly ℚ μ).map (algebraMap ℚ ℝ) * R.map (algebraMap ℚ ℝ)) := by
      refine (Polynomial.le_rootMultiplicity_iff hmul_ne).mpr ?_
      rw [← Polynomial.map_mul]
      exact hdvd
    rw [Polynomial.rootMultiplicity_mul hmul_ne] at hrm_prod
    have hrm_R : m ≤ Polynomial.rootMultiplicity μ (R.map (algebraMap ℚ ℝ)) := by omega
    have hR_dvd : (X - C μ) ^ m ∣ R.map (algebraMap ℚ ℝ) :=
      dvd_trans (pow_dvd_pow _ hrm_R) (Polynomial.pow_rootMultiplicity_dvd _ _)
    have ihR := ih hR0 hR_dvd
    rw [pow_succ']
    exact mul_dvd_mul_left _ ihR

private lemma charpoly_J_sub_I_zmod2 (n : ℕ) :
    ((Matrix.vecMulVec (1 : Fin n → ZMod 2) 1 - Matrix.scalar (Fin n) 1)).charpoly =
      (X + 1 : (ZMod 2)[X]) ^ n - (n : ZMod 2) • (X + 1 : (ZMod 2)[X]) ^ (n - 1) := by
  rw [Matrix.charpoly_sub_scalar, Matrix.charpoly_vecMulVec, Fintype.card_fin]
  have hdot : (1 : Fin n → ZMod 2) ⬝ᵥ 1 = (n : ZMod 2) := by
    simp [dotProduct]
  rw [hdot, Polynomial.sub_comp, Polynomial.pow_comp, Polynomial.smul_comp, Polynomial.pow_comp]
  simp

/-- **Neumann's theorem**: if `n > 2 * d` for an equiangular system of `n` lines in `ℝ^d`,
then `1 / α` is an odd integer `k ≥ 3`. -/
theorem neumann_theorem {d n : ℕ} {α : ℝ} {v : Fin n → EuclideanSpace ℝ (Fin d)}
    (hdn2 : 2 * d < n) (hv : IsEquiangularSystem d n α v) :
    ∃ k : ℕ, Odd k ∧ 3 ≤ k ∧ α = 1 / (k : ℝ) := by
  have hd_pos : 1 ≤ d := by
    by_contra hd0
    have hd_eq : d = 0 := by omega
    subst hd_eq
    exact not_isEquiangularSystem_zero_dim (by omega) hv
  have hdn : d < n := by omega
  have hα0 : 0 < α := alpha_pos_of_dim_lt hdn hv
  have hα1 : α < 1 := hv.2.1
  rcases equiangularSystem_to_seidel hv hα0 with ⟨S, hS, _, _, hrank⟩
  have hR_dvd : (X + C (1 / α)) ^ (n - d) ∣ (S.map (Int.cast : ℤ → ℝ)).charpoly :=
    seidelGram_dvd_charpoly_real hS hrank
  rw [show S.map (Int.cast : ℤ → ℝ) = S.map (Int.castRingHom ℝ) from rfl,
    Matrix.charpoly_map] at hR_dvd
  let μ : ℝ := -(1 / α)
  have hX_eq : X + C (1 / α) = X - C μ := by
    simp [μ, sub_eq_add_neg]
  rw [hX_eq] at hR_dvd
  have hnd_pos : 1 ≤ n - d := by omega
  have hnd_ge2 : 2 ≤ n - d := by omega
  have hroot_S : (S.charpoly.map (Int.castRingHom ℝ)).eval μ = 0 := by
    apply Polynomial.dvd_iff_isRoot.mp
    exact dvd_trans (dvd_pow_self _ (by omega : n - d ≠ 0)) hR_dvd
  have hIntZ : IsIntegral ℤ μ := ⟨S.charpoly, S.charpoly_monic, by
    simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] using hroot_S⟩
  have hIntQ : IsIntegral ℚ μ := hIntZ.tower_top
  let P : ℚ[X] := S.charpoly.map (Int.castRingHom ℚ)
  have hP0 : P ≠ 0 := (S.charpoly_monic.map (Int.castRingHom ℚ)).ne_zero
  have hP_map : P.map (algebraMap ℚ ℝ) = S.charpoly.map (Int.castRingHom ℝ) := by
    dsimp only [P]
    rw [Polynomial.map_map]
    congr 1
  have hQ_dvd : (minpoly ℚ μ) ^ (n - d) ∣ P :=
    pow_dvd_of_pow_map_dvd hP0 hIntQ (hP_map ▸ hR_dvd)
  have hdeg_le : (n - d) * (minpoly ℚ μ).natDegree ≤ n := by
    have hle := Polynomial.natDegree_le_of_dvd hQ_dvd hP0
    have hmon : (minpoly ℚ μ).Monic := minpoly.monic hIntQ
    rw [hmon.natDegree_pow] at hle
    have hPdeg : P.natDegree = n := by
      dsimp only [P]
      rw [← Matrix.charpoly_map, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    omega
  have hdeg_pos : 0 < (minpoly ℚ μ).natDegree := minpoly.natDegree_pos hIntQ
  have hdeg_eq1 : (minpoly ℚ μ).natDegree = 1 := by
    have hlt : n < 2 * (n - d) := by omega
    have hmul : (n - d) * (minpoly ℚ μ).natDegree < (n - d) * 2 := by omega
    have hlt2 : (minpoly ℚ μ).natDegree < 2 := Nat.lt_of_mul_lt_mul_left hmul
    omega
  have hq_eq : minpoly ℚ μ = X + C ((minpoly ℚ μ).coeff 0) := by
    have heq := Polynomial.eq_X_add_C_of_natDegree_le_one hdeg_eq1.le
    rw [← hdeg_eq1, Polynomial.coeff_natDegree, (minpoly.monic hIntQ).leadingCoeff,
      map_one, one_mul] at heq
    exact heq
  let q : ℚ := -((minpoly ℚ μ).coeff 0)
  have hμ_q : μ = (q : ℝ) := by
    have ha := minpoly.aeval ℚ μ
    rw [hq_eq, map_add, Polynomial.aeval_X, Polynomial.aeval_C] at ha
    change μ + ((minpoly ℚ μ).coeff 0 : ℝ) = 0 at ha
    have hqR : (q : ℝ) = -((minpoly ℚ μ).coeff 0 : ℝ) := by simp [q]
    linarith
  obtain ⟨m, hm⟩ := hIntZ.mem_range_ratCast_iff.mp ⟨q, hμ_q.symm⟩
  let c : ℤ := -m
  have hc_eq : (c : ℝ) = 1 / α := by
    have hmR : (m : ℝ) = μ := hm
    dsimp [μ] at hmR
    have hcR : (c : ℝ) = -(m : ℝ) := by simp [c]
    linarith
  have hc_gt1 : (1 : ℝ) < (c : ℝ) := by
    rw [hc_eq]
    exact one_lt_one_div hα0 hα1
  have hc_ge2 : (2 : ℤ) ≤ c := by
    have : (1 : ℤ) < c := by exact_mod_cast hc_gt1
    omega
  let k : ℕ := c.toNat
  have hk_cast : (k : ℤ) = c := Int.toNat_of_nonneg (by omega)
  have hk_ge2 : 2 ≤ k := by omega
  have hα_eq : α = 1 / (k : ℝ) := by
    have hkR : (k : ℝ) = (c : ℝ) := by exact_mod_cast hk_cast
    rw [hkR, hc_eq, one_div_one_div]
  have hOdd : Odd k := by
    by_contra hnot
    have hEven : Even k := Nat.not_odd_iff_even.mp hnot
    have h2R : (X + C (c : ℝ)) ^ 2 ∣ S.charpoly.map (Int.castRingHom ℝ) := by
      have : (X + C (c : ℝ)) ^ 2 ∣ (X - C μ) ^ (n - d) := by
        rw [show X - C μ = X + C (c : ℝ) by
          have hμc : -μ = (c : ℝ) := by dsimp [μ]; linarith [hc_eq]
          rw [sub_eq_add_neg, ← Polynomial.C_neg, hμc]]
        exact pow_dvd_pow _ hnd_ge2
      exact dvd_trans this hR_dvd
    have h2Z : (X + C c) ^ 2 ∣ S.charpoly := by
      have hmap : ((X + C c) ^ 2).map (Int.castRingHom ℝ) ∣
          S.charpoly.map (Int.castRingHom ℝ) := by
        simpa [Polynomial.map_pow] using h2R
      exact (Polynomial.map_dvd_map (Int.castRingHom ℝ) Int.cast_injective
        ((Polynomial.monic_X_add_C c).pow 2)).mp hmap
    have h2_mod2 : ((X + C c) ^ 2).map (Int.castRingHom (ZMod 2)) ∣
        S.charpoly.map (Int.castRingHom (ZMod 2)) :=
      Polynomial.map_dvd (Int.castRingHom (ZMod 2)) h2Z
    have hc_mod2 : (c : ZMod 2) = 0 := by
      rcases even_iff_two_dvd.mp hEven with ⟨t, ht⟩
      rw [← hk_cast, ht]
      push_cast
      have h2z : (2 : ZMod 2) = 0 := rfl
      simp [h2z]
    have hX2 : (X : (ZMod 2)[X]) ^ 2 ∣ (S.map (Int.castRingHom (ZMod 2))).charpoly := by
      rw [Matrix.charpoly_map]
      have heq : ((X + C c : ℤ[X]) ^ 2).map (Int.castRingHom (ZMod 2)) = (X : (ZMod 2)[X]) ^ 2 := by
        simp only [Polynomial.map_pow, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
        change (X + C (c : ZMod 2)) ^ 2 = X ^ 2
        rw [hc_mod2, map_zero, add_zero]
      rwa [heq] at h2_mod2
    have hS_mod2 : S.map (Int.castRingHom (ZMod 2)) =
        Matrix.vecMulVec (1 : Fin n → ZMod 2) 1 - Matrix.scalar (Fin n) 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [hS.diag_eq_zero i]
      · simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.vecMulVec_apply, Pi.one_apply,
          mul_one, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, sub_zero]
        rcases hS.offDiag_eq_one_or_neg_one hij with h | h <;> simp [h]
    rw [hS_mod2, charpoly_J_sub_I_zmod2] at hX2
    rcases Nat.even_or_odd n with hn_even | hn_odd
    · have hn_mod2 : (n : ZMod 2) = 0 := by
        rcases even_iff_two_dvd.mp hn_even with ⟨t, rfl⟩
        push_cast
        have h2z : (2 : ZMod 2) = 0 := rfl
        simp [h2z]
      rw [hn_mod2, zero_smul, sub_zero] at hX2
      have heval := congrArg (Polynomial.eval (0 : ZMod 2))
        (dvd_trans (dvd_pow_self X (by norm_num)) hX2).choose_spec
      simp only [Polynomial.eval_mul, Polynomial.eval_X, zero_mul, Polynomial.eval_pow,
        Polynomial.eval_add, Polynomial.eval_one, zero_add, one_pow] at heval
      exact absurd heval (by decide)
    · have hn_mod2 : (n : ZMod 2) = 1 := by
        rcases hn_odd with ⟨t, ht⟩
        rw [ht]
        push_cast
        have h2z : (2 : ZMod 2) = 0 := rfl
        simp [h2z]
      have hn1 : 1 ≤ n := by omega
      have hfac : (X + 1 : (ZMod 2)[X]) ^ n - (1 : ZMod 2) • (X + 1 : (ZMod 2)[X]) ^ (n - 1) =
          (X + 1 : (ZMod 2)[X]) ^ (n - 1) * X := by
        have hsub : n = (n - 1) + 1 := by omega
        calc (X + 1 : (ZMod 2)[X]) ^ n - (1 : ZMod 2) • (X + 1 : (ZMod 2)[X]) ^ (n - 1)
            = (X + 1 : (ZMod 2)[X]) ^ (n - 1) * (X + 1) - (X + 1 : (ZMod 2)[X]) ^ (n - 1) := by
              rw [← pow_succ, ← hsub, one_smul]
          _ = (X + 1 : (ZMod 2)[X]) ^ (n - 1) * X := by ring
      rw [hn_mod2, hfac] at hX2
      rcases hX2 with ⟨Q, hQ⟩
      have hcoeff := congrArg (fun p : (ZMod 2)[X] => p.coeff 1) hQ
      rw [Polynomial.coeff_mul_X, pow_two, mul_assoc,
        Polynomial.coeff_X_mul, Polynomial.coeff_X_mul_zero] at hcoeff
      have h0 : ((X + 1 : (ZMod 2)[X]) ^ (n - 1)).coeff 0 = 1 := by
        rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow, Polynomial.eval_add,
          Polynomial.eval_X, Polynomial.eval_one, zero_add, one_pow]
      rw [h0] at hcoeff
      exact absurd hcoeff (by decide)
  rcases hOdd with ⟨r, hr⟩
  exact ⟨k, ⟨r, hr⟩, by omega, hα_eq⟩

end Neumann

section Frontier

/-- **Phase 1 Culminating Theorem**: for any `(d, n) ∈ {(18, 59), (18, 58), (19, 74), (19, 73)}`,
any equiangular system of `n` lines in `ℝ^d` forces `α = 1 / 5` and yields an integer Seidel
matrix `S` with `5I + S` positive semidefinite of rank at most `d` and `(X + 5)^(n - d) ∣ S.charpoly`. -/
theorem phase1_frontier_forces_one_fifth {d n : ℕ} {α : ℝ}
    {v : Fin n → EuclideanSpace ℝ (Fin d)}
    (hdn : (d = 18 ∧ (n = 59 ∨ n = 58)) ∨ (d = 19 ∧ (n = 74 ∨ n = 73)))
    (hv : IsEquiangularSystem d n α v) :
    α = 1 / 5 ∧
      ∃ S : Matrix (Fin n) (Fin n) ℤ,
        IsSeidelMatrix S ∧
        (seidelGram (1 / 5) S).PosSemidef ∧
        (seidelGram (1 / 5) S).rank ≤ d ∧
        (X + C 5) ^ (n - d) ∣ S.charpoly := by
  have h2d : 2 * d < n := by rcases hdn with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;> omega
  obtain ⟨k, hOdd, hk3, hα⟩ := neumann_theorem h2d hv
  have hk_ne3 : k ≠ 3 := by
    intro hk3'
    subst hk3'
    have hv3 : IsEquiangularSystem d n (1 / 3) v := by simpa [hα] using hv
    have hd15 : 15 ≤ d := by rcases hdn with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
    have hle := lemmens_seidel_bound hd15 hv3
    rcases hdn with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;> omega
  have hk_ne_ge7 : ¬ 7 ≤ k := by
    intro hk7
    have hrel := relative_bound_mul hv
    rw [hα] at hrel
    have hkR : (7 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk7
    have hk_pos : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
    have hmul : (n : ℝ) * ((k : ℝ) ^ 2 - (d : ℝ)) ≤ (d : ℝ) * ((k : ℝ) ^ 2 - 1) := by
      have hk2 : (n : ℝ) * (1 - (d : ℝ) * (1 / (k : ℝ)) ^ 2) * (k : ℝ) ^ 2 ≤
          (d : ℝ) * (1 - (1 / (k : ℝ)) ^ 2) * (k : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hrel hk_pos.le
      have hne : (k : ℝ) ≠ 0 := by linarith
      field_simp [hne] at hk2
      linarith
    have hmul_int : (n - d : ℝ) * (k : ℝ) ^ 2 ≤ (d : ℝ) * (n - 1 : ℝ) := by linarith
    have hk49 : (49 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    rcases hdn with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;> norm_num at hmul_int <;> nlinarith
  have hk5 : k = 5 := by
    rcases hOdd with ⟨t, ht⟩
    omega
  have hα5 : α = 1 / 5 := by simpa [hk5] using hα
  have hv5 : IsEquiangularSystem d n (1 / 5) v := hα5 ▸ hv
  obtain ⟨S, hS, _, hPSD, hrank⟩ := equiangularSystem_to_seidel hv5 (by norm_num)
  have hdvd := seidelGram_dvd_charpoly_int hS (k := 5) (by norm_num)
    (by simpa using hrank)
  exact ⟨hα5, S, hS, hPSD, hrank, hdvd⟩

end Frontier

end EquiangularLines

end
