module

public import EquiangularLines.Basic
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Seidel Matrices and Gram Equivalence

This module defines integer Seidel matrices, switching equivalence, basic trace identities,
and the bidirectional equivalence between equiangular line systems in `ℝ^d` and positive
semidefinite Seidel Gram matrices `G = (1 / α) • I + S` of rank at most `d`.
-/

@[expose] public section

namespace EquiangularLines

open Matrix Polynomial
open scoped InnerProductSpace ComplexOrder

/-- An integer matrix `S : Matrix (Fin n) (Fin n) ℤ` is a Seidel matrix if it is symmetric,
has zero diagonal, and has `±1` off-diagonal entries. -/
def IsSeidelMatrix {n : ℕ} (S : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  Sᵀ = S ∧ (∀ i, S i i = 0) ∧ (∀ i j, i ≠ j → S i j = 1 ∨ S i j = -1)

/-- The real Seidel Gram matrix `(1 / α) • I + S` associated with cosine `α` and Seidel matrix `S`. -/
noncomputable def seidelGram {n : ℕ} (α : ℝ) (S : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (1 / α) • (1 : Matrix (Fin n) (Fin n) ℝ) + S.map (Int.cast : ℤ → ℝ)

/-- The Gram matrix `G_{ij} = ⟪v i, v j⟫_ℝ` of a finite family of vectors. -/
noncomputable def gramMatrix {d n : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ⟪v i, v j⟫_ℝ

namespace IsSeidelMatrix

variable {n : ℕ} {S : Matrix (Fin n) (Fin n) ℤ}

lemma transpose_eq (hS : IsSeidelMatrix S) : Sᵀ = S := hS.1

lemma symm (hS : IsSeidelMatrix S) (i j : Fin n) : S j i = S i j := by
  have := congr_fun (congr_fun hS.1 i) j
  simpa using this

lemma diag_eq_zero (hS : IsSeidelMatrix S) (i : Fin n) : S i i = 0 := hS.2.1 i

lemma offDiag_eq_one_or_neg_one (hS : IsSeidelMatrix S) {i j : Fin n} (hij : i ≠ j) :
    S i j = 1 ∨ S i j = -1 :=
  hS.2.2 i j hij

lemma offDiag_sq (hS : IsSeidelMatrix S) {i j : Fin n} (hij : i ≠ j) :
    S i j ^ 2 = 1 := by
  rcases hS.offDiag_eq_one_or_neg_one hij with h | h <;> simp [h]

lemma trace_eq_zero (hS : IsSeidelMatrix S) : S.trace = 0 := by
  simp [Matrix.trace, hS.diag_eq_zero]

lemma sq_diag (hS : IsSeidelMatrix S) (i : Fin n) :
    (S * S) i i = (n : ℤ) - 1 := by
  rw [Matrix.mul_apply]
  have hterm : ∀ j : Fin n, S i j * S j i = if j = i then 0 else 1 := by
    intro j
    rw [hS.symm i j]
    by_cases hji : j = i
    · subst hji
      simp [hS.diag_eq_zero]
    · simp only [hji, ↓reduceIte, ← sq]
      exact hS.offDiag_sq (Ne.symm hji)
  simp_rw [hterm]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : (Finset.univ.filter (fun j : Fin n => j ≠ i)).card = n - 1 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_fin]
  rw [hcard]
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Fin.pos i)
  omega

lemma trace_sq (hS : IsSeidelMatrix S) :
    (S * S).trace = (n : ℤ) * ((n : ℤ) - 1) := by
  cases n with
  | zero => simp [Matrix.trace]
  | succ m =>
    simp only [Matrix.trace, Matrix.diag_apply, hS.sq_diag]
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]

lemma submatrix {m : ℕ} (hS : IsSeidelMatrix S) (e : Fin m ↪ Fin n) :
    IsSeidelMatrix (S.submatrix e e) := by
  refine ⟨?_, fun i => hS.diag_eq_zero (e i), fun i j hij =>
    hS.offDiag_eq_one_or_neg_one (e.injective.ne hij)⟩
  ext i j
  exact hS.symm (e i) (e j)

/-- Switching a Seidel matrix by a diagonal matrix of `±1` signs. -/
def switch (d : Fin n → ℤ) (S : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.diagonal d * S * Matrix.diagonal d

lemma switch_apply (d : Fin n → ℤ) (S : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    switch d S i j = d i * S i j * d j := by
  simp [switch, Matrix.mul_apply, Matrix.diagonal_apply]

lemma switch_isSeidelMatrix (hS : IsSeidelMatrix S) {d : Fin n → ℤ}
    (hd : ∀ i, d i = 1 ∨ d i = -1) :
    IsSeidelMatrix (switch d S) := by
  refine ⟨?_, fun i => ?_, fun i j hij => ?_⟩
  · ext i j
    simp only [Matrix.transpose_apply, switch_apply, hS.symm]
    ring
  · simp [switch_apply, hS.diag_eq_zero]
  · simp only [switch_apply]
    rcases hd i with hi | hi <;> rcases hd j with hj | hj <;>
      rcases hS.offDiag_eq_one_or_neg_one hij with hij1 | hij1 <;>
      simp [hi, hj, hij1]

lemma switch_charpoly (S : Matrix (Fin n) (Fin n) ℤ) {d : Fin n → ℤ}
    (hd : ∀ i, d i = 1 ∨ d i = -1) :
    (switch d S).charpoly = S.charpoly := by
  have hD : Matrix.diagonal d * Matrix.diagonal d = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rcases hd i with h | h <;> simp [h]
    · simp [hij]
  rw [switch, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hD, Matrix.one_mul]

end IsSeidelMatrix

@[simp]
lemma seidelGram_apply_diag {n : ℕ} (α : ℝ) (S : Matrix (Fin n) (Fin n) ℤ)
    (hS : IsSeidelMatrix S) (i : Fin n) :
    seidelGram α S i i = 1 / α := by
  simp [seidelGram, hS.diag_eq_zero]

lemma seidelGram_apply_ne {n : ℕ} (α : ℝ) (S : Matrix (Fin n) (Fin n) ℤ)
    {i j : Fin n} (hij : i ≠ j) :
    seidelGram α S i j = (S i j : ℝ) := by
  simp [seidelGram, Matrix.one_apply_ne hij]

lemma seidelGram_isHermitian {n : ℕ} (α : ℝ) (S : Matrix (Fin n) (Fin n) ℤ)
    (hS : IsSeidelMatrix S) :
    (seidelGram α S).IsHermitian := by
  ext i j
  simp [seidelGram, hS.symm, Matrix.one_apply, eq_comm]

lemma gramMatrix_eq_transpose_mul_self {d n : ℕ}
    (v : Fin n → EuclideanSpace ℝ (Fin d)) :
    let B : Matrix (Fin d) (Fin n) ℝ := Matrix.of fun k j => v j k
    gramMatrix v = Bᵀ * B := by
  intro B
  ext i j
  simp only [gramMatrix, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, B]
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  simp [mul_comm]

lemma gramMatrix_posSemidef {d n : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d)) :
    (gramMatrix v).PosSemidef := by
  rw [gramMatrix_eq_transpose_mul_self v]
  simpa using Matrix.posSemidef_conjTranspose_mul_self (Matrix.of fun k j => v j k)

lemma gramMatrix_rank_le {d n : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d)) :
    (gramMatrix v).rank ≤ d := by
  rw [gramMatrix_eq_transpose_mul_self v, Matrix.rank_transpose_mul_self]
  exact (Matrix.rank_transpose _).symm.trans_le (Matrix.rank_le_width _)

/-- Forward reduction: every equiangular system with `α > 0` yields an integer Seidel matrix `S`
such that `(1 / α) I + S` is positive semidefinite of rank at most `d`. -/
theorem equiangularSystem_to_seidel {d n : ℕ} {α : ℝ}
    {v : Fin n → EuclideanSpace ℝ (Fin d)}
    (hv : IsEquiangularSystem d n α v) (hα : 0 < α) :
    ∃ S : Matrix (Fin n) (Fin n) ℤ,
      IsSeidelMatrix S ∧
      seidelGram α S = (1 / α) • gramMatrix v ∧
      (seidelGram α S).PosSemidef ∧
      (seidelGram α S).rank ≤ d := by
  classical
  let S : Matrix (Fin n) (Fin n) ℤ :=
    Matrix.of fun i j => if i = j then 0 else if ⟪v i, v j⟫_ℝ = α then 1 else -1
  have hS : IsSeidelMatrix S := by
    refine ⟨?_, fun i => by simp [S], fun i j hij => ?_⟩
    · ext i j
      by_cases hij : i = j
      · simp [S, hij]
      · have hji : j ≠ i := Ne.symm hij
        simp [S, hij, hji, real_inner_comm]
    · simp only [S, Matrix.of_apply, hij, ↓reduceIte]
      split_ifs <;> simp
  have hGram : seidelGram α S = (1 / α) • gramMatrix v := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [seidelGram, gramMatrix, S, hv.2.2.1 i]
    · have habs : |⟪v i, v j⟫_ℝ| = α := hv.2.2.2 i j hij
      simp only [seidelGram, gramMatrix, Matrix.add_apply, Matrix.smul_apply,
        Matrix.one_apply_ne hij, Matrix.map_apply, Matrix.of_apply, hij, ↓reduceIte, S,
        smul_eq_mul]
      rcases abs_eq hα.le |>.mp habs with hpos | hneg
      · simp [hpos, inv_mul_cancel₀ hα.ne']
      · have hne : -α ≠ α := by linarith
        simp [hneg, hne, inv_mul_cancel₀ hα.ne']
  have hPSD : (seidelGram α S).PosSemidef := by
    rw [hGram]
    exact (gramMatrix_posSemidef v).smul (one_div_nonneg.mpr hα.le)
  have hrank : (seidelGram α S).rank ≤ d := by
    rw [hGram, Matrix.rank_smul_of_mem_nonZeroDivisors]
    · exact gramMatrix_rank_le v
    · exact mem_nonZeroDivisors_of_ne_zero (one_div_ne_zero hα.ne')
  exact ⟨S, hS, hGram, hPSD, hrank⟩

/-- Helper lemma: summing a `dite` over `{k : Fin d // k.1 < r}` when `r ≤ d`. -/
private lemma sum_fin_lt_eq {d r : ℕ} (hr : r ≤ d) (F : Fin r → ℝ) :
    (∑ k : Fin d, if hk : (k : ℕ) < r then F ⟨k, hk⟩ else 0) = ∑ l : Fin r, F l := by
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun k : Fin d => (k : ℕ) < r)]
  have hzero : (∑ k ∈ Finset.univ.filter (fun k : Fin d => ¬(k : ℕ) < r),
      if hk : (k : ℕ) < r then F ⟨k, hk⟩ else 0) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    split_ifs with h
    · exact absurd h (Finset.mem_filter.mp hk).2
    · rfl
  rw [hzero, add_zero]
  refine Finset.sum_bij (fun k hk => ⟨k, (Finset.mem_filter.mp hk).2⟩) ?_ ?_ ?_ ?_
  · intro k _
    exact Finset.mem_univ _
  · intro a _ b _ hab
    exact Fin.ext (Fin.mk.inj hab)
  · intro l _
    exact ⟨Fin.castLE hr l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, l.isLt⟩, rfl⟩
  · intro k hk
    split_ifs with h
    · rfl
    · exact absurd (Finset.mem_filter.mp hk).2 h

/-- Converse reduction: any Seidel matrix `S` whose Gram matrix `(1 / α) I + S` is positive
semidefinite of rank at most `d` (with `0 < α < 1`) arises from an equiangular system in `ℝ^d`. -/
theorem seidel_to_equiangularSystem {d n : ℕ} {α : ℝ}
    {S : Matrix (Fin n) (Fin n) ℤ} (hS : IsSeidelMatrix S)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hPSD : (seidelGram α S).PosSemidef) (hrank : (seidelGram α S).rank ≤ d) :
    ∃ v : Fin n → EuclideanSpace ℝ (Fin d),
      IsEquiangularSystem d n α v ∧ seidelGram α S = (1 / α) • gramMatrix v := by
  classical
  let G : Matrix (Fin n) (Fin n) ℝ := α • seidelGram α S
  have hG_psd : G.PosSemidef := hPSD.smul hα0.le
  have hG_herm : G.IsHermitian := hG_psd.isHermitian
  have hG_rank : G.rank ≤ d := by
    rwa [Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hα0.ne')]
  let P : Fin n → Prop := fun m => hG_herm.eigenvalues m ≠ 0
  let r : ℕ := Fintype.card {m : Fin n // P m}
  have hr_eq : G.rank = r := hG_herm.rank_eq_card_non_zero_eigs
  have hr : r ≤ d := hr_eq ▸ hG_rank
  let e : {m : Fin n // P m} ≃ Fin r := Fintype.equivFin _
  let U : Matrix (Fin n) (Fin n) ℝ := hG_herm.eigenvectorUnitary
  let v : Fin n → EuclideanSpace ℝ (Fin d) := fun j =>
    WithLp.toLp 2 fun k : Fin d =>
      if hk : (k : ℕ) < r then
        Real.sqrt (hG_herm.eigenvalues (e.symm ⟨k, hk⟩).1) * U j (e.symm ⟨k, hk⟩).1
      else 0
  have hinner_G : ∀ i j : Fin n, ⟪v i, v j⟫_ℝ = G i j := by
    intro i j
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct]
    simp only [star_trivial]
    have hmul : ∑ k : Fin d, v j k * v i k =
        ∑ k : Fin d,
          if hk : (k : ℕ) < r then
            (Real.sqrt (hG_herm.eigenvalues (e.symm ⟨k, hk⟩).1) * U j (e.symm ⟨k, hk⟩).1) *
            (Real.sqrt (hG_herm.eigenvalues (e.symm ⟨k, hk⟩).1) * U i (e.symm ⟨k, hk⟩).1)
          else 0 := by
      refine Finset.sum_congr rfl fun k _ => ?_
      change (if hk : (k : ℕ) < r then _ else 0) * (if hk : (k : ℕ) < r then _ else 0) = _
      split_ifs <;> ring
    rw [hmul, sum_fin_lt_eq hr (fun l =>
      (Real.sqrt (hG_herm.eigenvalues (e.symm l).1) * U j (e.symm l).1) *
      (Real.sqrt (hG_herm.eigenvalues (e.symm l).1) * U i (e.symm l).1))]
    rw [show (∑ l : Fin r,
        (Real.sqrt (hG_herm.eigenvalues (e.symm l).1) * U j (e.symm l).1) *
        (Real.sqrt (hG_herm.eigenvalues (e.symm l).1) * U i (e.symm l).1)) =
      ∑ m : {m : Fin n // P m},
        (Real.sqrt (hG_herm.eigenvalues m.1) * U j m.1) *
        (Real.sqrt (hG_herm.eigenvalues m.1) * U i m.1) from
      e.symm.sum_comp (fun m : {m : Fin n // P m} =>
        (Real.sqrt (hG_herm.eigenvalues m.1) * U j m.1) *
        (Real.sqrt (hG_herm.eigenvalues m.1) * U i m.1))]
    have hsub :
        (∑ m : {m : Fin n // P m},
          (Real.sqrt (hG_herm.eigenvalues m.1) * U j m.1) *
          (Real.sqrt (hG_herm.eigenvalues m.1) * U i m.1)) =
        ∑ m : Fin n, U i m * (hG_herm.eigenvalues m * U j m) := by
      have hterm : ∀ m : Fin n,
          (if P m then
            (Real.sqrt (hG_herm.eigenvalues m) * U j m) *
            (Real.sqrt (hG_herm.eigenvalues m) * U i m)
          else 0) = U i m * (hG_herm.eigenvalues m * U j m) := by
        intro m
        by_cases hm : P m
        · simp only [hm, ↓reduceIte]
          have hnn : 0 ≤ hG_herm.eigenvalues m := hG_psd.eigenvalues_nonneg m
          calc (Real.sqrt (hG_herm.eigenvalues m) * U j m) *
                (Real.sqrt (hG_herm.eigenvalues m) * U i m)
              = (Real.sqrt (hG_herm.eigenvalues m) * Real.sqrt (hG_herm.eigenvalues m)) *
                  (U i m * U j m) := by ring
            _ = hG_herm.eigenvalues m * (U i m * U j m) := by rw [Real.mul_self_sqrt hnn]
            _ = U i m * (hG_herm.eigenvalues m * U j m) := by ring
        · have hm0 : hG_herm.eigenvalues m = 0 := not_not.mp hm
          simp [hm, hm0]
      have hsum_filt :
          (∑ m : {m : Fin n // P m},
            (Real.sqrt (hG_herm.eigenvalues m.1) * U j m.1) *
            (Real.sqrt (hG_herm.eigenvalues m.1) * U i m.1)) =
          ∑ m ∈ Finset.univ.filter P,
            (Real.sqrt (hG_herm.eigenvalues m) * U j m) *
            (Real.sqrt (hG_herm.eigenvalues m) * U i m) := by
        symm
        exact Finset.sum_subtype (Finset.univ.filter P) (by simp)
          (fun m => (Real.sqrt (hG_herm.eigenvalues m) * U j m) *
            (Real.sqrt (hG_herm.eigenvalues m) * U i m))
      rw [hsum_filt, Finset.sum_filter]
      refine Finset.sum_congr rfl fun m _ => ?_
      exact hterm m
    rw [hsub]
    have hspec := congr_fun (congr_fun hG_herm.spectral_theorem i) j
    simpa [U, Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal_apply,
      RCLike.ofReal_real_eq_id, Function.comp_def, star_trivial, Finset.sum_mul,
      mul_assoc] using hspec.symm
  have hv_sys : IsEquiangularSystem d n α v := by
    refine ⟨hα0.le, hα1, fun i => ?_, fun i j hij => ?_⟩
    · have hnorm2 : ‖v i‖ ^ 2 = 1 := by
        rw [← real_inner_self_eq_norm_sq, hinner_G i i]
        simp [G, seidelGram_apply_diag α S hS i, mul_inv_cancel₀ hα0.ne']
      have hn0 : 0 ≤ ‖v i‖ := norm_nonneg _
      nlinarith
    · rw [hinner_G i j]
      have hGij : G i j = α * (S i j : ℝ) := by
        simp [G, seidelGram_apply_ne α S hij]
      rw [hGij, abs_mul, abs_of_pos hα0]
      rcases hS.offDiag_eq_one_or_neg_one hij with h1 | h1 <;> simp [h1]
  have hGram : seidelGram α S = (1 / α) • gramMatrix v := by
    ext i j
    simp only [gramMatrix, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, hinner_G i j]
    simp only [G, Matrix.smul_apply, smul_eq_mul]
    field_simp [hα0.ne']
  exact ⟨v, hv_sys, hGram⟩

/-- Equivalence between equiangular line systems of cosine `α ∈ (0, 1)` and Seidel matrices
with `(1 / α) I + S` positive semidefinite of rank at most `d`. -/
theorem hasEquiangularLinesWithAngle_iff_seidel {d n : ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    HasEquiangularLinesWithAngle d n α ↔
      ∃ S : Matrix (Fin n) (Fin n) ℤ,
        IsSeidelMatrix S ∧ (seidelGram α S).PosSemidef ∧ (seidelGram α S).rank ≤ d := by
  constructor
  · rintro ⟨v, hv⟩
    rcases equiangularSystem_to_seidel hv hα0 with ⟨S, hS, _, hPSD, hrank⟩
    exact ⟨S, hS, hPSD, hrank⟩
  · rintro ⟨S, hS, hPSD, hrank⟩
    rcases seidel_to_equiangularSystem hS hα0 hα1 hPSD hrank with ⟨v, hv, _⟩
    exact ⟨v, hv⟩

/-- The characteristic polynomial of `(1 / α) I + S` is `χ_S(X - 1 / α)`. -/
theorem seidelGram_charpoly {n : ℕ} (α : ℝ) (S : Matrix (Fin n) (Fin n) ℤ) :
    (seidelGram α S).charpoly =
      (S.map (Int.cast : ℤ → ℝ)).charpoly.comp (X - C (1 / α)) := by
  have h : seidelGram α S =
      S.map (Int.cast : ℤ → ℝ) - Matrix.scalar (Fin n) (-(1 / α)) := by
    ext i j
    by_cases hij : i = j <;> simp [seidelGram, hij, sub_eq_add_neg, add_comm]
  rw [h, Matrix.charpoly_sub_scalar, map_neg, sub_eq_add_neg]

/-- For a real symmetric matrix `M`, `X ^ (n - M.rank)` divides `M.charpoly`. -/
theorem pow_sub_rank_dvd_charpoly {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.IsHermitian) :
    X ^ (n - M.rank) ∣ M.charpoly := by
  rw [hM.charpoly_eq, hM.rank_eq_card_non_zero_eigs]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  have hcard :
      (Finset.univ.filter (fun i : Fin n => hM.eigenvalues i = 0)).card =
        n - Fintype.card {i : Fin n // hM.eigenvalues i ≠ 0} := by
    have hcomp := Fintype.card_subtype_compl (fun i : Fin n => hM.eigenvalues i = 0)
    have hle : Fintype.card {i : Fin n // hM.eigenvalues i = 0} ≤ n := by
      simpa [Fintype.card_fin] using
        Fintype.card_subtype_le (fun i : Fin n => hM.eigenvalues i = 0)
    rw [Fintype.card_fin] at hcomp
    rw [← Fintype.card_subtype]
    have hne : Fintype.card {i : Fin n // ¬hM.eigenvalues i = 0} =
        Fintype.card {i : Fin n // hM.eigenvalues i ≠ 0} := rfl
    omega
  rw [← hcard]
  have hsplit := Finset.prod_filter_mul_prod_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun i : Fin n => hM.eigenvalues i = 0)
    (f := fun i : Fin n => X - C (hM.eigenvalues i))
  rw [← hsplit]
  have hzero : (∏ i ∈ Finset.univ.filter (fun i : Fin n => hM.eigenvalues i = 0),
      (X - C (hM.eigenvalues i))) =
      X ^ (Finset.univ.filter (fun i : Fin n => hM.eigenvalues i = 0)).card := by
    calc (∏ i ∈ Finset.univ.filter (fun i : Fin n => hM.eigenvalues i = 0),
          (X - C (hM.eigenvalues i)))
        = ∏ _i ∈ Finset.univ.filter (fun i : Fin n => hM.eigenvalues i = 0), X := by
          refine Finset.prod_congr rfl fun i hi => ?_
          simp [(Finset.mem_filter.mp hi).2]
      _ = X ^ (Finset.univ.filter (fun i : Fin n => hM.eigenvalues i = 0)).card :=
          Finset.prod_const _
  rw [hzero]
  exact dvd_mul_right _ _

/-- If `(1 / α) I + S` has rank at most `d`, then `(X + 1 / α) ^ (n - d)` divides `χ_S(X)` in `ℝ[X]`. -/
theorem seidelGram_dvd_charpoly_real {d n : ℕ} {α : ℝ} {S : Matrix (Fin n) (Fin n) ℤ}
    (hS : IsSeidelMatrix S) (hrank : (seidelGram α S).rank ≤ d) :
    (X + C (1 / α)) ^ (n - d) ∣ (S.map (Int.cast : ℤ → ℝ)).charpoly := by
  have hdvd : X ^ (n - d) ∣ (seidelGram α S).charpoly :=
    dvd_trans (pow_dvd_pow X (Nat.sub_le_sub_left hrank n))
      (pow_sub_rank_dvd_charpoly (seidelGram_isHermitian α S hS))
  rcases hdvd with ⟨Q, hQ⟩
  refine ⟨Q.comp (X + C (1 / α)), ?_⟩
  have hcomp := congrArg (fun p : ℝ[X] => p.comp (X + C (1 / α))) hQ
  simp only [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp] at hcomp
  rw [seidelGram_charpoly, Polynomial.comp_assoc] at hcomp
  have hcancel : (X - C (1 / α)).comp (X + C (1 / α)) = X := by simp
  rwa [hcancel, Polynomial.comp_X] at hcomp

/-- When `1 / α = k` is an integer, `(X + k) ^ (n - d)` divides `S.charpoly` in `ℤ[X]`. -/
theorem seidelGram_dvd_charpoly_int {d n : ℕ} {k : ℤ} {S : Matrix (Fin n) (Fin n) ℤ}
    (hS : IsSeidelMatrix S) (hk : k ≠ 0)
    (hrank : (seidelGram (1 / (k : ℝ)) S).rank ≤ d) :
    (X + C k) ^ (n - d) ∣ S.charpoly := by
  have hR := seidelGram_dvd_charpoly_real hS hrank
  have h1 : (1 : ℝ) / ((1 : ℝ) / (k : ℝ)) = (k : ℝ) := by
    have hkR : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
    field_simp [hkR]
  rw [h1, show S.map (Int.cast : ℤ → ℝ) = S.map (Int.castRingHom ℝ) from rfl,
    Matrix.charpoly_map] at hR
  have hmap : ((X + C k) ^ (n - d)).map (Int.castRingHom ℝ) ∣
      S.charpoly.map (Int.castRingHom ℝ) := by
    simpa [Polynomial.map_pow] using hR
  exact (Polynomial.map_dvd_map (Int.castRingHom ℝ) Int.cast_injective
    ((Polynomial.monic_X_add_C k).pow _)).mp hmap

end EquiangularLines

end
