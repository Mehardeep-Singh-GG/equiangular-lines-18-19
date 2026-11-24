module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Equiangular Lines in Euclidean Space

This module defines the geometric problem of equiangular lines in `ℝ^d` (`EuclideanSpace ℝ (Fin d)`)
and establishes basic equivalences with distinct-line formulations and orthogonality bounds.
-/

@[expose] public section

namespace EquiangularLines

open scoped InnerProductSpace

/-- A family `v : Fin n → EuclideanSpace ℝ (Fin d)` of unit vectors forms an equiangular system
with common cosine `α ∈ [0, 1)` if `|⟪v i, v j⟫_ℝ| = α` for all distinct indices `i ≠ j`. -/
def IsEquiangularSystem (d n : ℕ) (α : ℝ) (v : Fin n → EuclideanSpace ℝ (Fin d)) : Prop :=
  0 ≤ α ∧ α < 1 ∧ (∀ i, ‖v i‖ = 1) ∧ (∀ i j, i ≠ j → |⟪v i, v j⟫_ℝ| = α)

/-- There exists an equiangular system of `n` lines in `ℝ^d`. -/
def HasEquiangularLines (d n : ℕ) : Prop :=
  ∃ α v, IsEquiangularSystem d n α v

/-- There exists an equiangular system of `n` lines in `ℝ^d` with common cosine `α`. -/
def HasEquiangularLinesWithAngle (d n : ℕ) (α : ℝ) : Prop :=
  ∃ v, IsEquiangularSystem d n α v

lemma abs_inner_le_one_of_unit {d : ℕ} {u w : EuclideanSpace ℝ (Fin d)}
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) : |⟪u, w⟫_ℝ| ≤ 1 := by
  calc
    |⟪u, w⟫_ℝ| ≤ ‖u‖ * ‖w‖ := abs_real_inner_le_norm u w
    _ = 1 := by rw [hu, hw, mul_one]

lemma abs_inner_eq_one_iff {d : ℕ} {u w : EuclideanSpace ℝ (Fin d)}
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) :
    |⟪u, w⟫_ℝ| = 1 ↔ u = w ∨ u = -w := by
  constructor
  · intro h
    rcases abs_eq (zero_le_one' ℝ) |>.mp h with hpos | hneg
    · left
      have hsq : ‖u - w‖ ^ 2 = 0 := by
        rw [norm_sub_sq_real, hu, hw, hpos]
        ring
      exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))
    · right
      have hsq : ‖u + w‖ ^ 2 = 0 := by
        rw [norm_add_sq_real, hu, hw, hneg]
        ring
      exact eq_neg_of_add_eq_zero_left (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))
  · rintro (rfl | rfl)
    · rw [real_inner_self_eq_norm_sq, hu]
      norm_num
    · rw [inner_neg_left, real_inner_self_eq_norm_sq, hw]
      norm_num

lemma span_eq_span_iff_eq_or_eq_neg {d : ℕ} {u w : EuclideanSpace ℝ (Fin d)}
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) :
    Submodule.span ℝ {u} = Submodule.span ℝ {w} ↔ u = w ∨ u = -w := by
  constructor
  · intro hspan
    have hu_mem : u ∈ Submodule.span ℝ {w} := by
      rw [← hspan]
      exact Submodule.subset_span (Set.mem_singleton u)
    rw [Submodule.mem_span_singleton] at hu_mem
    rcases hu_mem with ⟨c, hc⟩
    have hc_norm : |c| = 1 := by
      have h1 : ‖c • w‖ = 1 := hc.symm ▸ hu
      rwa [norm_smul, Real.norm_eq_abs, hw, mul_one] at h1
    rcases abs_eq (zero_le_one' ℝ) |>.mp hc_norm with rfl | rfl
    · left; simpa using hc.symm
    · right; simpa using hc.symm
  · rintro (rfl | rfl)
    · rfl
    · ext x
      simp only [Submodule.mem_span_singleton]
      constructor <;> rintro ⟨c, rfl⟩
      · exact ⟨-c, by simp⟩
      · exact ⟨-c, by simp⟩

/-- For `n ≥ 2`, `α < 1` in `IsEquiangularSystem` is equivalent to distinct spanning vectors
`v i ≠ ±v j`. -/
theorem isEquiangularSystem_iff_ne_pm {d n : ℕ} (hn : 2 ≤ n) (α : ℝ)
    (v : Fin n → EuclideanSpace ℝ (Fin d)) :
    IsEquiangularSystem d n α v ↔
      0 ≤ α ∧ (∀ i, ‖v i‖ = 1) ∧
        (∀ i j, i ≠ j → v i ≠ v j ∧ v i ≠ -v j ∧ |⟪v i, v j⟫_ℝ| = α) := by
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  constructor
  · rintro ⟨hα0, hα1, hnorm, hinner⟩
    refine ⟨hα0, hnorm, fun i j hij => ?_⟩
    have hij_eq := hinner i j hij
    have hne : ¬ (v i = v j ∨ v i = -v j) := by
      rw [← abs_inner_eq_one_iff (hnorm i) (hnorm j), hij_eq]
      exact hα1.ne
    push Not at hne
    exact ⟨hne.1, hne.2, hij_eq⟩
  · rintro ⟨hα0, hnorm, hpair⟩
    refine ⟨hα0, ?_, hnorm, fun i j hij => (hpair i j hij).2.2⟩
    have hle : α ≤ 1 := by
      rw [← (hpair i0 i1 h01).2.2]
      exact abs_inner_le_one_of_unit (hnorm i0) (hnorm i1)
    refine lt_of_le_of_ne hle ?_
    intro hEq
    have h1 : |⟪v i0, v i1⟫_ℝ| = 1 := (hpair i0 i1 h01).2.2.trans hEq
    rw [abs_inner_eq_one_iff (hnorm i0) (hnorm i1)] at h1
    rcases h1 with h | h
    · exact (hpair i0 i1 h01).1 h
    · exact (hpair i0 i1 h01).2.1 h

/-- For `n ≥ 2`, `α < 1` in `IsEquiangularSystem` is equivalent to distinct 1-dimensional lines
`Submodule.span ℝ {v i} ≠ Submodule.span ℝ {v j}`. -/
theorem isEquiangularSystem_iff_distinct_lines {d n : ℕ} (hn : 2 ≤ n) (α : ℝ)
    (v : Fin n → EuclideanSpace ℝ (Fin d)) :
    IsEquiangularSystem d n α v ↔
      0 ≤ α ∧ (∀ i, ‖v i‖ = 1) ∧
        (∀ i j, i ≠ j →
          Submodule.span ℝ {v i} ≠ Submodule.span ℝ {v j} ∧ |⟪v i, v j⟫_ℝ| = α) := by
  rw [isEquiangularSystem_iff_ne_pm hn]
  refine and_congr_right fun _ => and_congr_right fun hnorm => ?_
  constructor
  · intro h i j hij
    have hp := h i j hij
    refine ⟨?_, hp.2.2⟩
    rw [ne_eq, span_eq_span_iff_eq_or_eq_neg (hnorm i) (hnorm j)]
    exact not_or.mpr ⟨hp.1, hp.2.1⟩
  · intro h i j hij
    have hp := h i j hij
    have hne := hp.1
    rw [ne_eq, span_eq_span_iff_eq_or_eq_neg (hnorm i) (hnorm j), not_or] at hne
    exact ⟨hne.1, hne.2, hp.2⟩

/-- If an equiangular system has cosine `α = 0`, the vectors are orthonormal, hence `n ≤ d`. -/
theorem card_le_dim_of_alpha_zero {d n : ℕ} {v : Fin n → EuclideanSpace ℝ (Fin d)}
    (hv : IsEquiangularSystem d n 0 v) : n ≤ d := by
  rcases hv with ⟨_, _, hnorm, hinner⟩
  have horth : Orthonormal ℝ v := by
    refine ⟨hnorm, fun {i j} hij => ?_⟩
    exact abs_eq_zero.mp (hinner i j hij)
  have hli : LinearIndependent ℝ v := horth.linearIndependent
  simpa [finrank_euclideanSpace_fin] using hli.fintype_card_le_finrank

/-- Any equiangular system with `n > d` vectors necessarily has strictly positive cosine `0 < α`. -/
theorem alpha_pos_of_dim_lt {d n : ℕ} {α : ℝ} {v : Fin n → EuclideanSpace ℝ (Fin d)}
    (hdn : d < n) (hv : IsEquiangularSystem d n α v) : 0 < α := by
  refine lt_of_le_of_ne hv.1 ?_
  intro hzero
  subst hzero
  have hle : n ≤ d := card_le_dim_of_alpha_zero hv
  omega

/-- No equiangular system with `n ≥ 1` exists in dimension `0`. -/
theorem not_isEquiangularSystem_zero_dim {n : ℕ} (hn : 1 ≤ n) {α : ℝ}
    {v : Fin n → EuclideanSpace ℝ (Fin 0)} (hv : IsEquiangularSystem 0 n α v) : False := by
  have h0 := hv.2.2.1 ⟨0, hn⟩
  have hv0 : v ⟨0, hn⟩ = 0 := by ext i; exact Fin.elim0 i
  rw [hv0, norm_zero] at h0
  norm_num at h0

/-- Restriction of an equiangular system along an embedding `Fin m ↪ Fin n`. -/
theorem IsEquiangularSystem.comp_embedding {d n m : ℕ} {α : ℝ}
    {v : Fin n → EuclideanSpace ℝ (Fin d)} (hv : IsEquiangularSystem d n α v)
    (e : Fin m ↪ Fin n) : IsEquiangularSystem d m α (v ∘ e) := by
  rcases hv with ⟨h0, h1, hnorm, hinner⟩
  exact ⟨h0, h1, fun i => hnorm (e i), fun i j hij => hinner (e i) (e j) (e.injective.ne hij)⟩

/-- Sign-flipping vectors preserves `IsEquiangularSystem`. -/
theorem IsEquiangularSystem.sign_flip {d n : ℕ} {α : ℝ}
    {v : Fin n → EuclideanSpace ℝ (Fin d)} (hv : IsEquiangularSystem d n α v)
    (ε : Fin n → ℝ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    IsEquiangularSystem d n α (fun i => ε i • v i) := by
  rcases hv with ⟨h0, h1, hnorm, hinner⟩
  refine ⟨h0, h1, fun i => ?_, fun i j hij => ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, hnorm i, mul_one]
    rcases hε i with h | h <;> simp [h]
  · rw [inner_smul_left, inner_smul_right, abs_mul, abs_mul]
    have hεi : |ε i| = 1 := by rcases hε i with h | h <;> simp [h]
    have hεj : |ε j| = 1 := by rcases hε j with h | h <;> simp [h]
    simpa [hεi, hεj] using hinner i j hij

end EquiangularLines

end
