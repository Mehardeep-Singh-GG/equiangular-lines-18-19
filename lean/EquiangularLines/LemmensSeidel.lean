module

public import EquiangularLines.Seidel
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Lemmens–Seidel Bound (`α = 1 / 3`)

This module proves the Lemmens–Seidel theorem in the range `d ≥ 15`:
any equiangular line system of `n` vectors in `ℝ^d` with cosine `α = 1 / 3` satisfies
`n ≤ 2 * (d - 1)`.

The proof splits into two completely elementary cases on the scaled vectors `u_i = √3 v_i`
(which have `‖u_i‖² = 3` and `⟪u_i, u_j⟫ = ±1` for `i ≠ j`):
1. **Pillar case (`HasPillar`)**: four distinct vectors admit signs summing to `0`.
   Their 3D span decomposes the remaining vectors into 3 orthogonal pillars in `ℝ^(d-3)`;
   either at most 1 pillar is nonempty (`n ≤ 4 + 2(d - 3) = 2(d - 1)`), or Bessel's inequality
   forces each pillar to have at most `4` orthogonal axes (`n ≤ 4 + 8 + 8 + 8 = 28 ≤ 2(d - 1)`).
2. **No-pillar case (`¬ HasPillar`)**: after switching vertex `0` to have `+1` inner products,
   the `-1`-graph `Γ` has no `K_3` and no induced `2 K_2`, so either `Γ` contains an induced `C_5`
   (making `rank(A) ≤ 5`) or `Γ` is a bipartite chain graph (making `dim ker(I - A) ≤ 1`).
   In both subcases `n - d - 1 ≤ dim ker(I - A) ≤ 5`, hence `n ≤ d + 6 ≤ 2(d - 1)` for `d ≥ 8`.
-/

@[expose] public section

namespace EquiangularLines

open Matrix
open scoped InnerProductSpace

section LemmensSeidelHelpers

private lemma linearIndependent_of_pairwise_orthogonal {d m : ℕ}
    {w : Fin m → EuclideanSpace ℝ (Fin d)}
    (hne : ∀ i, w i ≠ 0) (horth : ∀ i j, i ≠ j → ⟪w i, w j⟫_ℝ = 0) :
    LinearIndependent ℝ w := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h0 : ⟪w i, ∑ j : Fin m, c j • w j⟫_ℝ = 0 := by rw [hc, inner_zero_right]
  rw [inner_sum] at h0
  simp_rw [real_inner_smul_right] at h0
  have hsingle : (∑ j : Fin m, c j * ⟪w i, w j⟫_ℝ) = c i * ⟪w i, w i⟫_ℝ := by
    refine Finset.sum_eq_single i (fun j _ hji => ?_) (fun hi => absurd (Finset.mem_univ i) hi)
    rw [horth i j hji.symm, mul_zero]
  rw [hsingle, real_inner_self_eq_norm_sq] at h0
  have hnorm : ‖w i‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne i))
  exact (mul_eq_zero.mp h0).resolve_right hnorm

/-- Bessel's inequality for a finite orthogonal family of vectors of squared norm `2`. -/
private lemma bessel_sq_norm_two {d : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (y : ι → EuclideanSpace ℝ (Fin d))
    (hnorm : ∀ i ∈ s, ⟪y i, y i⟫_ℝ = 2)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪y i, y j⟫_ℝ = 0)
    (z : EuclideanSpace ℝ (Fin d)) :
    ∑ i ∈ s, ⟪z, y i⟫_ℝ ^ 2 ≤ 2 * ⟪z, z⟫_ℝ := by
  let proj : EuclideanSpace ℝ (Fin d) := ∑ i ∈ s, ((1 / 2 : ℝ) * ⟪z, y i⟫_ℝ) • y i
  have hnn : 0 ≤ ⟪z - proj, z - proj⟫_ℝ := real_inner_self_nonneg
  have hzproj : ⟪z, proj⟫_ℝ = (1 / 2 : ℝ) * ∑ i ∈ s, ⟪z, y i⟫_ℝ ^ 2 := by
    simp only [proj, inner_sum, real_inner_smul_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hproj_sq : ⟪proj, proj⟫_ℝ = (1 / 2 : ℝ) * ∑ i ∈ s, ⟪z, y i⟫_ℝ ^ 2 := by
    simp only [proj, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hinner : (∑ j ∈ s, (1 / 2 : ℝ) * ⟪z, y i⟫_ℝ * ((1 / 2 : ℝ) * ⟪z, y j⟫_ℝ * ⟪y i, y j⟫_ℝ)) =
        (1 / 2 : ℝ) * ⟪z, y i⟫_ℝ * ((1 / 2 : ℝ) * ⟪z, y i⟫_ℝ * ⟪y i, y i⟫_ℝ) := by
      refine Finset.sum_eq_single i (fun j hj hji => ?_) (fun hi' => absurd hi hi')
      rw [horth i hi j hj hji.symm]; ring
    have hcomm : (∑ j ∈ s, (1 / 2 : ℝ) * ⟪z, y i⟫_ℝ * ((1 / 2 : ℝ) * ⟪z, y j⟫_ℝ * ⟪y j, y i⟫_ℝ)) =
        ∑ j ∈ s, (1 / 2 : ℝ) * ⟪z, y i⟫_ℝ * ((1 / 2 : ℝ) * ⟪z, y j⟫_ℝ * ⟪y i, y j⟫_ℝ) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [real_inner_comm (y j) (y i)]
    rw [hcomm, hinner, hnorm i hi]
    ring
  have hexpand : ⟪z - proj, z - proj⟫_ℝ = ⟪z, z⟫_ℝ - 2 * ⟪z, proj⟫_ℝ + ⟪proj, proj⟫_ℝ := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm proj z]
    ring
  linarith

/-- Four vectors in a `1/3`-equiangular system form a pillar if signed copies sum to `0`. -/
private def HasPillar {d n : ℕ} (u : Fin n → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∃ a b c e : Fin n, a ≠ b ∧ a ≠ c ∧ a ≠ e ∧ b ≠ c ∧ b ≠ e ∧ c ≠ e ∧
    ∃ sa sb sc se : ℝ,
      (sa = 1 ∨ sa = -1) ∧ (sb = 1 ∨ sb = -1) ∧ (sc = 1 ∨ sc = -1) ∧ (se = 1 ∨ se = -1) ∧
      sa • u a + sb • u b + sc • u c + se • u e = 0

/-- Pillar case (`HasPillar u`): `n ≤ 2 * (d - 1)` whenever `15 ≤ d`. -/
private lemma lemmens_seidel_pillar_case {d n : ℕ} (hd : 15 ≤ d)
    {u : Fin n → EuclideanSpace ℝ (Fin d)}
    (hu_norm : ∀ i, ⟪u i, u i⟫_ℝ = 3)
    (hu_inner : ∀ i j, i ≠ j → ⟪u i, u j⟫_ℝ = 1 ∨ ⟪u i, u j⟫_ℝ = -1)
    (hpillar : HasPillar u) :
    n ≤ 2 * (d - 1) := by
  rcases hpillar with ⟨a, b, c, e, hab, hac, hae, hbc, hbe, hce,
    sa, sb, sc, se, hsa, hsb, hsc, hse, hsum⟩
  let u0 := sa • u a
  let u1 := sb • u b
  let u2 := sc • u c
  let u3 := se • u e
  have hu0_norm : ⟪u0, u0⟫_ℝ = 3 := by
    simp only [u0, real_inner_smul_left, real_inner_smul_right, hu_norm a]
    rcases hsa with h | h <;> simp [h]
  have hu1_norm : ⟪u1, u1⟫_ℝ = 3 := by
    simp only [u1, real_inner_smul_left, real_inner_smul_right, hu_norm b]
    rcases hsb with h | h <;> simp [h]
  have hu2_norm : ⟪u2, u2⟫_ℝ = 3 := by
    simp only [u2, real_inner_smul_left, real_inner_smul_right, hu_norm c]
    rcases hsc with h | h <;> simp [h]
  have hu3_norm : ⟪u3, u3⟫_ℝ = 3 := by
    simp only [u3, real_inner_smul_left, real_inner_smul_right, hu_norm e]
    rcases hse with h | h <;> simp [h]
  have hsign_inner : ∀ {p q : Fin n} {sp sq : ℝ},
      (sp = 1 ∨ sp = -1) → (sq = 1 ∨ sq = -1) → p ≠ q →
      ⟪sp • u p, sq • u q⟫_ℝ = 1 ∨ ⟪sp • u p, sq • u q⟫_ℝ = -1 := by
    intro p q sp sq hsp hsq hpq
    simp only [real_inner_smul_left, real_inner_smul_right]
    rcases hsp with rfl | rfl <;> rcases hsq with rfl | rfl <;>
      rcases hu_inner p q hpq with h | h <;> simp [h]
  have h01_pm := hsign_inner hsa hsb hab
  have h02_pm := hsign_inner hsa hsc hac
  have h03_pm := hsign_inner hsa hse hae
  have h12_pm := hsign_inner hsb hsc hbc
  have h13_pm := hsign_inner hsb hse hbe
  have h23_pm := hsign_inner hsc hse hce
  have hzero_sq : ⟪u0 + u1 + u2 + u3, u0 + u1 + u2 + u3⟫_ℝ = 0 := by
    rw [show u0 + u1 + u2 + u3 = 0 from hsum, inner_zero_left]
  have hexp : ⟪u0 + u1 + u2 + u3, u0 + u1 + u2 + u3⟫_ℝ =
      ⟪u0, u0⟫_ℝ + ⟪u1, u1⟫_ℝ + ⟪u2, u2⟫_ℝ + ⟪u3, u3⟫_ℝ +
      2 * (⟪u0, u1⟫_ℝ + ⟪u0, u2⟫_ℝ + ⟪u0, u3⟫_ℝ + ⟪u1, u2⟫_ℝ + ⟪u1, u3⟫_ℝ + ⟪u2, u3⟫_ℝ) := by
    simp only [inner_add_left, inner_add_right]
    rw [real_inner_comm u1 u0, real_inner_comm u2 u0, real_inner_comm u3 u0,
      real_inner_comm u2 u1, real_inner_comm u3 u1, real_inner_comm u3 u2]
    ring
  have hge : ∀ {x : ℝ}, x = 1 ∨ x = -1 → -1 ≤ x := by rintro x (rfl | rfl) <;> norm_num
  have h01 : ⟪u0, u1⟫_ℝ = -1 := by
    rcases h01_pm with h | h <;>
      linarith [hge h02_pm, hge h03_pm, hge h12_pm, hge h13_pm, hge h23_pm]
  have h02 : ⟪u0, u2⟫_ℝ = -1 := by
    rcases h02_pm with h | h <;>
      linarith [hge h01_pm, hge h03_pm, hge h12_pm, hge h13_pm, hge h23_pm]
  have h03 : ⟪u0, u3⟫_ℝ = -1 := by
    rcases h03_pm with h | h <;>
      linarith [hge h01_pm, hge h02_pm, hge h12_pm, hge h13_pm, hge h23_pm]
  have h12 : ⟪u1, u2⟫_ℝ = -1 := by
    rcases h12_pm with h | h <;>
      linarith [hge h01_pm, hge h02_pm, hge h03_pm, hge h13_pm, hge h23_pm]
  have h13 : ⟪u1, u3⟫_ℝ = -1 := by
    rcases h13_pm with h | h <;>
      linarith [hge h01_pm, hge h02_pm, hge h03_pm, hge h12_pm, hge h23_pm]
  have h23 : ⟪u2, u3⟫_ℝ = -1 := by
    rcases h23_pm with h | h <;>
      linarith [hge h01_pm, hge h02_pm, hge h03_pm, hge h12_pm, hge h13_pm]
  let E : Fin 3 → EuclideanSpace ℝ (Fin d) := ![u0 + u1, u0 + u2, u0 + u3]
  have hE0 : E 0 = u0 + u1 := rfl
  have hE1 : E 1 = u0 + u2 := rfl
  have hE2 : E 2 = u0 + u3 := rfl
  have h10 : ⟪u1, u0⟫_ℝ = -1 := by rw [real_inner_comm]; exact h01
  have h20 : ⟪u2, u0⟫_ℝ = -1 := by rw [real_inner_comm]; exact h02
  have h30 : ⟪u3, u0⟫_ℝ = -1 := by rw [real_inner_comm]; exact h03
  have h21 : ⟪u2, u1⟫_ℝ = -1 := by rw [real_inner_comm]; exact h12
  have h31 : ⟪u3, u1⟫_ℝ = -1 := by rw [real_inner_comm]; exact h13
  have h32 : ⟪u3, u2⟫_ℝ = -1 := by rw [real_inner_comm]; exact h23
  have hE_norm : ∀ t : Fin 3, ⟪E t, E t⟫_ℝ = 4 := by
    intro t
    fin_cases t
    · change ⟪E 0, E 0⟫_ℝ = 4
      rw [hE0, inner_add_left, inner_add_right, inner_add_right,
        hu0_norm, hu1_norm, h01, h10]
      ring
    · change ⟪E 1, E 1⟫_ℝ = 4
      rw [hE1, inner_add_left, inner_add_right, inner_add_right,
        hu0_norm, hu2_norm, h02, h20]
      ring
    · change ⟪E 2, E 2⟫_ℝ = 4
      rw [hE2, inner_add_left, inner_add_right, inner_add_right,
        hu0_norm, hu3_norm, h03, h30]
      ring
  have hE_orth : ∀ s t : Fin 3, s ≠ t → ⟪E s, E t⟫_ℝ = 0 := by
    intro s t hst
    fin_cases s <;> fin_cases t <;>
      try exact absurd rfl hst
    · change ⟪E 0, E 1⟫_ℝ = 0
      rw [hE0, hE1, inner_add_left, inner_add_right, inner_add_right,
        hu0_norm, h02, h10, h12]
      ring
    · change ⟪E 0, E 2⟫_ℝ = 0
      rw [hE0, hE2, inner_add_left, inner_add_right, inner_add_right,
        hu0_norm, h03, h10, h13]
      ring
    · change ⟪E 1, E 0⟫_ℝ = 0
      rw [hE1, hE0, inner_add_left, inner_add_right, inner_add_right,
        hu0_norm, h01, h20, h21]
      ring
    · change ⟪E 1, E 2⟫_ℝ = 0
      rw [hE1, hE2, inner_add_left, inner_add_right, inner_add_right,
        hu0_norm, h03, h20, h23]
      ring
    · change ⟪E 2, E 0⟫_ℝ = 0
      rw [hE2, hE0, inner_add_left, inner_add_right, inner_add_right,
        hu0_norm, h01, h30, h31]
      ring
    · change ⟪E 2, E 1⟫_ℝ = 0
      rw [hE2, hE1, inner_add_left, inner_add_right, inner_add_right,
        hu0_norm, h02, h30, h32]
      ring
  let P : Finset (Fin n) := {a, b, c, e}
  have hP_card : P.card = 4 := by
    simp only [P]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hce]
    · simp [hbc, hbe]
    · simp [hab, hac, hae]
  let R : Finset (Fin n) := Finset.univ \ P
  have hR_card : P.card + R.card = n := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ P), Finset.card_univ, Fintype.card_fin]
    have hle : P.card ≤ n := by
      simpa [Fintype.card_fin] using Finset.card_le_univ P
    omega
  -- Choose canonical sign for each i ∈ R so ⟪w i, u0⟫ = 1
  let sgn : Fin n → ℝ := fun i => if ⟪u i, u0⟫_ℝ = 1 then 1 else -1
  let w : Fin n → EuclideanSpace ℝ (Fin d) := fun i => sgn i • u i
  have hw_norm : ∀ i, ⟪w i, w i⟫_ℝ = 3 := by
    intro i
    simp only [w, real_inner_smul_left, real_inner_smul_right, hu_norm i]
    by_cases h : ⟪u i, u0⟫_ℝ = 1 <;> simp [sgn, h]
  have hw_inner_pm : ∀ i j, i ≠ j → ⟪w i, w j⟫_ℝ = 1 ∨ ⟪w i, w j⟫_ℝ = -1 := by
    intro i j hij
    have hs : ∀ k, sgn k = 1 ∨ sgn k = -1 := fun k => by
      by_cases h : ⟪u k, u0⟫_ℝ = 1 <;> simp [sgn, h]
    exact hsign_inner (hs i) (hs j) hij
  have hw_u0 : ∀ i ∈ R, ⟪w i, u0⟫_ℝ = 1 := by
    intro i hi
    have hne : i ≠ a := by
      intro h; subst h; exact (Finset.mem_sdiff.mp hi).2 (by simp [P])
    have hpm : ⟪u i, u0⟫_ℝ = 1 ∨ ⟪u i, u0⟫_ℝ = -1 := by
      simpa [u0, real_inner_smul_right] using
        hsign_inner (Or.inl rfl) hsa hne
    by_cases h : ⟪u i, u0⟫_ℝ = 1
    · simp [w, sgn, h]
    · have hneg : ⟪u i, u0⟫_ℝ = -1 := hpm.resolve_left h
      have hs : sgn i = -1 := by simp only [sgn, h, ↓reduceIte]
      rw [show w i = sgn i • u i from rfl, hs, neg_one_smul, inner_neg_left, hneg]
      norm_num
  have hw_u123_pm : ∀ i ∈ R,
      (⟪w i, u1⟫_ℝ = 1 ∨ ⟪w i, u1⟫_ℝ = -1) ∧
      (⟪w i, u2⟫_ℝ = 1 ∨ ⟪w i, u2⟫_ℝ = -1) ∧
      (⟪w i, u3⟫_ℝ = 1 ∨ ⟪w i, u3⟫_ℝ = -1) := by
    intro i hi
    have hia : i ≠ a := fun h => (Finset.mem_sdiff.mp hi).2 (by subst h; simp [P])
    have hib : i ≠ b := fun h => (Finset.mem_sdiff.mp hi).2 (by subst h; simp [P])
    have hic : i ≠ c := fun h => (Finset.mem_sdiff.mp hi).2 (by subst h; simp [P])
    have hie : i ≠ e := fun h => (Finset.mem_sdiff.mp hi).2 (by subst h; simp [P])
    have hs : sgn i = 1 ∨ sgn i = -1 := by
      by_cases h : ⟪u i, u0⟫_ℝ = 1 <;> simp [sgn, h]
    exact ⟨hsign_inner hs hsb hib, hsign_inner hs hsc hic, hsign_inner hs hse hie⟩
  let cls : Fin n → Fin 3 := fun i =>
    if ⟪w i, u1⟫_ℝ = 1 then 0 else if ⟪w i, u2⟫_ℝ = 1 then 1 else 2
  have hcls_inner : ∀ i ∈ R,
      (cls i = 0 ∧ ⟪w i, E 0⟫_ℝ = 2 ∧ ⟪w i, E 1⟫_ℝ = 0 ∧ ⟪w i, E 2⟫_ℝ = 0) ∨
      (cls i = 1 ∧ ⟪w i, E 0⟫_ℝ = 0 ∧ ⟪w i, E 1⟫_ℝ = 2 ∧ ⟪w i, E 2⟫_ℝ = 0) ∨
      (cls i = 2 ∧ ⟪w i, E 0⟫_ℝ = 0 ∧ ⟪w i, E 1⟫_ℝ = 0 ∧ ⟪w i, E 2⟫_ℝ = 2) := by
    intro i hi
    have hsum0 : ⟪w i, u0⟫_ℝ + ⟪w i, u1⟫_ℝ + ⟪w i, u2⟫_ℝ + ⟪w i, u3⟫_ℝ = 0 := by
      rw [← inner_add_right, ← inner_add_right, ← inner_add_right]
      rw [show u0 + u1 + u2 + u3 = 0 from hsum, inner_zero_right]
    have h0 := hw_u0 i hi
    rcases hw_u123_pm i hi with ⟨h1, h2, h3⟩
    have hE0 : ⟪w i, E 0⟫_ℝ = ⟪w i, u0⟫_ℝ + ⟪w i, u1⟫_ℝ := by
      simp [E, inner_add_right]
    have hE1 : ⟪w i, E 1⟫_ℝ = ⟪w i, u0⟫_ℝ + ⟪w i, u2⟫_ℝ := by
      simp [E, inner_add_right]
    have hE2 : ⟪w i, E 2⟫_ℝ = ⟪w i, u0⟫_ℝ + ⟪w i, u3⟫_ℝ := by
      simp [E, inner_add_right]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3
    · exfalso; linarith
    · exfalso; linarith
    · exfalso; linarith
    · left
      refine ⟨by simp [cls, h1], ?_, ?_, ?_⟩ <;> linarith
    · exfalso; linarith
    · right; left
      have h1' : ⟪w i, u1⟫_ℝ ≠ 1 := by linarith
      refine ⟨by simp [cls, h1', h2], ?_, ?_, ?_⟩ <;> linarith
    · right; right
      have h1' : ⟪w i, u1⟫_ℝ ≠ 1 := by linarith
      have h2' : ⟪w i, u2⟫_ℝ ≠ 1 := by linarith
      refine ⟨by simp [cls, h1', h2'], ?_, ?_, ?_⟩ <;> linarith
    · exfalso; linarith
  let y : Fin n → EuclideanSpace ℝ (Fin d) := fun i => w i - (1 / 2 : ℝ) • E (cls i)
  have hy_E : ∀ i ∈ R, ∀ t : Fin 3, ⟪y i, E t⟫_ℝ = 0 := by
    intro i hi t
    rcases hcls_inner i hi with ⟨hc, ha0, ha1, ha2⟩ | ⟨hc, hb0, hb1, hb2⟩ | ⟨hc, hc0, hc1, hc2⟩
    · fin_cases t <;> simp only [y, hc, inner_sub_left, real_inner_smul_left]
      · change ⟪w i, E 0⟫_ℝ - 1 / 2 * ⟪E 0, E 0⟫_ℝ = 0
        rw [ha0, hE_norm 0]; ring
      · change ⟪w i, E 1⟫_ℝ - 1 / 2 * ⟪E 0, E 1⟫_ℝ = 0
        rw [ha1, hE_orth 0 1 (by decide)]; ring
      · change ⟪w i, E 2⟫_ℝ - 1 / 2 * ⟪E 0, E 2⟫_ℝ = 0
        rw [ha2, hE_orth 0 2 (by decide)]; ring
    · fin_cases t <;> simp only [y, hc, inner_sub_left, real_inner_smul_left]
      · change ⟪w i, E 0⟫_ℝ - 1 / 2 * ⟪E 1, E 0⟫_ℝ = 0
        rw [hb0, hE_orth 1 0 (by decide)]; ring
      · change ⟪w i, E 1⟫_ℝ - 1 / 2 * ⟪E 1, E 1⟫_ℝ = 0
        rw [hb1, hE_norm 1]; ring
      · change ⟪w i, E 2⟫_ℝ - 1 / 2 * ⟪E 1, E 2⟫_ℝ = 0
        rw [hb2, hE_orth 1 2 (by decide)]; ring
    · fin_cases t <;> simp only [y, hc, inner_sub_left, real_inner_smul_left]
      · change ⟪w i, E 0⟫_ℝ - 1 / 2 * ⟪E 2, E 0⟫_ℝ = 0
        rw [hc0, hE_orth 2 0 (by decide)]; ring
      · change ⟪w i, E 1⟫_ℝ - 1 / 2 * ⟪E 2, E 1⟫_ℝ = 0
        rw [hc1, hE_orth 2 1 (by decide)]; ring
      · change ⟪w i, E 2⟫_ℝ - 1 / 2 * ⟪E 2, E 2⟫_ℝ = 0
        rw [hc2, hE_norm 2]; ring
  have hy_norm : ∀ i ∈ R, ⟪y i, y i⟫_ℝ = 2 := by
    intro i hi
    have hwe : ⟪w i, E (cls i)⟫_ℝ = 2 := by
      rcases hcls_inner i hi with ⟨hc, ha0, _, _⟩ | ⟨hc, _, hb1, _⟩ | ⟨hc, _, _, hc2⟩
      · simp [hc, ha0]
      · simp [hc, hb1]
      · simp [hc, hc2]
    have h1 : ⟪w i, (1 / 2 : ℝ) • E (cls i)⟫_ℝ = 1 := by
      rw [real_inner_smul_right, hwe]; ring
    have h2 : ⟪(1 / 2 : ℝ) • E (cls i), w i⟫_ℝ = 1 := by
      rw [real_inner_smul_left, real_inner_comm, hwe]; ring
    have h3 : ⟪(1 / 2 : ℝ) • E (cls i), (1 / 2 : ℝ) • E (cls i)⟫_ℝ = 1 := by
      rw [real_inner_smul_left, real_inner_smul_right, hE_norm]; ring
    rw [show y i = w i - (1 / 2 : ℝ) • E (cls i) from rfl,
      inner_sub_left, inner_sub_right, inner_sub_right, hw_norm i, h1, h2, h3]
    norm_num
  have hy_inner_eq : ∀ i ∈ R, ∀ j ∈ R, cls i = cls j →
      ⟪y i, y j⟫_ℝ = ⟪w i, w j⟫_ℝ - 1 := by
    intro i hi j hj hcij
    have hwi : ⟪w i, E (cls j)⟫_ℝ = 2 := by
      rw [← hcij]
      rcases hcls_inner i hi with ⟨hc, ha0, _, _⟩ | ⟨hc, _, hb1, _⟩ | ⟨hc, _, _, hc2⟩
      · simp [hc, ha0]
      · simp [hc, hb1]
      · simp [hc, hc2]
    have hwj : ⟪E (cls i), w j⟫_ℝ = 2 := by
      rw [real_inner_comm, hcij]
      rcases hcls_inner j hj with ⟨hc, ha0, _, _⟩ | ⟨hc, _, hb1, _⟩ | ⟨hc, _, _, hc2⟩
      · simp [hc, ha0]
      · simp [hc, hb1]
      · simp [hc, hc2]
    have h1 : ⟪w i, (1 / 2 : ℝ) • E (cls j)⟫_ℝ = 1 := by
      rw [real_inner_smul_right, hwi]; ring
    have h2 : ⟪(1 / 2 : ℝ) • E (cls i), w j⟫_ℝ = 1 := by
      rw [real_inner_smul_left, hwj]; ring
    have h3 : ⟪(1 / 2 : ℝ) • E (cls i), (1 / 2 : ℝ) • E (cls j)⟫_ℝ = 1 := by
      rw [real_inner_smul_left, real_inner_smul_right, hcij, hE_norm]; ring
    rw [show y i = w i - (1 / 2 : ℝ) • E (cls i) from rfl,
      show y j = w j - (1 / 2 : ℝ) • E (cls j) from rfl,
      inner_sub_left, inner_sub_right, inner_sub_right, h1, h2, h3]
    ring
  have hy_inner_ne : ∀ i ∈ R, ∀ j ∈ R, cls i ≠ cls j →
      ⟪y i, y j⟫_ℝ = ⟪w i, w j⟫_ℝ := by
    intro i hi j hj hcij
    have hwi : ⟪w i, E (cls j)⟫_ℝ = 0 := by
      rcases hcls_inner i hi with ⟨hi', ha0, ha1, ha2⟩ | ⟨hi', ha0, ha1, ha2⟩ | ⟨hi', ha0, ha1, ha2⟩ <;>
        rcases hcls_inner j hj with ⟨hj', _, _, _⟩ | ⟨hj', _, _, _⟩ | ⟨hj', _, _, _⟩ <;>
        simp only [hi', hj'] at hcij ⊢ <;>
        first | exact absurd rfl hcij | exact ha0 | exact ha1 | exact ha2
    have hwj : ⟪E (cls i), w j⟫_ℝ = 0 := by
      rw [real_inner_comm]
      rcases hcls_inner i hi with ⟨hi', _, _, _⟩ | ⟨hi', _, _, _⟩ | ⟨hi', _, _, _⟩ <;>
        rcases hcls_inner j hj with ⟨hj', hb0, hb1, hb2⟩ | ⟨hj', hb0, hb1, hb2⟩ | ⟨hj', hb0, hb1, hb2⟩ <;>
        simp only [hi', hj'] at hcij ⊢ <;>
        first | exact absurd rfl hcij | exact hb0 | exact hb1 | exact hb2
    have h1 : ⟪w i, (1 / 2 : ℝ) • E (cls j)⟫_ℝ = 0 := by
      rw [real_inner_smul_right, hwi, mul_zero]
    have h2 : ⟪(1 / 2 : ℝ) • E (cls i), w j⟫_ℝ = 0 := by
      rw [real_inner_smul_left, hwj, mul_zero]
    have h3 : ⟪(1 / 2 : ℝ) • E (cls i), (1 / 2 : ℝ) • E (cls j)⟫_ℝ = 0 := by
      rw [real_inner_smul_left, real_inner_smul_right, hE_orth (cls i) (cls j) hcij]; ring
    rw [show y i = w i - (1 / 2 : ℝ) • E (cls i) from rfl,
      show y j = w j - (1 / 2 : ℝ) • E (cls j) from rfl,
      inner_sub_left, inner_sub_right, inner_sub_right, h1, h2, h3]
    ring
  let C : Fin 3 → Finset (Fin n) := fun t => R.filter (fun i => cls i = t)
  have hC_sum : (C 0).card + (C 1).card + (C 2).card = R.card := by
    have hsum_cls : R.card = ∑ t ∈ (Finset.univ : Finset (Fin 3)), (C t).card :=
      Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ (cls i))
    rw [hsum_cls, Fin.sum_univ_three]
  let B : Fin 3 → Finset (Fin n) := fun t =>
    (C t).filter (fun i => ∀ j ∈ C t, j < i → y j ≠ -y i)
  have hB_orth : ∀ t : Fin 3, ∀ i ∈ B t, ∀ j ∈ B t, i ≠ j → ⟪y i, y j⟫_ℝ = 0 := by
    intro t i hi j hj hij
    have hiR : i ∈ R := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
    have hjR : j ∈ R := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1
    have hci : cls i = t := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
    have hcj : cls j = t := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
    have h_inner := hy_inner_eq i hiR j hjR (hci.trans hcj.symm)
    rcases hw_inner_pm i j hij with h1 | h1
    · linarith
    · exfalso
      have hcomm : ⟪y j, y i⟫_ℝ = ⟪y i, y j⟫_ℝ := real_inner_comm _ _
      have hsq : ⟪y i + y j, y i + y j⟫_ℝ = 0 := by
        rw [inner_add_left, inner_add_right, inner_add_right,
          hy_norm i hiR, hy_norm j hjR, hcomm, h_inner, h1]
        ring
      have hy_eq : y j = -y i := by
        have h0 : y i + y j = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp
          (by rwa [← real_inner_self_eq_norm_sq]))
        exact eq_neg_of_add_eq_zero_right h0
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · have hne := (Finset.mem_filter.mp hj).2 i (Finset.mem_filter.mp hi).1 hlt
        exact hne (by rw [hy_eq, neg_neg])
      · have hne := (Finset.mem_filter.mp hi).2 j (Finset.mem_filter.mp hj).1 hgt
        exact hne hy_eq
  have hC_le_two_B : ∀ t : Fin 3, (C t).card ≤ 2 * (B t).card := by
    intro t
    have hsplit : (C t).card = (B t).card + (C t \ B t).card := by
      have hsub : B t ⊆ C t := Finset.filter_subset _ _
      rw [Finset.card_sdiff_of_subset hsub]
      have := Finset.card_le_card hsub
      omega
    rw [hsplit]
    suffices hdiff : (C t \ B t).card ≤ (B t).card by omega
    have hpartner : ∀ i ∈ C t \ B t, ∃ j ∈ B t, y j = -y i := by
      intro i hi
      have hiC : i ∈ C t := (Finset.mem_sdiff.mp hi).1
      have hiNB : i ∉ B t := (Finset.mem_sdiff.mp hi).2
      simp only [B, Finset.mem_filter, hiC, true_and, not_forall, not_not] at hiNB
      rcases hiNB with ⟨j, hjC, hjlt, hyji⟩
      refine ⟨j, Finset.mem_filter.mpr ⟨hjC, fun k hkC hkl hykj => ?_⟩, hyji⟩
      have hki : k ≠ i := (lt_trans hkl hjlt).ne
      have hkR : k ∈ R := (Finset.mem_filter.mp hkC).1
      have hiR : i ∈ R := (Finset.mem_filter.mp hiC).1
      have hck : cls k = t := (Finset.mem_filter.mp hkC).2
      have hci : cls i = t := (Finset.mem_filter.mp hiC).2
      have hyki : y k = y i := by rw [hykj, hyji, neg_neg]
      have h2 : ⟪y k, y i⟫_ℝ = 2 := by rw [hyki, hy_norm i hiR]
      have h1 : ⟪y k, y i⟫_ℝ = ⟪w k, w i⟫_ℝ - 1 := hy_inner_eq k hkR i hiR (hck.trans hci.symm)
      rcases hw_inner_pm k i hki with hw | hw <;> linarith
    choose partner hpartner_mem hpartner_eq using hpartner
    refine Finset.card_le_card_of_injOn
      (fun i => if hi : i ∈ C t \ B t then partner i hi else i) ?_ ?_
    · intro i hi
      simp only [Finset.mem_coe] at hi ⊢
      simp only [hi, ↓reduceDIte]
      exact hpartner_mem i hi
    · intro i1 hi1 i2 hi2 heq
      simp only [Finset.mem_coe] at hi1 hi2
      simp only [hi1, hi2, ↓reduceDIte] at heq
      by_contra hne
      have h1R : i1 ∈ R := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi1).1).1
      have h2R : i2 ∈ R := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi2).1).1
      have hc1 : cls i1 = t := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi1).1).2
      have hc2 : cls i2 = t := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi2).1).2
      have hy_same : y i1 = y i2 := by
        have hp1 := hpartner_eq i1 hi1
        have hp2 := hpartner_eq i2 hi2
        rw [← heq] at hp2
        exact neg_inj.mp (hp1.symm.trans hp2)
      have h2 : ⟪y i1, y i2⟫_ℝ = 2 := by rw [hy_same, hy_norm i2 h2R]
      have h1 : ⟪y i1, y i2⟫_ℝ = ⟪w i1, w i2⟫_ℝ - 1 :=
        hy_inner_eq i1 h1R i2 h2R (hc1.trans hc2.symm)
      rcases hw_inner_pm i1 i2 hne with hw | hw <;> linarith
  have hB_le_dim : ∀ t : Fin 3, (B t).card ≤ d - 3 := by
    intro t
    let eB : Fin (B t).card ≃ B t :=
      (finCongr (Fintype.card_coe (B t))).symm.trans (Fintype.equivFin (B t)).symm
    let basisVecs : Fin 3 ⊕ Fin (B t).card → EuclideanSpace ℝ (Fin d) :=
      Sum.elim E (fun k => y (eB k).1)
    have hli : LinearIndependent ℝ basisVecs := by
      let eqv : Fin 3 ⊕ Fin (B t).card ≃ Fin (3 + (B t).card) := finSumFinEquiv
      have hli' : LinearIndependent ℝ (basisVecs ∘ eqv.symm) := by
        refine linearIndependent_of_pairwise_orthogonal ?_ ?_
        · intro idx h0
          rcases hidx : eqv.symm idx with a | k
          · have h4 : ⟪E a, E a⟫_ℝ = 4 := hE_norm a
            simp only [Function.comp_apply, hidx, basisVecs, Sum.elim_inl] at h0
            rw [h0, inner_zero_left] at h4
            norm_num at h4
          · have hkR : (eB k).1 ∈ R :=
              (Finset.mem_filter.mp (Finset.mem_filter.mp (eB k).2).1).1
            have h2 : ⟪y (eB k).1, y (eB k).1⟫_ℝ = 2 := hy_norm _ hkR
            simp only [Function.comp_apply, hidx, basisVecs, Sum.elim_inr] at h0
            rw [h0, inner_zero_left] at h2
            norm_num at h2
        · intro idx1 idx2 hne
          have hne' : eqv.symm idx1 ≠ eqv.symm idx2 := eqv.symm.injective.ne hne
          rcases h1 : eqv.symm idx1 with a1 | k1 <;> rcases h2 : eqv.symm idx2 with a2 | k2 <;>
            simp only [Function.comp_apply, h1, h2, basisVecs, Sum.elim_inl, Sum.elim_inr]
          · exact hE_orth a1 a2 (by simpa [h1, h2] using hne')
          · have hk2R : (eB k2).1 ∈ R :=
              (Finset.mem_filter.mp (Finset.mem_filter.mp (eB k2).2).1).1
            rw [real_inner_comm]
            exact hy_E _ hk2R a1
          · have hk1R : (eB k1).1 ∈ R :=
              (Finset.mem_filter.mp (Finset.mem_filter.mp (eB k1).2).1).1
            exact hy_E _ hk1R a2
          · exact hB_orth t _ (eB k1).2 _ (eB k2).2 (fun heq => by
              apply hne'
              rw [h1, h2]
              congr 1
              exact eB.injective (Subtype.ext heq))
      simpa [Function.comp_assoc] using hli'.comp eqv eqv.injective
    have hcard := hli.fintype_card_le_finrank
    simp only [Fintype.card_sum, Fintype.card_fin, finrank_euclideanSpace_fin] at hcard
    omega
  have hB_le_four : ∀ t s : Fin 3, t ≠ s → (C s).Nonempty → (B t).card ≤ 4 := by
    intro t s hts ⟨j0, hj0⟩
    have hj0R : j0 ∈ R := (Finset.mem_filter.mp hj0).1
    have hj0c : cls j0 = s := (Finset.mem_filter.mp hj0).2
    have hbes := bessel_sq_norm_two (B t) y
      (fun i hi => hy_norm i (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1)
      (hB_orth t) (y j0)
    have hsum_ones : ∑ i ∈ B t, ⟪y j0, y i⟫_ℝ ^ 2 = ((B t).card : ℝ) := by
      have hterm : ∀ i ∈ B t, ⟪y j0, y i⟫_ℝ ^ 2 = 1 := by
        intro i hi
        have hiR : i ∈ R := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
        have hic : cls i = t := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
        have hji : j0 ≠ i := fun h => hts (by rw [← hj0c, ← hic, h])
        have hne_cls : cls j0 ≠ cls i := by rw [hj0c, hic]; exact hts.symm
        rw [hy_inner_ne j0 hj0R i hiR hne_cls]
        rcases hw_inner_pm j0 i hji with h | h <;> simp [h]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hnorm_j0 : ⟪y j0, y j0⟫_ℝ = 2 := hy_norm j0 hj0R
    rw [hsum_ones, hnorm_j0] at hbes
    have hle : ((B t).card : ℝ) ≤ 4 := by linarith
    exact_mod_cast hle
  -- Now split on whether at most one of C 0, C 1, C 2 is nonempty
  by_cases htwo : (∃ t s : Fin 3, t ≠ s ∧ (C t).Nonempty ∧ (C s).Nonempty)
  · rcases htwo with ⟨t0, s0, hts0, ht0_ne, hs0_ne⟩
    have hC_le_eight : ∀ t : Fin 3, (C t).card ≤ 8 := by
      intro t
      have hBt : (B t).card ≤ 4 := by
        by_cases ht : t = t0
        · subst ht; exact hB_le_four t s0 hts0 hs0_ne
        · exact hB_le_four t t0 ht ht0_ne
      exact (hC_le_two_B t).trans (by omega)
    have h28 : n ≤ 28 := by
      have c0 := hC_le_eight 0
      have c1 := hC_le_eight 1
      have c2 := hC_le_eight 2
      omega
    omega
  · -- At most one C t is nonempty
    push Not at htwo
    have hc_le : R.card ≤ 2 * (d - 3) := by
      by_cases h0 : (C 0).Nonempty
      · have h1 : (C 1).card = 0 := Finset.card_eq_zero.mpr (htwo 0 1 (by decide) h0)
        have h2 : (C 2).card = 0 := Finset.card_eq_zero.mpr (htwo 0 2 (by decide) h0)
        have hb := hB_le_dim 0
        have hc := hC_le_two_B 0
        omega
      · by_cases h1 : (C 1).Nonempty
        · have h0' : (C 0).card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp h0)
          have h2 : (C 2).card = 0 := Finset.card_eq_zero.mpr (htwo 1 2 (by decide) h1)
          have hb := hB_le_dim 1
          have hc := hC_le_two_B 1
          omega
        · have h0' : (C 0).card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp h0)
          have h1' : (C 1).card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp h1)
          have hb := hB_le_dim 2
          have hc := hC_le_two_B 2
          omega
    omega

end LemmensSeidelHelpers

section NoPillarCase

private lemma ker_one_sub_adj_le_one_of_bipartite {n : ℕ}
    (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    (hadj_symm : ∀ {x y}, adj x y → adj y x)
    (L' R' : Finset (Fin n)) (hdisj : Disjoint L' R')
    (hbip : ∀ x y, adj x y → (x ∈ L' ∧ y ∈ R') ∨ (x ∈ R' ∧ y ∈ L'))
    (hNo2K2 : ∀ a b c e : Fin n,
      a ≠ b → a ≠ c → a ≠ e → b ≠ c → b ≠ e → c ≠ e →
      adj a b → adj c e → ¬ adj a c → ¬ adj a e → ¬ adj b c → ¬ adj b e → False) :
    Module.finrank ℝ (LinearMap.ker (1 - Matrix.of fun i j : Fin n =>
      if adj i j then (1 : ℝ) else 0).mulVecLin) ≤ 1 := by
  classical
  let A : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => if adj i j then 1 else 0
  let NL : Fin n → Finset (Fin n) := fun i => R'.filter (adj i)
  let NR : Fin n → Finset (Fin n) := fun j => L'.filter (adj j)
  have hL_indep : ∀ a ∈ L', ∀ c ∈ L', ¬ adj a c := by
    intro a ha c hc had
    rcases hbip a c had with ⟨_, h1⟩ | ⟨h1, _⟩
    · exact Finset.disjoint_left.mp hdisj hc h1
    · exact Finset.disjoint_left.mp hdisj ha h1
  have hR_indep : ∀ b ∈ R', ∀ e ∈ R', ¬ adj b e := by
    intro b hb e he had
    rcases hbip b e had with ⟨h1, _⟩ | ⟨_, h1⟩
    · exact Finset.disjoint_right.mp hdisj hb h1
    · exact Finset.disjoint_right.mp hdisj he h1
  have hcomp_L : ∀ a ∈ L', ∀ c ∈ L', NL a ⊆ NL c ∨ NL c ⊆ NL a := by
    intro a ha c hc
    by_contra hnot
    rw [not_or, Finset.not_subset, Finset.not_subset] at hnot
    rcases hnot with ⟨⟨b, hba, hbc⟩, ⟨e, hec, hea⟩⟩
    have hbR : b ∈ R' := (Finset.mem_filter.mp hba).1
    have heR : e ∈ R' := (Finset.mem_filter.mp hec).1
    have hab : adj a b := (Finset.mem_filter.mp hba).2
    have hce : adj c e := (Finset.mem_filter.mp hec).2
    have hnac : ¬ adj a c := hL_indep a ha c hc
    have hnae : ¬ adj a e := fun h => hea (Finset.mem_filter.mpr ⟨heR, h⟩)
    have hnbc : ¬ adj b c := fun h => hbc (Finset.mem_filter.mpr ⟨hbR, hadj_symm h⟩)
    have hnbe : ¬ adj b e := hR_indep b hbR e heR
    have hne_ab : a ≠ b := fun h => Finset.disjoint_left.mp hdisj ha (h ▸ hbR)
    have hne_ac : a ≠ c := fun h => hbc (h ▸ hba)
    have hne_ae : a ≠ e := fun h => Finset.disjoint_left.mp hdisj ha (h ▸ heR)
    have hne_bc : b ≠ c := fun h => Finset.disjoint_left.mp hdisj hc (h ▸ hbR)
    have hne_be : b ≠ e := fun h => hbc (h ▸ hec)
    have hne_ce : c ≠ e := fun h => Finset.disjoint_left.mp hdisj hc (h ▸ heR)
    exact hNo2K2 a b c e hne_ab hne_ac hne_ae hne_bc hne_be hne_ce hab hce hnac hnae hnbc hnbe
  have hcomp_R : ∀ b ∈ R', ∀ e ∈ R', NR b ⊆ NR e ∨ NR e ⊆ NR b := by
    intro b hb e he
    by_contra hnot
    rw [not_or, Finset.not_subset, Finset.not_subset] at hnot
    rcases hnot with ⟨⟨a, hab, hae⟩, ⟨c, hce, hcb⟩⟩
    have haL : a ∈ L' := (Finset.mem_filter.mp hab).1
    have hcL : c ∈ L' := (Finset.mem_filter.mp hce).1
    have hadj_ab : adj a b := hadj_symm (Finset.mem_filter.mp hab).2
    have hadj_ce : adj c e := hadj_symm (Finset.mem_filter.mp hce).2
    have hnac : ¬ adj a c := hL_indep a haL c hcL
    have hnae : ¬ adj a e := fun h => hae (Finset.mem_filter.mpr ⟨haL, hadj_symm h⟩)
    have hnbc : ¬ adj b c := fun h => hcb (Finset.mem_filter.mpr ⟨hcL, h⟩)
    have hnbe : ¬ adj b e := hR_indep b hb e he
    have hne_ab : a ≠ b := fun h => Finset.disjoint_left.mp hdisj haL (h ▸ hb)
    have hne_ac : a ≠ c := fun h => hae (h ▸ hce)
    have hne_ae : a ≠ e := fun h => Finset.disjoint_left.mp hdisj haL (h ▸ he)
    have hne_bc : b ≠ c := fun h => Finset.disjoint_left.mp hdisj hcL (h ▸ hb)
    have hne_be : b ≠ e := fun h => hcb (h ▸ hce)
    have hne_ce : c ≠ e := fun h => Finset.disjoint_left.mp hdisj hcL (h ▸ he)
    exact hNo2K2 a b c e hne_ab hne_ac hne_ae hne_bc hne_be hne_ce hadj_ab hadj_ce hnac hnae hnbc hnbe
  have hker_eq : ∀ x ∈ LinearMap.ker (1 - A).mulVecLin, ∀ i : Fin n,
      x i = ∑ j ∈ Finset.univ.filter (adj i), x j := by
    intro x hx i
    rw [LinearMap.mem_ker, mulVecLin_apply, sub_mulVec, one_mulVec, sub_eq_zero] at hx
    have hi := congr_fun hx i
    dsimp [A, Matrix.mulVec, dotProduct] at hi
    rw [Finset.sum_filter, hi]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : adj i j <;> simp [h]
  have hker_L : ∀ x ∈ LinearMap.ker (1 - A).mulVecLin, ∀ i ∈ L',
      x i = ∑ j ∈ NL i, x j := by
    intro x hx i hi
    rw [hker_eq x hx i]
    congr 1
    ext j
    simp only [NL, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨(hbip i j h).elim (fun h' => h'.2) (fun h' => absurd h'.1 (Finset.disjoint_left.mp hdisj hi)), h⟩,
      fun h => h.2⟩
  have hker_R : ∀ x ∈ LinearMap.ker (1 - A).mulVecLin, ∀ j ∈ R',
      x j = ∑ i ∈ NR j, x i := by
    intro x hx j hj
    rw [hker_eq x hx j]
    congr 1
    ext i
    simp only [NR, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨(hbip j i h).elim (fun h' => absurd h'.1 (Finset.disjoint_right.mp hdisj hj)) (fun h' => h'.2), h⟩,
      fun h => h.2⟩
  have hker_iso : ∀ x ∈ LinearMap.ker (1 - A).mulVecLin, ∀ v : Fin n,
      v ∉ L' → v ∉ R' → x v = 0 := by
    intro x hx v hvL hvR
    rw [hker_eq x hx v]
    have hempty : Finset.univ.filter (adj v) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro y _ h
      rcases hbip v y h with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hvL h1
      · exact hvR h1
    rw [hempty, Finset.sum_empty]
  let L_act : Finset (Fin n) := L'.filter (fun i => (NL i).Nonempty)
  let R_act : Finset (Fin n) := R'.filter (fun j => (NR j).Nonempty)
  by_cases hL_empty : L_act = ∅
  · have hker_bot : LinearMap.ker (1 - A).mulVecLin = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Submodule.mem_bot]
      ext v
      simp only [Pi.zero_apply]
      by_cases hvL : v ∈ L'
      · have hNL : NL v = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro j hj
          have hmem : v ∈ L_act := Finset.mem_filter.mpr ⟨hvL, ⟨j, hj⟩⟩
          rw [hL_empty] at hmem
          exact (Finset.notMem_empty v) hmem
        rw [hker_L x hx v hvL, hNL, Finset.sum_empty]
      · by_cases hvR : v ∈ R'
        · have hNR : NR v = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro i hi
            have hiL : i ∈ L' := (Finset.mem_filter.mp hi).1
            have hadj : adj i v := hadj_symm (Finset.mem_filter.mp hi).2
            have hmem : i ∈ L_act := Finset.mem_filter.mpr ⟨hiL, ⟨v, Finset.mem_filter.mpr ⟨hvR, hadj⟩⟩⟩
            rw [hL_empty] at hmem
            exact (Finset.notMem_empty i) hmem
          rw [hker_R x hx v hvR, hNR, Finset.sum_empty]
        · exact hker_iso x hx v hvL hvR
    rw [hker_bot, finrank_bot]
    omega
  · have hL_ne : L_act.Nonempty := Finset.nonempty_iff_ne_empty.mpr hL_empty
    obtain ⟨i0, hi0_mem, hi0_min⟩ := Finset.exists_min_image L_act (fun i => (NL i).card) hL_ne
    let φ : LinearMap.ker (1 - A).mulVecLin →ₗ[ℝ] ℝ :=
      { toFun := fun x => x.1 i0
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hker_phi : LinearMap.ker φ = ⊥ := by
      rw [eq_bot_iff]
      rintro ⟨x, hx⟩ hxi0
      rw [Submodule.mem_bot, Subtype.ext_iff, ZeroMemClass.coe_zero]
      change x i0 = 0 at hxi0
      have hi0L : i0 ∈ L' := (Finset.mem_filter.mp hi0_mem).1
      let Y1 : Finset (Fin n) := NL i0
      have hY1_ne : Y1.Nonempty := (Finset.mem_filter.mp hi0_mem).2
      have hY1_sub : ∀ i ∈ L_act, Y1 ⊆ NL i := by
        intro i hi
        have hiL : i ∈ L' := (Finset.mem_filter.mp hi).1
        rcases hcomp_L i0 hi0L i hiL with h | h
        · exact h
        · have hcard : (NL i).card = (NL i0).card :=
            le_antisymm (Finset.card_le_card h) (hi0_min i hi)
          exact (Finset.eq_of_subset_of_card_le h hcard.ge).symm.subset
      have hY1_NR : ∀ j ∈ Y1, NR j = L_act := by
        intro j hj
        have hjR : j ∈ R' := (Finset.mem_filter.mp hj).1
        ext i
        simp only [NR, L_act, Finset.mem_filter]
        constructor
        · rintro ⟨hiL, hji⟩
          exact ⟨hiL, ⟨j, Finset.mem_filter.mpr ⟨hjR, hadj_symm hji⟩⟩⟩
        · rintro ⟨hiL, hi_ne⟩
          have hj_in : j ∈ NL i := hY1_sub i (Finset.mem_filter.mpr ⟨hiL, hi_ne⟩) hj
          exact ⟨hiL, hadj_symm (Finset.mem_filter.mp hj_in).2⟩
      have hY1_Ract : Y1 ⊆ R_act := by
        intro j hj
        refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1, ?_⟩
        rw [hY1_NR j hj]
        exact hL_ne
      have hsum_L_act : ∑ i ∈ L_act, x i = 0 := by
        have hconst : ∀ j ∈ Y1, x j = ∑ i ∈ L_act, x i := by
          intro j hj
          rw [hker_R x hx j (Finset.mem_filter.mp hj).1, hY1_NR j hj]
        have hsum_eq : x i0 = ∑ j ∈ Y1, x j := hker_L x hx i0 hi0L
        rw [hxi0, Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul] at hsum_eq
        have hcard_pos : (Y1.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hY1_ne.card_pos.ne'
        exact (mul_eq_zero.mp hsum_eq.symm).resolve_left hcard_pos
      have hx_Y1 : ∀ j ∈ Y1, x j = 0 := by
        intro j hj
        rw [hker_R x hx j (Finset.mem_filter.mp hj).1, hY1_NR j hj, hsum_L_act]
      let X1 : Finset (Fin n) := L_act.filter (fun i => NL i = Y1)
      have hx_X1 : ∀ i ∈ X1, x i = 0 := by
        intro i hi
        have hiL : i ∈ L' := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
        have hNL : NL i = Y1 := (Finset.mem_filter.mp hi).2
        rw [hker_L x hx i hiL, hNL]
        exact Finset.sum_eq_zero hx_Y1
      have hind : ∀ k : ℕ, ∀ DoneL DoneR : Finset (Fin n),
          DoneL ⊆ L_act → DoneR ⊆ R_act →
          (L_act \ DoneL).card + (R_act \ DoneR).card = k →
          (∀ i ∈ DoneL, x i = 0) →
          (∀ j ∈ DoneR, x j = 0) →
          (∀ i ∈ DoneL, ∀ j ∈ R_act \ DoneR, ¬ adj i j) →
          (∀ i ∈ L_act \ DoneL, ∀ j ∈ DoneR, adj i j) →
          (∀ i ∈ L_act, x i = 0) ∧ (∀ j ∈ R_act, x j = 0) := by
        intro k
        induction k using Nat.strong_induction_on with
        | _ k ih =>
          intro DoneL DoneR hDL hDR hk hxDL hxDR hno_cross hall_cross
          by_cases hcaseA : ∃ i ∈ L_act \ DoneL, NL i = DoneR
          · let newL := (L_act \ DoneL).filter (fun i => NL i = DoneR)
            have hnewL_ne : newL.Nonempty := by
              rcases hcaseA with ⟨i, hi, heq⟩
              exact ⟨i, Finset.mem_filter.mpr ⟨hi, heq⟩⟩
            let DoneL' := DoneL ∪ newL
            have hDL' : DoneL' ⊆ L_act := Finset.union_subset hDL
              ((Finset.filter_subset _ _).trans Finset.sdiff_subset)
            have hlt : (L_act \ DoneL').card + (R_act \ DoneR).card < k := by
              have hss : L_act \ DoneL' ⊂ L_act \ DoneL := by
                rw [Finset.ssubset_iff_of_subset]
                · rcases hnewL_ne with ⟨i, hi⟩
                  exact ⟨i, (Finset.mem_filter.mp hi).1, fun h =>
                    (Finset.mem_sdiff.mp h).2 (Finset.mem_union_right _ hi)⟩
                · intro i hi
                  exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hi).1,
                    fun h => (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ h)⟩
              have hcard_lt := Finset.card_lt_card hss
              omega
            refine ih _ hlt DoneL' DoneR hDL' hDR rfl ?_ hxDR ?_ ?_
            · intro i hi
              rcases Finset.mem_union.mp hi with hi1 | hi2
              · exact hxDL i hi1
              · have hiL : i ∈ L' := (Finset.mem_filter.mp (Finset.mem_sdiff.mp
                  (Finset.mem_filter.mp hi2).1).1).1
                rw [hker_L x hx i hiL, (Finset.mem_filter.mp hi2).2]
                exact Finset.sum_eq_zero hxDR
            · intro i hi j hj
              rcases Finset.mem_union.mp hi with hi1 | hi2
              · exact hno_cross i hi1 j hj
              · have hNL : NL i = DoneR := (Finset.mem_filter.mp hi2).2
                intro hadj
                have hjR : j ∈ R' := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hj).1).1
                have hj_in : j ∈ NL i := Finset.mem_filter.mpr ⟨hjR, hadj⟩
                rw [hNL] at hj_in
                exact (Finset.mem_sdiff.mp hj).2 hj_in
            · intro i hi j hj
              apply hall_cross _ _ j hj
              exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hi).1,
                fun h => (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ h)⟩
          · push Not at hcaseA
            by_cases hR_rem : (R_act \ DoneR).Nonempty
            · obtain ⟨jmax, hjmax_mem, hjmax_max⟩ :=
                Finset.exists_max_image (R_act \ DoneR) (fun j => (NR j).card) hR_rem
              have hjmax_R : jmax ∈ R' :=
                (Finset.mem_filter.mp (Finset.mem_sdiff.mp hjmax_mem).1).1
              have hNR_jmax : NR jmax = L_act \ DoneL := by
                ext i
                simp only [NR, Finset.mem_filter, Finset.mem_sdiff]
                constructor
                · rintro ⟨hiL, hji⟩
                  have hi_act : i ∈ L_act := Finset.mem_filter.mpr ⟨hiL,
                    ⟨jmax, Finset.mem_filter.mpr ⟨hjmax_R, hadj_symm hji⟩⟩⟩
                  refine ⟨hi_act, fun hiD => ?_⟩
                  exact hno_cross i hiD jmax hjmax_mem (hadj_symm hji)
                · rintro ⟨hi_act, hiND⟩
                  have hiL : i ∈ L' := (Finset.mem_filter.mp hi_act).1
                  have hi_rem : i ∈ L_act \ DoneL := Finset.mem_sdiff.mpr ⟨hi_act, hiND⟩
                  refine ⟨hiL, ?_⟩
                  by_contra hnji
                  have hNL_ne : NL i ≠ DoneR := hcaseA i hi_rem
                  have hDoneR_sub : DoneR ⊆ NL i := by
                    intro j hj
                    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (hDR hj)).1,
                      hall_cross i hi_rem j hj⟩
                  have hss : DoneR ⊂ NL i := ssubset_of_subset_of_ne hDoneR_sub hNL_ne.symm
                  obtain ⟨j', hj'_in, hj'_notin⟩ := Finset.exists_of_ssubset hss
                  have hj'R : j' ∈ R' := (Finset.mem_filter.mp hj'_in).1
                  have hj'adj : adj i j' := (Finset.mem_filter.mp hj'_in).2
                  have hj'_act : j' ∈ R_act := Finset.mem_filter.mpr ⟨hj'R,
                    ⟨i, Finset.mem_filter.mpr ⟨hiL, hadj_symm hj'adj⟩⟩⟩
                  have hj'_rem : j' ∈ R_act \ DoneR := Finset.mem_sdiff.mpr ⟨hj'_act, hj'_notin⟩
                  rcases hcomp_R jmax hjmax_R j' hj'R with hsub | hsub
                  · have hlt_card : (NR jmax).card < (NR j').card := by
                      apply Finset.card_lt_card
                      rw [Finset.ssubset_iff_of_subset hsub]
                      exact ⟨i, Finset.mem_filter.mpr ⟨hiL, hadj_symm hj'adj⟩,
                        fun h => hnji (Finset.mem_filter.mp h).2⟩
                    have hle := hjmax_max j' hj'_rem
                    omega
                  · have hmem : i ∈ NR jmax := hsub (Finset.mem_filter.mpr ⟨hiL, hadj_symm hj'adj⟩)
                    exact hnji (Finset.mem_filter.mp hmem).2
              let newR := (R_act \ DoneR).filter (fun j => NR j = L_act \ DoneL)
              have hnewR_ne : newR.Nonempty :=
                ⟨jmax, Finset.mem_filter.mpr ⟨hjmax_mem, hNR_jmax⟩⟩
              let DoneR' := DoneR ∪ newR
              have hDR' : DoneR' ⊆ R_act := Finset.union_subset hDR
                ((Finset.filter_subset _ _).trans Finset.sdiff_subset)
              have hlt : (L_act \ DoneL).card + (R_act \ DoneR').card < k := by
                have hss : R_act \ DoneR' ⊂ R_act \ DoneR := by
                  rw [Finset.ssubset_iff_of_subset]
                  · rcases hnewR_ne with ⟨j, hj⟩
                    exact ⟨j, (Finset.mem_filter.mp hj).1, fun h =>
                      (Finset.mem_sdiff.mp h).2 (Finset.mem_union_right _ hj)⟩
                  · intro j hj
                    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hj).1,
                      fun h => (Finset.mem_sdiff.mp hj).2 (Finset.mem_union_left _ h)⟩
                have hcard_lt := Finset.card_lt_card hss
                omega
              refine ih _ hlt DoneL DoneR' hDL hDR' rfl hxDL ?_ ?_ ?_
              · intro j hj
                rcases Finset.mem_union.mp hj with hj1 | hj2
                · exact hxDR j hj1
                · have hjR : j ∈ R' := (Finset.mem_filter.mp (Finset.mem_sdiff.mp
                    (Finset.mem_filter.mp hj2).1).1).1
                  have hNR : NR j = L_act \ DoneL := (Finset.mem_filter.mp hj2).2
                  rw [hker_R x hx j hjR, hNR]
                  have hsum_split : ∑ i ∈ L_act, x i =
                      ∑ i ∈ DoneL, x i + ∑ i ∈ L_act \ DoneL, x i := by
                    rw [← Finset.sum_sdiff hDL, add_comm]
                  have h0 : ∑ i ∈ DoneL, x i = 0 := Finset.sum_eq_zero hxDL
                  linarith
              · intro i hi j hj
                apply hno_cross i hi j
                exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hj).1,
                  fun h => (Finset.mem_sdiff.mp hj).2 (Finset.mem_union_left _ h)⟩
              · intro i hi j hj
                rcases Finset.mem_union.mp hj with hj1 | hj2
                · exact hall_cross i hi j hj1
                · have hNR : NR j = L_act \ DoneL := (Finset.mem_filter.mp hj2).2
                  have hi_in : i ∈ NR j := hNR ▸ hi
                  exact hadj_symm (Finset.mem_filter.mp hi_in).2
            · -- R_act \ DoneR is empty, so DoneR = R_act and L_act \ DoneL must also be empty
              have hR_empty : R_act \ DoneR = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR_rem
              have hL_empty' : L_act \ DoneL = ∅ := by
                by_contra hne
                rcases Finset.nonempty_iff_ne_empty.mpr hne with ⟨i, hi⟩
                apply hcaseA i hi
                ext j
                simp only [NL, Finset.mem_filter]
                constructor
                · rintro ⟨hjR, hij⟩
                  have hj_act : j ∈ R_act := Finset.mem_filter.mpr ⟨hjR,
                    ⟨i, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_sdiff.mp hi).1).1,
                      hadj_symm hij⟩⟩⟩
                  by_contra hjD
                  have hj_rem : j ∈ R_act \ DoneR := Finset.mem_sdiff.mpr ⟨hj_act, hjD⟩
                  rw [hR_empty] at hj_rem
                  exact Finset.notMem_empty j hj_rem
                · intro hjD
                  exact ⟨(Finset.mem_filter.mp (hDR hjD)).1, hall_cross i hi j hjD⟩
              refine ⟨fun i hi => hxDL i ?_, fun j hj => hxDR j ?_⟩
              · by_contra hiD
                have hi_rem : i ∈ L_act \ DoneL := Finset.mem_sdiff.mpr ⟨hi, hiD⟩
                rw [hL_empty'] at hi_rem
                exact Finset.notMem_empty i hi_rem
              · by_contra hjD
                have hj_rem : j ∈ R_act \ DoneR := Finset.mem_sdiff.mpr ⟨hj, hjD⟩
                rw [hR_empty] at hj_rem
                exact Finset.notMem_empty j hj_rem
      have hfinal := hind _ X1 Y1 (Finset.filter_subset _ _) hY1_Ract rfl hx_X1 hx_Y1
        (fun i hi j hj => by
          have hNL : NL i = Y1 := (Finset.mem_filter.mp hi).2
          intro hadj
          have hj_in : j ∈ NL i := Finset.mem_filter.mpr
            ⟨(Finset.mem_filter.mp (Finset.mem_sdiff.mp hj).1).1, hadj⟩
          rw [hNL] at hj_in
          exact (Finset.mem_sdiff.mp hj).2 hj_in)
        (fun i hi j hj => by
          have hi_act : i ∈ L_act := (Finset.mem_sdiff.mp hi).1
          exact (Finset.mem_filter.mp (hY1_sub i hi_act hj)).2)
      ext v
      change x v = 0
      by_cases hvL : v ∈ L'
      · by_cases hv_act : v ∈ L_act
        · exact hfinal.1 v hv_act
        · have hNL : NL v = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro j hj
            exact hv_act (Finset.mem_filter.mpr ⟨hvL, ⟨j, hj⟩⟩)
          rw [hker_L x hx v hvL, hNL, Finset.sum_empty]
      · by_cases hvR : v ∈ R'
        · by_cases hv_act : v ∈ R_act
          · exact hfinal.2 v hv_act
          · have hNR : NR v = ∅ := by
              rw [Finset.eq_empty_iff_forall_notMem]
              intro i hi
              exact hv_act (Finset.mem_filter.mpr ⟨hvR, ⟨i, hi⟩⟩)
            rw [hker_R x hx v hvR, hNR, Finset.sum_empty]
        · exact hker_iso x hx v hvL hvR
    have hle := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp hker_phi)
    simpa [Module.finrank_self] using hle

private lemma fin5_dist_two {i j : Fin 5} (hij : i ≠ j) (h1 : j ≠ i + 1) (h2 : i ≠ j + 1) :
    j = i + 2 ∨ i = j + 2 := by
  revert i j hij h1 h2; decide

private lemma fin5_cases_rel (k i : Fin 5) :
    k = i ∨ k = i + 1 ∨ k = i + 2 ∨ k = i + 3 ∨ k = i + 4 := by
  revert k i; decide

private lemma fin5_shift_ne (i a b : Fin 5) (h : a ≠ b) : i + a ≠ i + b :=
  fun e => h (add_left_cancel e)

private lemma fin5_add_ne_zero (i k : Fin 5) (hk : k ≠ 0) : i ≠ i + k := by
  simpa using fin5_shift_ne i 0 k hk.symm

private lemma fin5_add_eq {i a b c : Fin 5} (h : a + b = c) : i + a + b = i + c := by
  rw [add_assoc, h]

private lemma fin5_add_zero_eq {i a b : Fin 5} (h : a + b = 0) : i + a + b = i := by
  rw [add_assoc, h, add_zero]

private lemma ker_one_sub_adj_le_five {n : ℕ}
    (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    (hadj_symm : ∀ {x y}, adj x y → adj y x) (hadj_irrefl : ∀ i, ¬ adj i i)
    (hNoK3 : ∀ a b c : Fin n, ¬ (adj a b ∧ adj b c ∧ adj c a))
    (hNo2K2 : ∀ a b c e : Fin n,
      a ≠ b → a ≠ c → a ≠ e → b ≠ c → b ≠ e → c ≠ e →
      adj a b → adj c e → ¬ adj a c → ¬ adj a e → ¬ adj b c → ¬ adj b e → False) :
    Module.finrank ℝ (LinearMap.ker (1 - Matrix.of fun i j : Fin n =>
      if adj i j then (1 : ℝ) else 0).mulVecLin) ≤ 5 := by
  classical
  let A : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => if adj i j then 1 else 0
  by_cases hno_edge : ∀ x y : Fin n, ¬ adj x y
  · have hA0 : A = 0 := by
      ext i j
      simp [A, hno_edge i j]
    rw [show LinearMap.ker (1 - A).mulVecLin = ⊥ from by
      rw [hA0, sub_zero, mulVecLin_one]
      exact LinearMap.ker_id]
    simp
  · push Not at hno_edge
    rcases hno_edge with ⟨u0, w0, hu0w0⟩
    have huw_ne : u0 ≠ w0 := fun h => hadj_irrefl u0 (h ▸ hu0w0)
    let L : Finset (Fin n) := Finset.univ.filter (adj u0)
    let R : Finset (Fin n) := Finset.univ.filter (adj w0)
    have hLR_disj : Disjoint L R := by
      rw [Finset.disjoint_left]
      intro x hxL hxR
      exact hNoK3 u0 w0 x ⟨hu0w0, (Finset.mem_filter.mp hxR).2,
        hadj_symm (Finset.mem_filter.mp hxL).2⟩
    by_cases hC5 : ∃ z : Fin n, z ∉ L ∧ z ∉ R ∧ ∃ l ∈ L, ∃ r ∈ R, adj z l ∧ adj z r
    · rcases hC5 with ⟨z, hzL, hzR, l, hlL, r, hrR, hzl, hzr⟩
      have hl_adj : adj u0 l := (Finset.mem_filter.mp hlL).2
      have hr_adj : adj w0 r := (Finset.mem_filter.mp hrR).2
      have hlr_nadj : ¬ adj l r := fun h => hNoK3 z l r ⟨hzl, h, hadj_symm hzr⟩
      have hzu_nadj : ¬ adj z u0 := fun h => hzL (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj_symm h⟩)
      have hzw_nadj : ¬ adj z w0 := fun h => hzR (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj_symm h⟩)
      have hur_nadj : ¬ adj u0 r := fun h =>
        Finset.disjoint_left.mp hLR_disj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩) hrR
      have hwl_nadj : ¬ adj w0 l := fun h =>
        Finset.disjoint_left.mp hLR_disj hlL (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      let C : Fin 5 → Fin n := ![u0, l, z, r, w0]
      have hC_cycle : ∀ i : Fin 5, adj (C i) (C (i + 1)) := by
        intro i
        fin_cases i <;> simp [C, hl_adj, hadj_symm hzl, hzr, hadj_symm hr_adj, hadj_symm hu0w0]
      have hC_nonedge : ∀ i : Fin 5, ¬ adj (C i) (C (i + 2)) := by
        intro i
        fin_cases i
        · change ¬ adj u0 z; exact fun h => hzu_nadj (hadj_symm h)
        · change ¬ adj l r; exact hlr_nadj
        · change ¬ adj z w0; exact hzw_nadj
        · change ¬ adj r u0; exact fun h => hur_nadj (hadj_symm h)
        · change ¬ adj w0 l; exact hwl_nadj
      have hC_nonedge' : ∀ i j : Fin 5, i ≠ j → j ≠ i + 1 → i ≠ j + 1 → ¬ adj (C i) (C j) := by
        intro i j hij h1 h2
        rcases fin5_dist_two hij h1 h2 with rfl | rfl
        · exact hC_nonedge i
        · exact fun h => hC_nonedge j (hadj_symm h)
      have hC_inj : Function.Injective C := by
        intro i j hij
        by_contra hne
        have hstep : ∀ a b : Fin 5, a ≠ b → C a = C b → False := by
          intro a b hab heq
          by_cases h1 : b = a + 1
          · subst h1; exact hadj_irrefl (C a) (heq ▸ hC_cycle a)
          · by_cases h2 : a = b + 1
            · subst h2; exact hadj_irrefl (C b) (heq ▸ hC_cycle b)
            · rcases fin5_dist_two hab h1 h2 with rfl | rfl
              · have h1' : adj (C (a + 4)) (C a) := by
                  have htmp := hC_cycle (a + 4)
                  rwa [fin5_add_zero_eq (i := a) (a := 4) (b := 1) rfl] at htmp
                have h2' : ¬ adj (C (a + 2)) (C (a + 4)) := by
                  rw [← fin5_add_eq (i := a) (a := 2) (b := 2) (c := 4) rfl]; exact hC_nonedge (a + 2)
                exact h2' (heq ▸ hadj_symm h1')
              · have h1' : adj (C (b + 4)) (C b) := by
                  have htmp := hC_cycle (b + 4)
                  rwa [fin5_add_zero_eq (i := b) (a := 4) (b := 1) rfl] at htmp
                have h2' : ¬ adj (C (b + 2)) (C (b + 4)) := by
                  rw [← fin5_add_eq (i := b) (a := 2) (b := 2) (c := 4) rfl]; exact hC_nonedge (b + 2)
                exact h2' (heq ▸ hadj_symm h1')
        exact hstep i j hne hij
      -- Classify every vertex by its adjacency to C
      have h_no_C_isolated : ∀ x : Fin n, (∀ i : Fin 5, ¬ adj x (C i)) →
          ∀ y : Fin n, ¬ adj x y := by
        intro x hxC y hxy
        have hxy_ne : x ≠ y := fun h => hadj_irrefl x (h ▸ hxy)
        by_cases hyC : ∀ i : Fin 5, ¬ adj y (C i)
        · have hC40 : adj (C 4) (C 0) := by
            change adj (C 4) (C (4 + 1)); exact hC_cycle 4
          have hxC0 : x ≠ C 0 := fun h => (hxC 4) (h ▸ hadj_symm hC40)
          have hxC4 : x ≠ C 4 := fun h => (hxC 0) (h ▸ hC40)
          have hyC0 : y ≠ C 0 := fun h => (hyC 4) (h ▸ hadj_symm hC40)
          have hyC4 : y ≠ C 4 := fun h => (hyC 0) (h ▸ hC40)
          exact hNo2K2 x y (C 0) (C 4) hxy_ne hxC0 hxC4 hyC0 hyC4 (hC_inj.ne (by decide))
            hxy (hadj_symm hC40)
            (hxC 0) (hxC 4) (hyC 0) (hyC 4)
        · push Not at hyC
          rcases hyC with ⟨i, hyi⟩
          have hyip1 : ¬ adj y (C (i + 1)) := fun h =>
            hNoK3 y (C i) (C (i + 1)) ⟨hyi, hC_cycle i, hadj_symm h⟩
          have hC_m1_i : adj (C (i + 4)) (C i) := by
            have htmp := hC_cycle (i + 4)
            rwa [fin5_add_zero_eq (i := i) (a := 4) (b := 1) rfl] at htmp
          have hyim1 : ¬ adj y (C (i + 4)) := fun h =>
            hNoK3 y (C (i + 4)) (C i) ⟨h, hC_m1_i, hadj_symm hyi⟩
          have hpair : ∃ k : Fin 5, ¬ adj y (C k) ∧ ¬ adj y (C (k + 1)) := by
            by_cases hyip2 : adj y (C (i + 2))
            · have hC23 : adj (C (i + 2)) (C (i + 3)) := by
                rw [← fin5_add_eq (i := i) (a := 2) (b := 1) (c := 3) rfl]; exact hC_cycle (i + 2)
              refine ⟨i + 3, fun h => hNoK3 y (C (i + 2)) (C (i + 3))
                ⟨hyip2, hC23, hadj_symm h⟩, ?_⟩
              rw [fin5_add_eq (i := i) (a := 3) (b := 1) (c := 4) rfl]; exact hyim1
            · refine ⟨i + 1, hyip1, ?_⟩
              rw [fin5_add_eq (i := i) (a := 1) (b := 1) (c := 2) rfl]; exact hyip2
          rcases hpair with ⟨k, hyk, hyk1⟩
          have hxCk : x ≠ C k := fun h => (hxC (k + 1)) (h ▸ hC_cycle k)
          have hxCk1 : x ≠ C (k + 1) := fun h => (hxC k) (h ▸ hadj_symm (hC_cycle k))
          have hyCk : y ≠ C k := fun h => hyk1 (h ▸ hC_cycle k)
          have hyCk1 : y ≠ C (k + 1) := fun h => hyk (h ▸ hadj_symm (hC_cycle k))
          exact hNo2K2 x y (C k) (C (k + 1)) hxy_ne hxCk hxCk1 hyCk hyCk1
            (hC_inj.ne (fin5_add_ne_zero k 1 (by decide)))
            hxy (hC_cycle k) (hxC k) (hxC (k + 1)) hyk hyk1
      have h_hit_C_two : ∀ x : Fin n, (∃ j : Fin 5, adj x (C j)) →
          ∃ i : Fin 5, adj x (C (i + 4)) ∧ adj x (C (i + 1)) ∧
            ¬ adj x (C i) ∧ ¬ adj x (C (i + 2)) ∧ ¬ adj x (C (i + 3)) := by
        intro x ⟨j, hxj⟩
        have hxjp1 : ¬ adj x (C (j + 1)) := fun h =>
          hNoK3 x (C j) (C (j + 1)) ⟨hxj, hC_cycle j, hadj_symm h⟩
        have hC_m1_j : adj (C (j + 4)) (C j) := by
          have htmp := hC_cycle (j + 4)
          rwa [fin5_add_zero_eq (i := j) (a := 4) (b := 1) rfl] at htmp
        have hxjm1 : ¬ adj x (C (j + 4)) := fun h =>
          hNoK3 x (C (j + 4)) (C j) ⟨h, hC_m1_j, hadj_symm hxj⟩
        by_cases hxjp2 : adj x (C (j + 2))
        · have hC23 : adj (C (j + 2)) (C (j + 3)) := by
            rw [← fin5_add_eq (i := j) (a := 2) (b := 1) (c := 3) rfl]; exact hC_cycle (j + 2)
          have hxjp3 : ¬ adj x (C (j + 3)) := fun h =>
            hNoK3 x (C (j + 2)) (C (j + 3)) ⟨hxjp2, hC23, hadj_symm h⟩
          refine ⟨j + 1, ?_, ?_, hxjp1, ?_, ?_⟩
          · rw [fin5_add_zero_eq (i := j) (a := 1) (b := 4) rfl]; exact hxj
          · rw [fin5_add_eq (i := j) (a := 1) (b := 1) (c := 2) rfl]; exact hxjp2
          · rw [fin5_add_eq (i := j) (a := 1) (b := 2) (c := 3) rfl]; exact hxjp3
          · rw [fin5_add_eq (i := j) (a := 1) (b := 3) (c := 4) rfl]; exact hxjm1
        · by_cases hxjp3 : adj x (C (j + 3))
          · refine ⟨j + 4, ?_, ?_, hxjm1, ?_, ?_⟩
            · rw [fin5_add_eq (i := j) (a := 4) (b := 4) (c := 3) rfl]; exact hxjp3
            · rw [fin5_add_zero_eq (i := j) (a := 4) (b := 1) rfl]; exact hxj
            · rw [fin5_add_eq (i := j) (a := 4) (b := 2) (c := 1) rfl]; exact hxjp1
            · rw [fin5_add_eq (i := j) (a := 4) (b := 3) (c := 2) rfl]; exact hxjp2
          · exfalso
            have hC23 : adj (C (j + 2)) (C (j + 3)) := by
              rw [← fin5_add_eq (i := j) (a := 2) (b := 1) (c := 3) rfl]; exact hC_cycle (j + 2)
            have hxCj : x ≠ C j := fun h => hadj_irrefl x (h ▸ hxj)
            have hxCj2 : x ≠ C (j + 2) := fun h => hxjp3 (h ▸ hC23)
            have hxCj3 : x ≠ C (j + 3) := fun h => hxjp2 (h ▸ hadj_symm hC23)
            have hC_j2 : C j ≠ C (j + 2) := hC_inj.ne (fin5_add_ne_zero j 2 (by decide))
            have hC_j3 : C j ≠ C (j + 3) := hC_inj.ne (fin5_add_ne_zero j 3 (by decide))
            have hC_23 : C (j + 2) ≠ C (j + 3) :=
              hC_inj.ne (fin5_shift_ne j 2 3 (by decide))
            have hnj_3 : ¬ adj (C j) (C (j + 3)) := fun h =>
              hC_nonedge (j + 3) (by rw [fin5_add_zero_eq (i := j) (a := 3) (b := 2) rfl]; exact hadj_symm h)
            exact hNo2K2 x (C j) (C (j + 2)) (C (j + 3)) hxCj hxCj2 hxCj3 hC_j2 hC_j3 hC_23
              hxj hC23 hxjp2 hxjp3 (hC_nonedge j) hnj_3
      have hrow_in_C : ∀ x : Fin n, A.row x = 0 ∨ ∃ i : Fin 5, A.row x = A.row (C i) := by
        intro x
        by_cases hxC : ∀ i : Fin 5, ¬ adj x (C i)
        · left
          ext y
          simp [A, h_no_C_isolated x hxC y]
        · right
          push Not at hxC
          obtain ⟨i, hxm1, hxp1, hxi, hxp2, hxp3⟩ := h_hit_C_two x hxC
          refine ⟨i, ?_⟩
          ext y
          simp only [Matrix.row_apply, A]
          suffices adj x y ↔ adj (C i) y by
            by_cases h : adj x y
            · simp [h, this.mp h]
            · simp [h, mt this.mpr h]
          by_cases hyC : ∀ k : Fin 5, ¬ adj y (C k)
          · have hny := h_no_C_isolated y hyC
            exact ⟨fun h => absurd (hadj_symm h) (hny x), fun h => absurd (hadj_symm h) (hny (C i))⟩
          · push Not at hyC
            obtain ⟨k, hykm1, hykp1, hyk, hykp2, hykp3⟩ := h_hit_C_two y hyC
            rcases fin5_cases_rel k i with rfl | rfl | rfl | rfl | rfl
            · constructor
              · intro h; exact absurd ⟨h, hykp1, hadj_symm hxp1⟩ (hNoK3 x y (C (k + 1)))
              · intro h; exact absurd ⟨h, hykp1, hadj_symm (hC_cycle k)⟩
                  (hNoK3 (C k) y (C (k + 1)))
            · have hy0 : adj y (C i) := by
                rw [← fin5_add_zero_eq (i := i) (a := 1) (b := 4) rfl]; exact hykm1
              have hy2 : adj y (C (i + 2)) := by
                rw [← fin5_add_eq (i := i) (a := 1) (b := 1) (c := 2) rfl]; exact hykp1
              have hy4 : ¬ adj y (C (i + 4)) := by
                rw [← fin5_add_eq (i := i) (a := 1) (b := 3) (c := 4) rfl]; exact hykp3
              have hCiy : adj (C i) y := hadj_symm hy0
              refine ⟨fun _ => hCiy, fun _ => ?_⟩
              by_contra hnxy
              have h24 : ¬ adj (C (i + 2)) (C (i + 4)) := by
                rw [← fin5_add_eq (i := i) (a := 2) (b := 2) (c := 4) rfl]; exact hC_nonedge (i + 2)
              have hx_ne : x ≠ C (i + 4) := fun h => hadj_irrefl x (h ▸ hxm1)
              have hxy_ne : x ≠ y := fun h => hyk (h ▸ hxp1)
              have hx_C2 : x ≠ C (i + 2) := fun h => h24 (h ▸ hxm1)
              have h4_y : C (i + 4) ≠ y := fun h => h24 (hadj_symm (h ▸ hy2))
              have h4_2 : C (i + 4) ≠ C (i + 2) := hC_inj.ne (fin5_shift_ne i 4 2 (by decide))
              have hy_2 : y ≠ C (i + 2) := fun h => hadj_irrefl y (h ▸ hy2)
              exact hNo2K2 x (C (i + 4)) y (C (i + 2)) hx_ne hxy_ne hx_C2 h4_y h4_2 hy_2
                hxm1 hy2 hnxy hxp2 (fun h => hy4 (hadj_symm h)) (fun h => h24 (hadj_symm h))
            · have hy1 : adj y (C (i + 1)) := by
                rw [← fin5_add_eq (i := i) (a := 2) (b := 4) (c := 1) rfl]; exact hykm1
              constructor
              · intro h; exact absurd ⟨h, hy1, hadj_symm hxp1⟩ (hNoK3 x y (C (i + 1)))
              · intro h; exact absurd ⟨h, hy1, hadj_symm (hC_cycle i)⟩ (hNoK3 (C i) y (C (i + 1)))
            · have hy4 : adj y (C (i + 4)) := by
                rw [← fin5_add_eq (i := i) (a := 3) (b := 1) (c := 4) rfl]; exact hykp1
              have hC40 : adj (C (i + 4)) (C i) := by
                have htmp := hC_cycle (i + 4)
                rwa [fin5_add_zero_eq (i := i) (a := 4) (b := 1) rfl] at htmp
              constructor
              · intro h; exact absurd ⟨h, hy4, hadj_symm hxm1⟩ (hNoK3 x y (C (i + 4)))
              · intro h; exact absurd ⟨h, hy4, hC40⟩ (hNoK3 (C i) y (C (i + 4)))
            · have hy0 : adj y (C i) := by
                rw [← fin5_add_zero_eq (i := i) (a := 4) (b := 1) rfl]; exact hykp1
              have hy3 : adj y (C (i + 3)) := by
                rw [← fin5_add_eq (i := i) (a := 4) (b := 4) (c := 3) rfl]; exact hykm1
              have hy1 : ¬ adj y (C (i + 1)) := by
                rw [← fin5_add_eq (i := i) (a := 4) (b := 2) (c := 1) rfl]; exact hykp2
              have hCiy : adj (C i) y := hadj_symm hy0
              refine ⟨fun _ => hCiy, fun _ => ?_⟩
              by_contra hnxy
              have h13 : ¬ adj (C (i + 1)) (C (i + 3)) := by
                rw [← fin5_add_eq (i := i) (a := 1) (b := 2) (c := 3) rfl]; exact hC_nonedge (i + 1)
              have hx_ne : x ≠ C (i + 1) := fun h => hadj_irrefl x (h ▸ hxp1)
              have hxy_ne : x ≠ y := fun h => hxp3 (h ▸ hy3)
              have hx_C3 : x ≠ C (i + 3) := fun h => h13 (hadj_symm (h ▸ hxp1))
              have h1_y : C (i + 1) ≠ y := fun h => h13 (h ▸ hy3)
              have h1_3 : C (i + 1) ≠ C (i + 3) := hC_inj.ne (fin5_shift_ne i 1 3 (by decide))
              have hy_3 : y ≠ C (i + 3) := fun h => hadj_irrefl y (h ▸ hy3)
              exact hNo2K2 x (C (i + 1)) y (C (i + 3)) hx_ne hxy_ne hx_C3 h1_y h1_3 hy_3
                hxp1 hy3 hnxy hxp3 (fun h => hy1 (hadj_symm h)) h13
      have hA_rank : A.rank ≤ 5 := by
        rw [Matrix.rank_eq_finrank_span_row]
        have hspan : Submodule.span ℝ (Set.range A.row) ≤
            Submodule.span ℝ (Set.range fun i : Fin 5 => A.row (C i)) := by
          rw [Submodule.span_le]
          rintro _ ⟨x, rfl⟩
          rcases hrow_in_C x with h0 | ⟨i, hi⟩
          · rw [h0]; exact Submodule.zero_mem _
          · rw [hi]; exact Submodule.subset_span ⟨i, rfl⟩
        calc Module.finrank ℝ (Submodule.span ℝ (Set.range A.row))
            ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range fun i : Fin 5 => A.row (C i))) :=
              Submodule.finrank_mono hspan
          _ ≤ Fintype.card (Fin 5) := finrank_range_le_card (fun i : Fin 5 => A.row (C i))
          _ = 5 := Fintype.card_fin 5
      have hker_le : LinearMap.ker (1 - A).mulVecLin ≤ LinearMap.range A.mulVecLin := by
        intro x hx
        rw [LinearMap.mem_ker, mulVecLin_apply, sub_mulVec, one_mulVec, sub_eq_zero] at hx
        exact ⟨x, hx.symm⟩
      exact (Submodule.finrank_mono hker_le).trans hA_rank
    · let L' : Finset (Fin n) := L ∪ Finset.univ.filter (fun z => z ∉ L ∧ z ∉ R ∧ ∃ r ∈ R, adj z r)
      let R' : Finset (Fin n) := R ∪ Finset.univ.filter (fun z => z ∉ L ∧ z ∉ R ∧ ∃ l ∈ L, adj z l)
      have hdisj : Disjoint L' R' := by
        rw [Finset.disjoint_left]
        intro x hxL hxR
        rcases Finset.mem_union.mp hxL with hx1 | hx2 <;>
          rcases Finset.mem_union.mp hxR with hy1 | hy2
        · exact Finset.disjoint_left.mp hLR_disj hx1 hy1
        · exact (Finset.mem_filter.mp hy2).2.1 hx1
        · exact (Finset.mem_filter.mp hx2).2.2.1 hy1
        · rcases (Finset.mem_filter.mp hx2).2.2.2 with ⟨r, hrR, hxr⟩
          rcases (Finset.mem_filter.mp hy2).2.2.2 with ⟨l, hlL, hxl⟩
          exact hC5 ⟨x, (Finset.mem_filter.mp hx2).2.1, (Finset.mem_filter.mp hx2).2.2.1,
            l, hlL, r, hrR, hxl, hxr⟩
      have hbip : ∀ x y, adj x y → (x ∈ L' ∧ y ∈ R') ∨ (x ∈ R' ∧ y ∈ L') := by
        intro x y hxy
        have h_nL : ∀ a ∈ L', ∀ b ∈ L', ¬ adj a b := by
          intro a ha b hb hab
          rcases Finset.mem_union.mp ha with ha1 | ha2 <;>
            rcases Finset.mem_union.mp hb with hb1 | hb2
          · exact hNoK3 u0 a b ⟨(Finset.mem_filter.mp ha1).2, hab, hadj_symm (Finset.mem_filter.mp hb1).2⟩
          · rcases (Finset.mem_filter.mp hb2).2.2.2 with ⟨r, hrR, hbr⟩
            exact hC5 ⟨b, (Finset.mem_filter.mp hb2).2.1, (Finset.mem_filter.mp hb2).2.2.1,
              a, ha1, r, hrR, hadj_symm hab, hbr⟩
          · rcases (Finset.mem_filter.mp ha2).2.2.2 with ⟨r, hrR, har⟩
            exact hC5 ⟨a, (Finset.mem_filter.mp ha2).2.1, (Finset.mem_filter.mp ha2).2.2.1,
              b, hb1, r, hrR, hab, har⟩
          · have ha_nL : ¬ adj u0 a := fun h => (Finset.mem_filter.mp ha2).2.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
            have ha_nR : ¬ adj w0 a := fun h => (Finset.mem_filter.mp ha2).2.2.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
            have hb_nL : ¬ adj u0 b := fun h => (Finset.mem_filter.mp hb2).2.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
            have hb_nR : ¬ adj w0 b := fun h => (Finset.mem_filter.mp hb2).2.2.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
            have ha_ne_b : a ≠ b := fun h => hadj_irrefl a (h ▸ hab)
            have ha_ne_u : a ≠ u0 := fun h => ha_nR (h ▸ hadj_symm hu0w0)
            have ha_ne_w : a ≠ w0 := fun h => ha_nL (h ▸ hu0w0)
            have hb_ne_u : b ≠ u0 := fun h => hb_nR (h ▸ hadj_symm hu0w0)
            have hb_ne_w : b ≠ w0 := fun h => hb_nL (h ▸ hu0w0)
            exact hNo2K2 a b u0 w0 ha_ne_b ha_ne_u ha_ne_w hb_ne_u hb_ne_w huw_ne
              hab hu0w0 (fun h => ha_nL (hadj_symm h)) (fun h => ha_nR (hadj_symm h))
              (fun h => hb_nL (hadj_symm h)) (fun h => hb_nR (hadj_symm h))
        have h_nR : ∀ a ∈ R', ∀ b ∈ R', ¬ adj a b := by
          intro a ha b hb hab
          rcases Finset.mem_union.mp ha with ha1 | ha2 <;>
            rcases Finset.mem_union.mp hb with hb1 | hb2
          · exact hNoK3 w0 a b ⟨(Finset.mem_filter.mp ha1).2, hab, hadj_symm (Finset.mem_filter.mp hb1).2⟩
          · rcases (Finset.mem_filter.mp hb2).2.2.2 with ⟨l, hlL, hbl⟩
            exact hC5 ⟨b, (Finset.mem_filter.mp hb2).2.1, (Finset.mem_filter.mp hb2).2.2.1,
              l, hlL, a, ha1, hbl, hadj_symm hab⟩
          · rcases (Finset.mem_filter.mp ha2).2.2.2 with ⟨l, hlL, hal⟩
            exact hC5 ⟨a, (Finset.mem_filter.mp ha2).2.1, (Finset.mem_filter.mp ha2).2.2.1,
              l, hlL, b, hb1, hal, hab⟩
          · have ha_nL : ¬ adj u0 a := fun h => (Finset.mem_filter.mp ha2).2.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
            have ha_nR : ¬ adj w0 a := fun h => (Finset.mem_filter.mp ha2).2.2.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
            have hb_nL : ¬ adj u0 b := fun h => (Finset.mem_filter.mp hb2).2.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
            have hb_nR : ¬ adj w0 b := fun h => (Finset.mem_filter.mp hb2).2.2.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
            have ha_ne_b : a ≠ b := fun h => hadj_irrefl a (h ▸ hab)
            have ha_ne_u : a ≠ u0 := fun h => ha_nR (h ▸ hadj_symm hu0w0)
            have ha_ne_w : a ≠ w0 := fun h => ha_nL (h ▸ hu0w0)
            have hb_ne_u : b ≠ u0 := fun h => hb_nR (h ▸ hadj_symm hu0w0)
            have hb_ne_w : b ≠ w0 := fun h => hb_nL (h ▸ hu0w0)
            exact hNo2K2 a b u0 w0 ha_ne_b ha_ne_u ha_ne_w hb_ne_u hb_ne_w huw_ne
              hab hu0w0 (fun h => ha_nL (hadj_symm h)) (fun h => ha_nR (hadj_symm h))
              (fun h => hb_nL (hadj_symm h)) (fun h => hb_nR (hadj_symm h))
        have h_in_LR : ∀ a b, adj a b → a ∈ L' ∨ a ∈ R' := by
          intro a b hab
          by_contra hna
          rw [not_or] at hna
          have ha_nL : a ∉ L := fun h => hna.1 (Finset.mem_union_left _ h)
          have ha_nR : a ∉ R := fun h => hna.2 (Finset.mem_union_left _ h)
          have hb_nL : b ∉ L := fun h => hna.2 (Finset.mem_union_right _ (Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, ha_nL, ha_nR, b, h, hab⟩))
          have hb_nR : b ∉ R := fun h => hna.1 (Finset.mem_union_right _ (Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, ha_nL, ha_nR, b, h, hab⟩))
          have ha_nu : ¬ adj u0 a := fun h => ha_nL (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          have ha_nw : ¬ adj w0 a := fun h => ha_nR (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          have hb_nu : ¬ adj u0 b := fun h => hb_nL (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          have hb_nw : ¬ adj w0 b := fun h => hb_nR (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          have hab_ne : a ≠ b := fun h => hadj_irrefl a (h ▸ hab)
          have hau : a ≠ u0 := fun h => ha_nw (h ▸ hadj_symm hu0w0)
          have haw : a ≠ w0 := fun h => ha_nu (h ▸ hu0w0)
          have hbu : b ≠ u0 := fun h => hb_nw (h ▸ hadj_symm hu0w0)
          have hbw : b ≠ w0 := fun h => hb_nu (h ▸ hu0w0)
          exact hNo2K2 a b u0 w0 hab_ne hau haw hbu hbw huw_ne
            hab hu0w0 (fun h => ha_nu (hadj_symm h)) (fun h => ha_nw (hadj_symm h))
            (fun h => hb_nu (hadj_symm h)) (fun h => hb_nw (hadj_symm h))
        rcases h_in_LR x y hxy with hxL | hxR <;>
          rcases h_in_LR y x (hadj_symm hxy) with hyL | hyR
        · exact absurd hxy (h_nL x hxL y hyL)
        · exact Or.inl ⟨hxL, hyR⟩
        · exact Or.inr ⟨hxR, hyL⟩
        · exact absurd hxy (h_nR x hxR y hyR)
      exact (ker_one_sub_adj_le_one_of_bipartite adj hadj_symm L' R' hdisj hbip hNo2K2).trans (by norm_num)

end NoPillarCase

/-- No-pillar case (`¬ HasPillar u`): `n ≤ d + 6` for all `d, n`. -/
private lemma lemmens_seidel_no_pillar_case {d n : ℕ}
    {v : Fin n → EuclideanSpace ℝ (Fin d)}
    (hv : IsEquiangularSystem d n (1 / 3) v)
    (hnopillar : ¬ HasPillar (fun i => Real.sqrt 3 • v i)) :
    n ≤ d + 6 := by
  classical
  cases n with
  | zero => omega
  | succ m =>
    let v0 : Fin (m + 1) := 0
    let u : Fin (m + 1) → EuclideanSpace ℝ (Fin d) := fun i => Real.sqrt 3 • v i
    have hu_norm : ∀ i, ⟪u i, u i⟫_ℝ = 3 := by
      intro i
      simp only [u, real_inner_smul_left, real_inner_smul_right]
      rw [real_inner_self_eq_norm_sq, hv.2.2.1 i]
      norm_num [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    have hu_inner : ∀ i j, i ≠ j → ⟪u i, u j⟫_ℝ = 1 ∨ ⟪u i, u j⟫_ℝ = -1 := by
      intro i j hij
      have habs : |⟪u i, u j⟫_ℝ| = 1 := by
        simp only [u, real_inner_smul_left, real_inner_smul_right, abs_mul]
        rw [abs_of_nonneg (Real.sqrt_nonneg 3), hv.2.2.2 i j hij]
        have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
        linarith
      exact abs_eq (zero_le_one' ℝ) |>.mp habs
    let s : Fin (m + 1) → ℝ := fun i =>
      if i = v0 then 1 else if ⟪u i, u v0⟫_ℝ = 1 then 1 else -1
    have hs_pm : ∀ i, s i = 1 ∨ s i = -1 := fun i => by
      by_cases h1 : i = v0
      · simp [s, h1]
      · by_cases h2 : ⟪u i, u v0⟫_ℝ = 1 <;> simp [s, h1, h2]
    let u' : Fin (m + 1) → EuclideanSpace ℝ (Fin d) := fun i => s i • u i
    have hu'_norm : ∀ i, ⟪u' i, u' i⟫_ℝ = 3 := by
      intro i
      simp only [u', real_inner_smul_left, real_inner_smul_right, hu_norm i]
      rcases hs_pm i with h | h <;> simp [h]
    have hu'_inner : ∀ i j, i ≠ j → ⟪u' i, u' j⟫_ℝ = 1 ∨ ⟪u' i, u' j⟫_ℝ = -1 := by
      intro i j hij
      simp only [u', real_inner_smul_left, real_inner_smul_right]
      rcases hs_pm i with hi | hi <;> rcases hs_pm j with hj | hj <;>
        rcases hu_inner i j hij with h | h <;> simp [hi, hj, h]
    have hu'_v0 : ∀ i, i ≠ v0 → ⟪u' v0, u' i⟫_ℝ = 1 := by
      intro i hi
      rw [real_inner_comm]
      have hs0 : s v0 = 1 := by simp [s]
      simp only [u', hs0, one_smul, real_inner_smul_left]
      by_cases h : ⟪u i, u v0⟫_ℝ = 1
      · simp [s, hi, h]
      · have hneg := (hu_inner i v0 hi).resolve_left h
        simp [s, hi, hneg]
        norm_num
    have hnopillar' : ¬ HasPillar u' := by
      rintro ⟨a, b, c, e, hab, hac, hae, hbc, hbe, hce,
        sa, sb, sc, se, hsa, hsb, hsc, hse, hsum⟩
      apply hnopillar
      refine ⟨a, b, c, e, hab, hac, hae, hbc, hbe, hce,
        sa * s a, sb * s b, sc * s c, se * s e, ?_, ?_, ?_, ?_, ?_⟩
      · rcases hsa with h1 | h1 <;> rcases hs_pm a with h2 | h2 <;> simp [h1, h2]
      · rcases hsb with h1 | h1 <;> rcases hs_pm b with h2 | h2 <;> simp [h1, h2]
      · rcases hsc with h1 | h1 <;> rcases hs_pm c with h2 | h2 <;> simp [h1, h2]
      · rcases hse with h1 | h1 <;> rcases hs_pm e with h2 | h2 <;> simp [h1, h2]
      · simpa only [u', u, smul_smul, mul_assoc] using hsum
    let adj : Fin (m + 1) → Fin (m + 1) → Prop := fun i j => i ≠ j ∧ ⟪u' i, u' j⟫_ℝ = -1
    have hadj_symm : ∀ {x y}, adj x y → adj y x := fun {_ _} ⟨hij, h⟩ =>
      ⟨hij.symm, by rw [real_inner_comm]; exact h⟩
    have hadj_irrefl : ∀ i, ¬ adj i i := fun i ⟨h, _⟩ => h rfl
    have hadj_v0 : ∀ i, ¬ adj v0 i := fun i ⟨hne, h⟩ => by
      have := hu'_v0 i hne.symm
      linarith
    have hNoK3 : ∀ a b c : Fin (m + 1), ¬ (adj a b ∧ adj b c ∧ adj c a) := by
      rintro a b c ⟨hab, hbc, hca⟩
      have ha0 : a ≠ v0 := fun h => hadj_v0 b (h ▸ hab)
      have hb0 : b ≠ v0 := fun h => hadj_v0 c (h ▸ hbc)
      have hc0 : c ≠ v0 := fun h => hadj_v0 a (h ▸ hca)
      have hv0a : ⟪u' a, u' v0⟫_ℝ = 1 := by rw [real_inner_comm]; exact hu'_v0 a ha0
      have hv0b : ⟪u' b, u' v0⟫_ℝ = 1 := by rw [real_inner_comm]; exact hu'_v0 b hb0
      have hv0c : ⟪u' c, u' v0⟫_ℝ = 1 := by rw [real_inner_comm]; exact hu'_v0 c hc0
      have hba : ⟪u' b, u' a⟫_ℝ = -1 := by rw [real_inner_comm]; exact hab.2
      have hca' : ⟪u' c, u' a⟫_ℝ = -1 := hca.2
      have hac' : ⟪u' a, u' c⟫_ℝ = -1 := by rw [real_inner_comm]; exact hca.2
      have hcb : ⟪u' c, u' b⟫_ℝ = -1 := by rw [real_inner_comm]; exact hbc.2
      have hsum_sq : ⟪(-1 : ℝ) • u' v0 + u' a + u' b + u' c,
          (-1 : ℝ) • u' v0 + u' a + u' b + u' c⟫_ℝ = 0 := by
        simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
        rw [hu'_norm v0, hu'_norm a, hu'_norm b, hu'_norm c,
          hu'_v0 a ha0, hu'_v0 b hb0, hu'_v0 c hc0, hv0a, hv0b, hv0c,
          hab.2, hba, hbc.2, hcb, hca', hac']
        ring
      have h0 : (-1 : ℝ) • u' v0 + u' a + u' b + u' c = 0 :=
        norm_eq_zero.mp (sq_eq_zero_iff.mp (by rwa [← real_inner_self_eq_norm_sq]))
      exact hnopillar' ⟨v0, a, b, c, ha0.symm, hb0.symm, hc0.symm, hab.1, hca.1.symm, hbc.1,
        -1, 1, 1, 1, Or.inr rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, by simpa using h0⟩
    have hNo2K2 : ∀ a b c e : Fin (m + 1),
        a ≠ b → a ≠ c → a ≠ e → b ≠ c → b ≠ e → c ≠ e →
        adj a b → adj c e → ¬ adj a c → ¬ adj a e → ¬ adj b c → ¬ adj b e → False := by
      intro a b c e hab hac hae hbc hbe hce had_ab had_ce hnac hnae hnbc hnbe
      have hpos : ∀ p q, p ≠ q → ¬ adj p q → ⟪u' p, u' q⟫_ℝ = 1 := fun p q hpq hn =>
        (hu'_inner p q hpq).resolve_right fun h => hn ⟨hpq, h⟩
      have hba : ⟪u' b, u' a⟫_ℝ = -1 := by rw [real_inner_comm]; exact had_ab.2
      have hec : ⟪u' e, u' c⟫_ℝ = -1 := by rw [real_inner_comm]; exact had_ce.2
      have hca : ⟪u' c, u' a⟫_ℝ = 1 := by rw [real_inner_comm]; exact hpos a c hac hnac
      have hea : ⟪u' e, u' a⟫_ℝ = 1 := by rw [real_inner_comm]; exact hpos a e hae hnae
      have hcb : ⟪u' c, u' b⟫_ℝ = 1 := by rw [real_inner_comm]; exact hpos b c hbc hnbc
      have heb : ⟪u' e, u' b⟫_ℝ = 1 := by rw [real_inner_comm]; exact hpos b e hbe hnbe
      have hsum_sq : ⟪u' a + u' b + (-1 : ℝ) • u' c + (-1 : ℝ) • u' e,
          u' a + u' b + (-1 : ℝ) • u' c + (-1 : ℝ) • u' e⟫_ℝ = 0 := by
        simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
        rw [hu'_norm a, hu'_norm b, hu'_norm c, hu'_norm e,
          had_ab.2, hba, had_ce.2, hec,
          hpos a c hac hnac, hca, hpos a e hae hnae, hea,
          hpos b c hbc hnbc, hcb, hpos b e hbe hnbe, heb]
        ring
      have h0 : u' a + u' b + (-1 : ℝ) • u' c + (-1 : ℝ) • u' e = 0 :=
        norm_eq_zero.mp (sq_eq_zero_iff.mp (by rwa [← real_inner_self_eq_norm_sq]))
      exact hnopillar' ⟨a, b, c, e, hab, hac, hae, hbc, hbe, hce,
        1, 1, -1, -1, Or.inl rfl, Or.inl rfl, Or.inr rfl, Or.inr rfl, by simpa using h0⟩
    let v' : Fin (m + 1) → EuclideanSpace ℝ (Fin d) := fun i => s i • v i
    let G' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := Matrix.of fun i j => ⟪u' i, u' j⟫_ℝ
    have hG'_eq : G' = (3 : ℝ) • gramMatrix v' := by
      ext i j
      dsimp only [G', gramMatrix, u', v', u]
      simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
        real_inner_smul_left, real_inner_smul_right]
      have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
      calc _ = s j * (s i * ((Real.sqrt 3 * Real.sqrt 3) * ⟪v i, v j⟫_ℝ)) := by ring
        _ = s j * (s i * (3 * ⟪v i, v j⟫_ℝ)) := by rw [h3]
        _ = 3 * (s j * (s i * ⟪v i, v j⟫_ℝ)) := by ring
    have hG'_rank : G'.rank ≤ d := by
      rw [hG'_eq, Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero (by norm_num))]
      exact gramMatrix_rank_le v'
    let A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := Matrix.of fun i j => if adj i j then 1 else 0
    let J : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := Matrix.of fun _ _ => 1
    have hG'_decomp : G' = (2 : ℝ) • (1 - A) + J := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp only [G', A, J, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
          Matrix.one_apply_eq, Matrix.of_apply, hadj_irrefl i, ↓reduceIte, sub_zero, smul_eq_mul]
        rw [hu'_norm i]
        norm_num
      · by_cases had : adj i j
        · simp [G', A, J, hij, had, had.2]
          norm_num
        · have h1 := (hu'_inner i j hij).resolve_right fun h => had ⟨hij, h⟩
          simp [G', A, J, hij, had, h1]
    let S1 : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun x => ∑ i, x i
        map_add' := fun x y => by simp [Finset.sum_add_distrib]
        map_smul' := fun c x => by simp [Finset.mul_sum] }
    let K : Submodule ℝ (Fin (m + 1) → ℝ) := LinearMap.ker G'.mulVecLin
    let W : Submodule ℝ (Fin (m + 1) → ℝ) := K ⊓ LinearMap.ker S1
    have hW_le : W ≤ LinearMap.ker (1 - A).mulVecLin := by
      intro x hx
      rcases Submodule.mem_inf.mp hx with ⟨hxK, hxS⟩
      rw [LinearMap.mem_ker] at hxK hxS ⊢
      have hJx : J *ᵥ x = 0 := by
        ext i
        simpa [J, Matrix.mulVec, dotProduct, S1] using hxS
      have hGx : (2 : ℝ) • ((1 - A) *ᵥ x) + J *ᵥ x = 0 := by
        rw [mulVecLin_apply, hG'_decomp, Matrix.add_mulVec, Matrix.smul_mulVec] at hxK
        exact hxK
      rw [hJx, add_zero, smul_eq_zero_iff_right (by norm_num : (2 : ℝ) ≠ 0)] at hGx
      exact hGx
    have hK_rank : m + 1 - d ≤ Module.finrank ℝ K := by
      have hrk := LinearMap.finrank_range_add_finrank_ker G'.mulVecLin
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hrk
      change G'.rank + Module.finrank ℝ K = m + 1 at hrk
      omega
    have hS1_rank : m ≤ Module.finrank ℝ (LinearMap.ker S1) := by
      have hrk := LinearMap.finrank_range_add_finrank_ker S1
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hrk
      have hrange : Module.finrank ℝ (LinearMap.range S1) ≤ 1 := by
        simpa [Module.finrank_self] using (LinearMap.range S1).finrank_le
      omega
    have hW_rank : m + 1 - d - 1 ≤ Module.finrank ℝ W := by
      have hsup := Submodule.finrank_sup_add_finrank_inf_eq K (LinearMap.ker S1)
      have hle : Module.finrank ℝ ↥(K ⊔ LinearMap.ker S1) ≤ m + 1 := by
        simpa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
          Submodule.finrank_le (K ⊔ LinearMap.ker S1)
      change Module.finrank ℝ ↥(K ⊔ LinearMap.ker S1) + Module.finrank ℝ W =
        Module.finrank ℝ K + Module.finrank ℝ (LinearMap.ker S1) at hsup
      omega
    have h5 := ker_one_sub_adj_le_five adj hadj_symm hadj_irrefl hNoK3 hNo2K2
    have hW_le_5 : Module.finrank ℝ W ≤ 5 := (Submodule.finrank_mono hW_le).trans h5
    omega

/-- **Lemmens–Seidel (`α = 1/3`) bound**: for `d ≥ 15`, any equiangular line system with cosine `1/3`
has at most `2 * (d - 1)` lines. -/
theorem lemmens_seidel_bound {d n : ℕ} (hd : 15 ≤ d)
    {v : Fin n → EuclideanSpace ℝ (Fin d)}
    (hv : IsEquiangularSystem d n (1 / 3) v) :
    n ≤ 2 * (d - 1) := by
  let u : Fin n → EuclideanSpace ℝ (Fin d) := fun i => Real.sqrt 3 • v i
  have hu_norm : ∀ i, ⟪u i, u i⟫_ℝ = 3 := by
    intro i
    simp only [u, real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_self_eq_norm_sq, hv.2.2.1 i]
    norm_num [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hu_inner : ∀ i j, i ≠ j → ⟪u i, u j⟫_ℝ = 1 ∨ ⟪u i, u j⟫_ℝ = -1 := by
    intro i j hij
    have habs : |⟪u i, u j⟫_ℝ| = 1 := by
      simp only [u, real_inner_smul_left, real_inner_smul_right, abs_mul]
      rw [abs_of_nonneg (Real.sqrt_nonneg 3), hv.2.2.2 i j hij]
      have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
      linarith
    exact abs_eq (zero_le_one' ℝ) |>.mp habs
  by_cases hpillar : HasPillar u
  · exact lemmens_seidel_pillar_case hd hu_norm hu_inner hpillar
  · have h6 := lemmens_seidel_no_pillar_case hv hpillar
    omega

end EquiangularLines

end

