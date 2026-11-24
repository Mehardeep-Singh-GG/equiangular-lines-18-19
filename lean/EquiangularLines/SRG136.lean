module

public import EquiangularLines.Spectral

/-!
# Weapon A: Exact Equivalence `(19, 74) idx=136 ↔ SRG(75, 32, 10, 16)`

This module formalizes Section 8.1 (`Theorem 8.1`) of `reports/algebraist.md` completely free
of custom axioms:

1. **`IsSRG` / `ExistsSRG`:** Clean adjacency-matrix characterization of strongly regular graphs
   `SRG(v, k, λ, μ)`.
2. **`idx136_implies_SRG_75_32_10_16`:** Any `74 × 74` Seidel matrix `S` with characteristic
   polynomial `(X + 5)^55 * (X - 15)^17 * (X - 11) * (X - 9)` extends (after switching signs)
   to an adjacency matrix `A75` realizing `ExistsSRG 75 32 10 16`.
3. **`SRG_75_32_10_16_implies_idx136`:** Conversely, deleting any vertex from any
   `SRG(75, 32, 10, 16)` produces a `74 × 74` Seidel matrix with characteristic polynomial
   `(X + 5)^55 * (X - 15)^17 * (X - 11) * (X - 9)`.
4. **`idx136_eliminated_of_not_existsSRG`:** Taking `hno : ¬ ExistsSRG 75 32 10 16` as an
   explicit hypothesis (no custom `axiom`), proves no `74 × 74` Seidel matrix realizes `idx=136`
   and no equiangular system `(19, 74)` realizes that spectrum.
-/

@[expose] public section

open Matrix Polynomial
open scoped BigOperators

namespace EquiangularLines

section SRGDefs

/-- A symmetric `{0, 1}` matrix `A` with zero diagonal is the adjacency matrix of an
`SRG(v, k, lam, mu)` when it is `k`-regular and every pair of distinct vertices has `lam`
common neighbors if adjacent (`A i j = 1`) and `mu` common neighbors if non-adjacent (`A i j = 0`). -/
def IsSRG {v : ℕ} (k lam mu : ℕ) (A : Matrix (Fin v) (Fin v) ℤ) : Prop :=
  Aᵀ = A ∧
  (∀ i, A i i = 0) ∧
  (∀ i j, i ≠ j → A i j = 0 ∨ A i j = 1) ∧
  (∀ i, (∑ j : Fin v, A i j) = (k : ℤ)) ∧
  (∀ i j, i ≠ j → A i j = 1 → (A * A) i j = (lam : ℤ)) ∧
  (∀ i j, i ≠ j → A i j = 0 → (A * A) i j = (mu : ℤ))

/-- Existence of a strongly regular graph `SRG(v, k, lam, mu)`. -/
def ExistsSRG (v k lam mu : ℕ) : Prop :=
  ∃ A : Matrix (Fin v) (Fin v) ℤ, IsSRG k lam mu A

/-- Matrix-algebraic sufficient criterion for `IsSRG k lam mu A`. -/
theorem isSRG_of_matrix_eq {v k lam mu : ℕ} {A : Matrix (Fin v) (Fin v) ℤ}
    (hsymm : Aᵀ = A) (hdiag : ∀ i, A i i = 0)
    (h01 : ∀ i j, i ≠ j → A i j = 0 ∨ A i j = 1)
    (hdeg : ∀ i, (∑ j : Fin v, A i j) = (k : ℤ))
    (hsq : A * A =
      ((k : ℤ) - (mu : ℤ)) • (1 : Matrix (Fin v) (Fin v) ℤ) +
      ((lam : ℤ) - (mu : ℤ)) • A +
      (mu : ℤ) • Matrix.of (fun _ _ => (1 : ℤ))) :
    IsSRG k lam mu A := by
  refine ⟨hsymm, hdiag, h01, hdeg, fun i j hij h1 => ?_, fun i j hij h0 => ?_⟩
  · have he := congrArg (fun M : Matrix (Fin v) (Fin v) ℤ => M i j) hsq
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hij, Matrix.of_apply,
      smul_eq_mul, mul_zero, zero_add, mul_one, h1] at he
    linarith
  · have he := congrArg (fun M : Matrix (Fin v) (Fin v) ℤ => M i j) hsq
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hij, Matrix.of_apply,
      smul_eq_mul, mul_zero, zero_add, mul_one, h0] at he
    linarith

/-- Converse algebraic identity for any `SRG(v, k, lam, mu)` adjacency matrix `A`:
`A * A = (k - mu) • 1 + (lam - mu) • A + mu • J`. -/
theorem isSRG_matrix_eq {v k lam mu : ℕ} {A : Matrix (Fin v) (Fin v) ℤ}
    (hA : IsSRG k lam mu A) :
    A * A =
      ((k : ℤ) - (mu : ℤ)) • (1 : Matrix (Fin v) (Fin v) ℤ) +
      ((lam : ℤ) - (mu : ℤ)) • A +
      (mu : ℤ) • Matrix.of (fun _ _ => (1 : ℤ)) := by
  rcases hA with ⟨hsymm, hdiag, h01, hdeg, hlam, hmu⟩
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  by_cases hij : i = j
  · subst hij
    have hdiag_sq : (A * A) i i = ∑ x : Fin v, A i x := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hAx : A x i = A i x := congrArg (fun M : Matrix (Fin v) (Fin v) ℤ => M i x) hsymm
      rw [hAx]
      by_cases hix : i = x
      · subst hix; simp [hdiag i]
      · rcases h01 i x hix with h | h <;> simp [h]
    rw [hdiag_sq, hdeg i, hdiag i]
    simp only [↓reduceIte]
    ring
  · simp only [hij, ↓reduceIte, zero_add]
    rcases h01 i j hij with h0 | h1
    · rw [hmu i j hij h0, h0]
      ring
    · rw [hlam i j hij h1, h1]
      ring

end SRGDefs

section SpectralHelpers

private lemma seidel_hermitian_real {n : ℕ} {S : Matrix (Fin n) (Fin n) ℤ}
    (hS : IsSeidelMatrix S) :
    (S.map (Int.castRingHom ℝ)).IsHermitian := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, star_trivial]
  exact congrArg (fun M : Matrix (Fin n) (Fin n) ℤ => (M i j : ℝ)) hS.1

private lemma hermitian_charpoly_eq_prod' {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) :
    A.charpoly = ∏ i : Fin n, (X - C (hA.eigenvalues i)) := by
  have hspec := hA.spectral_theorem
  have hAeq :
      A = (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
        Matrix.diagonal hA.eigenvalues *
        (star hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) := by
    simpa [RCLike.ofReal_real_eq_id] using hspec
  let U : Matrix (Fin n) (Fin n) ℝ := hA.eigenvectorUnitary
  let Ustar : Matrix (Fin n) (Fin n) ℝ := star hA.eigenvectorUnitary
  have hUU : U * Ustar = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hmap1 : U.map C * Ustar.map C = 1 := by
    rw [← Matrix.map_mul, hUU]
    refine Matrix.ext fun i j => ?_
    rw [Matrix.map_apply]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hchar :
      charmatrix (U * Matrix.diagonal hA.eigenvalues * Ustar) =
        U.map C * charmatrix (Matrix.diagonal hA.eigenvalues) * Ustar.map C := by
    have hsc : U.map C * Matrix.scalar (Fin n) (X : ℝ[X]) * Ustar.map C =
        Matrix.scalar (Fin n) (X : ℝ[X]) := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.map_apply]
      have hinner : ∀ k : Fin n, (∑ x : Fin n,
          (C (U i x) * (if x = k then (X : ℝ[X]) else 0)) * C (Ustar k j)) =
          C (U i k * Ustar k j) * X := by
        intro k
        rw [Finset.sum_eq_single k]
        · simp [map_mul]; ring
        · intro x _ hxk; simp [hxk]
        · intro hk; exact False.elim (hk (Finset.mem_univ k))
      have houter : (∑ k : Fin n, ∑ x : Fin n,
          (C (U i x) * (if x = k then (X : ℝ[X]) else 0)) * C (Ustar k j)) =
          C (∑ k : Fin n, U i k * Ustar k j) * X := by
        simp_rw [hinner, ← Finset.sum_mul, ← map_sum]
      have hsum_comm : (∑ j_1 : Fin n, (∑ j_2 : Fin n,
          C (U i j_2) * (if j_2 = j_1 then (X : ℝ[X]) else 0)) * C (Ustar j_1 j)) =
          ∑ k : Fin n, ∑ x : Fin n,
            (C (U i x) * (if x = k then (X : ℝ[X]) else 0)) * C (Ustar k j) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul]
      rw [hsum_comm, houter]
      have hUU_ij : (∑ k : Fin n, U i k * Ustar k j) = if i = j then 1 else 0 := by
        simpa [Matrix.mul_apply, Matrix.one_apply] using
          congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hUU
      rw [hUU_ij]
      by_cases hij : i = j <;> simp [hij]
    rw [charmatrix, charmatrix]
    simp only [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.mul_sub, Matrix.sub_mul]
    rw [hsc]
  conv_lhs => rw [hAeq]
  change (charmatrix (U * Matrix.diagonal hA.eigenvalues * Ustar)).det = _
  rw [hchar, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
    hmap1, Matrix.det_one, one_mul]
  change (Matrix.diagonal hA.eigenvalues).charpoly = _
  rw [Matrix.charpoly_diagonal]

private lemma roots_prod_X_sub_C' {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∏ i ∈ s, (X - C (f i))).roots = s.val.map f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hprod_ne : (∏ i ∈ s, (X - C (f i))) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => X_sub_C_ne_zero _)
    rw [Finset.prod_insert ha, roots_mul (mul_ne_zero (X_sub_C_ne_zero _) hprod_ne),
      roots_X_sub_C, ih, Finset.insert_val_of_notMem ha, Multiset.map_cons,
      ← Multiset.singleton_add, add_comm]

private lemma multiset_count_map_eq_filter_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (s : Finset α) (y : β) :
    Multiset.count y (s.val.map f) = (s.filter (fun x => f x = y)).card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.insert_val_of_notMem ha, Multiset.map_cons, Multiset.count_cons, Finset.filter_insert]
    by_cases hfa : f a = y
    · simp only [hfa, ↓reduceIte, ih]
      have hmem : a ∉ s.filter (fun x => f x = y) := fun h => ha (Finset.mem_filter.mp h).1
      rw [Finset.card_insert_of_notMem hmem]
    · simp only [hfa, Ne.symm hfa, ↓reduceIte, ih, add_zero]

private lemma prod_X_sub_C_eq_of_counts {n : ℕ} (f : Fin n → ℝ)
    (a b c d : ℕ)
    (hcount1 : (Finset.univ.filter (fun k : Fin n => f k = -5)).card = a)
    (hcount2 : (Finset.univ.filter (fun k : Fin n => f k = 15)).card = b)
    (hcount3 : (Finset.univ.filter (fun k : Fin n => f k = 11)).card = c)
    (hcount4 : (Finset.univ.filter (fun k : Fin n => f k = 9)).card = d)
    (hall : ∀ k : Fin n, f k = -5 ∨ f k = 15 ∨ f k = 11 ∨ f k = 9) :
    (∏ k : Fin n, (X - C (f k))) =
      (X + C (5 : ℝ)) ^ a * (X - C (15 : ℝ)) ^ b * (X - C (11 : ℝ)) ^ c *
        (X - C (9 : ℝ)) ^ d := by
  classical
  have hpart :
      (Finset.univ : Finset (Fin n)) =
        Finset.univ.filter (fun k => f k = -5) ∪
          (Finset.univ.filter (fun k => f k = 15) ∪
            (Finset.univ.filter (fun k => f k = 11) ∪
              Finset.univ.filter (fun k => f k = 9))) := by
    ext k
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
    exact hall k
  have hd1 : Disjoint (Finset.univ.filter (fun k : Fin n => f k = -5))
      (Finset.univ.filter (fun k => f k = 15) ∪
        (Finset.univ.filter (fun k => f k = 11) ∪ Finset.univ.filter (fun k => f k = 9))) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and] at hk1 hk2
    rcases hk2 with h | h | h <;> linarith
  have hd2 : Disjoint (Finset.univ.filter (fun k : Fin n => f k = 15))
      (Finset.univ.filter (fun k => f k = 11) ∪ Finset.univ.filter (fun k => f k = 9)) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and] at hk1 hk2
    rcases hk2 with h | h <;> linarith
  have hd3 : Disjoint (Finset.univ.filter (fun k : Fin n => f k = 11))
      (Finset.univ.filter (fun k => f k = 9)) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk1 hk2
    linarith
  rw [hpart, Finset.prod_union hd1, Finset.prod_union hd2, Finset.prod_union hd3]
  have hp1 : (∏ k ∈ Finset.univ.filter (fun k : Fin n => f k = -5), (X - C (f k))) =
      (X + C (5 : ℝ)) ^ a := by
    rw [← hcount1, ← Finset.prod_const]
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [(Finset.mem_filter.mp hk).2, map_neg, sub_neg_eq_add]
  have hp2 : (∏ k ∈ Finset.univ.filter (fun k : Fin n => f k = 15), (X - C (f k))) =
      (X - C (15 : ℝ)) ^ b := by
    rw [← hcount2, ← Finset.prod_const]
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [(Finset.mem_filter.mp hk).2]
  have hp3 : (∏ k ∈ Finset.univ.filter (fun k : Fin n => f k = 11), (X - C (f k))) =
      (X - C (11 : ℝ)) ^ c := by
    rw [← hcount3, ← Finset.prod_const]
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [(Finset.mem_filter.mp hk).2]
  have hp4 : (∏ k ∈ Finset.univ.filter (fun k : Fin n => f k = 9), (X - C (f k))) =
      (X - C (9 : ℝ)) ^ d := by
    rw [← hcount4, ← Finset.prod_const]
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [(Finset.mem_filter.mp hk).2]
  rw [hp1, hp2, hp3, hp4]
  ring

end SpectralHelpers

section WeaponA

private lemma srg75_of_seidel74_block
    (S' : Matrix (Fin 74) (Fin 74) ℤ) (hS' : IsSeidelMatrix S')
    (w : Fin 74 → ℤ) (hw_pm : ∀ i : Fin 74, w i = 1 ∨ w i = -1)
    (hw_dot : w ⬝ᵥ w = 74) (hw_sum : ∑ i : Fin 74, w i = 10)
    (hS'_w : S' *ᵥ w = (10 : ℤ) • w - (fun _ => 1))
    (hS'_1 : S' *ᵥ (fun _ => (1 : ℤ)) = (10 : ℤ) • (fun _ => 1) - w)
    (hS'_sq : S' * S' =
      (75 : ℤ) • (1 : Matrix (Fin 74) (Fin 74) ℤ) + (10 : ℤ) • S' -
        Matrix.of (fun _ _ => (1 : ℤ)) - Matrix.vecMulVec w w) :
    ExistsSRG 75 32 10 16 := by
  let S75 : Matrix (Fin 75) (Fin 75) ℤ := Matrix.of fun i j =>
    Fin.cases (Fin.cases 0 w j) (fun a => Fin.cases (w a) (fun b => S' a b) j) i
  have hS75_00 : S75 0 0 = 0 := by simp [S75]
  have hS75_0s : ∀ b : Fin 74, S75 0 b.succ = w b := fun b => by simp [S75]
  have hS75_s0 : ∀ a : Fin 74, S75 a.succ 0 = w a := fun a => by simp [S75]
  have hS75_ss : ∀ a b : Fin 74, S75 a.succ b.succ = S' a b := fun a b => by simp [S75]
  have hS75_symm : S75ᵀ = S75 := by
    ext i j
    rw [Matrix.transpose_apply]
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => rfl
      | succ b => rw [hS75_0s, hS75_s0]
    | succ a =>
      induction j using Fin.cases with
      | zero => rw [hS75_s0, hS75_0s]
      | succ b =>
        rw [hS75_ss, hS75_ss]
        have hsym := congrArg (fun M : Matrix (Fin 74) (Fin 74) ℤ => M a b) hS'.1
        simpa using hsym
  have hS75_diag : ∀ i : Fin 75, S75 i i = 0 := fun i => by
    induction i using Fin.cases with
    | zero => exact hS75_00
    | succ a => rw [hS75_ss, hS'.2.1 a]
  have hS75_off : ∀ i j : Fin 75, i ≠ j → S75 i j = 1 ∨ S75 i j = -1 := fun i j hij => by
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd rfl hij
      | succ b => rw [hS75_0s]; exact hw_pm b
    | succ a =>
      induction j using Fin.cases with
      | zero => rw [hS75_s0]; exact hw_pm a
      | succ b =>
        rw [hS75_ss]
        exact hS'.2.2 a b (fun e => hij (congrArg Fin.succ e))
  have hS75_row : ∀ i : Fin 75, ∑ j : Fin 75, S75 i j = 10 := fun i => by
    rw [Fin.sum_univ_succ]
    induction i using Fin.cases with
    | zero =>
      rw [hS75_00, zero_add]
      simpa [hS75_0s] using hw_sum
    | succ a =>
      have ha1 := congrFun hS'_1 a
      simp only [Matrix.mulVec, dotProduct, mul_one, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at ha1
      rw [hS75_s0]
      simp_rw [hS75_ss]
      linarith
  have hS75_sq : S75 * S75 =
      (75 : ℤ) • (1 : Matrix (Fin 75) (Fin 75) ℤ) + (10 : ℤ) • S75 -
        Matrix.of (fun _ _ => (1 : ℤ)) := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.of_apply, smul_eq_mul]
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero =>
        rw [hS75_00, mul_zero, zero_add]
        simp_rw [hS75_0s, hS75_s0]
        simp only [↓reduceIte, mul_one, mul_zero]
        have hsum : ∑ x : Fin 74, w x * w x = 74 := hw_dot
        omega
      | succ b =>
        rw [hS75_00, hS75_0s, zero_mul, zero_add]
        simp_rw [hS75_0s, hS75_ss]
        simp only [(Fin.succ_ne_zero b).symm, ↓reduceIte, mul_zero, zero_add]
        have hb := congrFun hS'_w b
        simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hb
        have hsym : ∑ x : Fin 74, w x * S' x b = ∑ x : Fin 74, S' b x * w x := by
          refine Finset.sum_congr rfl fun x _ => ?_
          have hs := congrArg (fun M : Matrix (Fin 74) (Fin 74) ℤ => M x b) hS'.1
          rw [← hs, mul_comm]
          rfl
        rw [hsym]
        linarith
    | succ a =>
      induction j using Fin.cases with
      | zero =>
        rw [hS75_s0, hS75_00, mul_zero, zero_add]
        simp_rw [hS75_ss, hS75_s0]
        simp only [Fin.succ_ne_zero a, ↓reduceIte, mul_zero, zero_add]
        have ha := congrFun hS'_w a
        simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at ha
        linarith
      | succ b =>
        rw [hS75_s0, hS75_0s, hS75_ss]
        simp_rw [hS75_ss]
        simp only [Fin.succ_inj]
        have hsq := congrArg (fun M : Matrix (Fin 74) (Fin 74) ℤ => M a b) hS'_sq
        simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
          Matrix.one_apply, Matrix.of_apply, Matrix.vecMulVec_apply, smul_eq_mul] at hsq
        linarith
  let A75 : Matrix (Fin 75) (Fin 75) ℤ := Matrix.of fun i j =>
    if i = j then 0 else (1 - S75 i j) / 2
  have h2A75 : (2 : ℤ) • A75 =
      Matrix.of (fun _ _ => (1 : ℤ)) - (1 : Matrix (Fin 75) (Fin 75) ℤ) - S75 := by
    ext i j
    simp only [A75, Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply,
      smul_eq_mul]
    by_cases hij : i = j
    · subst hij; simp [hS75_diag i]
    · simp only [hij, ↓reduceIte]
      rcases hS75_off i j hij with h | h <;> simp [h]
  have hA75_symm : A75ᵀ = A75 := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [A75]
    · have hs : S75 j i = S75 i j :=
        congrArg (fun M : Matrix (Fin 75) (Fin 75) ℤ => M i j) hS75_symm
      simp [A75, hij, Ne.symm hij, hs]
  have hA75_diag : ∀ i : Fin 75, A75 i i = 0 := fun i => by simp [A75]
  have hA75_01 : ∀ i j : Fin 75, i ≠ j → A75 i j = 0 ∨ A75 i j = 1 := fun i j hij => by
    simp only [A75, Matrix.of_apply, hij, ↓reduceIte]
    rcases hS75_off i j hij with h | h <;> simp [h]
  have hA75_deg : ∀ i : Fin 75, ∑ j : Fin 75, A75 i j = 32 := fun i => by
    have hsum : (2 : ℤ) * ∑ j : Fin 75, A75 i j =
        ∑ j : Fin 75, ((1 : ℤ) - (if i = j then 1 else 0) - S75 i j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hij := congrArg (fun M : Matrix (Fin 75) (Fin 75) ℤ => M i j) h2A75
      simpa [Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply, smul_eq_mul]
        using hij
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, hS75_row i] at hsum
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte] at hsum
    omega
  have hA75_sq : A75 * A75 =
      ((32 : ℤ) - 16) • (1 : Matrix (Fin 75) (Fin 75) ℤ) +
      ((10 : ℤ) - 16) • A75 +
      (16 : ℤ) • Matrix.of (fun _ _ => (1 : ℤ)) := by
    let J75 : Matrix (Fin 75) (Fin 75) ℤ := Matrix.of fun _ _ => 1
    have hJJ : J75 * J75 = (75 : ℤ) • J75 := by
      ext i j; simp [J75, Matrix.mul_apply]
    have hAJ : A75 * J75 = (32 : ℤ) • J75 := by
      ext i j; simp [J75, Matrix.mul_apply, hA75_deg i]
    have hJA : J75 * A75 = (32 : ℤ) • J75 := by
      ext i j
      have hcol : ∑ x : Fin 75, A75 x j = 32 := by
        have hsum : ∑ x : Fin 75, A75 x j = ∑ x : Fin 75, A75 j x := by
          refine Finset.sum_congr rfl fun x _ => ?_
          exact congrArg (fun M : Matrix (Fin 75) (Fin 75) ℤ => M x j) hA75_symm.symm
        rw [hsum, hA75_deg j]
      simpa [J75, Matrix.mul_apply] using hcol
    have hSJ : S75 * J75 = (10 : ℤ) • J75 := by
      ext i j; simp [J75, Matrix.mul_apply, hS75_row i]
    have hJS : J75 * S75 = (10 : ℤ) • J75 := by
      ext i j
      have hsum : ∑ x : Fin 75, S75 x j = 10 := by
        have h1 : ∑ x : Fin 75, S75 x j = ∑ x : Fin 75, S75 j x := by
          refine Finset.sum_congr rfl fun x _ => ?_
          exact congrArg (fun M : Matrix (Fin 75) (Fin 75) ℤ => M x j) hS75_symm.symm
        rw [h1, hS75_row j]
      simpa [J75, Matrix.mul_apply] using hsum
    have hS_expr : S75 = J75 - 1 - (2 : ℤ) • A75 := by
      ext i j
      have hij := congrArg (fun M : Matrix (Fin 75) (Fin 75) ℤ => M i j) h2A75
      simp only [J75, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.one_apply,
        smul_eq_mul] at hij ⊢
      linarith
    have h4sq : (4 : ℤ) • (A75 * A75) = (2 • A75) * (2 • A75) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; norm_num
    have h2A' : (2 : ℤ) • A75 = J75 - 1 - S75 := by
      rw [hS_expr]
      ext i j
      simp only [Matrix.sub_apply]
      ring
    have hRHS_4 : ((2 : ℤ) • A75) * ((2 : ℤ) • A75) =
        (64 : ℤ) • (1 : Matrix (Fin 75) (Fin 75) ℤ) - (24 : ℤ) • A75 + (64 : ℤ) • J75 := by
      have hmul : (J75 - 1 - S75) * (J75 - 1 - S75) =
          J75 * J75 - J75 - J75 * S75 - J75 + 1 + S75 - S75 * J75 + S75 + S75 * S75 := by
        noncomm_ring
      rw [h2A', hmul, hJJ, hJS, hSJ, hS75_sq, hS_expr]
      ext i j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, J75,
        Matrix.of_apply, smul_eq_mul]
      ring
    ext i j
    have h1 := congrArg (fun M : Matrix (Fin 75) (Fin 75) ℤ => M i j) (h4sq.trans hRHS_4)
    simp only [J75, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.of_apply, smul_eq_mul] at h1 ⊢
    change 4 * (A75 * A75) i j = _ at h1
    linarith
  exact ⟨A75, isSRG_of_matrix_eq hA75_symm hA75_diag hA75_01 hA75_deg hA75_sq⟩

private lemma srg75_of_seidel_poly_pair
    (S' R' : Matrix (Fin 74) (Fin 74) ℤ) (Aset : Finset (Fin 74))
    (hS' : IsSeidelMatrix S')
    (hR'_eq : (2 : ℤ) • R' =
      (75 : ℤ) • (1 : Matrix (Fin 74) (Fin 74) ℤ) + (10 : ℤ) • S' - S' * S')
    (hA_card : Aset.card = 32) (hAc_card : (Asetᶜ).card = 42)
    (hR'_A : ∀ i j : Fin 74, R' i j = if (i ∈ Aset ↔ j ∈ Aset) then 1 else 0)
    (hpoly11 : (S'.map (Int.castRingHom ℝ) - (11 : ℝ) • 1) *
      (R'.map (Int.castRingHom ℝ) - (42 : ℝ) • 1) * R'.map (Int.castRingHom ℝ) = 0)
    (hpoly9 : (S'.map (Int.castRingHom ℝ) - (9 : ℝ) • 1) *
      (R'.map (Int.castRingHom ℝ) - (32 : ℝ) • 1) * R'.map (Int.castRingHom ℝ) = 0) :
    ExistsSRG 75 32 10 16 := by
  classical
  let S'_R : Matrix (Fin 74) (Fin 74) ℝ := S'.map (Int.castRingHom ℝ)
  let R'_R : Matrix (Fin 74) (Fin 74) ℝ := R'.map (Int.castRingHom ℝ)
  let vA : Fin 74 → ℝ := fun i => if i ∈ Aset then 1 else 0
  let vB : Fin 74 → ℝ := fun i => if i ∈ Aset then 0 else 1
  have hRvA : R'_R *ᵥ vA = (32 : ℝ) • vA := by
    ext i
    simp only [Matrix.mulVec, dotProduct, R'_R, Matrix.map_apply, hR'_A, Pi.smul_apply, smul_eq_mul,
      Int.coe_castRingHom]
    by_cases hi : i ∈ Aset
    · simp only [vA, hi, ↓reduceIte, true_iff, mul_one]
      have hsum : (∑ j : Fin 74, ((if j ∈ Aset then (1 : ℤ) else 0 : ℤ) : ℝ) *
          (if j ∈ Aset then (1 : ℝ) else 0)) = ∑ j : Fin 74, if j ∈ Aset then (1 : ℝ) else 0 := by
        refine Finset.sum_congr rfl fun j _ => by by_cases hj : j ∈ Aset <;> simp [hj]
      rw [hsum, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
        Finset.filter_mem_eq_inter, Finset.univ_inter, nsmul_eq_mul, mul_one, hA_card]
      norm_num
    · simp only [vA, hi, ↓reduceIte, false_iff, mul_zero]
      refine Finset.sum_eq_zero fun j _ => by by_cases hj : j ∈ Aset <;> simp [hj]
  have hRvB : R'_R *ᵥ vB = (42 : ℝ) • vB := by
    ext i
    simp only [Matrix.mulVec, dotProduct, R'_R, Matrix.map_apply, hR'_A, Pi.smul_apply, smul_eq_mul,
      Int.coe_castRingHom]
    by_cases hi : i ∈ Aset
    · simp only [vB, hi, ↓reduceIte, true_iff, mul_zero]
      refine Finset.sum_eq_zero fun j _ => by by_cases hj : j ∈ Aset <;> simp [hj]
    · simp only [vB, hi, ↓reduceIte, false_iff, mul_one]
      have hsum : (∑ j : Fin 74, ((if j ∉ Aset then (1 : ℤ) else 0 : ℤ) : ℝ) *
          (if j ∈ Aset then (0 : ℝ) else 1)) = ∑ j : Fin 74, if j ∉ Aset then (1 : ℝ) else 0 := by
        refine Finset.sum_congr rfl fun j _ => by by_cases hj : j ∈ Aset <;> simp [hj]
      rw [hsum, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
        mul_one]
      have hfc : (Finset.univ.filter (fun j : Fin 74 => j ∉ Aset)) = Asetᶜ := by
        ext j; simp
      rw [hfc, hAc_card]
      norm_num
  have hSvA_R : S'_R *ᵥ vA = (11 : ℝ) • vA := by
    have h0 := congrArg (fun M : Matrix (Fin 74) (Fin 74) ℝ => M *ᵥ vA) hpoly11
    have h1 : (32 : ℝ) • (((S'_R - (11 : ℝ) • 1) * (R'_R - (42 : ℝ) • 1)) *ᵥ vA) = 0 := by
      rw [← Matrix.mulVec_smul, ← hRvA, Matrix.mulVec_mulVec]
      simpa [Matrix.mul_assoc, S'_R, R'_R] using h0
    have h2 : ((S'_R - (11 : ℝ) • 1) * (R'_R - (42 : ℝ) • 1)) *ᵥ vA = 0 := by
      ext i
      have hi := congrFun h1 i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
      change _ = (0 : ℝ) at hi
      change _ = (0 : ℝ)
      linarith
    have hRvA' : (R'_R - (42 : ℝ) • 1) *ᵥ vA = (-10 : ℝ) • vA := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hRvA]
      ext i; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    have h3 : (-10 : ℝ) • ((S'_R - (11 : ℝ) • 1) *ᵥ vA) = 0 := by
      rw [← Matrix.mulVec_smul, ← hRvA', Matrix.mulVec_mulVec]
      exact h2
    have hS0 : (S'_R - (11 : ℝ) • 1) *ᵥ vA = 0 := by
      ext i
      have hi := congrFun h3 i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
      change _ = (0 : ℝ) at hi
      change _ = (0 : ℝ)
      linarith
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hS0
    exact hS0
  have hSvB_R : S'_R *ᵥ vB = (9 : ℝ) • vB := by
    have h0 := congrArg (fun M : Matrix (Fin 74) (Fin 74) ℝ => M *ᵥ vB) hpoly9
    have h1 : (42 : ℝ) • (((S'_R - (9 : ℝ) • 1) * (R'_R - (32 : ℝ) • 1)) *ᵥ vB) = 0 := by
      rw [← Matrix.mulVec_smul, ← hRvB, Matrix.mulVec_mulVec]
      simpa [Matrix.mul_assoc, S'_R, R'_R] using h0
    have h2 : ((S'_R - (9 : ℝ) • 1) * (R'_R - (32 : ℝ) • 1)) *ᵥ vB = 0 := by
      ext i
      have hi := congrFun h1 i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
      change _ = (0 : ℝ) at hi
      change _ = (0 : ℝ)
      linarith
    have hRvB' : (R'_R - (32 : ℝ) • 1) *ᵥ vB = (10 : ℝ) • vB := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hRvB]
      ext i; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    have h3 : (10 : ℝ) • ((S'_R - (9 : ℝ) • 1) *ᵥ vB) = 0 := by
      rw [← Matrix.mulVec_smul, ← hRvB', Matrix.mulVec_mulVec]
      exact h2
    have hS0 : (S'_R - (9 : ℝ) • 1) *ᵥ vB = 0 := by
      ext i
      have hi := congrFun h3 i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
      change _ = (0 : ℝ) at hi
      change _ = (0 : ℝ)
      linarith
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hS0
    exact hS0
  let vA_int : Fin 74 → ℤ := fun i => if i ∈ Aset then 1 else 0
  let vB_int : Fin 74 → ℤ := fun i => if i ∈ Aset then 0 else 1
  have hSvA : S' *ᵥ vA_int = (11 : ℤ) • vA_int := by
    have hvA_cast : ∀ j : Fin 74, ((vA_int j : ℤ) : ℝ) = vA j := fun j => by
      by_cases hj : j ∈ Aset <;> simp [vA, vA_int, hj]
    ext i
    have hr := congrFun hSvA_R i
    refine Int.cast_injective (α := ℝ) ?_
    simp only [Matrix.mulVec, dotProduct, S'_R, Matrix.map_apply, Pi.smul_apply, smul_eq_mul,
      Int.coe_castRingHom] at hr ⊢
    push_cast
    simp only [hvA_cast]
    exact hr
  have hSvB : S' *ᵥ vB_int = (9 : ℤ) • vB_int := by
    have hvB_cast : ∀ j : Fin 74, ((vB_int j : ℤ) : ℝ) = vB j := fun j => by
      by_cases hj : j ∈ Aset <;> simp [vB, vB_int, hj]
    ext i
    have hr := congrFun hSvB_R i
    refine Int.cast_injective (α := ℝ) ?_
    simp only [Matrix.mulVec, dotProduct, S'_R, Matrix.map_apply, Pi.smul_apply, smul_eq_mul,
      Int.coe_castRingHom] at hr ⊢
    push_cast
    simp only [hvB_cast]
    exact hr
  let w : Fin 74 → ℤ := fun i => if i ∈ Aset then -1 else 1
  have hw_pm : ∀ i : Fin 74, w i = 1 ∨ w i = -1 := fun i => by
    by_cases hi : i ∈ Aset <;> simp [w, hi]
  have hw_dot : w ⬝ᵥ w = 74 := by
    have h1 : ∀ i : Fin 74, w i * w i = 1 := fun i => by
      rcases hw_pm i with h | h <;> simp [h]
    simp [dotProduct, h1]
  have hw_sum : ∑ i : Fin 74, w i = 10 := by
    have hsp : (∑ i : Fin 74, w i) = (∑ i ∈ Aset, w i) + ∑ i ∈ Asetᶜ, w i :=
      (Finset.sum_add_sum_compl Aset w).symm
    have h1 : ∑ i ∈ Aset, w i = -(Aset.card : ℤ) := by
      calc
        ∑ i ∈ Aset, w i = ∑ _i ∈ Aset, (-1 : ℤ) :=
          Finset.sum_congr rfl fun i hi => by simp [w, hi]
        _ = -(Aset.card : ℤ) := by simp
    have h2 : ∑ i ∈ Asetᶜ, w i = (Asetᶜ.card : ℤ) := by
      calc
        ∑ i ∈ Asetᶜ, w i = ∑ _i ∈ Asetᶜ, (1 : ℤ) :=
          Finset.sum_congr rfl fun i hi => by simp [w, Finset.mem_compl.mp hi]
        _ = (Asetᶜ.card : ℤ) := by simp
    rw [hsp, h1, h2, hA_card, hAc_card]
    norm_num
  have hS'_w : S' *ᵥ w = (10 : ℤ) • w - (fun _ => 1) := by
    ext i
    have hw_eq : w = vB_int - vA_int := by
      ext j; by_cases hj : j ∈ Aset <;> simp [w, vA_int, vB_int, hj]
    have h1_eq : (fun _ : Fin 74 => (1 : ℤ)) = vB_int + vA_int := by
      ext j; by_cases hj : j ∈ Aset <;> simp [vA_int, vB_int, hj]
    rw [hw_eq, h1_eq, Matrix.mulVec_sub, hSvB, hSvA]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hS'_1 : S' *ᵥ (fun _ => (1 : ℤ)) = (10 : ℤ) • (fun _ => 1) - w := by
    ext i
    have hw_eq : w = vB_int - vA_int := by
      ext j; by_cases hj : j ∈ Aset <;> simp [w, vA_int, vB_int, hj]
    have h1_eq : (fun _ : Fin 74 => (1 : ℤ)) = vB_int + vA_int := by
      ext j; by_cases hj : j ∈ Aset <;> simp [vA_int, vB_int, hj]
    rw [h1_eq, hw_eq, Matrix.mulVec_add, hSvB, hSvA]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hS'_sq : S' * S' =
      (75 : ℤ) • (1 : Matrix (Fin 74) (Fin 74) ℤ) + (10 : ℤ) • S' -
        Matrix.of (fun _ _ => (1 : ℤ)) - Matrix.vecMulVec w w := by
    have h2R : (2 : ℤ) • R' =
        Matrix.of (fun _ _ => (1 : ℤ)) + Matrix.vecMulVec w w := by
      ext i j
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, Matrix.vecMulVec_apply,
        smul_eq_mul, hR'_A i j]
      by_cases hi : i ∈ Aset <;> by_cases hj : j ∈ Aset <;>
        simp only [w, hi, hj, ↓reduceIte, iff_self, iff_true, iff_false, not_true_eq_false] <;>
        norm_num
    ext i j
    have h1 := congrArg (fun M : Matrix (Fin 74) (Fin 74) ℤ => M i j) hR'_eq
    have h2 := congrArg (fun M : Matrix (Fin 74) (Fin 74) ℤ => M i j) h2R
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply] at h1 h2 ⊢
    linarith
  exact srg75_of_seidel74_block S' hS' w hw_pm hw_dot hw_sum hS'_w hS'_1 hS'_sq

/-- **Weapon A (Forward direction, `reports/algebraist.md` Theorem 8.1):**
If a `74 × 74` Seidel matrix `S` has characteristic polynomial
`(X + C 5)^55 * (X - C 15)^17 * (X - C 11) * (X - C 9)`, then there exists a strongly regular
graph `SRG(75, 32, 10, 16)`. -/
theorem idx136_implies_SRG_75_32_10_16 {S : Matrix (Fin 74) (Fin 74) ℤ}
    (hS : IsSeidelMatrix S)
    (hchar : S.charpoly =
      (X + C (5 : ℤ)) ^ 55 * (X - C (15 : ℤ)) ^ 17 * (X - C (11 : ℤ)) * (X - C (9 : ℤ))) :
    ExistsSRG 75 32 10 16 := by
  classical
  let S_R : Matrix (Fin 74) (Fin 74) ℝ := S.map (Int.castRingHom ℝ)
  have hHerm : S_R.IsHermitian := seidel_hermitian_real hS
  have hS_prod : S_R.charpoly = ∏ k : Fin 74, (X - C (hHerm.eigenvalues k)) :=
    hermitian_charpoly_eq_prod' hHerm
  have hSR : S_R.charpoly =
      (X - C (-5 : ℝ)) ^ 55 * (X - C (15 : ℝ)) ^ 17 *
        (X - C (11 : ℝ)) * (X - C (9 : ℝ)) := by
    have hm := congrArg (Polynomial.map (Int.castRingHom ℝ)) hchar
    rw [← Matrix.charpoly_map S (Int.castRingHom ℝ)] at hm
    simpa [S_R, sub_neg_eq_add, C_ofNat] using hm
  have hroots_eq :
      Finset.univ.val.map hHerm.eigenvalues =
        Multiset.replicate 55 (-5 : ℝ) + Multiset.replicate 17 (15 : ℝ) +
          {(11 : ℝ)} + {(9 : ℝ)} := by
    have h1 := congrArg Polynomial.roots (hS_prod.symm.trans hSR)
    rw [roots_prod_X_sub_C'] at h1
    have hne :
        (X - C (-5 : ℝ)) ^ 55 * (X - C (15 : ℝ)) ^ 17 *
          (X - C (11 : ℝ)) * (X - C (9 : ℝ)) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero _))
        (pow_ne_zero _ (X_sub_C_ne_zero _))) (X_sub_C_ne_zero _)) (X_sub_C_ne_zero _)
    rw [roots_mul hne, roots_mul (left_ne_zero_of_mul hne),
      roots_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hne)),
      roots_pow, roots_pow, roots_X_sub_C, roots_X_sub_C, roots_X_sub_C, roots_X_sub_C,
      Multiset.nsmul_singleton, Multiset.nsmul_singleton] at h1
    exact h1
  have hk1_ex : ∃! k1 : Fin 74, hHerm.eigenvalues k1 = 11 := by
    have hcnt : (Finset.univ.filter (fun k : Fin 74 => hHerm.eigenvalues k = 11)).card = 1 := by
      have hc := congrArg (Multiset.count (11 : ℝ)) hroots_eq
      rw [← multiset_count_map_eq_filter_card, hc]
      simp only [Multiset.count_add, Multiset.count_replicate, Multiset.count_singleton]
      norm_num
    rcases Finset.card_eq_one.mp hcnt with ⟨k1, hk1⟩
    refine ⟨k1, ?_, fun k hk => ?_⟩
    · have hm : k1 ∈ Finset.univ.filter (fun k : Fin 74 => hHerm.eigenvalues k = 11) := by
        rw [hk1]; exact Finset.mem_singleton_self k1
      exact (Finset.mem_filter.mp hm).2
    · have hm : k ∈ Finset.univ.filter (fun k : Fin 74 => hHerm.eigenvalues k = 11) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩
      rw [hk1, Finset.mem_singleton] at hm
      exact hm
  have hk2_ex : ∃! k2 : Fin 74, hHerm.eigenvalues k2 = 9 := by
    have hcnt : (Finset.univ.filter (fun k : Fin 74 => hHerm.eigenvalues k = 9)).card = 1 := by
      have hc := congrArg (Multiset.count (9 : ℝ)) hroots_eq
      rw [← multiset_count_map_eq_filter_card, hc]
      simp only [Multiset.count_add, Multiset.count_replicate, Multiset.count_singleton]
      norm_num
    rcases Finset.card_eq_one.mp hcnt with ⟨k2, hk2⟩
    refine ⟨k2, ?_, fun k hk => ?_⟩
    · have hm : k2 ∈ Finset.univ.filter (fun k : Fin 74 => hHerm.eigenvalues k = 9) := by
        rw [hk2]; exact Finset.mem_singleton_self k2
      exact (Finset.mem_filter.mp hm).2
    · have hm : k ∈ Finset.univ.filter (fun k : Fin 74 => hHerm.eigenvalues k = 9) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩
      rw [hk2, Finset.mem_singleton] at hm
      exact hm
  rcases hk1_ex with ⟨k1, hk1_val, hk1_uniq⟩
  rcases hk2_ex with ⟨k2, hk2_val, hk2_uniq⟩
  have hk12 : k1 ≠ k2 := fun h => by
    have := hk1_val.symm.trans (h ▸ hk2_val)
    norm_num at this
  have heig_mem : ∀ k : Fin 74,
      hHerm.eigenvalues k = -5 ∨ hHerm.eigenvalues k = 15 ∨ k = k1 ∨ k = k2 := by
    intro k
    have hmem : hHerm.eigenvalues k ∈ Finset.univ.val.map hHerm.eigenvalues :=
      Multiset.mem_map_of_mem _ (Finset.mem_univ k)
    rw [hroots_eq] at hmem
    simp only [Multiset.mem_add, Multiset.mem_replicate, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, true_and, Multiset.mem_singleton] at hmem
    rcases hmem with ((h | h) | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (hk1_uniq k h)))
    · exact Or.inr (Or.inr (Or.inr (hk2_uniq k h)))
  let R : Matrix (Fin 74) (Fin 74) ℤ := Matrix.of fun i j =>
    (75 * (if i = j then 1 else 0) + 10 * S i j - (S * S) i j) / 2
  have hR_two_mul : (2 : ℤ) • R =
      (75 : ℤ) • (1 : Matrix (Fin 74) (Fin 74) ℤ) + (10 : ℤ) • S - S * S := by
    ext i j
    simp only [R, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply,
      Matrix.of_apply, smul_eq_mul]
    have hdvd : (2 : ℤ) ∣ (75 * (if i = j then 1 else 0) + 10 * S i j - (S * S) i j) := by
      by_cases hij : i = j
      · subst hij
        have hdiag := hS.sq_diag i
        rw [hdiag, hS.2.1 i]
        exact ⟨1, by norm_num⟩
      · simp only [hij, ↓reduceIte, mul_zero, zero_add]
        have hS2_even : Even ((S * S) i j) := by
          rw [Matrix.mul_apply, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
          have hj_mem : j ∈ Finset.univ.erase i :=
            Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
          rw [← Finset.add_sum_erase _ _ hj_mem, hS.2.1 i, hS.2.1 j, zero_mul, mul_zero,
            zero_add, zero_add]
          let rest := (Finset.univ.erase i).erase j
          have hcard : rest.card = 72 := by
            simp only [rest, Finset.card_erase_of_mem hj_mem,
              Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
          have heach_odd : ∀ x ∈ rest, ∃ t : ℤ, S i x * S x j = 2 * t + 1 := fun x hx => by
            have hxj : x ≠ j := (Finset.mem_erase.mp hx).1
            have hxi : x ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
            rcases hS.2.2 i x hxi.symm with h1 | h1 <;>
              rcases hS.2.2 x j hxj with h2 | h2
            · exact ⟨0, by rw [h1, h2]; norm_num⟩
            · exact ⟨-1, by rw [h1, h2]; norm_num⟩
            · exact ⟨-1, by rw [h1, h2]; norm_num⟩
            · exact ⟨0, by rw [h1, h2]; norm_num⟩
          have hsum_mod : (∑ x ∈ rest, S i x * S x j) =
              ∑ x ∈ rest, ((S i x * S x j - 1) + 1) :=
            Finset.sum_congr rfl fun x _ => by ring
          rw [hsum_mod, Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul, mul_one]
          refine Even.add ?_ ⟨36, by norm_num⟩
          rw [even_iff_two_dvd]
          refine Finset.dvd_sum fun x hx => ?_
          rcases heach_odd x hx with ⟨t, ht⟩
          exact ⟨t, by linarith⟩
        rcases hS2_even with ⟨t, ht⟩
        refine ⟨5 * S i j - t, by linarith⟩
    exact Int.mul_ediv_cancel' hdvd
  let U : Matrix (Fin 74) (Fin 74) ℝ := hHerm.eigenvectorUnitary
  have hUU : U * Uᵀ = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self hHerm.eigenvectorUnitary
  have hU'U : Uᵀ * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self hHerm.eigenvectorUnitary
  have hspec : S_R = U * Matrix.diagonal hHerm.eigenvalues * Uᵀ := by
    simpa [U, Matrix.star_eq_conjTranspose, RCLike.ofReal_real_eq_id] using hHerm.spectral_theorem
  have h1_sand : (1 : Matrix (Fin 74) (Fin 74) ℝ) = U * Matrix.diagonal (fun _ => 1) * Uᵀ := by
    rw [Matrix.diagonal_one, Matrix.mul_one, hUU]
  have hsand_mul : ∀ f g : Fin 74 → ℝ,
      (U * Matrix.diagonal f * Uᵀ) * (U * Matrix.diagonal g * Uᵀ) =
        U * Matrix.diagonal (fun k => f k * g k) * Uᵀ := fun f g => by
    calc
      (U * Matrix.diagonal f * Uᵀ) * (U * Matrix.diagonal g * Uᵀ)
          = U * Matrix.diagonal f * (Uᵀ * U) * Matrix.diagonal g * Uᵀ := by
            simp only [Matrix.mul_assoc]
      _ = U * (Matrix.diagonal f * Matrix.diagonal g) * Uᵀ := by
            rw [hU'U, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = U * Matrix.diagonal (fun k => f k * g k) * Uᵀ := by
            rw [Matrix.diagonal_mul_diagonal]
  have hsand_smul : ∀ (c : ℝ) (f : Fin 74 → ℝ),
      c • (U * Matrix.diagonal f * Uᵀ) = U * Matrix.diagonal (fun k => c * f k) * Uᵀ :=
    fun c f => by
      rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.diagonal_smul]
      rfl
  have hsand_add : ∀ f g : Fin 74 → ℝ,
      (U * Matrix.diagonal f * Uᵀ) + (U * Matrix.diagonal g * Uᵀ) =
        U * Matrix.diagonal (fun k => f k + g k) * Uᵀ := fun f g => by
    rw [← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.diagonal_add]
  have hsand_sub : ∀ f g : Fin 74 → ℝ,
      (U * Matrix.diagonal f * Uᵀ) - (U * Matrix.diagonal g * Uᵀ) =
        U * Matrix.diagonal (fun k => f k - g k) * Uᵀ := fun f g => by
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, ← Matrix.diagonal_sub]
  let pR : ℝ → ℝ := fun x => (75 + 10 * x - x ^ 2) / 2
  have hR_real_spec :
      R.map (Int.castRingHom ℝ) =
        U * Matrix.diagonal (fun k => pR (hHerm.eigenvalues k)) * Uᵀ := by
    have hm := congrArg (Matrix.map · (Int.castRingHom ℝ)) hR_two_mul
    have hleft : ((2 : ℤ) • R).map (Int.castRingHom ℝ) =
        (2 : ℝ) • R.map (Int.castRingHom ℝ) := by
      ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.coe_castRingHom,
        Int.cast_mul, Int.cast_ofNat]
    have hmul_SS : (S * S).map (Int.castRingHom ℝ) = S_R * S_R := Matrix.map_mul
    have hright : ((75 : ℤ) • (1 : Matrix (Fin 74) (Fin 74) ℤ) + (10 : ℤ) • S - S * S).map
        (Int.castRingHom ℝ) =
        (75 : ℝ) • (1 : Matrix (Fin 74) (Fin 74) ℝ) + (10 : ℝ) • S_R - S_R * S_R := by
      ext i j
      have hmij : ((S * S) i j : ℝ) = (S_R * S_R) i j :=
        congrArg (fun M : Matrix (Fin 74) (Fin 74) ℝ => M i j) hmul_SS
      simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul, Int.coe_castRingHom]
      push_cast
      rw [hmij]
      have hSij : ((S i j : ℤ) : ℝ) = S_R i j := rfl
      rw [hSij]
    rw [hleft, hright] at hm
    have hR_eq : R.map (Int.castRingHom ℝ) =
        (1 / 2 : ℝ) • ((75 : ℝ) • (1 : Matrix (Fin 74) (Fin 74) ℝ) +
          (10 : ℝ) • S_R - S_R * S_R) := by
      ext i j
      have hij := congrArg (fun M : Matrix (Fin 74) (Fin 74) ℝ => M i j) hm
      simp only [Matrix.smul_apply, smul_eq_mul] at hij ⊢
      linarith
    rw [hR_eq]
    have h75_1 : (75 : ℝ) • (1 : Matrix (Fin 74) (Fin 74) ℝ) =
        U * Matrix.diagonal (fun _ => (75 : ℝ)) * Uᵀ := by
      rw [h1_sand, hsand_smul]
      simp only [mul_one]
    have h10_S : (10 : ℝ) • S_R =
        U * Matrix.diagonal (fun k => 10 * hHerm.eigenvalues k) * Uᵀ := by
      conv_lhs => rw [hspec]
      rw [hsand_smul]
    have hS2 : S_R * S_R = U * Matrix.diagonal (fun k => hHerm.eigenvalues k ^ 2) * Uᵀ := by
      conv_lhs => rw [hspec]
      rw [hsand_mul]
      refine congrArg (fun M => U * M * Uᵀ) (congrArg Matrix.diagonal (funext fun k => by ring))
    rw [h75_1, h10_S, hS2, hsand_add, hsand_sub, hsand_smul]
    refine congrArg (fun M => U * M * Uᵀ) (congrArg Matrix.diagonal (funext fun k => ?_))
    simp [pR]; ring
  have hpR_eval : ∀ k : Fin 74,
      pR (hHerm.eigenvalues k) = if k = k1 then 32 else if k = k2 then 42 else 0 := by
    intro k
    rcases heig_mem k with h | h | rfl | rfl
    · have hk_ne1 : k ≠ k1 := fun e => by rw [e, hk1_val] at h; norm_num at h
      have hk_ne2 : k ≠ k2 := fun e => by rw [e, hk2_val] at h; norm_num at h
      simp [pR, h, hk_ne1, hk_ne2]
      norm_num
    · have hk_ne1 : k ≠ k1 := fun e => by rw [e, hk1_val] at h; norm_num at h
      have hk_ne2 : k ≠ k2 := fun e => by rw [e, hk2_val] at h; norm_num at h
      simp [pR, h, hk_ne1, hk_ne2]
      norm_num
    · simp [pR, hk1_val]
      norm_num
    · simp [pR, hk12.symm, hk2_val]
      norm_num
  let u : Fin 74 → ℝ := fun i => Real.sqrt 32 * U i k1
  let wvec : Fin 74 → ℝ := fun i => Real.sqrt 42 * U i k2
  have hR_gram : ∀ i j : Fin 74, (R i j : ℝ) = u i * u j + wvec i * wvec j := by
    intro i j
    have hij := congrArg (fun M : Matrix (Fin 74) (Fin 74) ℝ => M i j) hR_real_spec
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Matrix.transpose_apply,
      Int.coe_castRingHom, mul_assoc] at hij
    simp_rw [hpR_eval] at hij
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k1)] at hij
    have hk2_mem : k2 ∈ Finset.univ.erase k1 := Finset.mem_erase.mpr ⟨hk12.symm, Finset.mem_univ k2⟩
    rw [← Finset.add_sum_erase _ _ hk2_mem] at hij
    have hrest : ∑ x ∈ (Finset.univ.erase k1).erase k2,
        U i x * ((if x = k1 then (32 : ℝ) else if x = k2 then 42 else 0) * U j x) = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      have hx2 : x ≠ k2 := (Finset.mem_erase.mp hx).1
      have hx1 : x ≠ k1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
      simp [hx1, hx2]
    rw [hrest, add_zero] at hij
    rw [hij]
    simp only [↓reduceIte, hk12.symm]
    have hs32 : Real.sqrt 32 * Real.sqrt 32 = 32 := Real.mul_self_sqrt (by norm_num)
    have hs42 : Real.sqrt 42 * Real.sqrt 42 = 42 := Real.mul_self_sqrt (by norm_num)
    calc
      U i k1 * (32 * U j k1) + U i k2 * (42 * U j k2)
          = (Real.sqrt 32 * U i k1) * (Real.sqrt 32 * U j k1) +
              (Real.sqrt 42 * U i k2) * (Real.sqrt 42 * U j k2) := by
            conv_lhs => rw [← hs32, ← hs42]
            ring
      _ = u i * u j + wvec i * wvec j := rfl
  have hR_diag : ∀ i : Fin 74, R i i = 1 := fun i => by
    have hij := congrArg (fun M : Matrix (Fin 74) (Fin 74) ℤ => M i i) hR_two_mul
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply_eq,
      hS.2.1 i, hS.sq_diag i, smul_eq_mul, mul_one, mul_zero, add_zero] at hij
    omega
  have huw_norm : ∀ i : Fin 74, u i ^ 2 + wvec i ^ 2 = 1 := fun i => by
    have h := hR_gram i i
    rw [hR_diag i, Int.cast_one] at h
    linarith [sq (u i), sq (wvec i)]
  have hR_range : ∀ i j : Fin 74, R i j = 1 ∨ R i j = -1 ∨ R i j = 0 := fun i j => by
    have hsq : ((R i j : ℝ)) ^ 2 ≤ 1 := by
      rw [hR_gram i j]
      nlinarith [huw_norm i, huw_norm j, sq_nonneg (u i * wvec j - wvec i * u j)]
    have hsq_int : (R i j) ^ 2 ≤ 1 := by exact_mod_cast hsq
    have hle : R i j ≤ 1 := by nlinarith
    have hge : -1 ≤ R i j := by nlinarith
    omega
  have hu_sum : ∑ i : Fin 74, u i ^ 2 = 32 := by
    have hcol : ∑ i : Fin 74, U i k1 ^ 2 = 1 := by
      have hc := congrArg (fun M : Matrix (Fin 74) (Fin 74) ℝ => M k1 k1) hU'U
      simpa [Matrix.mul_apply, Matrix.one_apply, sq] using hc
    have hs32 : Real.sqrt 32 ^ 2 = 32 := Real.sq_sqrt (by norm_num)
    calc
      ∑ i : Fin 74, u i ^ 2 = ∑ i : Fin 74, 32 * U i k1 ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        dsimp [u]
        rw [mul_pow, hs32]
      _ = 32 * ∑ i : Fin 74, U i k1 ^ 2 := by rw [← Finset.mul_sum]
      _ = 32 := by rw [hcol, mul_one]
  have hw_sum : ∑ i : Fin 74, wvec i ^ 2 = 42 := by
    have hcol : ∑ i : Fin 74, U i k2 ^ 2 = 1 := by
      have hc := congrArg (fun M : Matrix (Fin 74) (Fin 74) ℝ => M k2 k2) hU'U
      simpa [Matrix.mul_apply, Matrix.one_apply, sq] using hc
    have hs42 : Real.sqrt 42 ^ 2 = 42 := Real.sq_sqrt (by norm_num)
    calc
      ∑ i : Fin 74, wvec i ^ 2 = ∑ i : Fin 74, 42 * U i k2 ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        dsimp [wvec]
        rw [mul_pow, hs42]
      _ = 42 * ∑ i : Fin 74, U i k2 ^ 2 := by rw [← Finset.mul_sum]
      _ = 42 := by rw [hcol, mul_one]
  have huw_orth : ∑ i : Fin 74, u i * wvec i = 0 := by
    have hcol : ∑ i : Fin 74, U i k1 * U i k2 = 0 := by
      have hc := congrArg (fun M : Matrix (Fin 74) (Fin 74) ℝ => M k1 k2) hU'U
      simpa [Matrix.mul_apply, Matrix.one_apply, hk12] using hc
    calc
      ∑ i : Fin 74, u i * wvec i = ∑ i : Fin 74, (Real.sqrt 32 * Real.sqrt 42) * (U i k1 * U i k2) := by
        refine Finset.sum_congr rfl fun i _ => by dsimp [u, wvec]; ring
      _ = (Real.sqrt 32 * Real.sqrt 42) * ∑ i : Fin 74, U i k1 * U i k2 := by rw [← Finset.mul_sum]
      _ = 0 := by rw [hcol, mul_zero]
  have hj0_ex : ∃ j0 : Fin 74, R 0 j0 = 0 := by
    by_contra hno
    push Not at hno
    have hdet0 : ∀ j : Fin 74, (u 0 * wvec j - wvec 0 * u j) ^ 2 = 0 := fun j => by
      have hr2 : (R 0 j : ℝ) ^ 2 = 1 := by
        rcases hR_range 0 j with h | h | h
        · simp [h]
        · simp [h]
        · exact absurd h (hno j)
      rw [hR_gram 0 j] at hr2
      have hid : (u 0 * u j + wvec 0 * wvec j) ^ 2 + (u 0 * wvec j - wvec 0 * u j) ^ 2 =
          (u 0 ^ 2 + wvec 0 ^ 2) * (u j ^ 2 + wvec j ^ 2) := by ring
      rw [hr2, huw_norm 0, huw_norm j, mul_one] at hid
      linarith
    have hsum0 : ∑ j : Fin 74, (u 0 * wvec j - wvec 0 * u j) ^ 2 = 0 :=
      Finset.sum_eq_zero fun j _ => hdet0 j
    have hexp : ∑ j : Fin 74, (u 0 * wvec j - wvec 0 * u j) ^ 2 =
        u 0 ^ 2 * 42 + wvec 0 ^ 2 * 32 := by
      have hterm : ∀ j : Fin 74,
          (u 0 * wvec j - wvec 0 * u j) ^ 2 =
            u 0 ^ 2 * wvec j ^ 2 - 2 * u 0 * wvec 0 * (u j * wvec j) + wvec 0 ^ 2 * u j ^ 2 :=
        fun j => by ring
      simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [hw_sum, hu_sum, huw_orth]
      ring
    rw [hexp] at hsum0
    nlinarith [huw_norm 0, sq_nonneg (u 0), sq_nonneg (wvec 0)]
  rcases hj0_ex with ⟨j0, hj0⟩
  have hu0j0 : u 0 * u j0 + wvec 0 * wvec j0 = 0 := by
    have h := (hR_gram 0 j0).symm
    rw [hj0] at h
    simpa using h
  have hsum_sq_0_j0 : ∀ i : Fin 74, (R i 0) ^ 2 + (R i j0) ^ 2 = 1 := fun i => by
    let s : ℝ := u 0 * wvec j0 - wvec 0 * u j0
    have hs2 : s ^ 2 = 1 := by
      have hsq : s ^ 2 + (u 0 * u j0 + wvec 0 * wvec j0) ^ 2 =
          (u 0 ^ 2 + wvec 0 ^ 2) * (u j0 ^ 2 + wvec j0 ^ 2) := by
        dsimp [s]; ring
      rw [hu0j0, huw_norm 0, huw_norm j0] at hsq
      linarith
    have huj0 : u j0 = -wvec 0 * s := by
      have h1 : u j0 * (u 0 ^ 2 + wvec 0 ^ 2) =
          u 0 * (u 0 * u j0 + wvec 0 * wvec j0) - wvec 0 * s := by
        dsimp [s]; ring
      rw [huw_norm 0, hu0j0] at h1
      linarith
    have hwj0 : wvec j0 = u 0 * s := by
      have h1 : wvec j0 * (u 0 ^ 2 + wvec 0 ^ 2) =
          wvec 0 * (u 0 * u j0 + wvec 0 * wvec j0) + u 0 * s := by
        dsimp [s]; ring
      rw [huw_norm 0, hu0j0] at h1
      linarith
    have hr : ((R i 0 : ℝ)) ^ 2 + ((R i j0 : ℝ)) ^ 2 = 1 := by
      rw [hR_gram i 0, hR_gram i j0, huj0, hwj0]
      calc
        (u i * u 0 + wvec i * wvec 0) ^ 2 + (u i * (-wvec 0 * s) + wvec i * (u 0 * s)) ^ 2
            = (u i * u 0 + wvec i * wvec 0) ^ 2 + s ^ 2 * (-u i * wvec 0 + wvec i * u 0) ^ 2 := by
              ring
        _ = (u i * u 0 + wvec i * wvec 0) ^ 2 + (-u i * wvec 0 + wvec i * u 0) ^ 2 := by
              rw [hs2, one_mul]
        _ = (u i ^ 2 + wvec i ^ 2) * (u 0 ^ 2 + wvec 0 ^ 2) := by ring
        _ = 1 := by rw [huw_norm i, huw_norm 0, mul_one]
    exact_mod_cast hr
  let d : Fin 74 → ℤ := fun i => if R i 0 ≠ 0 then R i 0 else R i j0
  have hd_pm : ∀ i : Fin 74, d i = 1 ∨ d i = -1 := fun i => by
    have h1 := hsum_sq_0_j0 i
    rcases hR_range i 0 with ha | ha | ha <;> rcases hR_range i j0 with hb | hb | hb <;>
      simp [d, ha, hb] at h1 ⊢
  let R' : Matrix (Fin 74) (Fin 74) ℤ := Matrix.diagonal d * R * Matrix.diagonal d
  let S' : Matrix (Fin 74) (Fin 74) ℤ := IsSeidelMatrix.switch d S
  have hS' : IsSeidelMatrix S' := hS.switch_isSeidelMatrix hd_pm
  have hR'_eq : (2 : ℤ) • R' =
      (75 : ℤ) • (1 : Matrix (Fin 74) (Fin 74) ℤ) + (10 : ℤ) • S' - S' * S' := by
    let D := Matrix.diagonal d
    have hDD : D * D = 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij; rcases hd_pm i with h | h <;> simp [D, h]
      · simp [D, hij]
    have hS'S' : S' * S' = D * (S * S) * D := by
      calc
        S' * S' = (D * S * D) * (D * S * D) := rfl
        _ = D * S * (D * D) * S * D := by simp only [Matrix.mul_assoc]
        _ = D * (S * S) * D := by rw [hDD, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    calc
      (2 : ℤ) • R' = D * ((2 : ℤ) • R) * D := by
        dsimp only [R', D]
        rw [← Matrix.smul_mul, ← Matrix.mul_smul]
      _ = D * ((75 : ℤ) • 1 + (10 : ℤ) • S - S * S) * D := by rw [hR_two_mul]
      _ = (75 : ℤ) • (D * D) + (10 : ℤ) • (D * S * D) - D * (S * S) * D := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
          Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      _ = (75 : ℤ) • 1 + (10 : ℤ) • S' - S' * S' := by
        rw [hDD, ← hS'S']
        rfl
  let U1 : Finset (Fin 74) := Finset.univ.filter (fun i => R i 0 ≠ 0)
  let U2 : Finset (Fin 74) := Finset.univ.filter (fun i => R i 0 = 0)
  have hu'_vec : ∀ i : Fin 74,
      d i * R i 0 = (if i ∈ U1 then (1 : ℤ) else 0) ∧
      d i * R i j0 = (if i ∈ U1 then 0 else (1 : ℤ)) := fun i => by
    have h1 := hsum_sq_0_j0 i
    rcases hR_range i 0 with ha | ha | ha <;> rcases hR_range i j0 with hb | hb | hb <;>
      simp [U1, d, ha, hb] at h1 ⊢
  let u' : Fin 74 → ℝ := fun i => (d i : ℝ) * u i
  let w' : Fin 74 → ℝ := fun i => (d i : ℝ) * wvec i
  have hR'_gram : ∀ i j : Fin 74, (R' i j : ℝ) = u' i * u' j + w' i * w' j := fun i j => by
    have hRij : R' i j = d i * R i j * d j := by
      simp [R', Matrix.mul_apply, Matrix.diagonal_apply]
    rw [hRij]
    push_cast
    rw [hR_gram i j]
    dsimp [u', w']
    ring
  have hclass_vec : ∀ i : Fin 74,
      (i ∈ U1 → u' i = u 0 ∧ w' i = wvec 0) ∧
      (i ∉ U1 → u' i = u j0 ∧ w' i = wvec j0) := fun i => by
    have h1 := (hu'_vec i).1
    have h2 := (hu'_vec i).2
    constructor
    · intro hi
      simp only [hi, ↓reduceIte] at h1
      have hr1 : (u' i * u 0 + w' i * wvec 0 : ℝ) = 1 := by
        have hm : ((d i : ℝ) * (R i 0 : ℝ)) = 1 := by exact_mod_cast h1
        rw [hR_gram i 0] at hm
        simpa [u', w'] using by linarith
      have hsq' : (u' i) ^ 2 + (w' i) ^ 2 = 1 := by
        have hd2 : (d i : ℝ) ^ 2 = 1 := by rcases hd_pm i with h | h <;> simp [h]
        calc
          (u' i) ^ 2 + (w' i) ^ 2 = (d i : ℝ) ^ 2 * (u i ^ 2 + wvec i ^ 2) := by
            dsimp [u', w']; ring
          _ = 1 := by rw [hd2, huw_norm i, mul_one]
      have hz : (u' i - u 0) ^ 2 + (w' i - wvec 0) ^ 2 = 0 := by
        nlinarith [hsq', huw_norm 0, hr1]
      exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm (by linarith [sq_nonneg (w' i - wvec 0)])
          (sq_nonneg _))),
        sub_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm (by linarith [sq_nonneg (u' i - u 0)])
          (sq_nonneg _)))⟩
    · intro hi
      simp only [hi, ↓reduceIte] at h2
      have hr2 : (u' i * u j0 + w' i * wvec j0 : ℝ) = 1 := by
        have hm : ((d i : ℝ) * (R i j0 : ℝ)) = 1 := by exact_mod_cast h2
        rw [hR_gram i j0] at hm
        simpa [u', w'] using by linarith
      have hsq' : (u' i) ^ 2 + (w' i) ^ 2 = 1 := by
        have hd2 : (d i : ℝ) ^ 2 = 1 := by rcases hd_pm i with h | h <;> simp [h]
        calc
          (u' i) ^ 2 + (w' i) ^ 2 = (d i : ℝ) ^ 2 * (u i ^ 2 + wvec i ^ 2) := by
            dsimp [u', w']; ring
          _ = 1 := by rw [hd2, huw_norm i, mul_one]
      have hz : (u' i - u j0) ^ 2 + (w' i - wvec j0) ^ 2 = 0 := by
        nlinarith [hsq', huw_norm j0, hr2]
      exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm (by linarith [sq_nonneg (w' i - wvec j0)])
          (sq_nonneg _))),
        sub_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm (by linarith [sq_nonneg (u' i - u j0)])
          (sq_nonneg _)))⟩
  have hR'_blk : ∀ i j : Fin 74, R' i j = if (i ∈ U1 ↔ j ∈ U1) then 1 else 0 := fun i j => by
    have hr : (R' i j : ℝ) = if (i ∈ U1 ↔ j ∈ U1) then 1 else 0 := by
      rw [hR'_gram i j]
      by_cases hi : i ∈ U1 <;> by_cases hj : j ∈ U1
      · simp only [hi, hj, iff_self, ↓reduceIte]
        rw [(hclass_vec i).1 hi |>.1, (hclass_vec i).1 hi |>.2,
          (hclass_vec j).1 hj |>.1, (hclass_vec j).1 hj |>.2]
        nlinarith [huw_norm 0]
      · simp only [hi, hj, iff_false, not_true_eq_false, ↓reduceIte]
        rw [(hclass_vec i).1 hi |>.1, (hclass_vec i).1 hi |>.2,
          (hclass_vec j).2 hj |>.1, (hclass_vec j).2 hj |>.2]
        exact hu0j0
      · simp only [hi, hj, false_iff, not_true_eq_false, ↓reduceIte]
        rw [(hclass_vec i).2 hi |>.1, (hclass_vec i).2 hi |>.2,
          (hclass_vec j).1 hj |>.1, (hclass_vec j).1 hj |>.2]
        linarith [hu0j0]
      · simp only [hi, hj, iff_self, ↓reduceIte]
        rw [(hclass_vec i).2 hi |>.1, (hclass_vec i).2 hi |>.2,
          (hclass_vec j).2 hj |>.1, (hclass_vec j).2 hj |>.2]
        nlinarith [huw_norm j0]
    exact_mod_cast hr
  have hU_compl : U2 = U1ᶜ := by
    ext i; simp [U1, U2]
  have hU_sum_card : U1.card + U2.card = 74 := by
    rw [hU_compl, Finset.card_compl, Fintype.card_fin]
    exact Nat.add_sub_cancel' (Finset.card_le_univ U1)
  have htr_R2 : (R.map (Int.castRingHom ℝ) * R.map (Int.castRingHom ℝ)).trace = 2788 := by
    rw [hR_real_spec]
    have hmul :
        (U * Matrix.diagonal (fun k => pR (hHerm.eigenvalues k)) * Uᵀ) *
            (U * Matrix.diagonal (fun k => pR (hHerm.eigenvalues k)) * Uᵀ) =
          U * Matrix.diagonal (fun k => pR (hHerm.eigenvalues k) ^ 2) * Uᵀ := by
      calc
        (U * Matrix.diagonal (fun k => pR (hHerm.eigenvalues k)) * Uᵀ) *
            (U * Matrix.diagonal (fun k => pR (hHerm.eigenvalues k)) * Uᵀ)
            = U * Matrix.diagonal (fun k => pR (hHerm.eigenvalues k)) * (Uᵀ * U) *
                Matrix.diagonal (fun k => pR (hHerm.eigenvalues k)) * Uᵀ := by
              simp only [Matrix.mul_assoc]
        _ = U * (Matrix.diagonal (fun k => pR (hHerm.eigenvalues k)) *
                Matrix.diagonal (fun k => pR (hHerm.eigenvalues k))) * Uᵀ := by
              rw [hU'U, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = U * Matrix.diagonal (fun k => pR (hHerm.eigenvalues k) ^ 2) * Uᵀ := by
              rw [Matrix.diagonal_mul_diagonal]
              refine congrArg (fun M => U * M * Uᵀ) (congrArg Matrix.diagonal (funext fun k => ?_))
              ring
    rw [hmul, Matrix.trace_mul_cycle, hU'U, Matrix.one_mul, Matrix.trace_diagonal]
    simp_rw [hpR_eval]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k1)]
    have hk2_mem : k2 ∈ Finset.univ.erase k1 := Finset.mem_erase.mpr ⟨hk12.symm, Finset.mem_univ k2⟩
    rw [← Finset.add_sum_erase _ _ hk2_mem]
    have hrest : ∑ x ∈ (Finset.univ.erase k1).erase k2,
        (if x = k1 then (32 : ℝ) else if x = k2 then 42 else 0) ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      have hx2 : x ≠ k2 := (Finset.mem_erase.mp hx).1
      have hx1 : x ≠ k1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
      simp [hx1, hx2]
    rw [hrest, add_zero]
    simp only [↓reduceIte, hk12.symm]
    norm_num
  have htr_R'2 : (R' * R').trace = (U1.card : ℤ) ^ 2 + (U2.card : ℤ) ^ 2 := by
    have hsymm : R'ᵀ = R' := by
      ext i j; simp [hR'_blk, iff_comm]
    have hsum_eq : (R' * R').trace = ∑ i : Fin 74, ∑ j : Fin 74, R' i j := by
      rw [Matrix.trace]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.diag_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hs : R' j i = R' i j := congrArg (fun M : Matrix (Fin 74) (Fin 74) ℤ => M i j) hsymm
      rw [hs]
      by_cases h : (i ∈ U1 ↔ j ∈ U1) <;> simp [hR'_blk i j, h]
    rw [hsum_eq]
    have hrow : ∀ i : Fin 74, ∑ j : Fin 74, R' i j = if i ∈ U1 then (U1.card : ℤ) else U2.card := by
      intro i
      by_cases hi : i ∈ U1
      · simp only [hi, ↓reduceIte, hR'_blk, true_iff]
        simp
      · simp only [hi, ↓reduceIte, hR'_blk, false_iff]
        have hf : Finset.univ.filter (fun j : Fin 74 => j ∉ U1) = U2 := by
          ext j; simp [U1, U2]
        simp [Finset.sum_ite, hf]
    simp_rw [hrow, Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul]
    have hf : Finset.univ.filter (fun i : Fin 74 => i ∉ U1) = U2 := by
      ext i; simp [U1, U2]
    rw [hf, sq, sq]
  have htr_same : ((R' * R').trace : ℝ) =
      (R.map (Int.castRingHom ℝ) * R.map (Int.castRingHom ℝ)).trace := by
    let D := Matrix.diagonal d
    have hDD : D * D = 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij; rcases hd_pm i with h | h <;> simp [D, h]
      · simp [D, hij]
    have hRR : R' * R' = D * (R * R) * D := by
      calc
        R' * R' = (D * R * D) * (D * R * D) := rfl
        _ = D * R * (D * D) * R * D := by simp only [Matrix.mul_assoc]
        _ = D * (R * R) * D := by rw [hDD, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    have htr_int : (R' * R').trace = (R * R).trace := by
      rw [hRR, Matrix.trace_mul_cycle, hDD, Matrix.one_mul]
    rw [htr_int]
    have hm_mat : (R * R).map (Int.castRingHom ℝ) =
        R.map (Int.castRingHom ℝ) * R.map (Int.castRingHom ℝ) := Matrix.map_mul
    have hm := congrArg Matrix.trace hm_mat
    rw [← hm]
    simp [Matrix.trace, Matrix.diag_apply, Matrix.map_apply]
  have hcard_cases : (U1.card = 32 ∧ U2.card = 42) ∨ (U1.card = 42 ∧ U2.card = 32) := by
    have h2788 : (U1.card : ℤ) ^ 2 + (U2.card : ℤ) ^ 2 = 2788 := by
      have hr : (((R' * R').trace : ℤ) : ℝ) = 2788 := by rw [htr_same, htr_R2]
      have hi : (R' * R').trace = 2788 := by exact_mod_cast hr
      linarith [htr_R'2]
    have hsumZ : (U1.card : ℤ) + (U2.card : ℤ) = 74 := by exact_mod_cast hU_sum_card
    have hprod : ((U1.card : ℤ) - 32) * ((U1.card : ℤ) - 42) = 0 := by nlinarith
    rcases mul_eq_zero.mp hprod with h | h <;> omega
  let Aset : Finset (Fin 74) := if U1.card = 32 then U1 else U2
  have hA_card : Aset.card = 32 := by
    rcases hcard_cases with ⟨h1, _⟩ | ⟨h1, h2⟩
    · simp [Aset, h1]
    · simp [Aset, h1, h2]
  have hAc_card : (Asetᶜ).card = 42 := by
    rw [Finset.card_compl, Fintype.card_fin, hA_card]
  have hR'_A : ∀ i j : Fin 74, R' i j = if (i ∈ Aset ↔ j ∈ Aset) then 1 else 0 := fun i j => by
    rw [hR'_blk i j]
    by_cases h32 : U1.card = 32
    · simp [Aset, h32]
    · simp only [Aset, h32, ↓reduceIte, hU_compl, Finset.mem_compl]
      simp [not_iff_not]
  let S'_R : Matrix (Fin 74) (Fin 74) ℝ := S'.map (Int.castRingHom ℝ)
  let R'_R : Matrix (Fin 74) (Fin 74) ℝ := R'.map (Int.castRingHom ℝ)
  let DR : Matrix (Fin 74) (Fin 74) ℝ := (Matrix.diagonal d).map (Int.castRingHom ℝ)
  have hDR2 : DR * DR = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij; rcases hd_pm i with h | h <;> simp [DR, h]
    · simp [DR, hij]
  have hS'_conj : S'_R = DR * S_R * DR := by
    simp only [S'_R, S', IsSeidelMatrix.switch, S_R, DR]
    rw [Matrix.map_mul, Matrix.map_mul]
  have hR'_conj : R'_R = DR * R.map (Int.castRingHom ℝ) * DR := by
    simp only [R'_R, R', DR]
    rw [Matrix.map_mul, Matrix.map_mul]
  have hpoly11 : (S'_R - (11 : ℝ) • 1) * (R'_R - (42 : ℝ) • 1) * R'_R = 0 := by
    have h_base : (S_R - (11 : ℝ) • 1) * (R.map (Int.castRingHom ℝ) - (42 : ℝ) • 1) *
        R.map (Int.castRingHom ℝ) = 0 := by
      have hS11 : S_R - (11 : ℝ) • 1 =
          U * Matrix.diagonal (fun k => hHerm.eigenvalues k - 11) * Uᵀ := by
        conv_lhs => rw [hspec, h1_sand, hsand_smul, hsand_sub]
        simp only [mul_one]
      have hR42 : R.map (Int.castRingHom ℝ) - (42 : ℝ) • 1 =
          U * Matrix.diagonal (fun k => pR (hHerm.eigenvalues k) - 42) * Uᵀ := by
        rw [hR_real_spec, h1_sand, hsand_smul, hsand_sub]
        simp only [mul_one]
      rw [hS11, hR42, hR_real_spec, hsand_mul, hsand_mul]
      have hz : Matrix.diagonal (fun k =>
          (hHerm.eigenvalues k - 11) * (pR (hHerm.eigenvalues k) - 42) *
            pR (hHerm.eigenvalues k)) = 0 := by
        ext a b
        by_cases hab : a = b
        · subst hab
          simp only [Matrix.diagonal_apply_eq, Matrix.zero_apply, hpR_eval]
          by_cases h1 : a = k1
          · subst h1; simp [hk1_val]
          · by_cases h2 : a = k2
            · subst h2; simp [h1]
            · simp [h1, h2]
        · simp [hab]
      rw [hz, Matrix.mul_zero, Matrix.zero_mul]
    have hD11 : (11 : ℝ) • (1 : Matrix (Fin 74) (Fin 74) ℝ) =
        DR * ((11 : ℝ) • (1 : Matrix (Fin 74) (Fin 74) ℝ)) * DR := by
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hDR2]
    have hD42 : (42 : ℝ) • (1 : Matrix (Fin 74) (Fin 74) ℝ) =
        DR * ((42 : ℝ) • (1 : Matrix (Fin 74) (Fin 74) ℝ)) * DR := by
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hDR2]
    have h11_conj : S'_R - (11 : ℝ) • 1 = DR * (S_R - (11 : ℝ) • 1) * DR := by
      rw [Matrix.mul_sub, Matrix.sub_mul, ← hS'_conj, ← hD11]
    have h42_conj : R'_R - (42 : ℝ) • 1 = DR * (R.map (Int.castRingHom ℝ) - (42 : ℝ) • 1) * DR := by
      rw [Matrix.mul_sub, Matrix.sub_mul, ← hR'_conj, ← hD42]
    have hDR_cancel : ∀ X : Matrix (Fin 74) (Fin 74) ℝ, DR * (DR * X) = X := fun X => by
      rw [← Matrix.mul_assoc, hDR2, Matrix.one_mul]
    calc
      (S'_R - (11 : ℝ) • 1) * (R'_R - (42 : ℝ) • 1) * R'_R
          = (DR * (S_R - (11 : ℝ) • 1) * DR) * (DR * (R.map (Int.castRingHom ℝ) - (42 : ℝ) • 1) * DR) *
              (DR * R.map (Int.castRingHom ℝ) * DR) := by
            rw [h11_conj, h42_conj, hR'_conj]
      _ = DR * ((S_R - (11 : ℝ) • 1) * (R.map (Int.castRingHom ℝ) - (42 : ℝ) • 1) *
            R.map (Int.castRingHom ℝ)) * DR := by
            simp only [Matrix.mul_assoc, hDR_cancel]
      _ = 0 := by rw [h_base, Matrix.mul_zero, Matrix.zero_mul]
  have hpoly9 : (S'_R - (9 : ℝ) • 1) * (R'_R - (32 : ℝ) • 1) * R'_R = 0 := by
    have h_base : (S_R - (9 : ℝ) • 1) * (R.map (Int.castRingHom ℝ) - (32 : ℝ) • 1) *
        R.map (Int.castRingHom ℝ) = 0 := by
      have hS9 : S_R - (9 : ℝ) • 1 =
          U * Matrix.diagonal (fun k => hHerm.eigenvalues k - 9) * Uᵀ := by
        conv_lhs => rw [hspec, h1_sand, hsand_smul, hsand_sub]
        simp only [mul_one]
      have hR32 : R.map (Int.castRingHom ℝ) - (32 : ℝ) • 1 =
          U * Matrix.diagonal (fun k => pR (hHerm.eigenvalues k) - 32) * Uᵀ := by
        rw [hR_real_spec, h1_sand, hsand_smul, hsand_sub]
        simp only [mul_one]
      rw [hS9, hR32, hR_real_spec, hsand_mul, hsand_mul]
      have hz : Matrix.diagonal (fun k =>
          (hHerm.eigenvalues k - 9) * (pR (hHerm.eigenvalues k) - 32) *
            pR (hHerm.eigenvalues k)) = 0 := by
        ext a b
        by_cases hab : a = b
        · subst hab
          simp only [Matrix.diagonal_apply_eq, Matrix.zero_apply, hpR_eval]
          by_cases h1 : a = k1
          · subst h1; simp
          · by_cases h2 : a = k2
            · subst h2; simp [h1, hk2_val]
            · simp [h1, h2]
        · simp [hab]
      rw [hz, Matrix.mul_zero, Matrix.zero_mul]
    have hD9 : (9 : ℝ) • (1 : Matrix (Fin 74) (Fin 74) ℝ) =
        DR * ((9 : ℝ) • (1 : Matrix (Fin 74) (Fin 74) ℝ)) * DR := by
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hDR2]
    have hD32 : (32 : ℝ) • (1 : Matrix (Fin 74) (Fin 74) ℝ) =
        DR * ((32 : ℝ) • (1 : Matrix (Fin 74) (Fin 74) ℝ)) * DR := by
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hDR2]
    have h9_conj : S'_R - (9 : ℝ) • 1 = DR * (S_R - (9 : ℝ) • 1) * DR := by
      rw [Matrix.mul_sub, Matrix.sub_mul, ← hS'_conj, ← hD9]
    have h32_conj : R'_R - (32 : ℝ) • 1 = DR * (R.map (Int.castRingHom ℝ) - (32 : ℝ) • 1) * DR := by
      rw [Matrix.mul_sub, Matrix.sub_mul, ← hR'_conj, ← hD32]
    have hDR_cancel : ∀ X : Matrix (Fin 74) (Fin 74) ℝ, DR * (DR * X) = X := fun X => by
      rw [← Matrix.mul_assoc, hDR2, Matrix.one_mul]
    calc
      (S'_R - (9 : ℝ) • 1) * (R'_R - (32 : ℝ) • 1) * R'_R
          = (DR * (S_R - (9 : ℝ) • 1) * DR) * (DR * (R.map (Int.castRingHom ℝ) - (32 : ℝ) • 1) * DR) *
              (DR * R.map (Int.castRingHom ℝ) * DR) := by
            rw [h9_conj, h32_conj, hR'_conj]
      _ = DR * ((S_R - (9 : ℝ) • 1) * (R.map (Int.castRingHom ℝ) - (32 : ℝ) • 1) *
            R.map (Int.castRingHom ℝ)) * DR := by
            simp only [Matrix.mul_assoc, hDR_cancel]
      _ = 0 := by rw [h_base, Matrix.mul_zero, Matrix.zero_mul]
  exact srg75_of_seidel_poly_pair S' R' Aset hS' hR'_eq hA_card hAc_card hR'_A hpoly11 hpoly9

/-- **Weapon A (Converse direction, `reports/algebraist.md` Theorem 8.1):**
Deleting vertex `0` from any `SRG(75, 32, 10, 16)` yields a `74 × 74` Seidel matrix with
characteristic polynomial `(X + C 5)^55 * (X - C 15)^17 * (X - C 11) * (X - C 9)`. -/
theorem SRG_75_32_10_16_implies_idx136 {A75 : Matrix (Fin 75) (Fin 75) ℤ}
    (hA : IsSRG 32 10 16 A75) :
    ∃ S : Matrix (Fin 74) (Fin 74) ℤ,
      IsSeidelMatrix S ∧
      S.charpoly =
        (X + C (5 : ℤ)) ^ 55 * (X - C (15 : ℤ)) ^ 17 * (X - C (11 : ℤ)) * (X - C (9 : ℤ)) := by
  classical
  have hAsymm := hA.1
  have hAdiag := hA.2.1
  have hA01 := hA.2.2.1
  have hAdeg := hA.2.2.2.1
  have hAsq := isSRG_matrix_eq hA
  let J75 : Matrix (Fin 75) (Fin 75) ℤ := Matrix.of fun _ _ => 1
  let S75 : Matrix (Fin 75) (Fin 75) ℤ := J75 - 1 - (2 : ℤ) • A75
  have hS75_symm : S75ᵀ = S75 := by
    ext i j
    have ha : A75 j i = A75 i j := congrArg (fun M : Matrix (Fin 75) (Fin 75) ℤ => M i j) hAsymm
    simp only [S75, J75, Matrix.transpose_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.of_apply, Matrix.one_apply, smul_eq_mul, eq_comm, ha]
  have hS75_row : ∀ i : Fin 75, ∑ j : Fin 75, S75 i j = 10 := fun i => by
    simp only [S75, J75, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.one_apply,
      smul_eq_mul, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, ← Finset.mul_sum, hAdeg i]
    norm_num
  have hS75_sq : S75 * S75 = (75 : ℤ) • (1 : Matrix (Fin 75) (Fin 75) ℤ) + (10 : ℤ) • S75 - J75 := by
    have hJJ : J75 * J75 = (75 : ℤ) • J75 := by ext i j; simp [J75, Matrix.mul_apply]
    have hAJ : A75 * J75 = (32 : ℤ) • J75 := by ext i j; simp [J75, Matrix.mul_apply, hAdeg i]
    have hJA : J75 * A75 = (32 : ℤ) • J75 := by
      ext i j
      have hcol : ∑ x : Fin 75, A75 x j = (32 : ℤ) := by
        have h1 : ∑ x : Fin 75, A75 x j = ∑ x : Fin 75, A75 j x :=
          Finset.sum_congr rfl fun x _ =>
            congrArg (fun M : Matrix (Fin 75) (Fin 75) ℤ => M x j) hAsymm.symm
        rw [h1, hAdeg j]
        norm_num
      simpa [J75, Matrix.mul_apply] using hcol
    have hmul : S75 * S75 =
        (J75 - 1) * (J75 - 1) - (2 : ℤ) • ((J75 - 1) * A75) -
          (2 : ℤ) • (A75 * (J75 - 1)) + (4 : ℤ) • (A75 * A75) := by
      dsimp [S75]
      rw [Matrix.sub_mul]
      rw [Matrix.mul_sub (J75 - 1), Matrix.mul_sub ((2 : ℤ) • A75)]
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        show (2 : ℤ) * 2 = 4 by norm_num, sub_sub_eq_add_sub, add_sub_right_comm]
    have hJ1_sq : (J75 - 1) * (J75 - 1) = J75 * J75 - J75 - J75 + 1 := by
      noncomm_ring
    have hJ1A : (J75 - 1) * A75 = J75 * A75 - A75 := by
      rw [Matrix.sub_mul, Matrix.one_mul]
    have hAJ1 : A75 * (J75 - 1) = A75 * J75 - A75 := by
      rw [Matrix.mul_sub, Matrix.mul_one]
    rw [hmul, hJ1_sq, hJ1A, hAJ1, hJJ, hAJ, hJA, hAsq]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, S75, J75,
      Matrix.of_apply, smul_eq_mul]
    ring
  let S : Matrix (Fin 74) (Fin 74) ℤ := S75.submatrix Fin.succ Fin.succ
  have hS : IsSeidelMatrix S := by
    refine ⟨?_, fun i => ?_, fun i j hij => ?_⟩
    · ext i j
      have hs := congrArg (fun M : Matrix (Fin 75) (Fin 75) ℤ => M i.succ j.succ) hS75_symm
      simpa [S] using hs
    · simp only [S, S75, J75, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.of_apply, Matrix.one_apply_eq, smul_eq_mul, hAdiag i.succ]
      norm_num
    · have hij' : i.succ ≠ j.succ := fun h => hij (Fin.succ_injective _ h)
      simp only [S, Matrix.submatrix_apply, S75, J75, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.of_apply, Matrix.one_apply_ne hij', smul_eq_mul, sub_zero]
      rcases hA01 i.succ j.succ hij' with h | h <;> simp [h]
  let w : Fin 74 → ℤ := fun i => S75 0 i.succ
  have hw_pm : ∀ i : Fin 74, w i = 1 ∨ w i = -1 := fun i => by
    have hne : (0 : Fin 75) ≠ i.succ := (Fin.succ_ne_zero i).symm
    simp only [w, S75, J75, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply,
      Matrix.one_apply_ne hne, smul_eq_mul, sub_zero]
    rcases hA01 0 i.succ hne with h | h <;> simp [h]
  have hw_sum : ∑ i : Fin 74, w i = 10 := by
    have h0 := hS75_row 0
    rw [Fin.sum_univ_succ] at h0
    have h00 : S75 0 0 = 0 := by
      simp only [S75, J75, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.one_apply_eq,
        smul_eq_mul, hAdiag 0]
      norm_num
    rw [h00, zero_add] at h0
    exact h0
  have hS_sq : S * S =
      (75 : ℤ) • (1 : Matrix (Fin 74) (Fin 74) ℤ) + (10 : ℤ) • S -
        Matrix.of (fun _ _ => (1 : ℤ)) - Matrix.vecMulVec w w := by
    ext a b
    have hsq := congrArg (fun M : Matrix (Fin 75) (Fin 75) ℤ => M a.succ b.succ) hS75_sq
    rw [Matrix.mul_apply, Fin.sum_univ_succ] at hsq
    have hwa : S75 a.succ 0 = w a :=
      congrArg (fun M : Matrix (Fin 75) (Fin 75) ℤ => M a.succ 0) hS75_symm.symm
    simp only [S, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, Matrix.vecMulVec_apply, smul_eq_mul,
      Fin.succ_inj, J75] at hsq ⊢
    rw [hwa] at hsq
    linarith
  have hSw : S *ᵥ w = (10 : ℤ) • w - (fun _ => 1) := by
    ext a
    have hsq := congrArg (fun M : Matrix (Fin 75) (Fin 75) ℤ => M a.succ 0) hS75_sq
    rw [Matrix.mul_apply, Fin.sum_univ_succ] at hsq
    have h00 : S75 0 0 = 0 := by
      simp only [S75, J75, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.one_apply_eq,
        smul_eq_mul, hAdiag 0]
      norm_num
    have hwa : S75 a.succ 0 = w a :=
      congrArg (fun M : Matrix (Fin 75) (Fin 75) ℤ => M a.succ 0) hS75_symm.symm
    have hwx : ∀ x : Fin 74, S75 x.succ 0 = w x := fun x =>
      congrArg (fun M : Matrix (Fin 75) (Fin 75) ℤ => M x.succ 0) hS75_symm.symm
    simp only [h00, mul_zero, zero_add, hwa, hwx, Matrix.sub_apply, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply_ne (Fin.succ_ne_zero a), J75, Matrix.of_apply,
      smul_eq_mul, mul_zero, zero_add] at hsq
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, S,
      Matrix.submatrix_apply]
    linarith
  have hS1 : S *ᵥ (fun _ => (1 : ℤ)) = (10 : ℤ) • (fun _ => 1) - w := by
    ext a
    have hr := hS75_row a.succ
    rw [Fin.sum_univ_succ] at hr
    have hwa : S75 a.succ 0 = w a :=
      congrArg (fun M : Matrix (Fin 75) (Fin 75) ℤ => M a.succ 0) hS75_symm.symm
    rw [hwa] at hr
    simp only [Matrix.mulVec, dotProduct, mul_one, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, S,
      Matrix.submatrix_apply]
    linarith
  let Aset : Finset (Fin 74) := Finset.univ.filter (fun i => w i = -1)
  have hA_card : Aset.card = 32 := by
    have hsum1 : (∑ i : Fin 74, w i) = ((Asetᶜ).card : ℤ) - (Aset.card : ℤ) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => w i = -1)]
      have h1 : (∑ i ∈ Aset, w i) = -(Aset.card : ℤ) := by
        calc
          ∑ i ∈ Aset, w i = ∑ _i ∈ Aset, (-1 : ℤ) :=
            Finset.sum_congr rfl fun i hi => (Finset.mem_filter.mp hi).2
          _ = -(Aset.card : ℤ) := by simp
      have h2 : ∑ i ∈ Finset.univ.filter (fun i => ¬w i = -1), w i = ((Asetᶜ).card : ℤ) := by
        have hfc : Finset.univ.filter (fun i => ¬w i = -1) = Asetᶜ := by
          ext i; simp [Aset]
        rw [hfc]
        calc
          ∑ i ∈ Asetᶜ, w i = ∑ _i ∈ Asetᶜ, (1 : ℤ) := by
            refine Finset.sum_congr rfl fun i hi => ?_
            have hne : w i ≠ -1 := by simpa [Aset] using hi
            exact (hw_pm i).resolve_right hne
          _ = ((Asetᶜ).card : ℤ) := by simp
      change (∑ i ∈ Aset, w i) + _ = _
      rw [h1, h2]
      ring
    have htot : Aset.card + (Asetᶜ).card = 74 := by
      rw [Finset.card_compl, Fintype.card_fin]
      exact Nat.add_sub_cancel' (Finset.card_le_univ Aset)
    omega
  have hAc_card : (Asetᶜ).card = 42 := by
    rw [Finset.card_compl, Fintype.card_fin, hA_card]
  let S_R : Matrix (Fin 74) (Fin 74) ℝ := S.map (Int.castRingHom ℝ)
  have hHerm : S_R.IsHermitian := seidel_hermitian_real hS
  let U : Matrix (Fin 74) (Fin 74) ℝ := hHerm.eigenvectorUnitary
  have hUU : U * Uᵀ = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self hHerm.eigenvectorUnitary
  have hU'U : Uᵀ * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self hHerm.eigenvectorUnitary
  have hspec : S_R = U * Matrix.diagonal hHerm.eigenvalues * Uᵀ := by
    simpa [U, Matrix.star_eq_conjTranspose, RCLike.ofReal_real_eq_id] using hHerm.spectral_theorem
  let vA : Fin 74 → ℝ := fun i => if i ∈ Aset then 1 else 0
  let vB : Fin 74 → ℝ := fun i => if i ∈ Aset then 0 else 1
  have hvA_dot : vA ⬝ᵥ vA = 32 := by
    have hsq : ∀ i : Fin 74, vA i * vA i = if i ∈ Aset then (1 : ℝ) else 0 := fun i => by
      by_cases hi : i ∈ Aset <;> simp [vA, hi]
    simp only [dotProduct, hsq, Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.univ_inter]
    simp [hA_card]
  have hvB_dot : vB ⬝ᵥ vB = 42 := by
    have hsq : ∀ i : Fin 74, vB i * vB i = if i ∉ Aset then (1 : ℝ) else 0 := fun i => by
      by_cases hi : i ∈ Aset <;> simp [vB, hi]
    simp only [dotProduct, hsq, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_eq_mul, mul_one]
    have hfc : (Finset.univ.filter (fun i : Fin 74 => i ∉ Aset)) = Asetᶜ := by
      ext i; simp
    rw [hfc, hAc_card]
    norm_num
  have hvAB_dot : vA ⬝ᵥ vB = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i ∈ Aset <;> simp [vA, vB, hi]
  have hw_R : ∀ i : Fin 74, (w i : ℝ) = vB i - vA i := fun i => by
    by_cases hi : i ∈ Aset
    · have hw1 : w i = -1 := (Finset.mem_filter.mp hi).2
      simp [vA, vB, hi, hw1]
    · have hw1 : w i = 1 := (hw_pm i).resolve_right (fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩))
      simp [vA, vB, hi, hw1]
  have h1_R : ∀ i : Fin 74, (1 : ℝ) = vB i + vA i := fun i => by
    by_cases hi : i ∈ Aset <;> simp [vA, vB, hi]
  have hSvA_R : S_R *ᵥ vA = (11 : ℝ) • vA := by
    ext i
    have h1i := congrFun hS1 i
    have hwi := congrFun hSw i
    have h1r : ((∑ j : Fin 74, S i j : ℤ) : ℝ) = 10 - (w i : ℝ) := by
      have := congrArg (Int.cast : ℤ → ℝ) h1i
      simpa [Matrix.mulVec, dotProduct] using this
    have hwr : ((∑ j : Fin 74, S i j * w j : ℤ) : ℝ) = 10 * (w i : ℝ) - 1 := by
      have := congrArg (Int.cast : ℤ → ℝ) hwi
      simpa [Matrix.mulVec, dotProduct] using this
    have hvAi : (∑ j : Fin 74, (S i j : ℝ) * vA j) =
        ((∑ j : Fin 74, (S i j : ℝ) * (vB j + vA j)) -
          ∑ j : Fin 74, (S i j : ℝ) * (vB j - vA j)) / 2 := by
      rw [← Finset.sum_sub_distrib]
      have hterm : ∀ j : Fin 74,
          (S i j : ℝ) * (vB j + vA j) - (S i j : ℝ) * (vB j - vA j) = 2 * ((S i j : ℝ) * vA j) :=
        fun j => by ring
      simp_rw [hterm, ← Finset.mul_sum]
      ring
    simp_rw [← h1_R, ← hw_R, mul_one] at hvAi
    have hsum1 : (∑ j : Fin 74, (S i j : ℝ)) = 10 - (w i : ℝ) := by exact_mod_cast h1r
    have hsumw : (∑ j : Fin 74, (S i j : ℝ) * (w j : ℝ)) = 10 * (w i : ℝ) - 1 := by
      exact_mod_cast hwr
    simp only [Matrix.mulVec, dotProduct, S_R, Matrix.map_apply, Pi.smul_apply, smul_eq_mul,
      Int.coe_castRingHom]
    rw [hvAi, hsum1, hsumw, hw_R i]
    linarith [h1_R i]
  have hSvB_R : S_R *ᵥ vB = (9 : ℝ) • vB := by
    ext i
    have h1i := congrFun hS1 i
    have hwi := congrFun hSw i
    have h1r : ((∑ j : Fin 74, S i j : ℤ) : ℝ) = 10 - (w i : ℝ) := by
      have := congrArg (Int.cast : ℤ → ℝ) h1i
      simpa [Matrix.mulVec, dotProduct] using this
    have hwr : ((∑ j : Fin 74, S i j * w j : ℤ) : ℝ) = 10 * (w i : ℝ) - 1 := by
      have := congrArg (Int.cast : ℤ → ℝ) hwi
      simpa [Matrix.mulVec, dotProduct] using this
    have hvBi : (∑ j : Fin 74, (S i j : ℝ) * vB j) =
        ((∑ j : Fin 74, (S i j : ℝ) * (vB j + vA j)) +
          ∑ j : Fin 74, (S i j : ℝ) * (vB j - vA j)) / 2 := by
      rw [← Finset.sum_add_distrib]
      have hterm : ∀ j : Fin 74,
          (S i j : ℝ) * (vB j + vA j) + (S i j : ℝ) * (vB j - vA j) = 2 * ((S i j : ℝ) * vB j) :=
        fun j => by ring
      simp_rw [hterm, ← Finset.mul_sum]
      ring
    simp_rw [← h1_R, ← hw_R, mul_one] at hvBi
    have hsum1 : (∑ j : Fin 74, (S i j : ℝ)) = 10 - (w i : ℝ) := by exact_mod_cast h1r
    have hsumw : (∑ j : Fin 74, (S i j : ℝ) * (w j : ℝ)) = 10 * (w i : ℝ) - 1 := by
      exact_mod_cast hwr
    simp only [Matrix.mulVec, dotProduct, S_R, Matrix.map_apply, Pi.smul_apply, smul_eq_mul,
      Int.coe_castRingHom]
    rw [hvBi, hsum1, hsumw, hw_R i]
    linarith [h1_R i]
  let q : Fin 74 → Fin 74 → ℝ := fun k i => U i k
  have hq_norm : ∀ k : Fin 74, q k ⬝ᵥ q k = 1 := fun k => by
    have hc := congrArg (fun M : Matrix (Fin 74) (Fin 74) ℝ => M k k) hU'U
    simpa [q, Matrix.mul_apply, Matrix.one_apply, dotProduct] using hc
  have hSq : ∀ k : Fin 74, S_R *ᵥ q k = (hHerm.eigenvalues k) • q k := fun k => by
    have hq_single : q k = U *ᵥ Pi.single k 1 := by
      ext i; simp [q, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hq_single]
    conv_lhs => rw [hspec]
    calc
      (U * Matrix.diagonal hHerm.eigenvalues * Uᵀ) *ᵥ (U *ᵥ Pi.single k 1)
          = U *ᵥ (Matrix.diagonal hHerm.eigenvalues *ᵥ ((Uᵀ * U) *ᵥ Pi.single k 1)) := by
            simp only [Matrix.mul_assoc, Matrix.mulVec_mulVec]
      _ = U *ᵥ (Matrix.diagonal hHerm.eigenvalues *ᵥ Pi.single k 1) := by
            rw [hU'U, Matrix.one_mulVec]
      _ = U *ᵥ ((hHerm.eigenvalues k) • Pi.single k 1) := by
            congr 1; ext j
            simp [Matrix.mulVec_diagonal, Pi.single_apply]
            split_ifs with hjk <;> simp [hjk]
      _ = (hHerm.eigenvalues k) • (U *ᵥ Pi.single k 1) := Matrix.mulVec_smul _ _ _
  have hS_symm_R : S_Rᵀ = S_R := by
    ext i j
    have hij := congrArg (fun M : Matrix (Fin 74) (Fin 74) ℤ => M i j) hS.1
    simpa [S_R] using congrArg (Int.cast : ℤ → ℝ) hij
  have hvA_orth : ∀ k : Fin 74, vA ⬝ᵥ q k ≠ 0 → hHerm.eigenvalues k = 11 := fun k hne => by
    have hl : (hHerm.eigenvalues k) * (vA ⬝ᵥ q k) = 11 * (vA ⬝ᵥ q k) := by
      calc
        (hHerm.eigenvalues k) * (vA ⬝ᵥ q k)
            = vA ⬝ᵥ ((hHerm.eigenvalues k) • q k) := by rw [dotProduct_smul, smul_eq_mul]
        _ = vA ⬝ᵥ (S_R *ᵥ q k) := by rw [hSq k]
        _ = (S_R *ᵥ vA) ⬝ᵥ q k := by
            rw [dotProduct_mulVec]
            conv_lhs => rw [← hS_symm_R]
            rw [Matrix.vecMul_transpose]
        _ = ((11 : ℝ) • vA) ⬝ᵥ q k := by rw [hSvA_R]
        _ = 11 * (vA ⬝ᵥ q k) := by rw [smul_dotProduct, smul_eq_mul]
    exact mul_right_cancel₀ hne hl
  have hvB_orth : ∀ k : Fin 74, vB ⬝ᵥ q k ≠ 0 → hHerm.eigenvalues k = 9 := fun k hne => by
    have hl : (hHerm.eigenvalues k) * (vB ⬝ᵥ q k) = 9 * (vB ⬝ᵥ q k) := by
      calc
        (hHerm.eigenvalues k) * (vB ⬝ᵥ q k)
            = vB ⬝ᵥ ((hHerm.eigenvalues k) • q k) := by rw [dotProduct_smul, smul_eq_mul]
        _ = vB ⬝ᵥ (S_R *ᵥ q k) := by rw [hSq k]
        _ = (S_R *ᵥ vB) ⬝ᵥ q k := by
            rw [dotProduct_mulVec]
            conv_lhs => rw [← hS_symm_R]
            rw [Matrix.vecMul_transpose]
        _ = ((9 : ℝ) • vB) ⬝ᵥ q k := by rw [hSvB_R]
        _ = 9 * (vB ⬝ᵥ q k) := by rw [smul_dotProduct, smul_eq_mul]
    exact mul_right_cancel₀ hne hl
  have hS_quad : ∀ k : Fin 74,
      (hHerm.eigenvalues k ^ 2 - 10 * hHerm.eigenvalues k - 75) =
        -(2 * ((vA ⬝ᵥ q k) ^ 2 + (vB ⬝ᵥ q k) ^ 2)) := fun k => by
    have hq_quad : q k ⬝ᵥ ((S_R * S_R) *ᵥ q k) = hHerm.eigenvalues k ^ 2 := by
      rw [← Matrix.mulVec_mulVec, hSq k, Matrix.mulVec_smul, hSq k, dotProduct_smul, dotProduct_smul,
        hq_norm k, smul_eq_mul, smul_eq_mul]
      ring
    have hq_lin : q k ⬝ᵥ (S_R *ᵥ q k) = hHerm.eigenvalues k := by
      rw [hSq k, dotProduct_smul, hq_norm k, smul_eq_mul, mul_one]
    have hRhs : ∀ i j : Fin 74,
        (S_R * S_R) i j =
          75 * (if i = j then (1 : ℝ) else 0) + 10 * S_R i j - (1 + (w i : ℝ) * (w j : ℝ)) := by
      intro i j
      have hij := congrArg (fun M : Matrix (Fin 74) (Fin 74) ℤ => (M i j : ℝ)) hS_sq
      have hm : (S_R * S_R) i j = ((S * S) i j : ℝ) := by
        have hmm : (S * S).map (Int.castRingHom ℝ) = S_R * S_R := Matrix.map_mul
        have := congrArg (fun M : Matrix (Fin 74) (Fin 74) ℝ => M i j) hmm.symm
        simpa [S_R] using this
      rw [hm, hij]
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
        Matrix.of_apply, Matrix.vecMulVec_apply, S_R, Matrix.map_apply, smul_eq_mul,
        Int.coe_castRingHom]
      push_cast
      simp only [mul_ite, mul_one, mul_zero]
      ring
    have hquad_eval :
        q k ⬝ᵥ ((S_R * S_R) *ᵥ q k) =
          75 + 10 * hHerm.eigenvalues k - 2 * ((vA ⬝ᵥ q k) ^ 2 + (vB ⬝ᵥ q k) ^ 2) := by
      have h1 : ∀ i : Fin 74,
          ∑ j : Fin 74, (1 + (w i : ℝ) * (w j : ℝ)) * q k j =
            2 * ((vA ⬝ᵥ q k) * vA i + (vB ⬝ᵥ q k) * vB i) := fun i => by
        have hterm : ∀ j : Fin 74,
            (1 + (w i : ℝ) * (w j : ℝ)) * q k j =
              2 * ((vA j * q k j) * vA i + (vB j * q k j) * vB i) := fun j => by
          have h1mul : (1 : ℝ) = (vB i + vA i) * (vB j + vA j) := by
            rw [← h1_R i, ← h1_R j, mul_one]
          rw [hw_R i, hw_R j]
          calc
            (1 + (vB i - vA i) * (vB j - vA j)) * q k j
                = ((vB i + vA i) * (vB j + vA j) + (vB i - vA i) * (vB j - vA j)) * q k j := by
                  rw [← h1mul]
            _ = 2 * ((vA j * q k j) * vA i + (vB j * q k j) * vB i) := by ring
        simp_rw [hterm, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul]
        rfl
      have hdot :
          (∑ i : Fin 74, q k i * ∑ j : Fin 74, (1 + (w i : ℝ) * (w j : ℝ)) * q k j) =
            2 * ((vA ⬝ᵥ q k) ^ 2 + (vB ⬝ᵥ q k) ^ 2) := by
        simp_rw [h1]
        have hterm : ∀ i : Fin 74,
            q k i * (2 * ((vA ⬝ᵥ q k) * vA i + (vB ⬝ᵥ q k) * vB i)) =
              2 * ((vA ⬝ᵥ q k) * (vA i * q k i) + (vB ⬝ᵥ q k) * (vB i * q k i)) := fun i => by ring
        simp_rw [hterm, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
        change 2 * ((vA ⬝ᵥ q k) * (vA ⬝ᵥ q k) + (vB ⬝ᵥ q k) * (vB ⬝ᵥ q k)) = _
        ring
      have hexp :
          q k ⬝ᵥ ((S_R * S_R) *ᵥ q k) =
            75 * (q k ⬝ᵥ q k) + 10 * (q k ⬝ᵥ (S_R *ᵥ q k)) -
              ∑ i : Fin 74, q k i * ∑ j : Fin 74, (1 + (w i : ℝ) * (w j : ℝ)) * q k j := by
        simp only [dotProduct, Matrix.mulVec, hRhs]
        have hrow_s : ∀ i : Fin 74,
            ∑ j : Fin 74,
              (75 * (if i = j then (1 : ℝ) else 0) + 10 * S_R i j -
                (1 + (w i : ℝ) * (w j : ℝ))) * q k j =
              75 * q k i + 10 * ∑ j : Fin 74, S_R i j * q k j -
                ∑ j : Fin 74, (1 + (w i : ℝ) * (w j : ℝ)) * q k j := fun i => by
          have hs : ∀ j : Fin 74,
              (75 * (if i = j then (1 : ℝ) else 0) + 10 * S_R i j -
                (1 + (w i : ℝ) * (w j : ℝ))) * q k j =
                (if i = j then 75 * q k j else 0) + 10 * (S_R i j * q k j) -
                  (1 + (w i : ℝ) * (w j : ℝ)) * q k j := fun j => by
            split_ifs <;> ring
          simp only [hs, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq,
            Finset.mem_univ, ↓reduceIte, ← Finset.mul_sum]
        simp only [hrow_s, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
          mul_left_comm (q k _) 75, mul_left_comm (q k _) 10, ← Finset.mul_sum]
      rw [hexp, hq_norm k, hq_lin, hdot]
      ring
    linarith [hq_quad]
  have hall_eig : ∀ k : Fin 74,
      hHerm.eigenvalues k = -5 ∨ hHerm.eigenvalues k = 15 ∨
        hHerm.eigenvalues k = 11 ∨ hHerm.eigenvalues k = 9 := fun k => by
    by_cases hk11 : hHerm.eigenvalues k = 11
    · exact Or.inr (Or.inr (Or.inl hk11))
    · by_cases hk9 : hHerm.eigenvalues k = 9
      · exact Or.inr (Or.inr (Or.inr hk9))
      · have hA0 : vA ⬝ᵥ q k = 0 := not_not.mp fun h => hk11 (hvA_orth k h)
        have hB0 : vB ⬝ᵥ q k = 0 := not_not.mp fun h => hk9 (hvB_orth k h)
        have hq0 := hS_quad k
        rw [hA0, hB0] at hq0
        have hfac : (hHerm.eigenvalues k + 5) * (hHerm.eigenvalues k - 15) = 0 := by linarith
        rcases mul_eq_zero.mp hfac with h | h
        · exact Or.inl (by linarith)
        · exact Or.inr (Or.inl (by linarith))
  have hparseval : ∀ v : Fin 74 → ℝ, ∑ k : Fin 74, (v ⬝ᵥ q k) ^ 2 = v ⬝ᵥ v := fun v => by
    have h1 : ∀ k : Fin 74, v ⬝ᵥ q k = (Uᵀ *ᵥ v) k := fun k => by
      simp [Matrix.mulVec, dotProduct, q, mul_comm]
    simp_rw [h1]
    calc
      ∑ k : Fin 74, (Uᵀ *ᵥ v) k ^ 2 = (Uᵀ *ᵥ v) ⬝ᵥ (Uᵀ *ᵥ v) := by
        simp [dotProduct, sq]
      _ = ((U * Uᵀ) *ᵥ v) ⬝ᵥ v := by
        rw [dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec]
      _ = v ⬝ᵥ v := by rw [hUU, Matrix.one_mulVec]
  let S11 := Finset.univ.filter (fun k : Fin 74 => hHerm.eigenvalues k = 11)
  let S9 := Finset.univ.filter (fun k : Fin 74 => hHerm.eigenvalues k = 9)
  have hS11_card : S11.card = 1 := by
    have hsum11 : ∑ k : Fin 74, (vA ⬝ᵥ q k) ^ 2 = ∑ k ∈ S11, (32 : ℝ) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : Fin 74 => hHerm.eigenvalues k = 11)]
      have hrest : ∑ k ∈ Finset.univ.filter (fun k : Fin 74 => ¬hHerm.eigenvalues k = 11),
          (vA ⬝ᵥ q k) ^ 2 = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        have hne : hHerm.eigenvalues k ≠ 11 := (Finset.mem_filter.mp hk).2
        have h0 : vA ⬝ᵥ q k = 0 := not_not.mp fun h => hne (hvA_orth k h)
        simp [h0]
      rw [hrest, add_zero]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk11 : hHerm.eigenvalues k = 11 := (Finset.mem_filter.mp hk).2
      have hB0 : vB ⬝ᵥ q k = 0 := not_not.mp fun h => by
        have hk9 := hvB_orth k h
        linarith
      have hq := hS_quad k
      rw [hk11, hB0] at hq
      linarith
    rw [hparseval vA, hvA_dot, Finset.sum_const, nsmul_eq_mul] at hsum11
    have hc : (S11.card : ℝ) = 1 := by linarith
    exact_mod_cast hc
  have hS9_card : S9.card = 1 := by
    have hsum9 : ∑ k : Fin 74, (vB ⬝ᵥ q k) ^ 2 = ∑ k ∈ S9, (42 : ℝ) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : Fin 74 => hHerm.eigenvalues k = 9)]
      have hrest : ∑ k ∈ Finset.univ.filter (fun k : Fin 74 => ¬hHerm.eigenvalues k = 9),
          (vB ⬝ᵥ q k) ^ 2 = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        have hne : hHerm.eigenvalues k ≠ 9 := (Finset.mem_filter.mp hk).2
        have h0 : vB ⬝ᵥ q k = 0 := not_not.mp fun h => hne (hvB_orth k h)
        simp [h0]
      rw [hrest, add_zero]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk9 : hHerm.eigenvalues k = 9 := (Finset.mem_filter.mp hk).2
      have hA0 : vA ⬝ᵥ q k = 0 := not_not.mp fun h => by
        have hk11 := hvA_orth k h
        linarith
      have hq := hS_quad k
      rw [hk9, hA0] at hq
      linarith
    rw [hparseval vB, hvB_dot, Finset.sum_const, nsmul_eq_mul] at hsum9
    have hc : (S9.card : ℝ) = 1 := by linarith
    exact_mod_cast hc
  let Sm5 := Finset.univ.filter (fun k : Fin 74 => hHerm.eigenvalues k = -5)
  let S15 := Finset.univ.filter (fun k : Fin 74 => hHerm.eigenvalues k = 15)
  have hpart : (Finset.univ : Finset (Fin 74)) = Sm5 ∪ (S15 ∪ (S11 ∪ S9)) := by
    ext k; simp only [Sm5, S15, S11, S9, Finset.mem_univ, Finset.mem_union, Finset.mem_filter,
      true_and, true_iff]; exact hall_eig k
  have hd1 : Disjoint Sm5 (S15 ∪ (S11 ∪ S9)) := by
    rw [Finset.disjoint_left]; intro k hk1 hk2
    simp only [Sm5, S15, S11, S9, Finset.mem_filter, Finset.mem_union, Finset.mem_univ,
      true_and] at hk1 hk2
    rcases hk2 with h | h | h <;> linarith
  have hd2 : Disjoint S15 (S11 ∪ S9) := by
    rw [Finset.disjoint_left]; intro k hk1 hk2
    simp only [S15, S11, S9, Finset.mem_filter, Finset.mem_union, Finset.mem_univ,
      true_and] at hk1 hk2
    rcases hk2 with h | h <;> linarith
  have hd3 : Disjoint S11 S9 := by
    rw [Finset.disjoint_left]; intro k hk1 hk2
    simp only [S11, S9, Finset.mem_filter, Finset.mem_univ, true_and] at hk1 hk2
    linarith
  have hsum_card : Sm5.card + S15.card + 1 + 1 = 74 := by
    have hc := congrArg Finset.card hpart
    rw [Finset.card_univ, Fintype.card_fin, Finset.card_union_of_disjoint hd1,
      Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd3,
      hS11_card, hS9_card] at hc
    omega
  have htr_eig : ∑ k : Fin 74, hHerm.eigenvalues k = 0 := by
    have hspec_tr : S_R.trace = ∑ k : Fin 74, hHerm.eigenvalues k := by
      have hAeq : S_R = U * Matrix.diagonal hHerm.eigenvalues * Uᵀ := hspec
      conv_lhs => rw [hAeq]
      rw [Matrix.trace_mul_cycle, hU'U, Matrix.one_mul, Matrix.trace_diagonal]
    rw [← hspec_tr]
    have h0 : S.trace = 0 := hS.trace_eq_zero
    simpa [S_R, Matrix.trace, Matrix.diag_apply, Matrix.map_apply, ← map_sum] using
      congrArg (Int.cast : ℤ → ℝ) h0
  have htr_split : (-5 : ℝ) * (Sm5.card : ℝ) + 15 * (S15.card : ℝ) + 11 + 9 = 0 := by
    have hs := htr_eig
    conv_lhs at hs => rw [hpart]
    rw [Finset.sum_union hd1, Finset.sum_union hd2, Finset.sum_union hd3] at hs
    have s1 : ∑ k ∈ Sm5, hHerm.eigenvalues k = (-5 : ℝ) * (Sm5.card : ℝ) := by
      rw [← mul_comm (Sm5.card : ℝ), ← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_congr rfl fun k hk => (Finset.mem_filter.mp hk).2
    have s2 : ∑ k ∈ S15, hHerm.eigenvalues k = (15 : ℝ) * (S15.card : ℝ) := by
      rw [← mul_comm (S15.card : ℝ), ← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_congr rfl fun k hk => (Finset.mem_filter.mp hk).2
    have s3 : ∑ k ∈ S11, hHerm.eigenvalues k = 11 := by
      calc
        ∑ k ∈ S11, hHerm.eigenvalues k = ∑ _k ∈ S11, (11 : ℝ) :=
          Finset.sum_congr rfl fun k hk => (Finset.mem_filter.mp hk).2
        _ = (S11.card : ℝ) * 11 := by simp
      rw [hS11_card]; norm_num
    have s4 : ∑ k ∈ S9, hHerm.eigenvalues k = 9 := by
      calc
        ∑ k ∈ S9, hHerm.eigenvalues k = ∑ _k ∈ S9, (9 : ℝ) :=
          Finset.sum_congr rfl fun k hk => (Finset.mem_filter.mp hk).2
        _ = (S9.card : ℝ) * 9 := by simp
      rw [hS9_card]; norm_num
    rw [s1, s2, s3, s4] at hs
    linarith
  have hm5_card : Sm5.card = 55 := by
    have h74 : (Sm5.card : ℝ) + (S15.card : ℝ) + 1 + 1 = 74 := by exact_mod_cast hsum_card
    have hc : (Sm5.card : ℝ) = 55 := by linarith
    exact_mod_cast hc
  have h15_card : S15.card = 17 := by omega
  have hSR_eq : S_R.charpoly =
      (X + C (5 : ℝ)) ^ 55 * (X - C (15 : ℝ)) ^ 17 * (X - C (11 : ℝ)) * (X - C (9 : ℝ)) := by
    rw [hermitian_charpoly_eq_prod' hHerm]
    simpa [pow_one] using prod_X_sub_C_eq_of_counts hHerm.eigenvalues 55 17 1 1
      hm5_card h15_card hS11_card hS9_card hall_eig
  refine ⟨S, hS, ?_⟩
  apply Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective
  rw [← Matrix.charpoly_map S (Int.castRingHom ℝ)]
  simpa [S_R, C_ofNat] using hSR_eq

/-- Under the explicit hypothesis `hno : ¬ ExistsSRG 75 32 10 16` (no custom `axiom`),
no `74 × 74` Seidel matrix realizes the `idx=136` characteristic polynomial. -/
theorem idx136_eliminated_of_not_existsSRG
    (hno : ¬ ExistsSRG 75 32 10 16)
    {S : Matrix (Fin 74) (Fin 74) ℤ} (hS : IsSeidelMatrix S) :
    S.charpoly ≠
      (X + C (5 : ℤ)) ^ 55 * (X - C (15 : ℤ)) ^ 17 * (X - C (11 : ℤ)) * (X - C (9 : ℤ)) :=
  fun hchar => hno (idx136_implies_SRG_75_32_10_16 hS hchar)

end WeaponA

end EquiangularLines

end
