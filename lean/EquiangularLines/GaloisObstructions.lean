module

public import EquiangularLines.Obstructions
public import EquiangularLines.Bounds
public import Mathlib.Tactic.FinCases

/-!
# Phase 3 Galois & Submatrix Spectral Obstructions

This module formalizes the three deep algebraic obstruction pillars from Sections 6.1, 7.1, and 7.2
of `reports/algebraist.md`:

1. **Theorem 7.1 (`exists_unique_eulerian_switch`, `eulerian_switch_sq_mod_four`):**
   Every odd-order Seidel matrix `S : Matrix (Fin n) (Fin n) ℤ` admits an Eulerian switching vector
   `d : Fin n → ℤ` (`±1`) such that `(switch d S)` has every row sum congruent to `n - 1` mod `4`,
   unique up to global sign (`±d`), and any Eulerian-gauge odd-order Seidel matrix satisfies
   `(S ^ 2) i j ≡ (if i = j then 1 else 0) + (n - 2) [ZMOD 4]`.

2. **Theorem 7.2 (`simple_eig_projector_adjugate`, `simple_eig_projector_diag`,
   `galois_orthogonality_of_orth_vectors`, `galois_orthogonality_trace_constraint`):**
   At any simple eigenvalue `μ` of a real symmetric matrix `A`, the rank-1 spectral projector
   `w ⊗ wᵀ` satisfies `((μ • 1 - A).adjugate) u v = χ_A'(μ) * w u * w v` and
   `χ_{A_u}(μ) = χ_A'(μ) * (w u)^2`. Across distinct simple eigenvalues `μ : Fin e → ℝ`,
   orthogonality of unit eigenvectors yields the exact Galois trace-product constraints.

3. **Proposition 6.1 (`ker_submatrix_preserves_nullity`, `submatrix_nullity_ge_of_vertex_deletions`,
   `submatrix_nullity_ge_sub`, `submatrix_eigenvalue_count_eq_finrank_ker`,
   `submatrix_trace_cauchy_schwarz_obstruction`):**
   Vertex deletions preserving `μ`-nullity (`mult_μ(S_v) ≥ mult_μ(S)`) force every `μ`-eigenvector
   of `S` to vanish on the deleted set `I`, preserving full `μ`-multiplicity on `S[Iᶜ]`; combined
   with `IsSeidelMatrix.trace_eq_zero`, `IsSeidelMatrix.trace_sq`, and Cauchy–Schwarz on remaining
   eigenvalues of `S[Iᶜ]`, this yields the exact Proposition 6.1 Frobenius inequality.
-/

@[expose] public section

open Matrix Polynomial
open scoped BigOperators

namespace EquiangularLines

section Theorem71

private def negDeg {n : ℕ} (S : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j : Fin n => i ≠ j ∧ S i j = -1)).card

private lemma seidel_entry_eq_one_sub_two {n : ℕ} {S : Matrix (Fin n) (Fin n) ℤ}
    (hS : IsSeidelMatrix S) {i j : Fin n} (hij : i ≠ j) :
    S i j = 1 - 2 * (if S i j = -1 then (1 : ℤ) else 0) := by
  rcases hS.offDiag_eq_one_or_neg_one hij with h | h <;> simp [h]

private lemma row_sum_eq_sub_two_negDeg {n : ℕ} (hn : 1 ≤ n)
    {S : Matrix (Fin n) (Fin n) ℤ} (hS : IsSeidelMatrix S) (i : Fin n) :
    (∑ j : Fin n, S i j) = (n : ℤ) - 1 - 2 * (negDeg S i : ℤ) := by
  have h1 : (∑ j : Fin n, S i j) = ∑ j ∈ Finset.univ.erase i, S i j := by
    rw [← Finset.add_sum_erase Finset.univ (fun j => S i j) (Finset.mem_univ i),
      hS.diag_eq_zero i, zero_add]
  have h2 : (∑ j ∈ Finset.univ.erase i, S i j) =
      ∑ j ∈ Finset.univ.erase i, (1 - 2 * (if S i j = -1 then (1 : ℤ) else 0)) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    exact seidel_entry_eq_one_sub_two hS (Finset.mem_erase.mp hj).1.symm
  have h3 : (∑ j ∈ Finset.univ.erase i, (if S i j = -1 then (1 : ℤ) else 0)) =
      (negDeg S i : ℤ) := by
    have hfilt : Finset.univ.filter (fun j : Fin n => i ≠ j ∧ S i j = -1) =
        (Finset.univ.erase i).filter (fun j : Fin n => S i j = -1) := by
      ext j
      simp [Finset.mem_erase, ne_comm]
    simp only [negDeg, hfilt, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [h1, h2, Finset.sum_sub_distrib, ← Finset.mul_sum, h3, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, Nat.cast_sub hn, Nat.cast_one]

private lemma row_sum_mod4_iff_even_negDeg {n : ℕ} (hn : 1 ≤ n)
    {S : Matrix (Fin n) (Fin n) ℤ} (hS : IsSeidelMatrix S) (i : Fin n) :
    ((∑ j : Fin n, S i j) ≡ (n : ℤ) - 1 [ZMOD 4]) ↔ Even (negDeg S i) := by
  rw [row_sum_eq_sub_two_negDeg hn hS i, Int.modEq_iff_dvd]
  have hdiff : ((n : ℤ) - 1 - ((n : ℤ) - 1 - 2 * (negDeg S i : ℤ))) =
      2 * (negDeg S i : ℤ) := by ring
  rw [hdiff]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t.natAbs, ?_⟩
    omega
  · rintro ⟨t, ht⟩
    refine ⟨(t : ℤ), ?_⟩
    omega

private lemma even_sum_negDeg {n : ℕ} {S : Matrix (Fin n) (Fin n) ℤ} (hS : IsSeidelMatrix S) :
    Even (∑ i : Fin n, negDeg S i) := by
  let f : Fin n → Fin n → ℕ := fun i j => if i ≠ j ∧ S i j = -1 then 1 else 0
  have hdeg : ∀ i, negDeg S i = ∑ j : Fin n, f i j := fun i => by
    simp [negDeg, f]
  have hfsym : ∀ i j, f i j = f j i := fun i j => by
    simp only [f, ne_comm, hS.symm i j]
  have hfdiag : ∀ i, f i i = 0 := fun i => by simp [f]
  have hsum : (∑ i : Fin n, negDeg S i) =
      2 * ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), f i j := by
    have hsplit : ∀ i j : Fin n,
        f i j = (if i < j then f i j else 0) + (if j < i then f i j else 0) := fun i j => by
      rcases lt_trichotomy i j with hlt | rfl | hgt
      · simp [hlt, lt_asymm hlt]
      · simp [hfdiag i]
      · simp [hgt, lt_asymm hgt]
    calc
      (∑ i : Fin n, negDeg S i)
          = ∑ i : Fin n, ∑ j : Fin n, f i j := Finset.sum_congr rfl fun i _ => hdeg i
      _ = ∑ i : Fin n, ∑ j : Fin n,
            ((if i < j then f i j else 0) + (if j < i then f i j else 0)) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsplit i j
      _ = (∑ i : Fin n, ∑ j : Fin n, if i < j then f i j else 0) +
            (∑ i : Fin n, ∑ j : Fin n, if j < i then f i j else 0) := by
            simp_rw [Finset.sum_add_distrib]
      _ = (∑ i : Fin n, ∑ j : Fin n, if i < j then f i j else 0) +
            (∑ i : Fin n, ∑ j : Fin n, if i < j then f i j else 0) := by
            congr 1
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
            rw [hfsym]
      _ = 2 * ∑ i : Fin n, ∑ j : Fin n, if i < j then f i j else 0 := (two_mul _).symm
      _ = 2 * ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), f i j := by
            congr 1
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_filter]
  rw [hsum]
  exact even_two_mul _

private lemma negDeg_switch_zmod2 {n : ℕ} {S : Matrix (Fin n) (Fin n) ℤ}
    (hS : IsSeidelMatrix S) {d : Fin n → ℤ} (hd : ∀ i, d i = 1 ∨ d i = -1) (i : Fin n) :
    (negDeg (IsSeidelMatrix.switch d S) i : ZMod 2) =
      (negDeg S i : ZMod 2) +
        ((n - 1 : ℕ) : ZMod 2) * (if d i = 1 then 0 else 1) +
        ∑ j ∈ Finset.univ.erase i, (if d j = 1 then 0 else 1) := by
  let f : Fin n → ZMod 2 := fun u => if d u = 1 then 0 else 1
  have hterm : ∀ j : Fin n,
      (if i ≠ j ∧ IsSeidelMatrix.switch d S i j = -1 then (1 : ZMod 2) else 0) =
        (if i ≠ j ∧ S i j = -1 then (1 : ZMod 2) else 0) +
          (if i = j then 0 else f i + f j) := fun j => by
    by_cases hij : i = j
    · subst hij; simp
    · simp only [hij, ne_eq, not_false_eq_true, true_and, ite_false,
        IsSeidelMatrix.switch_apply, f]
      rcases hd i with hi | hi <;> rcases hd j with hj | hj <;>
        rcases hS.offDiag_eq_one_or_neg_one hij with h | h <;>
        simp [hi, hj, h] <;> decide
  have hL : (negDeg (IsSeidelMatrix.switch d S) i : ZMod 2) =
      ∑ j : Fin n, if i ≠ j ∧ IsSeidelMatrix.switch d S i j = -1 then (1 : ZMod 2) else 0 := by
    simp [negDeg]
  have hR : (negDeg S i : ZMod 2) =
      ∑ j : Fin n, if i ≠ j ∧ S i j = -1 then (1 : ZMod 2) else 0 := by
    simp [negDeg]
  have hsum_f : (∑ j : Fin n, if i = j then (0 : ZMod 2) else f i + f j) =
      ((n - 1 : ℕ) : ZMod 2) * f i + ∑ j ∈ Finset.univ.erase i, f j := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [ite_true, zero_add]
    have hcon : (∑ j ∈ Finset.univ.erase i, if i = j then (0 : ZMod 2) else f i + f j) =
        ∑ j ∈ Finset.univ.erase i, (f i + f j) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
      simp [hij]
    rw [hcon, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  calc
    (negDeg (IsSeidelMatrix.switch d S) i : ZMod 2)
        = ∑ j : Fin n, if i ≠ j ∧ IsSeidelMatrix.switch d S i j = -1 then (1 : ZMod 2) else 0 := hL
    _ = ∑ j : Fin n, ((if i ≠ j ∧ S i j = -1 then (1 : ZMod 2) else 0) +
          (if i = j then 0 else f i + f j)) := Finset.sum_congr rfl fun j _ => hterm j
    _ = (∑ j : Fin n, if i ≠ j ∧ S i j = -1 then (1 : ZMod 2) else 0) +
          ∑ j : Fin n, (if i = j then 0 else f i + f j) := Finset.sum_add_distrib
    _ = (negDeg S i : ZMod 2) + ((n - 1 : ℕ) : ZMod 2) * f i +
          ∑ j ∈ Finset.univ.erase i, f j := by
          rw [← hR, hsum_f, add_assoc]

/-- **Theorem 7.1 (Existence & uniqueness of the odd-`n` Eulerian switching gauge):**
Every symmetric Seidel matrix `S : Matrix (Fin n) (Fin n) ℤ` of odd order `n` has a switching vector
`d : Fin n → ℤ` (`d i = ±1`) such that every row sum of `switch d S` satisfies
`∑ j, switch d S i j ≡ n - 1 [ZMOD 4]`, and `d` is unique up to global sign `±d`. -/
theorem exists_unique_eulerian_switch {n : ℕ} (hn : Odd n)
    {S : Matrix (Fin n) (Fin n) ℤ} (hS : IsSeidelMatrix S) :
    ∃ d : Fin n → ℤ,
      (∀ i, d i = 1 ∨ d i = -1) ∧
      (∀ i, (∑ j, IsSeidelMatrix.switch d S i j) ≡ (n : ℤ) - 1 [ZMOD 4]) ∧
      (∀ d' : Fin n → ℤ, (∀ i, d' i = 1 ∨ d' i = -1) →
        (∀ i, (∑ j, IsSeidelMatrix.switch d' S i j) ≡ (n : ℤ) - 1 [ZMOD 4]) →
        (∀ i, d' i = d i) ∨ (∀ i, d' i = -d i)) := by
  have hn1 : 1 ≤ n := hn.pos
  let d : Fin n → ℤ := fun i => if Even (negDeg S i) then 1 else -1
  have hd : ∀ i, d i = 1 ∨ d i = -1 := fun i => by
    dsimp [d]; split_ifs <;> simp
  have hS_eul : IsSeidelMatrix (IsSeidelMatrix.switch d S) :=
    IsSeidelMatrix.switch_isSeidelMatrix hS hd
  have hrow_d : ∀ i, (∑ j, IsSeidelMatrix.switch d S i j) ≡ (n : ℤ) - 1 [ZMOD 4] := by
    intro i
    rw [row_sum_mod4_iff_even_negDeg hn1 hS_eul i, ← ZMod.natCast_eq_zero_iff_even]
    rw [negDeg_switch_zmod2 hS hd i]
    have hn_even : ((n - 1 : ℕ) : ZMod 2) = 0 := by
      rw [ZMod.natCast_eq_zero_iff_even]
      exact hn.tsub_odd (by decide : Odd 1)
    have hk_eq : ∀ u : Fin n, (if d u = 1 then (0 : ZMod 2) else 1) = (negDeg S u : ZMod 2) := by
      intro u
      dsimp [d]
      by_cases hu : Even (negDeg S u)
      · have hz : (negDeg S u : ZMod 2) = 0 := (ZMod.natCast_eq_zero_iff_even).mpr hu
        simp [hu, hz]
      · have ho : Odd (negDeg S u) := Nat.not_even_iff_odd.mp hu
        have hz : (negDeg S u : ZMod 2) = 1 := by
          rcases ho with ⟨t, ht⟩
          rw [ht, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
          have h2 : (2 : ZMod 2) = 0 := by decide
          rw [h2, zero_mul, zero_add]
        simp [hu, hz]
    have hsum_zero : (∑ u : Fin n, (negDeg S u : ZMod 2)) = 0 := by
      rw [← Nat.cast_sum, ZMod.natCast_eq_zero_iff_even]
      exact even_sum_negDeg hS
    have herase : (∑ j ∈ Finset.univ.erase i, (negDeg S j : ZMod 2)) = (negDeg S i : ZMod 2) := by
      have hadd := Finset.add_sum_erase Finset.univ (fun u => (negDeg S u : ZMod 2)) (Finset.mem_univ i)
      rw [hsum_zero] at hadd
      have hchar2 : ∀ x y : ZMod 2, x + y = 0 → y = x := by decide
      exact hchar2 _ _ hadd
    simp_rw [hk_eq]
    rw [hn_even, zero_mul, add_zero, herase]
    have hchar2_add : ∀ x : ZMod 2, x + x = 0 := by decide
    exact hchar2_add _
  refine ⟨d, hd, hrow_d, fun d' hd' hrow_d' => ?_⟩
  let S1 := IsSeidelMatrix.switch d S
  let ε : Fin n → ℤ := fun i => d i * d' i
  have hε : ∀ i, ε i = 1 ∨ ε i = -1 := fun i => by
    rcases hd i with h1 | h1 <;> rcases hd' i with h2 | h2 <;> simp [ε, h1, h2]
  have hswitch_eq : IsSeidelMatrix.switch d' S = IsSeidelMatrix.switch ε S1 := by
    ext i j
    simp only [S1, IsSeidelMatrix.switch_apply, ε]
    have hd2 : ∀ u, d u * d u = 1 := fun u => by
      rcases hd u with h | h <;> simp [h]
    calc
      d' i * S i j * d' j = (d i * d i) * d' i * S i j * ((d j * d j) * d' j) := by
        rw [hd2 i, hd2 j]; ring
      _ = (d i * d' i) * (d i * S i j * d j) * (d j * d' j) := by ring
  have hS2 : IsSeidelMatrix (IsSeidelMatrix.switch ε S1) :=
    IsSeidelMatrix.switch_isSeidelMatrix hS_eul hε
  have hev1 : ∀ i, (negDeg S1 i : ZMod 2) = 0 := fun i =>
    (ZMod.natCast_eq_zero_iff_even).mpr ((row_sum_mod4_iff_even_negDeg hn1 hS_eul i).mp (hrow_d i))
  have hev2 : ∀ i, (negDeg (IsSeidelMatrix.switch ε S1) i : ZMod 2) = 0 := fun i =>
    (ZMod.natCast_eq_zero_iff_even).mpr
      ((row_sum_mod4_iff_even_negDeg hn1 hS2 i).mp (by rw [← hswitch_eq]; exact hrow_d' i))
  let k : Fin n → ZMod 2 := fun i => if ε i = 1 then 0 else 1
  have hk_const : ∀ i : Fin n, k i = ∑ j : Fin n, k j := fun i => by
    have hmod := negDeg_switch_zmod2 hS_eul hε i
    have hn_even : ((n - 1 : ℕ) : ZMod 2) = 0 := by
      rw [ZMod.natCast_eq_zero_iff_even]
      exact hn.tsub_odd (by decide : Odd 1)
    rw [hev2 i, hev1 i, hn_even, zero_mul, zero_add, zero_add] at hmod
    change 0 = ∑ j ∈ Finset.univ.erase i, k j at hmod
    have hadd := Finset.add_sum_erase Finset.univ k (Finset.mem_univ i)
    rw [← hmod, add_zero] at hadd
    exact hadd
  have htot : (∑ j : Fin n, k j) = 0 ∨ (∑ j : Fin n, k j) = 1 := by
    have : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    exact this _
  rcases htot with h0 | h1
  · left
    intro i
    have hki : k i = 0 := (hk_const i).trans h0
    have hε1 : ε i = 1 := by
      dsimp [k] at hki
      split_ifs at hki with he
      · exact he
      · exact absurd hki (by decide)
    rcases hd i with hi | hi <;> rcases hd' i with hj | hj <;> simp [ε, hi, hj] at hε1 ⊢
  · right
    intro i
    have hki : k i = 1 := (hk_const i).trans h1
    have hεm1 : ε i = -1 := by
      dsimp [k] at hki
      split_ifs at hki with he
      · exact absurd hki (by decide)
      · rcases hε i with h' | h'
        · exact absurd h' he
        · exact h'
    rcases hd i with hi | hi <;> rcases hd' i with hj | hj <;> simp [ε, hi, hj] at hεm1 ⊢

/-- **Theorem 7.1 (`S_ε ^ 2 mod 4` law):**
For any odd-order Seidel matrix `S` in Eulerian gauge (`∀ i, ∑ j, S i j ≡ n - 1 [ZMOD 4]`),
`(S ^ 2) i j ≡ (if i = j then 1 else 0) + (n - 2) [ZMOD 4]`. -/
theorem eulerian_switch_sq_mod_four {n : ℕ} (hn : Odd n)
    {S : Matrix (Fin n) (Fin n) ℤ} (hS : IsSeidelMatrix S)
    (hEul : ∀ i, (∑ j, S i j) ≡ (n : ℤ) - 1 [ZMOD 4]) (i j : Fin n) :
    (S ^ 2) i j ≡ (if i = j then 1 else 0) + ((n : ℤ) - 2) [ZMOD 4] := by
  have hn1 : 1 ≤ n := hn.pos
  by_cases hij : i = j
  · subst hij
    have hdiag : (S ^ 2) i i = (n : ℤ) - 1 := by
      rw [sq]
      simpa using hS.sq_diag i
    simp only [ite_true]
    rw [hdiag]
    have hrhs : (1 : ℤ) + ((n : ℤ) - 2) = (n : ℤ) - 1 := by ring
    rw [hrhs]
  · simp only [hij, ite_false, zero_add]
    have hev_i : Even (negDeg S i) := (row_sum_mod4_iff_even_negDeg hn1 hS i).mp (hEul i)
    have hev_j : Even (negDeg S j) := (row_sum_mod4_iff_even_negDeg hn1 hS j).mp (hEul j)
    let a : Fin n → Fin n → ℤ := fun u v => if u ≠ v ∧ S u v = -1 then 1 else 0
    have ha_symm : ∀ u v, a u v = a v u := fun u v => by
      simp only [a, ne_comm, hS.symm u v]
    have ha_deg : ∀ u, (∑ v : Fin n, a u v) = (negDeg S u : ℤ) := fun u => by
      simp [a, negDeg]
    have hprod_k : ∀ k : Fin n, k ≠ i → k ≠ j →
        S i k * S k j ≡ 1 - 2 * a i k - 2 * a j k [ZMOD 4] := fun k hki hkj => by
      rw [← hS.symm k j, seidel_entry_eq_one_sub_two hS hki.symm,
        seidel_entry_eq_one_sub_two hS hkj.symm]
      have haik : (if S i k = -1 then (1 : ℤ) else 0) = a i k := by simp [a, hki.symm]
      have hajk : (if S j k = -1 then (1 : ℤ) else 0) = a j k := by simp [a, hkj.symm]
      rw [haik, hajk, Int.modEq_iff_dvd]
      refine ⟨-(a i k * a j k), ?_⟩
      ring
    let s : Finset (Fin n) := (Finset.univ.erase i).erase j
    have hs_card : (s.card : ℤ) = (n : ℤ) - 2 := by
      have hj_in : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
      have hcard_nat : s.card = n - 2 := by
        rw [Finset.card_erase_of_mem hj_in, Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ, Fintype.card_fin]
        omega
      have hn2 : 2 ≤ n := by
        have hsub : ({i, j} : Finset (Fin n)).card ≤ (Finset.univ : Finset (Fin n)).card :=
          Finset.card_le_univ _
        simpa [Finset.card_pair hij, Finset.card_fin] using hsub
      omega
    have hS2_sum : (S ^ 2) i j = ∑ k ∈ s, S i k * S k j := by
      rw [sq, Matrix.mul_apply]
      have h1 : (∑ k : Fin n, S i k * S k j) = ∑ k ∈ Finset.univ.erase i, S i k * S k j := by
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i), hS.diag_eq_zero i, zero_mul,
          zero_add]
      have hj_in : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
      rw [h1, ← Finset.add_sum_erase (Finset.univ.erase i) _ hj_in, hS.diag_eq_zero j, mul_zero,
        zero_add]
    have hsum_ai : (∑ k ∈ s, a i k) = (negDeg S i : ℤ) - a i j := by
      have h1 : (∑ k : Fin n, a i k) = ∑ k ∈ Finset.univ.erase i, a i k := by
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
        simp [a]
      have hj_in : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
      rw [← ha_deg i, h1, ← Finset.add_sum_erase (Finset.univ.erase i) _ hj_in]
      ring
    have hsum_aj : (∑ k ∈ s, a j k) = (negDeg S j : ℤ) - a i j := by
      have h1 : (∑ k : Fin n, a j k) = ∑ k ∈ Finset.univ.erase j, a j k := by
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
        simp [a]
      have hi_in : i ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩
      have hs_eq : s = (Finset.univ.erase j).erase i := Finset.erase_right_comm
      rw [← ha_deg j, h1, hs_eq, ← Finset.add_sum_erase (Finset.univ.erase j) _ hi_in, ha_symm j i]
      ring
    rw [hS2_sum, Int.modEq_iff_dvd]
    have hdvd_terms : (4 : ℤ) ∣ ∑ k ∈ s, ((1 - 2 * a i k - 2 * a j k) - S i k * S k j) := by
      refine Finset.dvd_sum fun k hk => ?_
      have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
      have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
      exact Int.modEq_iff_dvd.mp (hprod_k k hki hkj)
    have hdiff_sum : (∑ k ∈ s, (1 - 2 * a i k - 2 * a j k)) =
        ((n : ℤ) - 2) - 2 * ((negDeg S i : ℤ) + (negDeg S j : ℤ) - 2 * a i j) := by
      simp_rw [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib,
        ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one, hs_card,
        hsum_ai, hsum_aj]
      ring
    have hev_iZ : (2 : ℤ) ∣ (negDeg S i : ℤ) := by
      rcases hev_i with ⟨t, ht⟩; exact ⟨t, by omega⟩
    have hev_jZ : (2 : ℤ) ∣ (negDeg S j : ℤ) := by
      rcases hev_j with ⟨t, ht⟩; exact ⟨t, by omega⟩
    have hdvd_tail : (4 : ℤ) ∣ 2 * ((negDeg S i : ℤ) + (negDeg S j : ℤ) - 2 * a i j) := by
      rcases hev_iZ with ⟨ti, hti⟩
      rcases hev_jZ with ⟨tj, htj⟩
      refine ⟨ti + tj - a i j, ?_⟩
      rw [hti, htj]
      ring
    have hcomb := dvd_add hdvd_terms hdvd_tail
    rw [Finset.sum_sub_distrib, hdiff_sum] at hcomb
    convert hcomb using 1
    ring

end Theorem71

section Theorem72

private lemma derivative_prod_sub_C {n : ℕ} (s : Finset (Fin n)) (f : Fin n → ℝ) :
    (∏ k ∈ s, (X - C (f k))).derivative =
      ∑ k ∈ s, ∏ j ∈ s.erase k, (X - C (f j)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    rw [Finset.prod_insert has, Polynomial.derivative_mul, Polynomial.derivative_X_sub_C,
      one_mul, ih, Finset.sum_insert has, Finset.erase_insert has, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    have hka : k ≠ a := fun h => has (h ▸ hk)
    rw [Finset.erase_insert_of_ne hka.symm,
      Finset.prod_insert (fun h => has (Finset.mem_of_mem_erase h))]

private lemma adjugate_unitary_conj {n : ℕ} {U D : Matrix (Fin n) (Fin n) ℝ}
    (hUU : U * Uᵀ = 1) (hU'U : Uᵀ * U = 1) :
    (U * D * Uᵀ).adjugate = U * D.adjugate * Uᵀ := by
  have hdet_sq : U.det ^ 2 = 1 := by
    have h1 : (U * Uᵀ).det = (1 : Matrix (Fin n) (Fin n) ℝ).det := congrArg Matrix.det hUU
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, ← sq] at h1
    exact h1
  have hU_adj : U.adjugate = U.det • Uᵀ := by
    have h1 := Matrix.mul_adjugate U
    have h2 := congrArg (fun M => Uᵀ * M) h1
    rw [← Matrix.mul_assoc, hU'U, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one] at h2
    exact h2
  have hUt_adj : Uᵀ.adjugate = U.det • U := by
    rw [← Matrix.adjugate_transpose, hU_adj, Matrix.transpose_smul, Matrix.transpose_transpose]
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, hUt_adj, hU_adj,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, smul_smul, ← sq, hdet_sq, one_smul,
    Matrix.mul_assoc]

private lemma simple_eig_index_unique {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) {μ : ℝ}
    (hroot : A.charpoly.eval μ = 0) (hsimple : A.charpoly.derivative.eval μ ≠ 0) :
    ∃ k0 : Fin n, hA.eigenvalues k0 = μ ∧
      (∀ k : Fin n, hA.eigenvalues k = μ → k = k0) ∧
      A.charpoly.derivative.eval μ = ∏ j ∈ Finset.univ.erase k0, (μ - hA.eigenvalues j) := by
  have hchar : A.charpoly = ∏ k : Fin n, (X - C (hA.eigenvalues k)) := by
    simpa [RCLike.ofReal_real_eq_id] using hA.charpoly_eq
  have hprod0 : (∏ k : Fin n, (μ - hA.eigenvalues k)) = 0 := by
    have h := congrArg (Polynomial.eval μ) hchar
    rw [hroot, Polynomial.eval_prod] at h
    simpa [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] using h.symm
  obtain ⟨k0, _, hk0⟩ := Finset.prod_eq_zero_iff.mp hprod0
  have heig0 : hA.eigenvalues k0 = μ := sub_eq_zero.mp hk0 |>.symm
  have hderiv : A.charpoly.derivative.eval μ =
      ∑ k : Fin n, ∏ j ∈ Finset.univ.erase k, (μ - hA.eigenvalues j) := by
    rw [hchar, derivative_prod_sub_C Finset.univ hA.eigenvalues]
    change (Polynomial.evalRingHom μ)
        (∑ k : Fin n, ∏ j ∈ Finset.univ.erase k, (X - C (hA.eigenvalues j))) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    change (∏ j ∈ Finset.univ.erase k, (X - C (hA.eigenvalues j))).eval μ = _
    rw [Polynomial.eval_prod]
    simp
  have huniq : ∀ k : Fin n, hA.eigenvalues k = μ → k = k0 := by
    intro k hk
    by_contra hne
    have hzero_all : A.charpoly.derivative.eval μ = 0 := by
      rw [hderiv]
      refine Finset.sum_eq_zero fun t _ => ?_
      by_cases htk0 : t = k0
      · subst htk0
        exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ k⟩)
          (by simp [hk])
      · exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm htk0, Finset.mem_univ k0⟩)
          (by simp [heig0])
    exact hsimple hzero_all
  refine ⟨k0, heig0, huniq, ?_⟩
  rw [hderiv, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k0)]
  have hrest : (∑ k ∈ Finset.univ.erase k0,
      ∏ j ∈ Finset.univ.erase k, (μ - hA.eigenvalues j)) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have hne : k ≠ k0 := (Finset.mem_erase.mp hk).1
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ k0⟩)
      (by simp [heig0])
  rw [hrest, add_zero]

/-- **Theorem 7.2 (Simple-eigenvalue rank-1 adjugate formula):**
If `A : Matrix (Fin n) (Fin n) ℝ` is symmetric (`A.IsHermitian`) and `μ : ℝ` is a simple
eigenvalue (`A.charpoly.eval μ = 0` and `A.charpoly.derivative.eval μ ≠ 0`), then there exists a
unit eigenvector `w : Fin n → ℝ` (`A *ᵥ w = μ • w`, `w ⬝ᵥ w = 1`) such that
`((μ • 1 - A).adjugate) u v = A.charpoly.derivative.eval μ * (w u * w v)` for all `u, v : Fin n`. -/
theorem simple_eig_projector_adjugate {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) {μ : ℝ}
    (hroot : A.charpoly.eval μ = 0) (hsimple : A.charpoly.derivative.eval μ ≠ 0) :
    ∃ w : Fin n → ℝ,
      A *ᵥ w = μ • w ∧ w ⬝ᵥ w = 1 ∧
      ∀ u v : Fin n, ((μ • (1 : Matrix (Fin n) (Fin n) ℝ) - A).adjugate) u v =
        A.charpoly.derivative.eval μ * (w u * w v) := by
  obtain ⟨k0, heig0, huniq, hderiv_eq⟩ := simple_eig_index_unique hA hroot hsimple
  let U : Matrix (Fin n) (Fin n) ℝ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  have hUU : U * Uᵀ = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hU'U : Uᵀ * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hspec : A = U * Matrix.diagonal hA.eigenvalues * Uᵀ := by
    simpa [U, Matrix.star_eq_conjTranspose, RCLike.ofReal_real_eq_id] using hA.spectral_theorem
  let w : Fin n → ℝ := fun u => U u k0
  have hw_eq : w = U *ᵥ Pi.single k0 1 := by
    ext u
    simp [w, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hAw : A *ᵥ w = μ • w := by
    rw [hw_eq]
    conv_lhs => rw [hspec]
    calc
      (U * Matrix.diagonal hA.eigenvalues * Uᵀ) *ᵥ (U *ᵥ Pi.single k0 1)
          = U *ᵥ (Matrix.diagonal hA.eigenvalues *ᵥ ((Uᵀ * U) *ᵥ Pi.single k0 1)) := by
            simp only [Matrix.mul_assoc, Matrix.mulVec_mulVec]
      _ = U *ᵥ (Matrix.diagonal hA.eigenvalues *ᵥ Pi.single k0 1) := by
            rw [hU'U, Matrix.one_mulVec]
      _ = U *ᵥ (μ • Pi.single k0 1) := by
            congr 1; ext j
            simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
            split_ifs with hjk
            · subst hjk; simp [heig0]
            · simp
      _ = μ • (U *ᵥ Pi.single k0 1) := Matrix.mulVec_smul _ _ _
  have hww : w ⬝ᵥ w = 1 := by
    calc
      w ⬝ᵥ w = ∑ u : Fin n, U u k0 * U u k0 := rfl
      _ = (Uᵀ * U) k0 k0 := by
          simp only [Matrix.mul_apply, Matrix.transpose_apply]
      _ = 1 := by rw [hU'U, Matrix.one_apply_eq]
  have hdiff : μ • (1 : Matrix (Fin n) (Fin n) ℝ) - A =
      U * Matrix.diagonal (fun k => μ - hA.eigenvalues k) * Uᵀ := by
    calc
      μ • (1 : Matrix (Fin n) (Fin n) ℝ) - A
          = U * (μ • (1 : Matrix (Fin n) (Fin n) ℝ)) * Uᵀ -
              U * Matrix.diagonal hA.eigenvalues * Uᵀ := by
            rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUU, ← hspec]
      _ = U * (μ • (1 : Matrix (Fin n) (Fin n) ℝ) - Matrix.diagonal hA.eigenvalues) * Uᵀ := by
            simp only [Matrix.mul_sub, Matrix.sub_mul]
      _ = U * Matrix.diagonal (fun k => μ - hA.eigenvalues k) * Uᵀ := by
            congr 2
            ext a b
            by_cases hab : a = b <;> simp [hab]
  have hadj_D : (Matrix.diagonal (fun k => μ - hA.eigenvalues k)).adjugate =
      (A.charpoly.derivative.eval μ) • Matrix.diagonal (Pi.single k0 (1 : ℝ)) := by
    rw [Matrix.adjugate_diagonal]
    ext a b
    by_cases hab : a = b
    · subst hab
      by_cases ha0 : a = k0
      · subst ha0
        simp [hderiv_eq]
      · have hzero : (∏ j ∈ Finset.univ.erase a, (μ - hA.eigenvalues j)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm ha0, Finset.mem_univ k0⟩)
            (by simp [heig0])
        simp [ha0, hzero]
    · simp [hab]
  refine ⟨w, hAw, hww, fun u v => ?_⟩
  rw [hdiff, adjugate_unitary_conj hUU hU'U, hadj_D, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.smul_apply, smul_eq_mul]
  congr 1
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp_rw [Matrix.diagonal_mul, Matrix.transpose_apply, Pi.single_apply]
  have hterm_single : ∀ x : Fin n,
      U u x * ((if x = k0 then (1 : ℝ) else 0) * U v x) =
        if x = k0 then U u k0 * U v k0 else 0 := fun x => by
    by_cases hx : x = k0 <;> simp [hx]
  simp_rw [hterm_single, Finset.sum_ite_eq']
  simp [w]

/-- **Theorem 7.2 (Diagonal projector formula via `charmatrix_adjugate_diag`):**
At a simple eigenvalue `μ` of a symmetric matrix `A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ` with
unit eigenvector `w`, every vertex-deletion characteristic polynomial satisfies
`(A.submatrix u.succAbove u.succAbove).charpoly.eval μ = A.charpoly.derivative.eval μ * (w u) ^ 2`. -/
theorem simple_eig_projector_diag {m : ℕ} {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hA : A.IsHermitian) {μ : ℝ}
    (hroot : A.charpoly.eval μ = 0) (hsimple : A.charpoly.derivative.eval μ ≠ 0) :
    ∃ w : Fin (m + 1) → ℝ,
      A *ᵥ w = μ • w ∧ w ⬝ᵥ w = 1 ∧
      ∀ u : Fin (m + 1),
        (A.submatrix u.succAbove u.succAbove).charpoly.eval μ =
          A.charpoly.derivative.eval μ * (w u) ^ 2 := by
  obtain ⟨w, hAw, hww, hadj⟩ := simple_eig_projector_adjugate hA hroot hsimple
  refine ⟨w, hAw, hww, fun u => ?_⟩
  have hdiag_poly := charmatrix_adjugate_diag A u u.succAboveEmb (Fin.succAbove_ne u)
  have hmap_eval := congrArg (Polynomial.eval μ) hdiag_poly
  have hmap_mat :
      ((Polynomial.evalRingHom μ).mapMatrix (Matrix.charmatrix A).adjugate) u u =
        ((Matrix.adjugate (Matrix.charmatrix A)) u u).eval μ := rfl
  have hcharm_eval :
      (Polynomial.evalRingHom μ).mapMatrix (Matrix.charmatrix A) =
        μ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) - A := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.charmatrix, hij]
  have hLHS : (Matrix.adjugate (μ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) - A)) u u =
      (A.submatrix u.succAbove u.succAbove).charpoly.eval μ := by
    rw [← hcharm_eval, ← RingHom.map_adjugate, hmap_mat, hmap_eval]
    rfl
  have hRHS := hadj u u
  rw [hLHS, ← sq] at hRHS
  exact hRHS

/-- **Pure orthogonality engine for Theorem 7.2:**
For any pairwise orthogonal family of vectors `r : Fin e → Fin n → ℝ` (`∀ i ≠ j, ∑ u, r i u * r j u = 0`)
and any `p q : ℝ[X]`, `∑ u, ((∑ i, p.eval (μ i) * r i u) * (∑ j, q.eval (μ j) * r j u) -
∑ i, (p * q).eval (μ i) * (r i u)^2) = 0`. -/
theorem galois_orthogonality_of_orth_vectors {n e : ℕ}
    (μ : Fin e → ℝ) (r : Fin e → Fin n → ℝ)
    (horth : ∀ i j : Fin e, i ≠ j → ∑ u : Fin n, r i u * r j u = 0)
    (p q : ℝ[X]) :
    ∑ u : Fin n,
      ((∑ i : Fin e, p.eval (μ i) * r i u) * (∑ j : Fin e, q.eval (μ j) * r j u) -
        ∑ i : Fin e, (p * q).eval (μ i) * (r i u) ^ 2) = 0 := by
  have hexp : ∀ u : Fin n,
      (∑ i : Fin e, p.eval (μ i) * r i u) * (∑ j : Fin e, q.eval (μ j) * r j u) -
        ∑ i : Fin e, (p * q).eval (μ i) * (r i u) ^ 2 =
      ∑ i : Fin e, ∑ j ∈ Finset.univ.erase i,
        p.eval (μ i) * q.eval (μ j) * (r i u * r j u) := fun u => by
    rw [Finset.sum_mul]
    have hsplit : (∑ i : Fin e, p.eval (μ i) * r i u * ∑ j : Fin e, q.eval (μ j) * r j u) =
        ∑ i : Fin e, ((p * q).eval (μ i) * (r i u) ^ 2 +
          ∑ j ∈ Finset.univ.erase i, p.eval (μ i) * q.eval (μ j) * (r i u * r j u)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
      congr 1
      · rw [Polynomial.eval_mul]; ring
      · refine Finset.sum_congr rfl fun j _ => by ring
    rw [hsplit, Finset.sum_add_distrib, add_sub_cancel_left]
  simp_rw [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
  rw [← Finset.mul_sum, horth i j hij, mul_zero]

/-- **Theorem 7.2 (Galois orthogonality trace constraint):**
For any symmetric matrix `A : Matrix (Fin n) (Fin n) ℝ`, family of distinct simple eigenvalues
`μ : Fin e → ℝ`, and reference vertex `u0 : Fin n` at which `(A_{u0}).charpoly.eval (μ i) ≠ 0`,
there exist normalized ratios `r : Fin e → Fin n → ℝ` with `r i u0 = 1`,
`(r i u)^2 = χ_{A_u}(μ_i) / χ_{A_{u0}}(μ_i)`, `∑ u, r i u * r j u = 0` (`i ≠ j`), and vanishing
bilinear Galois trace sums for all `p, q : ℝ[X]`. -/
theorem galois_orthogonality_trace_constraint {m e : ℕ} {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hA : A.IsHermitian) (μ : Fin e → ℝ) (hμ_inj : Function.Injective μ)
    (hroot : ∀ i : Fin e, A.charpoly.eval (μ i) = 0)
    (hsimple : ∀ i : Fin e, A.charpoly.derivative.eval (μ i) ≠ 0)
    (u0 : Fin (m + 1))
    (hu0 : ∀ i : Fin e, (A.submatrix u0.succAbove u0.succAbove).charpoly.eval (μ i) ≠ 0) :
    ∃ r : Fin e → Fin (m + 1) → ℝ,
      (∀ i : Fin e, r i u0 = 1) ∧
      (∀ i : Fin e, ∀ u : Fin (m + 1),
        (r i u) ^ 2 = (A.submatrix u.succAbove u.succAbove).charpoly.eval (μ i) /
          (A.submatrix u0.succAbove u0.succAbove).charpoly.eval (μ i)) ∧
      (∀ i j : Fin e, i ≠ j → ∑ u : Fin (m + 1), r i u * r j u = 0) ∧
      (∀ p q : ℝ[X],
        ∑ u : Fin (m + 1),
          ((∑ i : Fin e, p.eval (μ i) * r i u) * (∑ j : Fin e, q.eval (μ j) * r j u) -
            ∑ i : Fin e, (p * q).eval (μ i) * (r i u) ^ 2) = 0) := by
  have hex : ∀ i : Fin e, ∃ w : Fin (m + 1) → ℝ,
      A *ᵥ w = μ i • w ∧ w ⬝ᵥ w = 1 ∧
      ∀ u : Fin (m + 1), (A.submatrix u.succAbove u.succAbove).charpoly.eval (μ i) =
        A.charpoly.derivative.eval (μ i) * (w u) ^ 2 := fun i =>
    simple_eig_projector_diag hA (hroot i) (hsimple i)
  choose w hw_eig _ hw_diag using hex
  have hw0_ne : ∀ i : Fin e, w i u0 ≠ 0 := by
    intro i hz
    have h0 := hw_diag i u0
    rw [hz, sq, mul_zero, mul_zero] at h0
    exact hu0 i h0
  have hw_orth : ∀ i j : Fin e, i ≠ j → w i ⬝ᵥ w j = 0 := by
    intro i j hij
    have hne_mu : μ i ≠ μ j := hμ_inj.ne hij
    have h1 : (A *ᵥ w i) ⬝ᵥ w j = μ i * (w i ⬝ᵥ w j) := by
      rw [hw_eig i, smul_dotProduct, smul_eq_mul]
    have h2 : (A *ᵥ w i) ⬝ᵥ w j = μ j * (w i ⬝ᵥ w j) := by
      have hAsymm : Aᵀ = A := by
        ext a b
        simpa [Matrix.transpose_apply] using hA.apply a b
      calc
        (A *ᵥ w i) ⬝ᵥ w j = (Aᵀ *ᵥ w i) ⬝ᵥ w j := by rw [hAsymm]
        _ = (w i ᵥ* A) ⬝ᵥ w j := by rw [Matrix.mulVec_transpose]
        _ = w i ⬝ᵥ (A *ᵥ w j) := (dotProduct_mulVec (w i) A (w j)).symm
        _ = w i ⬝ᵥ (μ j • w j) := by rw [hw_eig j]
        _ = μ j * (w i ⬝ᵥ w j) := by rw [dotProduct_smul, smul_eq_mul]
    have hdiff : (μ i - μ j) * (w i ⬝ᵥ w j) = 0 := by linarith
    exact (mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hne_mu)
  let r : Fin e → Fin (m + 1) → ℝ := fun i u => w i u / w i u0
  have hr_orth : ∀ i j : Fin e, i ≠ j → ∑ u : Fin (m + 1), r i u * r j u = 0 := fun i j hij => by
    have hsum : (∑ u : Fin (m + 1), r i u * r j u) =
        (w i u0 * w j u0)⁻¹ * (w i ⬝ᵥ w j) := by
      calc
        (∑ u : Fin (m + 1), r i u * r j u)
            = ∑ u : Fin (m + 1), (w i u0 * w j u0)⁻¹ * (w i u * w j u) := by
              refine Finset.sum_congr rfl fun u _ => ?_
              dsimp [r]
              ring
        _ = (w i u0 * w j u0)⁻¹ * (w i ⬝ᵥ w j) := (Finset.mul_sum _ _ _).symm
    rw [hsum, hw_orth i j hij, mul_zero]
  refine ⟨r, fun i => div_self (hw0_ne i), fun i u => ?_, hr_orth,
    fun p q => galois_orthogonality_of_orth_vectors μ r hr_orth p q⟩
  dsimp [r]
  rw [div_pow, hw_diag i u, hw_diag i u0]
  have hd_ne : A.charpoly.derivative.eval (μ i) ≠ 0 := hsimple i
  have hw2_ne : (w i u0) ^ 2 ≠ 0 := pow_ne_zero 2 (hw0_ne i)
  field_simp [hd_ne, hw2_ne]

end Theorem72

section Proposition61

private lemma matrix_sub_mul_ker_vanish_of_vertex {m : ℕ}
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hA : A.IsHermitian) (μ : ℝ)
    (v : Fin (m + 1))
    (hm : Module.finrank ℝ (LinearMap.ker (A - μ • 1).mulVecLin) ≤
      Module.finrank ℝ (LinearMap.ker
        (A.submatrix v.succAbove v.succAbove - μ • 1).mulVecLin))
    {w : Fin (m + 1) → ℝ} (hw : w ∈ LinearMap.ker (A - μ • 1).mulVecLin) :
    w v = 0 := by
  by_contra hwv
  let B : Matrix (Fin m) (Fin m) ℝ := A.submatrix v.succAbove v.succAbove - μ • 1
  let L : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ) := (A - μ • 1).mulVecLin
  let extLin : (Fin m → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ) :=
    { toFun := fun u i => ∑ t : Fin m, if v.succAbove t = i then u t else 0
      map_add' := fun u1 u2 => by
        ext i
        dsimp only [Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun t _ => by split_ifs <;> simp
      map_smul' := fun c u => by
        ext i
        dsimp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => by split_ifs <;> simp }
  have hext_succ : ∀ u t, extLin u (v.succAbove t) = u t := fun u t => by
    simp [extLin, Fin.succAbove_right_injective.eq_iff, Finset.sum_ite_eq']
  have hext_v : ∀ u, extLin u v = 0 := fun u => by
    dsimp [extLin]
    exact Finset.sum_eq_zero fun t _ => ite_eq_right (Fin.succAbove_ne v t)
  have hext_inj : Function.Injective extLin := by
    intro u1 u2 h
    ext t
    have ht := congrFun h (v.succAbove t)
    rwa [hext_succ, hext_succ] at ht
  have hmem_ker : ∀ u ∈ LinearMap.ker B.mulVecLin, extLin u ∈ LinearMap.ker L := by
    intro u hu
    rw [LinearMap.mem_ker] at hu ⊢
    change (A - μ • 1) *ᵥ extLin u = 0
    have hother : ∀ t : Fin m, ((A - μ • 1) *ᵥ extLin u) (v.succAbove t) = 0 := fun t => by
      have hu_t := congrFun hu t
      change (B *ᵥ u) t = 0 at hu_t
      rw [← hu_t]
      simp only [B, Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.submatrix_apply,
        Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      have hsplit : (∑ j : Fin (m + 1), (A (v.succAbove t) j -
          μ * (if v.succAbove t = j then (1 : ℝ) else 0)) * extLin u j) =
          ∑ a : Fin m, (A (v.succAbove t) (v.succAbove a) -
            μ * (if t = a then (1 : ℝ) else 0)) * u a := by
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ v), hext_v u, mul_zero,
          zero_add]
        have himg : Finset.univ.erase v = Finset.univ.image v.succAbove := by
          ext j
          simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_image, true_and]
          constructor
          · exact Fin.exists_succAbove_eq
          · rintro ⟨a, rfl⟩
            exact Fin.succAbove_ne v a
        rw [himg, Finset.sum_image (fun a _ b _ h => Fin.succAbove_right_injective h)]
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [hext_succ, Fin.succAbove_right_injective.eq_iff]
      exact hsplit
    have hw0 : (A - μ • 1) *ᵥ w = 0 := LinearMap.mem_ker.mp hw
    have hAsymm : (A - μ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ))ᵀ = A - μ • 1 := by
      have hA_sym : Aᵀ = A := by
        ext a b
        simpa [Matrix.transpose_apply] using hA.apply a b
      rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, hA_sym]
    have hdot0 : w ⬝ᵥ ((A - μ • 1) *ᵥ extLin u) = 0 := by
      calc
        w ⬝ᵥ ((A - μ • 1) *ᵥ extLin u)
            = (w ᵥ* (A - μ • 1)) ⬝ᵥ extLin u := by rw [dotProduct_mulVec]
        _ = ((A - μ • 1)ᵀ *ᵥ w) ⬝ᵥ extLin u := by rw [← Matrix.mulVec_transpose]
        _ = ((A - μ • 1) *ᵥ w) ⬝ᵥ extLin u := by rw [hAsymm]
        _ = 0 := by rw [hw0, zero_dotProduct]
    have hdot_v : w ⬝ᵥ ((A - μ • 1) *ᵥ extLin u) =
        w v * ((A - μ • 1) *ᵥ extLin u) v := by
      simp only [dotProduct]
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ v)]
      have hrest : (∑ j ∈ Finset.univ.erase v, w j * ((A - μ • 1) *ᵥ extLin u) j) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq (Finset.mem_erase.mp hj).1
        rw [hother t, mul_zero]
      rw [hrest, add_zero]
    have hv_zero : ((A - μ • 1) *ᵥ extLin u) v = 0 := by
      rw [hdot_v] at hdot0
      exact (mul_eq_zero.mp hdot0).resolve_left hwv
    ext j
    by_cases hjv : j = v
    · subst hjv; exact hv_zero
    · obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq hjv
      exact hother t
  let mapK : LinearMap.ker B.mulVecLin →ₗ[ℝ] LinearMap.ker L :=
    { toFun := fun u => ⟨extLin u.1, hmem_ker u.1 u.2⟩
      map_add' := fun u1 u2 => Subtype.ext (extLin.map_add u1.1 u2.1)
      map_smul' := fun c u => Subtype.ext (extLin.map_smul c u.1) }
  have hmapK_inj : Function.Injective mapK := fun u1 u2 h =>
    Subtype.ext (hext_inj (congrArg Subtype.val h))
  let res_v : LinearMap.ker L →ₗ[ℝ] ℝ :=
    { toFun := fun x => x.1 v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hker_strict : LinearMap.ker res_v < (⊤ : Submodule ℝ (LinearMap.ker L)) := by
    rw [lt_top_iff_ne_top]
    intro htop
    have hw_mem : (⟨w, hw⟩ : LinearMap.ker L) ∈ LinearMap.ker res_v := by
      rw [htop]; trivial
    exact hwv (LinearMap.mem_ker.mp hw_mem)
  have hrange_le : LinearMap.range mapK ≤ LinearMap.ker res_v := by
    rintro x ⟨u, rfl⟩
    exact hext_v u.1
  have hrank_lt : Module.finrank ℝ (LinearMap.range mapK) <
      Module.finrank ℝ (LinearMap.ker L) := by
    calc
      Module.finrank ℝ (LinearMap.range mapK)
          ≤ Module.finrank ℝ (LinearMap.ker res_v) := Submodule.finrank_mono hrange_le
      _ < Module.finrank ℝ (⊤ : Submodule ℝ (LinearMap.ker L)) :=
          Submodule.finrank_lt_finrank_of_lt hker_strict
      _ = Module.finrank ℝ (LinearMap.ker L) := finrank_top _ _
  have hrank_eq : Module.finrank ℝ (LinearMap.ker B.mulVecLin) =
      Module.finrank ℝ (LinearMap.range mapK) :=
    (LinearEquiv.ofInjective mapK hmapK_inj).finrank_eq
  have hL_eq : Module.finrank ℝ (LinearMap.ker L) =
      Module.finrank ℝ (LinearMap.ker (A - μ • 1).mulVecLin) := rfl
  have hB_eq : Module.finrank ℝ (LinearMap.ker B.mulVecLin) =
      Module.finrank ℝ (LinearMap.ker
        (A.submatrix v.succAbove v.succAbove - μ • 1).mulVecLin) := rfl
  omega

/-- **Proposition 6.1 (Nullity preservation under vertex deletions):**
If `A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ` is symmetric, `g : Fin k ↪ Fin (m + 1)` is an
excluded vertex set, `f : Fin m' ↪ Fin (m + 1)` spans its complement, and every `v = g a` satisfies
`mult_μ(A_v) ≥ mult_μ(A)`, then `mult_μ(A[Iᶜ]) ≥ mult_μ(A)` (zero multiplicity loss!). -/
theorem ker_submatrix_preserves_nullity {m k m' : ℕ}
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hA : A.IsHermitian) (μ : ℝ)
    (g : Fin k ↪ Fin (m + 1)) (f : Fin m' ↪ Fin (m + 1))
    (hcompl : ∀ i : Fin (m + 1), (∃ b : Fin m', f b = i) ∨ (∃ a : Fin k, g a = i))
    (hdel : ∀ a : Fin k, Module.finrank ℝ (LinearMap.ker (A - μ • 1).mulVecLin) ≤
      Module.finrank ℝ (LinearMap.ker
        (A.submatrix (g a).succAbove (g a).succAbove - μ • 1).mulVecLin)) :
    Module.finrank ℝ (LinearMap.ker (A - μ • 1).mulVecLin) ≤
      Module.finrank ℝ (LinearMap.ker (A.submatrix f f - μ • 1).mulVecLin) := by
  have hvan : ∀ w ∈ LinearMap.ker (A - μ • 1).mulVecLin, ∀ a : Fin k, w (g a) = 0 :=
    fun w hw a => matrix_sub_mul_ker_vanish_of_vertex hA μ (g a) (hdel a) hw
  let restrictF : LinearMap.ker (A - μ • 1).mulVecLin →ₗ[ℝ]
      LinearMap.ker (A.submatrix f f - μ • 1).mulVecLin :=
    { toFun := fun w => ⟨fun b => w.1 (f b), by
        rw [LinearMap.mem_ker]
        have hw0 : (A - μ • 1) *ᵥ w.1 = 0 := LinearMap.mem_ker.mp w.2
        ext b
        have hb := congrFun hw0 (f b)
        rw [Pi.zero_apply] at hb
        change ((A.submatrix f f - μ • 1) *ᵥ (fun c => w.1 (f c))) b = 0
        rw [← hb]
        simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.submatrix_apply,
          Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
        have hsum_split : (∑ i : Fin (m + 1),
            (A (f b) i - μ * (if f b = i then 1 else 0)) * w.1 i) =
            ∑ c : Fin m', (A (f b) (f c) - μ * (if b = c then 1 else 0)) * w.1 (f c) := by
          have hzero_out : ∀ i ∉ Finset.univ.image f,
              (A (f b) i - μ * (if f b = i then 1 else 0)) * w.1 i = 0 := fun i hi => by
            rcases hcompl i with ⟨c, rfl⟩ | ⟨a, rfl⟩
            · exact absurd (Finset.mem_image_of_mem f (Finset.mem_univ c)) hi
            · rw [hvan w.1 w.2 a, mul_zero]
          rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image f)) fun i _ hi => hzero_out i hi,
            Finset.sum_image (fun c1 _ c2 _ h => f.injective h)]
          refine Finset.sum_congr rfl fun c _ => ?_
          simp only [f.injective.eq_iff]
        exact hsum_split.symm⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective restrictF := by
    intro w1 w2 h
    apply Subtype.ext
    ext i
    rcases hcompl i with ⟨b, rfl⟩ | ⟨a, rfl⟩
    · exact congrFun (congrArg Subtype.val h) b
    · rw [hvan w1.1 w1.2 a, hvan w2.1 w2.2 a]
  exact LinearMap.finrank_le_finrank_of_injective hinj

/-- **General interlacing lower bound (`mult_μ(A[Iᶜ]) ≥ mult_μ(A) - |I|`):**
Combining the restriction map from `ker_submatrix_vanish_of_nullity_gt` with zero-outside-`f`
restriction proves `finrank ker(A - μ I) - k ≤ finrank ker(A[Iᶜ] - μ I)` directly. -/
theorem submatrix_nullity_ge_sub {n k m' : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ)
    (g : Fin k ↪ Fin n) (f : Fin m' ↪ Fin n)
    (hcompl : ∀ i : Fin n, (∃ b : Fin m', f b = i) ∨ (∃ a : Fin k, g a = i)) :
    Module.finrank ℝ (LinearMap.ker (A - μ • 1).mulVecLin) - k ≤
      Module.finrank ℝ (LinearMap.ker (A.submatrix f f - μ • 1).mulVecLin) := by
  let E := LinearMap.ker (A - μ • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVecLin
  let resG : E →ₗ[ℝ] (Fin k → ℝ) :=
    { toFun := fun w a => w.1 (g a)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hrn := LinearMap.finrank_range_add_finrank_ker resG
  have hrange_le : Module.finrank ℝ (LinearMap.range resG) ≤ k := by
    calc
      Module.finrank ℝ (LinearMap.range resG) ≤ Module.finrank ℝ (Fin k → ℝ) :=
        Submodule.finrank_le _
      _ = k := by simp
  let mapK : LinearMap.ker resG →ₗ[ℝ]
      LinearMap.ker (A.submatrix f f - μ • (1 : Matrix (Fin m') (Fin m') ℝ)).mulVecLin :=
    { toFun := fun w => ⟨fun b => w.1.1 (f b), by
        rw [LinearMap.mem_ker]
        have hw0 : (A - μ • 1) *ᵥ w.1.1 = 0 := LinearMap.mem_ker.mp w.1.2
        have hvan : ∀ a : Fin k, w.1.1 (g a) = 0 := fun a =>
          congrFun (LinearMap.mem_ker.mp w.2) a
        ext b
        have hb := congrFun hw0 (f b)
        rw [Pi.zero_apply] at hb
        change ((A.submatrix f f - μ • 1) *ᵥ (fun c => w.1.1 (f c))) b = 0
        rw [← hb]
        simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.submatrix_apply,
          Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
        have hzero_out : ∀ i ∉ Finset.univ.image f,
            (A (f b) i - μ * (if f b = i then 1 else 0)) * w.1.1 i = 0 := fun i hi => by
          rcases hcompl i with ⟨c, rfl⟩ | ⟨a, rfl⟩
          · exact absurd (Finset.mem_image_of_mem f (Finset.mem_univ c)) hi
          · rw [hvan a, mul_zero]
        rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image f)) fun i _ hi => hzero_out i hi,
          Finset.sum_image (fun c1 _ c2 _ h => f.injective h)]
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [f.injective.eq_iff]⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective mapK := by
    intro w1 w2 h
    apply Subtype.ext; apply Subtype.ext
    ext i
    rcases hcompl i with ⟨b, rfl⟩ | ⟨a, rfl⟩
    · exact congrFun (congrArg Subtype.val h) b
    · have h1 : w1.1.1 (g a) = 0 := congrFun (LinearMap.mem_ker.mp w1.2) a
      have h2 : w2.1.1 (g a) = 0 := congrFun (LinearMap.mem_ker.mp w2.2) a
      rw [h1, h2]
  have hle_map := LinearMap.finrank_le_finrank_of_injective hinj
  have hE_eq : Module.finrank ℝ E =
      Module.finrank ℝ (LinearMap.ker (A - μ • 1).mulVecLin) := rfl
  omega

/-- Convenience alias matching Proposition 6.1 naming: vertex-deletion multiplicity lower bound
directly on the complement submatrix `A.submatrix f f`. -/
theorem submatrix_nullity_ge_of_vertex_deletions {m k m' : ℕ}
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hA : A.IsHermitian) (μ : ℝ)
    (g : Fin k ↪ Fin (m + 1)) (f : Fin m' ↪ Fin (m + 1))
    (hcompl : ∀ i : Fin (m + 1), (∃ b : Fin m', f b = i) ∨ (∃ a : Fin k, g a = i))
    (hdel : ∀ a : Fin k, Module.finrank ℝ (LinearMap.ker (A - μ • 1).mulVecLin) ≤
      Module.finrank ℝ (LinearMap.ker
        (A.submatrix (g a).succAbove (g a).succAbove - μ • 1).mulVecLin)) :
    Module.finrank ℝ (LinearMap.ker (A - μ • 1).mulVecLin) ≤
      Module.finrank ℝ (LinearMap.ker (A.submatrix f f - μ • 1).mulVecLin) :=
  ker_submatrix_preserves_nullity hA μ g f hcompl hdel

/-- Exact equality between `dim ker (A - μ I)` and spectral eigenvalue count
`(Finset.univ.filter (fun k => hA.eigenvalues k = μ)).card` for any real symmetric matrix `A`. -/
theorem submatrix_eigenvalue_count_eq_finrank_ker {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (μ : ℝ) :
    Module.finrank ℝ (LinearMap.ker (A - μ • 1).mulVecLin) =
      (Finset.univ.filter fun k : Fin n => hA.eigenvalues k = μ).card := by
  let U : Matrix (Fin n) (Fin n) ℝ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  have hUU : U * Uᵀ = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hU'U : Uᵀ * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hspec : A = U * Matrix.diagonal hA.eigenvalues * Uᵀ := by
    simpa [U, Matrix.star_eq_conjTranspose, RCLike.ofReal_real_eq_id] using hA.spectral_theorem
  have hdiff : A - μ • (1 : Matrix (Fin n) (Fin n) ℝ) =
      U * Matrix.diagonal (fun k => hA.eigenvalues k - μ) * Uᵀ := by
    calc
      A - μ • (1 : Matrix (Fin n) (Fin n) ℝ)
          = U * Matrix.diagonal hA.eigenvalues * Uᵀ -
              U * (μ • (1 : Matrix (Fin n) (Fin n) ℝ)) * Uᵀ := by
            rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUU, ← hspec]
      _ = U * (Matrix.diagonal hA.eigenvalues - μ • (1 : Matrix (Fin n) (Fin n) ℝ)) * Uᵀ := by
            simp only [Matrix.mul_sub, Matrix.sub_mul]
      _ = U * Matrix.diagonal (fun k => hA.eigenvalues k - μ) * Uᵀ := by
            congr 2
            ext a b
            by_cases hab : a = b <;> simp [hab]
  have hmem_iff : ∀ x : Fin n → ℝ,
      x ∈ LinearMap.ker (A - μ • 1).mulVecLin ↔
        ∀ k : Fin n, hA.eigenvalues k ≠ μ → (Uᵀ *ᵥ x) k = 0 := by
    intro x
    rw [LinearMap.mem_ker]
    change (A - μ • 1) *ᵥ x = 0 ↔ _
    rw [hdiff]
    have hmul_eq : (U * Matrix.diagonal (fun k => hA.eigenvalues k - μ) * Uᵀ) *ᵥ x =
        U *ᵥ (Matrix.diagonal (fun k => hA.eigenvalues k - μ) *ᵥ (Uᵀ *ᵥ x)) := by
      simp only [Matrix.mul_assoc, Matrix.mulVec_mulVec]
    rw [hmul_eq]
    constructor
    · intro h k hne
      have h2 := congrArg (fun v => (Uᵀ *ᵥ v) k) h
      rw [Matrix.mulVec_mulVec, hU'U, Matrix.one_mulVec, Matrix.mulVec_zero, Pi.zero_apply,
        Matrix.mulVec_diagonal] at h2
      exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)
    · intro h
      have hdiag : Matrix.diagonal (fun k => hA.eigenvalues k - μ) *ᵥ (Uᵀ *ᵥ x) = 0 := by
        ext k
        rw [Matrix.mulVec_diagonal, Pi.zero_apply]
        by_cases hkm : hA.eigenvalues k = μ
        · simp [hkm]
        · simp [h k hkm]
      rw [hdiag, Matrix.mulVec_zero]
  let S_idx := {k : Fin n // hA.eigenvalues k = μ}
  let toFun : LinearMap.ker (A - μ • 1).mulVecLin →ₗ[ℝ] (S_idx → ℝ) :=
    { toFun := fun x k => (Uᵀ *ᵥ x.1) k.1
      map_add' := fun x1 x2 => by ext k; simp [Matrix.mulVec_add]
      map_smul' := fun c x => by ext k; simp [Matrix.mulVec_smul] }
  let invFun : (S_idx → ℝ) → (LinearMap.ker (A - μ • 1).mulVecLin) :=
    fun y => ⟨U *ᵥ (fun k => if hk : hA.eigenvalues k = μ then y ⟨k, hk⟩ else 0), by
      rw [hmem_iff]
      intro k hne
      rw [Matrix.mulVec_mulVec, hU'U, Matrix.one_mulVec]
      simp [hne]⟩
  have hleft : ∀ x, invFun (toFun x) = x := fun x => by
    apply Subtype.ext
    dsimp [invFun]
    have hvec : (fun k => if hk : hA.eigenvalues k = μ then (toFun x) ⟨k, hk⟩ else 0) =
        Uᵀ *ᵥ x.1 := by
      ext k
      by_cases hk : hA.eigenvalues k = μ
      · simp [toFun, hk]
      · simp [hk, (hmem_iff x.1).mp x.2 k hk]
    rw [hvec, Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
  have hright : ∀ y, toFun (invFun y) = y := fun y => by
    ext ⟨k, hk⟩
    dsimp [invFun, toFun]
    rw [Matrix.mulVec_mulVec, hU'U, Matrix.one_mulVec]
    simp [hk]
  let e : LinearMap.ker (A - μ • 1).mulVecLin ≃ₗ[ℝ] (S_idx → ℝ) :=
    { toFun := toFun
      map_add' := toFun.map_add'
      map_smul' := toFun.map_smul'
      invFun := invFun
      left_inv := hleft
      right_inv := hright }
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_subtype]

/-- **Proposition 6.1 (Submatrix Trace & Cauchy–Schwarz Obstruction):**
Let `T = S.submatrix f f` be an `m' × m'` principal submatrix of a Seidel matrix `S` (`IsSeidelMatrix`),
and let `idx : Fin r ↪ Fin m'` pick out `r` locked eigenvalues `vals j = hT.eigenvalues (idx j)`
of `T` (e.g. from `ker_submatrix_preserves_nullity` and `submatrix_nullity_ge_sub`). With
`t = m' - r`, the sum and squared sum of `vals` satisfy Cauchy–Schwarz against `Tr(T) = 0` and
`Tr(T^2) = m' * (m' - 1)`:
`(∑ j, vals j) ^ 2 + t * (∑ j, vals j ^ 2) ≤ t * (m' * (m' - 1))`. -/
theorem submatrix_trace_cauchy_schwarz_obstruction {n m' r : ℕ}
    {S : Matrix (Fin n) (Fin n) ℤ} (hS : IsSeidelMatrix S) (f : Fin m' ↪ Fin n)
    (hT : ((S.submatrix f f).map (Int.cast : ℤ → ℝ)).IsHermitian)
    (idx : Fin r ↪ Fin m') (vals : Fin r → ℝ)
    (hvals : ∀ j : Fin r, hT.eigenvalues (idx j) = vals j) :
    (∑ j : Fin r, vals j) ^ 2 + ((m' - r : ℕ) : ℝ) * ∑ j : Fin r, (vals j) ^ 2 ≤
      ((m' - r : ℕ) : ℝ) * ((m' : ℝ) * ((m' : ℝ) - 1)) := by
  let Tℤ : Matrix (Fin m') (Fin m') ℤ := S.submatrix f f
  have hTℤ : IsSeidelMatrix Tℤ := hS.submatrix f
  let T : Matrix (Fin m') (Fin m') ℝ := Tℤ.map (Int.cast : ℤ → ℝ)
  have hTr0 : T.trace = 0 := by
    have hZ : Tℤ.trace = 0 := hTℤ.trace_eq_zero
    simp only [T, Matrix.trace, Matrix.diag_apply, Matrix.map_apply]
    simpa [Matrix.trace, Matrix.diag_apply] using congrArg (Int.cast : ℤ → ℝ) hZ
  have hTr2 : (T * T).trace = (m' : ℝ) * ((m' : ℝ) - 1) := by
    have hZ : (Tℤ * Tℤ).trace = (m' : ℤ) * ((m' : ℤ) - 1) := hTℤ.trace_sq
    have hm_raw : (Tℤ * Tℤ).map (Int.castRingHom ℝ) =
        Tℤ.map (Int.castRingHom ℝ) * Tℤ.map (Int.castRingHom ℝ) := Matrix.map_mul
    have hm : T * T = (Tℤ * Tℤ).map (Int.castRingHom ℝ) := hm_raw.symm
    rw [hm]
    have htr : ((Tℤ * Tℤ).map (Int.castRingHom ℝ)).trace = ((Tℤ * Tℤ).trace : ℝ) := by
      simp [Matrix.trace, Matrix.diag_apply]
    rw [htr, hZ]
    push_cast
    ring
  have hsum_eigs : (∑ k : Fin m', hT.eigenvalues k) = 0 := by
    have h := hT.trace_eq_sum_eigenvalues
    simp only [RCLike.ofReal_real_eq_id, id_eq] at h
    change T.trace = _ at h
    rw [hTr0] at h
    exact h.symm
  have hsum_eigs2 : (∑ k : Fin m', hT.eigenvalues k ^ 2) = (m' : ℝ) * ((m' : ℝ) - 1) := by
    let U : Matrix (Fin m') (Fin m') ℝ := hT.eigenvectorUnitary
    let D : Matrix (Fin m') (Fin m') ℝ := Matrix.diagonal hT.eigenvalues
    have hspec : T = U * D * star U := by
      simpa [T, U, D, Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id, Function.comp_def]
        using hT.spectral_theorem
    have hUU : star U * U = 1 := Unitary.coe_star_mul_self hT.eigenvectorUnitary
    have hM2 : T * T = U * (D * D) * star U := by
      calc T * T = (U * D * star U) * (U * D * star U) := by rw [hspec]
        _ = U * D * (star U * U) * D * star U := by simp only [Matrix.mul_assoc]
        _ = U * (D * D) * star U := by rw [hUU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    have hsq : (T * T).trace = ∑ k : Fin m', hT.eigenvalues k ^ 2 := by
      rw [hM2, Matrix.trace_mul_cycle, hUU, Matrix.one_mul]
      simp only [D, Matrix.diagonal_mul_diagonal, Matrix.trace, Matrix.diag_apply,
        Matrix.diagonal_apply_eq, sq]
    rw [← hsq, hTr2]
  let used : Finset (Fin m') := Finset.univ.image idx
  let rest : Finset (Fin m') := Finset.univ \ used
  have hused_card : used.card = r := by
    rw [Finset.card_image_of_injective _ idx.injective, Finset.card_univ, Fintype.card_fin]
  have hrest_card : rest.card = m' - r := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ used),
      Finset.card_univ, Fintype.card_fin, hused_card]
  have hsum_used : (∑ k ∈ used, hT.eigenvalues k) = ∑ j : Fin r, vals j := by
    rw [Finset.sum_image (fun a _ b _ h => idx.injective h)]
    exact Finset.sum_congr rfl fun j _ => hvals j
  have hsum_used2 : (∑ k ∈ used, hT.eigenvalues k ^ 2) = ∑ j : Fin r, vals j ^ 2 := by
    rw [Finset.sum_image (fun a _ b _ h => idx.injective h)]
    exact Finset.sum_congr rfl fun j _ => by rw [hvals j]
  have hsplit1 : (∑ k : Fin m', hT.eigenvalues k) =
      (∑ k ∈ used, hT.eigenvalues k) + (∑ k ∈ rest, hT.eigenvalues k) := by
    rw [← Finset.sum_union (disjoint_sdiff_self_right : Disjoint used rest),
      Finset.union_sdiff_of_subset (Finset.subset_univ used)]
  have hsplit2 : (∑ k : Fin m', hT.eigenvalues k ^ 2) =
      (∑ k ∈ used, hT.eigenvalues k ^ 2) + (∑ k ∈ rest, hT.eigenvalues k ^ 2) := by
    rw [← Finset.sum_union (disjoint_sdiff_self_right : Disjoint used rest),
      Finset.union_sdiff_of_subset (Finset.subset_univ used)]
  have hrest_sum : (∑ k ∈ rest, hT.eigenvalues k) = -∑ j : Fin r, vals j := by
    rw [hsum_eigs, hsum_used] at hsplit1
    linarith
  have hrest_sum2 : (∑ k ∈ rest, hT.eigenvalues k ^ 2) =
      (m' : ℝ) * ((m' : ℝ) - 1) - ∑ j : Fin r, vals j ^ 2 := by
    rw [hsum_eigs2, hsum_used2] at hsplit2
    linarith
  have hcs := sq_sum_le_card_mul_sum_sq (s := rest) (f := hT.eigenvalues)
  rw [hrest_card, hrest_sum, hrest_sum2, neg_sq] at hcs
  linarith

end Proposition61

end EquiangularLines

end
