module

public import EquiangularLines.Phase3Algebra
public import EquiangularLines.Certs19_74A
public import EquiangularLines.Certs19_74B
public import EquiangularLines.Certs19_74C

/-!
# Exact Rational Farkas Certificates & `(19, 74)` Stage-2 Pure-Kernel Verification

This module proves:
1. `farkas_infeasible_nonneg`: exact rational Farkas lemma for `x ≥ 0`, `Aᵀ x = b`.
2. `farkas_infeasible_box`: exact rational Farkas lemma for bounded box variables `lo ≤ x ≤ hi`.
3. `checkCertZ_sound`: soundness of the pure-kernel checker `Certs.checkCertZ` (`CertKernel.lean`).
4. `charpoly_eliminated_of_deck_farkas`: connects `derivative_charpoly_eq_sum_vertex_deletions`
   (`Spectral.lean`) on an actual integer matrix `S : Matrix (Fin n) (Fin n) ℤ` directly to a
   certified Farkas refutation of its vertex-deletion deck.
5. `certs19_74_all_147_verified`: aggregates all `147` Stage-2 `1-vertex_farkas` certificates
   for `(19, 74)` proved purely in-kernel by `decide` across `Certs19_74A/B/C.lean`
   (zero `native_decide`, zero `sorry`, zero custom axioms).
-/

@[expose] public section

open Matrix Polynomial
open scoped BigOperators

namespace EquiangularLines

section FarkasCore

/-- **Exact Rational Nonnegative Farkas Lemma (`x ≥ 0, Aᵀ x = b`):**
If `yᵀ b < 0` while `yᵀ (A j) ≥ 0` for every column `j`, no `x ≥ 0` satisfies `∑ j, x j * A j i = b i`. -/
theorem farkas_infeasible_nonneg {m n : ℕ} (y : Fin m → ℚ)
    (A : Fin n → Fin m → ℚ) (b : Fin m → ℚ) (x : Fin n → ℚ)
    (hx : ∀ j : Fin n, 0 ≤ x j)
    (hAx : ∀ i : Fin m, (∑ j : Fin n, x j * A j i) = b i)
    (hdual_cols : ∀ j : Fin n, 0 ≤ ∑ i : Fin m, y i * A j i)
    (hdual_rhs : (∑ i : Fin m, y i * b i) < 0) :
    False := by
  have hsum : (∑ i : Fin m, y i * b i) = ∑ j : Fin n, x j * ∑ i : Fin m, y i * A j i := by
    calc
      (∑ i : Fin m, y i * b i)
          = ∑ i : Fin m, y i * ∑ j : Fin n, x j * A j i := by
            refine Finset.sum_congr rfl fun i _ => by rw [hAx i]
      _ = ∑ i : Fin m, ∑ j : Fin n, x j * (y i * A j i) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ j : Fin n, ∑ i : Fin m, x j * (y i * A j i) := Finset.sum_comm
      _ = ∑ j : Fin n, x j * ∑ i : Fin m, y i * A j i := by
            refine Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
  have hnonneg : 0 ≤ ∑ i : Fin m, y i * b i := by
    rw [hsum]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hx j) (hdual_cols j)
  linarith

/-- **Exact Rational Box Farkas Lemma (`lo ≤ x ≤ hi, Aᵀ x = b`):**
Any dual vector `y` whose RHS inner product `yᵀ b` strictly undercuts the box lower bound
`∑ j, min(lo_j * yᵀ A_j, hi_j * yᵀ A_j)` rules out all feasible `x ∈ [lo, hi]`. -/
theorem farkas_infeasible_box {m n : ℕ} (y : Fin m → ℚ)
    (A : Fin n → Fin m → ℚ) (b : Fin m → ℚ) (lo hi x : Fin n → ℚ)
    (hx : ∀ j : Fin n, lo j ≤ x j ∧ x j ≤ hi j)
    (hAx : ∀ i : Fin m, (∑ j : Fin n, x j * A j i) = b i)
    (hdual : (∑ i : Fin m, y i * b i) <
      ∑ j : Fin n,
        if 0 ≤ (∑ i : Fin m, y i * A j i) then lo j * (∑ i : Fin m, y i * A j i)
        else hi j * (∑ i : Fin m, y i * A j i)) :
    False := by
  have hsum : (∑ i : Fin m, y i * b i) = ∑ j : Fin n, x j * ∑ i : Fin m, y i * A j i := by
    calc
      (∑ i : Fin m, y i * b i)
          = ∑ i : Fin m, y i * ∑ j : Fin n, x j * A j i := by
            refine Finset.sum_congr rfl fun i _ => by rw [hAx i]
      _ = ∑ i : Fin m, ∑ j : Fin n, x j * (y i * A j i) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ j : Fin n, ∑ i : Fin m, x j * (y i * A j i) := Finset.sum_comm
      _ = ∑ j : Fin n, x j * ∑ i : Fin m, y i * A j i := by
            refine Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
  have hge :
      (∑ j : Fin n,
        if 0 ≤ (∑ i : Fin m, y i * A j i) then lo j * (∑ i : Fin m, y i * A j i)
        else hi j * (∑ i : Fin m, y i * A j i)) ≤
      ∑ i : Fin m, y i * b i := by
    rw [hsum]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hc : 0 ≤ ∑ i : Fin m, y i * A j i
    · rw [ite_eq_left_iff.mpr fun h => absurd hc h]
      exact mul_le_mul_of_nonneg_right (hx j).1 hc
    · rw [ite_eq_right_iff.mpr fun h => absurd h hc]
      exact mul_le_mul_of_nonpos_right (hx j).2 (le_of_not_ge hc)
  linarith

end FarkasCore

section DeckFarkasBridge

/-- Polynomial in `ℚ[X]` from a descending integer coefficient list `[a_0, ..., a_{s-1}]`
representing `∑ i, a_i * X^(s - 1 - i)`. -/
noncomputable def polyOfDescList : List ℤ → ℚ[X]
  | [] => 0
  | a :: as => C (a : ℚ) * X ^ as.length + polyOfDescList as

private lemma polyOfDescList_coeff_eq_zero_of_ge :
    ∀ (xs : List ℤ) {k : ℕ}, xs.length ≤ k → (polyOfDescList xs).coeff k = 0
  | [], _, _ => by simp [polyOfDescList]
  | a :: as, k, hk => by
    simp only [List.length_cons] at hk
    have hk_gt : as.length < k := hk
    have h1 : (C (a : ℚ) * X ^ as.length).coeff k = 0 := by
      rw [Polynomial.coeff_C_mul_X_pow]
      exact ite_eq_right_iff.mpr fun h => False.elim ((Nat.ne_of_gt hk_gt) h)
    have h2 : (polyOfDescList as).coeff k = 0 :=
      polyOfDescList_coeff_eq_zero_of_ge as (Nat.le_of_lt hk_gt)
    rw [polyOfDescList, Polynomial.coeff_add, h1, h2, zero_add]

/-- Coefficient extraction for `polyOfDescList`: entry `i : Fin xs.length` gives the degree
`xs.length - 1 - i` coefficient. -/
theorem polyOfDescList_coeff :
    ∀ (xs : List ℤ) (i : Fin xs.length),
      (polyOfDescList xs).coeff (xs.length - 1 - i.1) = (xs[i.1] : ℚ)
  | [], i => Fin.elim0 i
  | a :: as, ⟨0, _⟩ => by
    simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero, List.getElem_cons_zero,
      polyOfDescList, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, ↓reduceIte,
      polyOfDescList_coeff_eq_zero_of_ge as le_rfl, add_zero]
  | a :: as, ⟨k + 1, hk⟩ => by
    have hk' : k < as.length := Nat.lt_of_succ_lt_succ hk
    have hlt : as.length - 1 - k < as.length := by omega
    have h1 : (C (a : ℚ) * X ^ as.length).coeff (as.length - 1 - k) = 0 := by
      rw [Polynomial.coeff_C_mul_X_pow]
      exact ite_eq_right_iff.mpr fun h => False.elim ((Nat.ne_of_lt hlt) h)
    have hsub : (a :: as).length - 1 - (k + 1) = as.length - 1 - k := by
      simp only [List.length_cons]; omega
    rw [hsub]
    simp only [polyOfDescList, Polynomial.coeff_add, h1, zero_add, List.getElem_cons_succ]
    exact polyOfDescList_coeff as ⟨k, hk'⟩

private lemma dotZ_eq_sum_fin :
    ∀ (y v : List ℤ) (hlen : y.length = v.length),
      Certs.dotZ y v = ∑ i : Fin y.length, y[i.1] * v[i.1]'(hlen ▸ i.2)
  | [], [], _ => by simp [Certs.dotZ]
  | a :: as, b :: bs, hlen => by
    simp only [List.length_cons, Nat.succ.injEq] at hlen
    have ih := dotZ_eq_sum_fin as bs hlen
    simp only [Certs.dotZ, ih]
    symm
    change ∑ i : Fin (as.length + 1),
      (a :: as)[i.1] * (b :: bs)[i.1]'(by rw [List.length_cons, ← hlen]; exact i.2) =
      a * b + ∑ i : Fin as.length, as[i.1] * bs[i.1]'(hlen ▸ i.2)
    rw [Fin.sum_univ_succ]
    simp

private lemma checkCertZ_spec {rhs y : List ℤ} {cols : List (List ℤ)}
    (hchk : Certs.checkCertZ rhs y cols = true) :
    y.length = rhs.length ∧
    Certs.dotZ y rhs < 0 ∧
    (∀ col ∈ cols, col.length = y.length ∧ 0 ≤ Certs.dotZ y col) := by
  dsimp [Certs.checkCertZ] at hchk
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hchk
  rcases hchk with ⟨⟨hlen, hneg⟩, hcols⟩
  refine ⟨hlen, hneg, fun col hmem => ?_⟩
  exact hcols col hmem

/-- **Soundness of Pure-Kernel `Certs.checkCertZ`:**
If `Certs.checkCertZ rhs y cols = true`, no nonnegative linear combination of columns in `cols`
equals `rhs`. -/
theorem checkCertZ_sound {n : ℕ} {rhs y : List ℤ} {cols : List (List ℤ)}
    (hchk : Certs.checkCertZ rhs y cols = true)
    (x : Fin n → ℚ) (hx : ∀ j, 0 ≤ x j)
    (v : Fin n → List ℤ) (hv_mem : ∀ j, v j ∈ cols)
    (hAx : ∀ i : Fin rhs.length,
      (∑ j : Fin n, x j * ((v j).getD i.1 0 : ℚ)) = (rhs[i.1] : ℚ)) :
    False := by
  obtain ⟨hlen_yr, hneg, hcols⟩ := checkCertZ_spec hchk
  let m := rhs.length
  let yQ : Fin m → ℚ := fun i => (y[i.1]'(hlen_yr.symm ▸ i.2) : ℚ)
  let bQ : Fin m → ℚ := fun i => (rhs[i.1] : ℚ)
  let AQ : Fin n → Fin m → ℚ := fun j i => ((v j).getD i.1 0 : ℚ)
  let e : Fin y.length ≃ Fin m :=
    ⟨Fin.cast hlen_yr, Fin.cast hlen_yr.symm, fun _ => rfl, fun _ => rfl⟩
  have hdual_cols : ∀ j : Fin n, 0 ≤ ∑ i : Fin m, yQ i * AQ j i := fun j => by
    have hnn := (hcols (v j) (hv_mem j)).2
    have hdot := dotZ_eq_sum_fin y (v j) (hcols (v j) (hv_mem j)).1.symm
    have hcast : ((Certs.dotZ y (v j) : ℤ) : ℚ) = ∑ i : Fin m, yQ i * AQ j i := by
      rw [hdot]
      push_cast
      refine Fintype.sum_equiv e _ _ fun i => ?_
      have hlt : i.1 < (v j).length := by rw [(hcols (v j) (hv_mem j)).1]; exact i.2
      simp [yQ, AQ, e, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    rw [← hcast]
    exact_mod_cast hnn
  have hdual_rhs : (∑ i : Fin m, yQ i * bQ i) < 0 := by
    have hdot := dotZ_eq_sum_fin y rhs hlen_yr
    have hcast : ((Certs.dotZ y rhs : ℤ) : ℚ) = ∑ i : Fin m, yQ i * bQ i := by
      rw [hdot]
      push_cast
      exact Fintype.sum_equiv e _ _ fun _ => rfl
    rw [← hcast]
    exact_mod_cast hneg
  exact farkas_infeasible_nonneg yQ AQ bQ x hx hAx hdual_cols hdual_rhs

/-- **Deck–Farkas Elimination Bridge:**
Connects `derivative_charpoly_eq_sum_vertex_deletions S` (`Spectral.lean`) on an actual integer
matrix `S : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ` directly to a verified `Certs.checkCertZ`
certificate: any realization `S` whose scaled/shifted derivative polynomial
`φ(S.charpoly.derivative) * C c` lies in `G * polyOfDescList rhs` while every vertex-deletion
`φ(P_{S \ u}) * C c` factors as `G * polyOfDescList col` (`col ∈ cols`, `G ≠ 0`) yields `False`. -/
theorem charpoly_eliminated_of_deck_farkas {m : ℕ} (S : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ)
    (φ : ℤ[X] →+* ℚ[X]) (G : ℚ[X]) (hG : G ≠ 0) (c : ℚ)
    {rhs y : List ℤ} {cols : List (List ℤ)}
    (hchk : Certs.checkCertZ rhs y cols = true)
    (hrhs : φ S.charpoly.derivative * C c = G * polyOfDescList rhs)
    (hcols : ∀ u : Fin (m + 1), ∃ col ∈ cols, col.length = rhs.length ∧
      φ (S.submatrix u.succAbove u.succAbove).charpoly * C c = G * polyOfDescList col) :
    False := by
  choose col hcol_mem hcol_len hcol_eq using hcols
  have hderiv := derivative_charpoly_eq_sum_vertex_deletions S
  have hsum_poly : G * polyOfDescList rhs = G * ∑ u : Fin (m + 1), polyOfDescList (col u) := by
    calc
      G * polyOfDescList rhs = φ S.charpoly.derivative * C c := hrhs.symm
      _ = φ (∑ u : Fin (m + 1), (S.submatrix u.succAbove u.succAbove).charpoly) * C c := by
            rw [hderiv]
      _ = (∑ u : Fin (m + 1), φ (S.submatrix u.succAbove u.succAbove).charpoly) * C c := by
            rw [map_sum]
      _ = ∑ u : Fin (m + 1), φ (S.submatrix u.succAbove u.succAbove).charpoly * C c :=
            Finset.sum_mul _ _ _
      _ = ∑ u : Fin (m + 1), G * polyOfDescList (col u) :=
            Finset.sum_congr rfl fun u _ => hcol_eq u
      _ = G * ∑ u : Fin (m + 1), polyOfDescList (col u) := (Finset.mul_sum _ _ _).symm
  have hpoly_eq : polyOfDescList rhs = ∑ u : Fin (m + 1), polyOfDescList (col u) :=
    mul_left_cancel₀ hG hsum_poly
  have hcoeff : ∀ i : Fin rhs.length,
      (∑ u : Fin (m + 1), (1 : ℚ) * ((col u).getD i.1 0 : ℚ)) = (rhs[i.1] : ℚ) := fun i => by
    have hc := congrArg (fun P : ℚ[X] => Polynomial.lcoeff ℚ (rhs.length - 1 - i.1) P) hpoly_eq
    simp only [Polynomial.lcoeff_apply, polyOfDescList_coeff rhs i, map_sum] at hc
    rw [hc]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hi_u : i.1 < (col u).length := by rw [hcol_len u]; exact i.2
    have hcu := polyOfDescList_coeff (col u) ⟨i.1, hi_u⟩
    rw [show rhs.length - 1 - i.1 = (col u).length - 1 - i.1 by rw [hcol_len u]]
    rw [one_mul, hcu, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_u]
    rfl
  exact checkCertZ_sound hchk (fun _ => (1 : ℚ)) (fun _ => by norm_num) col hcol_mem hcoeff

end DeckFarkasBridge

section All147Certs

/-- **All `147` Stage-2 `1-vertex_farkas` Certificates Verified in Pure Lean Kernel:**
Aggregates `Certs19_74A_all_ok`, `Certs19_74B_all_ok`, and `Certs19_74C_all_ok`
(covering all `147` Stage-2 `1-vertex_farkas` candidates from `phase2_19_74.json`,
proved purely with `by decide`, zero `native_decide`). -/
theorem certs19_74_all_147_verified :
    Certs.Certs19_74A_spec ∧
    Certs.Certs19_74B_spec ∧
    Certs.Certs19_74C_spec ∧
    (Certs.Certs19_74A_indices.length + Certs.Certs19_74B_indices.length +
      Certs.Certs19_74C_indices.length = 147) ∧
    (∀ idx ∈ Certs.Certs19_74A_indices ++ Certs.Certs19_74B_indices ++ Certs.Certs19_74C_indices,
      idx < 169) := by
  have hlenA : Certs.Certs19_74A_indices.length = 49 := by decide
  have hlenB : Certs.Certs19_74B_indices.length = 49 := by decide
  have hlenC : Certs.Certs19_74C_indices.length = 49 := by decide
  have haltA : Certs.Certs19_74A_indices.all (· < 169) = true := by decide
  have haltB : Certs.Certs19_74B_indices.all (· < 169) = true := by decide
  have haltC : Certs.Certs19_74C_indices.all (· < 169) = true := by decide
  refine ⟨Certs.Certs19_74A_all_ok, Certs.Certs19_74B_all_ok, Certs.Certs19_74C_all_ok,
    by omega, fun idx hmem => ?_⟩
  simp only [List.mem_append] at hmem
  rcases hmem with (hA | hB) | hC
  · simpa using (List.all_eq_true.mp haltA) idx hA
  · simpa using (List.all_eq_true.mp haltB) idx hB
  · simpa using (List.all_eq_true.mp haltC) idx hC

end All147Certs

end EquiangularLines

end
