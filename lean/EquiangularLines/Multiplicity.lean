module

public import EquiangularLines.TwoAdic
public import Mathlib.Analysis.MeanInequalities

/-!
# GSY21 Multiplicity Forcing and Shifted 2-Adic Cofactor Congruences

This module formalizes Sections 3 and 4.3 of `reports/algebraist.md`:
1. **Cofactor 2-adic divisibility (`even_order_cofactor_two_pow_dvd`,
   `cofactor_comp_two_mul_add_odd_even`, `cofactor_comp_two_mul_add_odd_odd`):**
   Transferring `2 ^ n ∣ χ_S(2z - 1)` (even `n`, Proposition 7.3) and
   `2 ^ (d - 1) ∣ Q(2z - 1)` (odd `n`) to `Q(2w + κ)` for any odd integer `κ`.
2. **Corollary 4.3 (`odd_order_cofactor_two_adic_congruence`):**
   Exact mod-4 square-congruence connecting the cofactor quotient `F` to `odd_order_two_adic_congruence`.
3. **Trace-difference identity & GSY21 multiplicity forcing (`seidel_cofactor_trace_diff_eq`,
   `gsy_multiplicity_bound_even`, `gsy_multiplicity_bound_odd`):**
   Using real-root splitting of `S.charpoly` and AM-GM on `(r - κ)^2`, proves:
   - `4 * η ≤ T(κ)` for even `n`,
   - `η ^ η * 4 ^ (η - 1) ≤ T(κ) ^ η` for odd `n`,
   where `η = d - mult_κ(Q)` and `T(κ) = n(n - 1) - 25(n - d) - 10κ(n - d) + dκ^2`.
4. **Concrete Phase 2 multiplicity specializations:**
   - `(18, 59)` (`κ = 11`): multiplicity `≥ 1`
   - `(19, 74)` (`κ = 15`): multiplicity `≥ 6`
   - `(17, 49)` (`κ = 9`): multiplicity `≥ 4`
   - `(18, 60)` (`κ = 11`): multiplicity `≥ 6`
-/

@[expose] public section

open Matrix Polynomial
open scoped BigOperators

namespace EquiangularLines

section TwoAdicTransfer

private lemma monic_dvd_mul_pow_two_aux {m : ℕ} {M R : ℤ[X]} (hM : M.Monic)
    (hdvd : C ((2 : ℤ) ^ m) ∣ M * R) :
    C ((2 : ℤ) ^ m) ∣ R := by
  induction m generalizing R with
  | zero => simp
  | @succ m ih =>
    have h2 : C (2 : ℤ) ∣ M * R :=
      dvd_trans (by rw [pow_succ', C_mul]; exact dvd_mul_right _ _) hdvd
    have hmap : (M * R).map (Int.castRingHom (ZMod 2)) = 0 := by
      rcases h2 with ⟨T, hT⟩
      rw [hT, Polynomial.map_mul, Polynomial.map_C]
      have h0 : (Int.castRingHom (ZMod 2)) 2 = 0 := rfl
      rw [h0, map_zero, zero_mul]
    rw [Polynomial.map_mul] at hmap
    have hR_zero : R.map (Int.castRingHom (ZMod 2)) = 0 := by
      have hM_monic : (M.map (Int.castRingHom (ZMod 2))).Monic :=
        hM.map (Int.castRingHom (ZMod 2))
      have hlead : (R.map (Int.castRingHom (ZMod 2))).leadingCoeff = 0 := by
        rw [← Polynomial.leadingCoeff_mul_monic hM_monic, mul_comm, hmap,
          Polynomial.leadingCoeff_zero]
      exact Polynomial.leadingCoeff_eq_zero.mp hlead
    have h2R : C (2 : ℤ) ∣ R := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro j
      change ((2 : ℕ) : ℤ) ∣ R.coeff j
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have hj := congrArg (fun p : (ZMod 2)[X] => p.coeff j) hR_zero
      simpa [Polynomial.coeff_map] using hj
    rcases h2R with ⟨R', rfl⟩
    have hdvd' : C ((2 : ℤ) ^ m) ∣ M * R' := by
      rcases hdvd with ⟨T, hT⟩
      have hT' : C (2 : ℤ) * (M * R') = C (2 : ℤ) * (C ((2 : ℤ) ^ m) * T) := by
        calc
          C (2 : ℤ) * (M * R') = M * (C 2 * R') := by ring
          _ = C ((2 : ℤ) ^ (m + 1)) * T := hT
          _ = C (2 : ℤ) * (C ((2 : ℤ) ^ m) * T) := by rw [pow_succ', C_mul]; ring
      have hC2ne : (C (2 : ℤ) : ℤ[X]) ≠ 0 := by simp
      exact ⟨T, mul_left_cancel₀ hC2ne hT'⟩
    have hR' := ih hdvd'
    rw [pow_succ', C_mul]
    exact mul_dvd_mul_left _ hR'

private lemma charpoly_comp_shift_factor {n d : ℕ} {S : Matrix (Fin n) (Fin n) ℤ}
    {Q : ℤ[X]} (hQ : S.charpoly = (X + C (5 : ℤ)) ^ (n - d) * Q) :
    S.charpoly.comp (C 2 * X - 1) =
      C ((2 : ℤ) ^ (n - d)) * ((X + C (2 : ℤ)) ^ (n - d) * Q.comp (C 2 * X - 1)) := by
  rw [hQ, mul_comp, pow_comp, add_comp, X_comp, C_comp]
  have h5 : (C (2 : ℤ) * X - 1 + C 5 : ℤ[X]) = C 2 * X + C 4 := by
    rw [← Polynomial.C_1, sub_add_eq_add_sub, add_sub_assoc, ← map_sub]
    norm_num
  have h4 : (C (4 : ℤ) : ℤ[X]) = C 2 * C 2 := by
    rw [← map_mul]
    norm_num
  have hlin : (C (2 : ℤ) * X - 1 + C 5 : ℤ[X]) = C 2 * (X + C 2) := by
    rw [h5, h4, mul_add]
  rw [hlin, mul_pow, ← C_pow]
  ring

/-- For even `n` and `d ≤ n`, `C (2 ^ d)` divides `Q.comp (C 2 * X - 1)` in `ℤ[X]`. -/
theorem even_order_cofactor_two_pow_dvd {n d : ℕ} (hn : Even n) (hdn : d ≤ n)
    {S : Matrix (Fin n) (Fin n) ℤ} (hS : IsSeidelMatrix S)
    {Q : ℤ[X]} (hQ : S.charpoly = (X + C (5 : ℤ)) ^ (n - d) * Q) :
    C ((2 : ℤ) ^ d) ∣ Q.comp (C 2 * X - 1) := by
  have hdvdS := even_order_two_pow_dvd_charpoly hn hS
  rw [charpoly_comp_shift_factor hQ] at hdvdS
  have hC_dvd : C ((2 : ℤ) ^ d) ∣ (X + C (2 : ℤ)) ^ (n - d) * Q.comp (C 2 * X - 1) := by
    rcases hdvdS with ⟨T, hT⟩
    have hsplit : (2 : ℤ) ^ n = (2 : ℤ) ^ (n - d) * (2 : ℤ) ^ d := by
      rw [← pow_add]
      congr 1
      omega
    have hT' : C ((2 : ℤ) ^ (n - d)) * ((X + C 2) ^ (n - d) * Q.comp (C 2 * X - 1)) =
        C ((2 : ℤ) ^ (n - d)) * (C ((2 : ℤ) ^ d) * T) := by
      calc
        C ((2 : ℤ) ^ (n - d)) * ((X + C 2) ^ (n - d) * Q.comp (C 2 * X - 1))
            = C ((2 : ℤ) ^ n) * T := hT
        _ = C ((2 : ℤ) ^ (n - d)) * (C ((2 : ℤ) ^ d) * T) := by
            rw [hsplit, C_mul, mul_assoc]
    have hne : C ((2 : ℤ) ^ (n - d)) ≠ (0 : ℤ[X]) := by simp
    exact ⟨T, mul_left_cancel₀ hne hT'⟩
  exact monic_dvd_mul_pow_two_aux ((monic_X_add_C (2 : ℤ)).pow (n - d)) hC_dvd

private lemma comp_two_mul_add_odd_eq (Q : ℤ[X]) {κ : ℤ} (hκ : Odd κ) :
    Q.comp (C 2 * X + C κ) =
      (Q.comp (C 2 * X - 1)).comp (X + C ((κ + 1) / 2)) := by
  rw [Polynomial.comp_assoc, sub_comp, mul_comp, C_comp, X_comp, one_comp]
  congr 1
  rcases hκ with ⟨t, rfl⟩
  have ht : (2 * t + 1 + 1) / 2 = t + 1 := by omega
  rw [ht]
  have h1 : (C (2 : ℤ) * (X + C (t + 1)) - 1 : ℤ[X]) =
      C 2 * X + (C 2 * C (t + 1) - 1) := by ring
  rw [h1]
  congr 1
  rw [← Polynomial.C_1, ← map_mul, ← map_sub]
  congr 1
  ring

/-- For even `n`, `d ≤ n`, and odd `κ`, `C (2 ^ d)` divides `Q.comp (C 2 * X + C κ)`. -/
theorem cofactor_comp_two_mul_add_odd_even {n d : ℕ} (hn : Even n) (hdn : d ≤ n)
    {S : Matrix (Fin n) (Fin n) ℤ} (hS : IsSeidelMatrix S)
    {Q : ℤ[X]} (hQ : S.charpoly = (X + C (5 : ℤ)) ^ (n - d) * Q)
    {κ : ℤ} (hκ : Odd κ) :
    C ((2 : ℤ) ^ d) ∣ Q.comp (C 2 * X + C κ) := by
  rcases even_order_cofactor_two_pow_dvd hn hdn hS hQ with ⟨F, hF⟩
  refine ⟨F.comp (X + C ((κ + 1) / 2)), ?_⟩
  rw [comp_two_mul_add_odd_eq Q hκ, hF, mul_comp, C_comp]

/-- For odd `n`, `1 ≤ d ≤ n`, and odd `κ`, `C (2 ^ (d - 1))` divides `Q.comp (C 2 * X + C κ)`. -/
theorem cofactor_comp_two_mul_add_odd_odd {n d : ℕ} (hd1 : 1 ≤ d) (hdn : d ≤ n)
    {S : Matrix (Fin n) (Fin n) ℤ} (hS : IsSeidelMatrix S)
    {Q : ℤ[X]} (hQ : S.charpoly = (X + C (5 : ℤ)) ^ (n - d) * Q)
    {κ : ℤ} (hκ : Odd κ) :
    C ((2 : ℤ) ^ (d - 1)) ∣ Q.comp (C 2 * X + C κ) := by
  rcases (two_pow_factor_dvd_cofactor_comp hd1 hdn hS hQ).1 with ⟨F, hF⟩
  refine ⟨F.comp (X + C ((κ + 1) / 2)), ?_⟩
  rw [comp_two_mul_add_odd_eq Q hκ, hF, mul_comp, C_comp]

/-- **Corollary 4.3 (Odd-order 2-adic cofactor congruence):** For odd `n` and `1 ≤ d ≤ n`,
if `S.charpoly = (X + C 5)^(n - d) * Q`, then letting `F` be `2^(-(d-1)) Q(2X - 1)`,
`(X + C 2)^(n - d) * F = (C 2 * X - C n) * Q₀ ^ 2 + C 4 * R` in `ℤ[X]` with `Q₀` monic of
degree `(n - 1) / 2`. -/
theorem odd_order_cofactor_two_adic_congruence {n d : ℕ} (hn : Odd n) (hd1 : 1 ≤ d) (hdn : d ≤ n)
    {S : Matrix (Fin n) (Fin n) ℤ} (hS : IsSeidelMatrix S)
    {Q : ℤ[X]} (hQ : S.charpoly = (X + C (5 : ℤ)) ^ (n - d) * Q) :
    ∃ F Q₀ R : ℤ[X],
      Q.comp (C 2 * X - 1) = C ((2 : ℤ) ^ (d - 1)) * F ∧
      Q₀.Monic ∧
      Q₀.natDegree = (n - 1) / 2 ∧
      (X + C (2 : ℤ)) ^ (n - d) * F = (C 2 * X - C (n : ℤ)) * Q₀ ^ 2 + C 4 * R := by
  obtain ⟨F, hF⟩ := (two_pow_factor_dvd_cofactor_comp hd1 hdn hS hQ).1
  obtain ⟨Q₀, R, hQ₀_mon, hQ₀_deg, hcong⟩ := odd_order_two_adic_congruence hn hS
  refine ⟨F, Q₀, R, hF, hQ₀_mon, hQ₀_deg, ?_⟩
  have hcomp := charpoly_comp_shift_factor hQ
  rw [hF] at hcomp
  have hpow : C ((2 : ℤ) ^ (n - d)) * ((X + C (2 : ℤ)) ^ (n - d) * (C ((2 : ℤ) ^ (d - 1)) * F)) =
      C ((2 : ℤ) ^ (n - 1)) * ((X + C (2 : ℤ)) ^ (n - d) * F) := by
    have hexp : (2 : ℤ) ^ (n - 1) = (2 : ℤ) ^ (n - d) * (2 : ℤ) ^ (d - 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hexp, C_mul]
    ring
  rw [hcomp, hpow] at hcong
  have hne : C ((2 : ℤ) ^ (n - 1)) ≠ (0 : ℤ[X]) := by simp
  exact mul_left_cancel₀ hne hcong

end TwoAdicTransfer

section GSYMultiplicity

private lemma seidel_isHermitian_real {n : ℕ} {S : Matrix (Fin n) (Fin n) ℤ}
    (hS : IsSeidelMatrix S) :
    (S.map (Int.castRingHom ℝ)).IsHermitian := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, star_trivial]
  exact congrArg (fun M : Matrix (Fin n) (Fin n) ℤ => (M i j : ℝ)) hS.1

private lemma hermitian_charpoly_prod_real {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
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

private lemma hermitian_trace_eq_sum_eigs {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) : A.trace = ∑ i : Fin n, hA.eigenvalues i := by
  have hspec := hA.spectral_theorem
  have hAeq :
      A = (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
        Matrix.diagonal hA.eigenvalues *
        (star hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) := by
    simpa [RCLike.ofReal_real_eq_id] using hspec
  have hU :
      (star hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
        (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    Unitary.coe_star_mul_self hA.eigenvectorUnitary
  conv_lhs => rw [hAeq]
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul, Matrix.trace_diagonal]

private lemma hermitian_trace_sq_eq_sum_eigs_sq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) : (A * A).trace = ∑ i : Fin n, hA.eigenvalues i ^ 2 := by
  have hspec := hA.spectral_theorem
  have hAeq :
      A = (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
        Matrix.diagonal hA.eigenvalues *
        (star hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) := by
    simpa [RCLike.ofReal_real_eq_id] using hspec
  have hU1 :
      (star hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
        (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    Unitary.coe_star_mul_self hA.eigenvectorUnitary
  let U : Matrix (Fin n) (Fin n) ℝ := hA.eigenvectorUnitary
  let Ustar : Matrix (Fin n) (Fin n) ℝ := star hA.eigenvectorUnitary
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal hA.eigenvalues
  have hAA : A * A = U * (D * D) * Ustar := by
    rw [hAeq]
    calc
      (U * D * Ustar) * (U * D * Ustar)
          = U * D * (Ustar * U) * D * Ustar := by simp only [Matrix.mul_assoc]
      _ = U * D * 1 * D * Ustar := by rw [hU1]
      _ = U * (D * D) * Ustar := by simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [hAA, Matrix.trace_mul_cycle, hU1, Matrix.one_mul, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal]
  simp [sq]

private lemma splits_of_seidel_factor {n d : ℕ} {S : Matrix (Fin n) (Fin n) ℤ}
    (hS : IsSeidelMatrix S) {Q : ℤ[X]} (hQ : S.charpoly = (X + C (5 : ℤ)) ^ (n - d) * Q) :
    (Q.map (Int.castRingHom ℝ)).Splits := by
  let S_R : Matrix (Fin n) (Fin n) ℝ := S.map (Int.castRingHom ℝ)
  have hHerm : S_R.IsHermitian := seidel_isHermitian_real hS
  have hS_prod : S_R.charpoly = ∏ i : Fin n, (X - C (hHerm.eigenvalues i)) :=
    hermitian_charpoly_prod_real hHerm
  have hS_splits : S_R.charpoly.Splits := by
    rw [hS_prod]
    exact Splits.prod (fun i _ => Splits.X_sub_C _)
  have hS_ne : S_R.charpoly ≠ 0 := by
    rw [hS_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => X_sub_C_ne_zero _)
  have hdvd : Q.map (Int.castRingHom ℝ) ∣ S_R.charpoly := by
    have hmap := congrArg (Polynomial.map (Int.castRingHom ℝ)) hQ
    rw [← Matrix.charpoly_map S (Int.castRingHom ℝ), Polynomial.map_mul] at hmap
    exact ⟨_, by rw [hmap, mul_comm]⟩
  exact hS_splits.of_dvd hS_ne hdvd

private lemma roots_prod_X_sub_C_fin {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
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

/-- **Trace-difference identity:** For `S.charpoly = (X + C 5)^(n - d) * Q`, the sum of `(r - κ)^2`
over all real roots `r` of `Q` (with multiplicity) equals
`T(κ) = n(n - 1) - 25(n - d) - 10κ(n - d) + dκ^2`. -/
theorem seidel_cofactor_trace_diff_eq {n d : ℕ} (hdn : d ≤ n)
    {S : Matrix (Fin n) (Fin n) ℤ} (hS : IsSeidelMatrix S)
    {Q : ℤ[X]} (hQ : S.charpoly = (X + C (5 : ℤ)) ^ (n - d) * Q) (κ : ℤ) :
    ((Q.map (Int.castRingHom ℝ)).roots.map (fun r => (r - (κ : ℝ)) ^ 2)).sum =
      ((n : ℝ) * ((n : ℝ) - 1) - 25 * ((n : ℝ) - (d : ℝ)) -
        10 * (κ : ℝ) * ((n : ℝ) - (d : ℝ)) + (d : ℝ) * (κ : ℝ) ^ 2) := by
  let S_R : Matrix (Fin n) (Fin n) ℝ := S.map (Int.castRingHom ℝ)
  have hHerm : S_R.IsHermitian := seidel_isHermitian_real hS
  have hS_prod : S_R.charpoly = ∏ i : Fin n, (X - C (hHerm.eigenvalues i)) :=
    hermitian_charpoly_prod_real hHerm
  have hSR : S_R.charpoly = (X - C (-5 : ℝ)) ^ (n - d) * Q.map (Int.castRingHom ℝ) := by
    have hm := congrArg (Polynomial.map (Int.castRingHom ℝ)) hQ
    rw [← Matrix.charpoly_map S (Int.castRingHom ℝ), Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_add, map_X, Polynomial.map_C] at hm
    simpa [S_R, sub_neg_eq_add] using hm
  have hroots : S_R.charpoly.roots = Finset.univ.val.map hHerm.eigenvalues := by
    rw [hS_prod, roots_prod_X_sub_C_fin]
  have hroots_split :
      S_R.charpoly.roots =
        Multiset.replicate (n - d) (-5 : ℝ) + (Q.map (Int.castRingHom ℝ)).roots := by
    have hS_ne : S_R.charpoly ≠ 0 := by
      rw [hS_prod]; exact Finset.prod_ne_zero_iff.mpr (fun i _ => X_sub_C_ne_zero _)
    have hmul_ne : (X - C (-5 : ℝ)) ^ (n - d) * Q.map (Int.castRingHom ℝ) ≠ 0 := hSR ▸ hS_ne
    rw [hSR, roots_mul hmul_ne, roots_pow, roots_X_sub_C, Multiset.nsmul_singleton]
  have hsum_all :
      (∑ i : Fin n, (hHerm.eigenvalues i - (κ : ℝ)) ^ 2) =
        ((n - d : ℕ) : ℝ) * ((-5 : ℝ) - (κ : ℝ)) ^ 2 +
          ((Q.map (Int.castRingHom ℝ)).roots.map (fun r => (r - (κ : ℝ)) ^ 2)).sum := by
    have hm := congrArg (fun ms : Multiset ℝ => (ms.map (fun r => (r - (κ : ℝ)) ^ 2)).sum)
      (hroots.symm.trans hroots_split)
    simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_replicate, Multiset.sum_replicate,
      nsmul_eq_mul, Multiset.map_map, Function.comp_def] at hm
    change (Finset.univ.val.map (fun i : Fin n => (hHerm.eigenvalues i - (κ : ℝ)) ^ 2)).sum = _ at hm
    simpa [Finset.sum] using hm
  have htr1 : ∑ i : Fin n, hHerm.eigenvalues i = 0 := by
    rw [← hermitian_trace_eq_sum_eigs hHerm]
    have htrS : S.trace = 0 := hS.trace_eq_zero
    simpa [S_R, Matrix.trace, Matrix.diag_apply, Matrix.map_apply, ← map_sum] using
      congrArg (Int.cast : ℤ → ℝ) htrS
  have htr2 : ∑ i : Fin n, hHerm.eigenvalues i ^ 2 = (n : ℝ) * ((n : ℝ) - 1) := by
    rw [← hermitian_trace_sq_eq_sum_eigs_sq hHerm]
    have htrS2 : (S * S).trace = (n : ℤ) * ((n : ℤ) - 1) := hS.trace_sq
    have hmap : (S_R * S_R).trace = ((S * S).trace : ℝ) := by
      rw [show S_R * S_R = (S * S).map (Int.castRingHom ℝ) by rw [Matrix.map_mul]]
      simp [Matrix.trace, Matrix.diag_apply, Matrix.map_apply]
    rw [hmap, htrS2]
    push_cast
    ring
  have hexpand : ∑ i : Fin n, (hHerm.eigenvalues i - (κ : ℝ)) ^ 2 =
      (n : ℝ) * ((n : ℝ) - 1) + (n : ℝ) * (κ : ℝ) ^ 2 := by
    have hsub : ∀ i : Fin n,
        (hHerm.eigenvalues i - (κ : ℝ)) ^ 2 =
          hHerm.eigenvalues i ^ 2 - 2 * (κ : ℝ) * hHerm.eigenvalues i + (κ : ℝ) ^ 2 := fun i => by ring
    simp_rw [hsub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [htr2, htr1]
    ring
  have hnd : ((n - d : ℕ) : ℝ) = (n : ℝ) - (d : ℝ) := by
    rw [Nat.cast_sub hdn]
  rw [hexpand, hnd] at hsum_all
  linarith

private lemma am_gm_prod_pow {m : ℕ} (hm : 1 ≤ m) {z : Fin m → ℝ} (hz : ∀ i, 0 ≤ z i) :
    ((m : ℝ) ^ m) * (∏ i : Fin m, z i) ≤ (∑ i : Fin m, z i) ^ m := by
  let s : Finset (Fin m) := Finset.univ
  let w : Fin m → ℝ := fun _ => 1
  have hw : ∀ i ∈ s, 0 ≤ w i := fun _ _ => zero_le_one
  have hsum_w : ∑ i ∈ s, w i = (m : ℝ) := by simp [s, w]
  have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
  have hgm := Real.geom_mean_le_arith_mean s w z hw (by rw [hsum_w]; exact hm_pos) (fun i _ => hz i)
  rw [hsum_w] at hgm
  have hprod_nonneg : 0 ≤ ∏ i ∈ s, z i := Finset.prod_nonneg (fun i _ => hz i)
  have hLHS : (∏ i ∈ s, z i ^ w i) ^ (m : ℝ)⁻¹ = (∏ i : Fin m, z i) ^ (m : ℝ)⁻¹ := by
    congr 1
    exact Finset.prod_congr rfl fun i _ => Real.rpow_one _
  have hRHS : (∑ i ∈ s, w i * z i) / (m : ℝ) = (∑ i : Fin m, z i) / (m : ℝ) := by
    simp [s, w]
  rw [hLHS, hRHS] at hgm
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hprod_nonneg _) hgm m
  have hlhs_pow : ((∏ i : Fin m, z i) ^ (m : ℝ)⁻¹) ^ m = ∏ i : Fin m, z i := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hprod_nonneg, inv_mul_cancel₀ hm_pos.ne',
      Real.rpow_one]
  rw [hlhs_pow, div_pow] at hpow
  have hm_pow_pos : (0 : ℝ) < (m : ℝ) ^ m := pow_pos hm_pos m
  have hmul := (le_div_iff₀ hm_pow_pos).mp hpow
  linarith

private lemma gsy_multiplicity_core {n d γ : ℕ} (hdn : d ≤ n)
    {S : Matrix (Fin n) (Fin n) ℤ} (hS : IsSeidelMatrix S)
    {Q : ℤ[X]} (hQ_mon : Q.Monic) (hQ_deg : Q.natDegree = d)
    (hQ : S.charpoly = (X + C (5 : ℤ)) ^ (n - d) * Q)
    {κ : ℤ} (hγ : γ ≤ 1)
    (hdvd2 : C ((2 : ℤ) ^ (d - γ)) ∣ Q.comp (C 2 * X + C κ))
    (hγ_le_d : γ ≤ d) :
    let m := Q.rootMultiplicity κ
    let η := d - m
    1 ≤ η →
      ((η : ℝ) ^ η * (4 : ℝ) ^ (η - γ)) ≤
        ((n : ℝ) * ((n : ℝ) - 1) - 25 * ((n : ℝ) - (d : ℝ)) -
          10 * (κ : ℝ) * ((n : ℝ) - (d : ℝ)) + (d : ℝ) * (κ : ℝ) ^ 2) ^ η := by
  intro m η hη1
  have hm_le_d : m ≤ d := by
    rcases Polynomial.pow_rootMultiplicity_dvd Q κ with ⟨T, hT⟩
    have hT_mon : T.Monic := by
      have h1 := hQ_mon; rw [hT] at h1
      exact Polynomial.Monic.of_mul_monic_left ((monic_X_sub_C κ).pow m) h1
    have hdeg := congrArg Polynomial.natDegree hT
    rw [hQ_deg, ((monic_X_sub_C κ).pow m).natDegree_mul' hT_mon.ne_zero,
      natDegree_pow, natDegree_X_sub_C, mul_one] at hdeg
    omega
  have hm_dvd : (X - C κ) ^ m ∣ Q := Polynomial.pow_rootMultiplicity_dvd Q κ
  rcases hm_dvd with ⟨Q_rem, hQ_rem⟩
  have hQ_rem_mon : Q_rem.Monic := by
    have hm1 : Q_rem.Monic := by
      have h1 := hQ_mon
      rw [hQ_rem] at h1
      exact Polynomial.Monic.of_mul_monic_left ((monic_X_sub_C κ).pow m) h1
    exact hm1
  have hQ_rem_deg : Q_rem.natDegree = η := by
    have hdeg := congrArg Polynomial.natDegree hQ_rem
    rw [hQ_deg, ((monic_X_sub_C κ).pow m).natDegree_mul' hQ_rem_mon.ne_zero,
      natDegree_pow, natDegree_X_sub_C, mul_one] at hdeg
    omega
  have hQ_rem_ne_root : Q_rem.eval κ ≠ 0 := by
    intro hroot
    have hd1 : X - C κ ∣ Q_rem := Polynomial.dvd_iff_isRoot.mpr hroot
    have hm_succ : (X - C κ) ^ (m + 1) ∣ Q := by
      rcases hd1 with ⟨T, hT⟩
      refine ⟨T, ?_⟩
      rw [hQ_rem, hT, pow_succ]
      ring
    have hle := (Polynomial.le_rootMultiplicity_iff hQ_mon.ne_zero).mpr hm_succ
    change m + 1 ≤ m at hle
    omega
  have hcomp_rem :
      Q.comp (C 2 * X + C κ) =
        C ((2 : ℤ) ^ m) * (X ^ m * Q_rem.comp (C 2 * X + C κ)) := by
    rw [hQ_rem, mul_comp, pow_comp, sub_comp, X_comp, C_comp]
    have hsub : (C (2 : ℤ) * X + C κ - C κ : ℤ[X]) = C 2 * X := by ring
    rw [hsub, mul_pow, ← C_pow]
    ring
  have hdvd_rem : C ((2 : ℤ) ^ (η - γ)) ∣ Q_rem.comp (C 2 * X + C κ) := by
    rw [hcomp_rem] at hdvd2
    rcases hdvd2 with ⟨G₀, hG₀⟩
    have hexp : d - γ = m + (η - γ) := by omega
    rw [hexp, pow_add, C_mul] at hG₀
    have hC2m : C ((2 : ℤ) ^ m) ≠ (0 : ℤ[X]) := by simp
    have hcancel : X ^ m * Q_rem.comp (C 2 * X + C κ) = C ((2 : ℤ) ^ (η - γ)) * G₀ :=
      mul_left_cancel₀ hC2m (by rw [hG₀]; ring)
    have hXm_mon : (X ^ m : ℤ[X]).Monic := monic_X_pow m
    exact monic_dvd_mul_pow_two_aux hXm_mon ⟨G₀, hcancel⟩
  rcases hdvd_rem with ⟨G_int, hG_int⟩
  let g0 : ℤ := G_int.eval (0 : ℤ)
  have hG0_ne : g0 ≠ 0 := by
    intro h0
    have hev := congrArg (fun p : ℤ[X] => p.eval (0 : ℤ)) hG_int
    simp only [eval_comp, eval_add, eval_mul, eval_C, eval_X, mul_zero, zero_add] at hev
    change Q_rem.eval κ = (2 : ℤ) ^ (η - γ) * g0 at hev
    rw [h0, mul_zero] at hev
    exact hQ_rem_ne_root hev
  have hG0_abs_ge : (1 : ℝ) ≤ |(g0 : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |g0| := Int.one_le_abs hG0_ne
    exact_mod_cast h1
  have hG_real_split : (Q_rem.map (Int.castRingHom ℝ)).Splits := by
    have hQs := splits_of_seidel_factor hS hQ
    have hmap := congrArg (Polynomial.map (Int.castRingHom ℝ)) hQ_rem
    rw [Polynomial.map_mul] at hmap
    have hQne : Q.map (Int.castRingHom ℝ) ≠ 0 :=
      (hQ_mon.map (Int.castRingHom ℝ)).ne_zero
    exact hQs.of_dvd hQne ⟨_, by rw [hmap, mul_comm]⟩
  have hcard_roots : (Q_rem.map (Int.castRingHom ℝ)).roots.card = η := by
    rw [hG_real_split.natDegree_eq_card_roots.symm,
      Polynomial.natDegree_map_eq_of_injective Int.cast_injective, hQ_rem_deg]
  have hG_eval0_real :
      |(g0 : ℝ)| * (2 : ℝ) ^ (η - γ) =
        ((Q_rem.map (Int.castRingHom ℝ)).roots.map (fun r => |r - (κ : ℝ)|)).prod := by
    have hprod_roots : Q_rem.map (Int.castRingHom ℝ) =
        ((Q_rem.map (Int.castRingHom ℝ)).roots.map (fun r => X - C r)).prod := by
      have heq := hG_real_split.eq_prod_roots
      rw [(hQ_rem_mon.map (Int.castRingHom ℝ)).leadingCoeff, C_1, one_mul] at heq
      exact heq
    have heval := congrArg (fun p : ℤ[X] => (p.map (Int.castRingHom ℝ)).eval (0 : ℝ)) hG_int
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.map_comp, Polynomial.map_add, map_X, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_X, mul_zero, zero_add] at heval
    have hmap_eval : (Q_rem.map (Int.castRingHom ℝ)).eval (κ : ℝ) =
        ((Q_rem.map (Int.castRingHom ℝ)).roots.map (fun r => (κ : ℝ) - r)).prod := by
      rw [hprod_roots, eval_multiset_prod, Multiset.map_map]
      simp
    have hev2 : ((Int.castRingHom ℝ) ((2 : ℤ) ^ (η - γ))) = (2 : ℝ) ^ (η - γ) := by
      norm_cast
    have hevk : ((Int.castRingHom ℝ) κ) = (κ : ℝ) := rfl
    have hG_eval : (G_int.map (Int.castRingHom ℝ)).eval (0 : ℝ) = (g0 : ℝ) := by
      rw [Polynomial.eval_map, Polynomial.eval₂_at_zero]
      exact congrArg (Int.cast : ℤ → ℝ) (Polynomial.coeff_zero_eq_eval_zero G_int)
    rw [hevk] at heval
    rw [hG_eval, hev2, hmap_eval] at heval
    have h_abs_prod : ∀ ms : Multiset ℝ, |ms.prod| = (ms.map abs).prod := fun ms =>
      Multiset.induction_on ms (by simp) (fun a s ih => by simp [abs_mul, ih])
    have habs := congrArg abs heval.symm
    rw [abs_mul, abs_of_nonneg (by positivity), h_abs_prod] at habs
    simp only [Multiset.map_map, Function.comp_def, abs_sub_comm] at habs
    simpa [mul_comm] using habs
  let rs := (Q_rem.map (Int.castRingHom ℝ)).roots
  have hrs_card : rs.card = η := hcard_roots
  let e : Fin η ≃ Fin rs.card := finCongr hrs_card.symm
  let rArr : Fin η → ℝ := fun i => (rs.toList)[(e i).val]' (by rw [Multiset.length_toList]; exact (e i).isLt)
  have hprod_sq :
      (∏ i : Fin η, (rArr i - (κ : ℝ)) ^ 2) =
        (4 : ℝ) ^ (η - γ) * (g0 : ℝ) ^ 2 := by
    have hlist_prod : (∏ i : Fin η, |rArr i - (κ : ℝ)|) =
        (rs.map (fun r => |r - (κ : ℝ)|)).prod := by
      have hfin : (∏ i : Fin η, |rArr i - (κ : ℝ)|) =
          ∏ j : Fin rs.card, |rs.toList[j.val]'(by rw [Multiset.length_toList]; exact j.isLt) - (κ : ℝ)| := by
        refine Fintype.prod_equiv e _ _ fun i => rfl
      rw [hfin]
      rw [← Multiset.coe_toList rs, Multiset.map_coe, Multiset.prod_coe,
        ← List.prod_ofFn]
      congr 1
      refine List.ext_get (by simp) fun i hi1 hi2 => by simp
    have hsq_eq : (∏ i : Fin η, (rArr i - (κ : ℝ)) ^ 2) =
        (∏ i : Fin η, |rArr i - (κ : ℝ)|) ^ 2 := by
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [sq_abs]
    rw [hsq_eq, hlist_prod, ← hG_eval0_real, mul_pow, ← pow_mul, mul_comm (η - γ) 2, pow_mul]
    norm_num [mul_comm]
  have h4_bound : (4 : ℝ) ^ (η - γ) ≤ ∏ i : Fin η, (rArr i - (κ : ℝ)) ^ 2 := by
    rw [hprod_sq]
    have hsq1 : (1 : ℝ) ≤ (g0 : ℝ) ^ 2 := by
      rw [← sq_abs]
      exact one_le_pow₀ hG0_abs_ge
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) (η - γ)]
  have ham := am_gm_prod_pow hη1 (z := fun i => (rArr i - (κ : ℝ)) ^ 2) (fun i => sq_nonneg _)
  have hsum_le : (∑ i : Fin η, (rArr i - (κ : ℝ)) ^ 2) ≤
      ((Q.map (Int.castRingHom ℝ)).roots.map (fun r => (r - (κ : ℝ)) ^ 2)).sum := by
    have hlist_sum : (∑ i : Fin η, (rArr i - (κ : ℝ)) ^ 2) =
        (rs.map (fun r => (r - (κ : ℝ)) ^ 2)).sum := by
      have hfin : (∑ i : Fin η, (rArr i - (κ : ℝ)) ^ 2) =
          ∑ j : Fin rs.card,
            (rs.toList[j.val]'(by rw [Multiset.length_toList]; exact j.isLt) - (κ : ℝ)) ^ 2 :=
        Fintype.sum_equiv e _ _ fun i => rfl
      rw [hfin, ← Multiset.coe_toList rs, Multiset.map_coe, Multiset.sum_coe, ← List.sum_ofFn]
      congr 1
      refine List.ext_get (by simp) fun i hi1 hi2 => by simp
    rw [hlist_sum]
    have hsub_roots : rs ≤ (Q.map (Int.castRingHom ℝ)).roots := by
      have hmap := congrArg (Polynomial.map (Int.castRingHom ℝ)) hQ_rem
      rw [Polynomial.map_mul] at hmap
      have hQne : Q.map (Int.castRingHom ℝ) ≠ 0 :=
        (hQ_mon.map (Int.castRingHom ℝ)).ne_zero
      rw [hmap, roots_mul (hmap ▸ hQne)]
      exact Multiset.le_add_left _ _
    obtain ⟨t, ht⟩ := le_iff_exists_add.mp hsub_roots
    rw [ht, Multiset.map_add, Multiset.sum_add]
    exact le_add_of_nonneg_right (Multiset.sum_nonneg fun x hx => by
      rcases Multiset.mem_map.mp hx with ⟨r, _, rfl⟩
      exact sq_nonneg _)
  rw [seidel_cofactor_trace_diff_eq hdn hS hQ κ] at hsum_le
  have hsum_pow : (∑ i : Fin η, (rArr i - (κ : ℝ)) ^ 2) ^ η ≤
      ((n : ℝ) * ((n : ℝ) - 1) - 25 * ((n : ℝ) - (d : ℝ)) -
        10 * (κ : ℝ) * ((n : ℝ) - (d : ℝ)) + (d : ℝ) * (κ : ℝ) ^ 2) ^ η :=
    pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hsum_le η
  have hleft : (η : ℝ) ^ η * (4 : ℝ) ^ (η - γ) ≤
      (η : ℝ) ^ η * ∏ i : Fin η, (rArr i - (κ : ℝ)) ^ 2 :=
    mul_le_mul_of_nonneg_left h4_bound (by positivity)
  exact hleft.trans (ham.trans hsum_pow)

/-- **GSY21 Multiplicity Forcing (Even `n`):** If `S` is a Seidel matrix of even order `n` with
`S.charpoly = (X + C 5)^(n - d) * Q` (`d ≤ n`) and `κ` is odd, then `η = d - Q.rootMultiplicity κ`
satisfies `4 * η ≤ n(n - 1) - 25(n - d) - 10κ(n - d) + dκ^2`. -/
theorem gsy_multiplicity_bound_even {n d : ℕ} (hn : Even n) (hdn : d ≤ n)
    {S : Matrix (Fin n) (Fin n) ℤ} (hS : IsSeidelMatrix S)
    {Q : ℤ[X]} (hQ_mon : Q.Monic) (hQ_deg : Q.natDegree = d)
    (hQ : S.charpoly = (X + C (5 : ℤ)) ^ (n - d) * Q)
    {κ : ℤ} (hκ : Odd κ) :
    let η := d - Q.rootMultiplicity κ
    4 * (η : ℝ) ≤
      (n : ℝ) * ((n : ℝ) - 1) - 25 * ((n : ℝ) - (d : ℝ)) -
        10 * (κ : ℝ) * ((n : ℝ) - (d : ℝ)) + (d : ℝ) * (κ : ℝ) ^ 2 := by
  intro η
  have hT_nonneg : 0 ≤
      (n : ℝ) * ((n : ℝ) - 1) - 25 * ((n : ℝ) - (d : ℝ)) -
        10 * (κ : ℝ) * ((n : ℝ) - (d : ℝ)) + (d : ℝ) * (κ : ℝ) ^ 2 := by
    rw [← seidel_cofactor_trace_diff_eq hdn hS hQ κ]
    exact Multiset.sum_nonneg fun x hx => by
      rcases Multiset.mem_map.mp hx with ⟨r, _, rfl⟩
      exact sq_nonneg _
  by_cases hη0 : η = 0
  · simp [hη0]; exact hT_nonneg
  · have hη1 : 1 ≤ η := Nat.one_le_iff_ne_zero.mpr hη0
    have hdvd2 := cofactor_comp_two_mul_add_odd_even hn hdn hS hQ hκ
    have hcore := gsy_multiplicity_core hdn hS hQ_mon hQ_deg hQ (γ := 0) (by omega)
      (by simpa using hdvd2) (Nat.zero_le d) hη1
    simp only [Nat.sub_zero] at hcore
    have h4pow : ((4 : ℝ) * (η : ℝ)) ^ η ≤
        ((n : ℝ) * ((n : ℝ) - 1) - 25 * ((n : ℝ) - (d : ℝ)) -
          10 * (κ : ℝ) * ((n : ℝ) - (d : ℝ)) + (d : ℝ) * (κ : ℝ) ^ 2) ^ η := by
      have hmul : ((4 : ℝ) * (η : ℝ)) ^ η = (η : ℝ) ^ η * (4 : ℝ) ^ η := by ring
      rw [hmul]
      exact hcore
    exact le_of_pow_le_pow_left₀ hη0 hT_nonneg h4pow

/-- **GSY21 Multiplicity Forcing (Odd `n`):** If `S` is a Seidel matrix of odd order `n` with
`S.charpoly = (X + C 5)^(n - d) * Q` (`1 ≤ d ≤ n`) and `κ` is odd, then whenever
`η = d - Q.rootMultiplicity κ ≥ 1`, we have `η ^ η * 4 ^ (η - 1) ≤ T(κ) ^ η`. -/
theorem gsy_multiplicity_bound_odd {n d : ℕ} (hd1 : 1 ≤ d) (hdn : d ≤ n)
    {S : Matrix (Fin n) (Fin n) ℤ} (hS : IsSeidelMatrix S)
    {Q : ℤ[X]} (hQ_mon : Q.Monic) (hQ_deg : Q.natDegree = d)
    (hQ : S.charpoly = (X + C (5 : ℤ)) ^ (n - d) * Q)
    {κ : ℤ} (hκ : Odd κ) (hη1 : 1 ≤ d - Q.rootMultiplicity κ) :
    let η := d - Q.rootMultiplicity κ
    (η : ℝ) ^ η * (4 : ℝ) ^ (η - 1) ≤
      ((n : ℝ) * ((n : ℝ) - 1) - 25 * ((n : ℝ) - (d : ℝ)) -
        10 * (κ : ℝ) * ((n : ℝ) - (d : ℝ)) + (d : ℝ) * (κ : ℝ) ^ 2) ^ η := by
  have hdvd2 := cofactor_comp_two_mul_add_odd_odd hd1 hdn hS hQ hκ
  exact gsy_multiplicity_core hdn hS hQ_mon hQ_deg hQ (γ := 1) le_rfl hdvd2 hd1 hη1

end GSYMultiplicity

section FrontierSpecializations

/-- For `(d, n) = (18, 59)`, `(X - C 11)` divides the degree-18 cofactor `Q` (and
`(X + C 5)^41 * (X - C 11) ∣ S.charpoly`). -/
theorem frontier_18_59_mult_11 {S : Matrix (Fin 59) (Fin 59) ℤ} (hS : IsSeidelMatrix S)
    (hPSD : (seidelGram (1 / 5 : ℝ) S).PosSemidef)
    (hrank : (seidelGram (1 / 5 : ℝ) S).rank ≤ 18) :
    ∃ Q : ℤ[X], Q.Monic ∧ Q.natDegree = 18 ∧
      S.charpoly = (X + C (5 : ℤ)) ^ 41 * Q ∧ (X - C (11 : ℤ)) ^ 1 ∣ Q := by
  obtain ⟨_, Q, hQ_mon, hQ_eq, hQ_deg⟩ := seidel_charpoly_factorization hS hPSD hrank
  have hdeg18 : Q.natDegree = 18 := hQ_deg (by omega)
  have hmult : 1 ≤ Q.rootMultiplicity (11 : ℤ) := by
    by_contra hm0
    have hm_zero : Q.rootMultiplicity (11 : ℤ) = 0 := by omega
    have hη : 18 - Q.rootMultiplicity (11 : ℤ) = 18 := by omega
    have hbound := gsy_multiplicity_bound_odd (n := 59) (d := 18) (by omega) (by omega)
      hS hQ_mon hdeg18 hQ_eq (κ := 11) ⟨5, rfl⟩ (by rw [hη]; omega)
    rw [hη] at hbound
    norm_num at hbound
  exact ⟨Q, hQ_mon, hdeg18, hQ_eq,
    dvd_trans (pow_dvd_pow (X - C (11 : ℤ)) hmult) (Polynomial.pow_rootMultiplicity_dvd Q 11)⟩

/-- For `(d, n) = (19, 74)`, `(X - C 15)^6` divides the degree-19 cofactor `Q`. -/
theorem frontier_19_74_mult_15 {S : Matrix (Fin 74) (Fin 74) ℤ} (hS : IsSeidelMatrix S)
    (hPSD : (seidelGram (1 / 5 : ℝ) S).PosSemidef)
    (hrank : (seidelGram (1 / 5 : ℝ) S).rank ≤ 19) :
    ∃ Q : ℤ[X], Q.Monic ∧ Q.natDegree = 19 ∧
      S.charpoly = (X + C (5 : ℤ)) ^ 55 * Q ∧ (X - C (15 : ℤ)) ^ 6 ∣ Q := by
  obtain ⟨_, Q, hQ_mon, hQ_eq, hQ_deg⟩ := seidel_charpoly_factorization hS hPSD hrank
  have hdeg19 : Q.natDegree = 19 := hQ_deg (by omega)
  have hbound := gsy_multiplicity_bound_even (n := 74) (d := 19) ⟨37, rfl⟩ (by omega)
    hS hQ_mon hdeg19 hQ_eq (κ := 15) ⟨7, rfl⟩
  have hη : 19 - Q.rootMultiplicity (15 : ℤ) ≤ 13 := by
    norm_num at hbound
    by_contra hgt
    have h14 : (14 : ℝ) ≤ ((19 - Q.rootMultiplicity (15 : ℤ) : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 14 ≤ 19 - Q.rootMultiplicity (15 : ℤ))
    linarith
  have hmult : 6 ≤ Q.rootMultiplicity (15 : ℤ) := by omega
  exact ⟨Q, hQ_mon, hdeg19, hQ_eq,
    dvd_trans (pow_dvd_pow (X - C (15 : ℤ)) hmult) (Polynomial.pow_rootMultiplicity_dvd Q 15)⟩

/-- For `(d, n) = (17, 49)`, `(X - C 9)^4` divides the degree-17 cofactor `Q`. -/
theorem frontier_17_49_mult_9 {S : Matrix (Fin 49) (Fin 49) ℤ} (hS : IsSeidelMatrix S)
    (hPSD : (seidelGram (1 / 5 : ℝ) S).PosSemidef)
    (hrank : (seidelGram (1 / 5 : ℝ) S).rank ≤ 17) :
    ∃ Q : ℤ[X], Q.Monic ∧ Q.natDegree = 17 ∧
      S.charpoly = (X + C (5 : ℤ)) ^ 32 * Q ∧ (X - C (9 : ℤ)) ^ 4 ∣ Q := by
  obtain ⟨_, Q, hQ_mon, hQ_eq, hQ_deg⟩ := seidel_charpoly_factorization hS hPSD hrank
  have hdeg17 : Q.natDegree = 17 := hQ_deg (by omega)
  have hm_le : Q.rootMultiplicity (9 : ℤ) ≤ 17 := by
    rcases Polynomial.pow_rootMultiplicity_dvd Q 9 with ⟨T, hT⟩
    have hT_mon : T.Monic := by
      have h1 := hQ_mon; rw [hT] at h1
      exact Polynomial.Monic.of_mul_monic_left ((monic_X_sub_C (9 : ℤ)).pow _) h1
    have hdeg := congrArg Polynomial.natDegree hT
    rw [hdeg17, ((monic_X_sub_C (9 : ℤ)).pow _).natDegree_mul' hT_mon.ne_zero,
      natDegree_pow, natDegree_X_sub_C, mul_one] at hdeg
    omega
  have hmult : 4 ≤ Q.rootMultiplicity (9 : ℤ) := by
    by_contra hm_lt
    have hm3 : Q.rootMultiplicity (9 : ℤ) ≤ 3 := by omega
    let η := 17 - Q.rootMultiplicity (9 : ℤ)
    have hη14 : 14 ≤ η := by omega
    have hη_real : (14 : ℝ) ≤ (η : ℝ) := by exact_mod_cast hη14
    have hbound := gsy_multiplicity_bound_odd (n := 49) (d := 17) (by omega) (by omega)
      hS hQ_mon hdeg17 hQ_eq (κ := 9) ⟨4, rfl⟩ (by omega)
    norm_num at hbound
    have hprod_lt : ((49 : ℝ) ^ 14 < (14 : ℝ) ^ 14 * (4 : ℝ) ^ 13) := by norm_num
    have hgrow : (49 : ℝ) ^ η = (49 : ℝ) ^ 14 * (49 : ℝ) ^ (η - 14) := by
      rw [← pow_add]; congr 1; omega
    have hrhs_grow : (η : ℝ) ^ η * (4 : ℝ) ^ (η - 1) ≥
        (14 : ℝ) ^ 14 * (4 : ℝ) ^ 13 * ((14 * 4 : ℝ) ^ (η - 14)) := by
      have h_eq1 : η = 14 + (η - 14) := by omega
      have h_eq2 : η - 1 = 13 + (η - 14) := by omega
      have ha : (14 : ℝ) ^ 14 * (14 : ℝ) ^ (η - 14) ≤ (η : ℝ) ^ η := by
        calc
          (14 : ℝ) ^ 14 * (14 : ℝ) ^ (η - 14) = (14 : ℝ) ^ η := by rw [← pow_add, ← h_eq1]
          _ ≤ (η : ℝ) ^ η := pow_le_pow_left₀ (by norm_num) hη_real η
      have hb : (4 : ℝ) ^ (η - 1) = (4 : ℝ) ^ 13 * (4 : ℝ) ^ (η - 14) := by
        conv_lhs => rw [h_eq2]
        rw [pow_add]
      rw [hb]
      calc
        (η : ℝ) ^ η * ((4 : ℝ) ^ 13 * (4 : ℝ) ^ (η - 14))
            ≥ ((14 : ℝ) ^ 14 * (14 : ℝ) ^ (η - 14)) * ((4 : ℝ) ^ 13 * (4 : ℝ) ^ (η - 14)) :=
              mul_le_mul_of_nonneg_right ha (by positivity)
        _ = (14 : ℝ) ^ 14 * (4 : ℝ) ^ 13 * ((14 * 4 : ℝ) ^ (η - 14)) := by
              rw [mul_pow]; ring
    have hc2 : (49 : ℝ) ^ (η - 14) ≤ (14 * 4 : ℝ) ^ (η - 14) :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) (η - 14)
    have hbad : (49 : ℝ) ^ η < (η : ℝ) ^ η * (4 : ℝ) ^ (η - 1) := by
      rw [hgrow]
      calc
        (49 : ℝ) ^ 14 * (49 : ℝ) ^ (η - 14)
            < (14 : ℝ) ^ 14 * (4 : ℝ) ^ 13 * (49 : ℝ) ^ (η - 14) :=
              mul_lt_mul_of_pos_right hprod_lt (by positivity)
        _ ≤ (14 : ℝ) ^ 14 * (4 : ℝ) ^ 13 * (14 * 4 : ℝ) ^ (η - 14) :=
              mul_le_mul_of_nonneg_left hc2 (by positivity)
        _ ≤ (η : ℝ) ^ η * (4 : ℝ) ^ (η - 1) := hrhs_grow
    have hbound' : (η : ℝ) ^ η * (4 : ℝ) ^ (η - 1) ≤ (49 : ℝ) ^ η := hbound
    linarith
  exact ⟨Q, hQ_mon, hdeg17, hQ_eq,
    dvd_trans (pow_dvd_pow (X - C (9 : ℤ)) hmult) (Polynomial.pow_rootMultiplicity_dvd Q 9)⟩

/-- For `(d, n) = (18, 60)`, `(X - C 11)^6` divides the degree-18 cofactor `Q`. -/
theorem frontier_18_60_mult_11 {S : Matrix (Fin 60) (Fin 60) ℤ} (hS : IsSeidelMatrix S)
    (hPSD : (seidelGram (1 / 5 : ℝ) S).PosSemidef)
    (hrank : (seidelGram (1 / 5 : ℝ) S).rank ≤ 18) :
    ∃ Q : ℤ[X], Q.Monic ∧ Q.natDegree = 18 ∧
      S.charpoly = (X + C (5 : ℤ)) ^ 42 * Q ∧ (X - C (11 : ℤ)) ^ 6 ∣ Q := by
  obtain ⟨_, Q, hQ_mon, hQ_eq, hQ_deg⟩ := seidel_charpoly_factorization hS hPSD hrank
  have hdeg18 : Q.natDegree = 18 := hQ_deg (by omega)
  have hbound := gsy_multiplicity_bound_even (n := 60) (d := 18) ⟨30, rfl⟩ (by omega)
    hS hQ_mon hdeg18 hQ_eq (κ := 11) ⟨5, rfl⟩
  have hη : 18 - Q.rootMultiplicity (11 : ℤ) ≤ 12 := by
    norm_num at hbound
    by_contra hgt
    have h13 : (13 : ℝ) ≤ ((18 - Q.rootMultiplicity (11 : ℤ) : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 13 ≤ 18 - Q.rootMultiplicity (11 : ℤ))
    linarith
  have hmult : 6 ≤ Q.rootMultiplicity (11 : ℤ) := by omega
  exact ⟨Q, hQ_mon, hdeg18, hQ_eq,
    dvd_trans (pow_dvd_pow (X - C (11 : ℤ)) hmult) (Polynomial.pow_rootMultiplicity_dvd Q 11)⟩

end FrontierSpecializations

end EquiangularLines

end
