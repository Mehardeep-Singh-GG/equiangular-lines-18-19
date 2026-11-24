module

public import EquiangularLines.Bounds
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Spectral, 2-Adic, Jacobi, and Interlacing Machinery

This file builds the algebraic and spectral infrastructure for Phase 2 of the equiangular
lines program in ℝ¹⁸ and ℝ¹⁹:

1. **Factorization & trace identities (`Section 1`):**
   For an `n × n` Seidel matrix `S` with `5I + S` PSD of rank `≤ d`,
   `(X + 5)^(n - d) ∣ S.charpoly` over `ℤ[X]`, giving a monic integer cofactor `Q` of
   degree `d` (when `d ≤ n`) whose real roots all satisfy `-5 ≤ r`, together with exact
   trace identities `trace (5I + S) = 5n`, `trace ((5I + S)^2) = n(n + 24)` and the top
   coefficients of `S.charpoly` and `Q.comp (X - C 5)`.
2. **2-adic congruences (`Section 2`):**
   Via the rank-1 update `(S + I) = J - 2A` (`A` symmetric with zero diagonal), we prove
   `(2 : ℤ)^(2 * ((n - k) / 2)) ∣ (S.charpoly.comp (X - C 1)).coeff k`,
   `C (2 ^ (n - 1)) ∣ S.charpoly.comp (C 2 * X - 1)`, and the corresponding 2-adic
   divisibility `C (2 ^ (d - 1)) ∣ Q.comp (C 2 * X - 1)` on the cofactor `Q`.
3. **Jacobi complementary minors & vertex deletions (`Section 3`):**
   Over any commutative ring `R`, we prove Jacobi's `2 × 2` complementary-minor identity
   `adjugate B i i * adjugate B j j - adjugate B i j * adjugate B j i = B.det * det B_{≠i,j}`,
   identify diagonal cofactors of `charmatrix A` with vertex-deleted characteristic
   polynomials, prove `derivative A.charpoly = ∑ i, charpoly (A \ i)`, and deduce the
   two-vertex deletion identity `P_{A\i} P_{A\j} - P_A P_{A\i,j} = (adjugate (xI - A)_{i,j})^2`.
4. **Cauchy interlacing (`Section 4`):**
   For any real symmetric matrix `A : Matrix (Fin n) (Fin n) ℝ` and any principal
   submatrix `B = A.submatrix f f` (`f : Fin m ↪ Fin n`), we prove
   `λ_{k + (n - m)} ≤ μ_k ≤ λ_k` in decreasing eigenvalue order (`eigenvalues₀`).
-/

@[expose] public section

open Matrix Polynomial
open scoped BigOperators RealInnerProductSpace

namespace EquiangularLines

/-! ## Section 1: Characteristic polynomial factorization, traces, and coefficients -/

section Factorization

private lemma prod_X_sub_C_monic {ι R : Type*} [CommRing R] (s : Finset ι) (f : ι → R) :
    (∏ i ∈ s, (X - C (f i))).Monic :=
  monic_prod_of_monic s _ (fun i _ => monic_X_sub_C (f i))

private lemma prod_X_sub_C_natDegree {ι R : Type*} [CommRing R] [Nontrivial R]
    (s : Finset ι) (f : ι → R) :
    (∏ i ∈ s, (X - C (f i))).natDegree = s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have h1 : (X - C (f a)).Monic := monic_X_sub_C _
    have h2 : (∏ i ∈ s, (X - C (f i))).Monic := prod_X_sub_C_monic s f
    rw [h1.natDegree_mul' h2.ne_zero, natDegree_X_sub_C, ih]
    omega

private lemma prod_X_sub_C_coeff_sub_one {ι R : Type*} [CommRing R] [Nontrivial R]
    (s : Finset ι) (f : ι → R) (hs : 1 ≤ s.card) :
    (∏ i ∈ s, (X - C (f i))).coeff (s.card - 1) = -∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Nat.add_sub_cancel,
      Finset.sum_insert ha, sub_mul]
    rcases Nat.eq_zero_or_pos s.card with h0 | hpos
    · have hs0 : s = ∅ := Finset.card_eq_zero.mp h0
      subst hs0
      simp
    · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      have ih' := ih (by omega)
      rw [hm] at ih' ⊢
      simp only [Nat.succ_sub_one] at ih'
      simp only [coeff_sub, coeff_X_mul, coeff_C_mul]
      have hdeg : (∏ i ∈ s, (X - C (f i))).natDegree = m + 1 := by
        rw [prod_X_sub_C_natDegree, hm]
      have hlead : (∏ i ∈ s, (X - C (f i))).coeff (m + 1) = 1 := by
        rw [← hdeg]
        exact (prod_X_sub_C_monic s f).leadingCoeff
      rw [ih', hlead]
      ring

private lemma two_mul_prod_X_sub_C_coeff_sub_two {ι R : Type*} [CommRing R] [Nontrivial R]
    (s : Finset ι) (f : ι → R) (hs : 2 ≤ s.card) :
    2 * (∏ i ∈ s, (X - C (f i))).coeff (s.card - 2) =
      (∑ i ∈ s, f i) ^ 2 - ∑ i ∈ s, (f i) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
    rw [Finset.card_insert_of_notMem ha] at hs
    have hm1 : 1 ≤ s.card := by omega
    by_cases h1 : s.card = 1
    · obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp h1
      have hne : a ≠ b := fun hab => ha (by simp [hab])
      simp [Finset.sum_pair hne]
      ring
    · have hm2 : 2 ≤ s.card := by omega
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hm2
      have ih' := ih hm2
      have ih1 := prod_X_sub_C_coeff_sub_one s f hm1
      rw [show s.card + 1 - 2 = k + 1 by omega]
      rw [show s.card - 2 = k by omega] at ih'
      rw [show s.card - 1 = k + 1 by omega] at ih1
      rw [sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul, Finset.sum_insert ha]
      rw [mul_sub, ih', ih1]
      ring

private lemma charpoly_conj_unitary {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix.unitaryGroup (Fin n) ℝ) :
    ((U : Matrix (Fin n) (Fin n) ℝ) * D * (star U : Matrix (Fin n) (Fin n) ℝ)).charpoly =
      D.charpoly := by
  let U' : Matrix (Fin n) (Fin n) ℝ := U
  let Ustar : Matrix (Fin n) (Fin n) ℝ := star U
  have hUU : U' * Ustar = 1 := Unitary.coe_mul_star_self U
  have hmap1 : U'.map C * Ustar.map C = 1 := by
    rw [← Matrix.map_mul, hUU]
    refine Matrix.ext fun i j => ?_
    rw [Matrix.map_apply]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hchar :
      charmatrix (U' * D * Ustar) =
        U'.map C * charmatrix D * Ustar.map C := by
    have hsc : U'.map C * Matrix.scalar (Fin n) (X : ℝ[X]) * Ustar.map C =
        Matrix.scalar (Fin n) (X : ℝ[X]) := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.map_apply]
      have hinner : ∀ k : Fin n, (∑ x : Fin n,
          (C (U' i x) * (if x = k then (X : ℝ[X]) else 0)) * C (Ustar k j)) =
          C (U' i k * Ustar k j) * X := by
        intro k
        rw [Finset.sum_eq_single k]
        · simp [map_mul]; ring
        · intro x _ hxk; simp [hxk]
        · intro hk; exact False.elim (hk (Finset.mem_univ k))
      have houter : (∑ k : Fin n, ∑ x : Fin n,
          (C (U' i x) * (if x = k then (X : ℝ[X]) else 0)) * C (Ustar k j)) =
          C (∑ k : Fin n, U' i k * Ustar k j) * X := by
        simp_rw [hinner, ← Finset.sum_mul, ← map_sum]
      have hsum_comm : (∑ j_1 : Fin n, (∑ j_2 : Fin n,
          C (U' i j_2) * (if j_2 = j_1 then (X : ℝ[X]) else 0)) * C (Ustar j_1 j)) =
          ∑ k : Fin n, ∑ x : Fin n,
            (C (U' i x) * (if x = k then (X : ℝ[X]) else 0)) * C (Ustar k j) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul]
      rw [hsum_comm, houter]
      have hUU_ij : (∑ k : Fin n, U' i k * Ustar k j) = if i = j then 1 else 0 := by
        simpa [Matrix.mul_apply, Matrix.one_apply] using congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hUU
      rw [hUU_ij]
      by_cases hij : i = j <;> simp [hij]
    rw [charmatrix, charmatrix]
    simp only [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.mul_sub, Matrix.sub_mul]
    rw [hsc]
  rw [Matrix.charpoly, hchar, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
    hmap1, Matrix.det_one, one_mul]
  rfl

private lemma hermitian_charpoly_eq_prod {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) :
    A.charpoly = ∏ i : Fin n, (X - C (hA.eigenvalues i)) := by
  have hspec := hA.spectral_theorem
  have hAeq :
      A = (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
        Matrix.diagonal hA.eigenvalues *
        (star hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) := by
    simpa [RCLike.ofReal_real_eq_id] using hspec
  conv_lhs => rw [hAeq]
  rw [charpoly_conj_unitary, Matrix.charpoly_diagonal]

private lemma hermitian_trace_eq_sum_eigenvalues {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) :
    A.trace = ∑ i : Fin n, hA.eigenvalues i := by
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

private lemma hermitian_trace_sq_eq_sum_eigenvalues_sq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) :
    (A * A).trace = ∑ i : Fin n, (hA.eigenvalues i) ^ 2 := by
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

private lemma isHermitian_seidel_real {n : ℕ} {S : Matrix (Fin n) (Fin n) ℤ}
    (hS : IsSeidelMatrix S) :
    (S.map (Int.cast : ℤ → ℝ)).IsHermitian := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, star_trivial]
  exact congrArg (fun M : Matrix (Fin n) (Fin n) ℤ => (M i j : ℝ)) hS.1

private lemma seidel_symm {n : ℕ} {S : Matrix (Fin n) (Fin n) ℤ} (hS : IsSeidelMatrix S) :
    Sᵀ = S :=
  hS.1

private lemma seidel_off_pm {n : ℕ} {S : Matrix (Fin n) (Fin n) ℤ} (hS : IsSeidelMatrix S)
    {i j : Fin n} (hij : i ≠ j) : S i j = 1 ∨ S i j = -1 :=
  hS.2.2 i j hij

private lemma hermitian_charpoly_coeff_sub_one {n : ℕ} (hn : 1 ≤ n)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    A.charpoly.coeff (n - 1) = -A.trace := by
  rw [hermitian_charpoly_eq_prod hA]
  have hs : (1 : ℕ) ≤ (Finset.univ : Finset (Fin n)).card := by simpa using hn
  simpa [Finset.card_univ, Fintype.card_fin, hermitian_trace_eq_sum_eigenvalues hA] using
    prod_X_sub_C_coeff_sub_one (Finset.univ : Finset (Fin n)) hA.eigenvalues hs

private lemma hermitian_two_mul_charpoly_coeff_sub_two {n : ℕ} (hn : 2 ≤ n)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    2 * A.charpoly.coeff (n - 2) = A.trace ^ 2 - (A * A).trace := by
  rw [hermitian_charpoly_eq_prod hA]
  have hs : (2 : ℕ) ≤ (Finset.univ : Finset (Fin n)).card := by simpa using hn
  simpa [Finset.card_univ, Fintype.card_fin, hermitian_trace_eq_sum_eigenvalues hA,
    hermitian_trace_sq_eq_sum_eigenvalues_sq hA] using
    two_mul_prod_X_sub_C_coeff_sub_two (Finset.univ : Finset (Fin n)) hA.eigenvalues hs

lemma charpoly_add_smul_one {n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin n) (Fin n) R) (c : R) :
    (c • (1 : Matrix (Fin n) (Fin n) R) + A).charpoly = A.charpoly.comp (X - C c) := by
  let φ : R[X] →+* R[X] := Polynomial.eval₂RingHom C (X - C c)
  have hchar : charmatrix (c • (1 : Matrix (Fin n) (Fin n) R) + A) = (charmatrix A).map φ := by
    refine Matrix.ext fun i j => ?_
    by_cases hij : i = j
    · subst hij
      simp [φ, charmatrix, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq]
      ring
    · simp [φ, charmatrix, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hij,
        Matrix.diagonal_apply_ne _ hij]
  rw [Matrix.charpoly, hchar, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rfl

/-- For an `n × n` Seidel matrix `S` with `5I + S` PSD of rank `≤ d`, `(X + 5)^(n - d)` divides
`S.charpoly` in `ℤ[X]`, and the quotient `Q` is a monic polynomial of degree `d` (when `d ≤ n`). -/
theorem seidel_charpoly_factorization {n d : ℕ} {S : Matrix (Fin n) (Fin n) ℤ}
    (hS : IsSeidelMatrix S) (_hPSD : (seidelGram (1 / 5 : ℝ) S).PosSemidef)
    (hrank : (seidelGram (1 / 5 : ℝ) S).rank ≤ d) :
    (X + C (5 : ℤ)) ^ (n - d) ∣ S.charpoly ∧
      ∃ Q : ℤ[X], Q.Monic ∧ S.charpoly = (X + C (5 : ℤ)) ^ (n - d) * Q ∧
        (d ≤ n → Q.natDegree = d) := by
  have hdvd : (X + C (5 : ℤ)) ^ (n - d) ∣ S.charpoly :=
    seidelGram_dvd_charpoly_int (k := 5) hS (by norm_num)
      (by simpa [one_div_one_div] using hrank)
  refine ⟨hdvd, ?_⟩
  rcases hdvd with ⟨Q, hQ⟩
  have hPmon : ((X + C (5 : ℤ)) ^ (n - d)).Monic := (monic_X_add_C (5 : ℤ)).pow (n - d)
  have hSmon : S.charpoly.Monic := Matrix.charpoly_monic S
  have hQmon : Q.Monic := by
    rw [hQ] at hSmon
    exact Polynomial.Monic.of_mul_monic_left hPmon hSmon
  refine ⟨Q, hQmon, hQ, fun hdn => ?_⟩
  have hdegS : S.charpoly.natDegree = n := (Matrix.charpoly_natDegree_eq_dim S).trans (Fintype.card_fin n)
  have hdegP : ((X + C (5 : ℤ)) ^ (n - d)).natDegree = n - d := by
    rw [natDegree_pow, natDegree_X_add_C, mul_one]
  rw [hQ, hPmon.natDegree_mul' hQmon.ne_zero, hdegP] at hdegS
  omega

/-- Over `ℤ`, `trace (5I + S) = 5n` for any Seidel matrix `S`. -/
theorem seidel_five_trace_int {n : ℕ} {S : Matrix (Fin n) (Fin n) ℤ}
    (hS : IsSeidelMatrix S) :
    ((5 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) + S).trace = 5 * (n : ℤ) := by
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, hS.trace_eq_zero, add_zero]
  simp

/-- Over `ℤ`, `trace ((5I + S)^2) = n * (n + 24)` for any Seidel matrix `S`. -/
theorem seidel_five_trace_sq_int {n : ℕ} {S : Matrix (Fin n) (Fin n) ℤ}
    (hS : IsSeidelMatrix S) :
    (((5 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) + S) ^ 2).trace =
      (n : ℤ) * ((n : ℤ) + 24) := by
  have hsq :
      ((5 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) + S) ^ 2 =
        (25 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) + (10 : ℤ) • S + S * S := by
    calc
      ((5 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) + S) ^ 2
          = ((5 : ℤ) • 1 + S) * ((5 : ℤ) • 1 + S) := sq _
      _ = (25 : ℤ) • 1 + (5 : ℤ) • S + ((5 : ℤ) • S + S * S) := by
          simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one,
            smul_smul]
          norm_num
      _ = (25 : ℤ) • 1 + (10 : ℤ) • S + S * S := by
          rw [← add_assoc ((25 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) + (5 : ℤ) • S),
            add_assoc ((25 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)), ← add_smul]
          norm_num
  rw [hsq, Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_one, hS.trace_eq_zero, hS.trace_sq]
  simp only [Fintype.card_fin, smul_eq_mul, mul_zero, add_zero]
  ring

private lemma trace_map_ringHom {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (M : Matrix (Fin n) (Fin n) R) :
    (M.map f).trace = f M.trace := by
  simp [Matrix.trace, Matrix.diag_apply, Matrix.map_apply, map_sum]

/-- Over `ℝ`, `trace (seidelGram (1/5) S) = 5n` for any Seidel matrix `S`. -/
theorem seidel_five_trace {n : ℕ} {S : Matrix (Fin n) (Fin n) ℤ}
    (hS : IsSeidelMatrix S) :
    (seidelGram (1 / 5 : ℝ) S).trace = 5 * (n : ℝ) := by
  have hG : seidelGram (1 / 5 : ℝ) S =
      ((5 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) + S).map (Int.castRingHom ℝ) := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp [seidelGram]
    · simp [seidelGram, hij]
  rw [hG, trace_map_ringHom, seidel_five_trace_int hS]
  simp

/-- Over `ℝ`, `trace ((seidelGram (1/5) S)^2) = n * (n + 24)` for any Seidel matrix `S`. -/
theorem seidel_five_trace_sq {n : ℕ} {S : Matrix (Fin n) (Fin n) ℤ}
    (hS : IsSeidelMatrix S) :
    ((seidelGram (1 / 5 : ℝ) S) ^ 2).trace = (n : ℝ) * ((n : ℝ) + 24) := by
  have hG : seidelGram (1 / 5 : ℝ) S =
      ((5 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) + S).map (Int.castRingHom ℝ) := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp [seidelGram]
    · simp [seidelGram, hij]
  have hsq : (((5 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) + S).map (Int.castRingHom ℝ)) ^ 2 =
      (((5 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) + S) ^ 2).map (Int.castRingHom ℝ) := by
    rw [sq, sq, ← Matrix.map_mul]
  rw [hG, hsq, trace_map_ringHom, seidel_five_trace_sq_int hS]
  simp

/-- For any Seidel matrix `S` of order `n ≥ 1`, the `(n - 1)`-th coefficient of `S.charpoly` is `0`. -/
theorem seidel_charpoly_coeff_sub_one {n : ℕ} (hn : 1 ≤ n) {S : Matrix (Fin n) (Fin n) ℤ}
    (hS : IsSeidelMatrix S) :
    S.charpoly.coeff (n - 1) = 0 := by
  have hHerm : (S.map (Int.castRingHom ℝ)).IsHermitian := isHermitian_seidel_real hS
  have h1 := hermitian_charpoly_coeff_sub_one hn hHerm
  rw [Matrix.charpoly_map S (Int.castRingHom ℝ), coeff_map, trace_map_ringHom,
    hS.trace_eq_zero] at h1
  simp only [eq_intCast] at h1
  exact Int.cast_injective (α := ℝ) (by simpa using h1)

/-- For any Seidel matrix `S` of order `n ≥ 2`, twice the `(n - 2)`-th coefficient of
`S.charpoly` equals `- n * (n - 1)`. -/
theorem two_mul_seidel_charpoly_coeff_sub_two {n : ℕ} (hn : 2 ≤ n)
    {S : Matrix (Fin n) (Fin n) ℤ} (hS : IsSeidelMatrix S) :
    2 * S.charpoly.coeff (n - 2) = -(n : ℤ) * ((n : ℤ) - 1) := by
  have hHerm : (S.map (Int.castRingHom ℝ)).IsHermitian := isHermitian_seidel_real hS
  have h2 := hermitian_two_mul_charpoly_coeff_sub_two hn hHerm
  rw [Matrix.charpoly_map S (Int.castRingHom ℝ), coeff_map, trace_map_ringHom, ← Matrix.map_mul,
    trace_map_ringHom, hS.trace_eq_zero, hS.trace_sq] at h2
  simp only [eq_intCast] at h2
  have hcast : ((2 * S.charpoly.coeff (n - 2) : ℤ) : ℝ) = ((-(n : ℤ) * ((n : ℤ) - 1) : ℤ) : ℝ) := by
    push_cast at h2 ⊢
    linarith
  exact Int.cast_injective hcast

/-- For any Seidel matrix `S` of order `n ≥ 2`, `S.charpoly.coeff (n - 2) = - ((n * (n - 1) / 2 : ℕ) : ℤ)`. -/
theorem seidel_charpoly_coeff_sub_two {n : ℕ} (hn : 2 ≤ n) {S : Matrix (Fin n) (Fin n) ℤ}
    (hS : IsSeidelMatrix S) :
    S.charpoly.coeff (n - 2) = -((n * (n - 1) / 2 : ℕ) : ℤ) := by
  have h2 := two_mul_seidel_charpoly_coeff_sub_two hn hS
  have heven : 2 ∣ n * (n - 1) := (Nat.even_mul_pred_self n).two_dvd
  have h2' : 2 * (n * (n - 1) / 2) = n * (n - 1) := Nat.mul_div_cancel' heven
  have hcast : (2 : ℤ) * (n * (n - 1) / 2 : ℕ) = (n : ℤ) * ((n : ℤ) - 1) := by
    zify [show 1 ≤ n by omega] at h2' ⊢
    exact h2'
  linarith

/-- If `S.charpoly = (X + C 5)^(n - d) * Q` and `5I + S` is PSD, then every real root `r` of
`Q` satisfies `-5 ≤ r`, and every real root `μ` of `Q.comp (X - C 5)` satisfies `0 ≤ μ`. -/
theorem shifted_factor_nonneg_roots {n d : ℕ} {S : Matrix (Fin n) (Fin n) ℤ}
    (hS : IsSeidelMatrix S) (hPSD : (seidelGram (1 / 5 : ℝ) S).PosSemidef)
    {Q : ℤ[X]} (hQ : S.charpoly = (X + C (5 : ℤ)) ^ (n - d) * Q) :
    (∀ r : ℝ, (Q.map (Int.castRingHom ℝ)).IsRoot r → -5 ≤ r) ∧
      (∀ μ : ℝ, ((Q.comp (X - C (5 : ℤ))).map (Int.castRingHom ℝ)).IsRoot μ → 0 ≤ μ) := by
  let S_R : Matrix (Fin n) (Fin n) ℝ := S.map (Int.castRingHom ℝ)
  have hHerm : S_R.IsHermitian := by simpa [S_R] using isHermitian_seidel_real hS
  have hS_prod : S_R.charpoly = ∏ i : Fin n, (X - C (hHerm.eigenvalues i)) :=
    hermitian_charpoly_eq_prod hHerm
  have heig_ge : ∀ i : Fin n, -5 ≤ hHerm.eigenvalues i := by
    intro i
    let U : Matrix (Fin n) (Fin n) ℝ := hHerm.eigenvectorUnitary
    let v : Fin n → ℝ := U *ᵥ Pi.single i 1
    have hU : star U * U = 1 := Unitary.coe_star_mul_self hHerm.eigenvectorUnitary
    have hU' : Uᵀ * U = 1 := by simpa [Matrix.star_eq_conjTranspose] using hU
    have hspec : S_R = U * Matrix.diagonal hHerm.eigenvalues * Uᵀ := by
      simpa [U, Matrix.star_eq_conjTranspose, RCLike.ofReal_real_eq_id] using hHerm.spectral_theorem
    have hv_norm : v ⬝ᵥ v = 1 := by
      calc
        v ⬝ᵥ v = (U *ᵥ Pi.single i 1) ⬝ᵥ (U *ᵥ Pi.single i 1) := rfl
        _ = (Pi.single i 1 ᵥ* Uᵀ) ⬝ᵥ (U *ᵥ Pi.single i 1) := by rw [Matrix.vecMul_transpose]
        _ = Pi.single i 1 ⬝ᵥ ((Uᵀ * U) *ᵥ Pi.single i 1) := by
            rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
        _ = Pi.single i 1 ⬝ᵥ Pi.single i 1 := by rw [hU', Matrix.one_mulVec]
        _ = 1 := by simp
    have hv_eig : S_R *ᵥ v = hHerm.eigenvalues i • v := by
      calc
        S_R *ᵥ v = (U * Matrix.diagonal hHerm.eigenvalues * Uᵀ) *ᵥ (U *ᵥ Pi.single i 1) := by
            conv_lhs => rw [hspec]
        _ = U *ᵥ (Matrix.diagonal hHerm.eigenvalues *ᵥ ((Uᵀ * U) *ᵥ Pi.single i 1)) := by
            simp only [Matrix.mul_assoc, Matrix.mulVec_mulVec]
        _ = U *ᵥ (Matrix.diagonal hHerm.eigenvalues *ᵥ Pi.single i 1) := by
            rw [hU', Matrix.one_mulVec]
        _ = U *ᵥ (hHerm.eigenvalues i • Pi.single i 1) := by
            congr 1; ext j
            simp [Matrix.mulVec_diagonal, Pi.single_apply]
            split_ifs with hji <;> simp [hji]
        _ = hHerm.eigenvalues i • v := by rw [Matrix.mulVec_smul]
    have hG_eq : seidelGram (1 / 5 : ℝ) S = (5 : ℝ) • 1 + S_R := by
      refine Matrix.ext fun a b => ?_
      rw [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
      by_cases hab : a = b
      · subst hab; simp [seidelGram, S_R]
      · simp [seidelGram, S_R, hab]
    have hnonneg : 0 ≤ star v ⬝ᵥ (seidelGram (1 / 5 : ℝ) S *ᵥ v) :=
      hPSD.dotProduct_mulVec_nonneg v
    rw [hG_eq, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hv_eig,
      dotProduct_add, dotProduct_smul, dotProduct_smul] at hnonneg
    simp only [star_trivial, hv_norm, smul_eq_mul, mul_one] at hnonneg
    linarith
  have hroot_ge : ∀ r : ℝ, (Q.map (Int.castRingHom ℝ)).IsRoot r → -5 ≤ r := by
    intro r hr
    have hSR : S_R.charpoly = (X + C (5 : ℝ)) ^ (n - d) * Q.map (Int.castRingHom ℝ) := by
      have hm := congrArg (Polynomial.map (Int.castRingHom ℝ)) hQ
      rw [← Matrix.charpoly_map S (Int.castRingHom ℝ)] at hm
      simpa [S_R, C_ofNat] using hm
    have hrS : S_R.charpoly.IsRoot r := by
      rw [hSR, Polynomial.IsRoot.def, Polynomial.eval_mul, hr.eq_zero, mul_zero]
    rw [hS_prod, Polynomial.IsRoot.def, Polynomial.eval_prod] at hrS
    obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hrS
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hi
    rw [hi]
    exact heig_ge i
  refine ⟨hroot_ge, fun μ hμ => ?_⟩
  have hr : (Q.map (Int.castRingHom ℝ)).IsRoot (μ - 5) := by
    rw [Polynomial.IsRoot.def] at hμ ⊢
    simpa [Polynomial.map_comp, Polynomial.eval_comp] using hμ
  linarith [hroot_ge (μ - 5) hr]

/-- Exact top two coefficients of `Q.comp (X - C 5)` when `S.charpoly = (X + C 5)^(n - d) * Q`. -/
theorem shifted_factor_trace_coeffs {n d : ℕ} (hdn : d ≤ n) {S : Matrix (Fin n) (Fin n) ℤ}
    (hS : IsSeidelMatrix S) {Q : ℤ[X]} (hQ : S.charpoly = (X + C (5 : ℤ)) ^ (n - d) * Q) :
    (1 ≤ d → (Q.comp (X - C (5 : ℤ))).coeff (d - 1) = -5 * (n : ℤ)) ∧
      (2 ≤ d → (Q.comp (X - C (5 : ℤ))).coeff (d - 2) = 12 * (n : ℤ) * ((n : ℤ) - 1)) := by
  let M : Matrix (Fin n) (Fin n) ℤ := (5 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) + S
  have hM_comp : M.charpoly = S.charpoly.comp (X - C (5 : ℤ)) := charpoly_add_smul_one S 5
  have hM_prod : M.charpoly = X ^ (n - d) * Q.comp (X - C (5 : ℤ)) := by
    rw [hM_comp, hQ, mul_comp, pow_comp, add_comp, X_comp, C_comp]
    simp
  have hM_real : M.map (Int.castRingHom ℝ) = seidelGram (1 / 5 : ℝ) S := by
    refine Matrix.ext fun i j => ?_
    have hM_def : M = (5 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) + S := rfl
    rw [Matrix.map_apply, hM_def, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp [seidelGram]
    · simp [seidelGram, hij]
  have hHerm : (M.map (Int.castRingHom ℝ)).IsHermitian := by
    rw [hM_real]
    exact seidelGram_isHermitian (1 / 5 : ℝ) S hS
  refine ⟨fun hd1 => ?_, fun hd2 => ?_⟩
  · have hn1 : 1 ≤ n := le_trans hd1 hdn
    have hidx : (d - 1) + (n - d) = n - 1 := by omega
    have hcoeff : (Q.comp (X - C (5 : ℤ))).coeff (d - 1) = M.charpoly.coeff (n - 1) := by
      rw [hM_prod, ← hidx, Polynomial.coeff_X_pow_mul]
    have h1 := hermitian_charpoly_coeff_sub_one hn1 hHerm
    rw [Matrix.charpoly_map M (Int.castRingHom ℝ), coeff_map, trace_map_ringHom,
      seidel_five_trace_int hS] at h1
    simp only [eq_intCast] at h1
    have hM1 : M.charpoly.coeff (n - 1) = -5 * (n : ℤ) :=
      Int.cast_injective (α := ℝ) (by simpa [mul_comm] using h1)
    omega
  · have hn2 : 2 ≤ n := le_trans hd2 hdn
    have hidx : (d - 2) + (n - d) = n - 2 := by omega
    have hcoeff : (Q.comp (X - C (5 : ℤ))).coeff (d - 2) = M.charpoly.coeff (n - 2) := by
      rw [hM_prod, ← hidx, Polynomial.coeff_X_pow_mul]
    have h2 := hermitian_two_mul_charpoly_coeff_sub_two hn2 hHerm
    rw [Matrix.charpoly_map M (Int.castRingHom ℝ), coeff_map, trace_map_ringHom, ← Matrix.map_mul,
      trace_map_ringHom, ← sq, seidel_five_trace_int hS, seidel_five_trace_sq_int hS] at h2
    simp only [eq_intCast] at h2
    have hM2 : 2 * M.charpoly.coeff (n - 2) = 24 * (n : ℤ) * ((n : ℤ) - 1) := by
      apply Int.cast_injective (α := ℝ)
      push_cast at h2 ⊢
      linarith
    linarith

end Factorization

/-! ## Section 2: 2-adic congruences on the shifted characteristic polynomial -/

section TwoAdic

/-- Matrix determinant lemma for a rank-1 addition `A + u vᵀ`. -/
theorem det_add_vecMulVec {n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin n) (Fin n) R) (u v : Fin n → R) :
    (A + Matrix.vecMulVec u v).det = A.det + v ⬝ᵥ (Matrix.adjugate A *ᵥ u) := by
  let F : Finset (Fin n) → R := fun t =>
    ∑ σ : Equiv.Perm (Fin n),
      Equiv.Perm.sign σ • ((∏ i ∈ t, u (σ i) * v i) * ∏ i ∈ Finset.univ \ t, A (σ i) i)
  have hdet_split : (A + Matrix.vecMulVec u v).det =
      ∑ t ∈ (Finset.univ : Finset (Fin n)).powerset, F t := by
    rw [Matrix.det_apply]
    have hprod : ∀ σ : Equiv.Perm (Fin n),
        Equiv.Perm.sign σ • ∏ i : Fin n, (A + Matrix.vecMulVec u v) (σ i) i =
          ∑ t ∈ (Finset.univ : Finset (Fin n)).powerset,
            Equiv.Perm.sign σ • ((∏ i ∈ t, u (σ i) * v i) * ∏ i ∈ Finset.univ \ t, A (σ i) i) := by
      intro σ
      have hfun : ∀ i : Fin n, (A + Matrix.vecMulVec u v) (σ i) i =
          u (σ i) * v i + A (σ i) i := fun i => by
        rw [Matrix.add_apply, add_comm]
        simp [Matrix.vecMulVec]
      rw [Finset.prod_congr rfl (fun i _ => hfun i)]
      rw [Finset.prod_add (fun i => u (σ i) * v i) (fun i => A (σ i) i) Finset.univ, Finset.smul_sum]
    simp_rw [hprod]
    exact Finset.sum_comm
  have hF0 : F ∅ = A.det := by
    simp [F, Matrix.det_apply]
  have hF1 : ∀ j : Fin n, F {j} = ∑ i : Fin n, u i * v j * A.adjugate j i := by
    intro j
    let w : Fin n → R := fun i => u i * v j
    have hupd_det : F {j} = (A.updateCol j w).det := by
      rw [Matrix.det_apply]
      refine Finset.sum_congr rfl fun σ _ => ?_
      congr 1
      rw [Finset.prod_singleton, Finset.sdiff_singleton_eq_erase]
      symm
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
      congr 1
      · simp [w]
      · refine Finset.prod_congr rfl fun i hi => ?_
        exact Matrix.updateCol_ne (Finset.ne_of_mem_erase hi)
    rw [hupd_det, Matrix.det_eq_sum_mul_adjugate_col (A.updateCol j w) j]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hadj : (A.updateCol j w).adjugate j i = A.adjugate j i := by
      have htr : (A.updateCol j w)ᵀ = Aᵀ.updateRow j w := by
        refine Matrix.ext fun a b => ?_
        by_cases ha : a = j
        · subst ha; simp
        · simp [ha]
      have hud : (Aᵀ.updateRow j w).updateRow j (Pi.single i 1) =
          Aᵀ.updateRow j (Pi.single i 1) := by
        refine Matrix.ext fun a b => ?_
        by_cases ha : a = j
        · subst ha; simp
        · simp [ha]
      calc
        (A.updateCol j w).adjugate j i = (A.updateCol j w).adjugateᵀ i j := rfl
        _ = ((A.updateCol j w)ᵀ).adjugate i j := by rw [Matrix.adjugate_transpose]
        _ = (Aᵀ.updateRow j w).adjugate i j := by rw [htr]
        _ = Aᵀ.adjugate i j := by rw [Matrix.adjugate_apply, Matrix.adjugate_apply, hud]
        _ = A.adjugateᵀ i j := by rw [Matrix.adjugate_transpose]
        _ = A.adjugate j i := rfl
    rw [Matrix.updateCol_self, hadj]
  have hF_ge2 : ∀ t : Finset (Fin n), 2 ≤ t.card → F t = 0 := by
    intro t ht
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (lt_of_lt_of_le (by omega : 1 < 2) ht)
    let τ : Equiv.Perm (Fin n) := Equiv.swap a b
    have hτ_mem : ∀ {i : Fin n}, i ∈ t → τ i ∈ t := by
      intro i hi
      dsimp [τ]
      rw [Equiv.swap_apply_def]
      split_ifs with h1 h2
      · exact hb
      · exact ha
      · exact hi
    refine Finset.sum_involution (fun σ _ => σ * τ) ?_ ?_ ?_ ?_
    · intro σ _
      have hsign : Equiv.Perm.sign (σ * τ) = -Equiv.Perm.sign σ := by
        rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab, mul_neg_one]
      have hprod_t : ∏ i ∈ t, u ((σ * τ) i) * v i = ∏ i ∈ t, u (σ i) * v i := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
        congr 1
        refine Finset.prod_bij (fun i _ => τ i) (fun i hi => hτ_mem hi) ?_ ?_ ?_
        · intro i₁ _ i₂ _ h; exact τ.injective h
        · intro i hi; exact ⟨τ i, hτ_mem hi, by simp [τ]⟩
        · intro i _; exact congrArg u (Equiv.Perm.mul_apply σ τ i)
      have hprod_rest : ∏ i ∈ Finset.univ \ t, A ((σ * τ) i) i =
          ∏ i ∈ Finset.univ \ t, A (σ i) i := by
        refine Finset.prod_congr rfl fun i hi => ?_
        have hnot : i ∉ t := (Finset.mem_sdiff.mp hi).2
        have hia : i ≠ a := fun h => hnot (h ▸ ha)
        have hib : i ≠ b := fun h => hnot (h ▸ hb)
        rw [Equiv.Perm.mul_apply]
        simp [τ, Equiv.swap_apply_of_ne_of_ne hia hib]
      rw [hsign, hprod_t, hprod_rest, Units.smul_def, Units.smul_def, Units.val_neg,
        zsmul_eq_mul, zsmul_eq_mul, Int.cast_neg]
      ring
    · intro σ _ _ h
      have ha_eq := congrArg (fun π : Equiv.Perm (Fin n) => π a) h
      have : σ b = σ a := by simpa [τ] using ha_eq
      exact hab (σ.injective this).symm
    · intro _ _; exact Finset.mem_univ _
    · intro σ _; simp [τ, mul_assoc]
  rw [hdet_split, ← Finset.add_sum_erase _ F (Finset.mem_powerset.mpr (Finset.empty_subset _)), hF0]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not ((Finset.univ : Finset (Fin n)).powerset.erase ∅)
    (fun t => t.card = 1)]
  have hzero : ∑ t ∈ ((Finset.univ : Finset (Fin n)).powerset.erase ∅).filter
      (fun t => ¬t.card = 1), F t = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_powerset] at ht
    apply hF_ge2 t
    have hc0 : t.card ≠ 0 := fun h => ht.1.1 (Finset.card_eq_zero.mp h)
    have hc1 : t.card ≠ 1 := ht.2
    omega
  rw [hzero, add_zero]
  have himg : ((Finset.univ : Finset (Fin n)).powerset.erase ∅).filter (fun t => t.card = 1) =
      Finset.univ.image (fun j : Fin n => ({j} : Finset (Fin n))) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_powerset, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hne, _⟩, hcard⟩
      obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hcard
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨⟨Finset.singleton_ne_empty j, Finset.subset_univ _⟩, Finset.card_singleton j⟩
  rw [himg, Finset.sum_image (fun _ _ _ _ h => Finset.singleton_injective h)]
  simp_rw [hF1]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

/-- Matrix determinant lemma for a rank-1 subtraction `A - u vᵀ`. -/
theorem det_sub_vecMulVec {n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin n) (Fin n) R) (u v : Fin n → R) :
    (A - Matrix.vecMulVec u v).det = A.det - v ⬝ᵥ (Matrix.adjugate A *ᵥ u) := by
  have hsub : A - Matrix.vecMulVec u v = A + Matrix.vecMulVec (-u) v := by
    ext i j
    simp [Matrix.vecMulVec, sub_eq_add_neg]
  rw [hsub, det_add_vecMulVec, Matrix.mulVec_neg, dotProduct_neg, sub_eq_add_neg]

lemma two_dvd_sum_of_involution {α : Type*} (S : Finset α) (g : α → α) (f : α → ℤ)
    (hclosed : ∀ a ∈ S, g a ∈ S)
    (hinv : ∀ a ∈ S, g (g a) = a)
    (hno_fix : ∀ a ∈ S, g a ≠ a)
    (heq : ∀ a ∈ S, f (g a) = f a) :
    (2 : ℤ) ∣ ∑ a ∈ S, f a := by
  change ((2 : ℕ) : ℤ) ∣ ∑ a ∈ S, f a
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  refine Finset.sum_involution (fun a _ => g a) ?_ ?_ ?_ ?_
  · intro a ha
    rw [heq a ha]
    have h2 : (2 : ZMod 2) = 0 := rfl
    calc
      (f a : ZMod 2) + (f a : ZMod 2) = (2 : ZMod 2) * (f a : ZMod 2) := by ring
      _ = 0 := by rw [h2, zero_mul]
  · intro a ha _
    exact hno_fix a ha
  · intro a ha
    exact hclosed a ha
  · intro a ha
    exact hinv a ha

lemma even_card_of_fixed_point_free_involution {α : Type*} [DecidableEq α]
    (s : Finset α) (g : α → α)
    (hclosed : ∀ x ∈ s, g x ∈ s)
    (hinv : ∀ x ∈ s, g (g x) = x)
    (hno_fix : ∀ x ∈ s, g x ≠ x) :
    Even s.card := by
  rw [even_iff_two_dvd]
  have hdvd : (2 : ℤ) ∣ ∑ _x ∈ s, (1 : ℤ) :=
    two_dvd_sum_of_involution s g (fun _ => 1) hclosed hinv hno_fix (fun _ _ => rfl)
  simpa using Int.ofNat_dvd.mp (by simpa using hdvd)

lemma perm_inv_ne_self_of_odd_moved {n : ℕ} (σ : Equiv.Perm (Fin n))
    (hodd : Odd (Finset.univ.filter (fun r : Fin n => σ r ≠ r)).card) :
    σ⁻¹ ≠ σ := by
  intro heq
  let s : Finset (Fin n) := Finset.univ.filter (fun r => σ r ≠ r)
  have heven : Even s.card := by
    refine even_card_of_fixed_point_free_involution s σ ?_ ?_ ?_
    · intro x hx
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact fun hxx => hx (σ.injective hxx)
    · intro x _
      calc
        σ (σ x) = σ (σ⁻¹ x) := by rw [heq]
        _ = x := σ.apply_symm_apply x
    · intro x hx
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact hx
  exact (Nat.not_odd_iff_even.mpr heven) hodd

/-- Any symmetric integer matrix of odd order with zero diagonal has even determinant. -/
theorem two_dvd_det_of_symm_diag_zero_odd {n : ℕ} (hodd : Odd n)
    {M : Matrix (Fin n) (Fin n) ℤ} (hSymm : Mᵀ = M) (hdiag : ∀ i, M i i = 0) :
    (2 : ℤ) ∣ M.det := by
  rw [Matrix.det_apply]
  let S_der : Finset (Equiv.Perm (Fin n)) :=
    Finset.univ.filter (fun σ => ∀ i : Fin n, σ i ≠ i)
  have hsum : (∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ) • ∏ i, M (σ i) i) =
      ∑ σ ∈ S_der, (Equiv.Perm.sign σ : ℤ) * ∏ i, M (σ i) i := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun σ _ => ?_
    by_cases hder : ∀ i : Fin n, σ i ≠ i
    · split_ifs
      simp only [Units.smul_def, zsmul_eq_mul, Int.cast_id]
    · split_ifs
      push Not at hder
      rcases hder with ⟨i₀, hi₀⟩
      have hzero : (∏ i : Fin n, M (σ i) i) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i₀) (by rw [hi₀, hdiag i₀])
      rw [hzero, smul_zero]
  rw [hsum]
  refine two_dvd_sum_of_involution S_der (fun σ => σ⁻¹)
    (fun σ => (Equiv.Perm.sign σ : ℤ) * ∏ i, M (σ i) i) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [S_der, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    intro i hi
    exact hσ i (σ.symm_apply_eq.mp hi).symm
  · intro σ _
    exact inv_inv σ
  · intro σ hσ
    simp only [S_der, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    apply perm_inv_ne_self_of_odd_moved σ
    have hfilt : Finset.univ.filter (fun r : Fin n => σ r ≠ r) = Finset.univ := by
      ext r; simp [hσ r]
    simpa [hfilt, Fintype.card_fin] using hodd
  · intro σ _
    simp only [Equiv.Perm.sign_inv]
    congr 1
    refine (Fintype.prod_equiv σ (fun i => M (σ i) i) (fun i => M (σ⁻¹ i) i) fun i => ?_).symm
    have hinv : σ⁻¹ (σ i) = i := by simp
    rw [hinv]
    calc
      M (σ i) i = Mᵀ i (σ i) := rfl
      _ = M i (σ i) := by rw [hSymm]

private lemma perm_prod_symm_eq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} (hSymm : Aᵀ = A)
    (i : Fin n) (σ : Equiv.Perm (Fin n)) (hfix : σ i = i) :
    (∏ r ∈ (Finset.univ.erase i).filter (fun r => σ⁻¹ r ≠ r), A (σ⁻¹ r) r) =
      ∏ r ∈ (Finset.univ.erase i).filter (fun r => σ r ≠ r), A (σ r) r := by
  refine Finset.prod_bij (fun r _ => σ⁻¹ r) ?_ ?_ ?_ ?_
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hr ⊢
    refine ⟨?_, ?_⟩
    · intro hri
      apply hr.1
      calc
        r = σ (σ⁻¹ r) := by simp
        _ = σ i := by rw [hri]
        _ = i := hfix
    · intro hfix'
      apply hr.2
      calc
        σ⁻¹ r = σ (σ⁻¹ r) := hfix'.symm
        _ = r := by simp
  · intro a _ b _ hab
    exact σ.symm.injective hab
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hr
    refine ⟨σ r, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
    refine ⟨?_, fun hss => hr.2 (by simpa using hss.symm)⟩
    intro hsi
    apply hr.1
    rw [← hfix] at hsi
    exact σ.injective hsi
  · intro r _
    calc
      A (σ⁻¹ r) r = Aᵀ r (σ⁻¹ r) := rfl
      _ = A r (σ⁻¹ r) := by rw [hSymm]
      _ = A (σ (σ⁻¹ r)) (σ⁻¹ r) := by simp

lemma sum_matrix_symm_split {n : ℕ} {R : Type*} [CommRing R]
    (P : Matrix (Fin n) (Fin n) R) (hP : Pᵀ = P) :
    (∑ i : Fin n, ∑ j : Fin n, P i j) =
      (∑ i : Fin n, P i i) +
        2 * ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), P p.1 p.2 := by
  rw [← Fintype.sum_prod_type' (fun i j => P i j)]
  have hsplit : ∀ p : Fin n × Fin n, P p.1 p.2 =
      (if p.1 = p.2 then P p.1 p.2 else 0) +
      (if p.1 < p.2 then P p.1 p.2 else 0) +
      (if p.2 < p.1 then P p.1 p.2 else 0) := by
    intro p
    rcases lt_trichotomy p.1 p.2 with hlt | heq | hgt
    · simp [hlt, ne_of_lt hlt, not_lt_of_gt hlt]
    · simp [heq]
    · simp [hgt, ne_of_gt hgt, not_lt_of_gt hgt]
  calc
    (∑ p : Fin n × Fin n, P p.1 p.2)
        = ∑ p : Fin n × Fin n, ((if p.1 = p.2 then P p.1 p.2 else 0) +
            (if p.1 < p.2 then P p.1 p.2 else 0) +
            (if p.2 < p.1 then P p.1 p.2 else 0)) := Finset.sum_congr rfl fun p _ => hsplit p
    _ = (∑ p : Fin n × Fin n, if p.1 = p.2 then P p.1 p.2 else 0) +
        (∑ p : Fin n × Fin n, if p.1 < p.2 then P p.1 p.2 else 0) +
        (∑ p : Fin n × Fin n, if p.2 < p.1 then P p.1 p.2 else 0) := by
          simp only [Finset.sum_add_distrib]
    _ = (∑ i : Fin n, P i i) +
        2 * ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), P p.1 p.2 := by
          have h1 : (∑ p : Fin n × Fin n, if p.1 = p.2 then P p.1 p.2 else 0) =
              ∑ i : Fin n, P i i := by
            rw [Fintype.sum_prod_type]
            simp
          have h3 : (∑ p : Fin n × Fin n, if p.2 < p.1 then P p.1 p.2 else 0) =
              ∑ p : Fin n × Fin n, if p.1 < p.2 then P p.1 p.2 else 0 := by
            refine Fintype.sum_equiv (Equiv.prodComm (Fin n) (Fin n)) _ _ fun p => ?_
            simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
            have hsym : P p.2 p.1 = P p.1 p.2 := by
              calc
                P p.2 p.1 = Pᵀ p.1 p.2 := rfl
                _ = P p.1 p.2 := by rw [hP]
            simp [hsym]
          rw [h1, h3, ← Finset.sum_filter]
          ring

private lemma adjugate_two_adic_coeff_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hdiag : ∀ i, A i i = 0) (i j : Fin n) (k : ℕ) :
    ((Matrix.adjugate ((X : ℤ[X]) • (1 : Matrix (Fin n) (Fin n) ℤ[X]) +
        ((2 : ℤ) • A).map (Polynomial.C : ℤ →+* ℤ[X]))) i j).coeff k =
      ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
          σ i = j ∧ ((Finset.univ.erase i).filter (fun r => σ r = r)).card = k),
        (Equiv.Perm.sign σ : ℤ) * (2 : ℤ) ^ (n - 1 - k) *
          ∏ r ∈ (Finset.univ.erase i).filter (fun r => σ r ≠ r), A (σ r) r := by
  let M : Matrix (Fin n) (Fin n) ℤ[X] :=
    (X : ℤ[X]) • (1 : Matrix (Fin n) (Fin n) ℤ[X]) +
      ((2 : ℤ) • A).map (Polynomial.C : ℤ →+* ℤ[X])
  have hM_entry : ∀ a b : Fin n, M a b = if a = b then X else C (2 * A a b) := by
    intro a b
    have hM_def : M = (X : ℤ[X]) • (1 : Matrix (Fin n) (Fin n) ℤ[X]) +
        ((2 : ℤ) • A).map (Polynomial.C : ℤ →+* ℤ[X]) := rfl
    rw [hM_def, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply,
      Matrix.smul_apply, smul_eq_mul, zsmul_eq_mul]
    by_cases hab : a = b
    · subst hab; simp [hdiag a]
    · simp [hab]
  rw [Matrix.adjugate_apply, Matrix.det_apply]
  change (∑ σ : Equiv.Perm (Fin n),
      (Equiv.Perm.sign σ) • ∏ r : Fin n, (M.updateRow j (Pi.single i 1)) (σ r) r).coeff k = _
  rw [← Polynomial.lcoeff_apply, map_sum]
  simp only [Polynomial.lcoeff_apply]
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ • ∏ r : Fin n, (M.updateRow j (Pi.single i 1)) (σ r) r).coeff k) =
        if σ i = j ∧ ((Finset.univ.erase i).filter (fun r => σ r = r)).card = k then
          (Equiv.Perm.sign σ : ℤ) * (2 : ℤ) ^ (n - 1 - k) *
            ∏ r ∈ (Finset.univ.erase i).filter (fun r => σ r ≠ r), A (σ r) r
        else 0 := by
    intro σ
    rw [Units.smul_def, zsmul_eq_mul, ← C_eq_intCast, Int.cast_id, Polynomial.coeff_C_mul]
    by_cases hσ : σ i = j
    · have hprod : (∏ r : Fin n, (M.updateRow j (Pi.single i 1)) (σ r) r) =
          ∏ r ∈ Finset.univ.erase i, M (σ r) r := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
        have hi_val : (M.updateRow j (Pi.single i 1)) (σ i) i = 1 := by
          rw [hσ, Matrix.updateRow_self, Pi.single_eq_same]
        rw [hi_val, one_mul]
        refine Finset.prod_congr rfl fun r hr => ?_
        have hri : r ≠ i := (Finset.mem_erase.mp hr).1
        have hσrj : σ r ≠ j := fun h => hri (σ.injective (h.trans hσ.symm))
        rw [Matrix.updateRow_ne hσrj]
      have hsplit : (∏ r ∈ Finset.univ.erase i, M (σ r) r) =
          C ((2 : ℤ) ^ ((Finset.univ.erase i).filter (fun r => σ r ≠ r)).card *
            ∏ r ∈ (Finset.univ.erase i).filter (fun r => σ r ≠ r), A (σ r) r) *
            X ^ ((Finset.univ.erase i).filter (fun r => σ r = r)).card := by
        rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ.erase i) (fun r => σ r = r)]
        have hfix_prod :
            (∏ r ∈ (Finset.univ.erase i).filter (fun r => σ r = r), M (σ r) r) =
              X ^ ((Finset.univ.erase i).filter (fun r => σ r = r)).card := by
          trans ∏ _r ∈ (Finset.univ.erase i).filter (fun r => σ r = r), (X : ℤ[X])
          · refine Finset.prod_congr rfl fun r hr => ?_
            have hrr : σ r = r := (Finset.mem_filter.mp hr).2
            simp [hrr, hM_entry r r]
          · simp
        have hmov_prod :
            (∏ r ∈ (Finset.univ.erase i).filter (fun r => ¬σ r = r), M (σ r) r) =
              C ((2 : ℤ) ^ ((Finset.univ.erase i).filter (fun r => σ r ≠ r)).card *
                ∏ r ∈ (Finset.univ.erase i).filter (fun r => σ r ≠ r), A (σ r) r) := by
          have hsub :
              (∏ r ∈ (Finset.univ.erase i).filter (fun r => σ r ≠ r), M (σ r) r) =
                ∏ r ∈ (Finset.univ.erase i).filter (fun r => σ r ≠ r), C (2 * A (σ r) r) := by
            refine Finset.prod_congr rfl fun r hr => ?_
            have hne : σ r ≠ r := (Finset.mem_filter.mp hr).2
            simp [hM_entry (σ r) r, hne]
          simp only [ne_eq] at hsub ⊢
          rw [hsub, ← map_prod C, Finset.prod_mul_distrib, Finset.prod_const]
        rw [hfix_prod, hmov_prod, mul_comm]
      rw [hprod, hsplit, Polynomial.coeff_C_mul_X_pow]
      by_cases hk' : ((Finset.univ.erase i).filter (fun r => σ r = r)).card = k
      · have hcard_sum :
            ((Finset.univ.erase i).filter (fun r => σ r = r)).card +
              ((Finset.univ.erase i).filter (fun r => σ r ≠ r)).card = n - 1 := by
          have h := Finset.card_filter_add_card_filter_not
            (s := Finset.univ.erase i) (fun r => σ r = r)
          simpa [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_fin] using h
        have hmov : ((Finset.univ.erase i).filter (fun r => σ r ≠ r)).card = n - 1 - k := by
          omega
        simp only [hσ, hk', and_self, ↓reduceIte, hmov]
        ring
      · simp only [hσ, hk', Ne.symm hk', and_false, ↓reduceIte, mul_zero]
    · have hzero : (∏ r : Fin n, (M.updateRow j (Pi.single i 1)) (σ r) r) = 0 := by
        have hσj : σ (σ⁻¹ j) = j := by simp
        have hr0 : σ⁻¹ j ≠ i := fun h => hσ (by rw [← h]; exact hσj)
        refine Finset.prod_eq_zero (Finset.mem_univ (σ⁻¹ j)) ?_
        rw [hσj, Matrix.updateRow_self, Pi.single_eq_of_ne hr0]
      simp [hzero, hσ]
  simp_rw [hterm]
  rw [Finset.sum_filter]

/-- Core 2-adic coefficient theorem for `(X • 1 + (2 • A).map C - J).det` where `A` is symmetric
with zero diagonal over `ℤ`. -/
theorem seidel_shifted_charpoly_two_adic_aux {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    (hSymm : Aᵀ = A) (hdiag : ∀ i, A i i = 0) (k : ℕ) (hk : k ≤ n) :
    (2 : ℤ) ^ (2 * ((n - k) / 2)) ∣
      (((X : ℤ[X]) • (1 : Matrix (Fin n) (Fin n) ℤ[X]) +
        ((2 : ℤ) • A).map (Polynomial.C : ℤ →+* ℤ[X]) -
        Matrix.vecMulVec (fun _ => (1 : ℤ[X])) (fun _ => (1 : ℤ[X]))).det).coeff k := by
  let M : Matrix (Fin n) (Fin n) ℤ[X] :=
    (X : ℤ[X]) • (1 : Matrix (Fin n) (Fin n) ℤ[X]) +
      ((2 : ℤ) • A).map (Polynomial.C : ℤ →+* ℤ[X])
  have hM_symm : Mᵀ = M := by
    ext i j
    simp only [M, Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.map_apply, smul_eq_mul, eq_comm]
    have hij : A j i = A i j := by
      calc
        A j i = Aᵀ i j := rfl
        _ = A i j := by rw [hSymm]
    rw [hij]
  have hM_entry : ∀ i j : Fin n, M i j = if i = j then X else C (2 * A i j) := by
    intro i j
    have hM_def : M = (X : ℤ[X]) • (1 : Matrix (Fin n) (Fin n) ℤ[X]) +
        ((2 : ℤ) • A).map (Polynomial.C : ℤ →+* ℤ[X]) := rfl
    rw [hM_def, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply,
      Matrix.smul_apply, smul_eq_mul, zsmul_eq_mul]
    by_cases hij : i = j
    · subst hij; simp [hdiag i]
    · simp [hij]
  rw [det_sub_vecMulVec, Polynomial.coeff_sub]
  apply dvd_sub
  · rw [Matrix.det_apply]
    change (2 : ℤ) ^ (2 * ((n - k) / 2)) ∣
      (∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ) • ∏ i : Fin n, M (σ i) i).coeff k
    rw [← Polynomial.lcoeff_apply, map_sum]
    simp only [Polynomial.lcoeff_apply]
    apply Finset.dvd_sum
    intro σ _
    rw [Units.smul_def, zsmul_eq_mul, ← C_eq_intCast, Int.cast_id, Polynomial.coeff_C_mul]
    let fixSet : Finset (Fin n) := Finset.univ.filter (fun i => σ i = i)
    let movSet : Finset (Fin n) := Finset.univ.filter (fun i => σ i ≠ i)
    have hsplit : (∏ i : Fin n, M (σ i) i) =
        C ((2 : ℤ) ^ movSet.card * ∏ i ∈ movSet, A (σ i) i) * X ^ fixSet.card := by
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => σ i = i)]
      have hfix : (∏ i ∈ fixSet, M (σ i) i) = X ^ fixSet.card := by
        trans ∏ _i ∈ fixSet, (X : ℤ[X])
        · refine Finset.prod_congr rfl fun i hi => ?_
          have hii : σ i = i := (Finset.mem_filter.mp hi).2
          simp [hii, hM_entry i i]
        · simp
      have hmov : (∏ i ∈ Finset.univ.filter (fun i => ¬σ i = i), M (σ i) i) =
          C ((2 : ℤ) ^ movSet.card * ∏ i ∈ movSet, A (σ i) i) := by
        have hsub : (∏ i ∈ movSet, M (σ i) i) = ∏ i ∈ movSet, C (2 * A (σ i) i) := by
          refine Finset.prod_congr rfl fun i hi => ?_
          have hne : σ i ≠ i := (Finset.mem_filter.mp hi).2
          simp [hM_entry (σ i) i, hne]
        change (∏ i ∈ movSet, M (σ i) i) = _
        rw [hsub, ← map_prod C, Finset.prod_mul_distrib, Finset.prod_const]
      rw [hfix, hmov, mul_comm]
    rw [hsplit, Polynomial.coeff_C_mul_X_pow]
    by_cases hk' : fixSet.card = k
    · have hcard : fixSet.card + movSet.card = n := by
        simpa [fixSet, movSet, Fintype.card_fin] using
          Finset.card_filter_add_card_filter_not
            (s := (Finset.univ : Finset (Fin n))) (fun i => σ i = i)
      have hmov : movSet.card = n - k := by omega
      simp only [hk', ↓reduceIte, hmov]
      refine dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (pow_dvd_pow 2 (by omega)) _) _
    · simp only [Ne.symm hk', ↓reduceIte, mul_zero]
      exact dvd_zero _
  · have hdot : ((fun _ : Fin n => (1 : ℤ[X])) ⬝ᵥ (M.adjugate *ᵥ (fun _ => (1 : ℤ[X])))) =
        ∑ i : Fin n, ∑ j : Fin n, M.adjugate i j := by
      simp [dotProduct, Matrix.mulVec]
    have hadj_symm : (Matrix.adjugate M)ᵀ = Matrix.adjugate M := by
      rw [Matrix.adjugate_transpose, hM_symm]
    have h2C : (2 : ℤ[X]) = C (2 : ℤ) := by simp
    change (2 : ℤ) ^ (2 * ((n - k) / 2)) ∣
      (((fun _ : Fin n => (1 : ℤ[X])) ⬝ᵥ (M.adjugate *ᵥ (fun _ => (1 : ℤ[X])))).coeff k)
    rw [hdot, sum_matrix_symm_split _ hadj_symm, Polynomial.coeff_add, h2C, Polynomial.coeff_C_mul,
      ← Polynomial.lcoeff_apply, map_sum, ← Polynomial.lcoeff_apply, map_sum]
    simp only [Polynomial.lcoeff_apply]
    apply dvd_add
    · apply Finset.dvd_sum
      intro i _
      rw [adjugate_two_adic_coeff_eq A hdiag i i k]
      by_cases hkn : k = n
      · have hempty : Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
            σ i = i ∧ ((Finset.univ.erase i).filter (fun r => σ r = r)).card = k) = ∅ := by
          ext σ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          rintro ⟨_, hcard⟩
          have hle : ((Finset.univ.erase i).filter (fun r => σ r = r)).card ≤ n - 1 := by
            calc
              ((Finset.univ.erase i).filter (fun r => σ r = r)).card
                  ≤ (Finset.univ.erase i).card := Finset.card_filter_le _ _
              _ = n - 1 := by simp [Finset.card_erase_of_mem (Finset.mem_univ i)]
          have hpos : 0 < n := i.pos
          omega
        rw [hempty, Finset.sum_empty]
        exact dvd_zero _
      · have hkn_lt : k < n := lt_of_le_of_ne hk hkn
        let S_k : Finset (Equiv.Perm (Fin n)) :=
          Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
            σ i = i ∧ ((Finset.univ.erase i).filter (fun r => σ r = r)).card = k)
        have hfactor :
            (∑ σ ∈ S_k, (Equiv.Perm.sign σ : ℤ) * (2 : ℤ) ^ (n - 1 - k) *
                ∏ r ∈ (Finset.univ.erase i).filter (fun r => σ r ≠ r), A (σ r) r) =
              (2 : ℤ) ^ (n - 1 - k) *
                ∑ σ ∈ S_k, (Equiv.Perm.sign σ : ℤ) *
                  ∏ r ∈ (Finset.univ.erase i).filter (fun r => σ r ≠ r), A (σ r) r := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun σ _ => by ring
        change (2 : ℤ) ^ (2 * ((n - k) / 2)) ∣
          ∑ σ ∈ S_k, (Equiv.Perm.sign σ : ℤ) * (2 : ℤ) ^ (n - 1 - k) *
            ∏ r ∈ (Finset.univ.erase i).filter (fun r => σ r ≠ r), A (σ r) r
        rw [hfactor]
        rcases Nat.even_or_odd (n - k) with heven | hodd
        · have ⟨m, hm⟩ := heven
          have hexp : 2 * ((n - k) / 2) = (n - 1 - k) + 1 := by omega
          rw [hexp, pow_succ]
          apply mul_dvd_mul_left
          refine two_dvd_sum_of_involution S_k (fun σ => σ⁻¹)
            (fun σ => (Equiv.Perm.sign σ : ℤ) *
              ∏ r ∈ (Finset.univ.erase i).filter (fun r => σ r ≠ r), A (σ r) r) ?_ ?_ ?_ ?_
          · intro σ hσ
            simp only [S_k, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
            refine ⟨σ.inv_eq_iff_eq.mpr hσ.1.symm, ?_⟩
            rw [← hσ.2]
            congr 1
            ext r
            simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
            exact and_congr_right fun _ => σ.inv_eq_iff_eq.trans eq_comm
          · intro σ _
            exact inv_inv σ
          · intro σ hσ
            simp only [S_k, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
            apply perm_inv_ne_self_of_odd_moved σ
            have hmov_eq : Finset.univ.filter (fun r : Fin n => σ r ≠ r) =
                (Finset.univ.erase i).filter (fun r => σ r ≠ r) := by
              ext r
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
              constructor
              · intro hr
                exact ⟨fun hri => hr (by rw [hri, hσ.1]), hr⟩
              · exact fun hr => hr.2
            rw [hmov_eq]
            have hsum_card :
                ((Finset.univ.erase i).filter (fun r => σ r = r)).card +
                  ((Finset.univ.erase i).filter (fun r => σ r ≠ r)).card = n - 1 := by
              simpa [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_fin] using
                Finset.card_filter_add_card_filter_not
                  (s := Finset.univ.erase i) (fun r => σ r = r)
            rw [hσ.2] at hsum_card
            have hcard_eq : ((Finset.univ.erase i).filter (fun r => σ r ≠ r)).card = n - 1 - k := by
              omega
            rw [hcard_eq]
            rcases heven with ⟨m, hm⟩
            refine ⟨m - 1, by omega⟩
          · intro σ hσ
            simp only [S_k, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
            simp only [Equiv.Perm.sign_inv]
            congr 1
            exact perm_prod_symm_eq hSymm i σ hσ.1
        · have hexp : 2 * ((n - k) / 2) = n - 1 - k := by
            rcases hodd with ⟨m, hm⟩
            omega
          rw [hexp]
          exact dvd_mul_right _ _
    · rw [Finset.mul_sum]
      apply Finset.dvd_sum
      intro p _
      rw [adjugate_two_adic_coeff_eq A hdiag p.1 p.2 k]
      by_cases hkn : k = n
      · have hempty : Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
            σ p.1 = p.2 ∧ ((Finset.univ.erase p.1).filter (fun r => σ r = r)).card = k) = ∅ := by
          ext σ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          rintro ⟨_, hcard⟩
          have hle : ((Finset.univ.erase p.1).filter (fun r => σ r = r)).card ≤ n - 1 := by
            calc
              ((Finset.univ.erase p.1).filter (fun r => σ r = r)).card
                  ≤ (Finset.univ.erase p.1).card := Finset.card_filter_le _ _
              _ = n - 1 := by simp [Finset.card_erase_of_mem (Finset.mem_univ p.1)]
          have hpos : 0 < n := p.1.pos
          omega
        rw [hempty, Finset.sum_empty, mul_zero]
        exact dvd_zero _
      · have hkn_lt : k < n := lt_of_le_of_ne hk hkn
        rw [Finset.mul_sum]
        apply Finset.dvd_sum
        intro σ _
        have hdvd_pow : (2 : ℤ) ^ (2 * ((n - k) / 2)) ∣ (2 : ℤ) ^ (n - k) :=
          pow_dvd_pow 2 (by omega)
        refine dvd_trans hdvd_pow ?_
        have hexp : (2 : ℤ) ^ (n - k) = 2 * (2 : ℤ) ^ (n - 1 - k) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [hexp]
        have hmul : 2 * ((Equiv.Perm.sign σ : ℤ) * (2 : ℤ) ^ (n - 1 - k) *
            ∏ r ∈ (Finset.univ.erase p.1).filter (fun r => σ r ≠ r), A (σ r) r) =
            (2 * (2 : ℤ) ^ (n - 1 - k)) * ((Equiv.Perm.sign σ : ℤ) *
              ∏ r ∈ (Finset.univ.erase p.1).filter (fun r => σ r ≠ r), A (σ r) r) := by
          ring
        rw [hmul]
        exact dvd_mul_right _ _

/-- 2-adic divisibility of the coefficients of `S.charpoly.comp (X - C 1)` for any Seidel matrix `S`. -/
theorem seidel_shifted_charpoly_two_adic {n : ℕ} {S : Matrix (Fin n) (Fin n) ℤ}
    (hS : IsSeidelMatrix S) {k : ℕ} (hk : k ≤ n) :
    (2 : ℤ) ^ (2 * ((n - k) / 2)) ∣ (S.charpoly.comp (X - C (1 : ℤ))).coeff k := by
  let A : Matrix (Fin n) (Fin n) ℤ := Matrix.of (fun i j => if i = j then 0 else (1 - S i j) / 2)
  have hSymm : Aᵀ = A := by
    ext i j
    simp only [A, Matrix.transpose_apply, Matrix.of_apply, eq_comm]
    have hSij : S j i = S i j := by
      calc
        S j i = Sᵀ i j := rfl
        _ = S i j := by rw [seidel_symm hS]
    rw [hSij]
  have hdiag : ∀ i, A i i = 0 := fun i => by simp [A]
  have hcomp : S.charpoly.comp (X - C (1 : ℤ)) =
      ((X : ℤ[X]) • (1 : Matrix (Fin n) (Fin n) ℤ[X]) +
        ((2 : ℤ) • A).map (Polynomial.C : ℤ →+* ℤ[X]) -
        Matrix.vecMulVec (fun _ => (1 : ℤ[X])) (fun _ => (1 : ℤ[X]))).det := by
    rw [← charpoly_add_smul_one S 1, Matrix.charpoly]
    congr 1
    refine Matrix.ext fun i j => ?_
    let Lmat : Matrix (Fin n) (Fin n) ℤ := (1 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) + S
    have hLij : Lmat i j = (if i = j then 1 else 0) + S i j := by
      simp [Lmat, Matrix.one_apply]
    have hL : Lmat.charmatrix i j = (if i = j then X - 1 else C (-S i j)) := by
      rw [charmatrix, Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
        RingHom.mapMatrix_apply, Matrix.map_apply, hLij]
      by_cases hij : i = j <;> simp [hij, hS.2.1]
    let Rmat : Matrix (Fin n) (Fin n) ℤ[X] :=
      (X : ℤ[X]) • (1 : Matrix (Fin n) (Fin n) ℤ[X]) +
        ((2 : ℤ) • A).map (Polynomial.C : ℤ →+* ℤ[X]) -
        Matrix.vecMulVec (fun _ => (1 : ℤ[X])) (fun _ => (1 : ℤ[X]))
    have hR : Rmat i j = (if i = j then X - 1 else C (2 * A i j - 1)) := by
      rw [show Rmat i j = ((X : ℤ[X]) • (1 : Matrix (Fin n) (Fin n) ℤ[X])) i j +
          (((2 : ℤ) • A).map (Polynomial.C : ℤ →+* ℤ[X])) i j -
          (Matrix.vecMulVec (fun _ => (1 : ℤ[X])) (fun _ => (1 : ℤ[X]))) i j from rfl,
        Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply, Matrix.smul_apply,
        Matrix.vecMulVec_apply, smul_eq_mul, zsmul_eq_mul]
      by_cases hij : i = j
      · subst hij; simp [hdiag i]
      · simp [hij, map_sub]
    change Lmat.charmatrix i j = Rmat i j
    rw [hL, hR]
    by_cases hij : i = j
    · simp [hij]
    · simp only [hij, ↓reduceIte]
      rcases hS.2.2 i j hij with h | h <;> simp [A, hij, h]
  rw [hcomp]
  exact seidel_shifted_charpoly_two_adic_aux hSymm hdiag k hk

/-- Stronger 2-adic divisibility when `n - k` is even (in particular, `2^n ∣ S.charpoly.eval (-1)`
when `Even n`). -/
theorem seidel_shifted_charpoly_two_adic_even {n : ℕ} {S : Matrix (Fin n) (Fin n) ℤ}
    (hS : IsSeidelMatrix S) {k : ℕ} (hk : k ≤ n) (heven : Even (n - k)) :
    (2 : ℤ) ^ (n - k) ∣ (S.charpoly.comp (X - C (1 : ℤ))).coeff k := by
  have h := seidel_shifted_charpoly_two_adic hS hk
  rcases heven with ⟨m, hm⟩
  have h2 : 2 * ((n - k) / 2) = n - k := by omega
  rwa [h2] at h

/-- For any Seidel matrix `S` of order `n ≥ 1`, `C (2 ^ (n - 1))` divides `S.charpoly.comp (C 2 * X - 1)`. -/
theorem two_pow_sub_one_dvd_charpoly_two_mul_sub_one {n : ℕ} (hn : 1 ≤ n)
    {S : Matrix (Fin n) (Fin n) ℤ} (hS : IsSeidelMatrix S) :
    C ((2 : ℤ) ^ (n - 1)) ∣ S.charpoly.comp (C 2 * X - 1) := by
  let P : ℤ[X] := S.charpoly.comp (X - C (1 : ℤ))
  have hcomp : S.charpoly.comp (C 2 * X - 1) = P.comp (C 2 * X) := by
    simp only [P, Polynomial.comp_assoc, sub_comp, X_comp, C_comp, ← Polynomial.C_1]
  rw [hcomp, Polynomial.C_dvd_iff_dvd_coeff]
  have hP_deg : P.natDegree ≤ n := by
    calc
      P.natDegree = S.charpoly.natDegree * (X - C (1 : ℤ)).natDegree := Polynomial.natDegree_comp
      _ = n * 1 := by
          rw [(Matrix.charpoly_natDegree_eq_dim S).trans (Fintype.card_fin n), natDegree_X_sub_C]
      _ = n := mul_one n
      _ ≤ n := le_rfl
  have hcoeff_eq : ∀ k : ℕ, (P.comp (C 2 * X)).coeff k = 2 ^ k * P.coeff k := by
    intro k
    conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow P]
    rw [Polynomial.sum_comp, ← Polynomial.lcoeff_apply, map_sum]
    simp only [Polynomial.lcoeff_apply, mul_comp, C_comp, pow_comp, X_comp]
    have hmul : ∀ j : ℕ, (C (P.coeff j) * (C (2 : ℤ) * X) ^ j).coeff k =
        if j = k then 2 ^ k * P.coeff k else 0 := by
      intro j
      rw [mul_pow, ← C_pow, ← mul_assoc, ← C_mul, Polynomial.coeff_C_mul_X_pow]
      by_cases hjk : j = k
      · subst hjk; simp [mul_comm]
      · simp [hjk, Ne.symm hjk]
    simp_rw [hmul]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_range]
    split_ifs with hlt
    · rfl
    · have hzero : P.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp [hzero]
  intro k
  rw [hcoeff_eq k]
  by_cases hk : k ≤ n
  · have h2 := seidel_shifted_charpoly_two_adic hS hk
    have hdvd_pow : (2 : ℤ) ^ (n - 1) ∣ (2 : ℤ) ^ k * (2 : ℤ) ^ (2 * ((n - k) / 2)) := by
      rw [← pow_add]
      exact pow_dvd_pow 2 (by omega)
    exact dvd_trans hdvd_pow (mul_dvd_mul_left _ h2)
  · have hzero : P.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp [hzero]

private lemma monic_dvd_mul_pow_two {m : ℕ} {M R : ℤ[X]} (hM : M.Monic)
    (hdvd : C ((2 : ℤ) ^ m) ∣ M * R) :
    C ((2 : ℤ) ^ m) ∣ R := by
  induction m generalizing R with
  | zero => simp
  | @succ m ih =>
    have h2 : C (2 : ℤ) ∣ M * R :=
      dvd_trans (by rw [pow_succ', C_mul]; exact dvd_mul_right _ _) hdvd
    have hmap : (M * R).map (Int.castRingHom (ZMod 2)) = 0 := by
      rcases h2 with ⟨T, hT⟩
      rw [hT, Polynomial.map_mul]
      have hC2 : (C (2 : ℤ)).map (Int.castRingHom (ZMod 2)) = 0 := by
        rw [Polynomial.map_C]
        have h0 : (Int.castRingHom (ZMod 2)) 2 = 0 := rfl
        rw [h0, map_zero]
      rw [hC2, zero_mul]
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

/-- If `S.charpoly = (X + C 5)^(n - d) * Q` with `1 ≤ d ≤ n`, then `C (2 ^ (d - 1))` divides
`Q.comp (C 2 * X - 1)` in `ℤ[X]`, and `(2 : ℤ)^(d - 1 - j)` divides `(Q.comp (X - C 1)).coeff j`
for all `j ≤ d - 1`. -/
theorem two_pow_factor_dvd_cofactor_comp {n d : ℕ} (hd1 : 1 ≤ d) (hdn : d ≤ n)
    {S : Matrix (Fin n) (Fin n) ℤ} (hS : IsSeidelMatrix S)
    {Q : ℤ[X]} (hQ : S.charpoly = (X + C (5 : ℤ)) ^ (n - d) * Q) :
    C ((2 : ℤ) ^ (d - 1)) ∣ Q.comp (C 2 * X - 1) ∧
      ∀ j ≤ d - 1, (2 : ℤ) ^ (d - 1 - j) ∣ (Q.comp (X - C (1 : ℤ))).coeff j := by
  have hn1 : 1 ≤ n := le_trans hd1 hdn
  have hdvdS := two_pow_sub_one_dvd_charpoly_two_mul_sub_one hn1 hS
  have hcomp_prod : S.charpoly.comp (C 2 * X - 1) =
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
  rw [hcomp_prod] at hdvdS
  have hC_dvd : C ((2 : ℤ) ^ (d - 1)) ∣ (X + C (2 : ℤ)) ^ (n - d) * Q.comp (C 2 * X - 1) := by
    rcases hdvdS with ⟨T, hT⟩
    have hsplit_exp : (2 : ℤ) ^ (n - 1) = (2 : ℤ) ^ (n - d) * (2 : ℤ) ^ (d - 1) := by
      rw [← pow_add]
      congr 1
      omega
    have hT' : C ((2 : ℤ) ^ (n - d)) * ((X + C 2) ^ (n - d) * Q.comp (C 2 * X - 1)) =
        C ((2 : ℤ) ^ (n - d)) * (C ((2 : ℤ) ^ (d - 1)) * T) := by
      calc
        C ((2 : ℤ) ^ (n - d)) * ((X + C 2) ^ (n - d) * Q.comp (C 2 * X - 1))
            = C ((2 : ℤ) ^ (n - 1)) * T := hT
        _ = C ((2 : ℤ) ^ (n - d)) * (C ((2 : ℤ) ^ (d - 1)) * T) := by
            rw [hsplit_exp, C_mul, mul_assoc]
    have hne : C ((2 : ℤ) ^ (n - d)) ≠ (0 : ℤ[X]) := by simp
    exact ⟨T, mul_left_cancel₀ hne hT'⟩
  have hmon : ((X + C (2 : ℤ)) ^ (n - d)).Monic := (monic_X_add_C (2 : ℤ)).pow (n - d)
  have hdvdQ := monic_dvd_mul_pow_two hmon hC_dvd
  refine ⟨hdvdQ, fun j hj => ?_⟩
  let Q₁ : ℤ[X] := Q.comp (X - C (1 : ℤ))
  have hQ₁_comp : Q.comp (C 2 * X - 1) = Q₁.comp (C 2 * X) := by
    simp only [Q₁, Polynomial.comp_assoc, sub_comp, X_comp, C_comp, ← Polynomial.C_1]
  have hQ₁_coeff : (Q₁.comp (C 2 * X)).coeff j = (2 : ℤ) ^ j * Q₁.coeff j := by
    conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow Q₁]
    rw [Polynomial.sum_comp, ← Polynomial.lcoeff_apply, map_sum]
    simp only [Polynomial.lcoeff_apply, mul_comp, C_comp, pow_comp, X_comp]
    have hmul : ∀ i : ℕ, (C (Q₁.coeff i) * (C (2 : ℤ) * X) ^ i).coeff j =
        if i = j then (2 : ℤ) ^ j * Q₁.coeff j else 0 := by
      intro i
      rw [mul_pow, ← C_pow, ← mul_assoc, ← C_mul, Polynomial.coeff_C_mul_X_pow]
      by_cases hij : i = j
      · subst hij; simp [mul_comm]
      · simp [hij, Ne.symm hij]
    simp_rw [hmul]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_range]
    split_ifs with hlt
    · rfl
    · have hzero : Q₁.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp [hzero]
  have hdvd_j : (2 : ℤ) ^ (d - 1) ∣ (Q₁.comp (C 2 * X)).coeff j := by
    rw [← hQ₁_comp]
    exact (Polynomial.C_dvd_iff_dvd_coeff _ _).mp hdvdQ j
  rw [hQ₁_coeff] at hdvd_j
  have hsplit : (2 : ℤ) ^ (d - 1) = (2 : ℤ) ^ j * (2 : ℤ) ^ (d - 1 - j) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit] at hdvd_j
  exact (mul_dvd_mul_iff_left (pow_ne_zero j (by norm_num))).mp hdvd_j

end TwoAdic

/-! ## Section 3: Jacobi's complementary-minor identity and vertex-deletion formulas -/

section Jacobi

/-- Existence of a complementary embedding `Fin (n - 2) ↪ Fin n` and block equivalence
`Fin 2 ⊕ Fin (n - 2) ≃ Fin n` isolating a distinct pair `i ≠ j`. -/
theorem exists_compl_equiv_pair {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    ∃ (f : Fin (n - 2) ↪ Fin n) (e : Fin 2 ⊕ Fin (n - 2) ≃ Fin n),
      e (Sum.inl 0) = i ∧ e (Sum.inl 1) = j ∧ ∀ t : Fin (n - 2), e (Sum.inr t) = f t := by
  let s : Finset (Fin n) := (Finset.univ.erase i).erase j
  have hjs : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  have hcard_s : Fintype.card s = n - 2 := by
    rw [Fintype.card_coe, Finset.card_erase_of_mem hjs, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_fin]
    omega
  let es : Fin (n - 2) ≃ s := (Fintype.equivFinOfCardEq hcard_s).symm
  let f : Fin (n - 2) ↪ Fin n := es.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩
  have hf_ne : ∀ t, f t ≠ i ∧ f t ≠ j := by
    intro t
    have ht : (es t).1 ∈ s := (es t).2
    simp only [s, Finset.mem_erase, Finset.mem_univ, and_true] at ht
    exact ⟨ht.2, ht.1⟩
  let g : Fin 2 ⊕ Fin (n - 2) → Fin n := Sum.elim ![i, j] f
  have hg_inj : Function.Injective g := by
    rintro (a | a) (b | b) hab
    · fin_cases a <;> fin_cases b
      · rfl
      · exact False.elim (hij hab)
      · exact False.elim (hij hab.symm)
      · rfl
    · fin_cases a
      · exact False.elim ((hf_ne b).1 hab.symm)
      · exact False.elim ((hf_ne b).2 hab.symm)
    · fin_cases b
      · exact False.elim ((hf_ne a).1 hab)
      · exact False.elim ((hf_ne a).2 hab)
    · exact congrArg Sum.inr (f.injective hab)
  have h2n : 2 ≤ n := by
    have hsub : ({i, j} : Finset (Fin n)).card ≤ (Finset.univ : Finset (Fin n)).card :=
      Finset.card_le_univ _
    simpa [Finset.card_pair hij, Finset.card_fin] using hsub
  have hcard_eq : Fintype.card (Fin 2 ⊕ Fin (n - 2)) = Fintype.card (Fin n) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  let e : Fin 2 ⊕ Fin (n - 2) ≃ Fin n :=
    Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hg_inj, hcard_eq⟩)
  refine ⟨f, e, rfl, rfl, fun t => rfl⟩

/-- **Jacobi's 2 × 2 complementary-minor identity** over any commutative ring `R`:
`adjugate B i i * adjugate B j j - adjugate B i j * adjugate B j i = B.det * (B.submatrix f f).det`. -/
theorem jacobi_complementary_minor {n : ℕ} {R : Type*} [CommRing R]
    (B : Matrix (Fin n) (Fin n) R) {i j : Fin n} (_hij : i ≠ j)
    (f : Fin (n - 2) ↪ Fin n) (e : Fin 2 ⊕ Fin (n - 2) ≃ Fin n)
    (he0 : e (Sum.inl 0) = i) (he1 : e (Sum.inl 1) = j) (her : ∀ t, e (Sum.inr t) = f t) :
    Matrix.adjugate B i i * Matrix.adjugate B j j -
        Matrix.adjugate B i j * Matrix.adjugate B j i =
      B.det * (B.submatrix f f).det := by
  let M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) ℤ) :=
    Matrix.mvPolynomialX (Fin n) (Fin n) ℤ
  let C : Matrix (Fin 2 ⊕ Fin (n - 2)) (Fin 2 ⊕ Fin (n - 2)) (MvPolynomial (Fin n × Fin n) ℤ) :=
    M.submatrix e e
  let W : Matrix (Fin 2 ⊕ Fin (n - 2)) (Fin 2 ⊕ Fin (n - 2)) (MvPolynomial (Fin n × Fin n) ℤ) :=
    Matrix.fromBlocks ((Matrix.adjugate C).submatrix Sum.inl Sum.inl) 0
      ((Matrix.adjugate C).submatrix Sum.inr Sum.inl) 1
  have hCW : C * W = Matrix.fromBlocks (C.det • 1) (C.submatrix Sum.inl Sum.inr)
      0 (C.submatrix Sum.inr Sum.inr) := by
    refine Matrix.ext fun a b => ?_
    rcases b with b | b
    · have hcol : (C * W) a (Sum.inl b) = (C * Matrix.adjugate C) a (Sum.inl b) := by
        simp only [Matrix.mul_apply, Fintype.sum_sum_type, W, Matrix.fromBlocks_apply₁₁,
          Matrix.fromBlocks_apply₂₁, Matrix.submatrix_apply]
      rw [hcol, Matrix.mul_adjugate C]
      rcases a with a | a
      · rw [Matrix.smul_apply, Matrix.one_apply, Matrix.fromBlocks_apply₁₁, Matrix.smul_apply,
          Matrix.one_apply]
        by_cases hab : a = b <;> simp [hab]
      · rw [Matrix.smul_apply, Matrix.one_apply, Matrix.fromBlocks_apply₂₁]
        simp
    · simp only [Matrix.mul_apply, Fintype.sum_sum_type, W, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, zero_add,
        Matrix.one_apply, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      cases a <;> rfl
  have hdet_CW := congrArg Matrix.det hCW
  rw [Matrix.det_mul] at hdet_CW
  have hdet_W : W.det = ((Matrix.adjugate C).submatrix Sum.inl Sum.inl).det := by
    simp only [W, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]
  have hdet_RHS :
      (Matrix.fromBlocks (C.det • (1 : Matrix (Fin 2) (Fin 2) _)) (C.submatrix Sum.inl Sum.inr)
        0 (C.submatrix Sum.inr Sum.inr)).det =
      C.det ^ 2 * (C.submatrix Sum.inr Sum.inr).det := by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one]
  rw [hdet_W, hdet_RHS] at hdet_CW
  have hC_det : C.det = M.det := Matrix.det_submatrix_equiv_self e M
  have hC_ne : C.det ≠ 0 := by
    rw [hC_det]
    have : Nonempty (Fin n) := ⟨i⟩
    exact Matrix.det_mvPolynomialX_ne_zero (Fin n) ℤ
  have hM_jac : ((Matrix.adjugate C).submatrix Sum.inl Sum.inl).det =
      C.det * (C.submatrix Sum.inr Sum.inr).det := by
    apply mul_left_cancel₀ hC_ne
    calc
      C.det * ((Matrix.adjugate C).submatrix Sum.inl Sum.inl).det
          = C.det ^ 2 * (C.submatrix Sum.inr Sum.inr).det := hdet_CW
      _ = C.det * (C.det * (C.submatrix Sum.inr Sum.inr).det) := by ring
  rw [Matrix.det_fin_two] at hM_jac
  have hadjC : Matrix.adjugate C = (Matrix.adjugate M).submatrix e e :=
    Matrix.adjugate_submatrix_equiv_self e M
  simp only [hadjC, Matrix.submatrix_apply, he0, he1, hC_det] at hM_jac
  have hsub_eq : C.submatrix Sum.inr Sum.inr = M.submatrix f f := by
    ext a b
    simp [C, her]
  rw [hsub_eq] at hM_jac
  let φ : MvPolynomial (Fin n × Fin n) ℤ →+* R :=
    (MvPolynomial.aeval (fun p : Fin n × Fin n => B p.1 p.2)).toRingHom
  have hmap_M : M.map φ = B := by
    ext a b
    simp [M, φ, Matrix.mvPolynomialX_apply]
  have hadj_entry : ∀ a b : Fin n, φ (M.adjugate a b) = B.adjugate a b := fun a b => by
    have hadj : (M.adjugate).map φ = B.adjugate := by
      change φ.mapMatrix M.adjugate = B.adjugate
      rw [RingHom.map_adjugate, RingHom.mapMatrix_apply, hmap_M]
    rw [← hadj, Matrix.map_apply]
  have hsub_map : ((M.submatrix f f).map φ) = B.submatrix f f := by
    ext a b
    simp only [Matrix.map_apply, Matrix.submatrix_apply]
    simpa using congrArg (fun X => X (f a) (f b)) hmap_M
  have hres := congrArg φ hM_jac
  simp only [map_sub, map_mul, RingHom.map_det, hadj_entry] at hres
  simpa [hmap_M, hsub_map] using hres

/-- A diagonal cofactor of `charmatrix A` equals the characteristic polynomial of the
corresponding vertex-deleted principal submatrix. -/
theorem charmatrix_adjugate_diag {n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin n) (Fin n) R) (i : Fin n) (f : Fin (n - 1) ↪ Fin n)
    (hf : ∀ t : Fin (n - 1), f t ≠ i) :
    Matrix.adjugate (charmatrix A) i i = (A.submatrix f f).charpoly := by
  let g : Fin 1 ⊕ Fin (n - 1) → Fin n := Sum.elim (fun _ => i) f
  have hg_inj : Function.Injective g := by
    rintro (a | a) (b | b) hab
    · fin_cases a; fin_cases b; rfl
    · exact False.elim ((hf b) hab.symm)
    · exact False.elim ((hf a) hab)
    · exact congrArg Sum.inr (f.injective hab)
  have hpos : 1 ≤ n := i.pos
  have hcard : Fintype.card (Fin 1 ⊕ Fin (n - 1)) = Fintype.card (Fin n) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  let e : Fin 1 ⊕ Fin (n - 1) ≃ Fin n :=
    Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hg_inj, hcard⟩)
  rw [Matrix.adjugate_apply, ← Matrix.det_submatrix_equiv_self e]
  let L : Matrix (Fin (n - 1)) (Fin 1) R[X] := fun t _ => (charmatrix A) (f t) i
  have hblk : ((charmatrix A).updateRow i (Pi.single i 1)).submatrix e e =
      Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) R[X]) 0 L (charmatrix (A.submatrix f f)) := by
    refine Matrix.ext fun a b => ?_
    rcases a with a | a <;> rcases b with b | b
    · fin_cases a; fin_cases b
      simp [e, g, Matrix.submatrix_apply, Matrix.updateRow_self, Pi.single_eq_same]
    · fin_cases a
      simp [e, g, Matrix.submatrix_apply, Matrix.updateRow_self, Pi.single_eq_of_ne (hf b)]
    · fin_cases b
      rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁]
      change ((charmatrix A).updateRow i (Pi.single i 1)) (f a) i = (charmatrix A) (f a) i
      rw [Matrix.updateRow_ne (hf a)]
    · simp only [e, g, Equiv.ofBijective_apply, Sum.elim_inr, Matrix.submatrix_apply,
        Matrix.fromBlocks_apply₂₂]
      rw [Matrix.updateRow_ne (hf a)]
      by_cases hab : a = b
      · subst hab; simp [charmatrix]
      · simp [charmatrix, hab, f.injective.ne hab]
  rw [hblk, Matrix.det_fromBlocks_zero₁₂ 1 L (charmatrix (A.submatrix f f)), Matrix.det_one, one_mul]
  rfl

/-- Derivative of `A.charpoly` as the sum of diagonal cofactors of `charmatrix A`. -/
theorem derivative_charpoly_eq_sum_adjugate_diag {n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin n) (Fin n) R) :
    Polynomial.derivative A.charpoly = ∑ i : Fin n, Matrix.adjugate (charmatrix A) i i := by
  let M : Matrix (Fin n) (Fin n) R[X] := charmatrix A
  have hderiv_entry : ∀ a b : Fin n,
      Polynomial.derivative (M a b) = if a = b then 1 else 0 := by
    intro a b
    by_cases hab : a = b
    · subst hab
      simp [M, charmatrix]
    · simp [M, charmatrix, hab]
  rw [Matrix.charpoly, Matrix.det_apply]
  change Polynomial.derivative
    (∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ) • ∏ i : Fin n, M (σ i) i) = _
  simp_rw [Units.smul_def, zsmul_eq_mul]
  rw [Polynomial.derivative_sum]
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      Polynomial.derivative (((Equiv.Perm.sign σ : ℤ) : R[X]) * ∏ i : Fin n, M (σ i) i) =
        ∑ j : Fin n, ((Equiv.Perm.sign σ : ℤ) : R[X]) *
          ∏ i : Fin n, (M.updateRow j (Pi.single j 1)) (σ i) i := by
    intro σ
    have hsign_C : ((Equiv.Perm.sign σ : ℤ) : R[X]) = C ((Equiv.Perm.sign σ : ℤ) : R) := by
      simp
    rw [hsign_C, Polynomial.derivative_C_mul, Polynomial.derivative_prod_finset, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    by_cases hjj : σ j = j
    · rw [hderiv_entry (σ j) j]
      simp only [hjj, ↓reduceIte, mul_one]
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
      have hj_val : (M.updateRow j (Pi.single j 1)) (σ j) j = 1 := by
        rw [hjj, Matrix.updateRow_self, Pi.single_eq_same]
      rw [hj_val, one_mul]
      refine Finset.prod_congr rfl fun i hi => ?_
      have hij : i ≠ j := (Finset.mem_erase.mp hi).1
      have hσij : σ i ≠ j := fun h => hij (σ.injective (h.trans hjj.symm))
      rw [Matrix.updateRow_ne hσij]
    · rw [hderiv_entry (σ j) j]
      simp only [hjj, ↓reduceIte, mul_zero]
      symm
      have hσj : σ (σ⁻¹ j) = j := by simp
      have hi0 : σ⁻¹ j ≠ j := fun h => hjj ((congrArg σ h).symm.trans hσj)
      refine Finset.prod_eq_zero (Finset.mem_univ (σ⁻¹ j)) ?_
      rw [hσj, Matrix.updateRow_self, Pi.single_eq_of_ne hi0]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.adjugate_apply, Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]

/-- Derivative of the characteristic polynomial equals the sum of the `(n - 1) × (n - 1)`
vertex-deleted characteristic polynomials. -/
theorem derivative_charpoly_eq_sum_vertex_deletions {m : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) R) :
    Polynomial.derivative A.charpoly =
      ∑ i : Fin (m + 1), (A.submatrix i.succAbove i.succAbove).charpoly := by
  rw [derivative_charpoly_eq_sum_adjugate_diag]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact charmatrix_adjugate_diag A i ⟨i.succAbove, Fin.succAbove_right_injective⟩
    (fun t => Fin.succAbove_ne i t)

/-- **Jacobi two-vertex deletion identity:** for any symmetric matrix `A` and distinct indices
`i ≠ j` with complementary embeddings `fi, fj : Fin (n - 1) ↪ Fin n` and
`f : Fin (n - 2) ↪ Fin n`,
`P_{A\i} * P_{A\j} - P_A * P_{A\i,j} = (adjugate (charmatrix A) i j)^2`. -/
theorem jacobi_two_vertex_charpoly {n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin n) (Fin n) R) (hA : Aᵀ = A) {i j : Fin n} (hij : i ≠ j)
    (fi fj : Fin (n - 1) ↪ Fin n) (hfi : ∀ t, fi t ≠ i) (hfj : ∀ t, fj t ≠ j)
    (f : Fin (n - 2) ↪ Fin n) (e : Fin 2 ⊕ Fin (n - 2) ≃ Fin n)
    (he0 : e (Sum.inl 0) = i) (he1 : e (Sum.inl 1) = j) (her : ∀ t, e (Sum.inr t) = f t) :
    (A.submatrix fi fi).charpoly * (A.submatrix fj fj).charpoly -
        A.charpoly * (A.submatrix f f).charpoly =
      ((Matrix.adjugate (charmatrix A)) i j) ^ 2 := by
  have hjac := jacobi_complementary_minor (charmatrix A) hij f e he0 he1 her
  have hdi := charmatrix_adjugate_diag A i fi hfi
  have hdj := charmatrix_adjugate_diag A j fj hfj
  have hsymm : (charmatrix A)ᵀ = charmatrix A := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [charmatrix]
    · have hba : A b a = A a b := by
        calc
          A b a = Aᵀ a b := rfl
          _ = A a b := by rw [hA]
      simp [charmatrix, Matrix.transpose_apply, Matrix.sub_apply, hab, Ne.symm hab,
        hba]
  have hadj_symm : Matrix.adjugate (charmatrix A) j i = Matrix.adjugate (charmatrix A) i j := by
    calc
      Matrix.adjugate (charmatrix A) j i = (Matrix.adjugate (charmatrix A))ᵀ i j := rfl
      _ = Matrix.adjugate ((charmatrix A)ᵀ) i j := by rw [Matrix.adjugate_transpose]
      _ = Matrix.adjugate (charmatrix A) i j := by rw [hsymm]
  have hsub : ((charmatrix A).submatrix f f).det = (A.submatrix f f).charpoly := by
    change _ = (charmatrix (A.submatrix f f)).det
    congr 1
    ext a b
    by_cases hab : a = b
    · subst hab; simp [charmatrix, Matrix.submatrix_apply]
    · simp [charmatrix, Matrix.submatrix_apply, hab, f.injective.ne hab]
  rw [hdi, hdj, hadj_symm, hsub] at hjac
  change _ - _ = A.charpoly * (A.submatrix f f).charpoly at hjac
  rw [← sq] at hjac
  linear_combination hjac

end Jacobi

/-! ## Section 4: Cauchy interlacing theorem -/

section CauchyInterlacing

private lemma hermitian_rayleigh_eq_sum {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (x : Fin n → ℝ) :
    let e : Fin n ≃ Fin (Fintype.card (Fin n)) := (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    let U : Matrix (Fin n) (Fin n) ℝ := hA.eigenvectorUnitary
    let y : Fin (Fintype.card (Fin n)) → ℝ := fun j => (Uᵀ *ᵥ x) (e.symm j)
    x ⬝ᵥ x = ∑ j, (y j) ^ 2 ∧
      x ⬝ᵥ (A *ᵥ x) = ∑ j, hA.eigenvalues₀ j * (y j) ^ 2 := by
  intro e U y
  have hU_mul : U * Uᵀ = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hspec : A = U * Matrix.diagonal hA.eigenvalues * Uᵀ := by
    simpa [U, Matrix.star_eq_conjTranspose, RCLike.ofReal_real_eq_id] using hA.spectral_theorem
  have hnorm : x ⬝ᵥ x = ∑ j, (y j) ^ 2 := by
    calc
      x ⬝ᵥ x = x ⬝ᵥ ((U * Uᵀ) *ᵥ x) := by rw [hU_mul, Matrix.one_mulVec]
      _ = (Uᵀ *ᵥ x) ⬝ᵥ (Uᵀ *ᵥ x) := by
          rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
      _ = ∑ a : Fin n, ((Uᵀ *ᵥ x) a) ^ 2 := by simp [dotProduct, sq]
      _ = ∑ j : Fin (Fintype.card (Fin n)), (y j) ^ 2 := by
          refine (Fintype.sum_equiv e.symm _ _ fun j => rfl).symm
  have hray : x ⬝ᵥ (A *ᵥ x) = ∑ j, hA.eigenvalues₀ j * (y j) ^ 2 := by
    calc
      x ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ ((U * Matrix.diagonal hA.eigenvalues * Uᵀ) *ᵥ x) := by
          conv_lhs => rw [hspec]
      _ = x ⬝ᵥ (U *ᵥ (Matrix.diagonal hA.eigenvalues *ᵥ (Uᵀ *ᵥ x))) := by
          simp only [Matrix.mul_assoc, Matrix.mulVec_mulVec]
      _ = (Uᵀ *ᵥ x) ⬝ᵥ (Matrix.diagonal hA.eigenvalues *ᵥ (Uᵀ *ᵥ x)) := by
          rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
      _ = ∑ a : Fin n, hA.eigenvalues a * ((Uᵀ *ᵥ x) a) ^ 2 := by
          simp only [dotProduct, Matrix.mulVec_diagonal]
          refine Finset.sum_congr rfl fun a _ => by ring
      _ = ∑ j : Fin (Fintype.card (Fin n)), hA.eigenvalues₀ j * (y j) ^ 2 := by
          refine (Fintype.sum_equiv e.symm _ _ fun j => ?_).symm
          dsimp [Matrix.IsHermitian.eigenvalues, e, y]
          simp
  exact ⟨hnorm, hray⟩

private lemma rayleigh_ge_of_lower_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (x : Fin n → ℝ) (k : ℕ) (hk : k < Fintype.card (Fin n))
    (hzero : ∀ j : Fin (Fintype.card (Fin n)), k < j.val →
      ((hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)ᵀ *ᵥ x)
        ((Fintype.equivOfCardEq (Fintype.card_fin _)) j) = 0) :
    hA.eigenvalues₀ ⟨k, hk⟩ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
  obtain ⟨hnorm, hray⟩ := hermitian_rayleigh_eq_sum hA x
  dsimp only at hnorm hray
  rw [hnorm, hray, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hj : j.val ≤ k
  · have hle : hA.eigenvalues₀ ⟨k, hk⟩ ≤ hA.eigenvalues₀ j :=
      hA.eigenvalues₀_antitone (by simpa [Fin.le_def] using hj)
    exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
  · have hkj : k < j.val := lt_of_not_ge hj
    have hy0 := hzero j hkj
    change hA.eigenvalues₀ ⟨k, hk⟩ *
        (((hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)ᵀ *ᵥ x)
          ((Fintype.equivOfCardEq (Fintype.card_fin _)) j)) ^ 2 ≤
      hA.eigenvalues₀ j *
        (((hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)ᵀ *ᵥ x)
          ((Fintype.equivOfCardEq (Fintype.card_fin _)) j)) ^ 2
    rw [hy0]
    simp

private lemma rayleigh_le_of_upper_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (x : Fin n → ℝ) (k : ℕ) (hk : k < Fintype.card (Fin n))
    (hzero : ∀ j : Fin (Fintype.card (Fin n)), j.val < k →
      ((hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)ᵀ *ᵥ x)
        ((Fintype.equivOfCardEq (Fintype.card_fin _)) j) = 0) :
    x ⬝ᵥ (A *ᵥ x) ≤ hA.eigenvalues₀ ⟨k, hk⟩ * (x ⬝ᵥ x) := by
  obtain ⟨hnorm, hray⟩ := hermitian_rayleigh_eq_sum hA x
  dsimp only at hnorm hray
  rw [hnorm, hray, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hj : k ≤ j.val
  · have hle : hA.eigenvalues₀ j ≤ hA.eigenvalues₀ ⟨k, hk⟩ :=
      hA.eigenvalues₀_antitone (by simpa [Fin.le_def] using hj)
    exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
  · have hjk : j.val < k := lt_of_not_ge hj
    have hy0 := hzero j hjk
    change hA.eigenvalues₀ j *
        (((hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)ᵀ *ᵥ x)
          ((Fintype.equivOfCardEq (Fintype.card_fin _)) j)) ^ 2 ≤
      hA.eigenvalues₀ ⟨k, hk⟩ *
        (((hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)ᵀ *ᵥ x)
          ((Fintype.equivOfCardEq (Fintype.card_fin _)) j)) ^ 2
    rw [hy0]
    simp

private noncomputable def extendVec {m n : ℕ} (f : Fin m ↪ Fin n) :
    (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun z r := ∑ i : Fin m, if f i = r then z i else 0
  map_add' x y := by
    ext r
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  map_smul' c x := by
    ext r
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by split_ifs <;> ring

private lemma extendVec_apply_map {m n : ℕ} (f : Fin m ↪ Fin n) (z : Fin m → ℝ) (i : Fin m) :
    extendVec f z (f i) = z i := by
  change (∑ j : Fin m, if f j = f i then z j else 0) = z i
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [f.injective.ne hji]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

private lemma extendVec_apply_not_mem {m n : ℕ} (f : Fin m ↪ Fin n) (z : Fin m → ℝ) {r : Fin n}
    (hr : r ∉ Set.range f) :
    extendVec f z r = 0 := by
  change (∑ i : Fin m, if f i = r then z i else 0) = 0
  refine Finset.sum_eq_zero fun i _ => ?_
  have hne : f i ≠ r := fun h => hr ⟨i, h⟩
  simp [hne]

private lemma extendVec_dotProduct_self {m n : ℕ} (f : Fin m ↪ Fin n) (z : Fin m → ℝ) :
    extendVec f z ⬝ᵥ extendVec f z = z ⬝ᵥ z := by
  simp only [dotProduct]
  have hsplit : (∑ r : Fin n, extendVec f z r * extendVec f z r) =
      ∑ r ∈ Finset.univ.image f, extendVec f z r * extendVec f z r := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image f))]
    intro r _ hr
    have hr' : r ∉ Set.range f := by
      rintro ⟨i, rfl⟩
      exact hr (Finset.mem_image_of_mem f (Finset.mem_univ i))
    simp [extendVec_apply_not_mem f z hr']
  rw [hsplit, Finset.sum_image (fun a _ b _ h => f.injective h)]
  refine Finset.sum_congr rfl fun i _ => by rw [extendVec_apply_map]

private lemma extendVec_rayleigh {m n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin m ↪ Fin n) (z : Fin m → ℝ) :
    extendVec f z ⬝ᵥ (A *ᵥ extendVec f z) = z ⬝ᵥ (A.submatrix f f *ᵥ z) := by
  simp only [dotProduct, Matrix.mulVec]
  have hterm : ∀ r : Fin n, extendVec f z r * ∑ s : Fin n, A r s * extendVec f z s =
      ∑ s : Fin n, (if r ∈ Finset.univ.image f ∧ s ∈ Finset.univ.image f then
        extendVec f z r * A r s * extendVec f z s else 0) := by
    intro r
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hr : r ∈ Finset.univ.image f
    · by_cases hs : s ∈ Finset.univ.image f
      · simp [hr, hs, mul_assoc]
      · have hs' : s ∉ Set.range f := by
          rintro ⟨j, rfl⟩; exact hs (Finset.mem_image_of_mem f (Finset.mem_univ j))
        simp [hr, hs, extendVec_apply_not_mem f z hs']
    · have hr' : r ∉ Set.range f := by
        rintro ⟨i, rfl⟩; exact hr (Finset.mem_image_of_mem f (Finset.mem_univ i))
      simp [hr, extendVec_apply_not_mem f z hr']
  simp_rw [hterm]
  have hswap : ∀ r : Fin n,
      (∑ s : Fin n, if r ∈ Finset.univ.image f ∧ s ∈ Finset.univ.image f then
          extendVec f z r * A r s * extendVec f z s else 0) =
      if r ∈ Finset.univ.image f then
        ∑ s ∈ Finset.univ.image f, extendVec f z r * A r s * extendVec f z s
      else 0 := by
    intro r
    by_cases hr : r ∈ Finset.univ.image f
    · simp only [hr, true_and, ↓reduceIte, ← Finset.sum_filter]
      congr 1
      ext s; simp
    · simp [hr]
  simp_rw [hswap, ← Finset.sum_filter]
  have hfilt : Finset.univ.filter (fun r : Fin n => r ∈ Finset.univ.image f) = Finset.univ.image f := by
    ext r; simp
  rw [hfilt, Finset.sum_image (fun a _ b _ h => f.injective h)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.sum_image (fun a _ b _ h => f.injective h)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [extendVec_apply_map, extendVec_apply_map, Matrix.submatrix_apply]
  ring

private lemma dotProduct_self_pos_of_ne_zero {n : ℕ} {x : Fin n → ℝ} (hx : x ≠ 0) :
    0 < x ⬝ᵥ x := by
  have hnonneg : ∀ i : Fin n, 0 ≤ x i * x i := fun i => mul_self_nonneg (x i)
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  have hpos : 0 < x i₀ * x i₀ := mul_self_pos.mpr hi₀
  exact Finset.sum_pos' (fun i _ => hnonneg i) ⟨i₀, Finset.mem_univ i₀, hpos⟩

/-- **Cauchy Interlacing Theorem:** For any real Hermitian (symmetric) matrix
`A : Matrix (Fin n) (Fin n) ℝ` and any principal submatrix `B = A.submatrix f f`
(`f : Fin m ↪ Fin n`), the decreasingly ordered eigenvalues satisfy
`λ_{k + (n - m)} ≤ μ_k ≤ λ_k` for all `k < m`. -/
theorem cauchy_interlacing {n m : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (f : Fin m ↪ Fin n) (k : ℕ) (hk : k < m) :
    let B : Matrix (Fin m) (Fin m) ℝ := A.submatrix f f
    have hB : B.IsHermitian := hA.submatrix f
    have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective f f.injective
    have hkn : k < Fintype.card (Fin n) := by simpa using lt_of_lt_of_le hk hmn
    have hkm : k < Fintype.card (Fin m) := by simpa using hk
    have hkp : k + (n - m) < Fintype.card (Fin n) := by
      simp only [Fintype.card_fin]
      omega
    hA.eigenvalues₀ ⟨k + (n - m), hkp⟩ ≤ hB.eigenvalues₀ ⟨k, hkm⟩ ∧
      hB.eigenvalues₀ ⟨k, hkm⟩ ≤ hA.eigenvalues₀ ⟨k, hkn⟩ := by
  intro B hB hmn hkn hkm hkp
  let e_n : Fin (Fintype.card (Fin n)) ≃ Fin n := Fintype.equivOfCardEq (Fintype.card_fin _)
  let e_m : Fin (Fintype.card (Fin m)) ≃ Fin m := Fintype.equivOfCardEq (Fintype.card_fin _)
  let U : Matrix (Fin n) (Fin n) ℝ := hA.eigenvectorUnitary
  let V : Matrix (Fin m) (Fin m) ℝ := hB.eigenvectorUnitary
  have hU_mul : Uᵀ * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hV_mul : Vᵀ * V = 1 := by
    simpa [V, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self hB.eigenvectorUnitary
  refine ⟨?_, ?_⟩
  · -- Lower bound: λ_{k + (n - m)} ≤ μ_k
    let p : ℕ := k + (n - m)
    have hp_lt : p < Fintype.card (Fin n) := hkp
    let pad₂ : (Fin (p + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      { toFun := fun c a => if h : (e_n.symm a).val < p + 1 then c ⟨(e_n.symm a).val, h⟩ else 0
        map_add' := fun c₁ c₂ => by
          ext a
          by_cases h : (e_n.symm a).val < p + 1
          · simp only [Pi.add_apply, h, ↓reduceDIte]
          · simp only [Pi.add_apply, h, ↓reduceDIte, add_zero]
        map_smul' := fun r c => by
          ext a
          by_cases h : (e_n.symm a).val < p + 1
          · simp only [Pi.smul_apply, h, ↓reduceDIte, RingHom.id_apply]
          · simp only [Pi.smul_apply, h, ↓reduceDIte, RingHom.id_apply, smul_zero] }
    let T₂ : (Fin (p + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) := Matrix.mulVecLin U ∘ₗ pad₂
    let L₂ : (Fin (p + 1) → ℝ) →ₗ[ℝ] ({r : Fin n // r ∉ Set.range f} → ℝ) × (Fin k → ℝ) :=
      { toFun := fun c =>
          (fun r => (T₂ c) r.1,
           fun j => (Vᵀ *ᵥ (fun i : Fin m => (T₂ c) (f i))) (e_m ⟨j.val, by omega⟩))
        map_add' := fun c₁ c₂ => by
          refine Prod.ext ?_ ?_
          · ext r; simp [map_add]
          · ext j
            simp only [map_add, Pi.add_apply, Prod.snd_add]
            change (Vᵀ *ᵥ ((fun i => T₂ c₁ (f i)) + (fun i => T₂ c₂ (f i)))) _ = _
            rw [Matrix.mulVec_add]; rfl
        map_smul' := fun s c => by
          refine Prod.ext ?_ ?_
          · ext r; simp [map_smul]
          · ext j
            simp only [map_smul, Pi.smul_apply, RingHom.id_apply, Prod.smul_snd]
            change (Vᵀ *ᵥ (s • (fun i => T₂ c (f i)))) _ = _
            rw [Matrix.mulVec_smul]; rfl }
    have hcard_miss : Fintype.card {r : Fin n // r ∉ Set.range f} = n - m := by
      have hcompl := Fintype.card_subtype_compl (fun r : Fin n => r ∈ Set.range f)
      have hrange : Fintype.card {r : Fin n // r ∈ Set.range f} = m :=
        (Fintype.card_congr (Equiv.ofInjective f f.injective).symm).trans (Fintype.card_fin m)
      rw [hcompl, hrange, Fintype.card_fin]
    have hdim_lt : Module.finrank ℝ (({r : Fin n // r ∉ Set.range f} → ℝ) × (Fin k → ℝ)) <
        Module.finrank ℝ (Fin (p + 1) → ℝ) := by
      rw [Module.finrank_prod, Module.finrank_pi, Module.finrank_pi, hcard_miss]
      simp [p]
      omega
    have hnot_inj : ¬Function.Injective L₂ := by
      intro hinj
      exact absurd (LinearMap.finrank_le_finrank_of_injective hinj) (not_le_of_gt hdim_lt)
    have hker : LinearMap.ker L₂ ≠ ⊥ := by
      rw [← LinearMap.ker_eq_bot] at hnot_inj
      exact hnot_inj
    obtain ⟨c, hc_mem, hc_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hLc : L₂ c = 0 := hc_mem
    let x : Fin n → ℝ := T₂ c
    let z : Fin m → ℝ := fun i => x (f i)
    have hx_ne : x ≠ 0 := by
      intro hx0
      apply hc_ne
      ext j
      have hUx : Uᵀ *ᵥ x = 0 := by simp [hx0]
      have hcoord : (Uᵀ *ᵥ x) (e_n ⟨j.val, by omega⟩) = c j := by
        dsimp [x, T₂, pad₂, Matrix.mulVecLin_apply]
        rw [Matrix.mulVec_mulVec, hU_mul, Matrix.one_mulVec, Equiv.symm_apply_apply]
        simp [j.isLt]
      simpa [hUx] using hcoord.symm
    have hxz : extendVec f z = x := by
      ext r
      by_cases hr : r ∈ Set.range f
      · rcases hr with ⟨i, rfl⟩
        exact extendVec_apply_map f z i
      · rw [extendVec_apply_not_mem f z hr]
        have hr1 := congrArg (fun p => p.1 ⟨r, hr⟩) hLc
        simpa [L₂, x] using hr1.symm
    have hz_pos : 0 < z ⬝ᵥ z := by
      rw [← extendVec_dotProduct_self f z, hxz]
      exact dotProduct_self_pos_of_ne_zero hx_ne
    have hA_low : hA.eigenvalues₀ ⟨p, hp_lt⟩ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
      apply rayleigh_ge_of_lower_zero hA x p hp_lt
      intro j hj
      dsimp [x, T₂, pad₂, Matrix.mulVecLin_apply, e_n]
      rw [Matrix.mulVec_mulVec, hU_mul, Matrix.one_mulVec, Equiv.symm_apply_apply]
      have hnot : ¬j.val < p + 1 := by omega
      simp only [hnot, ↓reduceDIte]
    have hB_up : z ⬝ᵥ (B *ᵥ z) ≤ hB.eigenvalues₀ ⟨k, hkm⟩ * (z ⬝ᵥ z) := by
      apply rayleigh_le_of_upper_zero hB z k hkm
      intro j hj
      have hj' := congrArg (fun q => q.2 ⟨j.val, hj⟩) hLc
      simpa [L₂, x, z, e_m] using hj'
    have hray_eq : z ⬝ᵥ (B *ᵥ z) = x ⬝ᵥ (A *ᵥ x) := by
      rw [← extendVec_rayleigh A f z, hxz]
    have hnorm_eq : z ⬝ᵥ z = x ⬝ᵥ x := by
      rw [← extendVec_dotProduct_self f z, hxz]
    rw [← hnorm_eq, ← hray_eq] at hA_low
    exact le_of_mul_le_mul_right (le_trans hA_low hB_up) hz_pos
  · -- Upper bound: μ_k ≤ λ_k
    let pad₁ : (Fin (k + 1) → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
      { toFun := fun c a => if h : (e_m.symm a).val < k + 1 then c ⟨(e_m.symm a).val, h⟩ else 0
        map_add' := fun c₁ c₂ => by
          ext a
          by_cases h : (e_m.symm a).val < k + 1
          · simp only [Pi.add_apply, h, ↓reduceDIte]
          · simp only [Pi.add_apply, h, ↓reduceDIte, add_zero]
        map_smul' := fun r c => by
          ext a
          by_cases h : (e_m.symm a).val < k + 1
          · simp only [Pi.smul_apply, h, ↓reduceDIte, RingHom.id_apply]
          · simp only [Pi.smul_apply, h, ↓reduceDIte, RingHom.id_apply, smul_zero] }
    let T₁ : (Fin (k + 1) → ℝ) →ₗ[ℝ] (Fin m → ℝ) := Matrix.mulVecLin V ∘ₗ pad₁
    let L₁ : (Fin (k + 1) → ℝ) →ₗ[ℝ] (Fin k → ℝ) :=
      { toFun := fun c j => (Uᵀ *ᵥ extendVec f (T₁ c)) (e_n ⟨j.val, by omega⟩)
        map_add' := fun c₁ c₂ => by
          ext j
          simp [LinearMap.map_add, Matrix.mulVec_add]
        map_smul' := fun r c => by
          ext j
          simp [Matrix.mulVec_smul] }
    have hdim_lt : Module.finrank ℝ (Fin k → ℝ) < Module.finrank ℝ (Fin (k + 1) → ℝ) := by
      simp
    have hnot_inj : ¬Function.Injective L₁ := by
      intro hinj
      exact absurd (LinearMap.finrank_le_finrank_of_injective hinj) (not_le_of_gt hdim_lt)
    have hker : LinearMap.ker L₁ ≠ ⊥ := by
      rw [← LinearMap.ker_eq_bot] at hnot_inj
      exact hnot_inj
    obtain ⟨c, hc_mem, hc_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hLc : L₁ c = 0 := hc_mem
    let z : Fin m → ℝ := T₁ c
    have hz_ne : z ≠ 0 := by
      intro hz0
      apply hc_ne
      ext j
      have hVz : Vᵀ *ᵥ z = 0 := by simp [hz0]
      have hcoord : (Vᵀ *ᵥ z) (e_m ⟨j.val, by omega⟩) = c j := by
        dsimp [z, T₁, pad₁, Matrix.mulVecLin_apply]
        rw [Matrix.mulVec_mulVec, hV_mul, Matrix.one_mulVec, Equiv.symm_apply_apply]
        simp [j.isLt]
      simpa [hVz] using hcoord.symm
    have hz_pos : 0 < z ⬝ᵥ z := dotProduct_self_pos_of_ne_zero hz_ne
    have hB_low : hB.eigenvalues₀ ⟨k, hkm⟩ * (z ⬝ᵥ z) ≤ z ⬝ᵥ (B *ᵥ z) := by
      apply rayleigh_ge_of_lower_zero hB z k hkm
      intro j hj
      dsimp [z, T₁, pad₁, Matrix.mulVecLin_apply, e_m]
      rw [Matrix.mulVec_mulVec, hV_mul, Matrix.one_mulVec, Equiv.symm_apply_apply]
      have hnot : ¬j.val < k + 1 := by omega
      simp only [hnot, ↓reduceDIte]
    have hA_up : extendVec f z ⬝ᵥ (A *ᵥ extendVec f z) ≤
        hA.eigenvalues₀ ⟨k, hkn⟩ * (extendVec f z ⬝ᵥ extendVec f z) := by
      apply rayleigh_le_of_upper_zero hA (extendVec f z) k hkn
      intro j hj
      have hj' := congrArg (fun q => q ⟨j.val, hj⟩) hLc
      simpa [L₁, z, e_n] using hj'
    rw [extendVec_rayleigh, extendVec_dotProduct_self] at hA_up
    exact le_of_mul_le_mul_right (le_trans hB_low hA_up) hz_pos

end CauchyInterlacing

end EquiangularLines
