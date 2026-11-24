module

public import EquiangularLines.Spectral
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Exact 2-Adic Seidel Congruences (Theorem 4.2 and Proposition 7.3)

This module formalizes the two deep 2-adic theorems for Seidel matrices needed in Phase 2:

1. **Proposition 7.3 (`even_order_two_pow_dvd_charpoly`):**
   For any Seidel matrix `S` of **even** order `m`, `(2 : ℤ) ^ m` divides `S.charpoly.comp (C 2 * X - 1)`
   in `ℤ[X]` (sharpening `two_pow_sub_one_dvd_charpoly_two_mul_sub_one` by one full power of `2`).
2. **Cayley's Pfaffian square theorem (`skew_det_eq_sq`):**
   Over any commutative ring `R`, the determinant of any skew-symmetric `(2m) × (2m)` matrix with
   zero diagonal is a square in `R` (proved via Jacobi's `2 × 2` complementary-minor identity and
   integral closure of `MvPolynomial _ ℤ`).
3. **Theorem 4.2 (`odd_order_two_adic_congruence`):**
   For any Seidel matrix `S` of **odd** order `n`, there exists a monic polynomial `Q : ℤ[X]` of
   degree `(n - 1) / 2` such that
   `S.charpoly.comp (C 2 * X - 1) = C (2 ^ (n - 1)) * ((C 2 * X - C n) * Q ^ 2 + C 4 * R)`
   in `ℤ[X]`.
-/

@[expose] public section

open Matrix Polynomial
open scoped BigOperators

namespace EquiangularLines

/-! ## Section 1: Proposition 7.3 (Even-order sharp `2^m` divisibility) -/

section Prop73

private lemma odd_coeff_dvd_two_of_even_symm_diag_zero {m : ℕ} (hm : Even m)
    {A : Matrix (Fin m) (Fin m) ℤ} (hSymm : Aᵀ = A) (hdiag : ∀ i, A i i = 0)
    {k : ℕ} (hk : Odd k) :
    (2 : ℤ) ∣ ((-A).charpoly).coeff k := by
  by_cases hkm : m < k
  · have hdeg : ((-A).charpoly).natDegree = m :=
      (Matrix.charpoly_natDegree_eq_dim (-A)).trans (Fintype.card_fin m)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    exact dvd_zero _
  · let B : Matrix (Fin m) (Fin m) ℤ[X] :=
      (X : ℤ[X]) • (1 : Matrix (Fin m) (Fin m) ℤ[X]) + A.map (Polynomial.C : ℤ →+* ℤ[X])
    have hB_eq : charmatrix (-A) = B := by
      refine Matrix.ext fun i j => ?_
      by_cases hij : i = j
      · subst hij
        simp [B, charmatrix, hdiag i]
      · simp [B, charmatrix, hij]
    have hB_entry : ∀ a b : Fin m, B a b = if a = b then X else C (A a b) := fun a b => by
      have hB_def : B = (X : ℤ[X]) • (1 : Matrix (Fin m) (Fin m) ℤ[X]) +
          A.map (Polynomial.C : ℤ →+* ℤ[X]) := rfl
      rw [hB_def, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply,
        smul_eq_mul]
      by_cases hab : a = b
      · subst hab; simp [hdiag a]
      · simp [hab]
    rw [Matrix.charpoly, hB_eq, Matrix.det_apply]
    change (2 : ℤ) ∣
      (∑ σ : Equiv.Perm (Fin m), (Equiv.Perm.sign σ) • ∏ i : Fin m, B (σ i) i).coeff k
    rw [← Polynomial.lcoeff_apply, map_sum]
    simp only [Polynomial.lcoeff_apply]
    let S_k : Finset (Equiv.Perm (Fin m)) :=
      Finset.univ.filter (fun σ : Equiv.Perm (Fin m) =>
        (Finset.univ.filter (fun i : Fin m => σ i = i)).card = k)
    have hsum_eq :
        (∑ σ : Equiv.Perm (Fin m),
          ((Equiv.Perm.sign σ • ∏ i : Fin m, B (σ i) i).coeff k)) =
          ∑ σ ∈ S_k, (Equiv.Perm.sign σ : ℤ) *
            ∏ i ∈ Finset.univ.filter (fun i : Fin m => σ i ≠ i), A (σ i) i := by
      have hterm : ∀ σ : Equiv.Perm (Fin m),
          ((Equiv.Perm.sign σ • ∏ i : Fin m, B (σ i) i).coeff k) =
            if (Finset.univ.filter (fun i : Fin m => σ i = i)).card = k then
              (Equiv.Perm.sign σ : ℤ) *
                ∏ i ∈ Finset.univ.filter (fun i : Fin m => σ i ≠ i), A (σ i) i
            else 0 := by
        intro σ
        rw [Units.smul_def, zsmul_eq_mul, ← C_eq_intCast, Int.cast_id, Polynomial.coeff_C_mul]
        let fixSet : Finset (Fin m) := Finset.univ.filter (fun i => σ i = i)
        let movSet : Finset (Fin m) := Finset.univ.filter (fun i => σ i ≠ i)
        have hsplit : (∏ i : Fin m, B (σ i) i) =
            C (∏ i ∈ movSet, A (σ i) i) * X ^ fixSet.card := by
          rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => σ i = i)]
          have hfix : (∏ i ∈ fixSet, B (σ i) i) = X ^ fixSet.card := by
            trans ∏ _i ∈ fixSet, (X : ℤ[X])
            · refine Finset.prod_congr rfl fun i hi => ?_
              have hii : σ i = i := (Finset.mem_filter.mp hi).2
              simp [hii, hB_entry i i]
            · simp
          have hmov : (∏ i ∈ Finset.univ.filter (fun i => ¬σ i = i), B (σ i) i) =
              C (∏ i ∈ movSet, A (σ i) i) := by
            have hsub : (∏ i ∈ movSet, B (σ i) i) = ∏ i ∈ movSet, C (A (σ i) i) := by
              refine Finset.prod_congr rfl fun i hi => ?_
              have hne : σ i ≠ i := (Finset.mem_filter.mp hi).2
              simp [hB_entry (σ i) i, hne]
            change (∏ i ∈ movSet, B (σ i) i) = _
            rw [hsub, ← map_prod C]
          rw [hfix, hmov, mul_comm]
        rw [hsplit, Polynomial.coeff_C_mul_X_pow]
        change (Equiv.Perm.sign σ : ℤ) *
            (if k = fixSet.card then ∏ i ∈ movSet, A (σ i) i else 0) =
          if fixSet.card = k then
            (Equiv.Perm.sign σ : ℤ) * ∏ i ∈ movSet, A (σ i) i
          else 0
        by_cases hk' : fixSet.card = k
        · simp only [hk', ↓reduceIte]
        · simp only [hk', Ne.symm hk', ↓reduceIte, mul_zero]
      simp_rw [hterm]
      rw [Finset.sum_filter]
    rw [hsum_eq]
    refine two_dvd_sum_of_involution S_k (fun σ => σ⁻¹)
      (fun σ => (Equiv.Perm.sign σ : ℤ) *
        ∏ i ∈ Finset.univ.filter (fun i : Fin m => σ i ≠ i), A (σ i) i) ?_ ?_ ?_ ?_
    · intro σ hσ
      simp only [S_k, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      rw [← hσ]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact σ.inv_eq_iff_eq.trans eq_comm
    · intro σ _; exact inv_inv σ
    · intro σ hσ
      simp only [S_k, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      apply perm_inv_ne_self_of_odd_moved σ
      have hcard := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
        (fun i => σ i = i)
      simp only [Finset.card_univ, Fintype.card_fin] at hcard
      rw [hσ] at hcard
      have hcard' : k + (Finset.univ.filter (fun i : Fin m => σ i ≠ i)).card = m := hcard
      rcases hm with ⟨a, rfl⟩
      rcases hk with ⟨b, rfl⟩
      have hk_le : 2 * b + 1 ≤ a + a := by omega
      refine ⟨a - b - 1, by omega⟩
    · intro σ _
      simp only [Equiv.Perm.sign_inv]
      congr 1
      refine Finset.prod_bij (fun i _ => σ⁻¹ i) ?_ ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        intro hfix
        have h0 : σ (σ⁻¹ i) = i := by simp
        rw [hfix] at h0
        exact hi h0
      · intro a _ b _ hab; exact σ.symm.injective hab
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        refine ⟨σ i, ?_, by simp⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact fun hss => hi (σ.injective (by simpa using hss.symm))
      · intro i _
        calc
          A (σ⁻¹ i) i = Aᵀ i (σ⁻¹ i) := rfl
          _ = A i (σ⁻¹ i) := by rw [hSymm]
          _ = A (σ (σ⁻¹ i)) (σ⁻¹ i) := by simp

/-- **Proposition 7.3 (Even-order sharp `2^m` divisibility):**
For any Seidel matrix `S` of **even** order `m`, `C ((2 : ℤ) ^ m)` divides
`S.charpoly.comp (C 2 * X - 1)` in `ℤ[X]`. -/
theorem even_order_two_pow_dvd_charpoly {m : ℕ} (hm : Even m)
    {S : Matrix (Fin m) (Fin m) ℤ} (hS : IsSeidelMatrix S) :
    C ((2 : ℤ) ^ m) ∣ S.charpoly.comp (C 2 * X - 1) := by
  by_cases hm0 : m = 0
  · subst hm0; simp
  have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm0
  let A : Matrix (Fin m) (Fin m) ℤ :=
    Matrix.of fun i j => if i = j then 0 else (1 - S i j) / 2
  have hSymm : Aᵀ = A := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [A]
    · have hSij : S j i = S i j := by
        calc
          S j i = Sᵀ i j := rfl
          _ = S i j := by rw [hS.1]
      simp [A, hij, Ne.symm hij, hSij]
  have hdiag : ∀ i, A i i = 0 := fun i => by simp [A]
  let B : Matrix (Fin m) (Fin m) ℤ[X] :=
    (X : ℤ[X]) • (1 : Matrix (Fin m) (Fin m) ℤ[X]) + A.map (Polynomial.C : ℤ →+* ℤ[X])
  have hB_symm : Bᵀ = B := by
    ext i j
    have hAij : A j i = A i j := by
      calc
        A j i = Aᵀ i j := rfl
        _ = A i j := by rw [hSymm]
    simp only [B, Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.map_apply, smul_eq_mul, eq_comm]
    rw [hAij]
  have hB_char : charmatrix (-A) = B := by
    refine Matrix.ext fun i j => ?_
    by_cases hij : i = j
    · subst hij; simp [B, charmatrix, hdiag i]
    · simp [B, charmatrix, hij]
  have hcomp_det : S.charpoly.comp (C (2 : ℤ) * X - 1) =
      (C (2 : ℤ) • B - Matrix.vecMulVec (fun _ => (1 : ℤ[X])) (fun _ => (1 : ℤ[X]))).det := by
    let φ : ℤ[X] →+* ℤ[X] := Polynomial.eval₂RingHom C (C (2 : ℤ) * X)
    have h1 : S.charpoly.comp (C (2 : ℤ) * X - 1) =
        φ (((1 : ℤ) • (1 : Matrix (Fin m) (Fin m) ℤ) + S).charpoly) := by
      rw [charpoly_add_smul_one S 1]
      change S.charpoly.comp (C (2 : ℤ) * X - 1) =
        (S.charpoly.comp (X - C (1 : ℤ))).comp (C (2 : ℤ) * X)
      simp only [Polynomial.comp_assoc, sub_comp, X_comp]
      have hC1 : (C (1 : ℤ)).comp (C (2 : ℤ) * X) = 1 := by simp
      rw [hC1]
    rw [h1, Matrix.charpoly, RingHom.map_det, RingHom.mapMatrix_apply]
    congr 1
    refine Matrix.ext fun i j => ?_
    let Lmat : Matrix (Fin m) (Fin m) ℤ := (1 : ℤ) • (1 : Matrix (Fin m) (Fin m) ℤ) + S
    have hLij : Lmat i j = (if i = j then 1 else 0) + S i j := by
      simp [Lmat, Matrix.one_apply]
    have hL : (Lmat.charmatrix.map φ) i j =
        (if i = j then C 2 * X - 1 else C (-S i j)) := by
      rw [Matrix.map_apply, charmatrix, Matrix.sub_apply, Matrix.scalar_apply,
        Matrix.diagonal_apply, RingHom.mapMatrix_apply, Matrix.map_apply, hLij]
      by_cases hij : i = j
      · subst hij
        simp [φ, hS.2.1 i]
      · simp only [hij, ↓reduceIte, zero_sub, zero_add, φ,
          Polynomial.coe_eval₂RingHom, Polynomial.eval₂_neg, Polynomial.eval₂_C]
        rw [← map_neg]
    let Rmat : Matrix (Fin m) (Fin m) ℤ[X] :=
      C (2 : ℤ) • B - Matrix.vecMulVec (fun _ => (1 : ℤ[X])) (fun _ => (1 : ℤ[X]))
    have hR : Rmat i j = (if i = j then C 2 * X - 1 else C (2 * A i j - 1)) := by
      rw [show Rmat i j = C (2 : ℤ) * B i j -
          (Matrix.vecMulVec (fun _ => (1 : ℤ[X])) (fun _ => (1 : ℤ[X]))) i j from rfl]
      have hBij : B i j = (if i = j then X else 0) + C (A i j) := by
        have hBdef : B = (X : ℤ[X]) • (1 : Matrix (Fin m) (Fin m) ℤ[X]) +
            A.map (Polynomial.C : ℤ →+* ℤ[X]) := rfl
        rw [hBdef, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply,
          smul_eq_mul]
        by_cases hij : i = j <;> simp [hij]
      rw [hBij, Matrix.vecMulVec_apply]
      by_cases hij : i = j
      · subst hij; simp [hdiag i]
      · simp [hij, map_sub]
    change (Lmat.charmatrix.map φ) i j = Rmat i j
    rw [hL, hR]
    by_cases hij : i = j
    · simp [hij]
    · simp only [hij, ↓reduceIte]
      rcases hS.2.2 i j hij with h | h <;> simp [A, hij, h]
  rw [hcomp_det, det_sub_vecMulVec, Matrix.det_smul, Fintype.card_fin]
  apply dvd_sub
  · rw [C_pow]
    exact dvd_mul_right _ _
  · rw [Matrix.adjugate_smul, Fintype.card_fin, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    have hsplit_pow : (C (2 : ℤ) : ℤ[X]) ^ m = C (2 : ℤ) ^ (m - 1) * C (2 : ℤ) := by
      rw [← pow_succ, Nat.sub_add_cancel hm1]
    rw [C_pow, hsplit_pow]
    refine mul_dvd_mul_left _ ?_
    have hdot : ((fun _ : Fin m => (1 : ℤ[X])) ⬝ᵥ (B.adjugate *ᵥ (fun _ => (1 : ℤ[X])))) =
        ∑ i : Fin m, ∑ j : Fin m, B.adjugate i j := by
      simp [dotProduct, Matrix.mulVec]
    have hadj_symm : B.adjugateᵀ = B.adjugate := by
      rw [Matrix.adjugate_transpose, hB_symm]
    rw [hdot, sum_matrix_symm_split B.adjugate hadj_symm]
    apply dvd_add
    · have hdiag_eq : (∑ i : Fin m, B.adjugate i i) = Polynomial.derivative ((-A).charpoly) := by
        rw [derivative_charpoly_eq_sum_adjugate_diag (-A), hB_char]
      rw [hdiag_eq, Polynomial.C_dvd_iff_dvd_coeff]
      intro r
      rw [Polynomial.coeff_derivative]
      rcases Nat.even_or_odd r with heven | hodd
      · have hodd_succ : Odd (r + 1) := heven.add_one
        exact dvd_mul_of_dvd_left
          (odd_coeff_dvd_two_of_even_symm_diag_zero hm hSymm hdiag hodd_succ) _
      · have heven_succ : Even (r + 1) := hodd.add_one
        rcases heven_succ with ⟨t, ht⟩
        refine dvd_mul_of_dvd_right ?_ _
        refine ⟨(t : ℤ), ?_⟩
        norm_cast
        omega
    · have h2C : (2 : ℤ[X]) = C (2 : ℤ) := by simp
      rw [h2C]
      exact dvd_mul_right _ _

end Prop73

/-! ## Section 2: Cayley's Pfaffian Square Theorem (`skew_det_eq_sq`) -/

section Pfaffian

private lemma odd_skew_det_eq_zero {n : ℕ} (hn : Odd n) {R : Type*}
    [CommRing R] [IsDomain R] [CharZero R]
    {K : Matrix (Fin n) (Fin n) R} (hK : Kᵀ = -K) :
    K.det = 0 := by
  have hdet : K.det = -K.det := by
    calc
      K.det = Kᵀ.det := (Matrix.det_transpose K).symm
      _ = (-K).det := by rw [hK]
      _ = (-1 : R) ^ Fintype.card (Fin n) * K.det := Matrix.det_neg K
      _ = (-1 : R) * K.det := by rw [Fintype.card_fin, hn.neg_one_pow]
      _ = -K.det := by ring
  have h2 : (2 : R) * K.det = 0 := by
    calc
      (2 : R) * K.det = K.det + K.det := two_mul _
      _ = K.det + -K.det := congrArg (K.det + ·) hdet
      _ = 0 := add_neg_cancel _
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

private lemma skew_adjugate_transpose {n : ℕ} (hn : Even n) (hn1 : 1 ≤ n) {R : Type*}
    [CommRing R] {K : Matrix (Fin n) (Fin n) R} (hK : Kᵀ = -K) :
    K.adjugateᵀ = -K.adjugate := by
  have hodd : Odd (Fintype.card (Fin n) - 1) := by
    rw [Fintype.card_fin]
    rcases hn with ⟨m, rfl⟩
    refine ⟨m - 1, by omega⟩
  calc
    K.adjugateᵀ = Kᵀ.adjugate := Matrix.adjugate_transpose K
    _ = (-K).adjugate := by rw [hK]
    _ = ((-1 : R) • K).adjugate := by rw [neg_one_smul]
    _ = (-1 : R) ^ (Fintype.card (Fin n) - 1) • K.adjugate := Matrix.adjugate_smul (-1) K
    _ = (-1 : R) • K.adjugate := by rw [hodd.neg_one_pow]
    _ = -K.adjugate := neg_one_smul R _

private lemma skew_adjugate_diag_eq_zero {n : ℕ} (hn : Even n) (hn1 : 1 ≤ n) {R : Type*}
    [CommRing R] [IsDomain R] [CharZero R]
    {K : Matrix (Fin n) (Fin n) R} (hK : Kᵀ = -K) (i : Fin n) :
    K.adjugate i i = 0 := by
  let m : ℕ := n - 1
  have hm_succ : m + 1 = n := by omega
  let eFin : Fin (m + 1) ≃ Fin n := finCongr hm_succ
  let i' : Fin (m + 1) := eFin.symm i
  let f : Fin m ↪ Fin n := ⟨fun t => eFin (i'.succAbove t),
    fun _ _ h => Fin.succAbove_right_injective (eFin.injective h)⟩
  have hf : ∀ t : Fin m, f t ≠ i := fun t h => by
    have h' : i'.succAbove t = i' := by
      apply eFin.injective
      exact h.trans (eFin.apply_symm_apply i).symm
    exact Fin.succAbove_ne i' t h'
  let g : Fin 1 ⊕ Fin m → Fin n := Sum.elim (fun _ => i) f
  have hg_inj : Function.Injective g := by
    rintro (a | a) (b | b) hab
    · fin_cases a; fin_cases b; rfl
    · exact False.elim ((hf b) hab.symm)
    · exact False.elim ((hf a) hab)
    · exact congrArg Sum.inr (f.injective hab)
  have hcard : Fintype.card (Fin 1 ⊕ Fin m) = Fintype.card (Fin n) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  let e : Fin 1 ⊕ Fin m ≃ Fin n :=
    Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hg_inj, hcard⟩)
  let L : Matrix (Fin m) (Fin 1) R := fun t _ => K (f t) i
  have hblk : (K.updateRow i (Pi.single i 1)).submatrix e e =
      Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 L (K.submatrix f f) := by
    refine Matrix.ext fun a b => ?_
    rcases a with a | a <;> rcases b with b | b
    · fin_cases a; fin_cases b
      simp [e, g, Matrix.submatrix_apply, Matrix.updateRow_self, Pi.single_eq_same]
    · fin_cases a
      simp [e, g, Matrix.submatrix_apply, Matrix.updateRow_self, Pi.single_eq_of_ne (hf b)]
    · fin_cases b
      rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁]
      change (K.updateRow i (Pi.single i 1)) (f a) i = K (f a) i
      rw [Matrix.updateRow_ne (hf a)]
    · simp only [e, g, Equiv.ofBijective_apply, Sum.elim_inr, Matrix.submatrix_apply,
        Matrix.fromBlocks_apply₂₂]
      rw [Matrix.updateRow_ne (hf a)]
  have hadj_eq : K.adjugate i i = (K.submatrix f f).det := by
    rw [Matrix.adjugate_apply, ← Matrix.det_submatrix_equiv_self e, hblk,
      Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul]
  rw [hadj_eq]
  refine odd_skew_det_eq_zero ?_ ?_
  · rcases hn with ⟨k, rfl⟩
    refine ⟨k - 1, by omega⟩
  · ext a b
    calc
      (K.submatrix f f)ᵀ a b = K (f b) (f a) := rfl
      _ = Kᵀ (f a) (f b) := rfl
      _ = (-K) (f a) (f b) := by rw [hK]
      _ = -(K.submatrix f f) a b := rfl

private def symplecticBlock (m : ℕ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℤ :=
  Matrix.of fun i j =>
    if i.val + 1 = j.val ∧ Even i.val then 1
    else if j.val + 1 = i.val ∧ Even j.val then -1
    else 0

private lemma symplecticBlock_skew (m : ℕ) :
    (symplecticBlock m)ᵀ = -symplecticBlock m ∧ ∀ i, symplecticBlock m i i = 0 := by
  refine ⟨?_, fun i => by simp [symplecticBlock]⟩
  ext i j
  simp only [Matrix.transpose_apply, Matrix.neg_apply, symplecticBlock, Matrix.of_apply]
  split_ifs with h1 h2 h3 <;> omega

private lemma symplecticBlock_det (m : ℕ) : (symplecticBlock m).det = 1 := by
  induction m with
  | zero =>
    rw [Matrix.det_eq_one_of_card_eq_zero (Fintype.card_fin 0)]
  | @succ m ih =>
    let e0 : Fin (2 + 2 * m) ≃ Fin (2 * (m + 1)) := finCongr (by ring)
    let e : Fin 2 ⊕ Fin (2 * m) ≃ Fin (2 * (m + 1)) := finSumFinEquiv.trans e0
    let A2 : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of fun a b =>
      if a.val + 1 = b.val then 1 else if b.val + 1 = a.val then -1 else 0
    have hA2_det : A2.det = 1 := by
      rw [Matrix.det_fin_two]
      simp [A2]
    have hblk : (symplecticBlock (m + 1)).submatrix e e =
        Matrix.fromBlocks A2 0 0 (symplecticBlock m) := by
      refine Matrix.ext fun a b => ?_
      rcases a with a | a <;> rcases b with b | b
      · fin_cases a <;> fin_cases b <;> simp [e, e0, symplecticBlock, A2]
      · fin_cases a <;> simp [e, e0, symplecticBlock]
      · fin_cases b <;> simp [e, e0, symplecticBlock]
      · simp only [e, e0, Equiv.trans_apply, finSumFinEquiv_apply_right, Matrix.submatrix_apply,
          finCongr_apply, Matrix.fromBlocks_apply₂₂, symplecticBlock, Matrix.of_apply, Fin.val_cast,
          Fin.val_natAdd]
        have hpar1 : Even (2 + a.val) ↔ Even a.val := by
          simp [Nat.even_add, even_two]
        have hpar2 : Even (2 + b.val) ↔ Even b.val := by
          simp [Nat.even_add, even_two]
        have h1eq : (2 + a.val) + 1 = 2 + b.val ↔ a.val + 1 = b.val := by omega
        have h2eq : (2 + b.val) + 1 = 2 + a.val ↔ b.val + 1 = a.val := by omega
        simp only [hpar1, hpar2, h1eq, h2eq]
    rw [← Matrix.det_submatrix_equiv_self e, hblk, Matrix.det_fromBlocks_zero₂₁, hA2_det, ih,
      one_mul]

private abbrev SkewVar (N : ℕ) := { p : Fin N × Fin N // p.1 < p.2 }

private noncomputable def genericSkew (N : ℕ) : Matrix (Fin N) (Fin N) (MvPolynomial (SkewVar N) ℤ) :=
  Matrix.of fun i j =>
    if h1 : i < j then MvPolynomial.X ⟨(i, j), h1⟩
    else if h2 : j < i then -MvPolynomial.X ⟨(j, i), h2⟩
    else 0

private lemma genericSkew_skew (N : ℕ) :
    (genericSkew N)ᵀ = -genericSkew N ∧ ∀ i, genericSkew N i i = 0 := by
  refine ⟨?_, fun i => by simp [genericSkew]⟩
  ext i j
  simp only [Matrix.transpose_apply, Matrix.neg_apply, genericSkew, Matrix.of_apply]
  rcases lt_trichotomy i j with hij | rfl | hij
  · simp [hij, not_lt_of_gt hij]
  · simp
  · simp [hij, not_lt_of_gt hij]

private lemma genericSkew_det_eq_sq (m : ℕ) :
    ∃ p : MvPolynomial (SkewVar (2 * m)) ℤ, (genericSkew (2 * m)).det = p ^ 2 := by
  induction m with
  | zero =>
    refine ⟨1, ?_⟩
    rw [one_pow, Matrix.det_eq_one_of_card_eq_zero (Fintype.card_fin 0)]
  | @succ m ih =>
    rcases ih with ⟨p0, hp0⟩
    let N : ℕ := 2 * (m + 1)
    let f : Fin (2 * m) ↪ Fin N :=
      ⟨fun t => ⟨t.val + 2, by omega⟩, fun a b h => Fin.ext (by
        have hval := congrArg Fin.val h
        dsimp at hval
        omega)⟩
    have hf_val : ∀ t : Fin (2 * m), (f t).val = t.val + 2 := fun _ => rfl
    let g : Fin 2 ⊕ Fin (2 * m) → Fin N :=
      Sum.elim (fun a => if a.val = 0 then ⟨0, by omega⟩ else ⟨1, by omega⟩) f
    have hg_inj : Function.Injective g := by
      rintro (a | a) (b | b) hab
      · by_cases ha : a.val = 0 <;> by_cases hb : b.val = 0
        · exact congrArg Sum.inl (Fin.ext (by omega))
        · exfalso; have hv := congrArg Fin.val hab; dsimp [g] at hv; simp [ha, hb] at hv
          dsimp [N] at hv; omega
        · exfalso; have hv := congrArg Fin.val hab; dsimp [g] at hv; simp [ha, hb] at hv
          dsimp [N] at hv; omega
        · exact congrArg Sum.inl (Fin.ext (by omega))
      · exfalso
        have hv := congrArg Fin.val hab
        dsimp only [g, Sum.elim_inl, Sum.elim_inr] at hv
        rw [hf_val] at hv
        by_cases ha : a.val = 0 <;> simp only [ha, ↓reduceIte, Fin.val_mk] at hv <;> omega
      · exfalso
        have hv := congrArg Fin.val hab
        dsimp only [g, Sum.elim_inl, Sum.elim_inr] at hv
        rw [hf_val] at hv
        by_cases hb : b.val = 0 <;> simp only [hb, ↓reduceIte, Fin.val_mk] at hv <;> omega
      · exact congrArg Sum.inr (f.injective hab)
    have hcard : Fintype.card (Fin 2 ⊕ Fin (2 * m)) = Fintype.card (Fin N) := by
      simp [N]
      omega
    let e : Fin 2 ⊕ Fin (2 * m) ≃ Fin N :=
      Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hg_inj, hcard⟩)
    let i0 : Fin N := ⟨0, by omega⟩
    let i1 : Fin N := ⟨1, by omega⟩
    have hi01 : i0 ≠ i1 := fun h => by
      have hv := congrArg Fin.val h
      simp only [i0, i1] at hv
      omega
    have he0 : e (Sum.inl 0) = i0 := rfl
    have he1 : e (Sum.inl 1) = i1 := rfl
    have her : ∀ t, e (Sum.inr t) = f t := fun _ => rfl
    have hjac := jacobi_complementary_minor (genericSkew N) hi01 f e he0 he1 her
    have hskew : (genericSkew N)ᵀ = -genericSkew N := (genericSkew_skew N).1
    have hN_even : Even N := ⟨m + 1, by simp [N]; ring⟩
    have hN1 : 1 ≤ N := by omega
    have hadj0 : (genericSkew N).adjugate i0 i0 = 0 :=
      skew_adjugate_diag_eq_zero hN_even hN1 hskew i0
    have hadj1 : (genericSkew N).adjugate i1 i1 = 0 :=
      skew_adjugate_diag_eq_zero hN_even hN1 hskew i1
    have hadj_symm : (genericSkew N).adjugate i1 i0 = -(genericSkew N).adjugate i0 i1 := by
      have htr := skew_adjugate_transpose hN_even hN1 hskew
      calc
        (genericSkew N).adjugate i1 i0 = (genericSkew N).adjugateᵀ i0 i1 := rfl
        _ = (-(genericSkew N).adjugate) i0 i1 := by rw [htr]
        _ = -(genericSkew N).adjugate i0 i1 := rfl
    rw [hadj0, hadj1, hadj_symm] at hjac
    have hsq_eq : ((genericSkew N).adjugate i0 i1) ^ 2 =
        (genericSkew N).det * ((genericSkew N).submatrix f f).det := by
      calc
        ((genericSkew N).adjugate i0 i1) ^ 2
            = 0 * 0 - (genericSkew N).adjugate i0 i1 * (-(genericSkew N).adjugate i0 i1) := by
                ring
        _ = (genericSkew N).det * ((genericSkew N).submatrix f f).det := hjac
    let φ : MvPolynomial (SkewVar (2 * m)) ℤ →+* MvPolynomial (SkewVar N) ℤ :=
      (MvPolynomial.rename fun v => ⟨(f v.1.1, f v.1.2), by
        change v.1.1.val + 2 < v.1.2.val + 2
        have hv : v.1.1.val < v.1.2.val := v.2
        omega⟩).toRingHom
    have hsub_map : (genericSkew N).submatrix f f = (genericSkew (2 * m)).map φ := by
      ext a b
      simp only [Matrix.submatrix_apply, Matrix.map_apply, genericSkew, Matrix.of_apply]
      have hlt_iff1 : f a < f b ↔ a < b := by
        change a.val + 2 < b.val + 2 ↔ a.val < b.val
        omega
      have hlt_iff2 : f b < f a ↔ b < a := by
        change b.val + 2 < a.val + 2 ↔ b.val < a.val
        omega
      rcases lt_trichotomy a b with hab | rfl | hab
      · have hfab : f a < f b := hlt_iff1.mpr hab
        simp [hab, hfab, φ]
      · simp
      · have hfba : f b < f a := hlt_iff2.mpr hab
        have hnot : ¬f a < f b := not_lt_of_gt hfba
        simp [hab, hfba, hnot, not_lt_of_gt hab, φ]
    let q0 : MvPolynomial (SkewVar N) ℤ := φ p0
    have hsub_sq : ((genericSkew N).submatrix f f).det = q0 ^ 2 := by
      rw [hsub_map]
      change (φ.mapMatrix (genericSkew (2 * m))).det = (φ p0) ^ 2
      rw [← RingHom.map_det, hp0, map_pow]
    have hq0_ne : q0 ≠ 0 := by
      intro h0
      let ψ : MvPolynomial (SkewVar N) ℤ →+* ℤ :=
        (MvPolynomial.eval fun v : SkewVar N => symplecticBlock (m + 1) v.1.1 v.1.2)
      have heval_symp : (genericSkew N).map ψ = symplecticBlock (m + 1) := by
        ext a b
        simp only [Matrix.map_apply, genericSkew, Matrix.of_apply, ψ]
        rcases lt_trichotomy a b with hab | rfl | hab
        · simp [hab]
        · simp [symplecticBlock]
        · have hs := (symplecticBlock_skew (m + 1)).1
          have hba : symplecticBlock (m + 1) a b = -symplecticBlock (m + 1) b a :=
            congrArg (fun M : Matrix (Fin N) (Fin N) ℤ => M b a) hs
          simp [hab, not_lt_of_gt hab, hba]
      have heval_sub : ((genericSkew N).submatrix f f).map ψ = symplecticBlock m := by
        ext a b
        have h00 := congrArg (fun M : Matrix (Fin N) (Fin N) ℤ => M (f a) (f b)) heval_symp
        simp only [Matrix.map_apply, Matrix.submatrix_apply] at h00 ⊢
        rw [h00]
        have hpar1 : Even (a.val + 2) ↔ Even a.val := by simp [Nat.even_add, even_two]
        have hpar2 : Even (b.val + 2) ↔ Even b.val := by simp [Nat.even_add, even_two]
        have h1eq : (a.val + 2) + 1 = b.val + 2 ↔ a.val + 1 = b.val := by omega
        have h2eq : (b.val + 2) + 1 = a.val + 2 ↔ b.val + 1 = a.val := by omega
        simp only [symplecticBlock, Matrix.of_apply, hf_val, hpar1, hpar2, h1eq, h2eq]
      have hdet_one : ψ (q0 ^ 2) = 1 := by
        rw [← hsub_sq]
        rw [RingHom.map_det, RingHom.mapMatrix_apply, heval_sub, symplecticBlock_det m]
      rw [h0, zero_pow two_ne_zero, map_zero] at hdet_one
      exact one_ne_zero hdet_one.symm
    let P := MvPolynomial (SkewVar N) ℤ
    let F := FractionRing P
    have hq0_F : algebraMap P F q0 ≠ 0 :=
      mt (fun h => IsFractionRing.injective P F (by simpa using h)) hq0_ne
    let w : F := algebraMap P F ((genericSkew N).adjugate i0 i1) / algebraMap P F q0
    have hw_sq : w ^ 2 = algebraMap P F ((genericSkew N).det) := by
      rw [div_pow, div_eq_iff (pow_ne_zero 2 hq0_F)]
      calc
        algebraMap P F ((genericSkew N).adjugate i0 i1) ^ 2
            = algebraMap P F (((genericSkew N).adjugate i0 i1) ^ 2) := (map_pow _ _ _).symm
        _ = algebraMap P F ((genericSkew N).det * q0 ^ 2) := by rw [hsq_eq, hsub_sq]
        _ = algebraMap P F (genericSkew N).det * algebraMap P F q0 ^ 2 := by
            rw [map_mul, map_pow]
    have hw_int : IsIntegral P (w ^ 2) := by
      rw [hw_sq]
      exact isIntegral_algebraMap
    obtain ⟨p, hp⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := P)
      (by omega : 0 < 2) hw_int
    refine ⟨p, ?_⟩
    apply IsFractionRing.injective P F
    rw [map_pow, hp, hw_sq]

/-- **Cayley's Pfaffian Square Theorem:** Over any commutative ring `R`, the determinant of any
skew-symmetric `(2m) × (2m)` matrix with zero diagonal is a square in `R`. -/
theorem skew_det_eq_sq {m : ℕ} {R : Type*} [CommRing R]
    {K : Matrix (Fin (2 * m)) (Fin (2 * m)) R}
    (hskew : Kᵀ = -K) (hdiag : ∀ i, K i i = 0) :
    ∃ p : R, K.det = p ^ 2 := by
  obtain ⟨p0, hp0⟩ := genericSkew_det_eq_sq m
  let φ : MvPolynomial (SkewVar (2 * m)) ℤ →+* R :=
    (MvPolynomial.eval₂Hom (Int.castRingHom R) fun v => K v.1.1 v.1.2)
  have hmap : (genericSkew (2 * m)).map φ = K := by
    ext i j
    simp only [Matrix.map_apply, genericSkew, Matrix.of_apply, φ]
    rcases lt_trichotomy i j with hij | rfl | hij
    · simp [hij]
    · simp [hdiag i]
    · have hji : K i j = -K j i :=
        congrArg (fun M : Matrix (Fin (2 * m)) (Fin (2 * m)) R => M j i) hskew
      simp only [hij, not_lt_of_gt hij]
      change φ (-MvPolynomial.X ⟨(j, i), hij⟩) = K i j
      rw [map_neg, hji]
      congr 1
      simp [φ]
  refine ⟨φ p0, ?_⟩
  calc
    K.det = (φ.mapMatrix (genericSkew (2 * m))).det := by rw [RingHom.mapMatrix_apply, hmap]
    _ = φ (genericSkew (2 * m)).det := (RingHom.map_det φ (genericSkew (2 * m))).symm
    _ = φ (p0 ^ 2) := by rw [hp0]
    _ = (φ p0) ^ 2 := map_pow φ p0 2

end Pfaffian

/-! ## Section 3: Theorem 4.2 (Exact mod-`2^{n+1}` congruence for odd `n`) -/

section Thm42

private lemma exists_eulerian_switching {n : ℕ} (hn : Odd n)
    {S : Matrix (Fin n) (Fin n) ℤ} (hS : IsSeidelMatrix S) :
    ∃ d : Fin n → ℤ, (∀ i, d i = 1 ∨ d i = -1) ∧
      let S' := IsSeidelMatrix.switch d S
      IsSeidelMatrix S' ∧ S'.charpoly = S.charpoly ∧
        ∃ w : Fin n → ℤ,
          (Matrix.of fun i j : Fin n => if i = j then 0 else (1 - S' i j) / 2) *ᵥ (fun _ => 1) =
            (2 : ℤ) • w := by
  let A : Matrix (Fin n) (Fin n) ℤ :=
    Matrix.of fun i j => if i = j then 0 else (1 - S i j) / 2
  have hSymm : Aᵀ = A := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [A]
    · have hSij : S j i = S i j := by
        calc
          S j i = Sᵀ i j := rfl
          _ = S i j := by rw [hS.1]
      simp [A, hij, Ne.symm hij, hSij]
  have hdiag : ∀ i, A i i = 0 := fun i => by simp [A]
  let deg : Fin n → ℤ := fun i => ∑ j : Fin n, A i j
  let U : Finset (Fin n) := Finset.univ.filter (fun i => Odd (deg i))
  have hsum_deg_even : Even (∑ i : Fin n, deg i) := by
    have hsp := sum_matrix_symm_split A hSymm
    simp only [hdiag, Finset.sum_const_zero, zero_add] at hsp
    refine ⟨∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), A p.1 p.2, ?_⟩
    rw [hsp, two_mul]
  have hU_even : Even U.card := by
    rw [even_iff_two_dvd, ← Int.natCast_dvd_natCast, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hsum_zmod : (∑ i : Fin n, (deg i : ZMod 2)) = 0 := by
      rw [← Int.cast_sum]
      rcases hsum_deg_even with ⟨t, ht⟩
      rw [ht, ← two_mul, Int.cast_mul]
      have h2 : (2 : ZMod 2) = 0 := rfl
      simp [h2]
    have hdeg_zmod : ∀ i : Fin n, (deg i : ZMod 2) = if i ∈ U then 1 else 0 := by
      intro i
      by_cases hi : i ∈ U
      · have hodd : Odd (deg i) := (Finset.mem_filter.mp hi).2
        rcases hodd with ⟨t, ht⟩
        simp only [hi, ↓reduceIte, ht]
        have h2 : (2 : ZMod 2) = 0 := rfl
        push_cast
        rw [h2, zero_mul, zero_add]
      · have heven : Even (deg i) := by
          rw [← Int.not_odd_iff_even]
          intro hodd
          exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hodd⟩)
        rcases heven with ⟨t, ht⟩
        simp only [hi, ↓reduceIte, ht, ← two_mul]
        have h2 : (2 : ZMod 2) = 0 := rfl
        push_cast
        rw [h2, zero_mul]
    simp_rw [hdeg_zmod, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_eq_mul, mul_one] at hsum_zmod
    simpa [U] using hsum_zmod
  let d : Fin n → ℤ := fun i => if i ∈ U then -1 else 1
  have hd : ∀ i, d i = 1 ∨ d i = -1 := fun i => by
    by_cases hi : i ∈ U <;> simp [d, hi]
  let S' := IsSeidelMatrix.switch d S
  have hS' : IsSeidelMatrix S' := hS.switch_isSeidelMatrix hd
  have hchar : S'.charpoly = S.charpoly := IsSeidelMatrix.switch_charpoly S hd
  let A' : Matrix (Fin n) (Fin n) ℤ :=
    Matrix.of fun i j => if i = j then 0 else (1 - S' i j) / 2
  have hS_rel : ∀ i j : Fin n, i ≠ j → S i j = 1 - 2 * A i j := fun i j hij => by
    simp only [A, Matrix.of_apply, hij, ↓reduceIte]
    rcases hS.2.2 i j hij with h | h <;> simp [h]
  have hS'_rel : ∀ i j : Fin n, i ≠ j → 2 * A' i j = 1 - S' i j := fun i j hij => by
    simp only [A', Matrix.of_apply, hij, ↓reduceIte]
    rcases hS'.2.2 i j hij with h | h <;> simp [h]
  have heven_deg' : ∀ i : Fin n, Even (∑ j : Fin n, A' i j) := by
    intro i
    rw [even_iff_two_dvd]
    have hsum_mod4 : (4 : ℤ) ∣ ((n - 1 : ℤ) - ∑ j : Fin n, S' i j) := by
      have hterm_dvd : ∀ j : Fin n,
          (4 : ℤ) ∣ (S' i j - (if i = j then 0 else d i * d j - 2 * A i j)) := by
        intro j
        by_cases hij : i = j
        · subst hij; simp [hS'.2.1 i]
        · simp only [hij, ↓reduceIte]
          have h1 : S' i j = d i * d j * (1 - 2 * A i j) := by
            dsimp [S']
            rw [IsSeidelMatrix.switch_apply, hS_rel i j hij]
            ring
          have heq : S' i j - (d i * d j - 2 * A i j) = 2 * (1 - d i * d j) * A i j := by
            rw [h1]; ring
          rw [heq]
          have h4 : (4 : ℤ) ∣ 2 * (1 - d i * d j) := by
            rcases hd i with hdi | hdi <;> rcases hd j with hdj | hdj <;> simp [hdi, hdj]
          exact dvd_mul_of_dvd_left h4 _
      have hsum_dvd : (4 : ℤ) ∣
          ∑ j : Fin n, (S' i j - (if i = j then 0 else d i * d j - 2 * A i j)) :=
        Finset.dvd_sum fun j _ => hterm_dvd j
      have hsum_eval :
          (∑ j : Fin n, (if i = j then (0 : ℤ) else d i * d j - 2 * A i j)) =
            d i * (∑ j : Fin n, d j) - 1 - 2 * deg i := by
        have hddi : d i * d i = 1 := by rcases hd i with h | h <;> simp [h]
        have h1 : (∑ j : Fin n, (if i = j then (0 : ℤ) else d i * d j - 2 * A i j)) =
            (∑ j : Fin n, (d i * d j - 2 * A i j)) - (d i * d i - 2 * A i i) := by
          rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
          have hz : (if i = i then (0 : ℤ) else d i * d i - 2 * A i i) = 0 := by simp
          rw [hz, zero_add]
          have hsub : (∑ x ∈ Finset.univ.erase i, (if i = x then (0 : ℤ) else d i * d x - 2 * A i x)) =
              ∑ x ∈ Finset.univ.erase i, (d i * d x - 2 * A i x) := by
            refine Finset.sum_congr rfl fun x hx => ?_
            have hne : i ≠ x := (Finset.mem_erase.mp hx).1.symm
            simp [hne]
          rw [hsub]
          conv_rhs => rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
          ring
        rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hddi, hdiag i]
        simp only [deg]
        ring
      have hsum_d : (∑ j : Fin n, d j) = (n : ℤ) - 2 * (U.card : ℤ) := by
        have hd_eq : ∀ j : Fin n, d j = 1 - (if j ∈ U then (2 : ℤ) else 0) := fun j => by
          by_cases hj : j ∈ U <;> simp [d, hj]
        simp_rw [hd_eq, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, mul_one, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
          nsmul_eq_mul]
        have hinter : Finset.univ.filter (fun x => x ∈ U) = U := by ext x; simp
        rw [hinter]
        ring
      have hmain : (4 : ℤ) ∣ ((n - 1 : ℤ) - (d i * (∑ j : Fin n, d j) - 1 - 2 * deg i)) := by
        rw [hsum_d]
        rcases hn with ⟨m, rfl⟩
        rcases hU_even with ⟨k, hk⟩
        have hUk : (U.card : ℤ) = 2 * (k : ℤ) := by omega
        rw [hUk]
        by_cases hi : i ∈ U
        · have hdi : d i = -1 := by simp [d, hi]
          have hodd : Odd (deg i) := (Finset.mem_filter.mp hi).2
          rcases hodd with ⟨t, ht⟩
          rw [hdi, ht]
          refine ⟨(m : ℤ) - (k : ℤ) + t + 1, ?_⟩
          push_cast
          ring
        · have hdi : d i = 1 := by simp [d, hi]
          have heven : Even (deg i) := by
            rw [← Int.not_odd_iff_even]
            intro hodd
            exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hodd⟩)
          rcases heven with ⟨t, ht⟩
          rw [hdi, ht]
          refine ⟨(k : ℤ) + t, ?_⟩
          push_cast
          ring
      rw [Finset.sum_sub_distrib, hsum_eval] at hsum_dvd
      have hcomb : (n - 1 : ℤ) - ∑ j : Fin n, S' i j =
          ((n - 1 : ℤ) - (d i * (∑ j : Fin n, d j) - 1 - 2 * deg i)) -
            ((∑ j : Fin n, S' i j) - (d i * (∑ j : Fin n, d j) - 1 - 2 * deg i)) := by ring
      rw [hcomb]
      exact dvd_sub hmain hsum_dvd
    have htwice : 2 * ∑ j : Fin n, A' i j = (n - 1 : ℤ) - ∑ j : Fin n, S' i j := by
      rw [Finset.mul_sum]
      have hterm : ∀ j : Fin n, 2 * A' i j = (if i = j then 0 else 1) - S' i j := by
        intro j
        by_cases hij : i = j
        · subst hij; simp [A', hS'.2.1 i]
        · simp only [hij, ↓reduceIte]
          exact hS'_rel i j hij
      simp_rw [hterm, Finset.sum_sub_distrib]
      have hones : (∑ j : Fin n, (if i = j then (0 : ℤ) else 1)) = (n : ℤ) - 1 := by
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
        simp only [↓reduceIte, zero_add]
        have hc : (∑ x ∈ Finset.univ.erase i, (if i = x then (0 : ℤ) else 1)) =
            ∑ _x ∈ Finset.univ.erase i, (1 : ℤ) := by
          refine Finset.sum_congr rfl fun x hx => ?_
          simp [(Finset.mem_erase.mp hx).1.symm]
        rw [hc, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        have hn_pos : 1 ≤ n := by rcases hn with ⟨m, rfl⟩; omega
        zify [hn_pos]
      rw [hones]
    rcases hsum_mod4 with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    linarith
  choose w hw using heven_deg'
  refine ⟨d, hd, hS', hchar, w, ?_⟩
  ext i
  simp only [Matrix.mulVec, dotProduct, mul_one, Pi.smul_apply, smul_eq_mul]
  rw [hw i, two_mul]

private def jSym (m : ℕ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℤ :=
  Matrix.of fun i j => if i < j then 1 else if j < i then -1 else 0

private lemma jSym_det_one (m : ℕ) : (jSym m).det = 1 := by
  induction m with
  | zero =>
    rw [Matrix.det_eq_one_of_card_eq_zero (Fintype.card_fin 0)]
  | @succ m ih =>
    let N : ℕ := 2 * (m + 1)
    let E_row : Matrix (Fin N) (Fin N) ℤ := Matrix.of fun i j =>
      if i = j then 1 else if i.val = 1 ∧ j.val = 0 then -1 else 0
    have hE_row_tri : E_row.IsLowerTriangular := by
      intro i j hij
      have hne : i ≠ j := ne_of_lt hij
      have hval : i.val < j.val := hij
      simp only [E_row, Matrix.of_apply, hne, ↓reduceIte]
      split_ifs with h
      · omega
      · rfl
    have hE_row_det : E_row.det = 1 := by
      rw [Matrix.det_of_isLowerTriangular _ hE_row_tri]
      simp [E_row]
    let E_col : Matrix (Fin N) (Fin N) ℤ := E_rowᵀ
    have hE_col_det : E_col.det = 1 := by
      rw [Matrix.det_transpose, hE_row_det]
    let E2 : Matrix (Fin N) (Fin N) ℤ := Matrix.of fun i j =>
      if i = j then 1 else if 2 ≤ i.val ∧ j.val = 1 then -1 else 0
    have hE2_tri : E2.IsLowerTriangular := by
      intro i j hij
      have hne : i ≠ j := ne_of_lt hij
      have hval : i.val < j.val := hij
      simp only [E2, Matrix.of_apply, hne, ↓reduceIte]
      split_ifs with h
      · omega
      · rfl
    have hE2_det : E2.det = 1 := by
      rw [Matrix.det_of_isLowerTriangular _ hE2_tri]
      simp [E2]
    let M1 : Matrix (Fin N) (Fin N) ℤ := E_row * jSym (m + 1) * E_col
    have h1_val : ((1 : Fin N) : ℕ) = 1 := Nat.mod_eq_of_lt (by dsimp [N]; omega)
    have h0_val : ((0 : Fin N) : ℕ) = 0 := rfl
    have h01 : (0 : Fin N) ≠ 1 := fun h => by
      have := congrArg Fin.val h; rw [h0_val, h1_val] at this; omega
    have hEA : ∀ i k : Fin N, (E_row * jSym (m + 1)) i k =
        if i.val = 1 then jSym (m + 1) 1 k - jSym (m + 1) 0 k
        else jSym (m + 1) i k := by
      intro i k
      rw [Matrix.mul_apply]
      by_cases hi1 : i.val = 1
      · simp only [hi1, ↓reduceIte]
        have hi_one : i = 1 := Fin.ext (hi1.trans h1_val.symm)
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
        have hi0 : (0 : Fin N) ∈ Finset.univ.erase i :=
          Finset.mem_erase.mpr ⟨fun h => h01 (h.trans hi_one), Finset.mem_univ _⟩
        rw [← Finset.add_sum_erase _ _ hi0]
        have hrest : ∑ x ∈ (Finset.univ.erase i).erase 0,
            E_row i x * jSym (m + 1) x k = 0 := by
          refine Finset.sum_eq_zero fun x hx => ?_
          have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
          have hxi : x ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
          have hxv : x.val ≠ 0 := fun h => hx0 (Fin.ext (h.trans h0_val.symm))
          have hE : E_row i x = 0 := by
            simp only [E_row, Matrix.of_apply, Ne.symm hxi, ↓reduceIte, hxv, and_false]
          rw [hE, zero_mul]
        rw [hrest, add_zero]
        have hii : E_row i i = 1 := by simp [E_row]
        have hi_z : E_row i 0 = -1 := by
          have hne : i ≠ 0 := fun h => h01 (hi_one.symm.trans h).symm
          simp only [E_row, Matrix.of_apply, hne, ↓reduceIte, hi1, h0_val, and_self]
        rw [hii, hi_z, hi_one]
        ring
      · simp only [hi1, ↓reduceIte]
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
        have hrest : ∑ x ∈ Finset.univ.erase i, E_row i x * jSym (m + 1) x k = 0 := by
          refine Finset.sum_eq_zero fun x hx => ?_
          have hxi : x ≠ i := (Finset.mem_erase.mp hx).1
          have hE : E_row i x = 0 := by
            simp only [E_row, Matrix.of_apply, Ne.symm hxi, ↓reduceIte, hi1, false_and]
          rw [hE, zero_mul]
        rw [hrest, add_zero]
        simp [E_row]
    have hM1 : ∀ i j : Fin N, M1 i j =
        if j.val = 1 then (E_row * jSym (m + 1)) i 1 - (E_row * jSym (m + 1)) i 0
        else (E_row * jSym (m + 1)) i j := by
      intro i j
      dsimp [M1]
      rw [Matrix.mul_apply]
      by_cases hj1 : j.val = 1
      · simp only [hj1, ↓reduceIte]
        have hj_one : j = 1 := Fin.ext (hj1.trans h1_val.symm)
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
        have hj0 : (0 : Fin N) ∈ Finset.univ.erase j :=
          Finset.mem_erase.mpr ⟨fun h => h01 (h.trans hj_one), Finset.mem_univ _⟩
        rw [← Finset.add_sum_erase _ _ hj0]
        have hrest : ∑ x ∈ (Finset.univ.erase j).erase 0,
            (E_row * jSym (m + 1)) i x * E_col x j = 0 := by
          refine Finset.sum_eq_zero fun x hx => ?_
          have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
          have hxj : x ≠ j := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
          have hxv : x.val ≠ 0 := fun h => hx0 (Fin.ext (h.trans h0_val.symm))
          have hE : E_col x j = 0 := by
            simp only [E_col, Matrix.transpose_apply, E_row, Matrix.of_apply, hxj.symm, ↓reduceIte,
              hxv, and_false]
          rw [hE, mul_zero]
        rw [hrest, add_zero]
        have hjj : E_col j j = 1 := by simp [E_col, E_row]
        have hj_z : E_col 0 j = -1 := by
          have hne : j ≠ 0 := fun h => h01 (hj_one.symm.trans h).symm
          simp only [E_col, Matrix.transpose_apply, E_row, Matrix.of_apply, hne, ↓reduceIte, hj1,
            h0_val, and_self]
        rw [hjj, hj_z, hj_one]
        ring
      · simp only [hj1, ↓reduceIte]
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
        have hrest : ∑ x ∈ Finset.univ.erase j, (E_row * jSym (m + 1)) i x * E_col x j = 0 := by
          refine Finset.sum_eq_zero fun x hx => ?_
          have hxj : x ≠ j := (Finset.mem_erase.mp hx).1
          have hE : E_col x j = 0 := by
            simp only [E_col, Matrix.transpose_apply, E_row, Matrix.of_apply, hxj.symm, ↓reduceIte,
              hj1, false_and]
          rw [hE, mul_zero]
        rw [hrest, add_zero]
        simp [E_col, E_row]
    let M : Matrix (Fin N) (Fin N) ℤ := E2 * M1
    have hM_mul : ∀ i j : Fin N, M i j =
        if 2 ≤ i.val then M1 i j - M1 1 j else M1 i j := by
      intro i j
      dsimp [M]
      rw [Matrix.mul_apply]
      by_cases hi2 : 2 ≤ i.val
      · simp only [hi2, ↓reduceIte]
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
        have h1i : (1 : Fin N) ≠ i := fun h => by
          have := congrArg Fin.val h; rw [h1_val] at this; omega
        have hi1 : (1 : Fin N) ∈ Finset.univ.erase i :=
          Finset.mem_erase.mpr ⟨h1i, Finset.mem_univ _⟩
        rw [← Finset.add_sum_erase _ _ hi1]
        have hrest : ∑ x ∈ (Finset.univ.erase i).erase 1, E2 i x * M1 x j = 0 := by
          refine Finset.sum_eq_zero fun x hx => ?_
          have hx1 : x ≠ 1 := (Finset.mem_erase.mp hx).1
          have hxi : x ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
          have hxv : x.val ≠ 1 := fun h => hx1 (Fin.ext (h.trans h1_val.symm))
          have hE : E2 i x = 0 := by
            simp only [E2, Matrix.of_apply, Ne.symm hxi, ↓reduceIte, hxv, and_false]
          rw [hE, zero_mul]
        rw [hrest, add_zero]
        have hii : E2 i i = 1 := by simp [E2]
        have hi_o : E2 i 1 = -1 := by
          simp only [E2, Matrix.of_apply, h1i.symm, ↓reduceIte, hi2, h1_val, and_self]
        rw [hii, hi_o]
        ring
      · simp only [hi2, ↓reduceIte]
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
        have hrest : ∑ x ∈ Finset.univ.erase i, E2 i x * M1 x j = 0 := by
          refine Finset.sum_eq_zero fun x hx => ?_
          have hxi : x ≠ i := (Finset.mem_erase.mp hx).1
          have hE : E2 i x = 0 := by
            simp only [E2, Matrix.of_apply, Ne.symm hxi, ↓reduceIte, hi2, false_and]
          rw [hE, zero_mul]
        rw [hrest, add_zero]
        simp [E2]
    let e0 : Fin (2 + 2 * m) ≃ Fin N := finCongr (by simp [N]; ring)
    let e : Fin 2 ⊕ Fin (2 * m) ≃ Fin N := finSumFinEquiv.trans e0
    let A2 : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of fun a b =>
      if a.val + 1 = b.val then 1 else if b.val + 1 = a.val then -1 else 0
    have hA2_det : A2.det = 1 := by rw [Matrix.det_fin_two]; simp [A2]
    let B_blk : Matrix (Fin 2) (Fin (2 * m)) ℤ := Matrix.of fun a _ =>
      if a.val = 0 then 1 else 0
    have he_inl : ∀ a : Fin 2, (e (Sum.inl a)).val = a.val := fun _ => rfl
    have he_inr : ∀ a : Fin (2 * m), (e (Sum.inr a)).val = 2 + a.val := fun _ => rfl
    have hE_ge2 : ∀ (i k : Fin N), 2 ≤ i.val →
        (E_row * jSym (m + 1)) i k = jSym (m + 1) i k := fun i k hi => by
      rw [hEA]; simp only [show i.val ≠ 1 by omega, ↓reduceIte]
    have hE_1 : ∀ k : Fin N,
        (E_row * jSym (m + 1)) 1 k = jSym (m + 1) 1 k - jSym (m + 1) 0 k := fun k => by
      rw [hEA]; simp only [h1_val, ↓reduceIte]
    have hE_lt2 : ∀ (i k : Fin N), i.val < 2 →
        (E_row * jSym (m + 1)) i k =
          if i.val = 1 then jSym (m + 1) 1 k - jSym (m + 1) 0 k else jSym (m + 1) i k :=
      fun i k _ => hEA i k
    have hblk : M.submatrix e e = Matrix.fromBlocks A2 B_blk 0 (jSym m) := by
      refine Matrix.ext fun a b => ?_
      rcases a with a | a <;> rcases b with b | b
      · have ha2 : a.val < 2 := a.isLt
        have hb2 : b.val < 2 := b.isLt
        rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, hM_mul]
        simp only [show ¬ 2 ≤ (e (Sum.inl a)).val by rw [he_inl]; omega, ↓reduceIte]
        rw [hM1]
        by_cases hb1 : (e (Sum.inl b)).val = 1
        · simp only [hb1, ↓reduceIte]
          rw [hE_lt2 _ _ (by rw [he_inl]; omega), hE_lt2 _ _ (by rw [he_inl]; omega)]
          simp only [A2, jSym, Matrix.of_apply, Fin.lt_def, he_inl, h0_val, h1_val] at hb1 ⊢
          split_ifs <;> omega
        · simp only [hb1, ↓reduceIte]
          rw [hE_lt2 _ _ (by rw [he_inl]; omega)]
          simp only [A2, jSym, Matrix.of_apply, Fin.lt_def, he_inl, h0_val, h1_val] at hb1 ⊢
          split_ifs <;> omega
      · have ha2 : a.val < 2 := a.isLt
        rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, hM_mul]
        simp only [show ¬ 2 ≤ (e (Sum.inl a)).val by rw [he_inl]; omega, ↓reduceIte]
        rw [hM1]
        simp only [show (e (Sum.inr b)).val ≠ 1 by rw [he_inr]; omega, ↓reduceIte]
        rw [hE_lt2 _ _ (by rw [he_inl]; omega)]
        simp only [B_blk, jSym, Matrix.of_apply, Fin.lt_def, he_inl, he_inr, h0_val, h1_val]
        split_ifs <;> omega
      · have hb2 : b.val < 2 := b.isLt
        rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, hM_mul]
        simp only [show 2 ≤ (e (Sum.inr a)).val by rw [he_inr]; omega, ↓reduceIte]
        rw [hM1, hM1]
        by_cases hb1 : (e (Sum.inl b)).val = 1
        · simp only [hb1, ↓reduceIte]
          rw [hE_ge2 _ _ (by rw [he_inr]; omega), hE_ge2 _ _ (by rw [he_inr]; omega), hE_1, hE_1]
          simp only [jSym, Matrix.of_apply, Fin.lt_def, he_inl, he_inr, h0_val, h1_val] at hb1 ⊢
          split_ifs <;> omega
        · simp only [hb1, ↓reduceIte]
          rw [hE_ge2 _ _ (by rw [he_inr]; omega), hE_1]
          simp only [jSym, Matrix.of_apply, Fin.lt_def, he_inl, he_inr, h0_val, h1_val] at hb1 ⊢
          split_ifs <;> omega
      · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, hM_mul]
        simp only [show 2 ≤ (e (Sum.inr a)).val by rw [he_inr]; omega, ↓reduceIte]
        rw [hM1, hM1]
        simp only [show (e (Sum.inr b)).val ≠ 1 by rw [he_inr]; omega, ↓reduceIte]
        rw [hE_ge2 _ _ (by rw [he_inr]; omega), hE_1]
        simp only [jSym, Matrix.of_apply, Fin.lt_def, he_inr, h0_val, h1_val]
        split_ifs <;> omega
    have hM_det : M.det = (jSym (m + 1)).det := by
      dsimp [M, M1]
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, hE2_det, hE_row_det, hE_col_det,
        one_mul, one_mul, mul_one]
    rw [← hM_det, ← Matrix.det_submatrix_equiv_self e, hblk, Matrix.det_fromBlocks_zero₂₁,
      hA2_det, ih, one_mul]

private lemma basis_matrix_det {n : ℕ} (hn : 1 ≤ n) :
    (Matrix.of fun i j : Fin n =>
      if j.val = 0 then (1 : ℤ) else if i = j then 1 else if i.val = 0 then -1 else 0).det =
      (n : ℤ) := by
  let L : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j =>
    if j.val = 0 then 1 else if i = j then 1 else 0
  have hL_tri : L.IsLowerTriangular := by
    intro i j hij
    have hne : i ≠ j := ne_of_lt hij
    have hj0 : j.val ≠ 0 := by
      have : i.val < j.val := hij
      omega
    simp [L, hne, hj0]
  have hL_det : L.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular _ hL_tri]
    simp [L]
  let Linv : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j =>
    if i = j then 1 else if j.val = 0 then -1 else 0
  have hL_inv : L * Linv = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
      have hrest : ∑ x ∈ Finset.univ.erase i, L i x * Linv x i = 0 := by
        refine Finset.sum_eq_zero fun x hx => ?_
        have hxi : x ≠ i := (Finset.mem_erase.mp hx).1
        by_cases hx0 : x.val = 0
        · have hi0 : i.val ≠ 0 := fun h => hxi (Fin.ext (hx0.trans h.symm))
          simp [L, Linv, hxi, hx0, hi0]
        · simp [L, Linv, hxi, Ne.symm hxi, hx0]
      rw [hrest, add_zero]
      simp [L, Linv]
    · rw [Matrix.one_apply_ne hij]
      by_cases hj0 : j.val = 0
      · rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
        have hi_mem : i ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩
        rw [← Finset.add_sum_erase _ _ hi_mem]
        have hrest : ∑ x ∈ (Finset.univ.erase j).erase i, L i x * Linv x j = 0 := by
          refine Finset.sum_eq_zero fun x hx => ?_
          have hxi : x ≠ i := (Finset.mem_erase.mp hx).1
          have hxj : x ≠ j := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
          have hx0 : x.val ≠ 0 := fun h => hxj (Fin.ext (h.trans hj0.symm))
          simp [L, Linv, hxi.symm, hx0]
        rw [hrest, add_zero]
        have hii : L i i = 1 := by simp [L]
        have hijL : L i j = 1 := by simp [L, hj0]
        have hjj : Linv j j = 1 := by simp [Linv]
        have hijR : Linv i j = -1 := by simp [Linv, hij, hj0]
        rw [hii, hijL, hjj, hijR]
        ring
      · refine Finset.sum_eq_zero fun x _ => ?_
        by_cases hxi : x = i
        · subst hxi; simp [Linv, hij, hj0]
        · by_cases hx0 : x.val = 0
          · simp [Linv, show x ≠ j from fun h => hj0 (h ▸ hx0), hj0]
          · simp [L, Ne.symm hxi, hx0]
  have hadj : L.adjugate = Linv := by
    calc
      L.adjugate = L.adjugate * 1 := (Matrix.mul_one _).symm
      _ = L.adjugate * (L * Linv) := by rw [hL_inv]
      _ = (L.adjugate * L) * Linv := (Matrix.mul_assoc _ _ _).symm
      _ = (L.det • (1 : Matrix (Fin n) (Fin n) ℤ)) * Linv := by rw [Matrix.adjugate_mul]
      _ = Linv := by rw [hL_det, one_smul, Matrix.one_mul]
  let u : Fin n → ℤ := fun i => if i.val = 0 then -1 else 0
  let v : Fin n → ℤ := fun j => if j.val = 0 then 0 else 1
  have hQ_eq : (Matrix.of fun i j : Fin n =>
      if j.val = 0 then (1 : ℤ) else if i = j then 1 else if i.val = 0 then -1 else 0) =
      L + Matrix.vecMulVec u v := by
    ext i j
    simp only [Matrix.add_apply, Matrix.of_apply, Matrix.vecMulVec_apply, L, u, v]
    by_cases hj0 : j.val = 0
    · simp [hj0]
    · by_cases hij : i = j
      · subst hij; simp [hj0]
      · by_cases hi0 : i.val = 0 <;> simp [hj0, hij, hi0]
  rw [hQ_eq, det_add_vecMulVec, hL_det, hadj]
  simp only [dotProduct, Matrix.mulVec, u, v]
  have hi0 : (⟨0, hn⟩ : Fin n) ∈ Finset.univ := Finset.mem_univ _
  have hsum : (∑ j : Fin n, (if j.val = 0 then (0 : ℤ) else 1) *
      ∑ i : Fin n, Linv j i * (if i.val = 0 then (-1 : ℤ) else 0)) = (n : ℤ) - 1 := by
    have hj_term : ∀ j : Fin n,
        (if j.val = 0 then (0 : ℤ) else 1) *
          ∑ i : Fin n, Linv j i * (if i.val = 0 then (-1 : ℤ) else 0) =
          if j.val = 0 then 0 else 1 := by
      intro j
      by_cases hj0 : j.val = 0
      · simp [hj0]
      · simp only [hj0, ↓reduceIte, one_mul]
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (⟨0, hn⟩ : Fin n))]
        have hrest : ∑ x ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
            Linv j x * (if x.val = 0 then (-1 : ℤ) else 0) = 0 := by
          refine Finset.sum_eq_zero fun x hx => ?_
          have hx0 : x ≠ ⟨0, hn⟩ := (Finset.mem_erase.mp hx).1
          have hxv : x.val ≠ 0 := fun h => hx0 (Fin.ext h)
          simp [hxv]
        rw [hrest, add_zero]
        have hjn0 : j ≠ ⟨0, hn⟩ := fun h => hj0 (by simpa using congrArg Fin.val h)
        simp [Linv, hjn0]
    simp_rw [hj_term]
    rw [← Finset.add_sum_erase Finset.univ _ hi0]
    have hc : ∑ x ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), (if x.val = 0 then (0 : ℤ) else (1 : ℤ)) =
        ∑ _x ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), (1 : ℤ) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx0 : x ≠ ⟨0, hn⟩ := (Finset.mem_erase.mp hx).1
      have hxv : x.val ≠ 0 := fun h => hx0 (Fin.ext h)
      simp [hxv]
    simp only [↓reduceIte, zero_add]
    rw [hc, Finset.sum_const, Finset.card_erase_of_mem hi0, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    zify [hn]
  rw [hsum]
  ring

private lemma det_add_two_mul_mod4 {k : ℕ} (K L : Matrix (Fin k) (Fin k) ℤ[X]) :
    C (4 : ℤ) ∣ (K + C (2 : ℤ) • L).det - (K.det + C (2 : ℤ) * (K.adjugate * L).trace) := by
  let F : Finset (Fin k) → ℤ[X] := fun t =>
    ∑ σ : Equiv.Perm (Fin k),
      Equiv.Perm.sign σ • ((∏ i ∈ t, C (2 : ℤ) * L (σ i) i) * ∏ i ∈ Finset.univ \ t, K (σ i) i)
  have hdet_split : (K + C (2 : ℤ) • L).det =
      ∑ t ∈ (Finset.univ : Finset (Fin k)).powerset, F t := by
    rw [Matrix.det_apply]
    have hprod : ∀ σ : Equiv.Perm (Fin k),
        Equiv.Perm.sign σ • ∏ i : Fin k, (K + C (2 : ℤ) • L) (σ i) i =
          ∑ t ∈ (Finset.univ : Finset (Fin k)).powerset,
            Equiv.Perm.sign σ •
              ((∏ i ∈ t, C (2 : ℤ) * L (σ i) i) * ∏ i ∈ Finset.univ \ t, K (σ i) i) := by
      intro σ
      have hfun : ∀ i : Fin k, (K + C (2 : ℤ) • L) (σ i) i =
          C (2 : ℤ) * L (σ i) i + K (σ i) i := fun i => by
        rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_comm]
      rw [Finset.prod_congr rfl (fun i _ => hfun i)]
      rw [Finset.prod_add (fun i => C (2 : ℤ) * L (σ i) i) (fun i => K (σ i) i) Finset.univ,
        Finset.smul_sum]
    simp_rw [hprod]
    exact Finset.sum_comm
  have hF0 : F ∅ = K.det := by
    simp [F, Matrix.det_apply]
  have hF1 : ∀ j : Fin k, F {j} = C (2 : ℤ) * ∑ i : Fin k, K.adjugate j i * L i j := by
    intro j
    let w : Fin k → ℤ[X] := fun i => C (2 : ℤ) * L i j
    have hupd_det : F {j} = (K.updateCol j w).det := by
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
    rw [hupd_det, Matrix.det_eq_sum_mul_adjugate_col (K.updateCol j w) j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hadj : (K.updateCol j w).adjugate j i = K.adjugate j i := by
      have htr : (K.updateCol j w)ᵀ = Kᵀ.updateRow j w := by
        refine Matrix.ext fun a b => ?_
        by_cases ha : a = j
        · subst ha; simp
        · simp [ha]
      have hud : (Kᵀ.updateRow j w).updateRow j (Pi.single i 1) =
          Kᵀ.updateRow j (Pi.single i 1) := by
        refine Matrix.ext fun a b => ?_
        by_cases ha : a = j
        · subst ha; simp
        · simp [ha]
      calc
        (K.updateCol j w).adjugate j i = (K.updateCol j w).adjugateᵀ i j := rfl
        _ = ((K.updateCol j w)ᵀ).adjugate i j := by rw [Matrix.adjugate_transpose]
        _ = (Kᵀ.updateRow j w).adjugate i j := by rw [htr]
        _ = Kᵀ.adjugate i j := by rw [Matrix.adjugate_apply, Matrix.adjugate_apply, hud]
        _ = K.adjugateᵀ i j := by rw [Matrix.adjugate_transpose]
        _ = K.adjugate j i := rfl
    rw [Matrix.updateCol_self, hadj]
    simp only [w]
    ring
  have hF_ge2 : ∀ t : Finset (Fin k), 2 ≤ t.card → C (4 : ℤ) ∣ F t := by
    intro t ht
    refine Finset.dvd_sum fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul, ← C_eq_intCast, Int.cast_id]
    refine dvd_mul_of_dvd_right (dvd_mul_of_dvd_left ?_ _) _
    rw [Finset.prod_mul_distrib, Finset.prod_const]
    have h4pow : C (4 : ℤ) ∣ C (2 : ℤ) ^ t.card := by
      have h42 : (4 : ℤ) = 2 ^ 2 := by norm_num
      rw [h42, C_pow]
      exact pow_dvd_pow (C (2 : ℤ)) ht
    exact dvd_mul_of_dvd_left h4pow _
  rw [hdet_split, ← Finset.add_sum_erase _ F (Finset.mem_powerset.mpr (Finset.empty_subset _)), hF0]
  rw [← Finset.sum_filter_add_sum_filter_not ((Finset.univ : Finset (Fin k)).powerset.erase ∅)
    (fun t => t.card = 1)]
  have himg : ((Finset.univ : Finset (Fin k)).powerset.erase ∅).filter (fun t => t.card = 1) =
      Finset.univ.image (fun j : Fin k => ({j} : Finset (Fin k))) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_powerset, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, hcard⟩
      obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hcard
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨⟨Finset.singleton_ne_empty j, Finset.subset_univ _⟩, Finset.card_singleton j⟩
  rw [himg, Finset.sum_image (fun _ _ _ _ h => Finset.singleton_injective h)]
  simp_rw [hF1]
  have htr : (K.adjugate * L).trace = ∑ j : Fin k, ∑ i : Fin k, K.adjugate j i * L i j := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  have heq_sub :
      (K.det + ((∑ j : Fin k, C (2 : ℤ) * ∑ i : Fin k, K.adjugate j i * L i j) +
          ∑ t ∈ ((Finset.univ : Finset (Fin k)).powerset.erase ∅).filter (fun t => ¬t.card = 1),
            F t)) - (K.det + C (2 : ℤ) * (K.adjugate * L).trace) =
        ∑ t ∈ ((Finset.univ : Finset (Fin k)).powerset.erase ∅).filter (fun t => ¬t.card = 1),
          F t := by
    rw [← Finset.mul_sum, htr]
    ring
  rw [heq_sub]
  refine Finset.dvd_sum fun t ht => ?_
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_powerset] at ht
  apply hF_ge2 t
  have hc0 : t.card ≠ 0 := fun h => ht.1.1 (Finset.card_eq_zero.mp h)
  have hc1 : t.card ≠ 1 := ht.2
  omega

private lemma prod_linear_deg_and_coeff {ι : Type*} (s : Finset ι) (a b : ι → ℤ) :
    (∏ i ∈ s, (C (a i) * X + C (b i))).natDegree ≤ s.card ∧
      (∏ i ∈ s, (C (a i) * X + C (b i))).coeff s.card = ∏ i ∈ s, a i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    set P := ∏ j ∈ s, (C (a j) * X + C (b j))
    have hmul : (C (a i) * X + C (b i)) * P = C (a i) * (X * P) + C (b i) * P := by ring
    rw [hmul]
    have hdeg1 : (C (a i) * (X * P)).natDegree ≤ s.card + 1 := by
      refine le_trans (Polynomial.natDegree_mul_le) ?_
      rw [Polynomial.natDegree_C, zero_add]
      refine le_trans (Polynomial.natDegree_mul_le) ?_
      rw [Polynomial.natDegree_X]
      omega
    have hdeg2 : (C (b i) * P).natDegree ≤ s.card := by
      refine le_trans (Polynomial.natDegree_mul_le) ?_
      rw [Polynomial.natDegree_C, zero_add]
      exact ih.1
    refine ⟨le_trans (Polynomial.natDegree_add_le _ _) (max_le hdeg1 (by omega)), ?_⟩
    rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_mul, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < s.card + 1),
      mul_zero, add_zero, ih.2, Finset.prod_insert hi]

private lemma skew_det_monic_of_linear_jSym {m : ℕ}
    (K : Matrix (Fin (2 * m)) (Fin (2 * m)) ℤ[X])
    (hK : ∀ i j : Fin (2 * m), ∃ c : ℤ, K i j = C (jSym m i j) * X + C c) :
    K.det.natDegree ≤ 2 * m ∧ K.det.coeff (2 * m) = 1 := by
  choose consts hconsts using hK
  have hterm_deg : ∀ σ : Equiv.Perm (Fin (2 * m)),
      (Equiv.Perm.sign σ • ∏ i : Fin (2 * m), K (σ i) i).natDegree ≤ 2 * m ∧
      (Equiv.Perm.sign σ • ∏ i : Fin (2 * m), K (σ i) i).coeff (2 * m) =
        (Equiv.Perm.sign σ : ℤ) * ∏ i : Fin (2 * m), jSym m (σ i) i := by
    intro σ
    rw [Units.smul_def, zsmul_eq_mul, ← C_eq_intCast, Int.cast_id]
    have hprod_eq : (∏ i : Fin (2 * m), K (σ i) i) =
        ∏ i : Fin (2 * m), (C (jSym m (σ i) i) * X + C (consts (σ i) i)) :=
      Finset.prod_congr rfl fun i _ => hconsts (σ i) i
    have hpl := prod_linear_deg_and_coeff (Finset.univ : Finset (Fin (2 * m)))
      (fun i => jSym m (σ i) i) (fun i => consts (σ i) i)
    simp only [Finset.card_univ, Fintype.card_fin] at hpl
    rw [hprod_eq]
    refine ⟨le_trans (Polynomial.natDegree_mul_le) ?_, ?_⟩
    · rw [Polynomial.natDegree_C, zero_add]
      exact hpl.1
    · rw [Polynomial.coeff_C_mul, hpl.2]
  rw [Matrix.det_apply]
  refine ⟨?_, ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun σ _ => (hterm_deg σ).1
  · rw [← Polynomial.lcoeff_apply, map_sum]
    simp only [Polynomial.lcoeff_apply]
    simp_rw [fun σ => (hterm_deg σ).2]
    have hdet_eq :
        (∑ σ : Equiv.Perm (Fin (2 * m)),
          (Equiv.Perm.sign σ : ℤ) * ∏ i : Fin (2 * m), jSym m (σ i) i) = (jSym m).det := by
      rw [Matrix.det_apply]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Units.smul_def, zsmul_eq_mul, Int.cast_id]
    rw [hdet_eq]
    exact jSym_det_one m

/-- **Theorem 4.2 (Exact mod-`2^{n+1}` congruence for odd `n`):**
For any Seidel matrix `S` of **odd** order `n`, there exist polynomials `Q, R : ℤ[X]` with `Q`
monic of degree `(n - 1) / 2` such that
`S.charpoly.comp (C 2 * X - 1) = C (2 ^ (n - 1)) * ((C 2 * X - C n) * Q ^ 2 + C 4 * R)`. -/
theorem odd_order_two_adic_congruence {n : ℕ} (hn : Odd n)
    {S : Matrix (Fin n) (Fin n) ℤ} (hS : IsSeidelMatrix S) :
    ∃ Q R : ℤ[X], Q.Monic ∧ Q.natDegree = (n - 1) / 2 ∧
      S.charpoly.comp (C 2 * X - 1) =
        C ((2 : ℤ) ^ (n - 1)) * ((C 2 * X - C (n : ℤ)) * Q ^ 2 + C 4 * R) := by
  by_cases hn1 : n = 1
  · subst hn1
    refine ⟨1, 0, Polynomial.monic_one, by simp, ?_⟩
    have hchar1 : S.charpoly = X := by
      rw [Matrix.charpoly, Matrix.det_fin_one]
      simp [charmatrix, hS.2.1 0]
    rw [hchar1]
    simp
  rcases hn with ⟨m, rfl⟩
  have hm_pos : 1 ≤ m := by omega
  have hm_eq : ((2 * m + 1) - 1) / 2 = m := by omega
  let n : ℕ := 2 * m + 1
  have hn_odd : Odd n := ⟨m, rfl⟩
  have hn_pos : 1 ≤ n := by omega
  obtain ⟨d, hd, hS', hcharS, w, hw⟩ := exists_eulerian_switching hn_odd hS
  let S' := IsSeidelMatrix.switch d S
  change IsSeidelMatrix S' at hS'
  change S'.charpoly = S.charpoly at hcharS
  let A' : Matrix (Fin n) (Fin n) ℤ :=
    Matrix.of fun i j => if i = j then 0 else (1 - S' i j) / 2
  change A' *ᵥ (fun _ => 1) = (2 : ℤ) • w at hw
  have hSymm : A'ᵀ = A' := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [A']
    · have hSij : S' j i = S' i j := by
        calc
          S' j i = S'ᵀ i j := rfl
          _ = S' i j := by rw [hS'.1]
      simp [A', hij, Ne.symm hij, hSij]
  have hdiag : ∀ i, A' i i = 0 := fun i => by simp [A']
  have hS'_rel : ∀ i j : Fin n, i ≠ j → S' i j = 1 - 2 * A' i j := fun i j hij => by
    simp only [A', Matrix.of_apply, hij, ↓reduceIte]
    rcases hS'.2.2 i j hij with h | h <;> simp [h]
  let Q0 : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j =>
    if j.val = 0 then 1 else if i = j then 1 else if i.val = 0 then -1 else 0
  have hQ0_det : Q0.det = (n : ℤ) := basis_matrix_det hn_pos
  let D : Matrix (Fin n) (Fin n) ℤ[X] :=
    (X : ℤ[X]) • (1 : Matrix (Fin n) (Fin n) ℤ[X]) + A'.map (Polynomial.C : ℤ →+* ℤ[X])
  have hD_symm : Dᵀ = D := by
    ext i j
    rw [Matrix.transpose_apply]
    have hAij : A' j i = A' i j := by
      calc
        A' j i = A'ᵀ i j := rfl
        _ = A' i j := by rw [hSymm]
    simp only [D, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply,
      smul_eq_mul]
    rw [hAij]
    by_cases hij : j = i
    · subst hij; rfl
    · simp [hij, Ne.symm hij]
  let Jmat : Matrix (Fin n) (Fin n) ℤ[X] := Matrix.of fun _ _ => 1
  let Mz : Matrix (Fin n) (Fin n) ℤ[X] := C (2 : ℤ) • D - Jmat
  have hMz_det : Mz.det = S.charpoly.comp (C 2 * X - 1) := by
    rw [← hcharS]
    let φ : ℤ[X] →+* ℤ[X] := Polynomial.eval₂RingHom C (C (2 : ℤ) * X - 1)
    have hcomp : S'.charpoly.comp (C (2 : ℤ) * X - 1) = φ S'.charpoly := rfl
    rw [hcomp, Matrix.charpoly, RingHom.map_det, RingHom.mapMatrix_apply]
    congr 1
    refine Matrix.ext fun i j => ?_
    have hL : (S'.charmatrix.map φ) i j =
        if i = j then C 2 * X - 1 else C (-S' i j) := by
      rw [Matrix.map_apply, charmatrix, Matrix.sub_apply, Matrix.scalar_apply,
        Matrix.diagonal_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
      by_cases hij : i = j
      · subst hij; simp [φ, hS'.2.1 i]
      · simp only [hij, ↓reduceIte, zero_sub, φ,
          Polynomial.coe_eval₂RingHom, Polynomial.eval₂_neg, Polynomial.eval₂_C]
        rw [← map_neg]
    have hDij : D i j = (if i = j then X else 0) + C (A' i j) := by
      have hDdef : D = (X : ℤ[X]) • (1 : Matrix (Fin n) (Fin n) ℤ[X]) +
          A'.map (Polynomial.C : ℤ →+* ℤ[X]) := rfl
      rw [hDdef, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply,
        smul_eq_mul]
      by_cases hij : i = j <;> simp [hij]
    have hR : Mz i j = (if i = j then C 2 * X - 1 else C (2 * A' i j - 1)) := by
      rw [show Mz i j = C (2 : ℤ) * D i j - Jmat i j from rfl, hDij]
      by_cases hij : i = j
      · subst hij; simp [Jmat, hdiag i]
      · simp [Jmat, hij, map_sub]
    rw [hL, hR]
    by_cases hij : i = j
    · simp [hij]
    · simp only [hij, ↓reduceIte, hS'_rel i j hij]
      congr 1
      ring
  let Q0P : Matrix (Fin n) (Fin n) ℤ[X] := Q0.map (Polynomial.C : ℤ →+* ℤ[X])
  let T : Matrix (Fin n) (Fin n) ℤ[X] := Q0Pᵀ * Mz * Q0P
  have hT_det : T.det = C ((n : ℤ) ^ 2) * S.charpoly.comp (C 2 * X - 1) := by
    have hQ0P_det : Q0P.det = C (n : ℤ) := by
      change ((Polynomial.C : ℤ →+* ℤ[X]).mapMatrix Q0).det = C (n : ℤ)
      rw [← RingHom.map_det, hQ0_det]
    dsimp [T]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hQ0P_det, hMz_det, C_pow]
    ring
  have hw_row : ∀ a : Fin n, (∑ b : Fin n, A' a b) = 2 * w a := fun a => by
    have ha := congrFun hw a
    simpa [Matrix.mulVec, dotProduct, mul_one, two_mul] using ha
  have hw_col : ∀ b : Fin n, (∑ a : Fin n, A' a b) = 2 * w b := fun b => by
    have hsum : (∑ a : Fin n, A' a b) = ∑ a : Fin n, A' b a := by
      refine Finset.sum_congr rfl fun a _ => ?_
      calc
        A' a b = A'ᵀ b a := rfl
        _ = A' b a := by rw [hSymm]
    rw [hsum, hw_row b]
  have hQ0_col_sum_ne : ∀ j : Fin n, j.val ≠ 0 → (∑ a : Fin n, Q0 a j) = 0 := by
    intro j hj0
    have h0j : (⟨0, hn_pos⟩ : Fin n) ≠ j := fun h => hj0 (by simpa using congrArg Fin.val h.symm)
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
    have h0_mem : (⟨0, hn_pos⟩ : Fin n) ∈ Finset.univ.erase j :=
      Finset.mem_erase.mpr ⟨h0j, Finset.mem_univ _⟩
    rw [← Finset.add_sum_erase _ _ h0_mem]
    have hrest : ∑ x ∈ (Finset.univ.erase j).erase ⟨0, hn_pos⟩, Q0 x j = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      have hx0 : x ≠ ⟨0, hn_pos⟩ := (Finset.mem_erase.mp hx).1
      have hxj : x ≠ j := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
      have hxv : x.val ≠ 0 := fun h => hx0 (Fin.ext h)
      simp only [Q0, Matrix.of_apply, hj0, hxj, hxv, ↓reduceIte]
    rw [hrest, add_zero]
    have hjj : Q0 j j = 1 := by simp only [Q0, Matrix.of_apply, hj0, ↓reduceIte]
    have h0jv : Q0 ⟨0, hn_pos⟩ j = -1 := by
      simp only [Q0, Matrix.of_apply, hj0, h0j, ↓reduceIte]
    rw [hjj, h0jv]
    ring
  let eIdx : Fin (2 * m) ↪ Fin n :=
    ⟨fun t => ⟨t.val + 1, by omega⟩, fun a b h => Fin.ext (by
      have hv := congrArg Fin.val h; dsimp at hv; omega)⟩
  have heIdx_val : ∀ u : Fin (2 * m), (eIdx u).val = u.val + 1 := fun _ => rfl
  let i0 : Fin n := ⟨0, hn_pos⟩
  have hi0_val : i0.val = 0 := rfl
  let B : Matrix (Fin (2 * m)) (Fin (2 * m)) ℤ[X] := Matrix.of fun t s =>
    D (eIdx t) (eIdx s) - D (eIdx t) i0 - D i0 (eIdx s) + D i0 i0
  have hB_symm : Bᵀ = B := by
    ext t s
    have hD1 : D (eIdx s) (eIdx t) = D (eIdx t) (eIdx s) := by
      calc
        D (eIdx s) (eIdx t) = Dᵀ (eIdx t) (eIdx s) := rfl
        _ = D (eIdx t) (eIdx s) := by rw [hD_symm]
    have hD2 : D i0 (eIdx t) = D (eIdx t) i0 := by
      calc
        D i0 (eIdx t) = Dᵀ (eIdx t) i0 := rfl
        _ = D (eIdx t) i0 := by rw [hD_symm]
    have hD3 : D (eIdx s) i0 = D i0 (eIdx s) := by
      calc
        D (eIdx s) i0 = Dᵀ i0 (eIdx s) := rfl
        _ = D i0 (eIdx s) := by rw [hD_symm]
    simp only [B, Matrix.transpose_apply, Matrix.of_apply, hD1, hD2, hD3]
    ring
  have hT_00 : T i0 i0 = C (n : ℤ) * (C 2 * X - C (n : ℤ)) + C (4 * ∑ a : Fin n, w a) := by
    have hcol0 : ∀ a : Fin n, Q0P a i0 = 1 := fun a => by simp [Q0P, Q0, i0]
    have hrow0 : ∀ a : Fin n, Q0Pᵀ i0 a = 1 := fun a => by simp [Q0P, Q0, i0]
    have hsum_J : (Q0Pᵀ * Jmat * Q0P) i0 i0 = C ((n : ℤ) ^ 2) := by
      simp only [Matrix.mul_apply, hrow0, hcol0, Jmat, Matrix.of_apply, mul_one,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [C_pow, sq]
      simp
    have hsum_D : (Q0Pᵀ * D * Q0P) i0 i0 = C (n : ℤ) * X + C (2 * ∑ a : Fin n, w a) := by
      have h1 : (Q0Pᵀ * D * Q0P) i0 i0 = ∑ a : Fin n, ∑ b : Fin n, D a b := by
        simp only [Matrix.mul_apply, hrow0, hcol0, one_mul, mul_one]
        rw [Finset.sum_comm]
      have hDij : ∀ a b : Fin n, D a b = (if a = b then X else 0) + C (A' a b) := fun a b => by
        have hDdef : D = (X : ℤ[X]) • (1 : Matrix (Fin n) (Fin n) ℤ[X]) +
            A'.map (Polynomial.C : ℤ →+* ℤ[X]) := rfl
        rw [hDdef, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply,
          smul_eq_mul]
        by_cases hab : a = b <;> simp [hab]
      rw [h1]
      simp only [hDij, Finset.sum_add_distrib, ← map_sum, hw_row, ← Finset.mul_sum, map_mul]
      simp
    have hMz_eq : Mz = C (2 : ℤ) • D - Jmat := rfl
    calc
      T i0 i0 = ((Q0Pᵀ * (C (2 : ℤ) • D - Jmat) * Q0P)) i0 i0 := rfl
      _ = C (2 : ℤ) * (Q0Pᵀ * D * Q0P) i0 i0 - (Q0Pᵀ * Jmat * Q0P) i0 i0 := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
            Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      _ = C (n : ℤ) * (C 2 * X - C (n : ℤ)) + C (4 * ∑ a : Fin n, w a) := by
          rw [hsum_D, hsum_J]
          simp only [map_mul, C_pow, C_ofNat]
          ring
  have hT_0j : ∀ j : Fin n, j ≠ i0 → ∃ c : ℤ, T i0 j = C (4 * c) := by
    intro j hj
    have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
    have hQsum := hQ0_col_sum_ne j hj0
    have hQsumP : (∑ b : Fin n, Q0P b j) = 0 := by
      simp_rw [Q0P, Matrix.map_apply, ← map_sum, hQsum, map_zero]
    have hcol0 : ∀ a : Fin n, Q0Pᵀ i0 a = 1 := fun a => by simp [Q0P, Q0, i0]
    have hJ0 : (Q0Pᵀ * Jmat * Q0P) i0 j = 0 := by
      simp only [Matrix.mul_apply, hcol0, Jmat, Matrix.of_apply, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, ← Finset.mul_sum]
      rw [hQsumP, mul_zero]
    have hD0j : (Q0Pᵀ * D * Q0P) i0 j = C (2 * ∑ b : Fin n, w b * Q0 b j) := by
      have h1 : (Q0Pᵀ * D * Q0P) i0 j = ∑ b : Fin n, (∑ a : Fin n, D a b) * Q0P b j := by
        simp only [Matrix.mul_apply, hcol0, one_mul]
      have hcol_D : ∀ b : Fin n, (∑ a : Fin n, D a b) = X + C (2 * w b) := by
        intro b
        have hDij : ∀ a : Fin n, D a b = (if a = b then X else 0) + C (A' a b) := fun a => by
          have hDdef : D = (X : ℤ[X]) • (1 : Matrix (Fin n) (Fin n) ℤ[X]) +
              A'.map (Polynomial.C : ℤ →+* ℤ[X]) := rfl
          rw [hDdef, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply,
            smul_eq_mul]
          by_cases hab : a = b <;> simp [hab]
        simp only [hDij, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
          ← map_sum, hw_col b]
      rw [h1]
      simp only [hcol_D, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
        Q0P, Matrix.map_apply, ← map_mul, mul_assoc, ← map_sum, hQsum, map_zero,
        mul_zero, zero_add]
    refine ⟨∑ b : Fin n, w b * Q0 b j, ?_⟩
    calc
      T i0 j = C (2 : ℤ) * (Q0Pᵀ * D * Q0P) i0 j - (Q0Pᵀ * Jmat * Q0P) i0 j := by
        simp only [T, Mz, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      _ = C (4 * ∑ b : Fin n, w b * Q0 b j) := by
        rw [hD0j, hJ0, sub_zero, ← map_mul]
        congr 1
        ring
  have hT_symm : Tᵀ = T := by
    have hMz_symm : Mzᵀ = Mz := by
      ext a b
      have hDab : D b a = D a b := by
        calc
          D b a = Dᵀ a b := rfl
          _ = D a b := by rw [hD_symm]
      simp [Mz, Jmat, hDab]
    dsimp [T]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hMz_symm,
      Matrix.mul_assoc]
  have hT_j0 : ∀ j : Fin n, j ≠ i0 → ∃ c : ℤ, T j i0 = C (4 * c) := fun j hj => by
    rcases hT_0j j hj with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    calc
      T j i0 = Tᵀ i0 j := rfl
      _ = T i0 j := by rw [hT_symm]
      _ = C (4 * c) := hc
  have hT_sub : ∀ t s : Fin (2 * m), T (eIdx t) (eIdx s) = C (2 : ℤ) * B t s := by
    intro t s
    have hQ_col : ∀ u : Fin (2 * m), ∀ a : Fin n,
        Q0P a (eIdx u) = (if a = eIdx u then 1 else if a = i0 then -1 else 0) := by
      intro u a
      have heu0 : (eIdx u).val ≠ 0 := by rw [heIdx_val]; omega
      simp only [Q0P, Matrix.map_apply, Q0, Matrix.of_apply, heu0, ↓reduceIte]
      by_cases hau : a = eIdx u
      · simp only [hau, ↓reduceIte, map_one]
      · simp only [hau, ↓reduceIte]
        by_cases ha0 : a = i0
        · simp only [ha0, hi0_val, ↓reduceIte, map_neg, map_one]
        · have hav0 : a.val ≠ 0 := fun h => ha0 (Fin.ext (h.trans hi0_val.symm))
          simp only [ha0, hav0, ↓reduceIte, map_zero]
    have hQ_row : ∀ u : Fin (2 * m), ∀ a : Fin n,
        Q0Pᵀ (eIdx u) a = (if a = eIdx u then 1 else if a = i0 then -1 else 0) := fun u a =>
      hQ_col u a
    have hJ0 : (Q0Pᵀ * Jmat * Q0P) (eIdx t) (eIdx s) = 0 := by
      have hes0 : (eIdx s).val ≠ 0 := by rw [heIdx_val]; omega
      have hQsum : (∑ b : Fin n, Q0P b (eIdx s)) = 0 := by
        simp_rw [Q0P, Matrix.map_apply, ← map_sum, hQ0_col_sum_ne (eIdx s) hes0, map_zero]
      have hcol_J : ∀ a : Fin n, (Jmat * Q0P) a (eIdx s) = 0 := fun a => by
        rw [Matrix.mul_apply]
        simpa [Jmat] using hQsum
      rw [Matrix.mul_assoc, Matrix.mul_apply]
      simp [hcol_J]
    have hD_prod : ∀ M : Matrix (Fin n) (Fin n) ℤ[X],
        (Q0Pᵀ * M * Q0P) (eIdx t) (eIdx s) =
          M (eIdx t) (eIdx s) - M (eIdx t) i0 - M i0 (eIdx s) + M i0 i0 := by
      intro M
      have het0 : eIdx t ≠ i0 := fun h => by
        have := congrArg Fin.val h; rw [heIdx_val, hi0_val] at this; omega
      have hes0 : eIdx s ≠ i0 := fun h => by
        have := congrArg Fin.val h; rw [heIdx_val, hi0_val] at this; omega
      have hM_right : ∀ a : Fin n, (M * Q0P) a (eIdx s) = M a (eIdx s) - M a i0 := by
        intro a
        rw [Matrix.mul_apply, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (eIdx s))]
        have hi0_mem : i0 ∈ Finset.univ.erase (eIdx s) :=
          Finset.mem_erase.mpr ⟨hes0.symm, Finset.mem_univ _⟩
        rw [← Finset.add_sum_erase _ _ hi0_mem]
        have hrest : ∑ x ∈ (Finset.univ.erase (eIdx s)).erase i0,
            M a x * Q0P x (eIdx s) = 0 := by
          refine Finset.sum_eq_zero fun x hx => ?_
          have hx0 : x ≠ i0 := (Finset.mem_erase.mp hx).1
          have hxs : x ≠ eIdx s := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
          simp [hQ_col s x, hxs, hx0]
        rw [hrest, add_zero, hQ_col s (eIdx s), hQ_col s i0]
        simp only [↓reduceIte, hes0.symm]
        ring
      rw [Matrix.mul_assoc, Matrix.mul_apply, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (eIdx t))]
      have hi0_mem : i0 ∈ Finset.univ.erase (eIdx t) :=
        Finset.mem_erase.mpr ⟨het0.symm, Finset.mem_univ _⟩
      rw [← Finset.add_sum_erase _ _ hi0_mem]
      have hrest : ∑ x ∈ (Finset.univ.erase (eIdx t)).erase i0,
          Q0Pᵀ (eIdx t) x * (M * Q0P) x (eIdx s) = 0 := by
        refine Finset.sum_eq_zero fun x hx => ?_
        have hx0 : x ≠ i0 := (Finset.mem_erase.mp hx).1
        have hxt : x ≠ eIdx t := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
        have hq : Q0Pᵀ (eIdx t) x = 0 := by rw [hQ_row t x]; simp [hxt, hx0]
        rw [hq, zero_mul]
      rw [hrest, add_zero, hQ_row t (eIdx t), hQ_row t i0]
      simp only [↓reduceIte, het0.symm, hM_right (eIdx t), hM_right i0]
      ring
    calc
      T (eIdx t) (eIdx s) = C (2 : ℤ) * (Q0Pᵀ * D * Q0P) (eIdx t) (eIdx s) -
          (Q0Pᵀ * Jmat * Q0P) (eIdx t) (eIdx s) := by
        simp only [T, Mz, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      _ = C (2 : ℤ) * B t s := by
        rw [hD_prod D, hJ0, sub_zero]
        simp [B]
  have hT_mod : C ((2 : ℤ) ^ (n + 1)) ∣
      T.det - T i0 i0 * C ((2 : ℤ) ^ (n - 1)) * B.det := by
    rw [Matrix.det_apply]
    let S_fix : Finset (Equiv.Perm (Fin n)) := Finset.univ.filter (fun σ => σ i0 = i0)
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun σ : Equiv.Perm (Fin n) => σ i0 = i0)]
    have hnonfix : C ((2 : ℤ) ^ (n + 1)) ∣
        ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ¬σ i0 = i0),
          Equiv.Perm.sign σ • ∏ i : Fin n, T (σ i) i := by
      refine Finset.dvd_sum fun σ hσ => ?_
      have hne0 : σ i0 ≠ i0 := (Finset.mem_filter.mp hσ).2
      have hne_inv : σ⁻¹ i0 ≠ i0 := fun h => hne0 (by
        have := congrArg σ h
        simpa using this.symm)
      have hprod_split : (∏ i : Fin n, T (σ i) i) =
          T (σ i0) i0 * (T (σ (σ⁻¹ i0)) (σ⁻¹ i0) *
            ∏ i ∈ (Finset.univ.erase i0).erase (σ⁻¹ i0), T (σ i) i) := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i0)]
        congr 1
        have hmem : σ⁻¹ i0 ∈ Finset.univ.erase i0 := Finset.mem_erase.mpr ⟨hne_inv, Finset.mem_univ _⟩
        rw [← Finset.mul_prod_erase _ _ hmem]
      rw [Units.smul_def, zsmul_eq_mul, ← C_eq_intCast, Int.cast_id, hprod_split]
      refine dvd_mul_of_dvd_right ?_ _
      rcases hT_j0 (σ i0) hne0 with ⟨c1, hc1⟩
      have hσinv : σ (σ⁻¹ i0) = i0 := by simp
      rcases hT_0j (σ⁻¹ i0) hne_inv with ⟨c2, hc2⟩
      rw [hσinv, hc1, hc2]
      have hdvd_rest : C ((2 : ℤ) ^ (n - 2)) ∣
          ∏ i ∈ (Finset.univ.erase i0).erase (σ⁻¹ i0), T (σ i) i := by
        have hfac : ∀ i ∈ (Finset.univ.erase i0).erase (σ⁻¹ i0), C (2 : ℤ) ∣ T (σ i) i := by
          intro i hi
          have hi_inv : i ≠ σ⁻¹ i0 := (Finset.mem_erase.mp hi).1
          have hi0 : i ≠ i0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
          have hσi0 : σ i ≠ i0 := fun h => hi_inv (by
            have := congrArg (fun x => σ⁻¹ x) h
            simpa using this)
          let t : Fin (2 * m) := ⟨(σ i).val - 1, by
            have hne : (σ i).val ≠ 0 := fun h => hσi0 (Fin.ext h)
            omega⟩
          let s : Fin (2 * m) := ⟨i.val - 1, by
            have hne : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
            omega⟩
          have ht : eIdx t = σ i := Fin.ext (by
            have hne : (σ i).val ≠ 0 := fun h => hσi0 (Fin.ext (h.trans hi0_val.symm))
            rw [heIdx_val]
            dsimp [t]
            omega)
          have hs : eIdx s = i := Fin.ext (by
            have hne : i.val ≠ 0 := fun h => hi0 (Fin.ext (h.trans hi0_val.symm))
            rw [heIdx_val]
            dsimp [s]
            omega)
          rw [← ht, ← hs, hT_sub t s]
          exact dvd_mul_right _ _
        have hcard_rest : ((Finset.univ.erase i0).erase (σ⁻¹ i0)).card = n - 2 := by
          rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hne_inv, Finset.mem_univ _⟩),
            Finset.card_erase_of_mem (Finset.mem_univ i0), Finset.card_univ, Fintype.card_fin]
          omega
        rw [← hcard_rest]
        calc
          C ((2 : ℤ) ^ ((Finset.univ.erase i0).erase (σ⁻¹ i0)).card)
              = ∏ _i ∈ (Finset.univ.erase i0).erase (σ⁻¹ i0), C (2 : ℤ) := by
                  rw [C_pow, Finset.prod_const]
          _ ∣ ∏ i ∈ (Finset.univ.erase i0).erase (σ⁻¹ i0), T (σ i) i :=
              Finset.prod_dvd_prod_of_dvd _ _ hfac
      rcases hdvd_rest with ⟨R0, hR0⟩
      rw [hR0]
      have hexp : (2 : ℤ) ^ (n + 1) ∣ (4 * c1) * ((4 * c2) * (2 : ℤ) ^ (n - 2)) := by
        have hpow : (2 : ℤ) ^ (n + 1) ∣ (2 : ℤ) ^ (n + 2) := pow_dvd_pow 2 (by omega)
        refine dvd_trans hpow ?_
        have h2eq : (2 : ℤ) ^ (n + 2) = 4 * (4 * (2 : ℤ) ^ (n - 2)) := by
          have : n + 2 = 2 + (2 + (n - 2)) := by omega
          rw [this, pow_add, pow_add]
          norm_num
        rw [h2eq]
        refine ⟨c1 * c2, by ring⟩
      rcases hexp with ⟨k0, hk0⟩
      refine ⟨C k0 * R0, ?_⟩
      calc
        C (4 * c1) * (C (4 * c2) * (C ((2 : ℤ) ^ (n - 2)) * R0))
            = C ((4 * c1) * ((4 * c2) * (2 : ℤ) ^ (n - 2))) * R0 := by
                rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul]
                ring
        _ = C ((2 : ℤ) ^ (n + 1) * k0) * R0 := by rw [hk0]
        _ = C ((2 : ℤ) ^ (n + 1)) * (C k0 * R0) := by rw [map_mul, mul_assoc]
    have hfix_sum :
        (∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ i0 = i0),
          Equiv.Perm.sign σ • ∏ i : Fin n, T (σ i) i) =
          T i0 i0 * C ((2 : ℤ) ^ (n - 1)) * B.det := by
      let emb : Fin (2 * m) ≃ { x : Fin n // x ≠ i0 } :=
        { toFun := fun t => ⟨eIdx t, fun h => by
            have := congrArg Fin.val h; rw [heIdx_val, hi0_val] at this; omega⟩
          invFun := fun x => ⟨x.1.val - 1, by
            have hx : x.1.val ≠ 0 := fun h => x.2 (Fin.ext (h.trans hi0_val.symm))
            omega⟩
          left_inv := fun t => Fin.ext (by change (t.val + 1) - 1 = t.val; omega)
          right_inv := fun x => Subtype.ext (Fin.ext (by
            have hx : x.1.val ≠ 0 := fun h => x.2 (Fin.ext (h.trans hi0_val.symm))
            change (x.1.val - 1) + 1 = x.1.val
            omega)) }
      let liftPerm : Equiv.Perm (Fin (2 * m)) → Equiv.Perm (Fin n) := fun τ =>
        τ.extendDomain emb
      have hsign_lift : ∀ τ : Equiv.Perm (Fin (2 * m)),
          Equiv.Perm.sign (liftPerm τ) = Equiv.Perm.sign τ := fun τ =>
        Equiv.Perm.sign_extendDomain τ emb
      have heIdx_symm : ∀ y : { x : Fin n // x ≠ i0 }, eIdx (emb.symm y) = y.1 := fun y =>
        congrArg Subtype.val (emb.apply_symm_apply y)
      have hemb_val : ∀ x : Fin (2 * m), (emb x).1 = eIdx x := fun _ => rfl
      rw [Matrix.det_apply, Finset.mul_sum]
      symm
      refine Finset.sum_bij (fun τ _ => liftPerm τ) ?_ ?_ ?_ ?_
      · intro τ _
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        exact Equiv.Perm.extendDomain_apply_not_subtype τ emb (not_not.mpr rfl)
      · intro τ₁ _ τ₂ _ h
        ext t
        have ht := congrArg (fun π : Equiv.Perm (Fin n) => π (eIdx t)) h
        have h1 : liftPerm τ₁ (eIdx t) = eIdx (τ₁ t) :=
          Equiv.Perm.extendDomain_apply_image τ₁ emb t
        have h2 : liftPerm τ₂ (eIdx t) = eIdx (τ₂ t) :=
          Equiv.Perm.extendDomain_apply_image τ₂ emb t
        rw [h1, h2] at ht
        exact congrArg Fin.val (eIdx.injective ht)
      · intro σ hσ
        have hσ0 : σ i0 = i0 := (Finset.mem_filter.mp hσ).2
        let τ : Equiv.Perm (Fin (2 * m)) :=
          { toFun := fun t => emb.symm ⟨σ (eIdx t), fun h => (emb t).2 (σ.injective (h.trans hσ0.symm))⟩
            invFun := fun t => emb.symm ⟨σ⁻¹ (eIdx t), fun h => by
              have h' := congrArg σ h
              have h'' : eIdx t = i0 := by simpa [hσ0] using h'
              exact (emb t).2 h''⟩
            left_inv := fun t => by
              apply emb.injective
              apply Subtype.ext
              dsimp only
              simp only [hemb_val, heIdx_symm]
              simp
            right_inv := fun t => by
              apply emb.injective
              apply Subtype.ext
              dsimp only
              simp only [hemb_val, heIdx_symm]
              simp }
        refine ⟨τ, Finset.mem_univ _, ?_⟩
        ext x
        by_cases hx : x = i0
        · subst hx
          rw [Equiv.Perm.extendDomain_apply_not_subtype τ emb (not_not.mpr rfl), hσ0]
        · have hx' : x ≠ i0 := hx
          rw [Equiv.Perm.extendDomain_apply_subtype τ emb hx']
          have h1 : (emb (τ (emb.symm ⟨x, hx'⟩))).1 = σ (eIdx (emb.symm ⟨x, hx'⟩)) := by
            dsimp [τ]
            exact congrArg Subtype.val (emb.apply_symm_apply _)
          have h2 : eIdx (emb.symm ⟨x, hx'⟩) = x :=
            congrArg Subtype.val (emb.apply_symm_apply ⟨x, hx'⟩)
          rw [h1, h2]
      · intro τ _
        have hlift0 : liftPerm τ i0 = i0 :=
          Equiv.Perm.extendDomain_apply_not_subtype τ emb (not_not.mpr rfl)
        have hprod : (∏ i : Fin n, T (liftPerm τ i) i) =
            T i0 i0 * C ((2 : ℤ) ^ (n - 1)) * ∏ t : Fin (2 * m), B (τ t) t := by
          rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i0), hlift0]
          have hrest : (∏ i ∈ Finset.univ.erase i0, T (liftPerm τ i) i) =
              ∏ t : Fin (2 * m), T (eIdx (τ t)) (eIdx t) := by
            refine Finset.prod_bij (fun i hi => emb.symm ⟨i, (Finset.mem_erase.mp hi).1⟩)
              ?_ ?_ ?_ ?_
            · intro _ _; exact Finset.mem_univ _
            · intro i₁ hi₁ i₂ hi₂ h
              have := congrArg (fun t => (emb t).1) h
              simpa using this
            · intro t _
              refine ⟨eIdx t, Finset.mem_erase.mpr ⟨(emb t).2, Finset.mem_univ _⟩, ?_⟩
              apply emb.injective
              simp only [Equiv.apply_symm_apply]
              rfl
            · intro i hi
              have hi0 : i ≠ i0 := (Finset.mem_erase.mp hi).1
              have h1 : liftPerm τ i = eIdx (τ (emb.symm ⟨i, hi0⟩)) := by
                change τ.extendDomain emb i = (emb (τ (emb.symm ⟨i, hi0⟩))).1
                exact Equiv.Perm.extendDomain_apply_subtype τ emb hi0
              have h2 : eIdx (emb.symm ⟨i, hi0⟩) = i :=
                congrArg Subtype.val (emb.apply_symm_apply ⟨i, hi0⟩)
              rw [h1]
              conv_lhs => rhs; rw [← h2]
          rw [hrest]
          simp_rw [hT_sub, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
            Fintype.card_fin]
          have hexp : 2 * m = n - 1 := by omega
          rw [← C_pow, show (2 : ℤ) ^ (2 * m) = 2 ^ (n - 1) by rw [hexp], mul_assoc]
        rw [hsign_lift τ, Units.smul_def, Units.smul_def, zsmul_eq_mul, zsmul_eq_mul, hprod]
        ring
    rw [hfix_sum, add_sub_cancel_left]
    exact hnonfix
  let K : Matrix (Fin (2 * m)) (Fin (2 * m)) ℤ[X] := Matrix.of fun t s =>
    if t < s then B t s else if s < t then -B t s else 0
  let L : Matrix (Fin (2 * m)) (Fin (2 * m)) ℤ[X] := Matrix.of fun t s =>
    if t = s then X - C (A' i0 (eIdx t)) else if s < t then B t s else 0
  have hK_skew : Kᵀ = -K := by
    ext t s
    have hBts : B s t = B t s := by
      calc
        B s t = Bᵀ t s := rfl
        _ = B t s := by rw [hB_symm]
    simp only [K, Matrix.transpose_apply, Matrix.neg_apply, Matrix.of_apply]
    rcases lt_trichotomy t s with hlt | rfl | hgt
    · simp [hlt, not_lt_of_gt hlt, hBts]
    · simp
    · simp [hgt, not_lt_of_gt hgt, hBts]
  have hK_diag : ∀ t, K t t = 0 := fun t => by simp [K]
  have hB_KL : B = K + C (2 : ℤ) • L := by
    ext t s
    have hDij : ∀ a b : Fin n, D a b = (if a = b then X else 0) + C (A' a b) := fun a b => by
      have hDdef : D = (X : ℤ[X]) • (1 : Matrix (Fin n) (Fin n) ℤ[X]) +
          A'.map (Polynomial.C : ℤ →+* ℤ[X]) := rfl
      rw [hDdef, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply,
        smul_eq_mul]
      by_cases hab : a = b <;> simp [hab]
    have hA_sym : A' (eIdx t) i0 = A' i0 (eIdx t) := by
      calc
        A' (eIdx t) i0 = A'ᵀ i0 (eIdx t) := rfl
        _ = A' i0 (eIdx t) := by rw [hSymm]
    have hene : ∀ u : Fin (2 * m), eIdx u ≠ i0 := fun u h => by
      have := congrArg Fin.val h; rw [heIdx_val, hi0_val] at this; omega
    have hC2 : C (2 : ℤ) = (2 : ℤ[X]) := by norm_num
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, K, L, Matrix.of_apply]
    rcases lt_trichotomy t s with hlt | rfl | hgt
    · have hne : t ≠ s := ne_of_lt hlt
      simp [hlt, not_lt_of_gt hlt, hne]
    · simp only [lt_irrefl, ↓reduceIte, zero_add]
      simp only [B, Matrix.of_apply, hDij, hene t, (hene t).symm, ↓reduceIte, hdiag i0,
        hdiag (eIdx t), map_zero, add_zero, zero_add, hA_sym, hC2]
      ring
    · have hne : t ≠ s := ne_of_gt hgt
      simp only [not_lt_of_gt hgt, hgt, ↓reduceIte, hne, hC2]
      ring
  have hK_lin : ∀ t s : Fin (2 * m), ∃ c : ℤ, K t s = C (jSym m t s) * X + C c := by
    intro t s
    have hDij : ∀ a b : Fin n, D a b = (if a = b then X else 0) + C (A' a b) := fun a b => by
      have hDdef : D = (X : ℤ[X]) • (1 : Matrix (Fin n) (Fin n) ℤ[X]) +
          A'.map (Polynomial.C : ℤ →+* ℤ[X]) := rfl
      rw [hDdef, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply,
        smul_eq_mul]
      by_cases hab : a = b <;> simp [hab]
    have hene : ∀ u : Fin (2 * m), eIdx u ≠ i0 := fun u h => by
      have := congrArg Fin.val h; rw [heIdx_val, hi0_val] at this; omega
    have hB_off : t ≠ s → B t s = X + C (A' (eIdx t) (eIdx s) - A' (eIdx t) i0 - A' i0 (eIdx s)) := by
      intro hts
      have hets : eIdx t ≠ eIdx s := fun h => hts (eIdx.injective h)
      simp only [B, Matrix.of_apply, hDij, hets, hene t, (hene s).symm,
        ↓reduceIte, hdiag i0, zero_add, map_zero, add_zero, map_sub]
      ring
    rcases lt_trichotomy t s with hlt | rfl | hgt
    · refine ⟨A' (eIdx t) (eIdx s) - A' (eIdx t) i0 - A' i0 (eIdx s), ?_⟩
      simp [K, jSym, hlt, hB_off (ne_of_lt hlt)]
    · refine ⟨0, by simp [K, jSym]⟩
    · refine ⟨-(A' (eIdx t) (eIdx s) - A' (eIdx t) i0 - A' i0 (eIdx s)), ?_⟩
      simp only [K, jSym, Matrix.of_apply, not_lt_of_gt hgt, hgt, ↓reduceIte,
        hB_off (ne_of_gt hgt), map_neg, map_sub, map_one]
      ring
  obtain ⟨hK_deg, hK_coeff⟩ := skew_det_monic_of_linear_jSym K hK_lin
  obtain ⟨p, hp⟩ := skew_det_eq_sq hK_skew hK_diag
  have hp_deg : p.natDegree = m := by
    have hdet_deg : K.det.natDegree = 2 * m :=
      le_antisymm hK_deg (Polynomial.le_natDegree_of_ne_zero (by rw [hK_coeff]; exact one_ne_zero))
    have hp0 : p ≠ 0 := by
      intro h0
      rw [h0, zero_pow two_ne_zero] at hp
      rw [hp] at hK_coeff
      simp at hK_coeff
    rw [hp, Polynomial.natDegree_pow' (by
      have hlc : (p.leadingCoeff) ^ 2 ≠ 0 := by
        have : p.leadingCoeff ^ 2 = (p ^ 2).leadingCoeff := (Polynomial.leadingCoeff_pow p 2).symm
        rw [← hp] at this
        have hlc1 : K.det.leadingCoeff = 1 := by
          rw [Polynomial.leadingCoeff, hp, hdet_deg, ← hp, hK_coeff]
        rw [this, hlc1]
        exact one_ne_zero
      exact hlc)] at hdet_deg
    omega
  have hlc_sq : p.leadingCoeff ^ 2 = 1 := by
    have hdet_deg : K.det.natDegree = 2 * m :=
      le_antisymm hK_deg (Polynomial.le_natDegree_of_ne_zero (by rw [hK_coeff]; exact one_ne_zero))
    have hlc1 : K.det.leadingCoeff = 1 := by rw [Polynomial.leadingCoeff, hdet_deg, hK_coeff]
    rw [hp, Polynomial.leadingCoeff_pow] at hlc1
    exact hlc1
  have hlc_pm : p.leadingCoeff = 1 ∨ p.leadingCoeff = -1 := sq_eq_one_iff.mp hlc_sq
  let Q : ℤ[X] := if p.leadingCoeff = 1 then p else -p
  have hQ_monic : Q.Monic := by
    rcases hlc_pm with h1 | h1
    · simp [Q, Polynomial.Monic, h1]
    · have hQ_eq : Q = -p := by dsimp [Q]; simp [h1]
      rw [hQ_eq, Polynomial.Monic, Polynomial.leadingCoeff_neg, h1]
      ring
  have hQ_deg : Q.natDegree = m := by
    by_cases h1 : p.leadingCoeff = 1
    · simp [Q, h1, hp_deg]
    · simp [Q, h1, hp_deg]
  have hQ_sq : K.det = Q ^ 2 := by
    by_cases h1 : p.leadingCoeff = 1
    · simp [Q, h1, hp]
    · simp [Q, h1, hp]
  have hB_mod4 : C (4 : ℤ) ∣ B.det - C (n : ℤ) * Q ^ 2 := by
    have hdet_mod := det_add_two_mul_mod4 K L
    rw [← hB_KL] at hdet_mod
    have h2m_even : Even (2 * m) := ⟨m, by ring⟩
    have h2m_pos : 1 ≤ 2 * m := by omega
    have hadj_diag : ∀ t : Fin (2 * m), K.adjugate t t = 0 :=
      fun t => skew_adjugate_diag_eq_zero h2m_even h2m_pos hK_skew t
    have hadj_symm : K.adjugateᵀ = -K.adjugate :=
      skew_adjugate_transpose h2m_even h2m_pos hK_skew
    have htr_KL : (K.adjugate * L).trace = -(m : ℤ[X]) * K.det := by
      have htrK : (K.adjugate * K).trace = (2 * m : ℤ[X]) * K.det := by
        rw [Matrix.adjugate_mul, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
        push_cast
        ring
      have hsplit1 : (K.adjugate * K).trace =
          2 * ∑ p ∈ (Finset.univ : Finset (Fin (2 * m) × Fin (2 * m))).filter (fun p => p.1 < p.2),
            K.adjugate p.1 p.2 * K p.2 p.1 := by
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
        have hdiag0 : ∀ t : Fin (2 * m), K.adjugate t t * K t t = 0 := fun t => by rw [hK_diag t, mul_zero]
        have hsym_prod : ∀ t s : Fin (2 * m), K.adjugate t s * K s t = K.adjugate s t * K t s := by
          intro t s
          have h1 : K.adjugate t s = -K.adjugate s t := by
            calc
              K.adjugate t s = K.adjugateᵀ s t := rfl
              _ = (-K.adjugate) s t := by rw [hadj_symm]
              _ = -K.adjugate s t := rfl
          have h2 : K s t = -K t s := by
            calc
              K s t = Kᵀ t s := rfl
              _ = (-K) t s := by rw [hK_skew]
              _ = -K t s := rfl
          rw [h1, h2]
          ring
        let M_tr : Matrix (Fin (2 * m)) (Fin (2 * m)) ℤ[X] :=
          Matrix.of fun s t => K.adjugate s t * K t s
        have hM_symm : M_trᵀ = M_tr := by
          ext s t
          simp [M_tr, hsym_prod t s]
        have hsp := sum_matrix_symm_split M_tr hM_symm
        simp only [M_tr, Matrix.of_apply, hdiag0, Finset.sum_const_zero, zero_add] at hsp
        rw [hsp]
      have hsum_half : (∑ p ∈ (Finset.univ : Finset (Fin (2 * m) × Fin (2 * m))).filter
          (fun p => p.1 < p.2), K.adjugate p.1 p.2 * K p.2 p.1) = (m : ℤ[X]) * K.det := by
        have h2eq : (2 : ℤ[X]) * ∑ p ∈ (Finset.univ : Finset (Fin (2 * m) × Fin (2 * m))).filter
            (fun p => p.1 < p.2), K.adjugate p.1 p.2 * K p.2 p.1 =
            (2 : ℤ[X]) * ((m : ℤ[X]) * K.det) := by
          rw [← hsplit1, htrK]
          ring
        exact mul_left_cancel₀ (by norm_num : (2 : ℤ[X]) ≠ 0) h2eq
      have htrL_eq : (K.adjugate * L).trace =
          -∑ p ∈ (Finset.univ : Finset (Fin (2 * m) × Fin (2 * m))).filter (fun p => p.1 < p.2),
            K.adjugate p.1 p.2 * K p.2 p.1 := by
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
        rw [← Fintype.sum_prod_type' (fun s t => K.adjugate s t * L t s)]
        have hpart :
            (∑ p : Fin (2 * m) × Fin (2 * m), K.adjugate p.1 p.2 * L p.2 p.1) =
              ∑ p ∈ (Finset.univ : Finset (Fin (2 * m) × Fin (2 * m))).filter (fun p => p.1 < p.2),
                K.adjugate p.1 p.2 * L p.2 p.1 := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
            (fun p : Fin (2 * m) × Fin (2 * m) => p.1 < p.2)]
          have h0 : ∑ p ∈ (Finset.univ : Finset (Fin (2 * m) × Fin (2 * m))).filter
              (fun p => ¬p.1 < p.2), K.adjugate p.1 p.2 * L p.2 p.1 = 0 := by
            refine Finset.sum_eq_zero fun p hp => ?_
            have hle : p.2 ≤ p.1 := not_lt.mp (Finset.mem_filter.mp hp).2
            rcases lt_or_eq_of_le hle with hlt | heq
            · have hne : p.2 ≠ p.1 := ne_of_lt hlt
              simp [L, hne, not_lt_of_gt hlt]
            · rw [heq, hadj_diag, zero_mul]
          rw [h0, add_zero]
        rw [hpart, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun p hp => ?_
        have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
        have hne : p.2 ≠ p.1 := ne_of_gt hlt
        have hL_val : L p.2 p.1 = B p.2 p.1 := by simp [L, hne, hlt]
        have hK_val : K p.2 p.1 = -B p.2 p.1 := by simp [K, not_lt_of_gt hlt, hlt]
        rw [hL_val, hK_val]
        ring
      rw [htrL_eq, hsum_half]
      ring
    have heq_B : B.det - C (n : ℤ) * Q ^ 2 =
        (B.det - (K.det + C (2 : ℤ) * (K.adjugate * L).trace)) - C (4 : ℤ) * (C (m : ℤ) * Q ^ 2) := by
      rw [htr_KL, hQ_sq]
      have hn_eq : C (n : ℤ) = C (2 : ℤ) * C (m : ℤ) + 1 := by
        simp only [n, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat,
          map_add, map_mul, map_one]
      have hC2 : C (2 : ℤ) = (2 : ℤ[X]) := by norm_num
      have hC4 : C (4 : ℤ) = (4 : ℤ[X]) := by norm_num
      have hCm : C (m : ℤ) = (m : ℤ[X]) := by exact map_natCast (Polynomial.C : ℤ →+* ℤ[X]) m
      rw [hn_eq, hC4, hC2, hCm]
      ring
    rw [heq_B]
    exact dvd_sub hdet_mod (dvd_mul_right _ _)
  obtain ⟨R1, hR1⟩ := hB_mod4
  have hB_eq : B.det = C (n : ℤ) * Q ^ 2 + C 4 * R1 := by rw [← hR1]; ring
  obtain ⟨P, hP⟩ := two_pow_sub_one_dvd_charpoly_two_mul_sub_one hn_pos hS
  obtain ⟨R2, hR2⟩ := hT_mod
  have hpow_split : C ((2 : ℤ) ^ (n + 1)) = C ((2 : ℤ) ^ (n - 1)) * C (4 : ℤ) := by
    have h4 : (4 : ℤ) = 2 ^ 2 := by norm_num
    have hexp : n + 1 = (n - 1) + 2 := by omega
    rw [hexp, pow_add, h4, map_mul]
  have hcancel :
      C ((n : ℤ) ^ 2) * P - T i0 i0 * B.det = C (4 : ℤ) * R2 := by
    apply mul_left_cancel₀ (by simp : C ((2 : ℤ) ^ (n - 1)) ≠ 0)
    calc
      C ((2 : ℤ) ^ (n - 1)) * (C ((n : ℤ) ^ 2) * P - T i0 i0 * B.det)
          = C ((n : ℤ) ^ 2) * (C ((2 : ℤ) ^ (n - 1)) * P) -
              T i0 i0 * C ((2 : ℤ) ^ (n - 1)) * B.det := by ring
      _ = T.det - T i0 i0 * C ((2 : ℤ) ^ (n - 1)) * B.det := by rw [← hP, hT_det]
      _ = C ((2 : ℤ) ^ (n + 1)) * R2 := hR2
      _ = C ((2 : ℤ) ^ (n - 1)) * (C (4 : ℤ) * R2) := by rw [hpow_split, mul_assoc]
  let R3 : ℤ[X] :=
    R2 + C (∑ a : Fin n, w a) * B.det + C (n : ℤ) * (C 2 * X - C (n : ℤ)) * R1
  have hdiff : C ((n : ℤ) ^ 2) * (P - (C 2 * X - C (n : ℤ)) * Q ^ 2) = C (4 : ℤ) * R3 := by
    have hT00_eq : T i0 i0 = C (n : ℤ) * (C 2 * X - C (n : ℤ)) + C 4 * C (∑ a : Fin n, w a) := by
      rw [hT_00, ← map_mul]
    have hC4B : C ((n : ℤ) ^ 2) * ((C 2 * X - C (n : ℤ)) * Q ^ 2) =
        (C (n : ℤ) * (C 2 * X - C (n : ℤ))) * (B.det - C 4 * R1) := by
      rw [hB_eq, C_pow]
      ring
    calc
      C ((n : ℤ) ^ 2) * (P - (C 2 * X - C (n : ℤ)) * Q ^ 2)
          = (C ((n : ℤ) ^ 2) * P - T i0 i0 * B.det) +
              (T i0 i0 * B.det - (C (n : ℤ) * (C 2 * X - C (n : ℤ))) * (B.det - C 4 * R1)) := by
              rw [← hC4B]; ring
      _ = C (4 : ℤ) * R2 +
            ((C (n : ℤ) * (C 2 * X - C (n : ℤ)) + C 4 * C (∑ a : Fin n, w a)) * B.det -
              (C (n : ℤ) * (C 2 * X - C (n : ℤ))) * (B.det - C 4 * R1)) := by
              rw [hcancel, hT00_eq]
      _ = C (4 : ℤ) * R3 := by
          dsimp [R3]
          ring
  let R : ℤ[X] := R3 - C ((m : ℤ) ^ 2 + (m : ℤ)) * (P - (C 2 * X - C (n : ℤ)) * Q ^ 2)
  have hP_cong : P = (C 2 * X - C (n : ℤ)) * Q ^ 2 + C 4 * R := by
    have hn2 : C ((n : ℤ) ^ 2) = 1 + C (4 : ℤ) * C ((m : ℤ) ^ 2 + (m : ℤ)) := by
      have hn_int : (n : ℤ) ^ 2 = 1 + 4 * ((m : ℤ) ^ 2 + (m : ℤ)) := by
        simp only [n]
        push_cast
        ring
      rw [hn_int, map_add, map_one, map_mul]
    have h1 : P - (C 2 * X - C (n : ℤ)) * Q ^ 2 = C 4 * R := by
      calc
        P - (C 2 * X - C (n : ℤ)) * Q ^ 2
            = C ((n : ℤ) ^ 2) * (P - (C 2 * X - C (n : ℤ)) * Q ^ 2) -
                C (4 : ℤ) * C ((m : ℤ) ^ 2 + (m : ℤ)) * (P - (C 2 * X - C (n : ℤ)) * Q ^ 2) := by
                rw [hn2]; ring
        _ = C (4 : ℤ) * R3 -
              C (4 : ℤ) * C ((m : ℤ) ^ 2 + (m : ℤ)) * (P - (C 2 * X - C (n : ℤ)) * Q ^ 2) := by
              rw [hdiff]
        _ = C 4 * R := by
            dsimp [R]
            ring
    rw [← h1]
    ring
  refine ⟨Q, R, hQ_monic, ?_, ?_⟩
  · rw [hm_eq]
    exact hQ_deg
  · rw [hP, hP_cong]

end Thm42

end EquiangularLines

