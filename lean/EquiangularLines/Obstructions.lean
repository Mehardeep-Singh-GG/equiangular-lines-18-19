module

public import EquiangularLines.Multiplicity
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Phase 2 Obstructions: GKMS Even Bounds, Weapon B (`v_2(χ_{S_u}(λ₀)) = 0`), Jacobi & Kernel Support

This module formalizes the remaining algebraic and 2-adic obstruction pillars from Sections 6 and
8.2 of `reports/algebraist.md`:

1. **GKMS Even-Integer Eigenvalue Bounds (`Section 1`):**
   Modulo `2`, any `n × n` Seidel matrix reduces to `J_n - I_n`, so over `(ZMod 2)[X]`:
   - `even_order_seidel_zmod2_charpoly`: `(S.charpoly).map (ZMod 2) = (X + 1)^n` for even `n`,
     forcing every even integer `k` to satisfy `S.charpoly.eval k ≠ 0`
     (`even_eig_mult_even_order_eq_zero`).
   - `odd_order_seidel_zmod2_charpoly`: `(S.charpoly).map (ZMod 2) = X * (X + 1)^(n - 1)` for
     odd `n`, forcing every even integer `k` to have algebraic multiplicity `≤ 1`
     (`even_eig_mult_odd_order_le_one`).

2. **Weapon B (`v_2(χ_{S_u}(λ₀)) = 0`, Theorem 8.2 & Theorem 8.3):**
   - `exists_hensel_root_mod_two_pow`: For any odd-order Seidel matrix `S` and `k ≥ 1`, Newton/Hensel
     lifting produces an even integer `λ₀` with `2^k ∣ S.charpoly.eval λ₀` and
     `Odd (S.charpoly.derivative.eval λ₀)`.
   - `even_root_mod_four_eq_sub_one`: Any even `λ₀` with `4 ∣ S.charpoly.eval λ₀` satisfies
     `λ₀ ≡ n - 1 [ZMOD 4]`.
   - `strict_type2_eval_mod_eight`: Any Strict-Type-2 polynomial `g : ℤ[X]` of even degree
     `m ≥ 2` satisfies `g.eval λ₀ ≡ (λ₀ + 1)^(m - 1) * (λ₀ + 1 - m) [ZMOD 8]`.
   - `weapon_b_vertex_deletion_mod_eight`, `weapon_b_vertex_deletion_odd`,
     `weapon_b_padicVal_zero`, `weapon_b_derivative_mod_eight`:
     Every `(n - 1) × (n - 1)` vertex deletion `S_u` of an odd-order `n × n` Seidel matrix `S`
     satisfies the universal mod-`8` congruence, has odd evaluation at every even `λ₀`, has
     `padicValNat 2 (S_u.charpoly.eval λ₀).natAbs = 0`, and pins `χ_S'(λ₀) mod 8`.

3. **Jacobi Square-Class & Submatrix Kernel Support (`Section 3`):**
   - `jacobi_square_class_mod_charpoly`: `S.charpoly ∣ S_u.charpoly * S_v.charpoly - P^2`.
   - `psd_submatrix_kernel_extends`: Any kernel vector of a principal submatrix of a real
     symmetric PSD matrix extends by zero to a kernel vector of the full matrix.
   - `ker_submatrix_vanish_of_nullity_gt`: Dimension counting for `mult_μ(A) > m` producing a
     nonzero `μ`-eigenvector supported entirely outside an `m`-subset.
-/

@[expose] public section

open Matrix Polynomial
open scoped BigOperators

namespace EquiangularLines

private lemma eval_finset_sum {R ι : Type*} [CommSemiring R] (s : Finset ι)
    (f : ι → R[X]) (x : R) :
    (∑ i ∈ s, f i).eval x = ∑ i ∈ s, (f i).eval x :=
  map_sum (Polynomial.evalRingHom x) f s

section GKMS

private lemma adjugate_smul_one {n : ℕ} (_hn : 1 ≤ n) {R : Type*} [CommRing R] (c : R) :
    Matrix.adjugate (c • (1 : Matrix (Fin n) (Fin n) R)) =
      (c ^ (n - 1)) • (1 : Matrix (Fin n) (Fin n) R) := by
  ext i j
  rw [Matrix.adjugate_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte, mul_one]
    have hdiag :
        ((c • (1 : Matrix (Fin n) (Fin n) R)).updateRow i (Pi.single i 1)) =
          Matrix.diagonal (fun a : Fin n => if a = i then (1 : R) else c) := by
      ext a b
      by_cases hai : a = i
      · subst hai
        rw [Matrix.updateRow_self, Pi.single_apply, Matrix.diagonal_apply]
        by_cases hba : a = b <;> simp [hba, eq_comm]
      · rw [Matrix.updateRow_ne hai, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply,
          smul_eq_mul]
        by_cases hab : a = b
        · have hbi : b ≠ i := fun h => hai (hab.trans h)
          simp [hab, hbi]
        · simp [hab]
    rw [hdiag, Matrix.det_diagonal, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [↓reduceIte, one_mul]
    have hrest : ∏ x ∈ Finset.univ.erase i, (if x = i then (1 : R) else c) =
        ∏ _x ∈ Finset.univ.erase i, c := by
      refine Finset.prod_congr rfl fun x hx => ?_
      have hxi : x ≠ i := (Finset.mem_erase.mp hx).1
      simp [hxi]
    rw [hrest, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin]
  · simp only [hij, ↓reduceIte, mul_zero]
    refine Matrix.det_eq_zero_of_column_eq_zero j fun a => ?_
    by_cases haj : a = j
    · subst haj
      rw [Matrix.updateRow_self, Pi.single_apply]
      exact ite_eq_right fun h => hij h.symm
    · rw [Matrix.updateRow_ne haj, Matrix.smul_apply, Matrix.one_apply_ne haj, smul_eq_mul,
        mul_zero]

private lemma det_smul_one_sub_ones {n : ℕ} (hn : 1 ≤ n) {R : Type*} [CommRing R] (c : R) :
    (c • (1 : Matrix (Fin n) (Fin n) R) -
        Matrix.vecMulVec (fun _ => (1 : R)) (fun _ => 1)).det =
      c ^ n - (n : R) * c ^ (n - 1) := by
  rw [det_sub_vecMulVec, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin,
    adjugate_smul_one hn c]
  simp only [dotProduct, Matrix.mulVec, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, one_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private lemma zmod2_eval_map (p : ℤ[X]) (k : ℤ) :
    ((p.eval k : ℤ) : ZMod 2) = (p.map (Int.castRingHom (ZMod 2))).eval (k : ZMod 2) := by
  induction p using Polynomial.induction_on' with
  | add p1 p2 ih1 ih2 =>
    rw [Polynomial.eval_add, Int.cast_add, Polynomial.map_add, Polynomial.eval_add, ih1, ih2]
  | monomial d a => simp

private lemma seidel_map_zmod2 {n : ℕ} {S : Matrix (Fin n) (Fin n) ℤ} (hS : IsSeidelMatrix S) :
    S.map (Int.castRingHom (ZMod 2)) =
      Matrix.vecMulVec (fun _ => (1 : ZMod 2)) (fun _ => 1) - 1 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.vecMulVec_apply, Matrix.one_apply,
    mul_one]
  by_cases hij : i = j
  · subst hij
    simp [hS.2.1 i]
  · simp only [hij, ↓reduceIte, sub_zero]
    rcases hS.2.2 i j hij with h | h
    · simp [h]
    · simp [h]

/-- Over `ZMod 2`, the characteristic polynomial of an even-order Seidel matrix equals `(X + 1)^n`. -/
theorem even_order_seidel_zmod2_charpoly {n : ℕ} (hn : Even n)
    {S : Matrix (Fin n) (Fin n) ℤ} (hS : IsSeidelMatrix S) :
    S.charpoly.map (Int.castRingHom (ZMod 2)) = (X + 1) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · simp [Matrix.charpoly, Matrix.det_isEmpty]
  · rw [← Matrix.charpoly_map S (Int.castRingHom (ZMod 2)), seidel_map_zmod2 hS,
      Matrix.charpoly, Matrix.charmatrix]
    have hmat :
        scalar (Fin n) (X : (ZMod 2)[X]) -
            C.mapMatrix (Matrix.vecMulVec (fun _ => (1 : ZMod 2)) (fun _ => 1) - 1) =
          ((X + 1 : (ZMod 2)[X]) • (1 : Matrix (Fin n) (Fin n) (ZMod 2)[X]) -
            Matrix.vecMulVec (fun _ => (1 : (ZMod 2)[X])) (fun _ => 1)) := by
      ext i j
      simp only [Matrix.sub_apply, scalar_apply, Matrix.diagonal_apply, RingHom.mapMatrix_apply,
        Matrix.map_apply, Matrix.vecMulVec_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
      by_cases hij : i = j <;> simp [hij]
    rw [hmat, det_smul_one_sub_ones hn_pos]
    have hn_z2 : ((n : (ZMod 2)[X])) = 0 := by
      rcases hn with ⟨t, ht⟩
      rw [ht, ← two_mul, Nat.cast_mul, Nat.cast_ofNat]
      have h2 : (2 : (ZMod 2)[X]) = 0 := by
        rw [← map_ofNat (C : ZMod 2 →+* (ZMod 2)[X]) 2,
          (by decide : (2 : ZMod 2) = 0), map_zero]
      rw [h2, zero_mul]
    rw [hn_z2, zero_mul, sub_zero]

/-- Over `ZMod 2`, the characteristic polynomial of an odd-order Seidel matrix equals
`X * (X + 1)^(n - 1)`. -/
theorem odd_order_seidel_zmod2_charpoly {n : ℕ} (hn : Odd n)
    {S : Matrix (Fin n) (Fin n) ℤ} (hS : IsSeidelMatrix S) :
    S.charpoly.map (Int.castRingHom (ZMod 2)) = X * (X + 1) ^ (n - 1) := by
  have hn_pos : 1 ≤ n := hn.pos
  rw [← Matrix.charpoly_map S (Int.castRingHom (ZMod 2)), seidel_map_zmod2 hS,
    Matrix.charpoly, Matrix.charmatrix]
  have hmat :
      scalar (Fin n) (X : (ZMod 2)[X]) -
          C.mapMatrix (Matrix.vecMulVec (fun _ => (1 : ZMod 2)) (fun _ => 1) - 1) =
        ((X + 1 : (ZMod 2)[X]) • (1 : Matrix (Fin n) (Fin n) (ZMod 2)[X]) -
          Matrix.vecMulVec (fun _ => (1 : (ZMod 2)[X])) (fun _ => 1)) := by
    ext i j
    simp only [Matrix.sub_apply, scalar_apply, Matrix.diagonal_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, Matrix.vecMulVec_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
    by_cases hij : i = j <;> simp [hij]
  rw [hmat, det_smul_one_sub_ones hn_pos]
  have hn_z2 : (n : (ZMod 2)[X]) = 1 := by
    rcases hn with ⟨t, ht⟩
    rw [ht, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    have h2 : (2 : (ZMod 2)[X]) = 0 := by
      rw [← map_ofNat (C : ZMod 2 →+* (ZMod 2)[X]) 2,
        (by decide : (2 : ZMod 2) = 0), map_zero]
    rw [h2, zero_mul, zero_add]
  have hpow : (X + 1 : (ZMod 2)[X]) ^ n = (X + 1) * (X + 1) ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ']
  rw [hn_z2, one_mul, hpow]
  ring

/-- **GKMS even-eigenvalue exclusion (`Even n`):**
An even-order Seidel matrix cannot have any even integer eigenvalue. -/
theorem even_eig_mult_even_order_eq_zero {n : ℕ} (hn : Even n)
    {S : Matrix (Fin n) (Fin n) ℤ} (hS : IsSeidelMatrix S)
    {k : ℤ} (hk : Even k) :
    S.charpoly.eval k ≠ 0 ∧ S.charpoly.rootMultiplicity k = 0 := by
  have heval_mod2 : ((S.charpoly.eval k : ℤ) : ZMod 2) = 1 := by
    have hk0 : (k : ZMod 2) = 0 := by
      rcases hk with ⟨t, ht⟩
      rw [ht, ← two_mul, Int.cast_mul, Int.cast_ofNat]
      have h2 : (2 : ZMod 2) = 0 := by decide
      rw [h2, zero_mul]
    rw [zmod2_eval_map, even_order_seidel_zmod2_charpoly hn hS]
    simp [hk0]
  have hne : S.charpoly.eval k ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero] at heval_mod2
    exact zero_ne_one heval_mod2
  have hnot_dvd : ¬ (X - C k) ∣ S.charpoly := by
    intro hdvd
    exact hne (Polynomial.dvd_iff_isRoot.mp hdvd)
  have hmult : S.charpoly.rootMultiplicity k = 0 := by
    by_contra hpos
    have h1 : 1 ≤ S.charpoly.rootMultiplicity k := Nat.pos_of_ne_zero hpos
    have hdvd : (X - C k) ^ 1 ∣ S.charpoly :=
      dvd_trans (pow_dvd_pow _ h1) (Polynomial.pow_rootMultiplicity_dvd S.charpoly k)
    exact hnot_dvd (by simpa using hdvd)
  exact ⟨hne, hmult⟩

/-- **GKMS even-eigenvalue multiplicity bound (`Odd n`):**
Every even integer has multiplicity at most `1` as an eigenvalue of an odd-order Seidel matrix. -/
theorem even_eig_mult_odd_order_le_one {n : ℕ} (hn : Odd n)
    {S : Matrix (Fin n) (Fin n) ℤ} (hS : IsSeidelMatrix S)
    {k : ℤ} (hk : Even k) :
    ¬ (X - C k) ^ 2 ∣ S.charpoly ∧ S.charpoly.rootMultiplicity k ≤ 1 := by
  have hnot_dvd : ¬ (X - C k) ^ 2 ∣ S.charpoly := by
    intro hdvd
    have hdvd_map :
        ((X - C k : ℤ[X]) ^ 2).map (Int.castRingHom (ZMod 2)) ∣
          S.charpoly.map (Int.castRingHom (ZMod 2)) :=
      Polynomial.map_dvd (Int.castRingHom (ZMod 2)) hdvd
    have hk0 : (k : ZMod 2) = 0 := by
      rcases hk with ⟨t, ht⟩
      rw [ht, ← two_mul, Int.cast_mul, Int.cast_ofNat]
      have h2 : (2 : ZMod 2) = 0 := by decide
      rw [h2, zero_mul]
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      show (Int.castRingHom (ZMod 2)) k = (k : ZMod 2) by rfl, hk0, Polynomial.C_0, sub_zero,
      odd_order_seidel_zmod2_charpoly hn hS, sq] at hdvd_map
    rcases hdvd_map with ⟨q, hq⟩
    have hcoeff := congrArg (fun P : (ZMod 2)[X] => P.coeff 1) hq
    have hpow0 : ∀ t : ℕ, ((X + 1 : (ZMod 2)[X]) ^ t).coeff 0 = 1 := fun t => by
      induction t with
      | zero => simp
      | succ t ih => rw [pow_succ, Polynomial.mul_coeff_zero, ih]; simp
    have hlhs : ((X : (ZMod 2)[X]) * (X + 1) ^ (n - 1)).coeff 1 = 1 := by
      rw [show (1 : ℕ) = 0 + 1 by rfl, Polynomial.coeff_X_mul, hpow0 (n - 1)]
    have hrhs : ((X * X : (ZMod 2)[X]) * q).coeff 1 = 0 := by
      rw [mul_assoc, show (1 : ℕ) = 0 + 1 by rfl, Polynomial.coeff_X_mul, Polynomial.mul_coeff_zero]
      simp
    rw [hlhs, hrhs] at hcoeff
    exact one_ne_zero hcoeff
  have hmult : S.charpoly.rootMultiplicity k ≤ 1 := by
    by_contra hgt
    have h2 : 2 ≤ S.charpoly.rootMultiplicity k := by omega
    have hdvd : (X - C k) ^ 2 ∣ S.charpoly :=
      dvd_trans (pow_dvd_pow _ h2) (Polynomial.pow_rootMultiplicity_dvd S.charpoly k)
    exact hnot_dvd hdvd
  exact ⟨hnot_dvd, hmult⟩

end GKMS

section WeaponB

private lemma comp_two_mul_X_sub_one_injective {p q : ℤ[X]}
    (h : p.comp (C 2 * X - 1) = q.comp (C 2 * X - 1)) : p = q := by
  let r : ℤ[X] := p - q
  have hr_comp : r.comp (C 2 * X - 1) = 0 := by
    simp only [r, Polynomial.sub_comp, h, sub_self]
  by_contra hne
  have hr_ne : r ≠ 0 := sub_ne_zero.mpr hne
  let f : ℕ → ℤ := fun t => 2 * (t : ℤ) - 1
  have hf_inj : Function.Injective f := fun a b hab => by
    dsimp [f] at hab
    omega
  let s : Finset ℤ := (Finset.range (r.natDegree + 1)).image f
  have hsub : ∀ z ∈ s, z ∈ r.roots := fun z hz => by
    rcases Finset.mem_image.mp hz with ⟨t, _, rfl⟩
    rw [Polynomial.mem_roots hr_ne, Polynomial.IsRoot.def]
    have h0 := congrArg (Polynomial.eval (t : ℤ)) hr_comp
    simp only [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero] at h0
    exact h0
  have hle : s.card ≤ r.roots.card := by
    have hsub' : s ⊆ r.roots.toFinset :=
      Finset.subset_iff.mpr fun z hz => Multiset.mem_toFinset.mpr (hsub z hz)
    exact le_trans (Finset.card_le_card hsub') (Multiset.toFinset_card_le r.roots)
  have hroots_le : r.roots.card ≤ r.natDegree := Polynomial.card_roots' r
  have hcard : s.card = r.natDegree + 1 := by
    rw [Finset.card_image_of_injective _ hf_inj, Finset.card_range]
  omega

private lemma eval_add_taylor_int (f : ℤ[X]) (r h : ℤ) :
    ∃ q : ℤ, f.eval (r + h) = f.eval r + f.derivative.eval r * h + q * h ^ 2 := by
  induction f using Polynomial.induction_on' with
  | add p1 p2 ih1 ih2 =>
    rcases ih1 with ⟨q1, hq1⟩
    rcases ih2 with ⟨q2, hq2⟩
    refine ⟨q1 + q2, ?_⟩
    simp only [Polynomial.eval_add, Polynomial.derivative_add, hq1, hq2]
    ring
  | monomial k a =>
    induction k with
    | zero =>
      refine ⟨0, ?_⟩
      simp
    | succ k ih =>
      rcases ih with ⟨q, hq⟩
      have hsucc : Polynomial.monomial (k + 1) a = X * Polynomial.monomial k a := by
        rw [← Polynomial.C_mul_X_pow_eq_monomial, ← Polynomial.C_mul_X_pow_eq_monomial,
          pow_succ']
        ring
      rw [hsucc, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.derivative_mul,
        Polynomial.derivative_X, one_mul, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_X, hq]
      refine ⟨(Polynomial.monomial k a).derivative.eval r + (r + h) * q, ?_⟩
      ring

/-- **Hensel root approximation (`Weapon B`, Step 1):**
For every odd-order Seidel matrix `S` and every `k ≥ 1`, there exists an even integer `lam0`
such that `2^k ∣ S.charpoly.eval lam0` and `Odd (S.charpoly.derivative.eval lam0)`. -/
theorem exists_hensel_root_mod_two_pow {n : ℕ} (hn : Odd n)
    {S : Matrix (Fin n) (Fin n) ℤ} (hS : IsSeidelMatrix S)
    {k : ℕ} (hk : 1 ≤ k) :
    ∃ lam0 : ℤ, Even lam0 ∧ (2 : ℤ) ^ k ∣ S.charpoly.eval lam0 ∧
      Odd (S.charpoly.derivative.eval lam0) := by
  have hderiv_odd : ∀ r : ℤ, Even r → Odd (S.charpoly.derivative.eval r) := fun r hr => by
    have hmap_deriv :
        (S.charpoly.derivative).map (Int.castRingHom (ZMod 2)) =
          ((X : (ZMod 2)[X]) * (X + 1) ^ (n - 1)).derivative := by
      rw [← Polynomial.derivative_map, odd_order_seidel_zmod2_charpoly hn hS]
    have hr0 : (r : ZMod 2) = 0 := by
      rcases hr with ⟨t, ht⟩
      rw [ht, ← two_mul, Int.cast_mul, Int.cast_ofNat]
      have h2 : (2 : ZMod 2) = 0 := by decide
      rw [h2, zero_mul]
    have hev : ((S.charpoly.derivative.eval r : ℤ) : ZMod 2) = 1 := by
      rw [zmod2_eval_map, hmap_deriv, Polynomial.derivative_mul, Polynomial.derivative_X, one_mul]
      simp [hr0]
    rw [Int.odd_iff]
    by_contra hne
    have hm : S.charpoly.derivative.eval r % 2 = 0 := by omega
    have h2dvd : (2 : ℤ) ∣ S.charpoly.derivative.eval r := Int.dvd_of_emod_eq_zero hm
    rcases h2dvd with ⟨q, hq⟩
    have hz : ((S.charpoly.derivative.eval r : ℤ) : ZMod 2) = 0 := by
      rw [hq, Int.cast_mul, Int.cast_ofNat]
      have h2 : (2 : ZMod 2) = 0 := by decide
      rw [h2, zero_mul]
    rw [hev] at hz
    exact one_ne_zero hz
  induction k, hk using Nat.le_induction with
  | base =>
    refine ⟨0, ⟨0, rfl⟩, ?_, hderiv_odd 0 ⟨0, rfl⟩⟩
    have hev : ((S.charpoly.eval (0 : ℤ) : ℤ) : ZMod 2) = 0 := by
      rw [zmod2_eval_map, odd_order_seidel_zmod2_charpoly hn hS]
      simp
    change ((S.charpoly.eval (0 : ℤ) : ℤ) : ZMod 2) = 0 at hev
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hev
    simpa using hev
  | succ k hk ih =>
    rcases ih with ⟨r, hr_even, hdvd, hodd⟩
    let h : ℤ := S.charpoly.eval r
    have hr'_even : Even (r + h) := by
      have hd2 : (2 : ℤ) ∣ h := dvd_trans (pow_dvd_pow (2 : ℤ) hk) hdvd
      exact hr_even.add (even_iff_two_dvd.mpr hd2)
    refine ⟨r + h, hr'_even, ?_, hderiv_odd (r + h) hr'_even⟩
    rcases eval_add_taylor_int S.charpoly r h with ⟨q, hq⟩
    rw [hq]
    have hterm1 : (2 : ℤ) ^ (k + 1) ∣ h * (1 + S.charpoly.derivative.eval r) := by
      have hev1 : Even (1 + S.charpoly.derivative.eval r) := odd_one.add_odd hodd
      rcases hdvd with ⟨u, hu⟩
      rcases hev1 with ⟨v, hv⟩
      change h = 2 ^ k * u at hu
      refine ⟨u * v, ?_⟩
      rw [hu, hv, ← two_mul, pow_succ']
      ring
    have hterm2 : (2 : ℤ) ^ (k + 1) ∣ q * h ^ 2 := by
      have hk2 : k + 1 ≤ 2 * k := by omega
      have hp : (2 : ℤ) ^ (k + 1) ∣ (2 : ℤ) ^ (2 * k) := pow_dvd_pow 2 hk2
      have hsq : (2 : ℤ) ^ (2 * k) ∣ h ^ 2 := by
        rw [mul_comm, pow_mul]
        exact pow_dvd_pow_of_dvd hdvd 2
      exact dvd_trans (dvd_trans hp hsq) (dvd_mul_left _ _)
    have hfac : h + S.charpoly.derivative.eval r * h + q * h ^ 2 =
        h * (1 + S.charpoly.derivative.eval r) + q * h ^ 2 := by ring
    rw [hfac]
    exact dvd_add hterm1 hterm2

/-- **Parity / Mod-4 congruence for even Hensel roots:**
If `n` is odd, `S` is an `n × n` Seidel matrix, and `lam0` is an even integer with
`4 ∣ S.charpoly.eval lam0`, then `lam0 ≡ n - 1 [ZMOD 4]`. -/
theorem even_root_mod_four_eq_sub_one {n : ℕ} (hn : Odd n)
    {S : Matrix (Fin n) (Fin n) ℤ} (hS : IsSeidelMatrix S)
    {lam0 : ℤ} (hlam : Even lam0) (h4 : (4 : ℤ) ∣ S.charpoly.eval lam0) :
    lam0 ≡ (n : ℤ) - 1 [ZMOD 4] := by
  rcases odd_order_two_adic_congruence hn hS with ⟨Q, R, hQ_mon, hQ_deg, hcong⟩
  have hdiv2 : (n - 1) / 2 + (n - 1) / 2 = n - 1 := by
    rcases hn with ⟨t, rfl⟩
    omega
  let h : ℕ := (n - 1) / 2
  have hR_deg : R = 0 ∨ R.natDegree ≤ n - 1 := by
    by_cases hR0 : R = 0
    · exact Or.inl hR0
    · right
      by_contra hgt
      have hn_le : n ≤ R.natDegree := by omega
      have hp_deg : (C 2 * X - C (n : ℤ)).natDegree = 1 := by
        compute_degree!
      have hp_lc : (C 2 * X - C (n : ℤ)).leadingCoeff = 2 := by
        rw [Polynomial.leadingCoeff, hp_deg]
        compute_degree!
      have hlhs_deg : (S.charpoly.comp (C 2 * X - 1)).natDegree = n := by
        rw [Polynomial.natDegree_comp, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
        have hlin : (C (2 : ℤ) * X - 1).natDegree = 1 := by compute_degree!
        rw [hlin, mul_one]
      have hQ_sq_mon : (Q ^ 2).Monic := hQ_mon.pow 2
      have hQ_sq_deg : (Q ^ 2).natDegree = n - 1 := by
        rw [Polynomial.natDegree_pow, hQ_deg]
        omega
      have hA_deg : ((C 2 * X - C (n : ℤ)) * Q ^ 2).natDegree = n := by
        have hne_lin : C (2 : ℤ) * X - C (n : ℤ) ≠ 0 := by
          intro hz
          have := congrArg Polynomial.natDegree hz
          rw [hp_deg, Polynomial.natDegree_zero] at this
          omega
        rw [Polynomial.natDegree_mul hne_lin (hQ_sq_mon.ne_zero), hp_deg, hQ_sq_deg]
        have hn1 : 1 ≤ n := hn.pos
        omega
      have hB_deg : (C (4 : ℤ) * R).natDegree = R.natDegree := by
        rw [Polynomial.natDegree_C_mul (by norm_num : (4 : ℤ) ≠ 0)]
      rcases eq_or_lt_of_le hn_le with heq | hlt
      · have hlhs_lc : (S.charpoly.comp (C 2 * X - 1)).coeff n = (2 : ℤ) ^ n := by
          have hmon := Matrix.charpoly_monic S
          have hlin_deg : (C (2 : ℤ) * X - 1).natDegree = 1 := by compute_degree!
          have hlin_lc : (C (2 : ℤ) * X - 1).leadingCoeff = 2 := by
            rw [Polynomial.leadingCoeff, hlin_deg]
            compute_degree!
          have hdegS : S.charpoly.natDegree = n := by
            rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
          have hcomp_lc :
              (S.charpoly.comp (C 2 * X - 1)).leadingCoeff = (2 : ℤ) ^ n := by
            rw [Polynomial.leadingCoeff_comp (by omega), hmon.leadingCoeff, one_mul,
              hlin_lc, hdegS]
          rw [Polynomial.leadingCoeff, hlhs_deg] at hcomp_lc
          exact hcomp_lc
        have hcoeff := congrArg (fun P : ℤ[X] => P.coeff n) hcong
        rw [hlhs_lc] at hcoeff
        have hA_lc : ((C 2 * X - C (n : ℤ)) * Q ^ 2).coeff n = 2 := by
          have hlc : ((C 2 * X - C (n : ℤ)) * Q ^ 2).leadingCoeff = 2 := by
            rw [Polynomial.leadingCoeff_mul, hp_lc, hQ_sq_mon.leadingCoeff, mul_one]
          rwa [Polynomial.leadingCoeff, hA_deg] at hlc
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_C_mul, hA_lc] at hcoeff
        have hpow_eq : (2 : ℤ) ^ n = (2 : ℤ) ^ (n - 1) * 2 := by
          conv_lhs => rw [show n = (n - 1) + 1 by have := hn.pos; omega, pow_succ]
        have h4R : (2 : ℤ) ^ (n - 1) * (4 * R.coeff n) = 0 := by linarith
        have hR0' : R.coeff R.natDegree = 0 := by
          rw [← heq]
          rcases mul_eq_zero.mp h4R with h20 | h40
          · exact absurd h20 (pow_ne_zero _ (by norm_num))
          · omega
        exact absurd hR0' (Polynomial.leadingCoeff_ne_zero.mpr hR0)
      · have hlt' : ((C 2 * X - C (n : ℤ)) * Q ^ 2).natDegree < (C (4 : ℤ) * R).natDegree := by
          rw [hA_deg, hB_deg]
          exact hlt
        have hsum_deg :
            ((C 2 * X - C (n : ℤ)) * Q ^ 2 + C 4 * R).natDegree = R.natDegree := by
          rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt hlt', hB_deg]
        have hrhs_deg :
            (C ((2 : ℤ) ^ (n - 1)) * ((C 2 * X - C (n : ℤ)) * Q ^ 2 + C 4 * R)).natDegree =
              R.natDegree := by
          rw [Polynomial.natDegree_C_mul (pow_ne_zero _ (by norm_num)), hsum_deg]
        have hbad := congrArg Polynomial.natDegree hcong
        rw [hlhs_deg, hrhs_deg] at hbad
        omega
  let T : ℤ[X] := ∑ j ∈ Finset.range (h + 1), C ((2 : ℤ) ^ (h - j) * Q.coeff j) * (X + 1) ^ j
  let U : ℤ[X] := ∑ j ∈ Finset.range n, C ((2 : ℤ) ^ (n - 1 - j) * R.coeff j) * (X + 1) ^ j
  have hT_comp : T.comp (C 2 * X - 1) = C ((2 : ℤ) ^ h) * Q := by
    simp only [T, Polynomial.sum_comp, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.pow_comp, Polynomial.add_comp, Polynomial.X_comp, Polynomial.one_comp,
      sub_add_cancel]
    have hterm : ∀ j ∈ Finset.range (h + 1),
        C ((2 : ℤ) ^ (h - j) * Q.coeff j) * (C 2 * X) ^ j =
          C ((2 : ℤ) ^ h) * (C (Q.coeff j) * X ^ j) := fun j hj => by
      have hj_le : j ≤ h := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [mul_pow, ← Polynomial.C_pow]
      have hp : (2 : ℤ) ^ (h - j) * (2 : ℤ) ^ j = (2 : ℤ) ^ h := by
        rw [← pow_add, Nat.sub_add_cancel hj_le]
      calc
        C ((2 : ℤ) ^ (h - j) * Q.coeff j) * (C ((2 : ℤ) ^ j) * X ^ j)
            = C ((2 : ℤ) ^ (h - j) * (2 : ℤ) ^ j * Q.coeff j) * X ^ j := by
              simp only [map_mul]; ring
        _ = C ((2 : ℤ) ^ h) * (C (Q.coeff j) * X ^ j) := by
              rw [hp, map_mul]; ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    congr 1
    simp_rw [Polynomial.C_mul_X_pow_eq_monomial]
    exact (Polynomial.as_sum_range' Q (h + 1) (by omega)).symm
  have hU_comp : U.comp (C 2 * X - 1) = C ((2 : ℤ) ^ (n - 1)) * R := by
    simp only [U, Polynomial.sum_comp, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.pow_comp, Polynomial.add_comp, Polynomial.X_comp, Polynomial.one_comp,
      sub_add_cancel]
    have hterm : ∀ j ∈ Finset.range n,
        C ((2 : ℤ) ^ (n - 1 - j) * R.coeff j) * (C 2 * X) ^ j =
          C ((2 : ℤ) ^ (n - 1)) * (C (R.coeff j) * X ^ j) := fun j hj => by
      have hj_le : j ≤ n - 1 := by
        have := Finset.mem_range.mp hj
        omega
      rw [mul_pow, ← Polynomial.C_pow]
      have hp : (2 : ℤ) ^ (n - 1 - j) * (2 : ℤ) ^ j = (2 : ℤ) ^ (n - 1) := by
        rw [← pow_add, Nat.sub_add_cancel hj_le]
      calc
        C ((2 : ℤ) ^ (n - 1 - j) * R.coeff j) * (C ((2 : ℤ) ^ j) * X ^ j)
            = C ((2 : ℤ) ^ (n - 1 - j) * (2 : ℤ) ^ j * R.coeff j) * X ^ j := by
              simp only [map_mul]; ring
        _ = C ((2 : ℤ) ^ (n - 1)) * (C (R.coeff j) * X ^ j) := by
              rw [hp, map_mul]; ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    congr 1
    rcases hR_deg with rfl | hle
    · simp
    · have hn1 : 1 ≤ n := hn.pos
      simp_rw [Polynomial.C_mul_X_pow_eq_monomial]
      exact (Polynomial.as_sum_range' R n (by omega)).symm
  have hS_eq : S.charpoly = (X + 1 - C (n : ℤ)) * T ^ 2 + C 4 * U := by
    apply comp_two_mul_X_sub_one_injective
    rw [hcong, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.sub_comp, Polynomial.add_comp,
      Polynomial.X_comp, Polynomial.one_comp, Polynomial.C_comp, Polynomial.pow_comp,
      Polynomial.mul_comp, Polynomial.C_comp, hT_comp, hU_comp, sub_add_cancel]
    have h2pow : (C ((2 : ℤ) ^ h)) ^ 2 = C ((2 : ℤ) ^ (n - 1)) := by
      rw [← Polynomial.C_pow, ← pow_mul, show h * 2 = n - 1 by omega]
    rw [mul_pow, h2pow]
    ring
  have hT_odd : Odd (T.eval lam0) := by
    dsimp only [T]
    rw [eval_finset_sum]
    rw [Finset.sum_range_succ]
    have hlow_even :
        Even (∑ j ∈ Finset.range h,
          (C ((2 : ℤ) ^ (h - j) * Q.coeff j) * (X + 1) ^ j).eval lam0) := by
      refine Finset.even_sum _ fun j hj => ?_
      have hj_lt : j < h := Finset.mem_range.mp hj
      have h2dvd : (2 : ℤ) ∣ (2 : ℤ) ^ (h - j) :=
        dvd_pow_self 2 (by omega)
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      exact (even_iff_two_dvd.mpr h2dvd).mul_right _ |>.mul_right _
    have htop_odd : Odd ((C ((2 : ℤ) ^ (h - h) * Q.coeff h) * (X + 1) ^ h).eval lam0) := by
      have hQc : Q.coeff h = 1 := by
        dsimp only [h]
        rw [← hQ_deg]
        exact hQ_mon.leadingCoeff
      simp only [Nat.sub_self, pow_zero, one_mul, hQc, map_one, Polynomial.eval_pow,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
      exact (hlam.add_one).pow
    exact hlow_even.add_odd htop_odd
  have hT2_mod4 : (T.eval lam0) ^ 2 ≡ 1 [ZMOD 4] := by
    rw [Int.modEq_iff_dvd]
    rcases hT_odd with ⟨u, hu⟩
    refine ⟨-(u * (u + 1)), ?_⟩
    rw [hu]
    ring
  have hev := congrArg (Polynomial.eval lam0) hS_eq
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_pow] at hev
  rw [Int.modEq_iff_dvd]
  have hd4 : (4 : ℤ) ∣ (lam0 + 1 - n) * ((T.eval lam0) ^ 2 - 1) :=
    dvd_mul_of_dvd_right (Int.modEq_iff_dvd.mp hT2_mod4.symm) _
  have hd4' : (4 : ℤ) ∣ 4 * U.eval lam0 := dvd_mul_right _ _
  have hid : lam0 - ((n : ℤ) - 1) =
      (S.charpoly.eval lam0 - 4 * U.eval lam0) - (lam0 + 1 - n) * ((T.eval lam0) ^ 2 - 1) := by
    rw [hev]
    ring
  have hsub : (4 : ℤ) ∣ (S.charpoly.eval lam0 - 4 * U.eval lam0) -
      (lam0 + 1 - n) * ((T.eval lam0) ^ 2 - 1) :=
    dvd_sub (dvd_sub h4 hd4') hd4
  rw [← hid] at hsub
  simpa [sub_eq_add_neg, add_comm] using hsub.neg_right

/-- **Theorem 8.3 (Universal Mod-8 Congruence for Strict Type-2 Polynomials):**
Let `m ≥ 2` be even and `g : ℤ[X]` be monic of degree `m` with `g.coeff (m - 1) = 0`,
`g.coeff (m - 2) = -((m * (m - 1) / 2 : ℕ) : ℤ)`, and `C (2^m) ∣ g.comp (2X - 1)`.
Then for every integer `lam0`:
`g.eval lam0 ≡ (lam0 + 1)^(m - 1) * (lam0 + 1 - m) [ZMOD 8]`. -/
theorem strict_type2_eval_mod_eight {m : ℕ} (hm : Even m) (hm2 : 2 ≤ m) {g : ℤ[X]}
    (hg_mon : g.Monic) (hg_deg : g.natDegree = m)
    (hg_c1 : g.coeff (m - 1) = 0)
    (hg_c2 : g.coeff (m - 2) = -((m * (m - 1) / 2 : ℕ) : ℤ))
    (hdvd : C ((2 : ℤ) ^ m) ∣ g.comp (C 2 * X - 1))
    (lam0 : ℤ) :
    g.eval lam0 ≡ (lam0 + 1) ^ (m - 1) * (lam0 + 1 - (m : ℤ)) [ZMOD 8] := by
  rcases hdvd with ⟨H, hH_eq⟩
  have hH_deg : H.natDegree = m := by
    have hlin_deg : (C (2 : ℤ) * X - 1).natDegree = 1 := by compute_degree!
    have hlhs : (g.comp (C 2 * X - 1)).natDegree = m := by
      rw [Polynomial.natDegree_comp, hg_deg, hlin_deg, mul_one]
    have hH_ne : H ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hH_eq
      have := congrArg Polynomial.natDegree hH_eq
      rw [hlhs, Polynomial.natDegree_zero] at this
      omega
    have hrhs : (C ((2 : ℤ) ^ m) * H).natDegree = H.natDegree :=
      Polynomial.natDegree_C_mul (pow_ne_zero _ (by norm_num))
    rw [← hH_eq, hlhs] at hrhs
    exact hrhs.symm
  have hH_top : H.coeff m = 1 := by
    have hlin_deg : (C (2 : ℤ) * X - 1).natDegree = 1 := by compute_degree!
    have hlin_lc : (C (2 : ℤ) * X - 1).leadingCoeff = 2 := by
      rw [Polynomial.leadingCoeff, hlin_deg]
      compute_degree!
    have hlhs_lc : (g.comp (C 2 * X - 1)).leadingCoeff = (2 : ℤ) ^ m := by
      rw [Polynomial.leadingCoeff_comp (by omega), hg_mon.leadingCoeff, one_mul, hlin_lc, hg_deg]
    have hlhs_deg : (g.comp (C 2 * X - 1)).natDegree = m := by
      rw [Polynomial.natDegree_comp, hg_deg, hlin_deg, mul_one]
    have hcoeff := congrArg (fun P : ℤ[X] => P.coeff m) hH_eq
    have hlhs_c : (g.comp (C 2 * X - 1)).coeff m = (2 : ℤ) ^ m := by
      rw [Polynomial.leadingCoeff, hlhs_deg] at hlhs_lc
      exact hlhs_lc
    rw [hlhs_c, Polynomial.coeff_C_mul] at hcoeff
    have hdiff : (2 : ℤ) ^ m * (H.coeff m - 1) = 0 := by linarith
    rcases mul_eq_zero.mp hdiff with h20 | hc0
    · exact absurd h20 (pow_ne_zero _ (by norm_num))
    · linarith
  let G : ℤ[X] := ∑ k ∈ Finset.range (m + 1), C ((2 : ℤ) ^ (m - k) * H.coeff k) * (X + 1) ^ k
  have hg_eq : g = G := by
    apply comp_two_mul_X_sub_one_injective
    rw [hH_eq]
    simp only [G, Polynomial.sum_comp, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.pow_comp, Polynomial.add_comp, Polynomial.X_comp, Polynomial.one_comp,
      sub_add_cancel]
    have hterm : ∀ k ∈ Finset.range (m + 1),
        C ((2 : ℤ) ^ (m - k) * H.coeff k) * (C 2 * X) ^ k =
          C ((2 : ℤ) ^ m) * (C (H.coeff k) * X ^ k) := fun k hk => by
      have hk_le : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [mul_pow, ← Polynomial.C_pow]
      have hp : (2 : ℤ) ^ (m - k) * (2 : ℤ) ^ k = (2 : ℤ) ^ m := by
        rw [← pow_add, Nat.sub_add_cancel hk_le]
      calc
        C ((2 : ℤ) ^ (m - k) * H.coeff k) * (C ((2 : ℤ) ^ k) * X ^ k)
            = C ((2 : ℤ) ^ (m - k) * (2 : ℤ) ^ k * H.coeff k) * X ^ k := by
              simp only [map_mul]; ring
        _ = C ((2 : ℤ) ^ m) * (C (H.coeff k) * X ^ k) := by
              rw [hp, map_mul]; ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    congr 1
    simp_rw [Polynomial.C_mul_X_pow_eq_monomial]
    exact Polynomial.as_sum_range' H (m + 1) (by omega)
  let L : ℤ[X] := ∑ k ∈ Finset.range (m - 2), C ((2 : ℤ) ^ (m - k) * H.coeff k) * (X + 1) ^ k
  have hG_split : G = L +
      C ((2 : ℤ) ^ 2 * H.coeff (m - 2)) * (X + 1) ^ (m - 2) +
      C ((2 : ℤ) ^ 1 * H.coeff (m - 1)) * (X + 1) ^ (m - 1) +
      (X + 1) ^ m := by
    let term : ℕ → ℤ[X] := fun k => C ((2 : ℤ) ^ (m - k) * H.coeff k) * (X + 1) ^ k
    have hsplit1 : (∑ k ∈ Finset.range (m + 1), term k) =
        (∑ k ∈ Finset.range m, term k) + term m := Finset.sum_range_succ term m
    have hsplit2 : (∑ k ∈ Finset.range m, term k) =
        (∑ k ∈ Finset.range (m - 1), term k) + term (m - 1) := by
      conv_lhs => rw [show Finset.range m = Finset.range ((m - 1) + 1) by congr 1; omega]
      exact Finset.sum_range_succ term (m - 1)
    have hsplit3 : (∑ k ∈ Finset.range (m - 1), term k) =
        (∑ k ∈ Finset.range (m - 2), term k) + term (m - 2) := by
      conv_lhs => rw [show Finset.range (m - 1) = Finset.range ((m - 2) + 1) by congr 1; omega]
      exact Finset.sum_range_succ term (m - 2)
    have htm : term m = (X + 1) ^ m := by
      dsimp only [term]
      rw [Nat.sub_self, pow_zero, one_mul, hH_top, map_one, one_mul]
    have htm1 : term (m - 1) = C ((2 : ℤ) ^ 1 * H.coeff (m - 1)) * (X + 1) ^ (m - 1) := by
      dsimp only [term]
      rw [show m - (m - 1) = 1 by omega]
    have htm2 : term (m - 2) = C ((2 : ℤ) ^ 2 * H.coeff (m - 2)) * (X + 1) ^ (m - 2) := by
      dsimp only [term]
      rw [show m - (m - 2) = 2 by omega]
    change ∑ k ∈ Finset.range (m + 1), term k = _
    rw [hsplit1, hsplit2, hsplit3, htm, htm1, htm2]
  have hL_deg : L.natDegree < m - 2 ∨ m - 2 = 0 := by
    by_cases hm2' : m = 2
    · right; omega
    · left
      have hle : L.natDegree ≤ m - 3 := by
        refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
        have hk_lt : k < m - 2 := Finset.mem_range.mp hk
        calc
          (C ((2 : ℤ) ^ (m - k) * H.coeff k) * (X + 1) ^ k).natDegree
              ≤ ((X + 1 : ℤ[X]) ^ k).natDegree := Polynomial.natDegree_C_mul_le _ _
          _ = k := by
              rw [Polynomial.natDegree_pow, show (X + 1 : ℤ[X]).natDegree = 1 by compute_degree!,
                mul_one]
          _ ≤ m - 3 := by omega
      omega
  have hL_c1 : L.coeff (m - 1) = 0 := by
    rcases hL_deg with hlt | hz
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    · have : L = 0 := by simp [L, hz]
      simp [this]
  have hL_c2 : L.coeff (m - 2) = 0 := by
    rcases hL_deg with hlt | hz
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt hlt
    · have : L = 0 := by simp [L, hz]
      simp [this]
  have hXp1_coeff : ∀ d j : ℕ, ((X + 1 : ℤ[X]) ^ d).coeff j = (d.choose j : ℤ) := fun d j => by
    have h1 : (X + 1 : ℤ[X]) = X + C 1 := by simp
    rw [h1, Polynomial.coeff_X_add_C_pow]
    simp
  have hc1_eq : H.coeff (m - 1) * 2 = -(m : ℤ) := by
    have h := congrArg (fun P : ℤ[X] => P.coeff (m - 1)) (hg_eq.trans hG_split)
    rw [hg_c1] at h
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, hL_c1, zero_add] at h
    have hdeg_m2 : ((X + 1 : ℤ[X]) ^ (m - 2)).coeff (m - 1) = 0 := by
      rw [hXp1_coeff, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    rw [hdeg_m2, mul_zero, zero_add, hXp1_coeff, hXp1_coeff, Nat.choose_self, Nat.cast_one,
      mul_one, Nat.choose_symm (by omega : 1 ≤ m), Nat.choose_one_right] at h
    linarith
  have hc2_eq : H.coeff (m - 2) = 0 := by
    have h := congrArg (fun P : ℤ[X] => P.coeff (m - 2)) (hg_eq.trans hG_split)
    rw [hg_c2] at h
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, hL_c2, zero_add] at h
    have hch1 : (m - 1).choose (m - 2) = m - 1 := by
      rw [show m - 2 = (m - 1) - 1 by omega, Nat.choose_symm (by omega : 1 ≤ m - 1),
        Nat.choose_one_right]
    have hch2 : m.choose (m - 2) = m * (m - 1) / 2 := by
      rw [Nat.choose_symm (by omega : 2 ≤ m), Nat.choose_two_right]
    rw [hXp1_coeff, hXp1_coeff, hXp1_coeff, Nat.choose_self, Nat.cast_one, mul_one,
      hch1, hch2] at h
    have hdiv2 : 2 * (m * (m - 1) / 2) = m * (m - 1) := by
      have hev_prod : Even (m * (m - 1)) := hm.mul_right _
      exact Nat.mul_div_cancel' (even_iff_two_dvd.mp hev_prod)
    have hmul_eq : (2 : ℤ) ^ 1 * H.coeff (m - 1) * ((m - 1 : ℕ) : ℤ) =
        -((m : ℤ) * ((m - 1 : ℕ) : ℤ)) := by
      calc
        (2 : ℤ) ^ 1 * H.coeff (m - 1) * ((m - 1 : ℕ) : ℤ)
            = (H.coeff (m - 1) * 2) * ((m - 1 : ℕ) : ℤ) := by ring
        _ = -(m : ℤ) * ((m - 1 : ℕ) : ℤ) := by rw [hc1_eq]
        _ = -((m : ℤ) * ((m - 1 : ℕ) : ℤ)) := by ring
    rw [hmul_eq] at h
    have h2Z : (2 : ℤ) * ((m * (m - 1) / 2 : ℕ) : ℤ) = (m : ℤ) * ((m - 1 : ℕ) : ℤ) := by
      exact_mod_cast hdiv2
    linarith
  have heval_L : (8 : ℤ) ∣ L.eval lam0 := by
    dsimp only [L]
    rw [eval_finset_sum]
    refine Finset.dvd_sum fun k hk => ?_
    have hk_lt : k < m - 2 := Finset.mem_range.mp hk
    have h3 : 3 ≤ m - k := by omega
    have hdvd8 : (8 : ℤ) ∣ (2 : ℤ) ^ (m - k) := by
      simpa [show (8 : ℤ) = 2 ^ 3 by norm_num] using pow_dvd_pow (2 : ℤ) h3
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hdvd8 _) _
  have heval_g : g.eval lam0 = L.eval lam0 + (lam0 + 1) ^ (m - 1) * (lam0 + 1 - (m : ℤ)) := by
    have hev := congrArg (Polynomial.eval lam0) (hg_eq.trans hG_split)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one, hc2_eq, mul_zero, zero_mul, add_zero] at hev
    rw [hev]
    have hpow_m : (lam0 + 1) ^ m = (lam0 + 1) ^ (m - 1) * (lam0 + 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
    have hlin_c1 : (2 : ℤ) ^ 1 * H.coeff (m - 1) = -(m : ℤ) := by linarith
    rw [hlin_c1, hpow_m]
    ring
  rw [Int.modEq_iff_dvd]
  rw [heval_g]
  simpa using heval_L.neg_right

private lemma vertex_deletion_isSeidel {m : ℕ} {S : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ}
    (hS : IsSeidelMatrix S) (u : Fin (m + 1)) :
    IsSeidelMatrix (S.submatrix u.succAbove u.succAbove) := by
  refine ⟨?_, fun i => hS.2.1 _, fun i j hij => hS.2.2 _ _ (u.succAboveEmb.injective.ne hij)⟩
  ext i j
  exact congrArg (fun M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ => M (u.succAbove i) (u.succAbove j))
    hS.1

/-- **Weapon B (Theorem 8.2 + 8.3, mod-8 congruence on vertex deletions):**
For every even `m ≥ 2`, every `(m + 1) × (m + 1)` Seidel matrix `S`, every vertex `u`, and every
integer `lam0`, the vertex-deleted characteristic polynomial satisfies:
`S_u.charpoly.eval lam0 ≡ (lam0 + 1)^(m - 1) * (lam0 + 1 - m) [ZMOD 8]`. -/
theorem weapon_b_vertex_deletion_mod_eight {m : ℕ} (hm : Even m) (hm2 : 2 ≤ m)
    {S : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hS : IsSeidelMatrix S)
    (u : Fin (m + 1)) (lam0 : ℤ) :
    (S.submatrix u.succAbove u.succAbove).charpoly.eval lam0 ≡
      (lam0 + 1) ^ (m - 1) * (lam0 + 1 - (m : ℤ)) [ZMOD 8] := by
  let Su := S.submatrix u.succAbove u.succAbove
  have hSu : IsSeidelMatrix Su := vertex_deletion_isSeidel hS u
  have hm1 : 1 ≤ m := by omega
  have hc1 := seidel_charpoly_coeff_sub_one hm1 hSu
  have hc2 := seidel_charpoly_coeff_sub_two hm2 hSu
  have hdvd := even_order_two_pow_dvd_charpoly hm hSu
  have hdeg : Su.charpoly.natDegree = m := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  exact strict_type2_eval_mod_eight hm hm2 (Matrix.charpoly_monic Su) hdeg hc1 hc2 hdvd lam0

/-- **Weapon B (Parity obstruction `v_2(χ_{S_u}(λ₀)) = 0`):**
For every even `m`, every `(m + 1) × (m + 1)` Seidel matrix `S`, every vertex `u`, and every
even integer `lam0`, `S_u.charpoly.eval lam0` is odd (not divisible by `2`). -/
theorem weapon_b_vertex_deletion_odd {m : ℕ} (hm : Even m)
    {S : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hS : IsSeidelMatrix S)
    (u : Fin (m + 1)) {lam0 : ℤ} (hlam : Even lam0) :
    Odd ((S.submatrix u.succAbove u.succAbove).charpoly.eval lam0) ∧
      ¬ (2 : ℤ) ∣ (S.submatrix u.succAbove u.succAbove).charpoly.eval lam0 := by
  let Su := S.submatrix u.succAbove u.succAbove
  have hSu : IsSeidelMatrix Su := vertex_deletion_isSeidel hS u
  have heval_mod2 : ((Su.charpoly.eval lam0 : ℤ) : ZMod 2) = 1 := by
    have hk0 : (lam0 : ZMod 2) = 0 := by
      rcases hlam with ⟨t, ht⟩
      rw [ht, ← two_mul, Int.cast_mul, Int.cast_ofNat]
      have h2 : (2 : ZMod 2) = 0 := by decide
      rw [h2, zero_mul]
    rw [zmod2_eval_map, even_order_seidel_zmod2_charpoly hm hSu]
    simp [hk0]
  have hnot : ¬ (2 : ℤ) ∣ Su.charpoly.eval lam0 := by
    intro h2
    have h2' : ((2 : ℕ) : ℤ) ∣ Su.charpoly.eval lam0 := by simpa using h2
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h2'
    rw [h2'] at heval_mod2
    exact zero_ne_one heval_mod2
  have hodd : Odd (Su.charpoly.eval lam0) := by
    rw [Int.odd_iff]
    omega
  exact ⟨hodd, hnot⟩

/-- **Weapon B (2-adic valuation zero):**
For every even `m`, `(m + 1) × (m + 1)` Seidel matrix `S`, vertex `u`, and even `lam0`,
`padicValNat 2 (S_u.charpoly.eval lam0).natAbs = 0`. -/
theorem weapon_b_padicVal_zero {m : ℕ} (hm : Even m)
    {S : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hS : IsSeidelMatrix S)
    (u : Fin (m + 1)) {lam0 : ℤ} (hlam : Even lam0) :
    padicValNat 2 ((S.submatrix u.succAbove u.succAbove).charpoly.eval lam0).natAbs = 0 := by
  have hnot := (weapon_b_vertex_deletion_odd hm hS u hlam).2
  have hnot_nat : ¬ (2 : ℕ) ∣ ((S.submatrix u.succAbove u.succAbove).charpoly.eval lam0).natAbs := by
    intro h2
    exact hnot (Int.natCast_dvd.mpr h2)
  rw [Nat.padicValNat_def]
  exact multiplicity_eq_zero_of_not_dvd hnot_nat

/-- **Weapon B (Derivative sum congruence mod 8):**
Summing `weapon_b_vertex_deletion_mod_eight` over all `m + 1` vertices gives
`S.charpoly.derivative.eval lam0 ≡ (m + 1) * (lam0 + 1)^(m - 1) * (lam0 + 1 - m) [ZMOD 8]`. -/
theorem weapon_b_derivative_mod_eight {m : ℕ} (hm : Even m) (hm2 : 2 ≤ m)
    {S : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hS : IsSeidelMatrix S) (lam0 : ℤ) :
    S.charpoly.derivative.eval lam0 ≡
      ((m + 1 : ℕ) : ℤ) * ((lam0 + 1) ^ (m - 1) * (lam0 + 1 - (m : ℤ))) [ZMOD 8] := by
  have hderiv :
      S.charpoly.derivative =
        ∑ u : Fin (m + 1), (S.submatrix u.succAbove u.succAbove).charpoly := by
    rw [derivative_charpoly_eq_sum_adjugate_diag]
    refine Finset.sum_congr rfl fun u _ => ?_
    exact charmatrix_adjugate_diag S u u.succAboveEmb (Fin.succAbove_ne u)
  rw [hderiv, eval_finset_sum, Int.modEq_iff_dvd]
  have hsum :
      ((∑ _u : Fin (m + 1), (lam0 + 1) ^ (m - 1) * (lam0 + 1 - (m : ℤ))) -
        ∑ u : Fin (m + 1), (S.submatrix u.succAbove u.succAbove).charpoly.eval lam0) =
      ∑ u : Fin (m + 1),
        ((lam0 + 1) ^ (m - 1) * (lam0 + 1 - (m : ℤ)) -
          (S.submatrix u.succAbove u.succAbove).charpoly.eval lam0) := by
    rw [← Finset.sum_sub_distrib]
  have hdvd_sum :
      (8 : ℤ) ∣
        (∑ _u : Fin (m + 1), (lam0 + 1) ^ (m - 1) * (lam0 + 1 - (m : ℤ))) -
          ∑ u : Fin (m + 1), (S.submatrix u.succAbove u.succAbove).charpoly.eval lam0 := by
    rw [hsum]
    exact Finset.dvd_sum fun u _ =>
      Int.modEq_iff_dvd.mp (weapon_b_vertex_deletion_mod_eight hm hm2 hS u lam0)
  simpa using hdvd_sum

end WeaponB

section JacobiAndKernel

/-- **Jacobi Square-Class Compatibility (Obstruction 2):**
For any symmetric matrix `A : Matrix (Fin n) (Fin n) ℤ` and distinct indices `i ≠ j`, the product
of the two single-vertex deletion characteristic polynomials is a square modulo `A.charpoly` in
`ℤ[X]`:
`χ_{A_i} * χ_{A_j} - P^2 = χ_A * χ_{A_{i,j}}`. -/
theorem jacobi_square_class_mod_charpoly {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hAsymm : Aᵀ = A) {i j : Fin n} (hij : i ≠ j) :
    ∃ (fi : Fin (n - 1) ↪ Fin n) (fj : Fin (n - 1) ↪ Fin n) (fij : Fin (n - 2) ↪ Fin n)
      (P : ℤ[X]),
      (∀ t, fi t ≠ i) ∧ (∀ t, fj t ≠ j) ∧ (∀ t, fij t ≠ i ∧ fij t ≠ j) ∧
      (A.submatrix fi fi).charpoly * (A.submatrix fj fj).charpoly - P ^ 2 =
        A.charpoly * (A.submatrix fij fij).charpoly := by
  have h2n : 2 ≤ n := by
    have hsub : ({i, j} : Finset (Fin n)).card ≤ (Finset.univ : Finset (Fin n)).card :=
      Finset.card_le_univ _
    simpa [Finset.card_pair hij, Finset.card_fin] using hsub
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let fi : Fin m ↪ Fin (m + 1) := i.succAboveEmb
  let fj : Fin m ↪ Fin (m + 1) := j.succAboveEmb
  obtain ⟨fij, e, h0, h1, he_compl⟩ := exists_compl_equiv_pair hij
  have hfij_ne : ∀ t : Fin (m + 1 - 2), fij t ≠ i ∧ fij t ≠ j := fun t => by
    have ht1 : fij t ≠ i := by
      intro h
      have := e.injective ((he_compl t).trans (h.trans h0.symm))
      simp at this
    have ht2 : fij t ≠ j := by
      intro h
      have := e.injective ((he_compl t).trans (h.trans h1.symm))
      simp at this
    exact ⟨ht1, ht2⟩
  let M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ[X] := charmatrix A
  have hM_symm : Mᵀ = M := by
    ext a b
    simp only [M, charmatrix, Matrix.transpose_apply, Matrix.sub_apply, scalar_apply,
      Matrix.diagonal_apply, RingHom.mapMatrix_apply, Matrix.map_apply, eq_comm]
    have hab : A b a = A a b :=
      congrArg (fun X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ => X a b) hAsymm
    rw [hab]
  have hadj_symm : (Matrix.adjugate M) j i = (Matrix.adjugate M) i j := by
    have htr : (Matrix.adjugate M)ᵀ = Matrix.adjugate M := by
      rw [Matrix.adjugate_transpose, hM_symm]
    exact congrArg (fun X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ[X] => X i j) htr
  have hjac := jacobi_complementary_minor M hij fij e h0 h1 he_compl
  have hMi : Matrix.adjugate M i i = (A.submatrix fi fi).charpoly :=
    charmatrix_adjugate_diag A i fi (Fin.succAbove_ne i)
  have hMj : Matrix.adjugate M j j = (A.submatrix fj fj).charpoly :=
    charmatrix_adjugate_diag A j fj (Fin.succAbove_ne j)
  have hMij : (M.submatrix fij fij).det = (A.submatrix fij fij).charpoly := by
    have hsub : M.submatrix fij fij = charmatrix (A.submatrix fij fij) := by
      ext a b
      by_cases hab : a = b
      · subst hab; simp [M, charmatrix]
      · simp [M, charmatrix, hab, fij.injective.ne hab]
    rw [hsub]
    rfl
  refine ⟨fi, fj, fij, Matrix.adjugate M i j, Fin.succAbove_ne i, Fin.succAbove_ne j,
    hfij_ne, ?_⟩
  rw [← hMi, ← hMj, ← hMij]
  rw [hadj_symm, ← sq] at hjac
  exact hjac

/-- **Principal submatrix kernel extension (`Obstruction 4`, PSD case):**
If `M : Matrix (Fin n) (Fin n) ℝ` is real symmetric and positive semidefinite (`∀ y, 0 ≤ y ⬝ᵥ M *ᵥ y`),
then any kernel vector `x : Fin m → ℝ` of a principal submatrix `M.submatrix f f` zero-extends
to a genuine kernel vector `xExt : Fin n → ℝ` of `M`, and in particular `∑ a, M j (f a) * x a = 0`
for every vertex `j : Fin n`. -/
theorem psd_submatrix_kernel_extends {n m : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.IsHermitian) (hpsd : ∀ y : Fin n → ℝ, 0 ≤ y ⬝ᵥ (M *ᵥ y))
    (f : Fin m ↪ Fin n) {x : Fin m → ℝ} (hx : (M.submatrix f f) *ᵥ x = 0) :
    ∃ xExt : Fin n → ℝ,
      (∀ a : Fin m, xExt (f a) = x a) ∧
      (∀ i : Fin n, (∀ a : Fin m, f a ≠ i) → xExt i = 0) ∧
      M *ᵥ xExt = 0 ∧
      (∀ j : Fin n, ∑ a : Fin m, M j (f a) * x a = 0) := by
  let xExt : Fin n → ℝ := fun i => ∑ a : Fin m, if f a = i then x a else 0
  have hxExt_f : ∀ a : Fin m, xExt (f a) = x a := fun a => by
    simp only [xExt, f.injective.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hxExt_out : ∀ i : Fin n, (∀ a : Fin m, f a ≠ i) → xExt i = 0 := fun i hi =>
    Finset.sum_eq_zero fun a _ => ite_eq_right (hi a)
  have hsum_ext : ∀ g : Fin n → ℝ, (∑ i : Fin n, xExt i * g i) = ∑ a : Fin m, x a * g (f a) := by
    intro g
    simp_rw [xExt, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hMxExt : ∀ j : Fin n, (M *ᵥ xExt) j = ∑ a : Fin m, M j (f a) * x a := fun j => by
    simp only [Matrix.mulVec, dotProduct]
    have hswap : (∑ i : Fin n, M j i * xExt i) = ∑ i : Fin n, xExt i * M j i :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hswap, hsum_ext]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have hquad0 : xExt ⬝ᵥ (M *ᵥ xExt) = 0 := by
    change (∑ i : Fin n, xExt i * (M *ᵥ xExt) i) = 0
    rw [hsum_ext]
    have hsub : (∑ a : Fin m, x a * (M *ᵥ xExt) (f a)) = x ⬝ᵥ ((M.submatrix f f) *ᵥ x) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      have hfa := hMxExt (f a)
      simp only [Matrix.mulVec, dotProduct] at hfa
      rw [hfa]
    rw [hsub, hx, dotProduct_zero]
  let U : Matrix (Fin n) (Fin n) ℝ := (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  have hUU : U * Uᵀ = 1 := by
    have h := Unitary.coe_mul_star_self hM.eigenvectorUnitary
    simpa [U, Matrix.star_eq_conjTranspose] using h
  have hU'U : Uᵀ * U = 1 := by
    have h := Unitary.coe_star_mul_self hM.eigenvectorUnitary
    simpa [U, Matrix.star_eq_conjTranspose] using h
  have hspec : M = U * Matrix.diagonal hM.eigenvalues * Uᵀ := by
    simpa [U, Matrix.star_eq_conjTranspose, RCLike.ofReal_real_eq_id] using hM.spectral_theorem
  have heig_nonneg : ∀ k : Fin n, 0 ≤ hM.eigenvalues k := fun k => by
    let q : Fin n → ℝ := U *ᵥ Pi.single k 1
    have h0 := hpsd q
    have hMq : M *ᵥ q = hM.eigenvalues k • q := by
      dsimp [q]
      conv_lhs => rw [hspec]
      calc
        (U * Matrix.diagonal hM.eigenvalues * Uᵀ) *ᵥ (U *ᵥ Pi.single k 1)
            = U *ᵥ (Matrix.diagonal hM.eigenvalues *ᵥ ((Uᵀ * U) *ᵥ Pi.single k 1)) := by
              simp only [Matrix.mul_assoc, Matrix.mulVec_mulVec]
        _ = U *ᵥ (Matrix.diagonal hM.eigenvalues *ᵥ Pi.single k 1) := by
              rw [hU'U, Matrix.one_mulVec]
        _ = U *ᵥ ((hM.eigenvalues k) • Pi.single k 1) := by
              congr 1; ext j
              simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
              split_ifs with hjk <;> simp [hjk]
        _ = (hM.eigenvalues k) • (U *ᵥ Pi.single k 1) := Matrix.mulVec_smul _ _ _
    have hqq : q ⬝ᵥ q = 1 := by
      calc
        q ⬝ᵥ q = (U *ᵥ Pi.single k 1) ⬝ᵥ (U *ᵥ Pi.single k 1) := rfl
        _ = ((Uᵀ * U) *ᵥ Pi.single k 1) ⬝ᵥ Pi.single k 1 := by
              rw [dotProduct_mulVec]
              have hstep : (U *ᵥ Pi.single k 1) ᵥ* U = Uᵀ *ᵥ (U *ᵥ Pi.single k 1) := by
                ext j
                simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
                  mul_comm]
              rw [hstep, Matrix.mulVec_mulVec]
        _ = Pi.single k (1 : ℝ) ⬝ᵥ Pi.single k 1 := by rw [hU'U, Matrix.one_mulVec]
        _ = 1 := by simp [dotProduct, Pi.single_apply]
    rw [hMq, dotProduct_smul, hqq, smul_eq_mul, mul_one] at h0
    exact h0
  let y : Fin n → ℝ := Uᵀ *ᵥ xExt
  have hquad_sum : xExt ⬝ᵥ (M *ᵥ xExt) = ∑ k : Fin n, hM.eigenvalues k * y k ^ 2 := by
    have h1 : xExt ⬝ᵥ (M *ᵥ xExt) = y ⬝ᵥ (Matrix.diagonal hM.eigenvalues *ᵥ y) := by
      conv_lhs => rw [hspec]
      calc
        xExt ⬝ᵥ ((U * Matrix.diagonal hM.eigenvalues * Uᵀ) *ᵥ xExt)
            = xExt ⬝ᵥ (U *ᵥ (Matrix.diagonal hM.eigenvalues *ᵥ y)) := by
              simp only [y, Matrix.mul_assoc, Matrix.mulVec_mulVec]
        _ = (Uᵀ *ᵥ xExt) ⬝ᵥ (Matrix.diagonal hM.eigenvalues *ᵥ y) := by
              rw [dotProduct_mulVec]
              conv_lhs => arg 1; rw [← Matrix.transpose_transpose U, Matrix.vecMul_transpose]
    rw [h1]
    simp only [dotProduct, Matrix.mulVec_diagonal]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hquad_sum] at hquad0
  have hterm0 : ∀ k ∈ (Finset.univ : Finset (Fin n)), hM.eigenvalues k * y k ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
      mul_nonneg (heig_nonneg k) (sq_nonneg (y k))).mp hquad0
  have hdiag_y : Matrix.diagonal hM.eigenvalues *ᵥ y = 0 := by
    ext k
    simp only [Matrix.mulVec_diagonal, Pi.zero_apply]
    rcases mul_eq_zero.mp (hterm0 k (Finset.mem_univ k)) with hlam | hy2
    · simp [hlam]
    · simp [sq_eq_zero_iff.mp hy2]
  have hM_zero : M *ᵥ xExt = 0 := by
    conv_lhs => rw [hspec]
    simp only [Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
    change U *ᵥ (Matrix.diagonal hM.eigenvalues *ᵥ y) = 0
    rw [hdiag_y, Matrix.mulVec_zero]
  refine ⟨xExt, hxExt_f, hxExt_out, hM_zero, fun j => ?_⟩
  rw [← hMxExt j, hM_zero, Pi.zero_apply]

/-- **Kernel support dimension counting (`Proposition 6.1`):**
For any matrix `A : Matrix (Fin n) (Fin n) ℝ`, scalar `μ : ℝ`, and `m`-subset embedding
`f : Fin m ↪ Fin n`, if `m < dim ker(A - μ I)`, then there exists a nonzero `μ`-eigenvector of
`A` supported entirely outside the range of `f`. -/
theorem ker_submatrix_vanish_of_nullity_gt {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ)
    (f : Fin m ↪ Fin n)
    (hlt : m < Module.finrank ℝ (LinearMap.ker (A - μ • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVecLin)) :
    ∃ v : Fin n → ℝ, v ≠ 0 ∧ A *ᵥ v = μ • v ∧ ∀ a : Fin m, v (f a) = 0 := by
  let L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := (A - μ • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVecLin
  let E : Submodule ℝ (Fin n → ℝ) := LinearMap.ker L
  let res : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    { toFun := fun v a => v (f a)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let resE : E →ₗ[ℝ] (Fin m → ℝ) := res.comp E.subtype
  have hrn := LinearMap.finrank_range_add_finrank_ker resE
  have hrange_le : Module.finrank ℝ (LinearMap.range resE) ≤ m := by
    calc
      Module.finrank ℝ (LinearMap.range resE) ≤ Module.finrank ℝ (Fin m → ℝ) :=
        Submodule.finrank_le (LinearMap.range resE)
      _ = m := by simp
  have hE_eq : Module.finrank ℝ E =
      Module.finrank ℝ (LinearMap.ker (A - μ • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVecLin) := rfl
  have hker_pos : 0 < Module.finrank ℝ (LinearMap.ker resE) := by omega
  have hker_ne : LinearMap.ker resE ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hker_pos
    omega
  obtain ⟨w, hw_ker, hw_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
  refine ⟨(w : Fin n → ℝ), ?_, ?_, ?_⟩
  · intro hv0
    apply hw_ne
    exact Subtype.ext hv0
  · have hwE : L (w : Fin n → ℝ) = 0 := LinearMap.mem_ker.mp w.2
    have hmul : (A - μ • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ (w : Fin n → ℝ) = 0 := hwE
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hmul
    exact hmul
  · intro a
    have hw_res : resE w = 0 := LinearMap.mem_ker.mp hw_ker
    exact congrFun hw_res a

end JacobiAndKernel

end EquiangularLines
