module

public import EquiangularLines.GaloisObstructions

/-!
# Phase 3 Algebraic Obstructions & De Caen–Jacobi Resolvent

This module formalizes the four Phase 3 algebraic results requested for `(19, 74)` and `(18, 59)`:

1. **Shared Block-Commutator Spectral Reduction (`block_commutator_sim_eig`,
   `symm_block_quadratic_eigenvalues`):**
   Given a real block-symmetric matrix `M = fromBlocks A B Bᵀ C` satisfying `A * B + B * C = c • B`,
   `C` commutes with `Bᵀ * B`, every eigenspace `ker(Bᵀ * B - σ² I)` admits a simultaneous
   orthonormal eigenbasis for `C` and `Bᵀ * B`, and every nonzero common eigenvector `(σ², μ)`
   with `σ² > 0` produces nonzero eigenvalues `α, β` of `M` satisfying `α + β = c` and
   `α * β = (c - μ) * μ - σ²`.

2. **Commutator / Block-Trace Kills (`idx47_eliminated`, `idx861_eliminated`):**
   - `idx47_eliminated` for `(19, 74) idx=47`: proves `False` via commutator reduction
     (`σ² = 75 + 10λ - λ²` on positive singular modes of `B`), rational projector `P_K` onto
     `ker(Bᵀ B) ∩ {1}⊥` with irrationality of `√5` forcing `Tr(P_K (75I + 10X - X²)) ≥ 0`,
     and Frobenius contradiction `928 = Tr(Bᵀ B) ≤ 896`.
   - `idx861_eliminated` for `(18, 59) idx=861`: proves `False` via `X * Y + Y * Z = 8 • Y`, showing
     every positive singular value of `Y` satisfies `σ² ≤ 81` and induces an orthogonal
     `13`-eigenvector of `S_{u₁}`, forcing `rank(Y) ≤ 8` and `840 = ‖Y‖_F² ≤ 8 * 81 = 648`.

3. **De Caen–Jacobi Resolvent Identity (`jacobi_k_complementary_minor`,
   `idx13_resolvent_identity`, `idx13_pole_cancellation_at_15`):**
   Proves the general `k`-minor Jacobi identity over `[CommRing R]`, the exact cleared-denominator
   polynomial matrix identity `(x I - S) * M(x, S) = m(x) • 1` for `(19, 74) idx=13`
   (`m(x) = (x+5)(x-11)(x-15)(x-17)`), `M(15, S) = (S + 5I)(S - 11I)(S - 17I)`, and exact pole
   cancellation `(X - C 15)^(k - 15) ∣ det(M(X, S)[V, V])` for `k ≥ 15`.

4. **Surgical `(18, 59) idx=488` Rank Obstruction (`disjoint_eigenvectors_rank_ge`,
   `idx488_rank_obstruction`):**
   Proves rank lower bounds for linearly independent nonzero eigenvectors and eliminates any
   rank-`≤ 7` symmetric idempotent `E` with the `idx=488` block structure (`20` vertices with
   diagonal `1/8`, `|E[B, C₅]| = 1/16`, `E[B, out] = 0`) via `50/8 ≤ 35/8`.
-/

@[expose] public section

open Matrix Polynomial
open scoped BigOperators InnerProductSpace

namespace EquiangularLines

section BlockCommutator

private def toEucl {n : ℕ} (x : Fin n → ℝ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 x

private lemma eucl_inner_eq_dot {n : ℕ} (x y : Fin n → ℝ) :
    ⟪toEucl x, toEucl y⟫_ℝ = x ⬝ᵥ y := by
  rw [toEucl, toEucl, EuclideanSpace.inner_toLp_toLp]
  simp [dotProduct, mul_comm]

private lemma eucl_inner_eq_dot' {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) :
    ⟪u, v⟫_ℝ = u.ofLp ⬝ᵥ v.ofLp := by
  simpa [toEucl] using eucl_inner_eq_dot u.ofLp v.ofLp

private lemma hermitian_transpose_eq {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.IsHermitian) : Mᵀ = M := by
  ext i j
  simpa [Matrix.transpose_apply] using hM.apply i j

private lemma isHermitian_of_transpose_eq {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : Mᵀ = M) : M.IsHermitian := by
  ext i j
  simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hM i) j

private lemma dot_self_eq_zero_iff {n : ℕ} (x : Fin n → ℝ) :
    x ⬝ᵥ x = 0 ↔ x = 0 := by
  constructor
  · intro h
    ext i
    have hnn : ∀ j : Fin n, 0 ≤ x j * x j := fun j => mul_self_nonneg _
    exact mul_self_eq_zero.mp
      ((Finset.sum_eq_zero_iff_of_nonneg fun j _ => hnn j).mp h i (Finset.mem_univ i))
  · rintro rfl
    simp

private lemma dot_self_pos_of_ne_zero {n : ℕ} {x : Fin n → ℝ} (hx : x ≠ 0) :
    0 < x ⬝ᵥ x := by
  have hnn : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  exact lt_of_le_of_ne hnn fun h => hx ((dot_self_eq_zero_iff x).mp h.symm)

private lemma symm_sq_mulVec_zero {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : Mᵀ = M) {w : Fin n → ℝ} (h2 : (M * M) *ᵥ w = 0) : M *ᵥ w = 0 := by
  have hnorm : (M *ᵥ w) ⬝ᵥ (M *ᵥ w) = 0 := by
    calc
      (M *ᵥ w) ⬝ᵥ (M *ᵥ w) = ((M *ᵥ w) ᵥ* M) ⬝ᵥ w := dotProduct_mulVec _ _ _
      _ = (Mᵀ *ᵥ (M *ᵥ w)) ⬝ᵥ w := by rw [← Matrix.mulVec_transpose]
      _ = ((M * M) *ᵥ w) ⬝ᵥ w := by rw [hM, Matrix.mulVec_mulVec]
      _ = 0 := by rw [h2, zero_dotProduct]
  exact (dot_self_eq_zero_iff (M *ᵥ w)).mp hnorm

private lemma symm_pow_two_mulVec_zero {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : Mᵀ = M) : ∀ (m : ℕ) {w : Fin n → ℝ}, (M ^ (2 ^ m)) *ᵥ w = 0 → M *ᵥ w = 0
  | 0, w, hw => by simpa using hw
  | m + 1, w, hw => by
    have hMt : (M ^ (2 ^ m))ᵀ = M ^ (2 ^ m) := by rw [Matrix.transpose_pow, hM]
    have hsq : ((M ^ (2 ^ m)) * (M ^ (2 ^ m))) *ᵥ w = 0 := by
      rwa [← pow_add, ← mul_two, ← pow_succ]
    have hm := symm_sq_mulVec_zero hMt hsq
    exact symm_pow_two_mulVec_zero hM m hm

private lemma symm_pow_mulVec_zero {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : Mᵀ = M) {k : ℕ} (_hk : 1 ≤ k) {w : Fin n → ℝ}
    (hw : (M ^ k) *ᵥ w = 0) : M *ᵥ w = 0 := by
  have hle : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
  have hpow : (M ^ (2 ^ k)) *ᵥ w = 0 := by
    have hsplit : 2 ^ k = (2 ^ k - k) + k := (Nat.sub_add_cancel hle).symm
    rw [hsplit, pow_add, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]
  exact symm_pow_two_mulVec_zero hM k hpow

private lemma vec_fromBlocks_mulVec {n1 n2 : ℕ}
    (A : Matrix (Fin n1) (Fin n1) ℝ) (B : Matrix (Fin n1) (Fin n2) ℝ)
    (C : Matrix (Fin n2) (Fin n2) ℝ) (u : Fin n1 → ℝ) (v : Fin n2 → ℝ) :
    Matrix.fromBlocks A B Bᵀ C *ᵥ Sum.elim u v =
      Sum.elim (A *ᵥ u + B *ᵥ v) (Bᵀ *ᵥ u + C *ᵥ v) := by
  ext x
  cases x with
  | inl i =>
    simp [Matrix.mulVec, dotProduct, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Fintype.sum_sum_type, Pi.add_apply]
  | inr j =>
    simp [Matrix.mulVec, dotProduct, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Fintype.sum_sum_type, Pi.add_apply]

private lemma mulVec_is_eig_root_charpoly {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    {v : Fin n → ℝ} (hv : v ≠ 0) {r : ℝ} (hMv : M *ᵥ v = r • v) :
    M.charpoly.eval r = 0 := by
  have hker : (r • (1 : Matrix (Fin n) (Fin n) ℝ) - M) *ᵥ v = 0 := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hMv, sub_self]
  have hdet0 : (r • (1 : Matrix (Fin n) (Fin n) ℝ) - M).det = 0 := by
    by_contra hne
    exact hv (Matrix.eq_zero_of_mulVec_eq_zero hne hker)
  have hcharm_eval :
      (Polynomial.evalRingHom r).mapMatrix (Matrix.charmatrix M) =
        r • (1 : Matrix (Fin n) (Fin n) ℝ) - M := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.charmatrix, hij]
  rw [Matrix.charpoly, ← hdet0, ← hcharm_eval]
  exact RingHom.map_det (Polynomial.evalRingHom r) M.charmatrix

private lemma trace_eq_sum_onb_dot {n : ℕ} {U : Matrix (Fin n) (Fin n) ℝ}
    (hUU : U * Uᵀ = 1) (C : Matrix (Fin n) (Fin n) ℝ) :
    C.trace = ∑ k : Fin n, (fun i => U i k) ⬝ᵥ (C *ᵥ fun i => U i k) := by
  simp only [dotProduct, Matrix.mulVec]
  calc
    C.trace = ∑ i : Fin n, C i i := rfl
    _ = ∑ i : Fin n, ∑ j : Fin n, C i j * (U * Uᵀ) i j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hUU]
        simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
          Finset.mem_univ, ↓reduceIte]
    _ = ∑ i : Fin n, ∑ j : Fin n, C i j * ∑ k : Fin n, U i k * U j k := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp [Matrix.mul_apply, Matrix.transpose_apply]
    _ = ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n, C i j * (U i k * U j k) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp_rw [Finset.mul_sum]
        exact Finset.sum_comm
    _ = ∑ k : Fin n, ∑ i : Fin n, U i k * ∑ j : Fin n, C i j * U j k := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring

private lemma commutator_eq_of_block_relation {n1 n2 : ℕ}
    {A : Matrix (Fin n1) (Fin n1) ℝ} (hA : A.IsHermitian)
    {C : Matrix (Fin n2) (Fin n2) ℝ} (hC : C.IsHermitian)
    (B : Matrix (Fin n1) (Fin n2) ℝ) (c : ℝ)
    (hrel : A * B + B * C = c • B) :
    (Bᵀ * B) * C = C * (Bᵀ * B) := by
  have hA_sym : Aᵀ = A := hermitian_transpose_eq hA
  have hC_sym : Cᵀ = C := hermitian_transpose_eq hC
  have hBC : B * C = c • B - A * B := eq_sub_of_add_eq' hrel
  have h1 : (Bᵀ * B) * C = c • (Bᵀ * B) - Bᵀ * A * B := by
    calc
      (Bᵀ * B) * C = Bᵀ * (B * C) := Matrix.mul_assoc _ _ _
      _ = Bᵀ * (c • B - A * B) := by rw [hBC]
      _ = c • (Bᵀ * B) - Bᵀ * A * B := by
          rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_assoc]
  have h2 : ((Bᵀ * B) * C)ᵀ = (Bᵀ * B) * C := by
    rw [h1, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul,
      Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hA_sym,
      Matrix.mul_assoc]
  calc
    (Bᵀ * B) * C = ((Bᵀ * B) * C)ᵀ := h2.symm
    _ = Cᵀ * (Bᵀ * B)ᵀ := Matrix.transpose_mul _ _
    _ = C * (Bᵀ * B) := by
        rw [hC_sym, Matrix.transpose_mul, Matrix.transpose_transpose]

/-- Diagonalizes a symmetric matrix `C` on any `C`-invariant submodule `K_fun ⊆ (Fin n → ℝ)`,
returning an orthonormal eigenbasis `(e, μ)` of `K_fun` of cardinality `finrank ℝ K_fun`. -/
private lemma submodule_diag_symm {n : ℕ} (K_fun : Submodule ℝ (Fin n → ℝ))
    {C : Matrix (Fin n) (Fin n) ℝ} (hC : C.IsHermitian)
    (hC_pres : ∀ x ∈ K_fun, C *ᵥ x ∈ K_fun) :
    ∃ (d : ℕ) (e : Fin d → Fin n → ℝ) (μ : Fin d → ℝ),
      d = Module.finrank ℝ K_fun ∧
      (∀ r : Fin d, e r ∈ K_fun) ∧
      (∀ r : Fin d, C *ᵥ e r = μ r • e r) ∧
      (∀ r s : Fin d, e r ⬝ᵥ e s = if r = s then 1 else 0) ∧
      (∀ v ∈ K_fun, v = ∑ r : Fin d, (e r ⬝ᵥ v) • e r) := by
  classical
  have hC_sym : Cᵀ = C := hermitian_transpose_eq hC
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
    { carrier := {x | x.ofLp ∈ K_fun}
      zero_mem' := K_fun.zero_mem
      add_mem' := fun hx hy => K_fun.add_mem hx hy
      smul_mem' := @fun a _ hx => K_fun.smul_mem a hx }
  let toFunK : K →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun z => (z : EuclideanSpace ℝ (Fin n)).ofLp
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let eqvK : K ≃ₗ[ℝ] K_fun :=
    { toFun := fun x => ⟨toFunK x, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun x => ⟨toEucl x.1, x.2⟩
      left_inv := fun x => Subtype.ext (by rfl)
      right_inv := fun x => Subtype.ext (by rfl) }
  have hdim : Module.finrank ℝ K = Module.finrank ℝ K_fun := eqvK.finrank_eq
  let d : ℕ := Module.finrank ℝ K
  let b : OrthonormalBasis (Fin d) ℝ K := stdOrthonormalBasis ℝ K
  let MC : Matrix (Fin d) (Fin d) ℝ :=
    Matrix.of fun i j => toFunK (b i) ⬝ᵥ (C *ᵥ toFunK (b j))
  have hMC_herm : MC.IsHermitian := by
    apply isHermitian_of_transpose_eq
    ext i j
    simp only [MC, Matrix.transpose_apply, Matrix.of_apply]
    calc
      toFunK (b j) ⬝ᵥ (C *ᵥ toFunK (b i))
          = (toFunK (b j) ᵥ* C) ⬝ᵥ toFunK (b i) := dotProduct_mulVec _ _ _
      _ = (Cᵀ *ᵥ toFunK (b j)) ⬝ᵥ toFunK (b i) := by rw [← Matrix.mulVec_transpose]
      _ = (C *ᵥ toFunK (b j)) ⬝ᵥ toFunK (b i) := by rw [hC_sym]
      _ = toFunK (b i) ⬝ᵥ (C *ᵥ toFunK (b j)) := dotProduct_comm _ _
  let U : Matrix (Fin d) (Fin d) ℝ := (hMC_herm.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)
  have hU'U : Uᵀ * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self hMC_herm.eigenvectorUnitary
  have hUU : U * Uᵀ = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self hMC_herm.eigenvectorUnitary
  have hspec : MC = U * Matrix.diagonal hMC_herm.eigenvalues * Uᵀ := by
    simpa [U, Matrix.star_eq_conjTranspose, RCLike.ofReal_real_eq_id] using hMC_herm.spectral_theorem
  let eK : Fin d → K := fun r => ∑ i : Fin d, U i r • b i
  let e : Fin d → Fin n → ℝ := fun r => toFunK (eK r)
  have heK_norm : ∀ r s : Fin d, ⟪eK r, eK s⟫_ℝ = if r = s then 1 else 0 := by
    intro r s
    have hb_orth : ∀ i j : Fin d,
        ⟪(b i : EuclideanSpace ℝ (Fin n)), (b j : EuclideanSpace ℝ (Fin n))⟫_ℝ =
          if i = j then 1 else 0 := fun i j =>
      orthonormal_iff_ite.mp b.orthonormal i j
    let uMat : Fin d → Fin d → ℝ := fun i j => U i j
    have hstep1 : ⟪eK r, eK s⟫_ℝ =
        ∑ i : Fin d, ∑ j : Fin d, uMat i r * uMat j s * (if i = j then (1 : ℝ) else 0) := by
      have hcoe_r : (eK r : EuclideanSpace ℝ (Fin n)) =
          ∑ i : Fin d, uMat i r • (b i : EuclideanSpace ℝ (Fin n)) := by
        change K.subtype (∑ i : Fin d, U i r • b i) = _
        rw [map_sum]
        rfl
      have hcoe_s : (eK s : EuclideanSpace ℝ (Fin n)) =
          ∑ j : Fin d, uMat j s • (b j : EuclideanSpace ℝ (Fin n)) := by
        change K.subtype (∑ j : Fin d, U j s • b j) = _
        rw [map_sum]
        rfl
      change ⟪(eK r : EuclideanSpace ℝ (Fin n)), (eK s : EuclideanSpace ℝ (Fin n))⟫_ℝ = _
      rw [hcoe_r, hcoe_s, sum_inner]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_smul_left, inner_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [real_inner_smul_right, hb_orth, mul_assoc]
    rw [hstep1]
    have hsum : (∑ i : Fin d, ∑ j : Fin d, uMat i r * uMat j s * if i = j then (1 : ℝ) else 0) =
        ∑ i : Fin d, U i s * U i r := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single i
        (fun j _ hji => by
          rw [ite_eq_right_iff.mpr fun h => False.elim (hji h.symm), mul_zero])
        (fun hi => absurd (Finset.mem_univ i) hi)]
      simp only [↓reduceIte, mul_one]
      exact mul_comm _ _
    rw [hsum]
    have hdot : (∑ i : Fin d, U i s * U i r) = (Uᵀ * U) s r := by
      simp [Matrix.mul_apply, Matrix.transpose_apply]
    rw [hdot, hU'U, Matrix.one_apply]
    by_cases hrs : r = s <;> simp [hrs, eq_comm]
  have he_dot : ∀ r s : Fin d, e r ⬝ᵥ e s = if r = s then 1 else 0 := fun r s => by
    have h1 : e r ⬝ᵥ e s =
        ⟪(eK r : EuclideanSpace ℝ (Fin n)), (eK s : EuclideanSpace ℝ (Fin n))⟫_ℝ :=
      (eucl_inner_eq_dot' (eK r : EuclideanSpace ℝ (Fin n)) (eK s : EuclideanSpace ℝ (Fin n))).symm
    change e r ⬝ᵥ e s = _
    rw [h1]
    exact heK_norm r s
  have hC_repr_b : ∀ x : K,
      C *ᵥ toFunK x = ∑ i : Fin d, (toFunK (b i) ⬝ᵥ (C *ᵥ toFunK x)) • toFunK (b i) := by
    intro x
    let cx : K := ⟨toEucl (C *ᵥ toFunK x), hC_pres _ x.2⟩
    have hrep := b.sum_repr' cx
    have hval := congrArg toFunK hrep
    rw [map_sum] at hval
    have hval' : (∑ i : Fin d, (toFunK (b i) ⬝ᵥ (C *ᵥ toFunK x)) • toFunK (b i)) =
        C *ᵥ toFunK x := by
      convert hval using 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul]
        congr 1
        exact (eucl_inner_eq_dot' (b i : EuclideanSpace ℝ (Fin n)) (cx : EuclideanSpace ℝ (Fin n))).symm
      · rfl
    exact hval'.symm
  have he_C : ∀ r : Fin d, C *ᵥ e r = hMC_herm.eigenvalues r • e r := fun r => by
    have hCe := hC_repr_b (eK r)
    have he_exp : e r = ∑ j : Fin d, U j r • toFunK (b j) := by
      dsimp [e, eK]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => by rw [map_smul]
    have hcoef : ∀ i : Fin d,
        toFunK (b i) ⬝ᵥ (C *ᵥ e r) = (MC *ᵥ (fun j => U j r)) i := fun i => by
      rw [he_exp, Matrix.mulVec_sum, dotProduct_sum]
      simp_rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
      simp only [Matrix.mulVec, dotProduct, MC, Matrix.of_apply]
      refine Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hMC_eig : MC *ᵥ (fun j => U j r) = hMC_herm.eigenvalues r • (fun j => U j r) := by
      have hv : (fun j => U j r) = U *ᵥ Pi.single r 1 := by
        ext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [hv]
      conv_lhs => rw [hspec]
      calc
        (U * Matrix.diagonal hMC_herm.eigenvalues * Uᵀ) *ᵥ (U *ᵥ Pi.single r 1)
            = U *ᵥ (Matrix.diagonal hMC_herm.eigenvalues *ᵥ ((Uᵀ * U) *ᵥ Pi.single r 1)) := by
              simp only [Matrix.mul_assoc, Matrix.mulVec_mulVec]
        _ = U *ᵥ (Matrix.diagonal hMC_herm.eigenvalues *ᵥ Pi.single r 1) := by
              rw [hU'U, Matrix.one_mulVec]
        _ = U *ᵥ (hMC_herm.eigenvalues r • Pi.single r 1) := by
              congr 1; ext j
              simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
              split_ifs with hjr <;> simp [hjr]
        _ = hMC_herm.eigenvalues r • (U *ᵥ Pi.single r 1) := Matrix.mulVec_smul _ _ _
    change C *ᵥ toFunK (eK r) = _
    rw [hCe]
    change ∑ i : Fin d, (toFunK (b i) ⬝ᵥ (C *ᵥ e r)) • toFunK (b i) = hMC_herm.eigenvalues r • e r
    simp_rw [hcoef, hMC_eig, Pi.smul_apply, smul_eq_mul]
    rw [he_exp, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul]
  have hspan : ∀ v ∈ K_fun, v = ∑ r : Fin d, (e r ⬝ᵥ v) • e r := fun v hv => by
    let vK : K := ⟨toEucl v, hv⟩
    have hrep := b.sum_repr' vK
    have hv_b : v = ∑ i : Fin d, (toFunK (b i) ⬝ᵥ v) • toFunK (b i) := by
      have hval := congrArg toFunK hrep
      rw [map_sum] at hval
      have hvK_eq : toFunK vK = v := rfl
      rw [hvK_eq] at hval
      conv_lhs => rw [← hval]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul]
      congr 1
      exact eucl_inner_eq_dot' (b i : EuclideanSpace ℝ (Fin n)) (vK : EuclideanSpace ℝ (Fin n))
    have he_exp : ∀ r : Fin d, e r = ∑ i : Fin d, U i r • toFunK (b i) := fun r => by
      dsimp [e, eK]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => by rw [map_smul]
    have hRHS : (∑ r : Fin d, (e r ⬝ᵥ v) • e r) =
        ∑ i : Fin d, (∑ r : Fin d, U i r * (∑ j : Fin d, U j r * (toFunK (b j) ⬝ᵥ v))) •
          toFunK (b i) := by
      have hdot_e : ∀ r : Fin d, e r ⬝ᵥ v = ∑ j : Fin d, U j r * (toFunK (b j) ⬝ᵥ v) := fun r => by
        rw [he_exp r, sum_dotProduct]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_dotProduct, smul_eq_mul]
      simp_rw [hdot_e, he_exp, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp_rw [← Finset.sum_smul, mul_comm _ (U i _)]
    rw [hRHS]
    conv_lhs => rw [hv_b]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    have hUU_eval : ∀ i : Fin d,
        (∑ r : Fin d, U i r * ∑ j : Fin d, U j r * (toFunK (b j) ⬝ᵥ v)) = toFunK (b i) ⬝ᵥ v := by
      intro i
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      have hrow : ∀ j : Fin d, (∑ r : Fin d, U i r * (U j r * (toFunK (b j) ⬝ᵥ v))) =
          (U * Uᵀ) i j * (toFunK (b j) ⬝ᵥ v) := fun j => by
        simp [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, mul_assoc]
      simp_rw [hrow, hUU]
      simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte]
    exact (hUU_eval i).symm
  exact ⟨d, e, hMC_herm.eigenvalues, hdim, fun r => (eK r).2, he_C, he_dot, hspan⟩

/-- **Shared Block-Commutator Simultaneous Diagonalization:**
Given `A * B + B * C = c • B` with `A, C` symmetric, every eigenspace `ker(Bᵀ * B - σsq • 1)`
admits an orthonormal eigenbasis `(e r, μ r)` simultaneously diagonalizing `Bᵀ * B` and `C`. -/
theorem block_commutator_sim_eig {n1 n2 : ℕ}
    {A : Matrix (Fin n1) (Fin n1) ℝ} (hA : A.IsHermitian)
    {C : Matrix (Fin n2) (Fin n2) ℝ} (hC : C.IsHermitian)
    (B : Matrix (Fin n1) (Fin n2) ℝ) (c : ℝ) (hrel : A * B + B * C = c • B)
    (σsq : ℝ) :
    ∃ (d : ℕ) (e : Fin d → Fin n2 → ℝ) (μ : Fin d → ℝ),
      d = Module.finrank ℝ (LinearMap.ker (Bᵀ * B - σsq • 1).mulVecLin) ∧
      (∀ r : Fin d, (Bᵀ * B) *ᵥ e r = σsq • e r) ∧
      (∀ r : Fin d, C *ᵥ e r = μ r • e r) ∧
      (∀ r s : Fin d, e r ⬝ᵥ e s = if r = s then 1 else 0) ∧
      (∀ v : Fin n2 → ℝ, (Bᵀ * B) *ᵥ v = σsq • v →
        v = ∑ r : Fin d, (e r ⬝ᵥ v) • e r) := by
  have hcomm := commutator_eq_of_block_relation hA hC B c hrel
  let K_ker := LinearMap.ker (Bᵀ * B - σsq • (1 : Matrix (Fin n2) (Fin n2) ℝ)).mulVecLin
  have hmem_iff : ∀ x : Fin n2 → ℝ, x ∈ K_ker ↔ (Bᵀ * B) *ᵥ x = σsq • x := fun x => by
    rw [LinearMap.mem_ker]
    change (Bᵀ * B - σsq • 1) *ᵥ x = 0 ↔ _
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]
  have hC_pres : ∀ x ∈ K_ker, C *ᵥ x ∈ K_ker := fun x hx => by
    rw [hmem_iff] at hx ⊢
    calc
      (Bᵀ * B) *ᵥ (C *ᵥ x) = ((Bᵀ * B) * C) *ᵥ x := Matrix.mulVec_mulVec _ _ _
      _ = (C * (Bᵀ * B)) *ᵥ x := by rw [hcomm]
      _ = C *ᵥ ((Bᵀ * B) *ᵥ x) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = C *ᵥ (σsq • x) := by rw [hx]
      _ = σsq • (C *ᵥ x) := Matrix.mulVec_smul _ _ _
  obtain ⟨d, e, μ, hdim, heK, heC, hedot, hspan⟩ := submodule_diag_symm K_ker hC hC_pres
  exact ⟨d, e, μ, hdim, fun r => (hmem_iff (e r)).mp (heK r), heC, hedot,
    fun v hv => hspan v ((hmem_iff v).mpr hv)⟩

/-- **Shared 2D Block-Eigenvector Quadratic Theorem:**
If `A * B + B * C = c • B` and `e ≠ 0` satisfies `(Bᵀ * B) *ᵥ e = σsq • e` (`σsq > 0`) and
`C *ᵥ e = μ • e`, then `fromBlocks A B Bᵀ C` has two eigenvalues `α > β` with `α + β = c` and
`α * β = (c - μ) * μ - σsq`, and `zα = Sum.elim (B *ᵥ e) ((α - (c - μ)) • e)` satisfies
orthogonality against modes orthogonal to `e`. -/
theorem symm_block_quadratic_eigenvalues {n1 n2 : ℕ}
    {A : Matrix (Fin n1) (Fin n1) ℝ} {B : Matrix (Fin n1) (Fin n2) ℝ}
    {C : Matrix (Fin n2) (Fin n2) ℝ} (c : ℝ) (hrel : A * B + B * C = c • B)
    {e : Fin n2 → ℝ} (he_ne : e ≠ 0) {σsq μ : ℝ} (hσ : 0 < σsq)
    (hBB : (Bᵀ * B) *ᵥ e = σsq • e) (hC : C *ᵥ e = μ • e) :
    ∃ α β : ℝ,
      α + β = c ∧ α * β = (c - μ) * μ - σsq ∧
      β < α ∧
      (Sum.elim (B *ᵥ e) ((α - (c - μ)) • e) ≠ 0 ∧
       Matrix.fromBlocks A B Bᵀ C *ᵥ Sum.elim (B *ᵥ e) ((α - (c - μ)) • e) =
         α • Sum.elim (B *ᵥ e) ((α - (c - μ)) • e)) ∧
      (∃ zβ : Fin n1 ⊕ Fin n2 → ℝ, zβ ≠ 0 ∧ Matrix.fromBlocks A B Bᵀ C *ᵥ zβ = β • zβ) := by
  let disc : ℝ := (c - 2 * μ) ^ 2 + 4 * σsq
  have hdisc_pos : 0 < disc := by positivity
  let sqD : ℝ := Real.sqrt disc
  have hsqD_pos : 0 < sqD := Real.sqrt_pos.mpr hdisc_pos
  have hsqD2 : sqD ^ 2 = disc := Real.sq_sqrt hdisc_pos.le
  let α : ℝ := (c + sqD) / 2
  let β : ℝ := (c - sqD) / 2
  have hsum : α + β = c := by dsimp [α, β]; ring
  have hprod : α * β = (c - μ) * μ - σsq := by
    dsimp [α, β]
    calc
      (c + sqD) / 2 * ((c - sqD) / 2) = (c ^ 2 - sqD ^ 2) / 4 := by ring
      _ = (c ^ 2 - ((c - 2 * μ) ^ 2 + 4 * σsq)) / 4 := by rw [hsqD2]
      _ = (c - μ) * μ - σsq := by ring
  have hlt : β < α := by dsimp [α, β]; linarith
  have hq : ∀ r : ℝ, r = α ∨ r = β → σsq + μ * (r - (c - μ)) = r * (r - (c - μ)) := fun r hr => by
    have hquad : r ^ 2 - c * r + ((c - μ) * μ - σsq) = 0 := by
      rcases hr with rfl | rfl
      · dsimp [α]; nlinarith [hsqD2]
      · dsimp [β]; nlinarith [hsqD2]
    linarith
  let u1 : Fin n1 → ℝ := B *ᵥ e
  have hu1_dot : u1 ⬝ᵥ u1 = σsq * (e ⬝ᵥ e) := by
    calc
      (B *ᵥ e) ⬝ᵥ (B *ᵥ e) = ((B *ᵥ e) ᵥ* B) ⬝ᵥ e := dotProduct_mulVec _ _ _
      _ = (Bᵀ *ᵥ (B *ᵥ e)) ⬝ᵥ e := by rw [← Matrix.mulVec_transpose]
      _ = ((Bᵀ * B) *ᵥ e) ⬝ᵥ e := by rw [Matrix.mulVec_mulVec]
      _ = (σsq • e) ⬝ᵥ e := by rw [hBB]
      _ = σsq * (e ⬝ᵥ e) := by rw [smul_dotProduct, smul_eq_mul]
  have hu1_ne : u1 ≠ 0 := by
    intro h0
    have he_pos : 0 < e ⬝ᵥ e := dot_self_pos_of_ne_zero he_ne
    have hprod_pos : 0 < σsq * (e ⬝ᵥ e) := mul_pos hσ he_pos
    rw [h0, dotProduct_zero] at hu1_dot
    linarith
  have hAu1 : A *ᵥ u1 = (c - μ) • u1 := by
    have hBC : A * B = c • B - B * C := eq_sub_of_add_eq hrel
    calc
      A *ᵥ (B *ᵥ e) = (A * B) *ᵥ e := Matrix.mulVec_mulVec _ _ _
      _ = (c • B - B * C) *ᵥ e := by rw [hBC]
      _ = c • (B *ᵥ e) - B *ᵥ (C *ᵥ e) := by
          rw [Matrix.sub_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
      _ = c • u1 - μ • u1 := by rw [hC, Matrix.mulVec_smul]
      _ = (c - μ) • u1 := by rw [sub_smul]
  have hz_eig : ∀ r : ℝ, r = α ∨ r = β →
      let zr := Sum.elim u1 ((r - (c - μ)) • e)
      zr ≠ 0 ∧ Matrix.fromBlocks A B Bᵀ C *ᵥ zr = r • zr := by
    intro r hr zr
    refine ⟨?_, ?_⟩
    · intro h0
      apply hu1_ne
      ext i
      simpa [zr] using congrFun h0 (Sum.inl i)
    · dsimp [zr]
      rw [vec_fromBlocks_mulVec, hAu1, Matrix.mulVec_smul, Matrix.mulVec_smul, hC, smul_smul]
      have hB'u1 : Bᵀ *ᵥ u1 = σsq • e := by
        calc
          Bᵀ *ᵥ (B *ᵥ e) = (Bᵀ * B) *ᵥ e := Matrix.mulVec_mulVec _ _ _
          _ = σsq • e := hBB
      rw [hB'u1]
      ext x
      cases x with
      | inl i =>
        simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, u1]
        ring
      | inr j =>
        simp only [Sum.elim_inr, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        calc
          σsq * e j + (r - (c - μ)) * μ * e j
              = (σsq + μ * (r - (c - μ))) * e j := by ring
          _ = r * ((r - (c - μ)) * e j) := by rw [hq r hr]; ring
  exact ⟨α, β, hsum, hprod, hlt, hz_eig α (Or.inl rfl), _, hz_eig β (Or.inr rfl)⟩

end BlockCommutator

section Kills47And861

private lemma nat_sq_eq_five_mul_sq {a b : ℕ} (h : a ^ 2 = 5 * b ^ 2) : a = 0 ∧ b = 0 := by
  induction a using Nat.strong_induction_on generalizing b with
  | ind a ih =>
    by_cases ha : a = 0
    · subst ha
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_eq_mul,
        OfNat.ofNat_ne_zero, pow_eq_zero_iff, false_or] at h
      exact ⟨rfl, h⟩
    · have hdvd_a : 5 ∣ a := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 5) ⟨b ^ 2, h⟩
      rcases hdvd_a with ⟨k, rfl⟩
      have h1 : 5 * k ^ 2 = b ^ 2 := by nlinarith
      have hdvd_b : 5 ∣ b := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 5) ⟨k ^ 2, h1.symm⟩
      rcases hdvd_b with ⟨m, rfl⟩
      have h2 : k ^ 2 = 5 * m ^ 2 := by nlinarith
      have hk_lt : k < 5 * k := by omega
      obtain ⟨hk0, hm0⟩ := ih k hk_lt h2
      omega

private lemma rat_add_mul_sqrt_five_eq_zero {p q : ℚ}
    (h : (p : ℝ) + (q : ℝ) * Real.sqrt 5 = 0) : p = 0 ∧ q = 0 := by
  by_cases hq : q = 0
  · subst hq
    simp only [Rat.cast_zero, zero_mul, add_zero, Rat.cast_eq_zero] at h
    exact ⟨h, rfl⟩
  · exfalso
    have hsq : ((-p / q : ℚ) : ℝ) = Real.sqrt 5 := by
      push_cast
      have hqR : (q : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr hq
      field_simp [hqR]
      linarith
    have hsq2 : ((-p / q) ^ 2 : ℚ) = 5 := by
      have hR : (((-p / q) ^ 2 : ℚ) : ℝ) = (5 : ℝ) := by
        have h1 : (((-p / q) ^ 2 : ℚ) : ℝ) = (((-p / q : ℚ) : ℝ) ^ 2) := by push_cast; rfl
        rw [h1, hsq]
        norm_num
      exact_mod_cast hR
    let r := -p / q
    have hr2 : r ^ 2 = 5 := hsq2
    have hnum : (r.num.natAbs) ^ 2 = 5 * r.den ^ 2 := by
      have hq_eq : (r.num : ℚ) ^ 2 = 5 * (r.den : ℚ) ^ 2 := by
        have hden : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr r.den_nz
        have hrat : (r.num : ℚ) / (r.den : ℚ) = r := Rat.num_div_den r
        rw [← hrat, div_pow] at hr2
        field_simp [hden] at hr2
        linarith
      have hZ : r.num ^ 2 = 5 * (r.den : ℤ) ^ 2 := by exact_mod_cast hq_eq
      zify
      simpa [sq_abs] using congrArg abs hZ
    obtain ⟨_, hd0⟩ := nat_sq_eq_five_mul_sq hnum
    exact r.den_nz hd0

private lemma idx47_pair_unique {α β : ℝ} (hsum : α + β = 10)
    (hα : α = 15 ∨ α = 11 ∨ α = -5 ∨ α ^ 2 - 28 * α + 191 = 0)
    (hβ : β = 15 ∨ β = 11 ∨ β = -5 ∨ β ^ 2 - 28 * β + 191 = 0) :
    (α = 15 ∧ β = -5) ∨ (α = -5 ∧ β = 15) := by
  rcases hα with rfl | rfl | rfl | hαq
  · rcases hβ with rfl | rfl | rfl | hβq
    · linarith
    · linarith
    · exact Or.inl ⟨rfl, rfl⟩
    · have : β = -5 := by linarith
      rw [this] at hβq; norm_num at hβq
  · rcases hβ with rfl | rfl | rfl | hβq
    · linarith
    · linarith
    · linarith
    · have : β = -1 := by linarith
      rw [this] at hβq; norm_num at hβq
  · rcases hβ with rfl | rfl | rfl | hβq
    · exact Or.inr ⟨rfl, rfl⟩
    · linarith
    · linarith
    · have : β = 15 := by linarith
      rw [this] at hβq; norm_num at hβq
  · rcases hβ with rfl | rfl | rfl | hβq
    · have : α = -5 := by linarith
      rw [this] at hαq; norm_num at hαq
    · have : α = -1 := by linarith
      rw [this] at hαq; norm_num at hαq
    · have : α = 15 := by linarith
      rw [this] at hαq; norm_num at hαq
    · have hsub : (α - β) * (α + β - 28) = 0 := by linarith
      rw [hsum] at hsub
      have hab : α = β := by
        rcases mul_eq_zero.mp hsub with h | h
        · linarith
        · norm_num at h
      have h5 : α = 5 := by linarith
      rw [h5] at hαq
      norm_num at hαq

private lemma idx861_pair_unique {α β : ℝ} (hsum : α + β = 8)
    (hα : α = 13 ∨ α = 11 ∨ α = 9 ∨ α = 5 ∨ α = -5)
    (hβ : β = 13 ∨ β = 11 ∨ β = 9 ∨ β = 5 ∨ β = -5) :
    (α = 13 ∧ β = -5) ∨ (α = -5 ∧ β = 13) := by
  rcases hα with rfl | rfl | rfl | rfl | rfl <;>
    rcases hβ with rfl | rfl | rfl | rfl | rfl <;>
    first | linarith | (exact Or.inl ⟨rfl, rfl⟩) | (exact Or.inr ⟨rfl, rfl⟩)

private lemma eval_perm_submatrix_charpoly {n1 n2 : ℕ}
    (S : Matrix (Fin (n1 + n2)) (Fin (n1 + n2)) ℝ)
    (e : Fin n1 ⊕ Fin n2 ≃ Fin (n1 + n2))
    (z : Fin n1 ⊕ Fin n2 → ℝ) (hz : z ≠ 0) (r : ℝ)
    (hz_eig : S.submatrix e e *ᵥ z = r • z) :
    S.charpoly.eval r = 0 := by
  let w : Fin (n1 + n2) → ℝ := z ∘ e.symm
  have hw : w ≠ 0 := by
    intro h0
    apply hz
    ext x
    have := congrFun h0 (e x)
    simpa [w] using this
  have hSw : S *ᵥ w = r • w := by
    ext i
    have h1 := congrFun hz_eig (e.symm i)
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    dsimp [w]
    rw [← h1, ← e.sum_comp (fun j => S i j * z (e.symm j))]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp
  exact mulVec_is_eig_root_charpoly hw hSw

private lemma aeval_ker_mulVec {n : ℕ} (A0 : Matrix (Fin n) (Fin n) ℝ)
    (p : ℚ[X]) {v : Fin n → ℝ} (hv : A0 *ᵥ v = 0) :
    Polynomial.aeval A0 (p.map (algebraMap ℚ ℝ)) *ᵥ v = ((p.eval 0 : ℚ) : ℝ) • v := by
  induction p using Polynomial.induction_on' with
  | add p1 p2 ih1 ih2 =>
    simp only [Polynomial.map_add, map_add, Matrix.add_mulVec, Polynomial.eval_add,
      Rat.cast_add, add_smul, ih1, ih2]
  | monomial d c =>
    cases d with
    | zero =>
      simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
    | succ k =>
      have hpow : (A0 ^ (k + 1)) *ᵥ v = 0 := by
        rw [pow_succ, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
      simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, hpow]

private lemma aeval_symm_of_symm {n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin n) (Fin n) R) (hA : Aᵀ = A) (p : R[X]) :
    (Polynomial.aeval A p)ᵀ = Polynomial.aeval A p := by
  induction p using Polynomial.induction_on' with
  | add p1 p2 ih1 ih2 =>
    simp only [map_add, Matrix.transpose_add, ih1, ih2]
  | monomial d c =>
    simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
      Matrix.one_mul, Matrix.transpose_smul, Matrix.transpose_pow, hA]

private lemma trace_proj_basis_eq {n d : ℕ} (U : Matrix (Fin n) (Fin n) ℝ)
    (hUU : U * Uᵀ = 1) (hU'U : Uᵀ * U = 1) (P : Fin n → Prop) [DecidablePred P]
    (e : Fin d → Fin n → ℝ)
    (he_orth : ∀ r s : Fin d, e r ⬝ᵥ e s = if r = s then 1 else 0)
    (hspan_u : ∀ k : Fin n, P k → (fun i => U i k) = ∑ r : Fin d, (e r ⬝ᵥ fun i => U i k) • e r)
    (hspan_e : ∀ r : Fin d, ∀ k : Fin n, ¬ P k → (fun i => U i k) ⬝ᵥ e r = 0)
    (R : Matrix (Fin n) (Fin n) ℝ) :
    (∑ k ∈ Finset.univ.filter P, (fun i => U i k) ⬝ᵥ (R *ᵥ fun i => U i k)) =
      ∑ r : Fin d, e r ⬝ᵥ (R *ᵥ e r) := by
  let u : Fin n → Fin n → ℝ := fun k i => U i k
  have hu_dot : ∀ k1 k2 : Fin n, u k1 ⬝ᵥ u k2 = if k1 = k2 then 1 else 0 := fun k1 k2 => by
    have hdot : u k1 ⬝ᵥ u k2 = (Uᵀ * U) k1 k2 := by
      simp [u, Matrix.mul_apply, Matrix.transpose_apply, dotProduct]
    rw [hdot, hU'U, Matrix.one_apply]
  have he_in_U : ∀ r : Fin d, e r = ∑ k ∈ Finset.univ.filter P, (u k ⬝ᵥ e r) • u k := fun r => by
    have hfull : e r = ∑ k : Fin n, (u k ⬝ᵥ e r) • u k := by
      ext i
      calc
        e r i = ∑ j : Fin n, (U * Uᵀ) i j * e r j := by
            rw [hUU]
            simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
              Finset.mem_univ, ↓reduceIte]
        _ = ∑ j : Fin n, (∑ k : Fin n, U i k * U j k) * e r j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            simp [Matrix.mul_apply, Matrix.transpose_apply]
        _ = ∑ k : Fin n, (u k ⬝ᵥ e r) * u k i := by
            simp_rw [Finset.sum_mul, mul_assoc]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun k _ => ?_
            simp [u, dotProduct, Finset.mul_sum, mul_comm]
        _ = (∑ k : Fin n, (u k ⬝ᵥ e r) • u k) i := by simp
    conv_lhs => rw [hfull]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ P (fun k => (u k ⬝ᵥ e r) • u k)]
    have hzero : (∑ k ∈ Finset.univ.filter (fun k => ¬ P k), (u k ⬝ᵥ e r) • u k) = 0 :=
      Finset.sum_eq_zero fun k hk => by
        rw [hspan_e r k (Finset.mem_filter.mp hk).2, zero_smul]
    rw [hzero, add_zero]
  have hL : (∑ k ∈ Finset.univ.filter P, u k ⬝ᵥ (R *ᵥ u k)) =
      ∑ k ∈ Finset.univ.filter P, ∑ r : Fin d, ∑ s : Fin d,
        (e r ⬝ᵥ u k) * (e s ⬝ᵥ u k) * (e r ⬝ᵥ (R *ᵥ e s)) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkP : P k := (Finset.mem_filter.mp hk).2
    have hsp : u k = ∑ r : Fin d, (e r ⬝ᵥ u k) • e r := hspan_u k hkP
    conv_lhs => rw [hsp]
    rw [sum_dotProduct, Matrix.mulVec_sum]
    simp_rw [smul_dotProduct, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul,
      smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    ring
  have hparseval : ∀ r s : Fin d,
      (∑ k ∈ Finset.univ.filter P, (e r ⬝ᵥ u k) * (e s ⬝ᵥ u k)) = if r = s then 1 else 0 := fun r s => by
    have hdot_rs : e r ⬝ᵥ e s =
        ∑ k ∈ Finset.univ.filter P, (e r ⬝ᵥ u k) * (e s ⬝ᵥ u k) := by
      conv_lhs => rw [he_in_U r, he_in_U s]
      rw [sum_dotProduct]
      simp_rw [smul_dotProduct, dotProduct_sum, dotProduct_smul, smul_eq_mul, hu_dot,
        mul_ite, mul_one, mul_zero]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_in : k ∈ Finset.univ.filter P := hk
      simp only [Finset.sum_ite_eq, hk_in, ↓reduceIte]
      rw [dotProduct_comm (u k) (e r), dotProduct_comm (u k) (e s)]
    rw [← hdot_rs, he_orth r s]
  rw [hL, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_comm]
  have hinner : (∑ s : Fin d, ∑ k ∈ Finset.univ.filter P,
      (e r ⬝ᵥ u k) * (e s ⬝ᵥ u k) * (e r ⬝ᵥ (R *ᵥ e s))) =
      ∑ s : Fin d, (if r = s then 1 else 0) * (e r ⬝ᵥ (R *ᵥ e s)) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_mul, hparseval r s]
  rw [hinner]
  simp

private lemma map_int_X_sub (k : ℤ) (r : ℝ) (hr : (k : ℝ) = r) :
    (X - C k).map (Int.castRingHom ℝ) = X - C r := by
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  exact congrArg (X - C ·) hr

private lemma map_int_X_add (k : ℤ) (r : ℝ) (hr : (k : ℝ) = r) :
    (X + C k).map (Int.castRingHom ℝ) = X + C r := by
  rw [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
  exact congrArg (X + C ·) hr

private lemma map_int_X_quad (b c : ℤ) (br cr : ℝ) (hb : (b : ℝ) = br) (hc : (c : ℝ) = cr) :
    (X ^ 2 - C b * X + C c).map (Int.castRingHom ℝ) = X ^ 2 - C br * X + C cr := by
  rw [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul,
    Polynomial.map_X, Polynomial.map_C, Polynomial.map_C]
  rw [show (Int.castRingHom ℝ b) = br from hb, show (Int.castRingHom ℝ c) = cr from hc]

private lemma map_int_X_sub_rat (k : ℤ) (r : ℚ) (hr : (k : ℚ) = r) :
    (X - C k).map (Int.castRingHom ℚ) = X - C r := by
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  exact congrArg (X - C ·) hr

private lemma map_int_X_add_rat (k : ℤ) (r : ℚ) (hr : (k : ℚ) = r) :
    (X + C k).map (Int.castRingHom ℚ) = X + C r := by
  rw [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
  exact congrArg (X + C ·) hr

private lemma block_eig_pair_roots {n1 n2 : ℕ}
    {Sℝ : Matrix (Fin (n1 + n2)) (Fin (n1 + n2)) ℝ}
    {A : Matrix (Fin n1) (Fin n1) ℝ} {B : Matrix (Fin n1) (Fin n2) ℝ}
    {C : Matrix (Fin n2) (Fin n2) ℝ} (e : Fin n1 ⊕ Fin n2 ≃ Fin (n1 + n2))
    (hPerm : Sℝ.submatrix e e = Matrix.fromBlocks A B Bᵀ C)
    (c : ℝ) (hrel : A * B + B * C = c • B)
    {v : Fin n2 → ℝ} (hv_ne : v ≠ 0) {σsq μ : ℝ} (hσ : 0 < σsq)
    (hBB : (Bᵀ * B) *ᵥ v = σsq • v) (hC : C *ᵥ v = μ • v) :
    ∃ α β : ℝ,
      α + β = c ∧ α * β = (c - μ) * μ - σsq ∧ β < α ∧
      Sℝ.charpoly.eval α = 0 ∧ Sℝ.charpoly.eval β = 0 ∧
      Sum.elim (B *ᵥ v) ((α - (c - μ)) • v) ≠ 0 ∧
      Sℝ.submatrix e e *ᵥ Sum.elim (B *ᵥ v) ((α - (c - μ)) • v) =
        α • Sum.elim (B *ᵥ v) ((α - (c - μ)) • v) := by
  obtain ⟨α, β, hsum, hprod, hlt, ⟨hzα_ne, hzα_eig⟩, ⟨zβ, hzβ_ne, hzβ_eig⟩⟩ :=
    symm_block_quadratic_eigenvalues c hrel hv_ne hσ hBB hC
  rw [← hPerm] at hzα_eig hzβ_eig
  exact ⟨α, β, hsum, hprod, hlt,
    eval_perm_submatrix_charpoly Sℝ e _ hzα_ne α hzα_eig,
    eval_perm_submatrix_charpoly Sℝ e zβ hzβ_ne β hzβ_eig,
    hzα_ne, hzα_eig⟩

private lemma idx47_mult11_le_one {Sℝ : Matrix (Fin 74) (Fin 74) ℝ}
    (hSℝ_herm : Sℝ.IsHermitian)
    (hchiR : Sℝ.charpoly =
      (X - C (15 : ℝ)) ^ 12 * (X - C (11 : ℝ)) * (X + C (5 : ℝ)) ^ 55 *
        (X ^ 2 - C (28 : ℝ) * X + C (191 : ℝ)) ^ 3) :
    Module.finrank ℝ (LinearMap.ker (Sℝ - (11 : ℝ) • 1).mulVecLin) ≤ 1 := by
  rw [submatrix_eigenvalue_count_eq_finrank_ker hSℝ_herm 11]
  have hch : Sℝ.charpoly = ∏ k : Fin 74, (X - C (hSℝ_herm.eigenvalues k)) := by
    simpa [RCLike.ofReal_real_eq_id] using hSℝ_herm.charpoly_eq
  have hdvd : (X - C (11 : ℝ)) ^ (Finset.univ.filter fun k : Fin 74 => hSℝ_herm.eigenvalues k = 11).card ∣
      Sℝ.charpoly := by
    rw [hch]
    have hsplit := Finset.prod_filter_mul_prod_filter_not
      (s := (Finset.univ : Finset (Fin 74)))
      (p := fun k => hSℝ_herm.eigenvalues k = 11)
      (f := fun k => X - C (hSℝ_herm.eigenvalues k))
    rw [← hsplit]
    have hpow : (∏ k ∈ Finset.univ.filter (fun k : Fin 74 => hSℝ_herm.eigenvalues k = 11),
        (X - C (hSℝ_herm.eigenvalues k))) =
        (X - C (11 : ℝ)) ^ (Finset.univ.filter fun k : Fin 74 => hSℝ_herm.eigenvalues k = 11).card := by
      calc
        (∏ k ∈ Finset.univ.filter (fun k : Fin 74 => hSℝ_herm.eigenvalues k = 11),
            (X - C (hSℝ_herm.eigenvalues k)))
            = ∏ _k ∈ Finset.univ.filter (fun k : Fin 74 => hSℝ_herm.eigenvalues k = 11),
                (X - C (11 : ℝ)) := by
              refine Finset.prod_congr rfl fun k hk => ?_
              rw [(Finset.mem_filter.mp hk).2]
        _ = _ := Finset.prod_const _
    rw [hpow]
    exact dvd_mul_right _ _
  by_contra hgt
  have h2 : 2 ≤ (Finset.univ.filter fun k : Fin 74 => hSℝ_herm.eigenvalues k = 11).card := by omega
  have hdvd2 : (X - C (11 : ℝ)) * (X - C (11 : ℝ)) ∣ Sℝ.charpoly := by
    rw [← sq]
    exact dvd_trans (pow_dvd_pow _ h2) hdvd
  let Q11 : ℝ[X] := (X - C (15 : ℝ)) ^ 12 * (X + C (5 : ℝ)) ^ 55 *
    (X ^ 2 - C (28 : ℝ) * X + C (191 : ℝ)) ^ 3
  have hsplit11 : Sℝ.charpoly = (X - C (11 : ℝ)) * Q11 := by
    rw [hchiR]; dsimp [Q11]; ac_rfl
  rw [hsplit11] at hdvd2
  have hdvd1 := (mul_dvd_mul_iff_left (X_sub_C_ne_zero (11 : ℝ))).mp hdvd2
  rcases hdvd1 with ⟨R, hR⟩
  have hev : Q11.eval 11 = 0 := by
    rw [hR, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      sub_self, zero_mul]
  dsimp [Q11] at hev
  norm_num at hev

private lemma map_aeval_rat_real {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (p : ℚ[X]) :
    (Polynomial.aeval A p).map (algebraMap ℚ ℝ) =
      Polynomial.aeval (A.map (algebraMap ℚ ℝ)) (p.map (algebraMap ℚ ℝ)) := by
  let ψ : Matrix (Fin n) (Fin n) ℚ →+* Matrix (Fin n) (Fin n) ℝ :=
    (algebraMap ℚ ℝ).mapMatrix
  change ψ (Polynomial.aeval A p) = Polynomial.aeval (ψ A) (p.map (algebraMap ℚ ℝ))
  induction p using Polynomial.induction_on' with
  | add p1 p2 ih1 ih2 =>
    simp only [map_add, Polynomial.map_add, ih1, ih2]
  | monomial d c =>
    have hsm : ψ (c • A ^ d) = (algebraMap ℚ ℝ c) • ψ (A ^ d) := by
      ext i j
      simp [ψ, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    simp only [Polynomial.aeval_monomial, Polynomial.map_monomial, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mul, Matrix.one_mul, hsm, map_pow]

private lemma idx47_kernel_projector (A0ℚ : Matrix (Fin 16) (Fin 16) ℚ)
    (hA0ℚ_sym : A0ℚᵀ = A0ℚ) :
    let A0ℝ : Matrix (Fin 16) (Fin 16) ℝ := A0ℚ.map (algebraMap ℚ ℝ)
    ∃ PKℚ : Matrix (Fin 16) (Fin 16) ℚ,
      let PKℝ : Matrix (Fin 16) (Fin 16) ℝ := PKℚ.map (algebraMap ℚ ℝ)
      PKℚᵀ = PKℚ ∧ PKℝᵀ = PKℝ ∧
      (∀ v : Fin 16 → ℝ, A0ℝ *ᵥ v = 0 → PKℝ *ᵥ v = v) ∧
      (∀ (v : Fin 16 → ℝ) (μ : ℝ), μ ≠ 0 → A0ℝ *ᵥ v = μ • v → PKℝ *ᵥ v = 0) := by
  intro A0ℝ
  let r0 : ℕ := A0ℚ.charpoly.rootMultiplicity 0
  have hchar_ne : A0ℚ.charpoly ≠ 0 := (Matrix.charpoly_monic A0ℚ).ne_zero
  obtain ⟨q0, hq0⟩ := (by simpa using Polynomial.pow_rootMultiplicity_dvd A0ℚ.charpoly 0 :
    Polynomial.X ^ r0 ∣ A0ℚ.charpoly)
  have hq0_eval0 : q0.eval 0 ≠ 0 := by
    intro h0
    have hdvd_x : Polynomial.X ∣ q0 := by simpa using Polynomial.dvd_iff_isRoot.mpr h0
    have hdvd_s : Polynomial.X ^ (r0 + 1) ∣ A0ℚ.charpoly := by
      rcases hdvd_x with ⟨q1, rfl⟩
      refine ⟨q1, ?_⟩
      rw [hq0, pow_succ]; ring
    have hle : r0 + 1 ≤ r0 := (Polynomial.le_rootMultiplicity_iff hchar_ne).mpr (by simpa using hdvd_s)
    omega
  let PKℚ : Matrix (Fin 16) (Fin 16) ℚ := (q0.eval 0)⁻¹ • Polynomial.aeval A0ℚ q0
  let PKℝ : Matrix (Fin 16) (Fin 16) ℝ := PKℚ.map (algebraMap ℚ ℝ)
  have hPKℚ_sym : PKℚᵀ = PKℚ := by
    change ((q0.eval 0)⁻¹ • Polynomial.aeval A0ℚ q0)ᵀ = (q0.eval 0)⁻¹ • Polynomial.aeval A0ℚ q0
    rw [Matrix.transpose_smul, aeval_symm_of_symm A0ℚ hA0ℚ_sym q0]
  have hA0ℝ_sym : A0ℝᵀ = A0ℝ := by
    ext i j
    simp only [A0ℝ, Matrix.transpose_apply, Matrix.map_apply]
    exact congrArg (algebraMap ℚ ℝ) (congrFun (congrFun hA0ℚ_sym i) j)
  have hPKℝ_sym : PKℝᵀ = PKℝ := by
    ext i j
    simp only [PKℝ, Matrix.transpose_apply, Matrix.map_apply]
    exact congrArg (algebraMap ℚ ℝ) (congrFun (congrFun hPKℚ_sym i) j)
  have hmap_aeval := map_aeval_rat_real A0ℚ q0
  have hPK_map : PKℝ = ((q0.eval 0 : ℚ) : ℝ)⁻¹ • Polynomial.aeval A0ℝ (q0.map (algebraMap ℚ ℝ)) := by
    ext i j
    simp only [PKℝ, PKℚ, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    have h1 := congrFun (congrFun hmap_aeval i) j
    simpa [Matrix.map_apply] using congrArg (fun z => ((q0.eval 0 : ℚ) : ℝ)⁻¹ * z) h1
  have hK : ∀ v : Fin 16 → ℝ, A0ℝ *ᵥ v = 0 → PKℝ *ᵥ v = v := fun v hv => by
    rw [hPK_map, Matrix.smul_mulVec, aeval_ker_mulVec A0ℝ q0 hv,
      smul_smul, inv_mul_cancel₀ (Rat.cast_ne_zero.mpr hq0_eval0), one_smul]
  have hP : ∀ (v : Fin 16 → ℝ) (μ : ℝ), μ ≠ 0 → A0ℝ *ᵥ v = μ • v → PKℝ *ᵥ v = 0 := by
    intro v μ hμ hv
    have hch_map : A0ℝ.charpoly = A0ℚ.charpoly.map (algebraMap ℚ ℝ) := Matrix.charpoly_map A0ℚ _
    have hpow_char : A0ℝ ^ r0 * Polynomial.aeval A0ℝ (q0.map (algebraMap ℚ ℝ)) = 0 := by
      have h1 : A0ℝ ^ r0 * Polynomial.aeval A0ℝ (q0.map (algebraMap ℚ ℝ)) =
          Polynomial.aeval A0ℝ A0ℝ.charpoly := by
        rw [hch_map, hq0, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, map_mul,
          map_pow, Polynomial.aeval_X]
      rw [h1, Matrix.aeval_self_charpoly A0ℝ]
    have hpow_0 : (A0ℝ ^ r0) *ᵥ (PKℝ *ᵥ v) = 0 := by
      rw [hPK_map, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hpow_char,
        Matrix.zero_mulVec, smul_zero]
    have hA0_PK : A0ℝ *ᵥ (PKℝ *ᵥ v) = 0 := by
      by_cases hr0 : r0 = 0
      · rw [hr0, pow_zero, Matrix.one_mulVec] at hpow_0
        rw [hpow_0, Matrix.mulVec_zero]
      · exact symm_pow_mulVec_zero hA0ℝ_sym (Nat.pos_of_ne_zero hr0) hpow_0
    have hcomm_A0 : A0ℝ * PKℝ = PKℝ * A0ℝ := by
      rw [hPK_map, Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      calc
        A0ℝ * Polynomial.aeval A0ℝ (q0.map (algebraMap ℚ ℝ))
            = Polynomial.aeval A0ℝ (Polynomial.X * q0.map (algebraMap ℚ ℝ)) := by
              rw [map_mul, Polynomial.aeval_X]
        _ = Polynomial.aeval A0ℝ (q0.map (algebraMap ℚ ℝ) * Polynomial.X) := by rw [mul_comm]
        _ = Polynomial.aeval A0ℝ (q0.map (algebraMap ℚ ℝ)) * A0ℝ := by rw [map_mul, Polynomial.aeval_X]
    have hμ_zero : μ • (PKℝ *ᵥ v) = 0 := by
      calc
        μ • (PKℝ *ᵥ v) = PKℝ *ᵥ (μ • v) := (Matrix.mulVec_smul _ _ _).symm
        _ = PKℝ *ᵥ (A0ℝ *ᵥ v) := by rw [hv]
        _ = (PKℝ * A0ℝ) *ᵥ v := Matrix.mulVec_mulVec _ _ _
        _ = (A0ℝ * PKℝ) *ᵥ v := by rw [← hcomm_A0]
        _ = A0ℝ *ᵥ (PKℝ *ᵥ v) := (Matrix.mulVec_mulVec _ _ _).symm
        _ = 0 := hA0_PK
    exact (smul_eq_zero.mp hμ_zero).resolve_left hμ
  exact ⟨PKℚ, hPKℚ_sym, hPKℝ_sym, hK, hP⟩

private lemma idx47_kernel_trace_nonneg
    {Sℝ : Matrix (Fin 74) (Fin 74) ℝ}
    {W : Matrix (Fin 58) (Fin 58) ℝ}
    {B : Matrix (Fin 58) (Fin 16) ℝ}
    {Xm : Matrix (Fin 16) (Fin 16) ℝ}
    (hX_herm : Xm.IsHermitian)
    (e : Fin 58 ⊕ Fin 16 ≃ Fin 74)
    (hPerm : Sℝ.submatrix e e = Matrix.fromBlocks W B Bᵀ Xm)
    (hspec_roots : ∀ r : ℝ, Sℝ.charpoly.eval r = 0 →
      r = 15 ∨ r = 11 ∨ r = -5 ∨ r ^ 2 - 28 * r + 191 = 0)
    (hS_mult11 : Module.finrank ℝ (LinearMap.ker (Sℝ - (11 : ℝ) • 1).mulVecLin) ≤ 1)
    (v11ℝ : Fin 74 → ℝ) (hv11ℝ_ne : v11ℝ ≠ 0)
    (hv11_ker : v11ℝ ∈ LinearMap.ker (Sℝ - (11 : ℝ) • 1).mulVecLin)
    (hv11_on_inr : ∀ v : Fin 16 → ℝ,
      v11ℝ ⬝ᵥ (Sum.elim (0 : Fin 58 → ℝ) v ∘ e.symm) = (fun _ => (1 : ℝ)) ⬝ᵥ v)
    (hX_one : Xm *ᵥ (fun _ => (1 : ℝ)) = (11 : ℝ) • (fun _ => (1 : ℝ)))
    (hrel : W * B + B * Xm = (10 : ℝ) • B)
    (Rℚ PKℚ : Matrix (Fin 16) (Fin 16) ℚ)
    (Rℝ A0ℝ PKℝ : Matrix (Fin 16) (Fin 16) ℝ)
    (hR_map : Rℚ.map (algebraMap ℚ ℝ) = Rℝ)
    (hPK_map : PKℚ.map (algebraMap ℚ ℝ) = PKℝ)
    (hRℝ_eq : Rℝ = (75 : ℝ) • 1 + (10 : ℝ) • Xm - Xm ^ 2)
    (hA0_sym : A0ℝᵀ = A0ℝ) (hA0_herm : A0ℝ.IsHermitian)
    (hPK_sym : PKℝᵀ = PKℝ)
    (hK_iff : ∀ v : Fin 16 → ℝ, A0ℝ *ᵥ v = 0 ↔ B *ᵥ v = 0 ∧ (fun _ => (1 : ℝ)) ⬝ᵥ v = 0)
    (hPK_on_K : ∀ v : Fin 16 → ℝ, A0ℝ *ᵥ v = 0 → PKℝ *ᵥ v = v)
    (hPK_on_perp : ∀ (v : Fin 16 → ℝ) (μ : ℝ), μ ≠ 0 → A0ℝ *ᵥ v = μ • v → PKℝ *ᵥ v = 0) :
    0 ≤ (PKℝ * Rℝ).trace := by
  let one16 : Fin 16 → ℝ := fun _ => 1
  let K_fun : Submodule ℝ (Fin 16 → ℝ) := LinearMap.ker A0ℝ.mulVecLin
  have hX_pres_K : ∀ v ∈ K_fun, Xm *ᵥ v ∈ K_fun := fun v hv => by
    have hv' := (hK_iff v).mp (LinearMap.mem_ker.mp hv)
    rcases hv' with ⟨hBv, h1v⟩
    rw [LinearMap.mem_ker]
    change A0ℝ *ᵥ (Xm *ᵥ v) = 0
    rw [hK_iff]
    refine ⟨?_, ?_⟩
    · calc
        B *ᵥ (Xm *ᵥ v) = (B * Xm) *ᵥ v := Matrix.mulVec_mulVec _ _ _
        _ = ((10 : ℝ) • B - W * B) *ᵥ v := by rw [eq_sub_of_add_eq' hrel]
        _ = (10 : ℝ) • (B *ᵥ v) - W *ᵥ (B *ᵥ v) := by
            rw [Matrix.sub_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
        _ = 0 := by simp [hBv]
    · calc
        one16 ⬝ᵥ (Xm *ᵥ v) = (one16 ᵥ* Xm) ⬝ᵥ v := dotProduct_mulVec _ _ _
        _ = (Xmᵀ *ᵥ one16) ⬝ᵥ v := by rw [← Matrix.mulVec_transpose]
        _ = (Xm *ᵥ one16) ⬝ᵥ v := by rw [hermitian_transpose_eq hX_herm]
        _ = ((11 : ℝ) • one16) ⬝ᵥ v := by rw [hX_one]
        _ = 0 := by rw [smul_dotProduct, smul_eq_mul, h1v, mul_zero]
  obtain ⟨dK, eK, lamK, _, heK_in, heK_eig, heK_dot, heK_span⟩ :=
    submodule_diag_symm K_fun hX_herm hX_pres_K
  have hlamK_val : ∀ r : Fin dK,
      lamK r = 15 ∨ lamK r = -5 ∨ (lamK r - 14 = Real.sqrt 5 ∨ lamK r - 14 = -Real.sqrt 5) := by
    intro r
    have her_ne : eK r ≠ 0 := by
      intro h0
      have := heK_dot r r
      rw [h0, dotProduct_zero] at this
      norm_num at this
    have hK_pair := (hK_iff (eK r)).mp (LinearMap.mem_ker.mp (heK_in r))
    have hBv : B *ᵥ eK r = 0 := hK_pair.1
    have h1v : one16 ⬝ᵥ eK r = 0 := hK_pair.2
    let z := Sum.elim (0 : Fin 58 → ℝ) (eK r)
    have hz_ne : z ≠ 0 := fun h0 => her_ne (by ext i; simpa [z] using congrFun h0 (Sum.inr i))
    have hz_eig : Sℝ.submatrix e e *ᵥ z = lamK r • z := by
      simp only [hPerm, z, vec_fromBlocks_mulVec, Matrix.mulVec_zero, hBv, add_zero, zero_add,
        heK_eig r]
      ext x; cases x <;> simp
    have hroot := eval_perm_submatrix_charpoly Sℝ e z hz_ne (lamK r) hz_eig
    rcases hspec_roots (lamK r) hroot with h15 | h11 | hm5 | hquad
    · exact Or.inl h15
    · exfalso
      let wK : Fin 74 → ℝ := z ∘ e.symm
      have hwK_ker : wK ∈ LinearMap.ker (Sℝ - (11 : ℝ) • 1).mulVecLin := by
        rw [LinearMap.mem_ker]
        change (Sℝ - (11 : ℝ) • 1) *ᵥ wK = 0
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]
        ext k
        have h1 := congrFun hz_eig (e.symm k)
        simp only [h11, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1 ⊢
        dsimp [wK]
        rw [← h1, ← e.sum_comp (fun j => Sℝ k j * z (e.symm j))]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp
      have hwK_ne : wK ≠ 0 := fun h0 => hz_ne (by ext x; simpa [wK] using congrFun h0 (e x))
      have hwK_orth : v11ℝ ⬝ᵥ wK = 0 := by
        rw [hv11_on_inr (eK r)]
        exact h1v
      have hli : LinearIndependent ℝ ![v11ℝ, wK] := by
        rw [Fintype.linearIndependent_iff]
        intro c hc
        have h0 : c 0 • v11ℝ + c 1 • wK = 0 := by simpa [Fin.sum_univ_two] using hc
        have hd1 : (c 0 • v11ℝ + c 1 • wK) ⬝ᵥ v11ℝ = 0 := by rw [h0, zero_dotProduct]
        rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul,
          dotProduct_comm wK v11ℝ, hwK_orth, mul_zero, add_zero] at hd1
        have hc0 : c 0 = 0 := (mul_eq_zero.mp hd1).resolve_right
          (dot_self_pos_of_ne_zero hv11ℝ_ne).ne'
        have hd2 : (c 0 • v11ℝ + c 1 • wK) ⬝ᵥ wK = 0 := by rw [h0, zero_dotProduct]
        rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul,
          hwK_orth, mul_zero, zero_add] at hd2
        have hc1 : c 1 = 0 := (mul_eq_zero.mp hd2).resolve_right
          (dot_self_pos_of_ne_zero hwK_ne).ne'
        intro i; fin_cases i <;> assumption
      let vSub : Fin 2 → LinearMap.ker (Sℝ - (11 : ℝ) • 1).mulVecLin := fun i =>
        ⟨![v11ℝ, wK] i, by fin_cases i <;> assumption⟩
      have hvSub_li : LinearIndependent ℝ vSub := by
        rw [Fintype.linearIndependent_iff]
        intro c hc
        have h0 : ∑ i, c i • ![v11ℝ, wK] i = 0 := by simpa [vSub] using congrArg Subtype.val hc
        exact Fintype.linearIndependent_iff.mp hli c h0
      have hfin := hvSub_li.fintype_card_le_finrank
      rw [Fintype.card_fin] at hfin
      omega
    · exact Or.inr (Or.inl hm5)
    · right; right
      have hsq5 : (lamK r - 14) ^ 2 = 5 := by linarith
      have h5 : (lamK r - 14) ^ 2 = (Real.sqrt 5) ^ 2 := by rw [hsq5]; norm_num
      exact sq_eq_sq_iff_eq_or_eq_neg.mp h5
  let U0 : Matrix (Fin 16) (Fin 16) ℝ := (hA0_herm.eigenvectorUnitary : Matrix (Fin 16) (Fin 16) ℝ)
  have hUU0 : U0 * U0ᵀ = 1 := by
    simpa [U0, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self hA0_herm.eigenvectorUnitary
  have hU'U0 : U0ᵀ * U0 = 1 := by
    simpa [U0, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self hA0_herm.eigenvectorUnitary
  have hspec0 : A0ℝ = U0 * Matrix.diagonal hA0_herm.eigenvalues * U0ᵀ := by
    simpa [U0, Matrix.star_eq_conjTranspose, RCLike.ofReal_real_eq_id] using hA0_herm.spectral_theorem
  have hu0_eig : ∀ k : Fin 16, A0ℝ *ᵥ (fun i => U0 i k) = hA0_herm.eigenvalues k • (fun i => U0 i k) := by
    intro k
    have hv : (fun i => U0 i k) = U0 *ᵥ Pi.single k 1 := by
      ext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hv]
    conv_lhs => rw [hspec0]
    calc
      (U0 * Matrix.diagonal hA0_herm.eigenvalues * U0ᵀ) *ᵥ (U0 *ᵥ Pi.single k 1)
          = U0 *ᵥ (Matrix.diagonal hA0_herm.eigenvalues *ᵥ ((U0ᵀ * U0) *ᵥ Pi.single k 1)) := by
            simp only [Matrix.mul_assoc, Matrix.mulVec_mulVec]
      _ = U0 *ᵥ (Matrix.diagonal hA0_herm.eigenvalues *ᵥ Pi.single k 1) := by
            rw [hU'U0, Matrix.one_mulVec]
      _ = U0 *ᵥ (hA0_herm.eigenvalues k • Pi.single k 1) := by
            congr 1; ext j
            simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
            split_ifs with hjk <;> simp [hjk]
      _ = hA0_herm.eigenvalues k • (U0 *ᵥ Pi.single k 1) := Matrix.mulVec_smul _ _ _
  have htr_eq : (PKℝ * Rℝ).trace = ∑ r : Fin dK, eK r ⬝ᵥ (Rℝ *ᵥ eK r) := by
    rw [trace_eq_sum_onb_dot hUU0 (PKℝ * Rℝ)]
    have hterm : ∀ k : Fin 16,
        (fun i => U0 i k) ⬝ᵥ ((PKℝ * Rℝ) *ᵥ fun i => U0 i k) =
          if hA0_herm.eigenvalues k = 0 then
            (fun i => U0 i k) ⬝ᵥ (Rℝ *ᵥ fun i => U0 i k)
          else 0 := fun k => by
      rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.mulVec_transpose, hPK_sym]
      by_cases hk : hA0_herm.eigenvalues k = 0
      · have hA0_u : A0ℝ *ᵥ (fun i => U0 i k) = 0 := by rw [hu0_eig k, hk, zero_smul]
        simp [hk, hPK_on_K _ hA0_u]
      · simp [hk, hPK_on_perp _ _ hk (hu0_eig k)]
    simp_rw [hterm, ← Finset.sum_filter]
    refine trace_proj_basis_eq U0 hUU0 hU'U0 (fun k => hA0_herm.eigenvalues k = 0)
      eK heK_dot ?_ ?_ Rℝ
    · intro k hk0
      apply heK_span
      rw [LinearMap.mem_ker]
      change A0ℝ *ᵥ (fun i => U0 i k) = 0
      rw [hu0_eig k, hk0, zero_smul]
    · intro r k hk_ne
      have he_A0 : A0ℝ *ᵥ eK r = 0 := LinearMap.mem_ker.mp (heK_in r)
      have hdot1 : (A0ℝ *ᵥ (fun i => U0 i k)) ⬝ᵥ eK r =
          hA0_herm.eigenvalues k * ((fun i => U0 i k) ⬝ᵥ eK r) := by
        rw [hu0_eig k, smul_dotProduct, smul_eq_mul]
      have hdot2 : (A0ℝ *ᵥ (fun i => U0 i k)) ⬝ᵥ eK r = 0 := by
        calc
          (A0ℝ *ᵥ (fun i => U0 i k)) ⬝ᵥ eK r
              = ((fun i => U0 i k) ᵥ* A0ℝ) ⬝ᵥ eK r := by
                rw [← Matrix.mulVec_transpose, hA0_sym]
          _ = (fun i => U0 i k) ⬝ᵥ (A0ℝ *ᵥ eK r) := (dotProduct_mulVec _ _ _).symm
          _ = 0 := by rw [he_A0, dotProduct_zero]
      rw [hdot2] at hdot1
      exact (mul_eq_zero.mp hdot1.symm).resolve_left hk_ne
  let mp : ℕ := (Finset.univ.filter fun r : Fin dK => lamK r - 14 = Real.sqrt 5).card
  let mm : ℕ := (Finset.univ.filter fun r : Fin dK => lamK r - 14 = -Real.sqrt 5).card
  have hsum_K : (∑ r : Fin dK, eK r ⬝ᵥ (Rℝ *ᵥ eK r)) =
      (14 * ((mp + mm : ℕ) : ℝ)) + (18 * ((mm : ℝ) - (mp : ℝ))) * Real.sqrt 5 := by
    have hterm : ∀ r : Fin dK, eK r ⬝ᵥ (Rℝ *ᵥ eK r) =
        if lamK r - 14 = Real.sqrt 5 then 14 - 18 * Real.sqrt 5
        else if lamK r - 14 = -Real.sqrt 5 then 14 + 18 * Real.sqrt 5
        else 0 := fun r => by
      have heigR : Rℝ *ᵥ eK r = (75 + 10 * lamK r - lamK r ^ 2) • eK r := by
        rw [hRℝ_eq, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
          Matrix.smul_mulVec, Matrix.one_mulVec, sq, ← Matrix.mulVec_mulVec, heK_eig r,
          Matrix.mulVec_smul, heK_eig r, smul_smul]
        ext i; simp [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [heigR, dotProduct_smul, smul_eq_mul, heK_dot r r]
      simp only [↓reduceIte, mul_one]
      have hsq5_pos : Real.sqrt 5 ≠ -Real.sqrt 5 := by
        have hs : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
        linarith
      rcases hlamK_val r with h15 | hm5 | hp | hm
      · rw [h15]
        have h1 : ¬ ((15 : ℝ) - 14 = Real.sqrt 5) := by
          intro h
          have : (1 : ℝ) ^ 2 = (Real.sqrt 5) ^ 2 := by rw [show (1 : ℝ) = 15 - 14 by norm_num, h]
          norm_num at this
        have h2 : ¬ ((15 : ℝ) - 14 = -Real.sqrt 5) := by
          intro h
          have : (1 : ℝ) ^ 2 = (-Real.sqrt 5) ^ 2 := by rw [show (1 : ℝ) = 15 - 14 by norm_num, h]
          norm_num at this
        simp only [h1, h2, ↓reduceIte]; norm_num
      · rw [hm5]
        have h1 : ¬ ((-5 : ℝ) - 14 = Real.sqrt 5) := by
          have : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
          linarith
        have h2 : ¬ ((-5 : ℝ) - 14 = -Real.sqrt 5) := by
          intro h
          have : (-19 : ℝ) ^ 2 = (-Real.sqrt 5) ^ 2 := by rw [show (-19 : ℝ) = -5 - 14 by norm_num, h]
          norm_num at this
        simp only [h1, h2, ↓reduceIte]; norm_num
      · simp only [hp, ↓reduceIte]
        rw [show lamK r = 14 + Real.sqrt 5 by linarith]
        ring_nf
        rw [Real.sq_sqrt (by norm_num)]
        ring
      · have hne : ¬ (-Real.sqrt 5 = Real.sqrt 5) := hsq5_pos.symm
        rw [hm]
        simp only [hne, ↓reduceIte]
        rw [show lamK r = 14 - Real.sqrt 5 by linarith]
        ring_nf
        rw [Real.sq_sqrt (by norm_num)]
        ring
    simp_rw [hterm]
    have hsplit : ∀ r : Fin dK,
        (if lamK r - 14 = Real.sqrt 5 then (14 - 18 * Real.sqrt 5 : ℝ)
          else if lamK r - 14 = -Real.sqrt 5 then 14 + 18 * Real.sqrt 5
          else 0) =
        (if lamK r - 14 = Real.sqrt 5 then (14 - 18 * Real.sqrt 5 : ℝ) else 0) +
        (if lamK r - 14 = -Real.sqrt 5 then (14 + 18 * Real.sqrt 5 : ℝ) else 0) := fun r => by
      by_cases hp : lamK r - 14 = Real.sqrt 5
      · have hne : ¬ (Real.sqrt 5 = -Real.sqrt 5) := by
          have : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
          linarith
        rw [hp]
        simp [hne]
      · simp [hp]
    have hp_sum : (∑ r : Fin dK, if lamK r - 14 = Real.sqrt 5 then (14 - 18 * Real.sqrt 5 : ℝ) else 0) =
        (mp : ℝ) * (14 - 18 * Real.sqrt 5) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hm_sum : (∑ r : Fin dK, if lamK r - 14 = -Real.sqrt 5 then (14 + 18 * Real.sqrt 5 : ℝ) else 0) =
        (mm : ℝ) * (14 + 18 * Real.sqrt 5) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [Finset.sum_congr rfl (fun r _ => hsplit r), Finset.sum_add_distrib, hp_sum, hm_sum]
    push_cast
    ring
  have htr_rat : (PKℝ * Rℝ).trace = ((PKℚ * Rℚ).trace : ℝ) := by
    rw [← hPK_map, ← hR_map, ← Matrix.map_mul]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.map_apply, Rat.cast_sum]
    rfl
  have heq_zero : (((14 * ((mp + mm : ℕ) : ℚ) - (PKℚ * Rℚ).trace : ℚ) : ℝ)) +
      (((18 * ((mm : ℤ) - (mp : ℤ)) : ℤ) : ℚ) : ℝ) * Real.sqrt 5 = 0 := by
    rw [htr_eq, hsum_K] at htr_rat
    push_cast at htr_rat ⊢
    rw [← htr_rat]
    ring
  obtain ⟨_, hq_zero⟩ := rat_add_mul_sqrt_five_eq_zero heq_zero
  have hm_eq : mm = mp := by
    have hZ : (18 : ℚ) * ((mm : ℤ) - (mp : ℤ)) = 0 := by exact_mod_cast hq_zero
    have hZ_int : (18 : ℤ) * ((mm : ℤ) - (mp : ℤ)) = 0 := by exact_mod_cast hZ
    omega
  rw [htr_eq, hsum_K, hm_eq]
  simp only [sub_self, mul_zero, zero_mul, add_zero]
  exact mul_nonneg (by norm_num) (Nat.cast_nonneg _)

private lemma idx47_eval_mode_val
    {Sℝ : Matrix (Fin 74) (Fin 74) ℝ}
    {W : Matrix (Fin 58) (Fin 58) ℝ}
    {B : Matrix (Fin 58) (Fin 16) ℝ}
    {Xm : Matrix (Fin 16) (Fin 16) ℝ}
    (e : Fin 58 ⊕ Fin 16 ≃ Fin 74)
    (hPerm : Sℝ.submatrix e e = Matrix.fromBlocks W B Bᵀ Xm)
    (hspec_roots : ∀ r : ℝ, Sℝ.charpoly.eval r = 0 →
      r = 15 ∨ r = 11 ∨ r = -5 ∨ r ^ 2 - 28 * r + 191 = 0)
    (hrel : W * B + B * Xm = (10 : ℝ) • B)
    (Rℝ : Matrix (Fin 16) (Fin 16) ℝ)
    (hRℝ_eq : Rℝ = (75 : ℝ) • 1 + (10 : ℝ) • Xm - Xm ^ 2)
    (σsq : ℝ) (hσ_pos : 0 < σsq)
    (dσ : ℕ) (eσ : Fin dσ → Fin 16 → ℝ) (μσ : Fin dσ → ℝ)
    (heσ_BB : ∀ r : Fin dσ, (Bᵀ * B) *ᵥ eσ r = σsq • eσ r)
    (heσ_X : ∀ r : Fin dσ, Xm *ᵥ eσ r = μσ r • eσ r)
    (heσ_dot : ∀ r s : Fin dσ, eσ r ⬝ᵥ eσ s = if r = s then 1 else 0) :
    ∀ r : Fin dσ, Rℝ *ᵥ eσ r = σsq • eσ r := fun r => by
  have her_ne : eσ r ≠ 0 := fun h0 => by
    have := heσ_dot r r; rw [h0, dotProduct_zero] at this; norm_num at this
  obtain ⟨α, β, hsum, hprod, _, hα_root, hβ_root, _, _⟩ :=
    block_eig_pair_roots e hPerm 10 hrel her_ne hσ_pos (heσ_BB r) (heσ_X r)
  have hpair := idx47_pair_unique hsum (hspec_roots α hα_root) (hspec_roots β hβ_root)
  have hαβ : α * β = -75 := by
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  have hval : 75 + 10 * μσ r - μσ r ^ 2 = σsq := by linarith
  rw [hRℝ_eq, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, sq, ← Matrix.mulVec_mulVec, heσ_X r, Matrix.mulVec_smul, heσ_X r,
    smul_smul]
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← hval]
  ring

private lemma idx47_frob_contradiction
    {Sℝ : Matrix (Fin 74) (Fin 74) ℝ}
    {W : Matrix (Fin 58) (Fin 58) ℝ} (hW_herm : W.IsHermitian)
    {B : Matrix (Fin 58) (Fin 16) ℝ}
    {Xm : Matrix (Fin 16) (Fin 16) ℝ} (hX_herm : Xm.IsHermitian)
    (e : Fin 58 ⊕ Fin 16 ≃ Fin 74)
    (hPerm : Sℝ.submatrix e e = Matrix.fromBlocks W B Bᵀ Xm)
    (hspec_roots : ∀ r : ℝ, Sℝ.charpoly.eval r = 0 →
      r = 15 ∨ r = 11 ∨ r = -5 ∨ r ^ 2 - 28 * r + 191 = 0)
    (hB_one : B *ᵥ (fun _ => (1 : ℝ)) = 0)
    (hX_one : Xm *ᵥ (fun _ => (1 : ℝ)) = (11 : ℝ) • (fun _ => (1 : ℝ)))
    (hrel : W * B + B * Xm = (10 : ℝ) • B)
    (hFrob : (Bᵀ * B).trace = 928)
    (Rℝ Jℝ A0ℝ PKℝ : Matrix (Fin 16) (Fin 16) ℝ)
    (hRℝ_eq : Rℝ = (75 : ℝ) • 1 + (10 : ℝ) • Xm - Xm ^ 2)
    (hR_tr : Rℝ.trace = 960)
    (hJ_def : Jℝ = Matrix.of fun _ _ => 1)
    (hA0_def : A0ℝ = Bᵀ * B + Jℝ)
    (hPK_sym : PKℝᵀ = PKℝ)
    (hK_iff : ∀ v : Fin 16 → ℝ, A0ℝ *ᵥ v = 0 ↔ B *ᵥ v = 0 ∧ (fun _ => (1 : ℝ)) ⬝ᵥ v = 0)
    (hPK_on_K : ∀ v : Fin 16 → ℝ, A0ℝ *ᵥ v = 0 → PKℝ *ᵥ v = v)
    (hPK_on_perp : ∀ (v : Fin 16 → ℝ) (μ : ℝ), μ ≠ 0 → A0ℝ *ᵥ v = μ • v → PKℝ *ᵥ v = 0)
    (hPK_trace_nonneg : 0 ≤ (PKℝ * Rℝ).trace) :
    False := by
  let one16 : Fin 16 → ℝ := fun _ => 1
  let K_BB : Matrix (Fin 16) (Fin 16) ℝ := Bᵀ * B
  have hBB_sym : K_BBᵀ = K_BB := by
    ext i j; simp [K_BB, Matrix.transpose_apply, Matrix.mul_apply, mul_comm]
  have hBB_herm : K_BB.IsHermitian := isHermitian_of_transpose_eq hBB_sym
  let U1 : Matrix (Fin 16) (Fin 16) ℝ := (hBB_herm.eigenvectorUnitary : Matrix (Fin 16) (Fin 16) ℝ)
  have hUU1 : U1 * U1ᵀ = 1 := by
    simpa [U1, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self hBB_herm.eigenvectorUnitary
  have hU'U1 : U1ᵀ * U1 = 1 := by
    simpa [U1, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self hBB_herm.eigenvectorUnitary
  have hspec1 : K_BB = U1 * Matrix.diagonal hBB_herm.eigenvalues * U1ᵀ := by
    simpa [U1, Matrix.star_eq_conjTranspose, RCLike.ofReal_real_eq_id] using hBB_herm.spectral_theorem
  have hu1_eig : ∀ k : Fin 16, K_BB *ᵥ (fun i => U1 i k) = hBB_herm.eigenvalues k • (fun i => U1 i k) := by
    intro k
    have hv : (fun i => U1 i k) = U1 *ᵥ Pi.single k 1 := by
      ext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hv]
    conv_lhs => rw [hspec1]
    calc
      (U1 * Matrix.diagonal hBB_herm.eigenvalues * U1ᵀ) *ᵥ (U1 *ᵥ Pi.single k 1)
          = U1 *ᵥ (Matrix.diagonal hBB_herm.eigenvalues *ᵥ ((U1ᵀ * U1) *ᵥ Pi.single k 1)) := by
            simp only [Matrix.mul_assoc, Matrix.mulVec_mulVec]
      _ = U1 *ᵥ (Matrix.diagonal hBB_herm.eigenvalues *ᵥ Pi.single k 1) := by
            rw [hU'U1, Matrix.one_mulVec]
      _ = U1 *ᵥ (hBB_herm.eigenvalues k • Pi.single k 1) := by
            congr 1; ext j
            simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
            split_ifs with hjk <;> simp [hjk]
      _ = hBB_herm.eigenvalues k • (U1 *ᵥ Pi.single k 1) := Matrix.mulVec_smul _ _ _
  have hu1_dot : ∀ k : Fin 16, (fun i => U1 i k) ⬝ᵥ (fun i => U1 i k) = 1 := fun k => by
    have : (fun i => U1 i k) ⬝ᵥ (fun i => U1 i k) = (U1ᵀ * U1) k k := by
      simp [dotProduct, Matrix.mul_apply, Matrix.transpose_apply]
    rw [this, hU'U1, Matrix.one_apply_eq]
  have hBB_eig_nonneg : ∀ k : Fin 16, 0 ≤ hBB_herm.eigenvalues k := fun k => by
    let u := fun i => U1 i k
    have hnonneg : 0 ≤ u ⬝ᵥ (K_BB *ᵥ u) := by
      have hBu : u ⬝ᵥ (K_BB *ᵥ u) = (B *ᵥ u) ⬝ᵥ (B *ᵥ u) := by
        calc
          u ⬝ᵥ (K_BB *ᵥ u) = u ⬝ᵥ (Bᵀ *ᵥ (B *ᵥ u)) := by rw [← Matrix.mulVec_mulVec]
          _ = (u ᵥ* Bᵀ) ⬝ᵥ (B *ᵥ u) := dotProduct_mulVec _ _ _
          _ = (B *ᵥ u) ⬝ᵥ (B *ᵥ u) := by
              have ht := Matrix.mulVec_transpose Bᵀ u
              rw [Matrix.transpose_transpose] at ht
              rw [← ht]
      rw [hBu]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    rw [hu1_eig k, dotProduct_smul, smul_eq_mul, hu1_dot k, mul_one] at hnonneg
    exact hnonneg
  have hmode_match : ∀ k : Fin 16, hBB_herm.eigenvalues k ≠ 0 →
      (fun i => U1 i k) ⬝ᵥ (Rℝ *ᵥ fun i => U1 i k) = hBB_herm.eigenvalues k := by
    intro k hk_ne
    let σsq : ℝ := hBB_herm.eigenvalues k
    have hσ_pos : 0 < σsq := lt_of_le_of_ne (hBB_eig_nonneg k) (Ne.symm hk_ne)
    obtain ⟨dσ, eσ, μσ, _, heσ_BB, heσ_X, heσ_dot, heσ_span⟩ :=
      block_commutator_sim_eig hW_herm hX_herm B 10 hrel σsq
    have heσ_R := idx47_eval_mode_val e hPerm hspec_roots hrel Rℝ hRℝ_eq σsq hσ_pos
      dσ eσ μσ heσ_BB heσ_X heσ_dot
    have huk_exp : (fun i => U1 i k) = ∑ r : Fin dσ, (eσ r ⬝ᵥ fun i => U1 i k) • eσ r :=
      heσ_span (fun i => U1 i k) (hu1_eig k)
    have hRuk : Rℝ *ᵥ (fun i => U1 i k) = σsq • (fun i => U1 i k) := by
      conv_lhs => rw [huk_exp]
      rw [Matrix.mulVec_sum]
      simp_rw [Matrix.mulVec_smul, heσ_R, smul_comm _ σsq]
      rw [← Finset.smul_sum, ← huk_exp]
    rw [hRuk, dotProduct_smul, smul_eq_mul, hu1_dot k, mul_one]
  let Qpos : Matrix (Fin 16) (Fin 16) ℝ := 1 - ((1 / 16 : ℝ) • Jℝ + PKℝ)
  have hQpos_sym : Qposᵀ = Qpos := by
    have hJsym : Jℝᵀ = Jℝ := by ext i j; simp [hJ_def]
    simp [Qpos, Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_smul,
      Matrix.transpose_one, hJsym, hPK_sym]
  have hQpos_trace : (Qpos * Rℝ).trace = (Bᵀ * B).trace := by
    rw [trace_eq_sum_onb_dot hUU1 (Qpos * Rℝ)]
    have hterm : ∀ k : Fin 16,
        (fun i => U1 i k) ⬝ᵥ ((Qpos * Rℝ) *ᵥ fun i => U1 i k) = hBB_herm.eigenvalues k := fun k => by
      rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.mulVec_transpose, hQpos_sym]
      let u := fun i => U1 i k
      by_cases hk0 : hBB_herm.eigenvalues k = 0
      · have hBBu : K_BB *ᵥ u = 0 := by rw [hu1_eig k, hk0, zero_smul]
        have hBu : B *ᵥ u = 0 := by
          have hnorm : (B *ᵥ u) ⬝ᵥ (B *ᵥ u) = 0 := by
            calc
              (B *ᵥ u) ⬝ᵥ (B *ᵥ u) = (u ᵥ* Bᵀ) ⬝ᵥ (B *ᵥ u) := by
                  have htr := Matrix.mulVec_transpose Bᵀ u
                  rw [Matrix.transpose_transpose] at htr
                  rw [← htr]
              _ = u ⬝ᵥ (K_BB *ᵥ u) := (dotProduct_mulVec _ _ _).symm.trans (by rw [← Matrix.mulVec_mulVec])
              _ = 0 := by rw [hBBu, dotProduct_zero]
          exact (dot_self_eq_zero_iff _).mp hnorm
        let c : ℝ := (one16 ⬝ᵥ u) / 16
        let u' : Fin 16 → ℝ := u - c • one16
        have hB_one16 : B *ᵥ one16 = 0 := hB_one
        have hu'_A0 : A0ℝ *ᵥ u' = 0 := by
          rw [hK_iff]
          refine ⟨?_, ?_⟩
          · dsimp [u']
            rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hBu, hB_one16, smul_zero, sub_zero]
          · rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
            have h16 : one16 ⬝ᵥ one16 = 16 := by simp [one16, dotProduct]
            rw [h16]; dsimp [c]; ring
        have hJu : Jℝ *ᵥ u = (one16 ⬝ᵥ u) • one16 := by
          ext i; simp [hJ_def, Matrix.mulVec, dotProduct, one16]
        have hPK_one : PKℝ *ᵥ one16 = 0 := by
          have hJ_one : Jℝ *ᵥ one16 = (16 : ℝ) • one16 := by
            ext i; simp [hJ_def, Matrix.mulVec, dotProduct, one16]
          have hA0_one : A0ℝ *ᵥ one16 = (16 : ℝ) • one16 := by
            rw [hA0_def, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hB_one16, Matrix.mulVec_zero,
              zero_add, hJ_one]
          exact hPK_on_perp one16 16 (by norm_num) hA0_one
        have hPKu : PKℝ *ᵥ u = u' := by
          have h1 : u = c • one16 + u' := by simp [u']
          conv_lhs => rw [h1, Matrix.mulVec_add, Matrix.mulVec_smul, hPK_one, smul_zero, zero_add,
            hPK_on_K u' hu'_A0]
        have hQu : Qpos *ᵥ u = 0 := by
          simp only [Qpos, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
            Matrix.smul_mulVec, hJu, hPKu]
          ext i
          simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, u', c]
          ring
        rw [hQu, zero_dotProduct, hk0]
      · have hB_one16 : B *ᵥ one16 = 0 := hB_one
        have h1u : one16 ⬝ᵥ u = 0 := by
          have hdot1 : one16 ⬝ᵥ (K_BB *ᵥ u) = hBB_herm.eigenvalues k * (one16 ⬝ᵥ u) := by
            rw [hu1_eig k, dotProduct_smul, smul_eq_mul]
          have hdot2 : one16 ⬝ᵥ (K_BB *ᵥ u) = 0 := by
            calc
              one16 ⬝ᵥ (K_BB *ᵥ u) = (one16 ᵥ* K_BB) ⬝ᵥ u := dotProduct_mulVec _ _ _
              _ = (K_BBᵀ *ᵥ one16) ⬝ᵥ u := by rw [← Matrix.mulVec_transpose]
              _ = (K_BB *ᵥ one16) ⬝ᵥ u := by rw [hBB_sym]
              _ = 0 := by
                dsimp [K_BB]
                rw [← Matrix.mulVec_mulVec, hB_one16, Matrix.mulVec_zero, zero_dotProduct]
          rw [hdot2] at hdot1
          exact (mul_eq_zero.mp hdot1.symm).resolve_left hk0
        have hJu : Jℝ *ᵥ u = 0 := by
          ext i; simp [hJ_def, Matrix.mulVec, dotProduct, one16] at h1u ⊢; exact h1u
        have hA0u : A0ℝ *ᵥ u = hBB_herm.eigenvalues k • u := by
          rw [hA0_def, Matrix.add_mulVec, hJu, add_zero]
          exact hu1_eig k
        have hPKu : PKℝ *ᵥ u = 0 := hPK_on_perp u _ hk0 hA0u
        have hQu : Qpos *ᵥ u = u := by
          simp [Qpos, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
            hJu, hPKu]
        rw [hQu]
        exact hmode_match k hk0
    simp_rw [hterm]
    have htr_BB : K_BB.trace = ∑ k : Fin 16, hBB_herm.eigenvalues k := by
      have h := hBB_herm.trace_eq_sum_eigenvalues
      simp only [RCLike.ofReal_real_eq_id, id_eq] at h
      exact h
    exact htr_BB.symm
  have hJR_tr : ((1 / 16 : ℝ) • Jℝ * Rℝ).trace = 64 := by
    have hJR_one : (Jℝ * Rℝ).trace = one16 ⬝ᵥ (Rℝ *ᵥ one16) := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, hJ_def, Matrix.of_apply, one_mul,
        dotProduct, Matrix.mulVec, one16]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp
    have hR_one : Rℝ *ᵥ one16 = (64 : ℝ) • one16 := by
      rw [hRℝ_eq, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, sq, ← Matrix.mulVec_mulVec, hX_one, Matrix.mulVec_smul, hX_one,
        smul_smul]
      ext i
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, one16]
      norm_num
    have hdot : one16 ⬝ᵥ (Rℝ *ᵥ one16) = 1024 := by
      rw [hR_one, dotProduct_smul, smul_eq_mul]
      simp [one16, dotProduct]
      norm_num
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, hJR_one, hdot]
    norm_num
  have hsplit_tr : (Qpos * Rℝ).trace = Rℝ.trace - ((1 / 16 : ℝ) • Jℝ * Rℝ).trace - (PKℝ * Rℝ).trace := by
    simp only [Qpos, Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, Matrix.trace_sub,
      Matrix.trace_add]
    ring
  rw [hQpos_trace, hFrob, hR_tr, hJR_tr] at hsplit_tr
  linarith

/-- **Phase 3 Unconditional Block-Trace Elimination of `(19, 74) idx=47`:**
Any Seidel matrix `S : Matrix (Fin 74) (Fin 74) ℤ` with the `idx=47` characteristic polynomial
and `58 + 16` block decomposition (`C₁` supporting the `11`-eigenvector and `(S²)[C_out, C₁] = 10 S[C_out, C₁]`)
leads to `928 = Tr(Bᵀ B) ≤ 896`, proving `False`. -/
theorem idx47_eliminated {S : Matrix (Fin 74) (Fin 74) ℤ} (hS : IsSeidelMatrix S)
    (hchi : S.charpoly =
      (X - C (15 : ℤ)) ^ 12 * (X - C (11 : ℤ)) * (X + C (5 : ℤ)) ^ 55 *
        (X ^ 2 - C (28 : ℤ) * X + C (191 : ℤ)) ^ 3)
    (e : Fin 58 ⊕ Fin 16 ≃ Fin 74)
    (hv11 : S *ᵥ (fun k => match e.symm k with | Sum.inl _ => (0 : ℤ) | Sum.inr _ => 1) =
      (11 : ℤ) • (fun k => match e.symm k with | Sum.inl _ => (0 : ℤ) | Sum.inr _ => 1))
    (h2v : ∀ (w : Fin 58) (u : Fin 16),
      (S ^ 2) (e (Sum.inl w)) (e (Sum.inr u)) = 10 * S (e (Sum.inl w)) (e (Sum.inr u))) :
    False := by
  let Sℝ : Matrix (Fin 74) (Fin 74) ℝ := S.map (Int.castRingHom ℝ)
  have hSℝ_herm : Sℝ.IsHermitian := by
    apply isHermitian_of_transpose_eq
    ext i j; simp [Sℝ, Matrix.transpose_apply, hS.symm i j]
  have hchiR : Sℝ.charpoly =
      (X - C (15 : ℝ)) ^ 12 * (X - C (11 : ℝ)) * (X + C (5 : ℝ)) ^ 55 *
        (X ^ 2 - C (28 : ℝ) * X + C (191 : ℝ)) ^ 3 := by
    have h1 := congrArg (Polynomial.map (Int.castRingHom ℝ)) hchi
    rw [← Matrix.charpoly_map S (Int.castRingHom ℝ)] at h1
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_pow, Polynomial.map_pow,
      map_int_X_sub 15 15 (by norm_num), map_int_X_sub 11 11 (by norm_num),
      map_int_X_add 5 5 (by norm_num),
      map_int_X_quad 28 191 28 191 (by norm_num) (by norm_num)] at h1
    exact h1
  have hspec_roots : ∀ r : ℝ, Sℝ.charpoly.eval r = 0 →
      r = 15 ∨ r = 11 ∨ r = -5 ∨ r ^ 2 - 28 * r + 191 = 0 := by
    intro r hr
    rw [hchiR] at hr
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, mul_eq_zero, pow_eq_zero_iff', ne_eq] at hr
    rcases hr with (((⟨h, _⟩ | h) | ⟨h, _⟩) | ⟨h, _⟩)
    · left; linarith
    · right; left; linarith
    · right; right; left; linarith
    · right; right; right; linarith
  have hS_mult11 := idx47_mult11_le_one hSℝ_herm hchiR
  let Wℤ : Matrix (Fin 58) (Fin 58) ℤ := S.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)
  let Bℤ : Matrix (Fin 58) (Fin 16) ℤ := S.submatrix (e ∘ Sum.inl) (e ∘ Sum.inr)
  let Xℤ : Matrix (Fin 16) (Fin 16) ℤ := S.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)
  let W : Matrix (Fin 58) (Fin 58) ℝ := Wℤ.map (Int.castRingHom ℝ)
  let B : Matrix (Fin 58) (Fin 16) ℝ := Bℤ.map (Int.castRingHom ℝ)
  let Xm : Matrix (Fin 16) (Fin 16) ℝ := Xℤ.map (Int.castRingHom ℝ)
  have hW_herm : W.IsHermitian := by
    apply isHermitian_of_transpose_eq
    ext i j; simp [W, Wℤ, Matrix.transpose_apply, hS.symm]
  have hX_herm : Xm.IsHermitian := by
    apply isHermitian_of_transpose_eq
    ext i j; simp [Xm, Xℤ, Matrix.transpose_apply, hS.symm]
  have hPerm : Sℝ.submatrix e e = Matrix.fromBlocks W B Bᵀ Xm := by
    ext a b
    cases a with
    | inl i =>
      cases b with
      | inl j => simp [Sℝ, W, Wℤ, Matrix.fromBlocks_apply₁₁]
      | inr j => simp [Sℝ, B, Bℤ, Matrix.fromBlocks_apply₁₂]
    | inr i =>
      cases b with
      | inl j => simp [Sℝ, B, Bℤ, Matrix.fromBlocks_apply₂₁, Matrix.transpose_apply, hS.symm]
      | inr j => simp [Sℝ, Xm, Xℤ, Matrix.fromBlocks_apply₂₂]
  let one16 : Fin 16 → ℝ := fun _ => 1
  have hB_one : B *ᵥ one16 = 0 := by
    ext w
    have hw := congrFun hv11 (e (Sum.inl w))
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Equiv.symm_apply_apply,
      mul_zero] at hw
    rw [← e.sum_comp (fun x => S (e (Sum.inl w)) x *
      match e.symm x with | Sum.inl _ => (0 : ℤ) | Sum.inr _ => 1)] at hw
    simp only [Fintype.sum_sum_type, Equiv.symm_apply_apply, mul_zero, Finset.sum_const_zero,
      zero_add, mul_one] at hw
    have hwR : ((∑ x : Fin 16, S (e (Sum.inl w)) (e (Sum.inr x)) : ℤ) : ℝ) = 0 := by exact_mod_cast hw
    simpa [B, Bℤ, one16, Matrix.mulVec, dotProduct] using hwR
  have hX_one : Xm *ᵥ one16 = (11 : ℝ) • one16 := by
    ext u
    have hu := congrFun hv11 (e (Sum.inr u))
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Equiv.symm_apply_apply,
      mul_one] at hu
    rw [← e.sum_comp (fun x => S (e (Sum.inr u)) x *
      match e.symm x with | Sum.inl _ => (0 : ℤ) | Sum.inr _ => 1)] at hu
    simp only [Fintype.sum_sum_type, Equiv.symm_apply_apply, mul_zero, Finset.sum_const_zero,
      zero_add, mul_one] at hu
    have huR : ((∑ x : Fin 16, S (e (Sum.inr u)) (e (Sum.inr x)) : ℤ) : ℝ) = 11 := by exact_mod_cast hu
    simpa [Xm, Xℤ, one16, Matrix.mulVec, dotProduct] using huR
  have hrel : W * B + B * Xm = (10 : ℝ) • B := by
    ext w u
    have hwu := h2v w u
    rw [sq, Matrix.mul_apply, ← e.sum_comp (fun x => S (e (Sum.inl w)) x * S x (e (Sum.inr u)))] at hwu
    simp only [Fintype.sum_sum_type] at hwu
    have hwuR : (((∑ x : Fin 58, S (e (Sum.inl w)) (e (Sum.inl x)) *
          S (e (Sum.inl x)) (e (Sum.inr u)) +
        ∑ x : Fin 16, S (e (Sum.inl w)) (e (Sum.inr x)) *
          S (e (Sum.inr x)) (e (Sum.inr u)) : ℤ) : ℝ)) =
        (10 : ℝ) * (S (e (Sum.inl w)) (e (Sum.inr u)) : ℝ) := by
      exact_mod_cast hwu
    simpa [W, Wℤ, B, Bℤ, Xm, Xℤ, Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply,
      smul_eq_mul] using hwuR
  have hFrob : (Bᵀ * B).trace = 928 := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
    have hsq1 : ∀ (u : Fin 16) (w : Fin 58), B w u * B w u = 1 := fun u w => by
      have hne : e (Sum.inl w) ≠ e (Sum.inr u) := fun h => by
        have := e.injective h; cases this
      rcases hS.offDiag_eq_one_or_neg_one hne with h1 | h1 <;> simp [B, Bℤ, h1]
    simp_rw [hsq1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    norm_num
  let Rℤ : Matrix (Fin 16) (Fin 16) ℤ := (75 : ℤ) • 1 + (10 : ℤ) • Xℤ - Xℤ ^ 2
  let Rℚ : Matrix (Fin 16) (Fin 16) ℚ := Rℤ.map (Int.castRingHom ℚ)
  let Rℝ : Matrix (Fin 16) (Fin 16) ℝ := Rℤ.map (Int.castRingHom ℝ)
  have hR_map : Rℚ.map (algebraMap ℚ ℝ) = Rℝ := by
    ext i j; simp [Rℚ, Rℝ]
  have hRℝ_eq : Rℝ = (75 : ℝ) • 1 + (10 : ℝ) • Xm - Xm ^ 2 := by
    let φR : Matrix (Fin 16) (Fin 16) ℤ →+* Matrix (Fin 16) (Fin 16) ℝ :=
      (Int.castRingHom ℝ).mapMatrix
    have hsm : ∀ (c : ℤ) (A : Matrix (Fin 16) (Fin 16) ℤ), φR (c • A) = (c : ℝ) • φR A :=
      fun c A => by
        apply Matrix.ext; intro i j
        simp [-zsmul_eq_mul, φR, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply,
          smul_eq_mul]
    change φR Rℤ = (75 : ℝ) • 1 + (10 : ℝ) • Xm - Xm ^ 2
    dsimp [Rℤ]
    rw [map_sub, map_add, map_pow, hsm, hsm, map_one]
    rfl
  have hXℤ_diag : ∀ i : Fin 16, Xℤ i i = 0 := fun i => hS.diag_eq_zero _
  have hXℤ_sq : ∀ i : Fin 16, (Xℤ ^ 2) i i = 15 := fun i => by
    rw [sq, Matrix.mul_apply]
    have h1 : (∑ j : Fin 16, Xℤ i j * Xℤ j i) = ∑ j ∈ Finset.univ.erase i, (1 : ℤ) := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i), hXℤ_diag i, zero_mul, zero_add]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hij : e (Sum.inr i) ≠ e (Sum.inr j) := fun h =>
        (Finset.mem_erase.mp hj).1 (Fin.ext (by
          have := e.injective h; cases this; rfl)).symm
      dsimp [Xℤ]
      rw [hS.symm (e (Sum.inr i)) (e (Sum.inr j))]
      rcases hS.offDiag_eq_one_or_neg_one hij with h1 | h1 <;> simp [h1]
    rw [h1, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin]
    norm_num
  have hR_tr : Rℝ.trace = 960 := by
    have hdiag_Z : ∀ i : Fin 16, Rℤ i i = 60 := fun i => by
      change ((75 : ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ) + (10 : ℤ) • Xℤ - Xℤ ^ 2) i i = 60
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
        ↓reduceIte, smul_eq_mul, hXℤ_diag i, hXℤ_sq i]
      norm_num
    have hZ : Rℤ.trace = 960 := by
      simp only [Matrix.trace, Matrix.diag_apply, hdiag_Z, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      norm_num
    simp only [Rℝ, Matrix.trace, Matrix.diag_apply, Matrix.map_apply]
    simpa [Matrix.trace, Matrix.diag_apply] using congrArg (Int.cast : ℤ → ℝ) hZ
  let Bℚ : Matrix (Fin 58) (Fin 16) ℚ := Bℤ.map (Int.castRingHom ℚ)
  let Jℚ : Matrix (Fin 16) (Fin 16) ℚ := Matrix.of fun _ _ => 1
  let A0ℚ : Matrix (Fin 16) (Fin 16) ℚ := Bℚᵀ * Bℚ + Jℚ
  have hA0ℚ_sym : A0ℚᵀ = A0ℚ := by
    ext i j; simp [A0ℚ, Jℚ, Matrix.transpose_apply, Matrix.mul_apply, mul_comm]
  let Jℝ : Matrix (Fin 16) (Fin 16) ℝ := Matrix.of fun _ _ => 1
  let A0ℝ : Matrix (Fin 16) (Fin 16) ℝ := Bᵀ * B + Jℝ
  have hA0_map : A0ℚ.map (algebraMap ℚ ℝ) = A0ℝ := by
    ext i j
    simp [A0ℚ, A0ℝ, Bℚ, B, Jℚ, Jℝ, Matrix.mul_apply]
  have hA0ℝ_sym : A0ℝᵀ = A0ℝ := by
    ext i j; simp [A0ℝ, Jℝ, Matrix.transpose_apply, Matrix.mul_apply, mul_comm]
  have hA0ℝ_herm : A0ℝ.IsHermitian := isHermitian_of_transpose_eq hA0ℝ_sym
  obtain ⟨PKℚ, _, hPK_sym, hPK_on_K, hPK_on_perp⟩ := idx47_kernel_projector A0ℚ hA0ℚ_sym
  let PKℝ : Matrix (Fin 16) (Fin 16) ℝ := PKℚ.map (algebraMap ℚ ℝ)
  rw [hA0_map] at hPK_on_K hPK_on_perp
  have hK_iff : ∀ v : Fin 16 → ℝ, A0ℝ *ᵥ v = 0 ↔ B *ᵥ v = 0 ∧ one16 ⬝ᵥ v = 0 := fun v => by
    constructor
    · intro hv
      have hdot0 : v ⬝ᵥ (A0ℝ *ᵥ v) = 0 := by rw [hv, dotProduct_zero]
      have hsum : v ⬝ᵥ (A0ℝ *ᵥ v) = (B *ᵥ v) ⬝ᵥ (B *ᵥ v) + (one16 ⬝ᵥ v) ^ 2 := by
        simp only [A0ℝ, Matrix.add_mulVec, dotProduct_add]
        congr 1
        · calc
            v ⬝ᵥ ((Bᵀ * B) *ᵥ v) = (v ᵥ* Bᵀ) ⬝ᵥ (B *ᵥ v) := by
                rw [← Matrix.mulVec_mulVec, dotProduct_mulVec]
            _ = (B *ᵥ v) ⬝ᵥ (B *ᵥ v) := by
                have htr := Matrix.mulVec_transpose Bᵀ v
                rw [Matrix.transpose_transpose] at htr
                rw [← htr]
        · have hJ : Jℝ *ᵥ v = (one16 ⬝ᵥ v) • one16 := by
            ext i; simp [Jℝ, Matrix.mulVec, dotProduct, one16]
          rw [hJ, dotProduct_smul, smul_eq_mul, dotProduct_comm v one16, sq]
      rw [hsum] at hdot0
      have hnn1 : 0 ≤ (B *ᵥ v) ⬝ᵥ (B *ᵥ v) := Finset.sum_nonneg fun i _ => mul_self_nonneg _
      have hnn2 : 0 ≤ (one16 ⬝ᵥ v) ^ 2 := sq_nonneg _
      have h1 : (B *ᵥ v) ⬝ᵥ (B *ᵥ v) = 0 := by linarith
      have h2 : (one16 ⬝ᵥ v) ^ 2 = 0 := by linarith
      exact ⟨(dot_self_eq_zero_iff _).mp h1, sq_eq_zero_iff.mp h2⟩
    · rintro ⟨hBv, h1v⟩
      have hJ : Jℝ *ᵥ v = 0 := by
        ext i; simp [Jℝ, Matrix.mulVec, dotProduct, one16] at h1v ⊢; exact h1v
      simp [A0ℝ, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hBv, hJ]
  let v11ℝ : Fin 74 → ℝ := fun k => match e.symm k with | Sum.inl _ => 0 | Sum.inr _ => 1
  have hv11ℝ_ne : v11ℝ ≠ 0 := fun h0 => by
    have := congrFun h0 (e (Sum.inr 0))
    simp [v11ℝ] at this
  have hv11_ker : v11ℝ ∈ LinearMap.ker (Sℝ - (11 : ℝ) • 1).mulVecLin := by
    rw [LinearMap.mem_ker]
    change (Sℝ - (11 : ℝ) • 1) *ᵥ v11ℝ = 0
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]
    ext k
    change ∑ j : Fin 74, (S k j : ℝ) * v11ℝ j = (11 : ℝ) * v11ℝ k
    have hkZ : (∑ j : Fin 74, S k j *
        (match e.symm j with | Sum.inl _ => (0 : ℤ) | Sum.inr _ => 1)) =
        11 * (match e.symm k with | Sum.inl _ => (0 : ℤ) | Sum.inr _ => 1) := congrFun hv11 k
    have hkR := congrArg (Int.cast : ℤ → ℝ) hkZ
    push_cast at hkR
    convert hkR using 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      dsimp [v11ℝ]; cases e.symm j <;> simp
    · dsimp [v11ℝ]; cases e.symm k <;> simp
  have hv11_on_inr : ∀ v : Fin 16 → ℝ,
      v11ℝ ⬝ᵥ (Sum.elim (0 : Fin 58 → ℝ) v ∘ e.symm) = one16 ⬝ᵥ v := fun v => by
    rw [dotProduct, ← e.sum_comp (fun k => v11ℝ k * (Sum.elim (0 : Fin 58 → ℝ) v ∘ e.symm) k)]
    simp [v11ℝ, Fintype.sum_sum_type, one16, dotProduct]
  have htr_nn := idx47_kernel_trace_nonneg hX_herm e hPerm hspec_roots hS_mult11 v11ℝ hv11ℝ_ne
    hv11_ker hv11_on_inr hX_one hrel Rℚ PKℚ Rℝ A0ℝ PKℝ hR_map rfl hRℝ_eq hA0ℝ_sym hA0ℝ_herm
    hPK_sym hK_iff hPK_on_K hPK_on_perp
  exact idx47_frob_contradiction hW_herm hX_herm e hPerm hspec_roots hB_one hX_one hrel hFrob
    Rℝ Jℝ A0ℝ PKℝ hRℝ_eq hR_tr rfl rfl hPK_sym hK_iff hPK_on_K hPK_on_perp htr_nn

private lemma idx861_mult13_le_eight {S1ℝ : Matrix (Fin 58) (Fin 58) ℝ}
    (hS1_herm : S1ℝ.IsHermitian)
    (hchiR : S1ℝ.charpoly =
      (X - C (13 : ℝ)) ^ 8 * (X - C (11 : ℝ)) ^ 5 * (X - C (9 : ℝ)) ^ 4 *
        (X - C (5 : ℝ)) * (X + C (5 : ℝ)) ^ 40) :
    Module.finrank ℝ (LinearMap.ker (S1ℝ - (13 : ℝ) • 1).mulVecLin) ≤ 8 := by
  rw [submatrix_eigenvalue_count_eq_finrank_ker hS1_herm 13]
  have hch : S1ℝ.charpoly = ∏ k : Fin 58, (X - C (hS1_herm.eigenvalues k)) := by
    simpa [RCLike.ofReal_real_eq_id] using hS1_herm.charpoly_eq
  have hdvd : (X - C (13 : ℝ)) ^ (Finset.univ.filter fun k : Fin 58 => hS1_herm.eigenvalues k = 13).card ∣
      S1ℝ.charpoly := by
    rw [hch]
    have hsplit := Finset.prod_filter_mul_prod_filter_not
      (s := (Finset.univ : Finset (Fin 58)))
      (p := fun k => hS1_herm.eigenvalues k = 13)
      (f := fun k => X - C (hS1_herm.eigenvalues k))
    rw [← hsplit]
    have hpow : (∏ k ∈ Finset.univ.filter (fun k : Fin 58 => hS1_herm.eigenvalues k = 13),
        (X - C (hS1_herm.eigenvalues k))) =
        (X - C (13 : ℝ)) ^ (Finset.univ.filter fun k : Fin 58 => hS1_herm.eigenvalues k = 13).card := by
      calc
        (∏ k ∈ Finset.univ.filter (fun k : Fin 58 => hS1_herm.eigenvalues k = 13),
            (X - C (hS1_herm.eigenvalues k)))
            = ∏ _k ∈ Finset.univ.filter (fun k : Fin 58 => hS1_herm.eigenvalues k = 13),
                (X - C (13 : ℝ)) := by
              refine Finset.prod_congr rfl fun k hk => ?_
              rw [(Finset.mem_filter.mp hk).2]
        _ = _ := Finset.prod_const _
    rw [hpow]
    exact dvd_mul_right _ _
  let Q : ℝ[X] := (X - C (11 : ℝ)) ^ 5 * (X - C (9 : ℝ)) ^ 4 *
    (X - C (5 : ℝ)) * (X + C (5 : ℝ)) ^ 40
  have hchiQ : S1ℝ.charpoly = (X - C (13 : ℝ)) ^ 8 * Q := by
    rw [hchiR]; dsimp [Q]; ac_rfl
  by_contra hm_gt
  have h9 : 9 ≤ (Finset.univ.filter fun k : Fin 58 => hS1_herm.eigenvalues k = 13).card := by omega
  have hdvd9 : (X - C (13 : ℝ)) ^ 8 * (X - C (13 : ℝ)) ∣ S1ℝ.charpoly := by
    rw [← pow_succ]
    exact dvd_trans (pow_dvd_pow _ h9) hdvd
  rw [hchiQ] at hdvd9
  have hne : (X - C (13 : ℝ)) ^ 8 ≠ 0 := pow_ne_zero 8 (X_sub_C_ne_zero 13)
  have hdvdQ : (X - C (13 : ℝ)) ∣ Q := (mul_dvd_mul_iff_left hne).mp hdvd9
  rcases hdvdQ with ⟨R, hR⟩
  have hev : Q.eval 13 = 0 := by
    rw [hR, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul]
  dsimp [Q] at hev
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C] at hev
  have hpos : (0 : ℝ) <
      (13 - 11 : ℝ) ^ 5 * (13 - 9 : ℝ) ^ 4 * (13 - 5 : ℝ) * (13 + 5 : ℝ) ^ 40 := by
    positivity
  linarith only [hev, hpos]

private lemma idx861_eval_mode_le_81
    {S1ℝ : Matrix (Fin 58) (Fin 58) ℝ}
    {Xm : Matrix (Fin 30) (Fin 30) ℝ}
    {Y : Matrix (Fin 30) (Fin 28) ℝ}
    {Zm : Matrix (Fin 28) (Fin 28) ℝ}
    (e : Fin 30 ⊕ Fin 28 ≃ Fin 58)
    (hPerm : S1ℝ.submatrix e e = Matrix.fromBlocks Xm Y Yᵀ Zm)
    (hspec_roots : ∀ r : ℝ, S1ℝ.charpoly.eval r = 0 →
      r = 13 ∨ r = 11 ∨ r = 9 ∨ r = 5 ∨ r = -5)
    (hrel : Xm * Y + Y * Zm = (8 : ℝ) • Y)
    (σsq : ℝ) (hσ_pos : 0 < σsq)
    (v : Fin 28 → ℝ) (hv_ne : v ≠ 0) (μv : ℝ)
    (hBB : (Yᵀ * Y) *ᵥ v = σsq • v)
    (hC : Zm *ᵥ v = μv • v) :
    σsq ≤ 81 ∧
    (let z13 : Fin 30 ⊕ Fin 28 → ℝ := Sum.elim (Y *ᵥ v) ((13 - (8 - μv)) • v)
     z13 ≠ 0 ∧ S1ℝ.submatrix e e *ᵥ z13 = (13 : ℝ) • z13) := by
  obtain ⟨α, β, hsum, hprod, hlt, hα_root, hβ_root, hzα_ne, hzα_eig⟩ :=
    block_eig_pair_roots e hPerm 8 hrel hv_ne hσ_pos hBB hC
  rcases idx861_pair_unique hsum (hspec_roots α hα_root) (hspec_roots β hβ_root) with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨by nlinarith [sq_nonneg (μv - 4)], hzα_ne, hzα_eig⟩
  · linarith

private lemma idx861_pos_eig_bound
    {S1ℝ : Matrix (Fin 58) (Fin 58) ℝ}
    {Xm : Matrix (Fin 30) (Fin 30) ℝ} (hX_herm : Xm.IsHermitian)
    {Y : Matrix (Fin 30) (Fin 28) ℝ}
    {Zm : Matrix (Fin 28) (Fin 28) ℝ} (hZ_herm : Zm.IsHermitian)
    (e : Fin 30 ⊕ Fin 28 ≃ Fin 58)
    (hPerm : S1ℝ.submatrix e e = Matrix.fromBlocks Xm Y Yᵀ Zm)
    (hspec_roots : ∀ r : ℝ, S1ℝ.charpoly.eval r = 0 →
      r = 13 ∨ r = 11 ∨ r = 9 ∨ r = 5 ∨ r = -5)
    (hS1_mult13 : Module.finrank ℝ (LinearMap.ker (S1ℝ - (13 : ℝ) • 1).mulVecLin) ≤ 8)
    (hrel : Xm * Y + Y * Zm = (8 : ℝ) • Y)
    (hFrob : (Yᵀ * Y).trace = 840) :
    False := by
  let K_YY : Matrix (Fin 28) (Fin 28) ℝ := Yᵀ * Y
  have hYY_herm : K_YY.IsHermitian := by
    apply isHermitian_of_transpose_eq
    simp [K_YY, Matrix.transpose_mul]
  let posVals : Finset ℝ := (Finset.univ.image hYY_herm.eigenvalues).filter (0 < ·)
  let d_fn : posVals → ℕ := fun σ =>
    Module.finrank ℝ (LinearMap.ker (K_YY - σ.1 • 1).mulVecLin)
  have h_sim : ∀ σ : posVals,
      ∃ (e_eig : Fin (d_fn σ) → Fin 28 → ℝ) (μ : Fin (d_fn σ) → ℝ),
        (∀ r, K_YY *ᵥ e_eig r = σ.1 • e_eig r) ∧
        (∀ r, Zm *ᵥ e_eig r = μ r • e_eig r) ∧
        (∀ r s, e_eig r ⬝ᵥ e_eig s = if r = s then 1 else 0) := by
    intro σ
    obtain ⟨d', e', μ', hdim', hBB', hC', hedot', _⟩ :=
      block_commutator_sim_eig hX_herm hZ_herm Y 8 hrel σ.1
    have hd_eq : d_fn σ = d' := hdim'.symm
    refine ⟨e' ∘ Fin.cast hd_eq, μ' ∘ Fin.cast hd_eq, fun r => hBB' _, fun r => hC' _,
      fun r s => ?_⟩
    dsimp only [Function.comp_def]
    rw [hedot']
    simp [Fin.cast_inj]
  choose e_eig μ heBB heC hedot using h_sim
  let ι := Σ σ : posVals, Fin (d_fn σ)
  have hp_eig : ∀ p : ι,
      p.1.1 ≤ 81 ∧
      (let z13 : Fin 30 ⊕ Fin 28 → ℝ :=
        Sum.elim (Y *ᵥ e_eig p.1 p.2) ((13 - (8 - μ p.1 p.2)) • e_eig p.1 p.2)
       z13 ≠ 0 ∧ S1ℝ.submatrix e e *ᵥ z13 = (13 : ℝ) • z13) := by
    intro p
    have he_ne : e_eig p.1 p.2 ≠ 0 := by
      intro h0
      have hd := hedot p.1 p.2 p.2
      rw [h0, dotProduct_zero] at hd
      simp at hd
    have hσ_pos : 0 < p.1.1 := (Finset.mem_filter.mp p.1.2).2
    exact idx861_eval_mode_le_81 e hPerm hspec_roots hrel p.1.1 hσ_pos
      (e_eig p.1 p.2) he_ne (μ p.1 p.2) (heBB p.1 p.2) (heC p.1 p.2)
  let K13 := LinearMap.ker (S1ℝ - (13 : ℝ) • (1 : Matrix (Fin 58) (Fin 58) ℝ)).mulVecLin
  let w : ι → Fin 58 → ℝ := fun p =>
    Sum.elim (Y *ᵥ e_eig p.1 p.2) ((13 - (8 - μ p.1 p.2)) • e_eig p.1 p.2) ∘ e.symm
  have hw_mem : ∀ p : ι, w p ∈ K13 := by
    intro p
    rw [LinearMap.mem_ker]
    change (S1ℝ - (13 : ℝ) • (1 : Matrix (Fin 58) (Fin 58) ℝ)) *ᵥ w p = 0
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]
    have hsub := (hp_eig p).2.2
    ext i
    have hi := congrFun hsub (e.symm i)
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
    dsimp [w]
    rw [← hi, ← e.sum_comp (fun j => S1ℝ i j *
      Sum.elim (Y *ᵥ e_eig p.1 p.2) ((13 - (8 - μ p.1 p.2)) • e_eig p.1 p.2) (e.symm j))]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp
  have hw_ne : ∀ p : ι, w p ≠ 0 := fun p h0 => by
    apply (hp_eig p).2.1
    ext x
    simpa [w] using congrFun h0 (e x)
  have hw_orth : ∀ p q : ι, p ≠ q → w p ⬝ᵥ w q = 0 := by
    intro p q hpq
    have he_orth : e_eig p.1 p.2 ⬝ᵥ e_eig q.1 q.2 = 0 := by
      by_cases hσ : p.1 = q.1
      · rcases p with ⟨σ1, r1⟩
        rcases q with ⟨σ2, r2⟩
        dsimp at hσ
        subst hσ
        have hr : r1 ≠ r2 := fun h => hpq (by subst h; rfl)
        rw [hedot σ1 r1 r2]
        simp [hr]
      · have hσ_ne : p.1.1 ≠ q.1.1 := fun h => hσ (Subtype.ext h)
        have hdot1 : (K_YY *ᵥ e_eig p.1 p.2) ⬝ᵥ e_eig q.1 q.2 =
            p.1.1 * (e_eig p.1 p.2 ⬝ᵥ e_eig q.1 q.2) := by
          rw [heBB, smul_dotProduct, smul_eq_mul]
        have hdot2 : (K_YY *ᵥ e_eig p.1 p.2) ⬝ᵥ e_eig q.1 q.2 =
            q.1.1 * (e_eig p.1 p.2 ⬝ᵥ e_eig q.1 q.2) := by
          have hsym : K_YYᵀ = K_YY := hermitian_transpose_eq hYY_herm
          calc
            (K_YY *ᵥ e_eig p.1 p.2) ⬝ᵥ e_eig q.1 q.2
                = e_eig q.1 q.2 ⬝ᵥ (K_YY *ᵥ e_eig p.1 p.2) := dotProduct_comm _ _
            _ = (e_eig q.1 q.2 ᵥ* K_YY) ⬝ᵥ e_eig p.1 p.2 := dotProduct_mulVec _ _ _
            _ = (K_YYᵀ *ᵥ e_eig q.1 q.2) ⬝ᵥ e_eig p.1 p.2 := by rw [Matrix.mulVec_transpose]
            _ = (K_YY *ᵥ e_eig q.1 q.2) ⬝ᵥ e_eig p.1 p.2 := by rw [hsym]
            _ = e_eig p.1 p.2 ⬝ᵥ (K_YY *ᵥ e_eig q.1 q.2) := dotProduct_comm _ _
            _ = e_eig p.1 p.2 ⬝ᵥ (q.1.1 • e_eig q.1 q.2) := by rw [heBB]
            _ = q.1.1 * (e_eig p.1 p.2 ⬝ᵥ e_eig q.1 q.2) := by rw [dotProduct_smul, smul_eq_mul]
        have hdiff : (p.1.1 - q.1.1) * (e_eig p.1 p.2 ⬝ᵥ e_eig q.1 q.2) = 0 := by linarith
        exact (mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hσ_ne)
    calc
      w p ⬝ᵥ w q = ∑ x : Fin 30 ⊕ Fin 28,
          Sum.elim (Y *ᵥ e_eig p.1 p.2) ((13 - (8 - μ p.1 p.2)) • e_eig p.1 p.2) x *
          Sum.elim (Y *ᵥ e_eig q.1 q.2) ((13 - (8 - μ q.1 q.2)) • e_eig q.1 q.2) x := by
        simpa [w, dotProduct] using (e.symm.sum_comp (fun x =>
          Sum.elim (Y *ᵥ e_eig p.1 p.2) ((13 - (8 - μ p.1 p.2)) • e_eig p.1 p.2) x *
          Sum.elim (Y *ᵥ e_eig q.1 q.2) ((13 - (8 - μ q.1 q.2)) • e_eig q.1 q.2) x))
      _ = (Y *ᵥ e_eig p.1 p.2) ⬝ᵥ (Y *ᵥ e_eig q.1 q.2) +
          ((13 - (8 - μ p.1 p.2)) • e_eig p.1 p.2) ⬝ᵥ
            ((13 - (8 - μ q.1 q.2)) • e_eig q.1 q.2) := by
        simp [Fintype.sum_sum_type, dotProduct]
      _ = (e_eig p.1 p.2 ᵥ* Yᵀ) ⬝ᵥ (Y *ᵥ e_eig q.1 q.2) +
          (13 - (8 - μ p.1 p.2)) * (13 - (8 - μ q.1 q.2)) * (e_eig p.1 p.2 ⬝ᵥ e_eig q.1 q.2) := by
        have ht := Matrix.mulVec_transpose Yᵀ (e_eig p.1 p.2)
        rw [Matrix.transpose_transpose] at ht
        rw [← ht, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, mul_assoc]
      _ = e_eig p.1 p.2 ⬝ᵥ (K_YY *ᵥ e_eig q.1 q.2) + 0 := by
        rw [← dotProduct_mulVec, Matrix.mulVec_mulVec, he_orth, mul_zero]
      _ = q.1.1 * (e_eig p.1 p.2 ⬝ᵥ e_eig q.1 q.2) + 0 := by
        rw [heBB, dotProduct_smul, smul_eq_mul]
      _ = 0 := by rw [he_orth, mul_zero, add_zero]
  have hw_li : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg p
    have hdot : (∑ q : ι, g q • w q) ⬝ᵥ w p = 0 := by rw [hg, zero_dotProduct]
    rw [sum_dotProduct] at hdot
    rw [Finset.sum_eq_single p (fun q _ hqp => by
      rw [smul_dotProduct, smul_eq_mul, hw_orth q p hqp, mul_zero])
      (fun hp => absurd (Finset.mem_univ p) hp)] at hdot
    rw [smul_dotProduct, smul_eq_mul] at hdot
    exact (mul_eq_zero.mp hdot).resolve_right (dot_self_pos_of_ne_zero (hw_ne p)).ne'
  let wK : ι → K13 := fun p => ⟨w p, hw_mem p⟩
  have hwK_li : LinearIndependent ℝ wK := by
    rw [Fintype.linearIndependent_iff]
    intro g hg p
    have hg_coe : ∑ q : ι, g q • w q = 0 := by
      have h0 := congrArg Subtype.val hg
      simpa [wK] using h0
    exact Fintype.linearIndependent_iff.mp hw_li g hg_coe p
  have hcard_le : Fintype.card ι ≤ 8 :=
    le_trans hwK_li.fintype_card_le_finrank hS1_mult13
  have hYY_eig_nonneg : ∀ k : Fin 28, 0 ≤ hYY_herm.eigenvalues k := fun k => by
    let U : Matrix (Fin 28) (Fin 28) ℝ := (hYY_herm.eigenvectorUnitary : Matrix (Fin 28) (Fin 28) ℝ)
    let u : Fin 28 → ℝ := fun i => U i k
    have hU'U : Uᵀ * U = 1 := by
      simpa [U, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self hYY_herm.eigenvectorUnitary
    have hspec : K_YY = U * Matrix.diagonal hYY_herm.eigenvalues * Uᵀ := by
      simpa [U, Matrix.star_eq_conjTranspose, RCLike.ofReal_real_eq_id] using hYY_herm.spectral_theorem
    have hu_dot : u ⬝ᵥ u = 1 := by
      have h := congrFun (congrFun hU'U k) k
      simpa [u, Matrix.mul_apply, Matrix.transpose_apply, dotProduct] using h
    have hu_eig : K_YY *ᵥ u = hYY_herm.eigenvalues k • u := by
      have hUk : Uᵀ *ᵥ u = Pi.single k 1 := by
        ext j
        have h := congrFun (congrFun hU'U j) k
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h
        simp only [Matrix.mulVec, Matrix.transpose_apply, dotProduct, u, Pi.single_apply]
        simpa [eq_comm] using h
      conv_lhs => rw [hspec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hUk]
      ext i
      simp [u, mul_comm]
    have hnonneg : 0 ≤ u ⬝ᵥ (K_YY *ᵥ u) := by
      have hYu : u ⬝ᵥ (K_YY *ᵥ u) = (Y *ᵥ u) ⬝ᵥ (Y *ᵥ u) := by
        calc
          u ⬝ᵥ (K_YY *ᵥ u) = u ⬝ᵥ (Yᵀ *ᵥ (Y *ᵥ u)) := by rw [← Matrix.mulVec_mulVec]
          _ = (u ᵥ* Yᵀ) ⬝ᵥ (Y *ᵥ u) := dotProduct_mulVec _ _ _
          _ = (Y *ᵥ u) ⬝ᵥ (Y *ᵥ u) := by
              have ht := Matrix.mulVec_transpose Yᵀ u
              rw [Matrix.transpose_transpose] at ht
              rw [← ht]
      rw [hYu]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    rw [hu_eig, dotProduct_smul, smul_eq_mul, hu_dot, mul_one] at hnonneg
    exact hnonneg
  have htr_sum : K_YY.trace = ∑ σ : posVals, (d_fn σ : ℝ) * σ.1 := by
    have htr := hYY_herm.trace_eq_sum_eigenvalues
    simp only [RCLike.ofReal_real_eq_id, id_eq] at htr
    rw [htr]
    have hfilt : (∑ k : Fin 28, hYY_herm.eigenvalues k) =
        ∑ k ∈ Finset.univ.filter (fun k : Fin 28 => 0 < hYY_herm.eigenvalues k),
          hYY_herm.eigenvalues k := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro k _ hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hk
      exact le_antisymm hk (hYY_eig_nonneg k)
    rw [hfilt]
    have hfib := Finset.sum_fiberwise_of_maps_to
      (s := Finset.univ.filter (fun k : Fin 28 => 0 < hYY_herm.eigenvalues k))
      (t := posVals) (g := hYY_herm.eigenvalues) (f := hYY_herm.eigenvalues)
      (fun k hk => Finset.mem_filter.mpr
        ⟨Finset.mem_image_of_mem _ (Finset.mem_univ k), (Finset.mem_filter.mp hk).2⟩)
    rw [← hfib, ← Finset.sum_attach posVals]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hcard_σ : (Finset.univ.filter fun k : Fin 28 => hYY_herm.eigenvalues k = σ.1).card = d_fn σ := by
      symm
      exact submatrix_eigenvalue_count_eq_finrank_ker hYY_herm σ.1
    have heq_filt :
        (Finset.univ.filter (fun k : Fin 28 => 0 < hYY_herm.eigenvalues k)).filter
          (fun k => hYY_herm.eigenvalues k = σ.1) =
        Finset.univ.filter (fun k : Fin 28 => hYY_herm.eigenvalues k = σ.1) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun ⟨_, h⟩ => h
      · intro h
        exact ⟨h ▸ (Finset.mem_filter.mp σ.2).2, h⟩
    rw [heq_filt]
    have hconst :
        ∑ k ∈ Finset.univ.filter (fun k : Fin 28 => hYY_herm.eigenvalues k = σ.1),
          hYY_herm.eigenvalues k =
        ∑ _k ∈ Finset.univ.filter (fun k : Fin 28 => hYY_herm.eigenvalues k = σ.1), σ.1 :=
      Finset.sum_congr rfl fun k hk => (Finset.mem_filter.mp hk).2
    rw [hconst, Finset.sum_const, nsmul_eq_mul, hcard_σ]
  have hbound : K_YY.trace ≤ 648 := by
    rw [htr_sum]
    have hsum_le : (∑ σ : posVals, (d_fn σ : ℝ) * σ.1) ≤ ∑ σ : posVals, (d_fn σ : ℝ) * 81 := by
      refine Finset.sum_le_sum fun σ _ => ?_
      by_cases hd0 : d_fn σ = 0
      · simp [hd0]
      · have hd_pos : 0 < d_fn σ := Nat.pos_of_ne_zero hd0
        exact mul_le_mul_of_nonneg_left (hp_eig ⟨σ, ⟨0, hd_pos⟩⟩).1 (Nat.cast_nonneg _)
    have hsum_card : (∑ σ : posVals, (d_fn σ : ℝ) * 81) = (Fintype.card ι : ℝ) * 81 := by
      have hc : (∑ σ : posVals, (d_fn σ : ℝ)) = (Fintype.card ι : ℝ) := by
        have hnat : (∑ σ : posVals, d_fn σ) = Fintype.card ι := by
          have hcard : Fintype.card ι = ∑ σ : posVals, d_fn σ := by simp [ι]
          exact hcard.symm
        exact_mod_cast hnat
      rw [← Finset.sum_mul, hc]
    have hcardR : (Fintype.card ι : ℝ) ≤ 8 := by exact_mod_cast hcard_le
    calc
      ∑ σ : posVals, (d_fn σ : ℝ) * σ.1 ≤ ∑ σ : posVals, (d_fn σ : ℝ) * 81 := hsum_le
      _ = (Fintype.card ι : ℝ) * 81 := hsum_card
      _ ≤ 8 * 81 := mul_le_mul_of_nonneg_right hcardR (by norm_num)
      _ = 648 := by norm_num
  linarith only [hFrob, hbound]

/-- **Phase 3 Unconditional Commutator/Singular-Value Elimination of `(18, 59) idx=861`:**
Any Seidel matrix `S : Matrix (Fin 59) (Fin 59) ℤ` with Eulerian row `u1` (`∀ v ≠ u1, S u1 v = 1`),
`S_{u1}` characteristic polynomial `(x - 13)^8 (x - 11)^5 (x - 9)^4 (x - 5) (x + 5)^40`, and
`30 + 28` partition `e` satisfying `(S^2)_{ij} = 1 + 8 S_{ij}` leads to `840 ≤ 648`, proving `False`. -/
theorem idx861_eliminated {S : Matrix (Fin 59) (Fin 59) ℤ} (hS : IsSeidelMatrix S)
    (u1 : Fin 59) (hrow : ∀ v : Fin 59, v ≠ u1 → S u1 v = 1)
    (hchi_u1 : (S.submatrix u1.succAbove u1.succAbove).charpoly =
      (X - C (13 : ℤ)) ^ 8 * (X - C (11 : ℤ)) ^ 5 * (X - C (9 : ℤ)) ^ 4 *
        (X - C (5 : ℤ)) * (X + C (5 : ℤ)) ^ 40)
    (e : Fin 30 ⊕ Fin 28 ≃ Fin 58)
    (h2v : ∀ (i : Fin 30) (j : Fin 28),
      (S ^ 2) (u1.succAbove (e (Sum.inl i))) (u1.succAbove (e (Sum.inr j))) =
        1 + 8 * S (u1.succAbove (e (Sum.inl i))) (u1.succAbove (e (Sum.inr j)))) :
    False := by
  let S1ℤ : Matrix (Fin 58) (Fin 58) ℤ := S.submatrix u1.succAbove u1.succAbove
  have hS1_seidel : IsSeidelMatrix S1ℤ := hS.submatrix u1.succAboveEmb
  let S1ℝ : Matrix (Fin 58) (Fin 58) ℝ := S1ℤ.map (Int.castRingHom ℝ)
  have hS1_herm : S1ℝ.IsHermitian := by
    apply isHermitian_of_transpose_eq
    ext i j; simp [S1ℝ, Matrix.transpose_apply, hS1_seidel.symm i j]
  have hchiR : S1ℝ.charpoly =
      (X - C (13 : ℝ)) ^ 8 * (X - C (11 : ℝ)) ^ 5 * (X - C (9 : ℝ)) ^ 4 *
        (X - C (5 : ℝ)) * (X + C (5 : ℝ)) ^ 40 := by
    have h1 := congrArg (Polynomial.map (Int.castRingHom ℝ)) hchi_u1
    rw [← Matrix.charpoly_map S1ℤ (Int.castRingHom ℝ)] at h1
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_pow, Polynomial.map_pow, Polynomial.map_pow,
      map_int_X_sub 13 13 (by norm_num), map_int_X_sub 11 11 (by norm_num),
      map_int_X_sub 9 9 (by norm_num), map_int_X_sub 5 5 (by norm_num),
      map_int_X_add 5 5 (by norm_num)] at h1
    exact h1
  have hspec_roots : ∀ r : ℝ, S1ℝ.charpoly.eval r = 0 →
      r = 13 ∨ r = 11 ∨ r = 9 ∨ r = 5 ∨ r = -5 := by
    intro r hr
    rw [hchiR] at hr
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, mul_eq_zero, pow_eq_zero_iff', ne_eq] at hr
    rcases hr with ((((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) | h) | ⟨h, _⟩)
    · left; linarith
    · right; left; linarith
    · right; right; left; linarith
    · right; right; right; left; linarith
    · right; right; right; right; linarith
  have hS1_mult13 := idx861_mult13_le_eight hS1_herm hchiR
  let Xℤ : Matrix (Fin 30) (Fin 30) ℤ := S1ℤ.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)
  let Yℤ : Matrix (Fin 30) (Fin 28) ℤ := S1ℤ.submatrix (e ∘ Sum.inl) (e ∘ Sum.inr)
  let Zℤ : Matrix (Fin 28) (Fin 28) ℤ := S1ℤ.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)
  let Xm : Matrix (Fin 30) (Fin 30) ℝ := Xℤ.map (Int.castRingHom ℝ)
  let Y : Matrix (Fin 30) (Fin 28) ℝ := Yℤ.map (Int.castRingHom ℝ)
  let Zm : Matrix (Fin 28) (Fin 28) ℝ := Zℤ.map (Int.castRingHom ℝ)
  have hX_herm : Xm.IsHermitian := by
    apply isHermitian_of_transpose_eq
    ext i j; simp [Xm, Xℤ, Matrix.transpose_apply, hS1_seidel.symm]
  have hZ_herm : Zm.IsHermitian := by
    apply isHermitian_of_transpose_eq
    ext i j; simp [Zm, Zℤ, Matrix.transpose_apply, hS1_seidel.symm]
  have hPerm : S1ℝ.submatrix e e = Matrix.fromBlocks Xm Y Yᵀ Zm := by
    ext a b
    cases a with
    | inl i =>
      cases b with
      | inl j => simp [S1ℝ, Xm, Xℤ, Matrix.fromBlocks_apply₁₁]
      | inr j => simp [S1ℝ, Y, Yℤ, Matrix.fromBlocks_apply₁₂]
    | inr i =>
      cases b with
      | inl j => simp [S1ℝ, Y, Yℤ, Matrix.fromBlocks_apply₂₁, Matrix.transpose_apply, hS1_seidel.symm]
      | inr j => simp [S1ℝ, Zm, Zℤ, Matrix.fromBlocks_apply₂₂]
  have hS1_sq : ∀ a b : Fin 58,
      (S ^ 2) (u1.succAbove a) (u1.succAbove b) = 1 + (S1ℤ ^ 2) a b := fun a b => by
    rw [sq, sq, Matrix.mul_apply, Matrix.mul_apply]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ u1)]
    have hfirst : S (u1.succAbove a) u1 * S u1 (u1.succAbove b) = 1 := by
      rw [hS.symm u1 (u1.succAbove a), hrow _ (Fin.succAbove_ne u1 a),
        hrow _ (Fin.succAbove_ne u1 b), one_mul]
    have himg : Finset.univ.erase u1 = Finset.univ.image u1.succAbove := by
      ext j
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_image, true_and]
      exact ⟨Fin.exists_succAbove_eq, fun ⟨t, ht⟩ => ht ▸ Fin.succAbove_ne u1 t⟩
    rw [hfirst, himg, Finset.sum_image (fun t1 _ t2 _ h => Fin.succAbove_right_injective h)]
    rfl
  have hrel : Xm * Y + Y * Zm = (8 : ℝ) • Y := by
    ext i j
    have h1 := h2v i j
    rw [hS1_sq (e (Sum.inl i)) (e (Sum.inr j))] at h1
    have h2 : (S1ℤ ^ 2) (e (Sum.inl i)) (e (Sum.inr j)) =
        8 * S1ℤ (e (Sum.inl i)) (e (Sum.inr j)) := by
      dsimp [S1ℤ]; linarith
    rw [sq, Matrix.mul_apply, ← e.sum_comp (fun x => S1ℤ (e (Sum.inl i)) x * S1ℤ x (e (Sum.inr j)))] at h2
    simp only [Fintype.sum_sum_type] at h2
    have h2R : (((∑ x : Fin 30, S1ℤ (e (Sum.inl i)) (e (Sum.inl x)) *
          S1ℤ (e (Sum.inl x)) (e (Sum.inr j)) +
        ∑ x : Fin 28, S1ℤ (e (Sum.inl i)) (e (Sum.inr x)) *
          S1ℤ (e (Sum.inr x)) (e (Sum.inr j)) : ℤ) : ℝ)) =
        (8 : ℝ) * (S1ℤ (e (Sum.inl i)) (e (Sum.inr j)) : ℝ) := by exact_mod_cast h2
    simpa [Xm, Xℤ, Y, Yℤ, Zm, Zℤ, Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply,
      smul_eq_mul] using h2R
  have hFrob : (Yᵀ * Y).trace = 840 := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
    have hsq1 : ∀ (u : Fin 28) (w : Fin 30), Y w u * Y w u = 1 := fun u w => by
      have hne : e (Sum.inl w) ≠ e (Sum.inr u) := fun h => by
        have := e.injective h; cases this
      rcases hS1_seidel.offDiag_eq_one_or_neg_one hne with h1 | h1 <;> simp [Y, Yℤ, h1]
    simp_rw [hsq1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    norm_num
  exact idx861_pos_eig_bound hX_herm hZ_herm e hPerm hspec_roots hS1_mult13 hrel hFrob

end Kills47And861

section ResolventIdx13

/-- **General `k`-Minor Jacobi Complementary Minor Identity (`[CommRing R]`):**
For any partition `e : Fin k ⊕ Fin m ≃ Fin n` (`U = e ∘ Sum.inl`, `V = e ∘ Sum.inr`),
`det A * det (adjugate A)[U, U] = (det A) ^ k * det A[V, V]`. -/
theorem jacobi_k_complementary_minor {R : Type*} [CommRing R] {k m n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (e : Fin k ⊕ Fin m ≃ Fin n) :
    A.det * (A.adjugate.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)).det =
      A.det ^ k * (A.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)).det := by
  let P : Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) R := A.submatrix e e
  let Q : Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) R := A.adjugate.submatrix e e
  let A11 := A.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)
  let A12 := A.submatrix (e ∘ Sum.inl) (e ∘ Sum.inr)
  let A21 := A.submatrix (e ∘ Sum.inr) (e ∘ Sum.inl)
  let A22 := A.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)
  let Q11 := A.adjugate.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)
  let Q12 := A.adjugate.submatrix (e ∘ Sum.inl) (e ∘ Sum.inr)
  let Q21 := A.adjugate.submatrix (e ∘ Sum.inr) (e ∘ Sum.inl)
  let Q22 := A.adjugate.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)
  have hP_blk : P = Matrix.fromBlocks A11 A12 A21 A22 := by
    ext a b; rcases a with i | i <;> rcases b with j | j <;> rfl
  have hQ_blk : Q = Matrix.fromBlocks Q11 Q12 Q21 Q22 := by
    ext a b; rcases a with i | i <;> rcases b with j | j <;> rfl
  have hPQ : P * Q = A.det • (1 : Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) R) := by
    ext a b
    simp only [P, Q, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    rw [e.sum_comp (fun j => A (e a) j * A.adjugate j (e b))]
    have hmul := congrFun (congrFun (Matrix.mul_adjugate A) (e a)) (e b)
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at hmul
    rw [hmul]
    by_cases hab : a = b <;> simp [hab, e.injective.eq_iff]
  have h11 : A11 * Q11 + A12 * Q21 = A.det • (1 : Matrix (Fin k) (Fin k) R) := by
    ext i j
    have hij := congrFun (congrFun hPQ (Sum.inl i)) (Sum.inl j)
    rw [hP_blk, hQ_blk, Matrix.fromBlocks_multiply] at hij
    simpa [Matrix.fromBlocks_apply₁₁, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] using hij
  have h21 : A21 * Q11 + A22 * Q21 = (0 : Matrix (Fin m) (Fin k) R) := by
    ext i j
    have hij := congrFun (congrFun hPQ (Sum.inr i)) (Sum.inl j)
    rw [hP_blk, hQ_blk, Matrix.fromBlocks_multiply] at hij
    simpa [Matrix.fromBlocks_apply₂₁, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] using hij
  let L : Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) R := Matrix.fromBlocks Q11 0 Q21 1
  have hPL : P * L = Matrix.fromBlocks (A.det • (1 : Matrix (Fin k) (Fin k) R)) A12 0 A22 := by
    rw [hP_blk]
    dsimp [L]
    rw [Matrix.fromBlocks_multiply, h11, h21]
    simp [Matrix.mul_zero, Matrix.mul_one]
  have hdet := congrArg Matrix.det hPL
  rw [Matrix.det_mul, Matrix.det_submatrix_equiv_self e A] at hdet
  have hL_det : L.det = Q11.det := by
    dsimp [L]
    rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]
  have hR_det : (Matrix.fromBlocks (A.det • (1 : Matrix (Fin k) (Fin k) R)) A12 0 A22).det =
      A.det ^ k * A22.det := by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one]
  rwa [hL_det, hR_det] at hdet

/-- Minimal polynomial `(x + 5)(x - 11)(x - 15)(x - 17)` for `(19, 74) idx=13`. -/
noncomputable def idx13MinPoly : ℤ[X] :=
  (X + C (5 : ℤ)) * (X - C (11 : ℤ)) * (X - C (15 : ℤ)) * (X - C (17 : ℤ))

/-- Explicit cleared-denominator polynomial resolvent `M(x, S)` satisfying
`(x I - S) * M(x, S) = m(x) I` whenever `m(S) = 0`. -/
noncomputable def idx13Resolvent {n : ℕ} (S : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin n) (Fin n) ℤ[X] :=
  ((X - C (11 : ℤ)) * (X - C (17 : ℤ))) • ((X - C (10 : ℤ)) • 1 + S.map C) -
    ((X - C (28 : ℤ)) • 1 + S.map C) *
      ((C (75 : ℤ) : ℤ[X]) • 1 + (C (10 : ℤ) : ℤ[X]) • S.map C - (S.map C) ^ 2)

/-- Any symmetric integer matrix `S` whose characteristic polynomial has roots only in
`{-5, 11, 15, 17}` satisfies the squarefree minimal polynomial `(S + 5I)(S - 11I)(S - 15I)(S - 17I) = 0`. -/
theorem idx13_minimal_poly_of_charpoly {n : ℕ} {S : Matrix (Fin n) (Fin n) ℤ}
    (hS_sym : Sᵀ = S)
    (hchar : S.charpoly = (X + C 5) ^ 55 * (X - C 11) ^ 3 * (X - C 15) ^ 15 * (X - C 17)) :
    (S + (5 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)) * (S - (11 : ℤ) • 1) *
      (S - (15 : ℤ) • 1) * (S - (17 : ℤ) • 1) = 0 := by
  let Sℝ : Matrix (Fin n) (Fin n) ℝ := S.map (Int.castRingHom ℝ)
  have hS_herm : Sℝ.IsHermitian := by
    apply isHermitian_of_transpose_eq
    ext i j
    simp only [Sℝ, Matrix.transpose_apply, Matrix.map_apply, eq_intCast]
    exact congrArg (Int.cast : ℤ → ℝ) (congrFun (congrFun hS_sym i) j)
  have hchiR : Sℝ.charpoly =
      (X + C (5 : ℝ)) ^ 55 * (X - C (11 : ℝ)) ^ 3 * (X - C (15 : ℝ)) ^ 15 * (X - C (17 : ℝ)) := by
    have h1 := congrArg (Polynomial.map (Int.castRingHom ℝ)) hchar
    rw [← Matrix.charpoly_map S (Int.castRingHom ℝ)] at h1
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_pow, Polynomial.map_pow,
      map_int_X_add 5 5 (by norm_num), map_int_X_sub 11 11 (by norm_num),
      map_int_X_sub 15 15 (by norm_num), map_int_X_sub 17 17 (by norm_num)] at h1
    exact h1
  have heig_mem : ∀ k : Fin n,
      (hS_herm.eigenvalues k + 5) * (hS_herm.eigenvalues k - 11) *
        (hS_herm.eigenvalues k - 15) * (hS_herm.eigenvalues k - 17) = 0 := fun k => by
    have hch : Sℝ.charpoly = ∏ j : Fin n, (X - C (hS_herm.eigenvalues j)) := by
      simpa [RCLike.ofReal_real_eq_id] using hS_herm.charpoly_eq
    have hrt : Sℝ.charpoly.eval (hS_herm.eigenvalues k) = 0 := by
      rw [hch, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
    rw [hchiR] at hrt
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, mul_eq_zero, pow_eq_zero_iff', ne_eq] at hrt
    rcases hrt with (((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) | h) <;> simp [h]
  let U : Matrix (Fin n) (Fin n) ℝ := (hS_herm.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  have hUU : U * Uᵀ = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self hS_herm.eigenvectorUnitary
  have hU'U : Uᵀ * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self hS_herm.eigenvectorUnitary
  have hspec : Sℝ = U * Matrix.diagonal hS_herm.eigenvalues * Uᵀ := by
    simpa [U, Matrix.star_eq_conjTranspose, RCLike.ofReal_real_eq_id] using hS_herm.spectral_theorem
  have hconj : ∀ (p : ℝ[X]), Polynomial.aeval Sℝ p =
      U * Matrix.diagonal (fun k => p.eval (hS_herm.eigenvalues k)) * Uᵀ := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p1 p2 ih1 ih2 =>
      simp only [map_add, ih1, ih2, Polynomial.eval_add]
      rw [← Matrix.add_mul, ← Matrix.mul_add]
      congr 2
      ext a b; by_cases hab : a = b <;> simp [hab]
    | monomial d c =>
      have hpow : Sℝ ^ d = U * Matrix.diagonal (fun k => (hS_herm.eigenvalues k) ^ d) * Uᵀ := by
        induction d with
        | zero =>
          simpa using hUU.symm
        | succ d' ih =>
          rw [pow_succ, ih]
          conv_lhs => rhs; rw [hspec]
          calc
            (U * Matrix.diagonal (fun k => hS_herm.eigenvalues k ^ d') * Uᵀ) *
                (U * Matrix.diagonal hS_herm.eigenvalues * Uᵀ)
                = U * Matrix.diagonal (fun k => hS_herm.eigenvalues k ^ d') * (Uᵀ * U) *
                    Matrix.diagonal hS_herm.eigenvalues * Uᵀ := by
                  simp only [Matrix.mul_assoc]
            _ = U * (Matrix.diagonal (fun k => hS_herm.eigenvalues k ^ d') *
                    Matrix.diagonal hS_herm.eigenvalues) * Uᵀ := by
                  rw [hU'U, Matrix.mul_one]
                  simp only [Matrix.mul_assoc]
            _ = U * Matrix.diagonal (fun k => hS_herm.eigenvalues k ^ (d' + 1)) * Uᵀ := by
                  congr 2
                  ext a b
                  by_cases hab : a = b <;> simp [hab, pow_succ]
      simp only [Polynomial.aeval_monomial, Polynomial.eval_monomial, hpow,
        Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul]
      rw [← Matrix.smul_mul, ← Matrix.mul_smul]
      congr 2
      ext a b
      by_cases hab : a = b <;> simp [hab, smul_eq_mul]
  have hprodR : (Sℝ + (5 : ℝ) • 1) * (Sℝ - (11 : ℝ) • 1) *
      (Sℝ - (15 : ℝ) • 1) * (Sℝ - (17 : ℝ) • 1) = 0 := by
    have haev : Polynomial.aeval Sℝ ((X + C (5 : ℝ)) * (X - C 11) * (X - C 15) * (X - C 17)) = 0 := by
      rw [hconj]
      have hdiag0 : Matrix.diagonal (fun k => ((X + C (5 : ℝ)) * (X - C 11) * (X - C 15) * (X - C 17)).eval
          (hS_herm.eigenvalues k)) = 0 := by
        ext a b
        by_cases hab : a = b
        · subst hab
          simp only [Matrix.diagonal_apply_eq, Matrix.zero_apply, Polynomial.eval_mul,
            Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
          exact heig_mem a
        · simp [hab]
      rw [hdiag0, Matrix.mul_zero, Matrix.zero_mul]
    simpa only [map_mul, map_add, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one] using haev
  let M : Matrix (Fin n) (Fin n) ℤ :=
    (S + (5 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)) * (S - (11 : ℤ) • 1) *
      (S - (15 : ℤ) • 1) * (S - (17 : ℤ) • 1)
  have hM_map : M.map (Int.castRingHom ℝ) = 0 := by
    let φ : Matrix (Fin n) (Fin n) ℤ →+* Matrix (Fin n) (Fin n) ℝ :=
      (Int.castRingHom ℝ).mapMatrix
    have hsm : ∀ (c : ℤ) (A : Matrix (Fin n) (Fin n) ℤ),
        φ (c • A) = (c : ℝ) • φ A := fun c A => by
      apply Matrix.ext; intro a b
      simp [-zsmul_eq_mul, φ, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply,
        smul_eq_mul]
    change φ M = 0
    dsimp [M]
    simp only [map_mul, map_add, map_sub, map_one, hsm]
    exact hprodR
  apply Matrix.ext; intro i j
  have hij := congrFun (congrFun hM_map i) j
  simp only [Matrix.map_apply, eq_intCast, Matrix.zero_apply] at hij
  have hij' : M i j = 0 := Int.cast_eq_zero.mp hij
  exact hij'

/-- **De Caen–Jacobi Resolvent Identity:**
`(X • 1 - S.map C) * idx13Resolvent S = idx13MinPoly • 1` whenever
`(S + 5I)(S - 11I)(S - 15I)(S - 17I) = 0`. -/
theorem idx13_resolvent_identity {n : ℕ} (S : Matrix (Fin n) (Fin n) ℤ)
    (hmin : (S + (5 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)) * (S - (11 : ℤ) • 1) *
      (S - (15 : ℤ) • 1) * (S - (17 : ℤ) • 1) = 0) :
    S.charmatrix * idx13Resolvent S = idx13MinPoly • (1 : Matrix (Fin n) (Fin n) ℤ[X]) := by
  let x : ℤ[X][X] := Polynomial.C (Polynomial.X : ℤ[X])
  let y : ℤ[X][X] := (Polynomial.X : ℤ[X][X])
  let M_poly : ℤ[X][X] :=
    (x - 11) * (x - 17) * ((x - 10) + y) - ((x - 28) + y) * (75 + 10 * y - y ^ 2)
  let mx : ℤ[X][X] := (x + 5) * (x - 11) * (x - 15) * (x - 17)
  let my : ℤ[X][X] := (y + 5) * (y - 11) * (y - 15) * (y - 17)
  have hid : (x - y) * M_poly = mx - my := by
    dsimp [x, y, M_poly, mx, my]
    ring
  let SC : Matrix (Fin n) (Fin n) ℤ[X] := S.map C
  have hmap := congrArg (Polynomial.aeval SC) hid
  have hlhs1 : Polynomial.aeval SC (x - y) = S.charmatrix := by
    simp only [x, y, map_sub, Polynomial.aeval_C, Polynomial.aeval_X,
      Algebra.algebraMap_eq_smul_one]
    apply Matrix.ext; intro i j
    by_cases hij : i = j <;> simp [SC, Matrix.charmatrix, Matrix.scalar_apply, hij]
  have hC_aeval : ∀ p : ℤ[X], Polynomial.aeval SC (Polynomial.C p) = p • (1 : Matrix (Fin n) (Fin n) ℤ[X]) :=
    fun p => by simp [Algebra.algebraMap_eq_smul_one]
  have h_ofNat : ∀ (k : ℕ) [k.AtLeastTwo],
      Polynomial.aeval SC (OfNat.ofNat k : ℤ[X][X]) =
        (C (OfNat.ofNat k : ℤ)) • (1 : Matrix (Fin n) (Fin n) ℤ[X]) := fun k _ => by
    rw [← map_ofNat (C : ℤ[X] →+* ℤ[X][X]) k, hC_aeval, map_ofNat]
  have hx_sub : ∀ (k : ℕ) [k.AtLeastTwo],
      Polynomial.aeval SC (x - OfNat.ofNat k) =
        (X - C (OfNat.ofNat k : ℤ)) • (1 : Matrix (Fin n) (Fin n) ℤ[X]) := fun k _ => by
    dsimp [x]
    rw [map_sub, hC_aeval, h_ofNat, ← sub_smul]
  have hx_add : ∀ (k : ℕ) [k.AtLeastTwo],
      Polynomial.aeval SC (x + OfNat.ofNat k) =
        (X + C (OfNat.ofNat k : ℤ)) • (1 : Matrix (Fin n) (Fin n) ℤ[X]) := fun k _ => by
    dsimp [x]
    rw [map_add, hC_aeval, h_ofNat, ← add_smul]
  have hlhs2 : Polynomial.aeval SC M_poly = idx13Resolvent S := by
    have hr2 : Polynomial.aeval SC (75 + 10 * y - y ^ 2) =
        (C (75 : ℤ) : ℤ[X]) • (1 : Matrix (Fin n) (Fin n) ℤ[X]) +
          (C (10 : ℤ) : ℤ[X]) • S.map C - (S.map C) ^ 2 := by
      dsimp [y]
      rw [map_sub, map_add, h_ofNat 75, map_mul, h_ofNat 10, Polynomial.aeval_X,
        map_pow, Polynomial.aeval_X, Matrix.smul_mul, Matrix.one_mul]
    dsimp [M_poly, idx13Resolvent]
    rw [map_sub, map_mul, map_mul, hx_sub 11, hx_sub 17, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, smul_smul, map_add, hx_sub 10, Polynomial.aeval_X, Matrix.smul_mul,
      Matrix.one_mul, map_mul, map_add, hx_sub 28, Polynomial.aeval_X, hr2]
  have hrhs1 : Polynomial.aeval SC mx = idx13MinPoly • (1 : Matrix (Fin n) (Fin n) ℤ[X]) := by
    dsimp [mx, idx13MinPoly]
    rw [map_mul, map_mul, map_mul, hx_add 5, hx_sub 11, hx_sub 15, hx_sub 17]
    simp only [Matrix.smul_mul, Matrix.one_mul, smul_smul]
  have hrhs2 : Polynomial.aeval SC my = 0 := by
    let ψ : Matrix (Fin n) (Fin n) ℤ →+* Matrix (Fin n) (Fin n) ℤ[X] := C.mapMatrix
    have hsm : ∀ (c : ℤ) (A : Matrix (Fin n) (Fin n) ℤ),
        ψ (c • A) = (C c : ℤ[X]) • ψ A := fun c A => by
      apply Matrix.ext; intro a b
      simp [-zsmul_eq_mul, ψ, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply,
        smul_eq_mul]
    have hmy : Polynomial.aeval SC my =
        ψ ((S + (5 : ℤ) • 1) * (S - (11 : ℤ) • 1) * (S - (15 : ℤ) • 1) * (S - (17 : ℤ) • 1)) := by
      dsimp [my, y]
      simp only [map_mul, map_add, map_sub, map_one, hsm, Polynomial.aeval_X, h_ofNat]
      simp only [SC, ψ, RingHom.mapMatrix_apply]
    rw [hmy, hmin, map_zero]
  rw [map_mul, hlhs1, hlhs2, map_sub, hrhs1, hrhs2, sub_zero] at hmap
  exact hmap

/-- Evaluating the `(19, 74) idx=13` resolvent at `X = 15` gives `(S + 5I)(S - 11I)(S - 17I)`. -/
theorem idx13_resolvent_at_15 {n : ℕ} (S : Matrix (Fin n) (Fin n) ℤ) :
    (idx13Resolvent S).map (Polynomial.eval 15) =
      (S + (5 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)) * (S - (11 : ℤ) • 1) * (S - (17 : ℤ) • 1) := by
  let p1 : ℤ[X] := C (-8 : ℤ) * (X + C 5) - (X - C 13) * (C 75 + C 10 * X - X ^ 2)
  let p2 : ℤ[X] := (X + C 5) * (X - C 11) * (X - C 17)
  have hp : p1 = p2 := by
    dsimp [p1, p2]
    simp only [map_neg, map_ofNat]
    ring
  have hmap := congrArg (Polynomial.aeval S) hp
  let ev : Matrix (Fin n) (Fin n) ℤ[X] →+* Matrix (Fin n) (Fin n) ℤ :=
    (Polynomial.evalRingHom (15 : ℤ)).mapMatrix
  have hev_SC : ev (S.map C) = S := by
    apply Matrix.ext; intro i j
    simp [ev, RingHom.mapMatrix_apply]
  have hev_smul : ∀ (q : ℤ[X]) (A : Matrix (Fin n) (Fin n) ℤ[X]),
      ev (q • A) = q.eval 15 • ev A := fun q A => by
    apply Matrix.ext; intro a b
    simp [ev, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  have hv1 : ((X - C (11 : ℤ)) * (X - C (17 : ℤ))).eval 15 = (-8 : ℤ) := by
    norm_num [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hv2 : (X - C (10 : ℤ)).eval 15 = (5 : ℤ) := by
    norm_num [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hv3 : (X - C (28 : ℤ)).eval 15 = (-13 : ℤ) := by
    norm_num [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have he1 : (idx13Resolvent S).map (Polynomial.eval 15) = Polynomial.aeval S p1 := by
    change ev (idx13Resolvent S) = Polynomial.aeval S p1
    dsimp [idx13Resolvent, p1]
    simp only [map_sub, map_mul, map_add, map_pow, map_one, hev_smul, hev_SC, hv1, hv2, hv3,
      Polynomial.eval_C, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mul, Matrix.one_mul]
    rw [add_comm ((5 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)) S,
      show (-13 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) = -((13 : ℤ) • 1) from neg_smul 13 1,
      add_comm (-((13 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ))) S, ← sub_eq_add_neg]
  have he2 : Polynomial.aeval S p2 =
      (S + (5 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)) * (S - (11 : ℤ) • 1) * (S - (17 : ℤ) • 1) := by
    dsimp [p2]
    simp only [map_mul, map_add, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one]
  rw [he1, hmap, he2]

private lemma adjugate_eq_smul_resolvent {n : ℕ} {A R : Matrix (Fin n) (Fin n) ℤ[X]}
    {p q : ℤ[X]} (hq : q.Monic) (hdet : A.det = p * q) (hAR : A * R = q • 1) :
    A.adjugate = p • R := by
  have h1 : A.adjugate * (A * R) = A.det • R := by
    rw [← Matrix.mul_assoc, Matrix.adjugate_mul]
    change (A.det • (1 : Matrix (Fin n) (Fin n) ℤ[X])) * R = A.det • R
    rw [Matrix.smul_mul, Matrix.one_mul]
  rw [hAR, Matrix.mul_smul, Matrix.mul_one, hdet, mul_comm p q, mul_smul] at h1
  apply Matrix.ext; intro i j
  have hij := congrFun (congrFun h1 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at hij ⊢
  exact hq.isRegular.left hij

private lemma pole_cancel_poly_helper (Mdet Vcdet Q_co Q_ch : ℤ[X]) (k : ℕ) (_hk : 15 < k)
    (hQco : Q_co = (X + C 5) ^ 54 * (X - C 11) ^ 2)
    (hq : Q_co ^ k * Mdet = (X - C (15 : ℤ)) ^ (k - 15) * (Q_ch ^ (k - 1) * Vcdet)) :
    (X - C (15 : ℤ)) ^ (k - 15) ∣ Mdet := by
  let P15 : ℤ[X] := (X - C (15 : ℤ)) ^ (k - 15)
  have hP15_mon : P15.Monic := (Polynomial.monic_X_sub_C _).pow _
  let φ : ℤ[X] →+* ℚ[X] := Polynomial.mapRingHom (Int.castRingHom ℚ)
  have hmap_eq : φ Q_co ^ k * φ Mdet = φ P15 * (φ Q_ch ^ (k - 1) * φ Vcdet) := by
    have h1 := congrArg φ hq
    simpa only [P15, map_mul, map_pow] using h1
  have hcop5 : IsCoprime (X - C (15 : ℚ)) (X + C (5 : ℚ)) := by
    refine ⟨C (-1 / 20 : ℚ), C (1 / 20 : ℚ), ?_⟩
    calc
      C (-1 / 20 : ℚ) * (X - C (15 : ℚ)) + C (1 / 20 : ℚ) * (X + C (5 : ℚ))
          = (C (-1 / 20 : ℚ) + C (1 / 20 : ℚ)) * X +
              (C (1 / 20 : ℚ) * C (5 : ℚ) - C (-1 / 20 : ℚ) * C (15 : ℚ)) := by ring
      _ = 0 * X + C (1 : ℚ) := by
            simp only [← Polynomial.C_add, ← Polynomial.C_mul, ← Polynomial.C_sub]
            norm_num
      _ = 1 := by simp
  have hcop11 : IsCoprime (X - C (15 : ℚ)) (X - C (11 : ℚ)) := by
    refine ⟨C (-1 / 4 : ℚ), C (1 / 4 : ℚ), ?_⟩
    calc
      C (-1 / 4 : ℚ) * (X - C (15 : ℚ)) + C (1 / 4 : ℚ) * (X - C (11 : ℚ))
          = (C (-1 / 4 : ℚ) + C (1 / 4 : ℚ)) * X +
              (-C (1 / 4 : ℚ) * C (11 : ℚ) - C (-1 / 4 : ℚ) * C (15 : ℚ)) := by ring
      _ = 0 * X + C (1 : ℚ) := by
            simp only [← Polynomial.C_neg, ← Polynomial.C_add, ← Polynomial.C_mul, ← Polynomial.C_sub]
            norm_num
      _ = 1 := by simp
  have hcop_Q : IsCoprime (φ P15) (φ Q_co ^ k) := by
    have hP15_q : φ P15 = (X - C (15 : ℚ)) ^ (k - 15) := by
      dsimp [P15, φ]
      rw [Polynomial.map_pow, map_int_X_sub_rat 15 15 (by norm_num)]
    have hQco_q : φ Q_co = (X + C (5 : ℚ)) ^ 54 * (X - C (11 : ℚ)) ^ 2 := by
      rw [hQco]
      dsimp [φ]
      rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow,
        map_int_X_add_rat 5 5 (by norm_num), map_int_X_sub_rat 11 11 (by norm_num)]
    rw [hP15_q, hQco_q]
    have h54 : IsCoprime (X - C (15 : ℚ)) ((X + C (5 : ℚ)) ^ 54) := hcop5.pow_right
    have h2 : IsCoprime (X - C (15 : ℚ)) ((X - C (11 : ℚ)) ^ 2) := hcop11.pow_right
    exact ((h54.mul_right h2).pow_right).pow_left
  have hdvd_Q : φ P15 ∣ φ Mdet :=
    hcop_Q.dvd_of_dvd_mul_left ⟨φ Q_ch ^ (k - 1) * φ Vcdet, hmap_eq⟩
  have hrem0 : Mdet %ₘ P15 = 0 := by
    have hdecomp : Mdet %ₘ P15 + P15 * (Mdet /ₘ P15) = Mdet :=
      Polynomial.modByMonic_add_div Mdet P15
    have hdvd_rem : φ P15 ∣ φ (Mdet %ₘ P15) := by
      have heq : φ (Mdet %ₘ P15) = φ Mdet - φ P15 * φ (Mdet /ₘ P15) := by
        rw [← congrArg φ hdecomp, map_add, map_mul]; ring
      rw [heq]
      exact dvd_sub hdvd_Q (dvd_mul_right _ _)
    have hdeg_lt : (φ (Mdet %ₘ P15)).degree < (φ P15).degree := by
      have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
      have hr : (Mdet %ₘ P15).degree < P15.degree :=
        Polynomial.degree_modByMonic_lt Mdet hP15_mon
      change ((Mdet %ₘ P15).map (Int.castRingHom ℚ)).degree < (P15.map (Int.castRingHom ℚ)).degree
      rwa [Polynomial.degree_map_eq_of_injective hinj, Polynomial.degree_map_eq_of_injective hinj]
    have hzero_q : φ (Mdet %ₘ P15) = 0 :=
      Polynomial.eq_zero_of_dvd_of_degree_lt hdvd_rem hdeg_lt
    exact Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
      (by simpa [φ] using hzero_q)
  exact ⟨Mdet /ₘ P15, by
    calc
      Mdet = Mdet %ₘ P15 + P15 * (Mdet /ₘ P15) := (Polynomial.modByMonic_add_div Mdet P15).symm
      _ = P15 * (Mdet /ₘ P15) := by rw [hrem0, zero_add]⟩

private lemma idx13_cancel_jacobi_powers (Mdet Vcdet : ℤ[X]) (k : ℕ) (_hk : 15 ≤ k)
    (P_co Q_co Q_ch A_char : ℤ[X])
    (hmon_char : A_char.Monic)
    (hP_co_eq : P_co = Q_co * (X - C (15 : ℤ)) ^ 14)
    (hchar_eq : A_char = Q_ch * (X - C (15 : ℤ)) ^ 15)
    (hjac : A_char * (P_co ^ k * Mdet) = A_char ^ k * Vcdet) :
    Q_co ^ k * Mdet = (X - C (15 : ℤ)) ^ (k - 15) * (Q_ch ^ (k - 1) * Vcdet) := by
  have hk1 : 1 ≤ k := by omega
  have hjac1 : P_co ^ k * Mdet = A_char ^ (k - 1) * Vcdet := by
    apply hmon_char.isRegular.left
    dsimp only
    rw [hjac, ← mul_assoc, ← pow_succ', show k - 1 + 1 = k by omega]
  have hlhs : P_co ^ k * Mdet = (X - C (15 : ℤ)) ^ (14 * k) * (Q_co ^ k * Mdet) := by
    rw [hP_co_eq, mul_pow, ← pow_mul]
    ring
  have hrhs : A_char ^ (k - 1) * Vcdet =
      (X - C (15 : ℤ)) ^ (14 * k) * ((X - C (15 : ℤ)) ^ (k - 15) * (Q_ch ^ (k - 1) * Vcdet)) := by
    rw [hchar_eq, mul_pow, ← pow_mul]
    have hexp : 15 * (k - 1) = 14 * k + (k - 15) := by omega
    rw [hexp, pow_add]
    ring
  have h15_mon : ((X - C (15 : ℤ)) ^ (14 * k)).Monic := (Polynomial.monic_X_sub_C _).pow _
  apply h15_mon.isRegular.left
  dsimp only
  rw [← hlhs, ← hrhs]
  exact hjac1

/-- **De Caen–Jacobi Pole Cancellation at `x = 15` (`(19, 74) idx=13`):**
For any vertex subset `V` of size `k ≥ 15` (via `e : Fin k ⊕ Fin m ≃ Fin 74`),
`(X - C 15) ^ (k - 15) ∣ det((idx13Resolvent S)[V, V])` in `ℤ[X]`. -/
theorem idx13_pole_cancellation_at_15 {S : Matrix (Fin 74) (Fin 74) ℤ} (hS : IsSeidelMatrix S)
    (hchar : S.charpoly = (X + C 5) ^ 55 * (X - C 11) ^ 3 * (X - C 15) ^ 15 * (X - C 17))
    {k m : ℕ} (hk : 15 ≤ k) (e : Fin k ⊕ Fin m ≃ Fin 74) :
    (X - C (15 : ℤ)) ^ (k - 15) ∣
      ((idx13Resolvent S).submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)).det := by
  have hS_sym : Sᵀ = S := by
    ext i j
    exact hS.symm i j
  have hmin := idx13_minimal_poly_of_charpoly hS_sym hchar
  have hres := idx13_resolvent_identity S hmin
  let Q_co : ℤ[X] := (X + C 5) ^ 54 * (X - C 11) ^ 2
  let P_co : ℤ[X] := Q_co * (X - C 15) ^ 14
  let Q_ch : ℤ[X] := (X + C 5) ^ 55 * (X - C 11) ^ 3 * (X - C 17)
  have hP_co_eq : P_co = Q_co * (X - C 15) ^ 14 := rfl
  have hchar_split : S.charmatrix.det = P_co * idx13MinPoly := by
    change S.charpoly = P_co * idx13MinPoly
    rw [hchar]
    dsimp [P_co, Q_co, idx13MinPoly]
    have hsplit (a b c d : ℤ[X]) :
        a ^ 55 * b ^ 3 * c ^ 15 * d = (a ^ 54 * b ^ 2 * c ^ 14) * (a * b * c * d) := by
      rw [pow_succ a 54, pow_succ b 2, pow_succ c 14]
      ac_rfl
    exact hsplit _ _ _ _
  have hidx_mon : idx13MinPoly.Monic := by
    dsimp [idx13MinPoly]
    exact (((Polynomial.monic_X_add_C _).mul (Polynomial.monic_X_sub_C _)).mul
      (Polynomial.monic_X_sub_C _)).mul (Polynomial.monic_X_sub_C _)
  have hadj_eq : S.charmatrix.adjugate = P_co • idx13Resolvent S :=
    adjugate_eq_smul_resolvent hidx_mon hchar_split hres
  by_cases hk15 : k = 15
  · subst hk15
    simp
  have hk_gt : 15 < k := Nat.lt_of_le_of_ne hk (Ne.symm hk15)
  let V := e ∘ Sum.inl
  let Vc := e ∘ Sum.inr
  have hchar_eq : S.charpoly = Q_ch * (X - C 15) ^ 15 := by
    rw [hchar]
    dsimp [Q_ch]
    ac_rfl
  have hjac := jacobi_k_complementary_minor S.charmatrix e
  have hdet_char : S.charmatrix.det = S.charpoly := rfl
  rw [hdet_char] at hjac
  have hsub_adj : (S.charmatrix.adjugate.submatrix V V).det =
      P_co ^ k * ((idx13Resolvent S).submatrix V V).det := by
    have hsm : S.charmatrix.adjugate.submatrix V V = P_co • ((idx13Resolvent S).submatrix V V) := by
      rw [hadj_eq]
      rfl
    rw [hsm, Matrix.det_smul, Fintype.card_fin]
  rw [hsub_adj] at hjac
  have hq_cancel := idx13_cancel_jacobi_powers (((idx13Resolvent S).submatrix V V).det)
    ((S.charmatrix.submatrix Vc Vc).det) k hk P_co Q_co Q_ch S.charpoly
    (Matrix.charpoly_monic S) hP_co_eq hchar_eq hjac
  exact pole_cancel_poly_helper (((idx13Resolvent S).submatrix V V).det)
    ((S.charmatrix.submatrix Vc Vc).det) Q_co Q_ch k hk_gt rfl hq_cancel

end ResolventIdx13

section RankObstruction488

/-- Any finite family of pairwise orthogonal nonzero vectors in `Fin n → ℝ` is linearly independent. -/
theorem pairwise_orth_linearIndependent {n : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → Fin n → ℝ) (hne : ∀ i, w i ≠ 0) (horth : ∀ i j, i ≠ j → w i ⬝ᵥ w j = 0) :
    LinearIndependent ℝ w := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hdot : (∑ j : ι, g j • w j) ⬝ᵥ w i = 0 := by rw [hg, zero_dotProduct]
  rw [sum_dotProduct] at hdot
  rw [Finset.sum_eq_single i (fun j _ hji => by
    rw [smul_dotProduct, smul_eq_mul, horth j i hji, mul_zero])
    (fun hi => absurd (Finset.mem_univ i) hi)] at hdot
  rw [smul_dotProduct, smul_eq_mul] at hdot
  exact (mul_eq_zero.mp hdot).resolve_right (dot_self_pos_of_ne_zero (hne i)).ne'

/-- **Rank Lower Bound from Linearly Independent Nonzero-Eigenvalue Eigenvectors:**
Any `m` linearly independent eigenvectors of `A` with nonzero eigenvalues force `m ≤ A.rank`. -/
theorem disjoint_eigenvectors_rank_ge {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin m → Fin n → ℝ) (c : Fin m → ℝ)
    (hli : LinearIndependent ℝ v) (hc : ∀ i, c i ≠ 0) (heig : ∀ i, A *ᵥ v i = c i • v i) :
    m ≤ A.rank := by
  have hmem : ∀ i : Fin m, v i ∈ LinearMap.range A.mulVecLin := fun i => by
    refine ⟨(c i)⁻¹ • v i, ?_⟩
    change A *ᵥ ((c i)⁻¹ • v i) = v i
    rw [Matrix.mulVec_smul, heig i, smul_smul, inv_mul_cancel₀ (hc i), one_smul]
  let vR : Fin m → LinearMap.range A.mulVecLin := fun i => ⟨v i, hmem i⟩
  have hvR_li : LinearIndependent ℝ vR := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hg0 : ∑ j : Fin m, g j • v j = 0 := by
      have hsub := congrArg Subtype.val hg
      simpa [vR] using hsub
    exact Fintype.linearIndependent_iff.mp hli g hg0 i
  simpa [Matrix.rank] using hvR_li.fintype_card_le_finrank

/-- **Hermitian Trace Cauchy–Schwarz Inequality (`(Tr T)^2 ≤ rk(T) * Tr(T^2)`):** -/
theorem hermitian_trace_sq_le_rank_mul_trace_mul {n : ℕ} {T : Matrix (Fin n) (Fin n) ℝ}
    (hT : T.IsHermitian) :
    (T.trace) ^ 2 ≤ (T.rank : ℝ) * (T * T).trace := by
  let s : Finset (Fin n) := Finset.univ.filter fun k => hT.eigenvalues k ≠ 0
  have hrank_eq : T.rank = s.card := by
    rw [hT.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  have htr1 : T.trace = ∑ k ∈ s, hT.eigenvalues k := by
    have htr := hT.trace_eq_sum_eigenvalues
    simp only [RCLike.ofReal_real_eq_id, id_eq] at htr
    rw [htr]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k _ hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hk
    exact hk
  have htr2 : (T * T).trace = ∑ k : Fin n, hT.eigenvalues k ^ 2 := by
    let U : Matrix (Fin n) (Fin n) ℝ := (hT.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
    have hU'U : Uᵀ * U = 1 := by
      simpa [U, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self hT.eigenvectorUnitary
    have hspec : T = U * Matrix.diagonal hT.eigenvalues * Uᵀ := by
      simpa [U, Matrix.star_eq_conjTranspose, RCLike.ofReal_real_eq_id] using hT.spectral_theorem
    have hT2 : T * T = (U * Matrix.diagonal (fun k => hT.eigenvalues k ^ 2)) * Uᵀ := by
      calc
        T * T = (U * Matrix.diagonal hT.eigenvalues * Uᵀ) *
            (U * Matrix.diagonal hT.eigenvalues * Uᵀ) := by
          conv_lhs => rw [hspec]
        _ = U * Matrix.diagonal hT.eigenvalues * (Uᵀ * U) *
            Matrix.diagonal hT.eigenvalues * Uᵀ := by
          simp only [Matrix.mul_assoc]
        _ = U * (Matrix.diagonal hT.eigenvalues * Matrix.diagonal hT.eigenvalues) * Uᵀ := by
          rw [hU'U, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
        _ = (U * Matrix.diagonal (fun k => hT.eigenvalues k ^ 2)) * Uᵀ := by
          congr 2
          ext a b
          by_cases hab : a = b <;> simp [hab, sq]
    rw [hT2, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU'U, Matrix.one_mul]
    simp [Matrix.trace, Matrix.diag_apply]
  have hcs := sq_sum_le_card_mul_sum_sq (s := s) (f := hT.eigenvalues)
  have hsub : (∑ k ∈ s, hT.eigenvalues k ^ 2) ≤ (T * T).trace := by
    rw [htr2]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun k _ _ => sq_nonneg _)
  rw [← htr1, ← hrank_eq] at hcs
  exact le_trans hcs (mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg _))

/-- **Surgical `(18, 59) idx=488` Rank Obstruction:**
Any symmetric idempotent `E : Matrix (Fin 59) (Fin 59) ℝ` with `rank(E) ≤ 7` having a `20`-vertex
block `B` (`E_{uu} = 1/8`), a disjoint `24`-vertex block `C5` (`|E_{uw}| = 1/16`), and
`E_{uz} = 0` outside `B ∪ C5` yields `Tr(E[B, B]) = 5/2` and `Tr(E[B, B]^2) = 5/8`, contradicting
`(5/2)^2 ≤ 7 * (5/8)`. -/
theorem idx488_rank_obstruction {E : Matrix (Fin 59) (Fin 59) ℝ}
    (hE_sym : Eᵀ = E) (hE_idem : E * E = E) (hE_rank : E.rank ≤ 7)
    (B : Fin 20 ↪ Fin 59) (C5 : Fin 24 ↪ Fin 59)
    (hdisj : ∀ (u : Fin 20) (w : Fin 24), B u ≠ C5 w)
    (hdiag : ∀ u : Fin 20, E (B u) (B u) = 1 / 8)
    (hC5 : ∀ (u : Fin 20) (w : Fin 24), |E (B u) (C5 w)| = 1 / 16)
    (hout : ∀ (u : Fin 20) (z : Fin 59),
      (∀ v : Fin 20, z ≠ B v) → (∀ w : Fin 24, z ≠ C5 w) → E (B u) z = 0) :
    False := by
  let T : Matrix (Fin 20) (Fin 20) ℝ := E.submatrix B B
  have hT_herm : T.IsHermitian := by
    apply isHermitian_of_transpose_eq
    ext i j
    simp only [T, Matrix.transpose_apply, Matrix.submatrix_apply]
    exact congrFun (congrFun hE_sym (B i)) (B j)
  let P : Matrix (Fin 59) (Fin 20) ℝ := Matrix.of fun i j => if i = B j then 1 else 0
  have hT_eq : T = Pᵀ * E * P := by
    ext u v
    simp only [T, P, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.of_apply]
    have hright : ∀ j : Fin 59,
        (∑ x : Fin 59, (if x = B u then (1 : ℝ) else 0) * E x j) = E (B u) j := fun j => by
      rw [Finset.sum_eq_single (B u) (fun x _ hx => by simp [hx])
        (fun h => absurd (Finset.mem_univ (B u)) h)]
      simp
    simp_rw [hright]
    rw [Finset.sum_eq_single (B v) (fun j _ hj => by simp [hj])
      (fun h => absurd (Finset.mem_univ (B v)) h)]
    simp
  have hT_rank : T.rank ≤ 7 := by
    rw [hT_eq]
    exact le_trans (Matrix.rank_mul_le_left _ _) (le_trans (Matrix.rank_mul_le_right _ _) hE_rank)
  have hT_tr : T.trace = 5 / 2 := by
    simp only [T, Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply, hdiag,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  have hrow_sq : ∀ u : Fin 20, (∑ v : Fin 20, E (B u) (B v) ^ 2) = 1 / 32 := fun u => by
    have hE2 : (E * E) (B u) (B u) = 1 / 8 := by rw [hE_idem, hdiag u]
    rw [Matrix.mul_apply] at hE2
    have hsq_sym : ∑ z : Fin 59, E (B u) z * E z (B u) = ∑ z : Fin 59, E (B u) z ^ 2 := by
      refine Finset.sum_congr rfl fun z _ => ?_
      have hsym_z : E z (B u) = E (B u) z := by
        simpa [Matrix.transpose_apply] using congrFun (congrFun hE_sym (B u)) z
      rw [hsym_z, sq]
    rw [hsq_sym] at hE2
    let sB : Finset (Fin 59) := Finset.univ.image B
    let sC : Finset (Fin 59) := Finset.univ.image C5
    have hs_disj : Disjoint sB sC := by
      rw [Finset.disjoint_left]
      intro z hzB hzC
      rcases Finset.mem_image.mp hzB with ⟨v, _, rfl⟩
      rcases Finset.mem_image.mp hzC with ⟨w, _, hw⟩
      exact hdisj v w hw.symm
    have hsum_sub : ∑ z : Fin 59, E (B u) z ^ 2 =
        (∑ z ∈ sB, E (B u) z ^ 2) + ∑ z ∈ sC, E (B u) z ^ 2 := by
      rw [← Finset.sum_union hs_disj]
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro z _ hz
      rw [Finset.mem_union, not_or] at hz
      have hnotB : ∀ v : Fin 20, z ≠ B v := fun v hv =>
        hz.1 (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, hv.symm⟩)
      have hnotC : ∀ w : Fin 24, z ≠ C5 w := fun w hw =>
        hz.2 (Finset.mem_image.mpr ⟨w, Finset.mem_univ w, hw.symm⟩)
      rw [hout u z hnotB hnotC, sq, mul_zero]
    have hB_sum : ∑ z ∈ sB, E (B u) z ^ 2 = ∑ v : Fin 20, E (B u) (B v) ^ 2 :=
      Finset.sum_image (fun v1 _ v2 _ h => B.injective h)
    have hC_sum : ∑ z ∈ sC, E (B u) z ^ 2 = 3 / 32 := by
      rw [Finset.sum_image (fun w1 _ w2 _ h => C5.injective h)]
      have hterm : ∀ w : Fin 24, E (B u) (C5 w) ^ 2 = 1 / 256 := fun w => by
        have habs := hC5 u w
        rw [← sq_abs, habs]
        norm_num
      simp_rw [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num
    rw [hsum_sub, hB_sum, hC_sum] at hE2
    linarith
  have hT2_tr : (T * T).trace = 5 / 8 := by
    have hT2_eq : (T * T).trace = ∑ u : Fin 20, ∑ v : Fin 20, E (B u) (B v) ^ 2 := by
      simp only [T, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.submatrix_apply]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      have hsym_vu : E (B v) (B u) = E (B u) (B v) := by
        simpa [Matrix.transpose_apply] using congrFun (congrFun hE_sym (B u)) (B v)
      rw [hsym_vu, sq]
    rw [hT2_eq]
    simp_rw [hrow_sq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  have hcs := hermitian_trace_sq_le_rank_mul_trace_mul hT_herm
  rw [hT_tr, hT2_tr] at hcs
  have hT_rankR : (T.rank : ℝ) ≤ 7 := by exact_mod_cast hT_rank
  nlinarith

end RankObstruction488

end EquiangularLines

end
