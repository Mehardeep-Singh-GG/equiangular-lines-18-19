module

public import EquiangularLines.SRG136
public import EquiangularLines.Certificates

/-!
# Frontier Equiangular Lines Master Composition (`ℝ¹⁸` and `ℝ¹⁹`)

This module composes Phase 1 (`Basic`, `Seidel`, `Bounds`), Phase 2 (`TwoAdic`,
`Multiplicity`, `SRG136`, `Obstructions`), and Phase 3 (`GaloisObstructions`,
`Phase3Algebra`, `CertKernel`, `Certs19_74A/B/C`, `Certificates`) into clean
end-to-end theorems for the two frontier cases `(18, 59)` and `(19, 74)`.

## Integrity & Explicit Hypotheses
- Zero `sorry`, zero custom axioms, zero `native_decide`.
- All remaining non-formalized external steps (namely `¬ ExistsSRG 75 32 10 16` for
  `(19, 74) idx=136` and the exhaustive finite spectral/polytope census reductions
  connecting arbitrary Seidel realizations to the verified Farkas decks / algebraic
  obstruction configurations) are stated explicitly as theorem hypotheses.
-/

@[expose] public section

open Matrix Polynomial
open scoped BigOperators

namespace EquiangularLines

/-- Characteristic polynomial of the `(19, 74) idx=136` survivor `(x+5)^55 (x-15)^17 (x-11) (x-9)`. -/
noncomputable def idx136Charpoly : ℤ[X] :=
  (X + C (5 : ℤ)) ^ 55 * (X - C (15 : ℤ)) ^ 17 * (X - C (11 : ℤ)) * (X - C (9 : ℤ))

/-- Characteristic polynomial of `(19, 74) idx=47`: `(x-15)^12 (x-11) (x+5)^55 (x^2 - 28x + 191)^3`. -/
noncomputable def idx47Charpoly : ℤ[X] :=
  (X - C (15 : ℤ)) ^ 12 * (X - C (11 : ℤ)) * (X + C (5 : ℤ)) ^ 55 *
    (X ^ 2 - C (28 : ℤ) * X + C (191 : ℤ)) ^ 3

/-- Block realization predicate for `(19, 74) idx=47` (used in `idx47_eliminated`). -/
def RealizesIdx47Block (S : Matrix (Fin 74) (Fin 74) ℤ) : Prop :=
  ∃ e : Fin 58 ⊕ Fin 16 ≃ Fin 74,
    S *ᵥ (fun k => match e.symm k with | Sum.inl _ => (0 : ℤ) | Sum.inr _ => 1) =
      (11 : ℤ) • (fun k => match e.symm k with | Sum.inl _ => (0 : ℤ) | Sum.inr _ => 1) ∧
    ∀ (w : Fin 58) (u : Fin 16),
      (S ^ 2) (e (Sum.inl w)) (e (Sum.inr u)) = 10 * S (e (Sum.inl w)) (e (Sum.inr u))

/-- Block realization predicate for `(18, 59) idx=861` (used in `idx861_eliminated`). -/
def RealizesIdx861Block (S : Matrix (Fin 59) (Fin 59) ℤ) : Prop :=
  ∃ (u1 : Fin 59) (e : Fin 30 ⊕ Fin 28 ≃ Fin 58),
    (∀ v : Fin 59, v ≠ u1 → S u1 v = 1) ∧
    (S.submatrix u1.succAbove u1.succAbove).charpoly =
      (X - C (13 : ℤ)) ^ 8 * (X - C (11 : ℤ)) ^ 5 * (X - C (9 : ℤ)) ^ 4 *
        (X - C (5 : ℤ)) * (X + C (5 : ℤ)) ^ 40 ∧
    ∀ (i : Fin 30) (j : Fin 28),
      (S ^ 2) (u1.succAbove (e (Sum.inl i))) (u1.succAbove (e (Sum.inr j))) =
        1 + 8 * S (u1.succAbove (e (Sum.inl i))) (u1.succAbove (e (Sum.inr j)))

/-- Spectral projector realization predicate for `(18, 59) idx=488` (`idx488_rank_obstruction`). -/
def RealizesIdx488Proj (S : Matrix (Fin 59) (Fin 59) ℤ) : Prop :=
  ∃ (E : Matrix (Fin 59) (Fin 59) ℝ) (B : Fin 20 ↪ Fin 59) (C5 : Fin 24 ↪ Fin 59),
    E * S.map (Int.castRingHom ℝ) = S.map (Int.castRingHom ℝ) * E ∧
    Eᵀ = E ∧ E * E = E ∧ E.rank ≤ 7 ∧
    (∀ (u : Fin 20) (w : Fin 24), B u ≠ C5 w) ∧
    (∀ u : Fin 20, E (B u) (B u) = 1 / 8) ∧
    (∀ (u : Fin 20) (w : Fin 24), |E (B u) (C5 w)| = 1 / 16) ∧
    (∀ (u : Fin 20) (z : Fin 59),
      (∀ v : Fin 20, z ≠ B v) → (∀ w : Fin 24, z ≠ C5 w) → E (B u) z = 0)

/-- Existence of a pure-kernel verified `Certs.checkCertZ` deck refutation for a Seidel matrix of order `m + 1`. -/
def RealizesVerifiedFarkasDeck {m : ℕ} (S : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) : Prop :=
  ∃ (φ : ℤ[X] →+* ℚ[X]) (G : ℚ[X]) (rhs y : List ℤ) (cols : List (List ℤ)) (c : ℚ),
    G ≠ 0 ∧
    Certs.checkCertZ rhs y cols = true ∧
    φ S.charpoly.derivative * C c = G * polyOfDescList rhs ∧
    ∀ u : Fin (m + 1), ∃ col ∈ cols, col.length = rhs.length ∧
      φ (S.submatrix u.succAbove u.succAbove).charpoly * C c = G * polyOfDescList col

/-- Phase 1 + Phase 2 reduction for `(19, 74)`: any system yields a `74 × 74` Seidel matrix `S`
with `(1/5) I + S / 5` PSD of rank `≤ 19` and `(x - 15)^6 (x + 5)^55 ∣ charpoly S`. -/
theorem frontier_19_74_reduction (h : HasEquiangularLines 19 74) :
    ∃ S : Matrix (Fin 74) (Fin 74) ℤ,
      IsSeidelMatrix S ∧
      (seidelGram (1 / 5 : ℝ) S).PosSemidef ∧
      (seidelGram (1 / 5 : ℝ) S).rank ≤ 19 ∧
      ∃ Q : ℤ[X], Q.Monic ∧ Q.natDegree = 19 ∧
        S.charpoly = (X + C (5 : ℤ)) ^ 55 * Q ∧
        (X - C (15 : ℤ)) ^ 6 ∣ Q := by
  rcases h with ⟨α, v, hsys⟩
  obtain ⟨_, S, hS, hpsd, hrk, _⟩ :=
    phase1_frontier_forces_one_fifth (Or.inr ⟨rfl, Or.inl rfl⟩) hsys
  exact ⟨S, hS, hpsd, hrk, frontier_19_74_mult_15 hS hpsd hrk⟩

/-- Phase 1 + Phase 2 reduction for `(18, 59)`: any system yields a `59 × 59` Seidel matrix `S`
with `(1/5) I + S / 5` PSD of rank `≤ 18` and `(x - 11) (x + 5)^41 ∣ charpoly S`. -/
theorem frontier_18_59_reduction (h : HasEquiangularLines 18 59) :
    ∃ S : Matrix (Fin 59) (Fin 59) ℤ,
      IsSeidelMatrix S ∧
      (seidelGram (1 / 5 : ℝ) S).PosSemidef ∧
      (seidelGram (1 / 5 : ℝ) S).rank ≤ 18 ∧
      ∃ Q : ℤ[X], Q.Monic ∧ Q.natDegree = 18 ∧
        S.charpoly = (X + C (5 : ℤ)) ^ 41 * Q ∧
        (X - C (11 : ℤ)) ^ 1 ∣ Q := by
  rcases h with ⟨α, v, hsys⟩
  obtain ⟨_, S, hS, hpsd, hrk, _⟩ :=
    phase1_frontier_forces_one_fifth (Or.inl ⟨rfl, Or.inl rfl⟩) hsys
  exact ⟨S, hS, hpsd, hrk, frontier_18_59_mult_11 hS hpsd hrk⟩

/-- Lean-verified elimination of the core `(19, 74)` configurations (`idx=136` under `¬ ExistsSRG`,
`idx=47` block structure, and any `Certs.checkCertZ`-certified vertex-deletion Farkas deck). -/
theorem frontier_19_74_core_cases_eliminated
    (hno_srg : ¬ ExistsSRG 75 32 10 16)
    {S : Matrix (Fin 74) (Fin 74) ℤ} (hS : IsSeidelMatrix S) :
    S.charpoly ≠ idx136Charpoly ∧
    ¬ (S.charpoly = idx47Charpoly ∧ RealizesIdx47Block S) ∧
    ¬ RealizesVerifiedFarkasDeck S := by
  refine ⟨?_, ?_, ?_⟩
  · exact idx136_eliminated_of_not_existsSRG hno_srg hS
  · rintro ⟨hchi, e, hv11, h2v⟩
    exact idx47_eliminated hS hchi e hv11 h2v
  · rintro ⟨φ, G, rhs, y, cols, c, hG, hchk, hrhs, hcols⟩
    exact charpoly_eliminated_of_deck_farkas S φ G hG c hchk hrhs hcols

/-- Lean-verified elimination of the core `(18, 59)` configurations (`idx=861` block structure,
`idx=488` rank-`≤ 7` projector structure, and any `Certs.checkCertZ`-certified Farkas deck). -/
theorem frontier_18_59_core_cases_eliminated
    {S : Matrix (Fin 59) (Fin 59) ℤ} (hS : IsSeidelMatrix S) :
    ¬ RealizesIdx861Block S ∧
    ¬ RealizesIdx488Proj S ∧
    ¬ RealizesVerifiedFarkasDeck S := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨u1, e, hrow, hchi_u1, h2v⟩
    exact idx861_eliminated hS u1 hrow hchi_u1 e h2v
  · rintro ⟨E, B, C5, _, hE_sym, hE_idem, hE_rank, hdisj, hdiag, hC5, hout⟩
    exact idx488_rank_obstruction hE_sym hE_idem hE_rank B C5 hdisj hdiag hC5 hout
  · rintro ⟨φ, G, rhs, y, cols, c, hG, hchk, hrhs, hcols⟩
    exact charpoly_eliminated_of_deck_farkas S φ G hG c hchk hrhs hcols

/-- **Conditional Master Frontier Theorem for `(19, 74)` (`N(19) < 74`):**
Composes Phase 1–3 (`phase1_frontier_forces_one_fifth`, `frontier_19_74_mult_15`,
`idx136_eliminated_of_not_existsSRG`, `idx47_eliminated`, `charpoly_eliminated_of_deck_farkas`)
with the explicit `¬ ExistsSRG 75 32 10 16` hypothesis and explicit finite-census exhaustion
hypothesis covering any surviving `(19, 74)` realization. Also bundled with pure-kernel
verification `certs19_74_all_147_verified` of all `147` Stage-2 `1-vertex_farkas` decks. -/
theorem frontier_19_74_no_lines_of_srg_and_cert_exhaustion
    (hno_srg : ¬ ExistsSRG 75 32 10 16)
    (hexh : ∀ S : Matrix (Fin 74) (Fin 74) ℤ,
      IsSeidelMatrix S →
      (seidelGram (1 / 5 : ℝ) S).PosSemidef →
      (seidelGram (1 / 5 : ℝ) S).rank ≤ 19 →
      (∃ Q : ℤ[X], Q.Monic ∧ Q.natDegree = 19 ∧
        S.charpoly = (X + C (5 : ℤ)) ^ 55 * Q ∧ (X - C (15 : ℤ)) ^ 6 ∣ Q) →
      S.charpoly = idx136Charpoly ∨
      (S.charpoly = idx47Charpoly ∧ RealizesIdx47Block S) ∨
      RealizesVerifiedFarkasDeck S) :
    ¬ HasEquiangularLines 19 74 ∧
    (Certs.Certs19_74A_spec ∧ Certs.Certs19_74B_spec ∧ Certs.Certs19_74C_spec) := by
  refine ⟨?_, ?_⟩
  · intro hlines
    obtain ⟨S, hS, hpsd, hrk, hQ⟩ := frontier_19_74_reduction hlines
    obtain ⟨hn136, hn47, hnfark⟩ := frontier_19_74_core_cases_eliminated hno_srg hS
    rcases hexh S hS hpsd hrk hQ with h136 | h47 | hfark
    · exact hn136 h136
    · exact hn47 h47
    · exact hnfark hfark
  · exact ⟨certs19_74_all_147_verified.1, certs19_74_all_147_verified.2.1,
      certs19_74_all_147_verified.2.2.1⟩

/-- **Conditional Master Frontier Theorem for `(18, 59)` (`N(18) < 59`):**
Composes Phase 1–3 (`phase1_frontier_forces_one_fifth`, `frontier_18_59_mult_11`,
`idx861_eliminated`, `idx488_rank_obstruction`, `charpoly_eliminated_of_deck_farkas`)
with the explicit finite-census exhaustion hypothesis covering any surviving `(18, 59)`
realization. -/
theorem frontier_18_59_no_lines_of_cert_exhaustion
    (hexh : ∀ S : Matrix (Fin 59) (Fin 59) ℤ,
      IsSeidelMatrix S →
      (seidelGram (1 / 5 : ℝ) S).PosSemidef →
      (seidelGram (1 / 5 : ℝ) S).rank ≤ 18 →
      (∃ Q : ℤ[X], Q.Monic ∧ Q.natDegree = 18 ∧
        S.charpoly = (X + C (5 : ℤ)) ^ 41 * Q ∧ (X - C (11 : ℤ)) ^ 1 ∣ Q) →
      RealizesIdx861Block S ∨
      RealizesIdx488Proj S ∨
      RealizesVerifiedFarkasDeck S) :
    ¬ HasEquiangularLines 18 59 := by
  intro hlines
  obtain ⟨S, hS, hpsd, hrk, hQ⟩ := frontier_18_59_reduction hlines
  obtain ⟨hn861, hn488, hnfark⟩ := frontier_18_59_core_cases_eliminated hS
  rcases hexh S hS hpsd hrk hQ with h861 | h488 | hfark
  · exact hn861 h861
  · exact hn488 h488
  · exact hnfark hfark

end EquiangularLines

end
