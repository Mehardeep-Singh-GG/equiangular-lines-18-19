import EquiangularLines.Basic
import EquiangularLines.Seidel
import EquiangularLines.LemmensSeidel
import EquiangularLines.Bounds
import EquiangularLines.Spectral
import EquiangularLines.TwoAdic
import EquiangularLines.Multiplicity
import EquiangularLines.SRG136
import EquiangularLines.Obstructions
import EquiangularLines.GaloisObstructions
import EquiangularLines.Phase3Algebra
import EquiangularLines.CertKernel
import EquiangularLines.Certs19_74A
import EquiangularLines.Certs19_74B
import EquiangularLines.Certs19_74C
import EquiangularLines.Certificates
import EquiangularLines.Main

/-!
# Axiom Audit for `EquiangularLines`

Every exported theorem across `Basic`, `Seidel`, `LemmensSeidel`, `Bounds`, and `Spectral`
is checked with `#print axioms` to confirm reliance strictly on the standard Lean axioms
(`propext`, `Classical.choice`, `Quot.sound`) — zero `sorryAx`, zero `Lean.ofReduceBool`,
zero `Lean.trustCompiler`, zero custom axioms.
-/

-- Basic.lean
#print axioms EquiangularLines.isEquiangularSystem_iff_ne_pm
#print axioms EquiangularLines.isEquiangularSystem_iff_distinct_lines
#print axioms EquiangularLines.card_le_dim_of_alpha_zero
#print axioms EquiangularLines.alpha_pos_of_dim_lt
#print axioms EquiangularLines.not_isEquiangularSystem_zero_dim
#print axioms EquiangularLines.IsEquiangularSystem.comp_embedding
#print axioms EquiangularLines.IsEquiangularSystem.sign_flip

-- Seidel.lean
#print axioms EquiangularLines.IsSeidelMatrix.trace_eq_zero
#print axioms EquiangularLines.IsSeidelMatrix.sq_diag
#print axioms EquiangularLines.IsSeidelMatrix.trace_sq
#print axioms EquiangularLines.IsSeidelMatrix.submatrix
#print axioms EquiangularLines.IsSeidelMatrix.switch_isSeidelMatrix
#print axioms EquiangularLines.IsSeidelMatrix.switch_charpoly
#print axioms EquiangularLines.seidelGram_isHermitian
#print axioms EquiangularLines.gramMatrix_eq_transpose_mul_self
#print axioms EquiangularLines.gramMatrix_posSemidef
#print axioms EquiangularLines.gramMatrix_rank_le
#print axioms EquiangularLines.equiangularSystem_to_seidel
#print axioms EquiangularLines.seidel_to_equiangularSystem
#print axioms EquiangularLines.hasEquiangularLinesWithAngle_iff_seidel
#print axioms EquiangularLines.seidelGram_charpoly
#print axioms EquiangularLines.pow_sub_rank_dvd_charpoly
#print axioms EquiangularLines.seidelGram_dvd_charpoly_real
#print axioms EquiangularLines.seidelGram_dvd_charpoly_int

-- LemmensSeidel.lean
#print axioms EquiangularLines.lemmens_seidel_bound

-- Bounds.lean
#print axioms EquiangularLines.gerzon_bound
#print axioms EquiangularLines.relative_bound_mul
#print axioms EquiangularLines.relative_bound
#print axioms EquiangularLines.neumann_theorem
#print axioms EquiangularLines.phase1_frontier_forces_one_fifth

-- Spectral.lean
#print axioms EquiangularLines.seidel_charpoly_factorization
#print axioms EquiangularLines.seidel_five_trace_int
#print axioms EquiangularLines.seidel_five_trace_sq_int
#print axioms EquiangularLines.seidel_five_trace
#print axioms EquiangularLines.seidel_five_trace_sq
#print axioms EquiangularLines.seidel_charpoly_coeff_sub_one
#print axioms EquiangularLines.two_mul_seidel_charpoly_coeff_sub_two
#print axioms EquiangularLines.seidel_charpoly_coeff_sub_two
#print axioms EquiangularLines.shifted_factor_nonneg_roots
#print axioms EquiangularLines.shifted_factor_trace_coeffs
#print axioms EquiangularLines.det_add_vecMulVec
#print axioms EquiangularLines.det_sub_vecMulVec
#print axioms EquiangularLines.two_dvd_det_of_symm_diag_zero_odd
#print axioms EquiangularLines.seidel_shifted_charpoly_two_adic_aux
#print axioms EquiangularLines.seidel_shifted_charpoly_two_adic
#print axioms EquiangularLines.seidel_shifted_charpoly_two_adic_even
#print axioms EquiangularLines.two_pow_sub_one_dvd_charpoly_two_mul_sub_one
#print axioms EquiangularLines.two_pow_factor_dvd_cofactor_comp
#print axioms EquiangularLines.exists_compl_equiv_pair
#print axioms EquiangularLines.jacobi_complementary_minor
#print axioms EquiangularLines.charmatrix_adjugate_diag
#print axioms EquiangularLines.derivative_charpoly_eq_sum_adjugate_diag
#print axioms EquiangularLines.derivative_charpoly_eq_sum_vertex_deletions
#print axioms EquiangularLines.jacobi_two_vertex_charpoly
#print axioms EquiangularLines.cauchy_interlacing

-- Phase 2: TwoAdic
#print axioms EquiangularLines.even_order_two_pow_dvd_charpoly
#print axioms EquiangularLines.skew_det_eq_sq
#print axioms EquiangularLines.odd_order_two_adic_congruence

-- Phase 2: Multiplicity
#print axioms EquiangularLines.even_order_cofactor_two_pow_dvd
#print axioms EquiangularLines.cofactor_comp_two_mul_add_odd_even
#print axioms EquiangularLines.cofactor_comp_two_mul_add_odd_odd
#print axioms EquiangularLines.odd_order_cofactor_two_adic_congruence
#print axioms EquiangularLines.seidel_cofactor_trace_diff_eq
#print axioms EquiangularLines.gsy_multiplicity_bound_even
#print axioms EquiangularLines.gsy_multiplicity_bound_odd
#print axioms EquiangularLines.frontier_18_59_mult_11
#print axioms EquiangularLines.frontier_19_74_mult_15
#print axioms EquiangularLines.frontier_17_49_mult_9
#print axioms EquiangularLines.frontier_18_60_mult_11

-- Phase 2: SRG136
#print axioms EquiangularLines.isSRG_of_matrix_eq
#print axioms EquiangularLines.isSRG_matrix_eq
#print axioms EquiangularLines.idx136_implies_SRG_75_32_10_16
#print axioms EquiangularLines.SRG_75_32_10_16_implies_idx136
#print axioms EquiangularLines.idx136_eliminated_of_not_existsSRG

-- Phase 2: Obstructions
#print axioms EquiangularLines.even_order_seidel_zmod2_charpoly
#print axioms EquiangularLines.odd_order_seidel_zmod2_charpoly
#print axioms EquiangularLines.even_eig_mult_even_order_eq_zero
#print axioms EquiangularLines.even_eig_mult_odd_order_le_one
#print axioms EquiangularLines.exists_hensel_root_mod_two_pow
#print axioms EquiangularLines.even_root_mod_four_eq_sub_one
#print axioms EquiangularLines.strict_type2_eval_mod_eight
#print axioms EquiangularLines.weapon_b_vertex_deletion_mod_eight
#print axioms EquiangularLines.weapon_b_vertex_deletion_odd
#print axioms EquiangularLines.weapon_b_padicVal_zero
#print axioms EquiangularLines.weapon_b_derivative_mod_eight
#print axioms EquiangularLines.jacobi_square_class_mod_charpoly
#print axioms EquiangularLines.psd_submatrix_kernel_extends
#print axioms EquiangularLines.ker_submatrix_vanish_of_nullity_gt

-- Phase 3: GaloisObstructions
#print axioms EquiangularLines.exists_unique_eulerian_switch
#print axioms EquiangularLines.eulerian_switch_sq_mod_four
#print axioms EquiangularLines.simple_eig_projector_adjugate
#print axioms EquiangularLines.simple_eig_projector_diag
#print axioms EquiangularLines.galois_orthogonality_of_orth_vectors
#print axioms EquiangularLines.galois_orthogonality_trace_constraint
#print axioms EquiangularLines.ker_submatrix_preserves_nullity
#print axioms EquiangularLines.submatrix_nullity_ge_sub
#print axioms EquiangularLines.submatrix_nullity_ge_of_vertex_deletions
#print axioms EquiangularLines.submatrix_eigenvalue_count_eq_finrank_ker
#print axioms EquiangularLines.submatrix_trace_cauchy_schwarz_obstruction

-- Phase 3: Phase3Algebra
#print axioms EquiangularLines.block_commutator_sim_eig
#print axioms EquiangularLines.symm_block_quadratic_eigenvalues
#print axioms EquiangularLines.idx47_eliminated
#print axioms EquiangularLines.idx861_eliminated
#print axioms EquiangularLines.jacobi_k_complementary_minor
#print axioms EquiangularLines.idx13_minimal_poly_of_charpoly
#print axioms EquiangularLines.idx13_resolvent_identity
#print axioms EquiangularLines.idx13_resolvent_at_15
#print axioms EquiangularLines.idx13_pole_cancellation_at_15
#print axioms EquiangularLines.pairwise_orth_linearIndependent
#print axioms EquiangularLines.disjoint_eigenvectors_rank_ge
#print axioms EquiangularLines.hermitian_trace_sq_le_rank_mul_trace_mul
#print axioms EquiangularLines.idx488_rank_obstruction

-- Phase 3: Pure-Kernel Certificate Verification & Certificates
#print axioms EquiangularLines.Certs.Certs19_74A_all_ok
#print axioms EquiangularLines.Certs.Certs19_74B_all_ok
#print axioms EquiangularLines.Certs.Certs19_74C_all_ok
#print axioms EquiangularLines.farkas_infeasible_nonneg
#print axioms EquiangularLines.farkas_infeasible_box
#print axioms EquiangularLines.polyOfDescList_coeff
#print axioms EquiangularLines.checkCertZ_sound
#print axioms EquiangularLines.charpoly_eliminated_of_deck_farkas
#print axioms EquiangularLines.certs19_74_all_147_verified

-- Phase 3: Main
#print axioms EquiangularLines.frontier_19_74_reduction
#print axioms EquiangularLines.frontier_18_59_reduction
#print axioms EquiangularLines.frontier_19_74_core_cases_eliminated
#print axioms EquiangularLines.frontier_18_59_core_cases_eliminated
#print axioms EquiangularLines.frontier_19_74_no_lines_of_srg_and_cert_exhaustion
#print axioms EquiangularLines.frontier_18_59_no_lines_of_cert_exhaustion
