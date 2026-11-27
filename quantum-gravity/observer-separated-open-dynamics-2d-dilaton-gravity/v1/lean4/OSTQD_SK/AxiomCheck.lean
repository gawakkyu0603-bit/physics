import OSTQD_SK

/-!
# OSTQD_SK.AxiomCheck

Audits that every public theorem in OSTQD_SK (all 34 public declarations) depends
exclusively on Lean 4's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`)
with zero `sorryAx` and zero custom axioms.
-/

-- Basic.lean (7)
#print axioms OSTQD_SK.trace_gksl_eq_zero
#print axioms OSTQD_SK.gksl_dual_adj
#print axioms OSTQD_SK.sk_quadratic_tp_normalization
#print axioms OSTQD_SK.sk_quadratic_conjugation_symmetry
#print axioms OSTQD_SK.sk_quadratic_im_nonneg
#print axioms OSTQD_SK.sk_fdt_wightman_rates
#print axioms OSTQD_SK.layer2_unraveling_gauge_nonuniqueness

-- Theorem1_CovariantKMS.lean (8)
#print axioms OSTQD_SK.eigenoperator_two_time_commutation
#print axioms OSTQD_SK.eigenoperator_energy_drift
#print axioms OSTQD_SK.eigenoperator_carre_du_champ
#print axioms OSTQD_SK.kms_detailed_balance_stationarity
#print axioms OSTQD_SK.kms_gns_monotonicity
#print axioms OSTQD_SK.kms_symmetric_intertwining
#print axioms OSTQD_SK.nonsecular_redfield_kossakowski_obstruction
#print axioms OSTQD_SK.multitime_qrt_exterior_nogo

-- Theorem2_WardAndFDT.lean (9)
#print axioms OSTQD_SK.bipartite_energy_ward_identity
#print axioms OSTQD_SK.bipartite_ward_from_commuting_jumps
#print axioms OSTQD_SK.mean_energy_conservation_nonzero_diffusion
#print axioms OSTQD_SK.jt_evaporation_ward_ode
#print axioms OSTQD_SK.jt_equilibrium_fdt_exact
#print axioms OSTQD_SK.jt_evaporating_variance_ode
#print axioms OSTQD_SK.jt_evaporating_nongaussian_cumulants_ode
#print axioms OSTQD_SK.jt_equilibrium_nongaussian_fdt_obstruction
#print axioms OSTQD_SK.jt_bernard_doyon_hj_canonical_fdt

-- Theorem3_HorizonHadamard.lean (5)
#print axioms OSTQD_SK.truncated_bosonic_hawking_ode
#print axioms OSTQD_SK.bosonic_exterior_diagonal_cpl_invariance
#print axioms OSTQD_SK.bosonic_tridiagonal_all_s_excitation
#print axioms OSTQD_SK.continuum_hadamard_firewall_vs_smooth
#print axioms OSTQD_SK.single_shot_number_projection_firewall_floor

-- Theorem4_NonIsometricThroat.lean (5)
#print axioms OSTQD_SK.kms_inward_port_locking_nogo
#print axioms OSTQD_SK.exterior_interior_algebra_separation
#print axioms OSTQD_SK.nonisometric_kernel_nontrivial
#print axioms OSTQD_SK.throat_closure_complete_erasure_eq
#print axioms OSTQD_SK.throat_closure_complete_erasure_bound
