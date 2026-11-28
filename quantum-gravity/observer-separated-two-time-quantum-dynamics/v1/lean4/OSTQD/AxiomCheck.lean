import OSTQD

/-!
# OSTQD.AxiomCheck

Audits all 50 listed public theorem declarations in OSTQD (alongside internal helper lemmas in
the modules) to verify that each depends exclusively on Lean 4's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) with zero `sorryAx` and zero custom axioms.
-/

-- Basic.lean (2)
#print axioms OSTQD.trace_gksl_eq_zero
#print axioms OSTQD.gksl_dual_adj

-- Theorem1_BPS.lean (10)
#print axioms OSTQD.carre_du_champ_eq_sum_comm_sq
#print axioms OSTQD.carre_du_champ_trace_nonneg
#print axioms OSTQD.bps_immunity_iff_comm
#print axioms OSTQD.two_time_commutation
#print axioms OSTQD.variance_deriv_exact_decomp
#print axioms OSTQD.eigenstate_variance_deriv_eq_carre_du_champ
#print axioms OSTQD.eigenbasis_sum_variance_deriv_eq_trace_carre_du_champ
#print axioms OSTQD.algebra_nonclosure_counterexample
#print axioms OSTQD.bps_sufficient_not_necessary_for_commutation
#print axioms OSTQD.nonhermitian_bps_degenerate_purity_increase

-- Theorem2_Horizon.lean (16)
#print axioms OSTQD.universal_actualization_nogo
#print axioms OSTQD.quantitative_horizon_heating_bound
#print axioms OSTQD.static_redshift_zero_conflict
#print axioms OSTQD.two_level_bogoliubov_incompatibility
#print axioms OSTQD.fermionic_hawking_HB_bps_immune
#print axioms OSTQD.fermionic_hawking_energy_at_s
#print axioms OSTQD.fermionic_hawking_firewall_entropy_identity
#print axioms OSTQD.local_actualization_nogo
#print axioms OSTQD.local_dissipation_bound
#print axioms OSTQD.fermionic_hawking_HA_comm_HB
#print axioms OSTQD.fermionic_hawking_local_incompatibility
#print axioms OSTQD.fermionic_hawking_local_nogo
#print axioms OSTQD.fermionic_hawking_ode
#print axioms OSTQD.positive_gamma_loc_fixed_ground_state_counterexample
#print axioms OSTQD.fermionic_hawking_reduced_states_invariant
#print axioms OSTQD.fermionic_hawking_neg_s_not_psd

-- Theorem3_CrossPerspective.lean (10)
#print axioms OSTQD.projA_projB_projA
#print axioms OSTQD.joint_extension_fidelity_bound
#print axioms OSTQD.joint_extension_no_simultaneous_faithful
#print axioms OSTQD.joint_extension_fidelity_bound_mixed
#print axioms OSTQD.joint_extension_bound_sharp
#print axioms OSTQD.observer_separated_cpl_consistency
#print axioms OSTQD.asymmetric_kay_choi_saturation
#print axioms OSTQD.shared_causal_record_instrument_agreement
#print axioms OSTQD.achievable_joint_region_choi_complete
#print axioms OSTQD.weak_record_measurement_vs_projective_readout

-- Theorem4_DoubleUncertainty.lean (6)
#print axioms OSTQD.parisi_wu_purity_monotonicity
#print axioms OSTQD.double_uncertainty_pythagorean
#print axioms OSTQD.weak_gravity_invisibility
#print axioms OSTQD.microcanonical_code_invariance
#print axioms OSTQD.commuting_jumps_block_eigenvalue
#print axioms OSTQD.microcanonical_window_scrambling_compatible

-- Theorem5_Bottleneck.lean (6)
#print axioms OSTQD.bottleneck_entanglement_fidelity_bound
#print axioms OSTQD.bottleneck_bound_sharp
#print axioms OSTQD.entanglement_fidelity_le_one
#print axioms OSTQD.bottleneck_entanglement_fidelity_min_bound
#print axioms OSTQD.bottleneck_bound_sharp_large_df
#print axioms OSTQD.classical_flag_beats_unassisted_bottleneck
