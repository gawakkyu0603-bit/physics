# Lean 4.36.0 Formalization of OSTQD-SK

This directory contains the independent Lean 4.36.0 + Mathlib4 (`rev = v4.36.0`) formalization of the finite-dimensional algebraic, two-Kraus unraveling gauge & local-unitary no-signaling vs. channel-compatibility, dynamical-KMS, symmetric-intertwining, free-subsystem Dirichlet-kernel regression, uniform-contraction Gibbs tracking, two-tiered Ward-identity, frozen-coefficient Bernard–Doyon JT cumulant, rational Hamilton–Jacobi factorization, naive finite-$q$ detailed-balance obstruction and constructive $E\ge 0$ entropy-difference jump process, bosonic all-$s$ `HasDerivAt` ODE, Mellin $2\times 2$ PSD kernel & sharp point-contact threshold, number-projective single-shot excitation floor, asymptotic point-split divergence, horizon-origin port vs. distant output mode vacuum noise, exact $d_f=1$ complete-erasure, and non-isometric rank-nullity core of *Consistency Audits of Observer-Separated Open Dynamics in 2D Dilaton Gravity: KMS Covariance, Non-Gaussian JT Fluctuations, and Chiral-Horizon Obstructions*.

Lean certifies only the exact algebraic and ODE statements formalized in these modules; physical kernel identifications, continuum distributional constructions, total-system unitary embeddings, and conceptual design proposals lie outside Lean (see `../VERIFICATION.md` and Table 3 of the manuscript).

## Reproduction (Linux / macOS / WSL with `elan`)

```bash
bash verify_lean.sh
# or directly inside lean4/:
cd lean4
lake exe cache get
lake build OSTQD_SK
lake env lean OSTQD_SK/AxiomCheck.lean
```

## Modules and Public Declarations (40 Public Theorems)

- `OSTQD_SK/Basic.lean` (8): `trace_gksl_eq_zero`, `gksl_dual_adj`, `sk_quadratic_tp_normalization`, `sk_quadratic_conjugation_symmetry`, `sk_quadratic_im_nonneg`, `sk_fdt_wightman_rates`, `layer2_unraveling_gauge_nonuniqueness`, `local_unitary_preserves_remote_marginal_vs_channel`
- `OSTQD_SK/Theorem1_CovariantKMS.lean` (9): `eigenoperator_two_time_commutation`, `eigenoperator_energy_drift`, `eigenoperator_carre_du_champ`, `kms_detailed_balance_stationarity`, `kms_gns_monotonicity`, `kms_symmetric_intertwining`, `nonsecular_redfield_kossakowski_obstruction`, `multitime_qrt_exterior_nogo`, `uniform_contraction_gibbs_tracking_bound`
- `OSTQD_SK/Theorem2_WardAndFDT.lean` (11): `bipartite_energy_ward_identity`, `bipartite_ward_from_commuting_jumps`, `mean_energy_conservation_nonzero_diffusion`, `jt_evaporation_ward_ode`, `jt_equilibrium_fdt_exact`, `jt_evaporating_variance_ode`, `jt_evaporating_nongaussian_cumulants_ode`, `jt_equilibrium_nongaussian_fdt_obstruction`, `jt_bernard_doyon_hj_canonical_fdt`, `jt_naive_bd_finite_q_detailed_balance_obstruction`, `jt_entropy_diff_jump_exact_detailed_balance`
- `OSTQD_SK/Theorem3_HorizonHadamard.lean` (6): `truncated_bosonic_hawking_ode`, `bosonic_exterior_diagonal_cpl_invariance`, `bosonic_tridiagonal_all_s_excitation`, `continuum_hadamard_firewall_vs_smooth`, `single_shot_number_projection_firewall_floor`, `mellin_contact_kernel_psd_and_extension_positivity`
- `OSTQD_SK/Theorem4_NonIsometricThroat.lean` (6): `kms_inward_port_locking_nogo`, `exterior_interior_algebra_separation`, `nonisometric_kernel_nontrivial`, `throat_closure_complete_erasure_eq`, `throat_closure_complete_erasure_bound`, `distant_output_mode_vacuum_noise_vs_horizon_port` (generalized for arbitrary $g\neq 0$)
- `OSTQD_SK/AxiomCheck.lean`: `#print axioms` audit verifying all 40 public declarations depend solely on `[propext, Classical.choice, Quot.sound]`.

See `VERIFICATION_LOG.txt` and `../VERIFICATION.md` for the complete kernel log (noting zero errors and zero tactic/linter warnings, distinct from Lean 4.36.0's benign `module`-system import notice) and explicit trust boundary.
