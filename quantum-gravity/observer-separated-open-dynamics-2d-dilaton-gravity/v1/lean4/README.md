# Lean 4.36.0 Formalization of OSTQD-SK (Paper 2)

This directory contains the independent Lean 4.36.0 + Mathlib4 (`rev = v4.36.0`) formalization of the finite-dimensional algebraic, two-Kraus unraveling gauge witness, dynamical-KMS, symmetric-intertwining, free-subsystem Dirichlet-kernel regression, two-tiered Ward-identity, frozen-coefficient Bernard–Doyon JT cumulant and rational Hamilton–Jacobi factorization, bosonic all-$s$ `HasDerivAt` ODE, number-projective single-shot excitation floor, asymptotic point-split divergence, exact $d_f=1$ complete-erasure, and non-isometric rank-nullity core of Paper 2 (*Consistency Audits of Observer-Separated Open Dynamics in 2D Dilaton Gravity: KMS Covariance, Non-Gaussian JT Fluctuations, and Chiral-Horizon Obstructions*).

Lean certifies only the exact algebraic and ODE statements formalized in these modules; physical kernel identifications, continuum distributional constructions, total-system unitary embeddings, and conceptual design proposals lie outside Lean (see `../VERIFICATION.md` and Table 3 of the manuscript).

## Reproduction (Linux / macOS / WSL with `elan`)

```bash
cd lean4
lake exe cache get
lake build OSTQD_SK
lake env lean OSTQD_SK/AxiomCheck.lean
```

## Modules and Public Declarations (34 Public Theorems)

- `OSTQD_SK/Basic.lean` (7): `trace_gksl_eq_zero`, `gksl_dual_adj`, `sk_quadratic_tp_normalization`, `sk_quadratic_conjugation_symmetry`, `sk_quadratic_im_nonneg`, `sk_fdt_wightman_rates`, `layer2_unraveling_gauge_nonuniqueness`
- `OSTQD_SK/Theorem1_CovariantKMS.lean` (8): `eigenoperator_two_time_commutation`, `eigenoperator_energy_drift`, `eigenoperator_carre_du_champ`, `kms_detailed_balance_stationarity`, `kms_gns_monotonicity`, `kms_symmetric_intertwining`, `nonsecular_redfield_kossakowski_obstruction`, `multitime_qrt_exterior_nogo`
- `OSTQD_SK/Theorem2_WardAndFDT.lean` (9): `bipartite_energy_ward_identity`, `bipartite_ward_from_commuting_jumps`, `mean_energy_conservation_nonzero_diffusion`, `jt_evaporation_ward_ode`, `jt_equilibrium_fdt_exact`, `jt_evaporating_variance_ode`, `jt_evaporating_nongaussian_cumulants_ode`, `jt_equilibrium_nongaussian_fdt_obstruction`, `jt_bernard_doyon_hj_canonical_fdt`
- `OSTQD_SK/Theorem3_HorizonHadamard.lean` (5): `truncated_bosonic_hawking_ode`, `bosonic_exterior_diagonal_cpl_invariance`, `bosonic_tridiagonal_all_s_excitation`, `continuum_hadamard_firewall_vs_smooth`, `single_shot_number_projection_firewall_floor`
- `OSTQD_SK/Theorem4_NonIsometricThroat.lean` (5): `kms_inward_port_locking_nogo`, `exterior_interior_algebra_separation`, `nonisometric_kernel_nontrivial`, `throat_closure_complete_erasure_eq`, `throat_closure_complete_erasure_bound`
- `OSTQD_SK/AxiomCheck.lean`: `#print axioms` audit verifying all 34 public declarations depend solely on `[propext, Classical.choice, Quot.sound]`.

See `VERIFICATION_LOG.txt` and `../VERIFICATION.md` for the complete kernel log (noting zero errors and zero tactic-linter warnings, distinct from Lean 4.36.0's benign `module`-system import notice) and explicit trust boundary.
