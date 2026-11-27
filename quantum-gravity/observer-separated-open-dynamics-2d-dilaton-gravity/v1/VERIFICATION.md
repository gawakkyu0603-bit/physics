# Verification and Trust Boundary (Paper 2: OSTQD-SK)

**Date:** November 27, 2026  
**Manuscript:** *Consistency Audits of Observer-Separated Open Dynamics in 2D Dilaton Gravity: KMS Covariance, Non-Gaussian JT Fluctuations, and Chiral-Horizon Obstructions*

This document specifies exactly what is machine-checked in Lean 4.36.0 (**34 public declarations**), what is proved analytically in the manuscript, what is audited numerically via categorized Python suites F1–F6 (**258 scientific numeric fields**, seed `20261127`), and what physical identifications, continuum steps, and conceptual proposals lie outside all three verification layers.

---

## 1. Lean 4.36.0 Formal Verification (`lean4/`)

### Reproduction commands
From `paper2_sk_jt/lean4/` (Linux / macOS / WSL with `elan` installed):

```bash
lake exe cache get
lake build OSTQD_SK
lake env lean OSTQD_SK/AxiomCheck.lean
grep -rnE '(^|[^A-Za-z0-9_])(sorry|admit|axiom|constant|unsafe|sorryAx)([^A-Za-z0-9_]|$)' OSTQD_SK.lean OSTQD_SK/Basic.lean OSTQD_SK/Theorem*.lean
```

### Explicit trust boundary (34 public declarations)

Formal verification certifies only the exact hypotheses and conclusions written in Lean; mapping those algebraic and ODE lemmas to physical interpretations, continuum distributions, or open-system design proposals lies outside the proof assistant.

| Manuscript result | Machine-checked Lean 4.36.0 core (34 public declarations) | Physical / continuum / conceptual steps outside Lean |
| --- | --- | --- |
| SK axioms, FDT & unraveling (§2) | `Basic.lean` (7): `trace_gksl_eq_zero`, `gksl_dual_adj`, `sk_quadratic_tp_normalization`, `sk_quadratic_conjugation_symmetry`, `sk_quadratic_im_nonneg`, `sk_fdt_wightman_rates`, `layer2_unraveling_gauge_nonuniqueness` | Path-integral derivation of Gaussian influence action (5) and uncorrelated bath preparation; bath $D_R\neq 0$ controls in F1; CP sufficiency beyond SK1–SK3; Gisin no-signaling. |
| Theorem 1 (fixed-$T_H$ & QRT, §3) | `Theorem1_CovariantKMS.lean` (8): `eigenoperator_two_time_commutation`, `eigenoperator_energy_drift`, `eigenoperator_carre_du_champ`, `kms_detailed_balance_stationarity`, `kms_gns_monotonicity`, `kms_symmetric_intertwining`, `nonsecular_redfield_kossakowski_obstruction`, `multitime_qrt_exterior_nogo` | Matrix-exponential lift to $\mathcal{U}(t)\circ\Phi(s)$ and $\frac{d}{ds}\chi^2_{\beta_H}(\rho(s))\le 0$ (F2); total-system Hamiltonian embeddings, unitary Markov dilations, and model-specific bath memory (not implied by `multitime_qrt_exterior_nogo`); exact Duhamel bound and $\mu/\lambda_{\mathrm{rel}}$ tracking (Proposition 1, F2). |
| Theorem 2 & Proposition 2 (Ward & JT, §4) | `Theorem2_WardAndFDT.lean` (9): `bipartite_energy_ward_identity`, `bipartite_ward_from_commuting_jumps`, `mean_energy_conservation_nonzero_diffusion`, `jt_evaporation_ward_ode`, `jt_equilibrium_fdt_exact`, `jt_evaporating_variance_ode`, `jt_evaporating_nongaussian_cumulants_ode`, `jt_equilibrium_nongaussian_fdt_obstruction`, `jt_bernard_doyon_hj_canonical_fdt` | Deriving JT Ward equation from Polyakov anomaly; Bernard–Doyon CGF (2012/2015); frozen-coefficient MC (F3); state-dependent evaporating feedback ($3D_2'(\bar{E})K_2$); global jump-process boundary prescriptions; Stanford–Witten 1-loop disk corrections; finite bath-correlation times (Gaikwad et al. 2023) and $CT_H\lesssim 1$. |
| Theorem 3 & Propositions 3–4 (Boson, smooth-band & Layer 2, §5) | `Theorem3_HorizonHadamard.lean` (5): `truncated_bosonic_hawking_ode`, `bosonic_exterior_diagonal_cpl_invariance`, `bosonic_tridiagonal_all_s_excitation`, `continuum_hadamard_firewall_vs_smooth`, `single_shot_number_projection_firewall_floor` | $N\to\infty$ Fock convergence ($\mathcal{O}(Nq^N)$ at fixed $\omega>0$, F4); tempered distribution $\Delta W_J^{\mathrm{raw}}\in\mathcal{S}'(\mathbb{R}^2)$, PSD-jet lemma, and bounded $c_{0,\min}$ witness (Proposition 3, F4); axis-supported / global positive continuum states (Louko 2014); $N\ge 3$ common $(0,0)$ eigenstates, steering, Local Friendliness settings, and Layer-2 design postulates. |
| Theorem 4 & Proposition 5 (KMS, closed infall, erasure, kernel, §6) | `Theorem4_NonIsometricThroat.lean` (5): `kms_inward_port_locking_nogo`, `exterior_interior_algebra_separation`, `nonisometric_kernel_nontrivial`, `throat_closure_complete_erasure_eq`, `throat_closure_complete_erasure_bound` | Static 4D Schwarzschild scattering ODEs (F5); Lorentzian causal-future curve structure on $J^-(I)$; multi-port total Hawking power; Proposition 5's condition-indexed synthesis; gravitational Cauchy-slice factorization; unifying F6's separated benchmarks. |

All verified kernel build logs (zero errors, zero tactic-linter warnings—distinct from Lean 4.36.0's benign `module`-system import notice logged by `lake build`—and zero forbidden tokens) and `#print axioms` outputs for all 34 public declarations are archived in `lean4/VERIFICATION_LOG.txt`.

---

## 2. Categorized Numerical Verification Suite (`scripts/verify_paper2_sk_jt.py`)

### Reproduction command
Tested with Python 3.14.7 (`numpy 2.4.2`, `scipy 1.17.1`, `matplotlib 3.10.8`), deterministic seed `20261127`, recording **258 scientific numeric fields** across F1–F6 in `docs/numerical_verification.json` (excluding `metadata`; comprising parameters, arrays, algebraic checks, negative controls, ODE/scattering integrations, and zero time-discretization bias Monte Carlo estimates, not 258 independent physical experiments) and generating all four vector PDF figures in `paper/figures/`:

```bash
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python scripts/verify_paper2_sk_jt.py
```

### Categorized summary of F1–F6 results

1. **F1 (Microscopic Kernel Normalization, Two-Kraus Unraveling Witness, Chiral Fourier Check, QND Bath Response, SK Non-Sufficiency, Two-Bath Non-KMS & Redfield CP Failure):**
   - *Algebraic / microscopic checks:* SK axioms (`0.0`, `0.0`, `0.2180`); 80-level bath characteristic function matches $N=D_K/2$ to `1.11e-16` (vs. `0.0760` doubled); chiral Fourier quadrature matches $(\Omega/2)e^{-\epsilon\Omega}$ to `1.44e-15`; Davies CPTP $\min\lambda(J)=+1.88\times 10^{-6}$, TP error `4.97e-16`; orthogonal Kraus gauge $(0.6, 0.8)$ gives channel diff `0.0` while shifting single-shot $p_0(|0\rangle\langle 0|): 1.0 \to 0.36$ and normalized conditional coherence on $|+\rangle\langle +|: 0.0 \to 0.48$ (unnormalized branch entry `6/25 = 0.24`).
   - *Negative controls:* $3\times 3$ Schur multiplier $\min\lambda(M/3) = -0.07459$; QND bath $D_R(t)=-0.78950\neq 0$ and Ohmic $\mathrm{Re}\,D_R(0)=-2.5465\neq 0$; two-bath Unruh ratio `0.22540`; Redfield Choi `-2.00e-3` at $T_H/\omega=0.25$.
2. **F2 (Fixed-$T_H$ Covariant $(t,s)$, Non-Commuting $\chi^2$, Free-Subsystem QRT Criterion, Duhamel Holonomy Bound & Relaxation-Gap Tracking Counterexample):**
   - *Algebraic / semigroup checks:* $d=6$ KMS stationarity `1.40e-17`, $(t,s)$ commutation `1.01e-15`, GNS Dirichlet `3.58e-15`, non-commuting symmetric $B_s$ intertwining `3.55e-13` and derivative `5.68e-14`; 2-level asymmetric $A_L$ failure (`0.5625`) vs. symmetric $B$ (`2.29e-16`); free-subsystem QRT Dirichlet witness `0.0` (commuting $\mathbf{1}\otimes\sigma_z$) vs. `1.25` (non-commuting $\sigma_x\otimes\mathbf{1}$, residual `0.0`).
   - *Negative controls:* 3-level diffusion (`0.864665`); non-stationary Duhamel bound (`0.01648 <= 0.02025 <= 0.02210`) & moving-Gibbs $D = 0.001724 > 0$; quasi-stationary relaxation-gap counterexample ($\mu=10^{-4},\eta=10^{-8}$, $\max|\dot{T}|/T^2 = 2\times 10^{-4}$ yet $p_{\mathrm{actual}} = 0.26893$, $p_{\mathrm{Gibbs}} = 0.11920$, trace distance `0.14973` at $T=1/2$).
3. **F3 (2D JT + CFT Ward ODE, Exact-Step Gaussian & Frozen-Coefficient Compound-Poisson MC, Three-Tier Equilibrium Closure Comparison & Rational HJ Factorization):**
   - *ODE / equilibrium hierarchy:* Ward ODE `7.60e-12`, chiral noise integral `8.88e-16`, 1-loop disk correction `0.317%`; 3-tier fixed-BD-coefficient equilibrium closure comparison verifies Tier 1 ($K_3=0$, $K_4/\kappa_4^{\mathrm{can}}=0.5$), Tier 2 ($K_3/\kappa_3^{\mathrm{can}}=1.0$, $K_4/\kappa_4^{\mathrm{can}}=1.5$), Tier 3 ($K_4/\kappa_4^{\mathrm{can}}=1.0$), and Hamilton–Jacobi zero-locus residual `0.0` across $E/E_0\in[0.2,3.0]$.
   - *Zero time-discretization bias Monte Carlo:* Gaussian exact-step MC ($2\times 10^4$ paths, `ddof=1`): `0.31%` at $CT_H\simeq 1$, `0.43%` at $0.65 u_{\mathrm{break}}$ ($P(E<0)=1.02\%$ at $CT_H=1$). Continuous-time non-homogeneous compound-Poisson MC ($10^5$ paths, zero time-discretization bias) for the frozen-coefficient additive closure: $K_2$ `0.46%`, $K_3$ `2.18%` at $u_{CT=1}$ ($\gamma_1 = -0.1938$ vs. `-0.1910`); $K_2$ `0.50%`, $K_3$ `0.72%`, $K_4$ `0.15%` at $u_{\mathrm{break}}$ ($\gamma_1 = -0.7549$, $\gamma_2 = +1.0201$).
4. **F4 (Bosonic ODE, Smooth-Band Point-Contact Positivity Witness, Number-Projective Single-Shot Floor & Free-Subsystem QRT Contrast):**
   - Truncated Fock `8.17e-16` ($N_{\mathrm{cut}}=32$), $\mathcal{O}(Nq^N)$ formula `4.44e-16`, `solve_ivp` `4.49e-11`; fixed-$s$ CPL `2.51e-16`; smooth-bump point-split slope `-2.0000000000000004`, raw-cutoff UV finiteness (`3.36e-9`), negative total raw response at $\Omega=2,3$ (`-0.001877`, `-0.001121`), exact $\sigma_\tau$-invariance (`0.0` across $\sigma_\tau\in\{0.5,1,2\}$ at $a=2$), fixed witness $a_*=2.1501$ (from bounded search on $a\in(1.5,4.0)$) with analytic bound $c_{00}\ge c_{0,\min}\ge -F_0(a_*)$ and numerically evaluated **$-F_0(a_*)\approx 0.00197949$** (no certified quadrature error bound or global infimum claimed); number-projective single-shot floor `0.54683` ($n=0\dots 10$), ensemble match `0.0`, $\|[P_A,P_B]\|_F = 0.58071$; free-subsystem QRT ratio `0.60653`.
5. **F5 (Near-Horizon-Stabilized 4D Static Schwarzschild Scattering, Separated Convergence Audits & Fixed-$\omega r_s$ Control):**
   - 45-pt max relative Wronskian `9.11e-12` (abs `1.63e-5` overall, `3.15e-9` for $\mathcal{T}>10^{-6}$); inner-boundary shifts $\le 8.79\times 10^{-9}$; outer-matching shifts $\le 3.00\times 10^{-7}$ (Dirac $(-80,480)$ `9.34e-9`; naive $f=1-1/y$ rounding shift `-6.76e-7`); Dirac SUSY `2.13e-7`; ultra-low DGM `1.01636`, Unruh `0.12708`, photon `0.45931`, graviton `0.019019`; fixed-$\omega r_s=0.4$ control $\mathcal{T}_{0,0} = 0.90894$; KMS linear shutdown `0.0`.
6. **F6 (Three Explicitly Separated Conditional Benchmark Models):**
   - Model 1 (simplified JT crossing): $u_{\mathrm{Page}}=32.18$ (`1.14e-13`), $e^{S_0} = 4.85\times 10^8$.
   - Model 2 (static $64\to 32$ Haar map $V$): rank `32`, nullity `32`, non-TP null-state trace `2.57e-31`, $\|V^\dagger V - \mathbf{1}\|_{\mathrm{op}} = 1.000000$, basis RMS `[0.1763, 0.1254, 0.0884, 0.0625]`.
   - Model 3 (separate isometric $N=8$ diary models): $d_C=2$ ($F_{\mathrm{rad}}: 0.25\to 1.0$, $F_{\mathrm{rem}}: 1.0\to 0.25$, cap sequence $(1,\dots,1,1/4)$, final $S_{\mathrm{rad}} = 1.000$ bit); $d_C=4$ intermediate bottleneck ($F_{\mathrm{rem}}(7) = 0.0660 \le 0.25$ at $d_{\mathrm{BH}}=2$, exact erasure $F_{\mathrm{rem}}(8) = 0.0625 = 1/16$ at $d_{\mathrm{BH}}=1$).

---

## 3. LaTeX Manuscript Build (`paper/`)

Compiled with WSL TeX Live 2023 (`pdflatex` + `bibtex`, including pre-built `main.bbl` for arXiv submission): **34 pages**, **84 cited references**, **4 vector PDF figures**, zero errors, zero BibTeX warnings, zero hyperref warnings, zero undefined citations or references, and zero overfull boxes.
