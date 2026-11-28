import OSTQD_SK.Basic

/-!
# OSTQD_SK.Theorem3_HorizonHadamard

Theorem 3 and Propositions 3–4 (Horizon Non-Hadamard Defect, Mellin Positive-Type Extension,
and Single-Shot Number-Projection Excitation Floor):
  (a) Arbitrary-`N` Bosonic Two-Mode Squeezed All-`s` Exact GKSL ODE (`HasDerivAt`):
      extending the 4D fermionic ODE to arbitrary Fock truncation dimension `N`.
  (b) Exact Exterior-Diagonal CPL Invariance (`Tr(D ρ^(N)(s)) = Tr(D ρ^(N)(0))`)
      juxtaposed with exact nearest-neighbor cross-horizon attenuation `exp(-Γ s / 2)`
      and universal `(1 - exp(-Γ s / 2))` all-`s` inertial energy excitation law for
      any tridiagonal inertial Hamiltonian `H_A^(N)`.
  (c) Continuum Free Chiral Boson Point-Split Non-Hadamard Divergence vs. Observer-`A` Smoothness:
      real-analytic asymptotic lemma taking the continuum cross-horizon point-split defect
      `ΔW_J(-ε, +ε) = (1 - e^{-Γ s/2}) / (16 π ε²)` as input: for any `Γ > 0, s > 0`, it exceeds
      every finite bound `M` as `ε → 0⁺`, whereas at `s = 0` (`S_SK^(A)`) it vanishes identically
      for all `ε > 0`.
  (d) Mellin positive-type kernel PSD and sharp point-contact threshold `c_00 ≥ c_*`
      (Proposition 3).
  (e) Single-shot number-projection firewall floor and projector non-commutativity
      (Proposition 4).
-/

open scoped Matrix BigOperators ComplexConjugate

namespace OSTQD_SK

/-- Exterior number operator `N_R = diag(0, 1, ..., N-1)` on the `N`-level Schmidt subspace
`span{|n_R, n_L⟩ : 0 ≤ n < N}`. -/
noncomputable def fockNumberOp (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (fun n : Fin N => (n.val : ℂ))

/-- Exact `N`-level exterior-dephased two-mode squeezed density matrix at auxiliary time `s`:
`ρ^(N)_{i,j}(s) = c_i c_j exp(-Γ s (i - j)² / 2)`. -/
noncomputable def bosonicRho (N : ℕ) (c : Fin N → ℝ) (Γ s : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j =>
    ((c i * c j * Real.exp (-(Γ * s) * ((i.val : ℝ) - (j.val : ℝ)) ^ 2 / 2) : ℝ) : ℂ)

lemma gkslOne_fockNumberOp_entry (N : ℕ) (Γ : ℝ) (hΓ : 0 ≤ Γ)
    (ρ : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    gkslOne ((Real.sqrt Γ : ℂ) • fockNumberOp N) ρ i j =
      (-((Γ : ℂ) * (((i.val : ℝ) - (j.val : ℝ) : ℝ) : ℂ) ^ 2 / 2)) * ρ i j := by
  have hdag : ((Real.sqrt Γ : ℂ) • fockNumberOp N)ᴴ = (Real.sqrt Γ : ℂ) • fockNumberOp N := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [fockNumberOp]
    · simp [fockNumberOp, hab, Ne.symm hab]
  unfold gkslOne
  rw [hdag]
  unfold fockNumberOp
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply,
    Matrix.diagonal_apply, smul_eq_mul]
  have hs1 : ∑ k : Fin N, (∑ l : Fin N,
      (Real.sqrt Γ : ℂ) * (if i = l then (i.val : ℂ) else 0) * ρ l k) *
      ((Real.sqrt Γ : ℂ) * (if k = j then (k.val : ℂ) else 0)) =
      (Real.sqrt Γ : ℂ) ^ 2 * (i.val : ℂ) * (j.val : ℂ) * ρ i j := by
    rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single i]
      · simp only [↓reduceIte]; ring
      · intro l _ hli; simp [Ne.symm hli]
      · intro hi; exact (hi (Finset.mem_univ i)).elim
    · intro k _ hkj; simp [hkj]
    · intro hj; exact (hj (Finset.mem_univ j)).elim
  have hs2 : ∑ k : Fin N, (∑ l : Fin N,
      (Real.sqrt Γ : ℂ) * (if i = l then (i.val : ℂ) else 0) *
      ((Real.sqrt Γ : ℂ) * (if l = k then (l.val : ℂ) else 0))) * ρ k j =
      (Real.sqrt Γ : ℂ) ^ 2 * (i.val : ℂ) ^ 2 * ρ i j := by
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single i]
      · simp only [↓reduceIte]; ring
      · intro l _ hli; simp [Ne.symm hli]
      · intro hi; exact (hi (Finset.mem_univ i)).elim
    · intro k _ hki
      have hinner : ∑ l : Fin N,
          (Real.sqrt Γ : ℂ) * (if i = l then (i.val : ℂ) else 0) *
          ((Real.sqrt Γ : ℂ) * (if l = k then (l.val : ℂ) else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro l _
        by_cases hil : i = l
        · subst hil; simp [Ne.symm hki]
        · simp [hil]
      rw [hinner, zero_mul]
    · intro hi; exact (hi (Finset.mem_univ i)).elim
  have hs3 : ∑ k : Fin N, ρ i k * (∑ l : Fin N,
      (Real.sqrt Γ : ℂ) * (if k = l then (k.val : ℂ) else 0) *
      ((Real.sqrt Γ : ℂ) * (if l = j then (l.val : ℂ) else 0))) =
      (Real.sqrt Γ : ℂ) ^ 2 * (j.val : ℂ) ^ 2 * ρ i j := by
    rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single j]
      · simp only [↓reduceIte]; ring
      · intro l _ hlj; simp [hlj]
      · intro hj; exact (hj (Finset.mem_univ j)).elim
    · intro k _ hkj
      have hinner : ∑ l : Fin N,
          (Real.sqrt Γ : ℂ) * (if k = l then (k.val : ℂ) else 0) *
          ((Real.sqrt Γ : ℂ) * (if l = j then (l.val : ℂ) else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro l _
        by_cases hlj : l = j
        · subst hlj; simp [hkj]
        · simp [hlj]
      rw [hinner, mul_zero]
    · intro hj; exact (hj (Finset.mem_univ j)).elim
  rw [hs1, hs2, hs3]
  have hsq : (Real.sqrt Γ : ℂ) ^ 2 = (Γ : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hΓ]
  rw [hsq]
  push_cast
  ring

/-- **Theorem 3(a)** (Arbitrary-`N` Bosonic All-`s` Exact GKSL ODE):
For EVERY Fock truncation dimension `N`, real amplitudes `c`, rate `Γ ≥ 0`, and
all `s : ℝ`, every entry `(i, j)` of `bosonicRho N c Γ s` satisfies the exact GKSL
differential equation `(d/ds) ρ^(N)_{ij}(s) = (L_B(ρ^(N)(s)))_{ij}` with
`L_B = -(Γ/2)[N_R, [N_R, ·]]`. -/
theorem truncated_bosonic_hawking_ode (N : ℕ) (c : Fin N → ℝ) (Γ s : ℝ) (hΓ : 0 ≤ Γ)
    (i j : Fin N) :
    HasDerivAt (fun τ : ℝ => bosonicRho N c Γ τ i j)
      (gksl [(Real.sqrt Γ : ℂ) • fockNumberOp N] (bosonicRho N c Γ s) i j) s := by
  have hrhs : gksl [(Real.sqrt Γ : ℂ) • fockNumberOp N] (bosonicRho N c Γ s) i j =
      ((-(Γ * ((i.val : ℝ) - (j.val : ℝ)) ^ 2 / 2) *
        (c i * c j * Real.exp (-(Γ * s) * ((i.val : ℝ) - (j.val : ℝ)) ^ 2 / 2)) : ℝ) : ℂ) := by
    unfold gksl
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [gkslOne_fockNumberOp_entry N Γ hΓ]
    unfold bosonicRho
    simp only [Matrix.of_apply]
    push_cast
    ring
  rw [hrhs]
  set α : ℝ := Γ * ((i.val : ℝ) - (j.val : ℝ)) ^ 2 / 2
  have hlin : HasDerivAt (fun τ : ℝ => -(Γ * τ) * ((i.val : ℝ) - (j.val : ℝ)) ^ 2 / 2) (-α) s := by
    have h1 := (hasDerivAt_id s).const_mul (-α)
    convert h1 using 1
    · funext τ; dsimp only [α, id]; ring
    · ring
  have hre : HasDerivAt
      (fun τ : ℝ => c i * c j * Real.exp (-(Γ * τ) * ((i.val : ℝ) - (j.val : ℝ)) ^ 2 / 2))
      ((-α) * (c i * c j * Real.exp (-(Γ * s) * ((i.val : ℝ) - (j.val : ℝ)) ^ 2 / 2))) s := by
    have h2 := (hlin.exp).const_mul (c i * c j)
    convert h2 using 1
    ring
  exact hre.ofReal_comp

/-- **Theorem 3(b.1)** (Exact Exterior-Diagonal CPL Invariance for All `s`):
Every diagonal exterior observable `D = diag(d_0, ..., d_{N-1})` has strictly
`s`-invariant expectation value `Tr(D ρ^(N)(s)) = Tr(D ρ^(N)(0))`. -/
theorem bosonic_exterior_diagonal_cpl_invariance (N : ℕ) (c : Fin N → ℝ)
    (diagObs : Fin N → ℂ) (Γ s : ℝ) :
    (Matrix.diagonal diagObs * bosonicRho N c Γ s).trace =
      (Matrix.diagonal diagObs * bosonicRho N c Γ 0).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i, Finset.sum_eq_single i]
  · simp [bosonicRho]
  · intro j _ hji; simp [Ne.symm hji]
  · intro hi; exact (hi (Finset.mem_univ i)).elim
  · intro j _ hji; simp [Ne.symm hji]
  · intro hi; exact (hi (Finset.mem_univ i)).elim

/-- **Theorem 3(b.2)** (Exact Universal `(1 - exp(-Γ s / 2))` All-`s` Excitation Law for
Tridiagonal Inertial Hamiltonians):
For ANY tridiagonal matrix `H_A` (nonzero entries only for `|i - j| ≤ 1`, covering the
exact truncated bosonic inertial Hamiltonian `H_A = ω[cosh(2r)(2N+1)-1 - sinh(2r)(b_R†b_L† + b_R b_L)]`
at arbitrary Fock cutoff `N`), the excitation energy above `s = 0` equals
`(Tr(H_A ρ_diag) - Tr(H_A ρ(0))) · (1 - exp(-Γ s / 2))` identically for all `s ∈ ℝ`,
while every nearest-neighbor cross-horizon correlator decays by `exp(-Γ s / 2)`. -/
theorem bosonic_tridiagonal_all_s_excitation (N : ℕ) (c : Fin N → ℝ) (Γ s : ℝ)
    (H_A : Matrix (Fin N) (Fin N) ℂ)
    (htridiag : ∀ i j : Fin N, i ≠ j → (i.val : ℝ) - (j.val : ℝ) ≠ 1 →
      (i.val : ℝ) - (j.val : ℝ) ≠ -1 → H_A i j = 0) :
    (H_A * bosonicRho N c Γ s).trace - (H_A * bosonicRho N c Γ 0).trace =
      ((∑ i : Fin N, H_A i i * bosonicRho N c Γ 0 i i) - (H_A * bosonicRho N c Γ 0).trace) *
        (1 - (Real.exp (-(Γ * s) / 2) : ℂ)) := by
  have hentry : ∀ i j : Fin N,
      H_A i j * bosonicRho N c Γ s j i - H_A i j * bosonicRho N c Γ 0 j i =
        (if i = j then (0 : ℂ) else -(H_A i j * bosonicRho N c Γ 0 j i)) *
          (1 - (Real.exp (-(Γ * s) / 2) : ℂ)) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp [bosonicRho]
    · by_cases hp : (i.val : ℝ) - (j.val : ℝ) = 1
      · have hsq : ((j.val : ℝ) - (i.val : ℝ)) ^ 2 = 1 := by
          have : (j.val : ℝ) - (i.val : ℝ) = -1 := by linarith
          rw [this]; ring
        simp only [hij, ↓reduceIte, bosonicRho, Matrix.of_apply, hsq, mul_one, mul_zero,
          neg_zero, zero_div, Real.exp_zero]
        push_cast
        ring
      · by_cases hm : (i.val : ℝ) - (j.val : ℝ) = -1
        · have hsq : ((j.val : ℝ) - (i.val : ℝ)) ^ 2 = 1 := by
            have : (j.val : ℝ) - (i.val : ℝ) = 1 := by linarith
            rw [this]; ring
          simp only [hij, ↓reduceIte, bosonicRho, Matrix.of_apply, hsq, mul_one, mul_zero,
            neg_zero, zero_div, Real.exp_zero]
          push_cast
          ring
        · have h0 : H_A i j = 0 := htridiag i j hij hp hm
          simp [h0]
  have htr_lhs : (H_A * bosonicRho N c Γ s).trace - (H_A * bosonicRho N c Γ 0).trace =
      ∑ i : Fin N, ∑ j : Fin N,
        (H_A i j * bosonicRho N c Γ s j i - H_A i j * bosonicRho N c Γ 0 j i) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib]
  rw [htr_lhs]
  simp_rw [hentry, ← Finset.sum_mul]
  congr 1
  have htr0 : (H_A * bosonicRho N c Γ 0).trace =
      ∑ i : Fin N, ∑ j : Fin N, H_A i j * bosonicRho N c Γ 0 j i := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [htr0, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsplit : ∑ j : Fin N, (if i = j then (0 : ℂ) else -(H_A i j * bosonicRho N c Γ 0 j i)) =
      H_A i i * bosonicRho N c Γ 0 i i - ∑ j : Fin N, H_A i j * bosonicRho N c Γ 0 j i := by
    have hadd : (∑ j : Fin N, (if i = j then (0 : ℂ) else -(H_A i j * bosonicRho N c Γ 0 j i))) +
        (∑ j : Fin N, H_A i j * bosonicRho N c Γ 0 j i) =
        H_A i i * bosonicRho N c Γ 0 i i := by
      rw [← Finset.sum_add_distrib]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji; simp [Ne.symm hji]
      · intro hi; exact (hi (Finset.mem_univ i)).elim
    linear_combination hadd
  exact hsplit

/-- Symmetric cross-horizon point-split Hadamard defect `ΔW_J(-ε, +ε)` for a free 2D chiral
boson current under uniform-`Γ` exterior dephasing:
`ΔW_J(-ε, +ε; s) = (1 - exp(-Γ s / 2)) / (16 π ε²)`. -/
noncomputable def hadamardHorizonDefect (Γ s ε : ℝ) : ℝ :=
  (1 - Real.exp (-(Γ * s) / 2)) / (16 * Real.pi * ε ^ 2)

/-- **Theorem 3(c)** (Point-Split Non-Hadamard Asymptotic Lemma vs. Observer-`A` Smoothness):
  (1) At `s = 0` (Observer `A`'s unperturbed Unruh input), `ΔW_J(-ε, +ε; 0) = 0` for all `ε > 0`.
  (2) For any `Γ > 0, s > 0` and every finite threshold `M > 0`, there exists `ε₀ > 0` such that
      `ΔW_J(-ε, +ε; s) > M` for all `0 < ε < ε₀` (`ε⁻²` point-split divergence at `X⁻ = 0`). -/
theorem continuum_hadamard_firewall_vs_smooth (Γ s : ℝ) :
    (∀ ε : ℝ, hadamardHorizonDefect Γ 0 ε = 0) ∧
    (0 < Γ → 0 < s → ∀ M : ℝ, 0 < M →
      ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → M < hadamardHorizonDefect Γ s ε) := by
  constructor
  · intro ε; unfold hadamardHorizonDefect; simp
  · intro hΓ hs M hM
    have hnum_pos : 0 < 1 - Real.exp (-(Γ * s) / 2) := by
      have hneg : -(Γ * s) / 2 < 0 := by nlinarith
      have hlt : Real.exp (-(Γ * s) / 2) < 1 := Real.exp_lt_one_iff.mpr hneg
      linarith
    have hden_pos : 0 < 16 * Real.pi * M := by
      have := Real.pi_pos
      positivity
    let ε0 : ℝ := Real.sqrt ((1 - Real.exp (-(Γ * s) / 2)) / (16 * Real.pi * M))
    have hε0_pos : 0 < ε0 := Real.sqrt_pos.mpr (div_pos hnum_pos hden_pos)
    refine ⟨ε0, hε0_pos, fun ε hε_pos hε_lt => ?_⟩
    unfold hadamardHorizonDefect
    have hε2_pos : 0 < 16 * Real.pi * ε ^ 2 := by
      have := Real.pi_pos
      positivity
    rw [lt_div_iff₀ hε2_pos]
    have hε2_lt : ε ^ 2 < ε0 ^ 2 := by nlinarith
    have hε0_sq : ε0 ^ 2 = (1 - Real.exp (-(Γ * s) / 2)) / (16 * Real.pi * M) :=
      Real.sq_sqrt (le_of_lt (div_pos hnum_pos hden_pos))
    rw [hε0_sq] at hε2_lt
    have hmul : M * (16 * Real.pi * ε ^ 2) < M * (16 * Real.pi * ((1 - Real.exp (-(Γ * s) / 2)) / (16 * Real.pi * M))) := by
      have h16piM : 0 < M * (16 * Real.pi) := by have := Real.pi_pos; positivity
      nlinarith
    have hcancel : M * (16 * Real.pi * ((1 - Real.exp (-(Γ * s) / 2)) / (16 * Real.pi * M))) =
        1 - Real.exp (-(Γ * s) / 2) := by
      have hne : 16 * Real.pi * M ≠ 0 := ne_of_gt hden_pos
      field_simp [hne]
    linarith

/-- Single-shot post-projection inertial energy `⟨n_R, n_L | H_A(ω) | n_R, n_L⟩`
for a bosonic Hawking mode of frequency `ω` and squeezing parameter `r`:
`ω ((2 n + 1) cosh(2 r) - 1)`. -/
noncomputable def singleShotInertialEnergy (ω r : ℝ) (n : ℕ) : ℝ :=
  ω * ((2 * (n : ℝ) + 1) * Real.cosh (2 * r) - 1)

/-- **Proposition 4 (Number-Projective Single-Shot Excitation Floor and Projector
Non-Commutativity)**:
  (1) On a single global Hilbert space, applying the selective exterior number-projective
      instrument `{|n_R⟩⟨n_R| ⊗ 1_L}` to the two-mode squeezed Unruh vacuum excites the
      squeezed-basis inertial quadratic form `H_A(ω)` for EVERY outcome `n : ℕ` of this
      number-projective instrument above the strictly positive floor
      `2 ω sinh²(r) = 2 ω n_BE(ω) > 0` (`ω > 0, r ≠ 0`):
      `⟨n_R, n_L | H_A(ω) | n_R, n_L⟩ = 2 ω (n cosh(2r) + sinh²(r)) ≥ 2 ω sinh²(r) > 0`.
      (This floor is uniform across outcomes of the number-projective instrument, not across
      arbitrary unravelings of number dephasing.)
  (2) On any truncated Schmidt space of dimension `N ≥ 2` with nonzero amplitudes
      `c_0, c_1 ≠ 0`, the inertial vacuum projector `P_A = |0_A⟩⟨0_A|` and exterior number
      projector `P_B = |0_R⟩⟨0_R| ⊗ 1_L` strictly fail to commute (`[P_A, P_B] ≠ 0`).
      (Note: non-commutativity precludes a joint PVM over all states and precludes any state
      simultaneously satisfying `P_A = 1` with a sharp `P_B` eigenvalue, but does not rule out
      common `(0, 0)` eigenstates when `N ≥ 3`.) -/
theorem single_shot_number_projection_firewall_floor (ω r : ℝ) (n : ℕ)
    (hω : 0 < ω) (hr : r ≠ 0) :
    singleShotInertialEnergy ω r n =
      2 * ω * ((n : ℝ) * Real.cosh (2 * r) + (Real.sinh r) ^ 2) ∧
    2 * ω * (Real.sinh r) ^ 2 ≤ singleShotInertialEnergy ω r n ∧
    0 < singleShotInertialEnergy ω r n ∧
    ∀ (N : ℕ) (hN : 2 ≤ N) (c : Fin N → ℝ),
      c ⟨0, by omega⟩ ≠ 0 → c ⟨1, by omega⟩ ≠ 0 →
      let P_A : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun i j => ((c i * c j : ℝ) : ℂ)
      let P_B : Matrix (Fin N) (Fin N) ℂ :=
        Matrix.of fun i j => if i = ⟨0, by omega⟩ ∧ j = ⟨0, by omega⟩ then (1 : ℂ) else 0
      comm P_A P_B ≠ 0 := by
  have hcosh_id : Real.cosh (2 * r) = 1 + 2 * (Real.sinh r) ^ 2 := by
    rw [Real.cosh_eq, Real.sinh_eq]
    have h2 : Real.exp (2 * r) = Real.exp r * Real.exp r := by
      rw [← Real.exp_add]; congr 1; ring
    have hm2 : Real.exp (-(2 * r)) = Real.exp (-r) * Real.exp (-r) := by
      rw [← Real.exp_add]; congr 1; ring
    have hprod : Real.exp r * Real.exp (-r) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [h2, hm2]
    linear_combination hprod
  have hform : singleShotInertialEnergy ω r n =
      2 * ω * ((n : ℝ) * Real.cosh (2 * r) + (Real.sinh r) ^ 2) := by
    unfold singleShotInertialEnergy
    linear_combination ω * hcosh_id
  have hcosh_pos : 0 < Real.cosh (2 * r) := Real.cosh_pos (2 * r)
  have hsinh_ne : Real.sinh r ≠ 0 := by
    intro h0
    have heq : Real.exp r = Real.exp (-r) := by
      rw [Real.sinh_eq] at h0
      linarith
    have hrr : r = -r := Real.exp_injective heq
    exact hr (by linarith)
  have hsinh2_pos : 0 < (Real.sinh r) ^ 2 := sq_pos_of_ne_zero hsinh_ne
  have hfloor : 2 * ω * (Real.sinh r) ^ 2 ≤ singleShotInertialEnergy ω r n := by
    rw [hform]
    have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hterm : 0 ≤ (n : ℝ) * Real.cosh (2 * r) := mul_nonneg hn_nonneg (le_of_lt hcosh_pos)
    nlinarith
  have hpos : 0 < singleShotInertialEnergy ω r n := by
    have hbase : 0 < 2 * ω * (Real.sinh r) ^ 2 := by positivity
    linarith
  refine ⟨hform, hfloor, hpos, ?_⟩
  intro N hN c hc0 hc1 P_A P_B hcomm
  let i0 : Fin N := ⟨0, by omega⟩
  let i1 : Fin N := ⟨1, by omega⟩
  have hne01 : i0 ≠ i1 := by
    intro heq
    have hv := congrArg Fin.val heq
    simp [i0, i1] at hv
  have hentry := congrFun (congrFun hcomm i0) i1
  have hAB : (P_A * P_B) i0 i1 = 0 := by
    simp only [Matrix.mul_apply, P_B, Matrix.of_apply]
    apply Finset.sum_eq_zero
    intro k _
    have hne : i1 ≠ ⟨0, by omega⟩ := fun h => hne01 h.symm
    simp [hne]
  have hBA : (P_B * P_A) i0 i1 = ((c i0 * c i1 : ℝ) : ℂ) := by
    simp only [Matrix.mul_apply, P_B, P_A, Matrix.of_apply]
    rw [Finset.sum_eq_single i0]
    · simp [i0]
    · intro k _ hki0
      have hne : k ≠ ⟨0, by omega⟩ := hki0
      simp [hne]
    · intro hmem; exact (hmem (Finset.mem_univ i0)).elim
  simp only [comm, Matrix.sub_apply, Matrix.zero_apply] at hentry
  rw [hAB, hBA, zero_sub, neg_eq_zero] at hentry
  have hreal : c i0 * c i1 = 0 := by exact_mod_cast hentry
  rcases mul_eq_zero.mp hreal with h0 | h1
  · exact hc0 h0
  · exact hc1 h1

/-- **Proposition 3 (Mellin Positive-Type Frequency Kernel PSD and Sharp Contact Threshold
`c_00 ≥ c_*`)**:
In Mellin frequency space `k ∈ ℝ` with attenuation factor `b ∈ [-1, 1]` (covering
`b(k) = exp(-Γ(κ |k|) s / 2) ∈ (0, 1]`):
  (1) The `2 × 2` Hermitian Mellin frequency matrix `[[e^{πk}, -b], [-b, e^{-πk}]]` has strictly
      positive diagonal entries and non-negative determinant `e^{πk} e^{-πk} - b² = 1 - b² ≥ 0`.
  (2) For ALL complex Mellin amplitudes `zR, zL ∈ ℂ`, the frequency-resolved quadratic form
      satisfies the exact Schur-complement sum-of-squares identity
        `e^{πk}|zR|² + e^{-πk}|zL|² - 2 b Re(zR zL*) = |e^{πk/2} zR - b e^{-πk/2} zL|² + (1 - b²) e^{-πk} |zL|² ≥ 0`.
  (3) For any point-contact extension `T_{c_00} = T_M + (c_00 - c_*) δ ⊗ δ`:
      (a) sufficiency: `c_00 ≥ c_*` implies `m + (c_00 - c_*) |q0|² ≥ 0` for all `m ≥ 0, q0 ∈ ℂ`;
      (b) sharp necessity: if a scale-averaged test sequence satisfies `m_ℓ → 0` and
          `0 ≤ m_ℓ + (c_00 - c_*)` for all `ℓ : ℕ`, then necessarily `c_00 ≥ c_*`. -/
theorem mellin_contact_kernel_psd_and_extension_positivity
    (k b : ℝ) (hb : |b| ≤ 1) (zR zL : ℂ) :
    0 < Real.exp (Real.pi * k) ∧
    0 < Real.exp (-(Real.pi * k)) ∧
    Real.exp (Real.pi * k) * Real.exp (-(Real.pi * k)) - b ^ 2 = 1 - b ^ 2 ∧
    0 ≤ 1 - b ^ 2 ∧
    Real.exp (Real.pi * k) * Complex.normSq zR +
        Real.exp (-(Real.pi * k)) * Complex.normSq zL -
        2 * b * (zR * star zL).re =
      Complex.normSq (((Real.exp (Real.pi * k / 2) : ℝ) : ℂ) * zR -
        ((b * Real.exp (-(Real.pi * k / 2)) : ℝ) : ℂ) * zL) +
      (1 - b ^ 2) * Real.exp (-(Real.pi * k)) * Complex.normSq zL ∧
    0 ≤ Real.exp (Real.pi * k) * Complex.normSq zR +
        Real.exp (-(Real.pi * k)) * Complex.normSq zL -
        2 * b * (zR * star zL).re ∧
    (∀ (c00 cstar m : ℝ) (q0 : ℂ), cstar ≤ c00 → 0 ≤ m →
      0 ≤ m + (c00 - cstar) * Complex.normSq q0) ∧
    (∀ (c00 cstar : ℝ) (m : ℕ → ℝ),
      Filter.Tendsto m Filter.atTop (nhds 0) →
      (∀ l : ℕ, 0 ≤ m l + (c00 - cstar)) →
      cstar ≤ c00) := by
  have hb2 : b ^ 2 ≤ 1 := by
    have h1 := abs_le.mp hb
    nlinarith
  have h1mb2 : 0 ≤ 1 - b ^ 2 := by linarith
  have hexp_prod : Real.exp (Real.pi * k) * Real.exp (-(Real.pi * k)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hhalf_pos : Real.exp (Real.pi * k / 2) * Real.exp (Real.pi * k / 2) =
      Real.exp (Real.pi * k) := by
    rw [← Real.exp_add]; congr 1; ring
  have hhalf_neg : Real.exp (-(Real.pi * k / 2)) * Real.exp (-(Real.pi * k / 2)) =
      Real.exp (-(Real.pi * k)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hhalf_cancel : Real.exp (Real.pi * k / 2) * Real.exp (-(Real.pi * k / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have hsos : Real.exp (Real.pi * k) * Complex.normSq zR +
        Real.exp (-(Real.pi * k)) * Complex.normSq zL -
        2 * b * (zR * star zL).re =
      Complex.normSq (((Real.exp (Real.pi * k / 2) : ℝ) : ℂ) * zR -
        ((b * Real.exp (-(Real.pi * k / 2)) : ℝ) : ℂ) * zL) +
      (1 - b ^ 2) * Real.exp (-(Real.pi * k)) * Complex.normSq zL := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im]
    linear_combination
      (zR.re * zR.re + zR.im * zR.im) * hhalf_pos.symm +
      (b ^ 2 * (zL.re * zL.re + zL.im * zL.im)) * hhalf_neg.symm -
      (2 * b * (zR.re * zL.re + zR.im * zL.im)) * hhalf_cancel.symm
  have hquad_nn : 0 ≤ Real.exp (Real.pi * k) * Complex.normSq zR +
      Real.exp (-(Real.pi * k)) * Complex.normSq zL -
      2 * b * (zR * star zL).re := by
    rw [hsos]
    have h1 : 0 ≤ Complex.normSq (((Real.exp (Real.pi * k / 2) : ℝ) : ℂ) * zR -
        ((b * Real.exp (-(Real.pi * k / 2)) : ℝ) : ℂ) * zL) := Complex.normSq_nonneg _
    have h2 : 0 ≤ (1 - b ^ 2) * Real.exp (-(Real.pi * k)) * Complex.normSq zL :=
      mul_nonneg (mul_nonneg h1mb2 (le_of_lt (Real.exp_pos _))) (Complex.normSq_nonneg _)
    linarith
  refine ⟨Real.exp_pos _, Real.exp_pos _, by rw [hexp_prod], h1mb2, hsos, hquad_nn, ?_, ?_⟩
  · intro c00 cstar m q0 hc hm
    have hdiff : 0 ≤ c00 - cstar := sub_nonneg.mpr hc
    have hterm : 0 ≤ (c00 - cstar) * Complex.normSq q0 :=
      mul_nonneg hdiff (Complex.normSq_nonneg _)
    linarith
  · intro c00 cstar m hm hpos
    have htend : Filter.Tendsto (fun l => m l + (c00 - cstar)) Filter.atTop
        (nhds (0 + (c00 - cstar))) := hm.add_const (c00 - cstar)
    have hge : 0 ≤ 0 + (c00 - cstar) :=
      ge_of_tendsto' htend hpos
    linarith

end OSTQD_SK
