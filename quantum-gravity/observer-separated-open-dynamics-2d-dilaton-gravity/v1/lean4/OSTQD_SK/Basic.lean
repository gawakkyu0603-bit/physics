import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# OSTQD_SK.Basic

Core finite-dimensional matrix GKSL superoperator definitions and Schwinger–Keldysh (SK)
influence-functional algebraic axioms (trace-preservation normalization, conjugation
symmetry, necessary probability-decay positivity `Im S_IF ≥ 0`, dynamical KMS / FDT
Wightman rate positivity under the full-anticommutator Keldysh kernel `D_K = 2 N`,
Layer-2 unraveling non-uniqueness, and separation of remote no-signaling from
Layer-1 channel model-compatibility) for the observer-separated Schwinger–Keldysh
effective action in 2D dilaton gravity.
-/

open scoped Matrix BigOperators ComplexConjugate

namespace OSTQD_SK

variable {d m n : ℕ}

/-- Matrix commutator `[A, B] = A B - B A`. -/
def comm (A B : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  A * B - B * A

/-- Matrix anticommutator `{A, B} = A B + B A`. -/
def anticomm (A B : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  A * B + B * A

/-- Single-jump GKSL (Lindblad) Schrödinger generator `L ρ L† - (1/2) {L† L, ρ}`. -/
noncomputable def gkslOne (L ρ : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  L * ρ * Lᴴ - (2⁻¹ : ℂ) • (Lᴴ * L * ρ + ρ * (Lᴴ * L))

/-- Multi-jump GKSL Schrödinger generator. -/
noncomputable def gksl (Ls : List (Matrix (Fin d) (Fin d) ℂ))
    (ρ : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  (Ls.map (fun L => gkslOne L ρ)).sum

/-- Single-jump GKSL Heisenberg (dual) generator `L† X L - (1/2) {L† L, X}`. -/
noncomputable def gkslDualOne (L X : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Lᴴ * X * L - (2⁻¹ : ℂ) • (Lᴴ * L * X + X * (Lᴴ * L))

/-- Multi-jump GKSL Heisenberg (dual) generator. -/
noncomputable def gkslDual (Ls : List (Matrix (Fin d) (Fin d) ℂ))
    (X : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  (Ls.map (fun L => gkslDualOne L X)).sum

/-- Single-jump carré du champ `L†(X²) - X L†(X) - L†(X) X`. -/
noncomputable def carreDuChampOne (L X : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  gkslDualOne L (X * X) - X * gkslDualOne L X - gkslDualOne L X * X

/-- Multi-jump carré du champ `L†(X²) - X L†(X) - L†(X) X`. -/
noncomputable def carreDuChamp (Ls : List (Matrix (Fin d) (Fin d) ℂ))
    (X : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  gkslDual Ls (X * X) - X * gkslDual Ls X - gkslDual Ls X * X

/-- Squared Frobenius norm `‖A‖_F² = ∑_{i,j} |A_{ij}|²`. -/
def frobNormSq (A : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, Complex.normSq (A i j)

lemma star_mul_self_re (z : ℂ) : (star z * z).re = Complex.normSq z := by
  simp [Complex.normSq_apply]

lemma star_mul_self_im (z : ℂ) : (star z * z).im = 0 := by
  simp
  ring

lemma frobNormSq_nonneg (A : Matrix (Fin m) (Fin n) ℂ) : 0 ≤ frobNormSq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

lemma trace_conjTranspose_mul_self_re (A : Matrix (Fin m) (Fin n) ℂ) :
    ((Aᴴ * A).trace).re = frobNormSq A := by
  unfold frobNormSq
  rw [Matrix.trace, Complex.re_sum]
  simp_rw [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum,
    star_mul_self_re]
  rw [Finset.sum_comm]

lemma trace_list_sum (Ms : List (Matrix (Fin d) (Fin d) ℂ)) :
    Ms.sum.trace = (Ms.map Matrix.trace).sum := by
  induction Ms with
  | nil => simp
  | cons M rest ih => simp [Matrix.trace_add, ih]

lemma trace_gkslOne_eq_zero (L ρ : Matrix (Fin d) (Fin d) ℂ) :
    (gkslOne L ρ).trace = 0 := by
  unfold gkslOne
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_add]
  have h1 : (L * ρ * Lᴴ).trace = (Lᴴ * L * ρ).trace := by
    rw [Matrix.trace_mul_cycle]
  have h2 : (ρ * (Lᴴ * L)).trace = (Lᴴ * L * ρ).trace := by
    rw [Matrix.trace_mul_comm]
  rw [h1, h2]
  simp only [smul_eq_mul]
  ring

/-- Exact trace preservation of every GKSL generator: `Tr(L(ρ)) = 0`. -/
theorem trace_gksl_eq_zero (Ls : List (Matrix (Fin d) (Fin d) ℂ))
    (ρ : Matrix (Fin d) (Fin d) ℂ) : (gksl Ls ρ).trace = 0 := by
  unfold gksl
  rw [trace_list_sum]
  induction Ls with
  | nil => simp
  | cons L rest ih =>
    simp only [List.map_cons, List.sum_cons, trace_gkslOne_eq_zero, zero_add]
    exact ih

lemma gkslDualOne_adj (L X ρ : Matrix (Fin d) (Fin d) ℂ) :
    (X * gkslOne L ρ).trace = (gkslDualOne L X * ρ).trace := by
  unfold gkslOne gkslDualOne
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_sub]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_smul]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, Matrix.trace_add]
  have h1 : (X * (L * ρ * Lᴴ)).trace = (Lᴴ * X * L * ρ).trace := by
    calc (X * (L * ρ * Lᴴ)).trace
        = ((X * L) * (ρ * Lᴴ)).trace := by simp [Matrix.mul_assoc]
      _ = ((ρ * Lᴴ) * (X * L)).trace := Matrix.trace_mul_comm _ _
      _ = (ρ * (Lᴴ * X * L)).trace := by simp [Matrix.mul_assoc]
      _ = (Lᴴ * X * L * ρ).trace := Matrix.trace_mul_comm _ _
  have h2 : (X * (Lᴴ * L * ρ)).trace = (X * (Lᴴ * L) * ρ).trace := by
    simp [Matrix.mul_assoc]
  have h3 : (X * (ρ * (Lᴴ * L))).trace = (Lᴴ * L * X * ρ).trace := by
    calc (X * (ρ * (Lᴴ * L))).trace
        = ((X * ρ) * (Lᴴ * L)).trace := by simp [Matrix.mul_assoc]
      _ = ((Lᴴ * L) * (X * ρ)).trace := Matrix.trace_mul_comm _ _
      _ = (Lᴴ * L * X * ρ).trace := by simp [Matrix.mul_assoc]
  rw [h1, h2, h3]
  simp only [smul_eq_mul]
  ring

/-- Exact Schrödinger–Heisenberg duality: `Tr(X L(ρ)) = Tr(L†(X) ρ)`. -/
theorem gksl_dual_adj (Ls : List (Matrix (Fin d) (Fin d) ℂ))
    (X ρ : Matrix (Fin d) (Fin d) ℂ) :
    (X * gksl Ls ρ).trace = (gkslDual Ls X * ρ).trace := by
  unfold gksl gkslDual
  induction Ls with
  | nil => simp
  | cons L rest ih =>
    simp only [List.map_cons, List.sum_cons, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
    rw [gkslDualOne_adj, ih]

/-!
### Schwinger–Keldysh (SK) Influence Functional Axioms and Dynamical KMS / FDT Mapping
-/

/-- Quadratic Schwinger–Keldysh influence Lagrangian for real Hermitian-jump fields
`(Kp, Km)` with couplings `γ`:
`L_IF(K_+, K_-) = (i / 2) ∑_k γ_k (K_{k,+} - K_{k,-})²`. -/
noncomputable def skQuadraticInfluence (γ Kp Km : Fin m → ℝ) : ℂ :=
  (Complex.I / 2) * ∑ k : Fin m, (γ k : ℂ) * ((Kp k - Km k : ℝ) : ℂ) ^ 2

/-- **SK Axiom 1 (Trace-Preservation Normalization)**: `L_IF(K, K) = 0`. -/
theorem sk_quadratic_tp_normalization (γ K : Fin m → ℝ) :
    skQuadraticInfluence γ K K = 0 := by
  unfold skQuadraticInfluence
  simp

/-- **SK Axiom 2 (Conjugation / Hermiticity Symmetry)**:
`L_IF(K_+, K_-)* = - L_IF(K_-, K_+)`. -/
theorem sk_quadratic_conjugation_symmetry (γ Kp Km : Fin m → ℝ) :
    star (skQuadraticInfluence γ Kp Km) = -skQuadraticInfluence γ Km Kp := by
  unfold skQuadraticInfluence
  simp only [star_mul, star_div₀, Complex.star_def, Complex.conj_I, map_ofNat,
    map_sum, map_mul, Complex.conj_ofReal, map_pow]
  have hsq : ∀ k : Fin m, ((Kp k - Km k : ℝ) : ℂ) ^ 2 = ((Km k - Kp k : ℝ) : ℂ) ^ 2 := by
    intro k
    push_cast
    ring
  simp_rw [hsq]
  ring

/-- **SK Axiom 3 (Necessary Probability-Decay Positivity `Im L_IF ≥ 0`)**:
Whenever all rates `γ k ≥ 0`, the imaginary part of the quadratic QND influence
Lagrangian (`N = γ_k`, equivalently `D_K = 2 γ_k` in `(i/4) D_K K_a² = (i/2) N K_a²`)
is non-negative (`Im L_IF = (1/2) ∑_k γ_k (K_{k,+} - K_{k,-})² ≥ 0`).
Note: pointwise `Im S_IF ≥ 0` is a necessary condition for CPTP evolution, not by itself
sufficient without a valid unitary dilation or positive semidefinite Kossakowski structure. -/
theorem sk_quadratic_im_nonneg (γ Kp Km : Fin m → ℝ) (hγ : ∀ k, 0 ≤ γ k) :
    (skQuadraticInfluence γ Kp Km).im = (1 / 2 : ℝ) * ∑ k : Fin m, γ k * (Kp k - Km k) ^ 2 ∧
    0 ≤ (skQuadraticInfluence γ Kp Km).im := by
  have him : (skQuadraticInfluence γ Kp Km).im =
      (1 / 2 : ℝ) * ∑ k : Fin m, γ k * (Kp k - Km k) ^ 2 := by
    unfold skQuadraticInfluence
    have hsum_cast : (∑ k : Fin m, (γ k : ℂ) * ((Kp k - Km k : ℝ) : ℂ) ^ 2) =
        ((∑ k : Fin m, γ k * (Kp k - Km k) ^ 2 : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hsum_cast]
    simp only [Complex.mul_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  refine ⟨him, ?_⟩
  rw [him]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun k _ => mul_nonneg (hγ k) (sq_nonneg _))

/-- **SK Dynamical KMS / Fluctuation-Dissipation Theorem (Bosonic Wightman Rates)**:
Given inverse Hawking temperature `β > 0`, mode frequency `ω > 0`, non-negative spectral
density `ρ_spec = G^> - G^< ≥ 0`, and full-anticommutator Keldysh noise kernel
`D_K = G^> + G^< = 2 N = coth(β ω / 2) · ρ_spec` (matching noise action `(i/4) O_a D_K O_a =
(i/2) O_a N O_a`), the unit-coupling downward and upward Wightman rates
`γ_↓ = (D_K + ρ_spec)/2 = N + ρ_spec/2` and `γ_↑ = (D_K - ρ_spec)/2 = N - ρ_spec/2` satisfy:
  (1) `γ_↓ ≥ 0` and `γ_↑ ≥ 0` (rate non-negativity),
  (2) `γ_↑ = exp(-β ω) · γ_↓` (exact dynamical KMS detailed-balance ratio),
  (3) `γ_↓ - γ_↑ = ρ_spec` (exact spectral sum rule). -/
theorem sk_fdt_wightman_rates (β ω ρ_spec : ℝ) (hβ : 0 < β) (hω : 0 < ω) (hρ : 0 ≤ ρ_spec) :
    let e := Real.exp (β * ω)
    let D_K := ((e + 1) / (e - 1)) * ρ_spec
    let γ_down := (D_K + ρ_spec) / 2
    let γ_up := (D_K - ρ_spec) / 2
    0 ≤ γ_down ∧ 0 ≤ γ_up ∧ γ_up = Real.exp (-(β * ω)) * γ_down ∧ γ_down - γ_up = ρ_spec := by
  intro e D_K γ_down γ_up
  have hbw : 0 < β * ω := mul_pos hβ hω
  have he_gt : 1 < e := Real.one_lt_exp_iff.mpr hbw
  have he_sub_pos : 0 < e - 1 := sub_pos.mpr he_gt
  have he_sub_ne : e - 1 ≠ 0 := ne_of_gt he_sub_pos
  have he_pos : 0 < e := lt_trans zero_lt_one he_gt
  have he_ne : e ≠ 0 := ne_of_gt he_pos
  have hgd : γ_down = (e / (e - 1)) * ρ_spec := by
    dsimp only [γ_down, D_K]
    field_simp [he_sub_ne]
    ring
  have hgu : γ_up = (1 / (e - 1)) * ρ_spec := by
    dsimp only [γ_up, D_K]
    field_simp [he_sub_ne]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hgd]; exact mul_nonneg (div_nonneg (le_of_lt he_pos) (le_of_lt he_sub_pos)) hρ
  · rw [hgu]; exact mul_nonneg (div_nonneg zero_le_one (le_of_lt he_sub_pos)) hρ
  · rw [hgd, hgu, Real.exp_neg]
    change (1 / (e - 1)) * ρ_spec = e⁻¹ * ((e / (e - 1)) * ρ_spec)
    field_simp [he_ne, he_sub_ne]
  · dsimp only [γ_down, γ_up]; ring

/-- **Layer-2 Unraveling Gauge Non-Uniqueness Witness (Remark 2)**:
  (1) For arbitrary Hilbert-space dimension `d`, any two Kraus operators `K0, K1 : M_d(ℂ)`,
      and any real orthogonal mixing `(u, v)` with `u² + v² = 1`, the rotated Kraus pair
      `K0' = u K0 + v K1`, `K1' = -v K0 + u K1` yields the IDENTICAL Layer-1 CPTP channel
      `K0' ρ K0'† + K1' ρ K1'† = K0 ρ K0† + K1 ρ K1†` for every `ρ` and preserves the
      trace-preservation sum `K0'† K0' + K1'† K1' = K0† K0 + K1† K1`.
  (2) Even for the completely dephasing qubit channel (`K0 = |0⟩⟨0|`, `K1 = |1⟩⟨1|`), the
      orthogonal gauge `(u, v) = (3/5, 4/5)` produces strictly different single-shot
      outcome probabilities on `|0⟩⟨0|` (`9/25 ≠ 1`) and strictly different post-measurement
      branch states on `|+⟩⟨+|` (nonzero unnormalized branch coherence `6/25 ≠ 0`,
      corresponding to normalized conditional coherence `12/25`, vs. collapsed `0`).
This provides an explicit finite-dimensional witness illustrating that a non-selective
Layer-1 CPTP map does not uniquely determine a selective Layer-2 unraveling. -/
theorem layer2_unraveling_gauge_nonuniqueness {d : ℕ}
    (K0 K1 ρ : Matrix (Fin d) (Fin d) ℂ) (u v : ℝ) (huv : u ^ 2 + v ^ 2 = 1) :
    let K0' : Matrix (Fin d) (Fin d) ℂ := (u : ℂ) • K0 + (v : ℂ) • K1
    let K1' : Matrix (Fin d) (Fin d) ℂ := (-(v : ℂ)) • K0 + (u : ℂ) • K1
    (K0' * ρ * K0'ᴴ + K1' * ρ * K1'ᴴ = K0 * ρ * K0ᴴ + K1 * ρ * K1ᴴ) ∧
    (K0'ᴴ * K0' + K1'ᴴ * K1' = K0ᴴ * K0 + K1ᴴ * K1) ∧
    (let P0 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun i j => if i = 0 ∧ j = 0 then 1 else 0
     let P1 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun i j => if i = 1 ∧ j = 1 then 1 else 0
     let Q0 : Matrix (Fin 2) (Fin 2) ℂ := ((3 / 5 : ℝ) : ℂ) • P0 + ((4 / 5 : ℝ) : ℂ) • P1
     let ρ0 : Matrix (Fin 2) (Fin 2) ℂ := P0
     let ρp : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun _ _ => (1 / 2 : ℂ)
     (Q0 * ρ0 * Q0ᴴ).trace ≠ (P0 * ρ0 * P0ᴴ).trace ∧
     (Q0 * ρp * Q0ᴴ) 0 1 ≠ (P0 * ρp * P0ᴴ) 0 1) := by
  intro K0' K1'
  have huvC : (u : ℂ) * (u : ℂ) + (v : ℂ) * (v : ℂ) = 1 := by
    have h1 : (((u ^ 2 + v ^ 2 : ℝ) : ℂ)) = (1 : ℂ) := by exact_mod_cast huv
    push_cast at h1
    linear_combination h1
  have hK0'h : K0'ᴴ = (u : ℂ) • K0ᴴ + (v : ℂ) • K1ᴴ := by
    dsimp only [K0']
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul]
    simp
  have hK1'h : K1'ᴴ = (-(v : ℂ)) • K0ᴴ + (u : ℂ) • K1ᴴ := by
    dsimp only [K1']
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul]
    simp
  have hch : K0' * ρ * K0'ᴴ + K1' * ρ * K1'ᴴ = K0 * ρ * K0ᴴ + K1 * ρ * K1ᴴ := by
    ext i j
    rw [hK0'h, hK1'h]
    dsimp only [K0', K1']
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination
      (K0 * ρ * K0ᴴ) i j * huvC + (K1 * ρ * K1ᴴ) i j * huvC
  have htp : K0'ᴴ * K0' + K1'ᴴ * K1' = K0ᴴ * K0 + K1ᴴ * K1 := by
    ext i j
    rw [hK0'h, hK1'h]
    dsimp only [K0', K1']
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination
      (K0ᴴ * K0) i j * huvC + (K1ᴴ * K1) i j * huvC
  refine ⟨hch, htp, ?_⟩
  intro P0 P1 Q0 ρ0 ρp
  constructor
  · have h1 : (P0 * ρ0 * P0ᴴ).trace = 1 := by
      simp [P0, ρ0, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fin.sum_univ_two]
    have h2 : (Q0 * ρ0 * Q0ᴴ).trace = (9 / 25 : ℂ) := by
      simp [Q0, P0, P1, ρ0, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fin.sum_univ_two, map_ofNat]
      norm_num
    rw [h1, h2]
    norm_num
  · have h1 : (P0 * ρp * P0ᴴ) 0 1 = 0 := by
      simp [P0, ρp, Matrix.mul_apply, Matrix.conjTranspose_apply]
    have h2 : (Q0 * ρp * Q0ᴴ) 0 1 = (6 / 25 : ℂ) := by
      simp [Q0, P0, P1, ρp, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two, map_ofNat]
      norm_num
    rw [h1, h2]
    norm_num

/-- **No-Signaling vs. Layer-1 Model-Compatibility Separation (Remark 2 & Proposition 4)**:
  (1) On any bipartite finite-dimensional factorization `Fin dR × Fin dL`, conjugating by ANY
      local exterior unitary `U ⊗ I_L` (`U† U = 1`) leaves every interior-local observable
      `I_R ⊗ Y_L` invariant in the Heisenberg picture (`(U ⊗ I_L)† (I_R ⊗ Y_L) (U ⊗ I_L) = I_R ⊗ Y_L`)
      and therefore preserves every interior expectation value `Tr((I_R ⊗ Y_L) ·)` (remote marginal
      no-signaling), completely independent of any target exterior channel `Φ_B`.
  (2) Conversely, on a qubit (`Fin 2`), the local Pauli-`X` unitary satisfies `X† X = 1` (hence
      no-signaling) while strictly differing from the target exterior dephasing channel
      `Φ_B(ρ) = P_0 ρ P_0 + P_1 ρ P_1` on `|0⟩⟨0|`. Thus `∑_x I_{B,x} = Φ_B` is a model-compatibility
      constraint to reproduce a specified Layer-1 channel, distinct from remote no-signaling. -/
theorem local_unitary_preserves_remote_marginal_vs_channel {dR dL : ℕ}
    (U : Matrix (Fin dR) (Fin dR) ℂ) (hU : Uᴴ * U = 1)
    (Y : Matrix (Fin dL) (Fin dL) ℂ)
    (ρ : Matrix (Fin dR × Fin dL) (Fin dR × Fin dL) ℂ) :
    let Uext : Matrix (Fin dR × Fin dL) (Fin dR × Fin dL) ℂ :=
      Matrix.of fun p q => if p.2 = q.2 then U p.1 q.1 else 0
    let Yint : Matrix (Fin dR × Fin dL) (Fin dR × Fin dL) ℂ :=
      Matrix.of fun p q => if p.1 = q.1 then Y p.2 q.2 else 0
    Uextᴴ * Yint * Uext = Yint ∧
    (Yint * (Uext * ρ * Uextᴴ)).trace = (Yint * ρ).trace ∧
    (let X2 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun i j => if i = j then 0 else 1
     let P0 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun i j => if i = 0 ∧ j = 0 then 1 else 0
     let P1 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun i j => if i = 1 ∧ j = 1 then 1 else 0
     X2ᴴ * X2 = 1 ∧ X2 * P0 * X2ᴴ ≠ P0 * P0 * P0ᴴ + P1 * P0 * P1ᴴ) := by
  intro Uext Yint
  have hUext_adj : ∀ p q : Fin dR × Fin dL,
      Uextᴴ p q = if p.2 = q.2 then Uᴴ p.1 q.1 else 0 := by
    intro p q
    simp only [Matrix.conjTranspose_apply, Uext, Matrix.of_apply]
    by_cases h : p.2 = q.2
    · simp [h]
    · have h' : q.2 ≠ p.2 := Ne.symm h
      simp [h, h']
  have hYU : ∀ p q : Fin dR × Fin dL,
      (Yint * Uext) p q = Y p.2 q.2 * U p.1 q.1 := by
    intro p q
    simp only [Matrix.mul_apply, Yint, Uext, Matrix.of_apply, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single p.1]
    · rw [Finset.sum_eq_single q.2]
      · simp
      · intro l _ hlq; simp [hlq]
      · intro hq; exact (hq (Finset.mem_univ q.2)).elim
    · intro r _ hrp
      apply Finset.sum_eq_zero
      intro l _; simp [Ne.symm hrp]
    · intro hp; exact (hp (Finset.mem_univ p.1)).elim
  have hheis : Uextᴴ * Yint * Uext = Yint := by
    rw [Matrix.mul_assoc]
    ext p q
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, hUext_adj, hYU]
    have hinner : ∑ r : Fin dR, ∑ l : Fin dL,
        (if p.2 = l then Uᴴ p.1 r else 0) * (Y l q.2 * U r q.1) =
        Y p.2 q.2 * (Uᴴ * U) p.1 q.1 := by
      rw [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.sum_eq_single p.2]
      · simp; ring
      · intro l _ hlp; simp [Ne.symm hlp]
      · intro hp; exact (hp (Finset.mem_univ p.2)).elim
    rw [hinner, hU]
    simp only [Yint, Matrix.of_apply, Matrix.one_apply]
    by_cases h1 : p.1 = q.1
    · simp [h1]
    · simp [h1]
  have htr : (Yint * (Uext * ρ * Uextᴴ)).trace = (Yint * ρ).trace := by
    calc (Yint * (Uext * ρ * Uextᴴ)).trace
        = ((Yint * Uext * ρ) * Uextᴴ).trace := by simp only [Matrix.mul_assoc]
      _ = (Uextᴴ * (Yint * Uext * ρ)).trace := Matrix.trace_mul_comm _ _
      _ = ((Uextᴴ * Yint * Uext) * ρ).trace := by simp only [Matrix.mul_assoc]
      _ = (Yint * ρ).trace := by rw [hheis]
  refine ⟨hheis, htr, ?_⟩
  intro X2 P0 P1
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [X2, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  · intro heq
    have h00 := congrFun (congrFun heq (0 : Fin 2)) (0 : Fin 2)
    simp [X2, P0, P1, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.add_apply,
      Fin.sum_univ_two] at h00

end OSTQD_SK
