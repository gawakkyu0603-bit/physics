import OSTQD_Layer2.Theorem1_SteeringNoGo

/-!
# OSTQD_Layer2.Theorem2_BranchingModels

Formalizes Theorem 2 of `paper3_layer2_type2`:
1. Model I signed global-section negativity lower bound `∑ Q⁻ ≥ (S - 2) / 4` for any signed
   quasi-probability decomposition `Q = Q⁺ - Q⁻` matching CHSH value `S`.
2. Explicit closed-form signed global section saturating `∑ Q⁻ = 1/5` on the rational `S = 14/5` witness.
3. Model II observer-relative Born-weighted branching presheaf: exact Layer-1 barycenter linearity,
   commuting shared-record CPL consistency, and non-affine quadratic weight negative control.
-/

open scoped Matrix BigOperators ComplexConjugate

namespace OSTQD_Layer2

variable {d k m : ℕ}

/-- Universal lower bound on total signed quasi-probability negativity:
    any signed distribution `Q = Q⁺ - Q⁻` (`Q⁺, Q⁻ ≥ 0`, `∑(Q⁺ - Q⁻) = 1`) achieving CHSH value `S`
    must carry negativity `∑ Q⁻ ≥ (S - 2) / 4`. -/
theorem signed_global_section_negativity_lower_bound
    (Qpos Qneg : Bool → Bool → Bool → Bool → ℝ)
    (hPos : ∀ a0 a1 b0 b1, 0 ≤ Qpos a0 a1 b0 b1)
    (hNeg : ∀ a0 a1 b0 b1, 0 ≤ Qneg a0 a1 b0 b1)
    (hNorm : ∑ a0 : Bool, ∑ a1 : Bool, ∑ b0 : Bool, ∑ b1 : Bool,
        (Qpos a0 a1 b0 b1 - Qneg a0 a1 b0 b1) = 1) :
    ((∑ a0 : Bool, ∑ a1 : Bool, ∑ b0 : Bool, ∑ b1 : Bool,
        chshPoly a0 a1 b0 b1 * (Qpos a0 a1 b0 b1 - Qneg a0 a1 b0 b1)) - 2) / 4 ≤
      ∑ a0 : Bool, ∑ a1 : Bool, ∑ b0 : Bool, ∑ b1 : Bool, Qneg a0 a1 b0 b1 := by
  have hpt : ∀ a0 a1 b0 b1 : Bool,
      chshPoly a0 a1 b0 b1 * (Qpos a0 a1 b0 b1 - Qneg a0 a1 b0 b1) ≤
        2 * (Qpos a0 a1 b0 b1 - Qneg a0 a1 b0 b1) + 4 * Qneg a0 a1 b0 b1 := by
    intro a0 a1 b0 b1
    have hle := chshPoly_le_two a0 a1 b0 b1
    have hge := neg_two_le_chshPoly a0 a1 b0 b1
    have hp := hPos a0 a1 b0 b1
    have hn := hNeg a0 a1 b0 b1
    nlinarith
  have hsum :
      (∑ a0 : Bool, ∑ a1 : Bool, ∑ b0 : Bool, ∑ b1 : Bool,
        chshPoly a0 a1 b0 b1 * (Qpos a0 a1 b0 b1 - Qneg a0 a1 b0 b1)) ≤
      (∑ a0 : Bool, ∑ a1 : Bool, ∑ b0 : Bool, ∑ b1 : Bool,
        (2 * (Qpos a0 a1 b0 b1 - Qneg a0 a1 b0 b1) + 4 * Qneg a0 a1 b0 b1)) :=
    Finset.sum_le_sum fun a0 _ => Finset.sum_le_sum fun a1 _ =>
      Finset.sum_le_sum fun b0 _ => Finset.sum_le_sum fun b1 _ => hpt a0 a1 b0 b1
  have hrhs :
      (∑ a0 : Bool, ∑ a1 : Bool, ∑ b0 : Bool, ∑ b1 : Bool,
        (2 * (Qpos a0 a1 b0 b1 - Qneg a0 a1 b0 b1) + 4 * Qneg a0 a1 b0 b1)) =
      2 + 4 * (∑ a0 : Bool, ∑ a1 : Bool, ∑ b0 : Bool, ∑ b1 : Bool, Qneg a0 a1 b0 b1) := by
    simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hNorm]
    ring
  linarith

/-- Explicit closed-form signed global section saturating `∑ Q⁻ = 1/5` on the rational `S = 14/5` table:
    weights `w1 = 1/5` on `b0=b1=a0`, `w2 = 1/10` on `b0≠b1 ∧ b0=a1`, `w3 = 0` on `b0=b1≠a0`,
    and `w4 = -1/20` on `b0≠b1 ∧ b0≠a1`. -/
noncomputable def rationalSignedPos (a0 a1 b0 b1 : Bool) : ℝ :=
  if b0 = b1 then (if b0 = a0 then 1/5 else 0)
  else (if b0 = a1 then 1/10 else 0)

noncomputable def rationalSignedNeg (_a0 a1 b0 b1 : Bool) : ℝ :=
  if b0 ≠ b1 ∧ b0 ≠ a1 then 1/20 else 0

theorem signed_global_section_rational_witness_sharp :
    (∀ a0 a1 b0 b1, 0 ≤ rationalSignedPos a0 a1 b0 b1) ∧
    (∀ a0 a1 b0 b1, 0 ≤ rationalSignedNeg a0 a1 b0 b1) ∧
    (∑ a0 : Bool, ∑ a1 : Bool, ∑ b0 : Bool, ∑ b1 : Bool,
      (rationalSignedPos a0 a1 b0 b1 - rationalSignedNeg a0 a1 b0 b1) = 1) ∧
    (∑ a0 : Bool, ∑ a1 : Bool, ∑ b0 : Bool, ∑ b1 : Bool,
      bSign a0 * bSign b0 * (rationalSignedPos a0 a1 b0 b1 - rationalSignedNeg a0 a1 b0 b1) = 4/5) ∧
    (∑ a0 : Bool, ∑ a1 : Bool, ∑ b0 : Bool, ∑ b1 : Bool,
      bSign a0 * bSign b1 * (rationalSignedPos a0 a1 b0 b1 - rationalSignedNeg a0 a1 b0 b1) = 4/5) ∧
    (∑ a0 : Bool, ∑ a1 : Bool, ∑ b0 : Bool, ∑ b1 : Bool,
      bSign a1 * bSign b0 * (rationalSignedPos a0 a1 b0 b1 - rationalSignedNeg a0 a1 b0 b1) = 3/5) ∧
    (∑ a0 : Bool, ∑ a1 : Bool, ∑ b0 : Bool, ∑ b1 : Bool,
      bSign a1 * bSign b1 * (rationalSignedPos a0 a1 b0 b1 - rationalSignedNeg a0 a1 b0 b1) = -3/5) ∧
    (∑ a0 : Bool, ∑ a1 : Bool, ∑ b0 : Bool, ∑ b1 : Bool, rationalSignedNeg a0 a1 b0 b1 = 1/5) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a0 a1 b0 b1; cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> norm_num [rationalSignedPos]
  · intro a0 a1 b0 b1; cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> norm_num [rationalSignedNeg]
  · norm_num [rationalSignedPos, rationalSignedNeg]
  · norm_num [rationalSignedPos, rationalSignedNeg, bSign]
  · norm_num [rationalSignedPos, rationalSignedNeg, bSign]
  · norm_num [rationalSignedPos, rationalSignedNeg, bSign]
  · norm_num [rationalSignedPos, rationalSignedNeg, bSign]
  · norm_num [rationalSignedNeg]

/-- Model II observer-relative Born-weighted branch barycenter reproduces Layer-1 evolution identically. -/
theorem presheaf_barycenter_reproduces_layer1
    (Ks : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (ρ : Matrix (Fin d) (Fin d) ℂ)
    (hNonzero : ∀ x : Fin k, (krausBranch (Ks x) ρ).trace ≠ 0) :
    (∑ x : Fin k,
      (krausBranch (Ks x) ρ).trace •
        (((krausBranch (Ks x) ρ).trace)⁻¹ • krausBranch (Ks x) ρ)) =
      nonSelectiveMap Ks ρ := by
  unfold nonSelectiveMap
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [smul_smul, mul_inv_cancel₀ (hNonzero x), one_smul]

/-- Common-future CPL consistency on commuting shared record effects `{E_a}`, `{F_b}`:
    joint probabilities `T(a,b) = Tr(E_a F_b ρ)` reproduce both observer marginals identically. -/
theorem commuting_records_cpl_marginals
    (Es : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (Fs : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hSumE : (∑ a : Fin k, Es a) = 1)
    (hSumF : (∑ b : Fin m, Fs b) = 1)
    (hComm : ∀ a b, Es a * Fs b = Fs b * Es a)
    (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (∀ a : Fin k, (∑ b : Fin m, bornWeight (Es a * Fs b) ρ) = bornWeight (Es a) ρ) ∧
    (∀ b : Fin m, (∑ a : Fin k, bornWeight (Es a * Fs b) ρ) = bornWeight (Fs b) ρ) := by
  constructor
  · intro a
    unfold bornWeight
    rw [← Matrix.trace_sum, ← Finset.sum_mul, ← Finset.mul_sum, hSumF, mul_one]
  · intro b
    unfold bornWeight
    have hswap : ∀ a : Fin k, (Es a * Fs b * ρ).trace = (Fs b * Es a * ρ).trace := by
      intro a; rw [hComm a b]
    simp_rw [hswap]
    rw [← Matrix.trace_sum, ← Finset.sum_mul, ← Finset.mul_sum, hSumE, mul_one]

/-- Negative control: a non-affine purity-weighted branch rule `w_nl(ρ) = Tr(ρ²) Tr(E ρ)`
    strictly violates convex affineness on a classical mixture of `|0⟩⟨0|` and `|1⟩⟨1|`. -/
theorem nonaffine_quadratic_weight_fails_convexity :
    let E : Matrix (Fin 2) (Fin 2) ℝ := !![3/4, 0; 0, 1/4]
    let ρ1 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
    let ρ2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 1]
    let wNL := fun (ρ : Matrix (Fin 2) (Fin 2) ℝ) => (ρ * ρ).trace * (E * ρ).trace
    wNL ((1/2 : ℝ) • ρ1 + (1/2 : ℝ) • ρ2) ≠ (1/2 : ℝ) * wNL ρ1 + (1/2 : ℝ) * wNL ρ2 := by
  intro E ρ1 ρ2 wNL
  norm_num [wNL, E, ρ1, ρ2, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]

/-- Counterexample (R1): identical uniform marginals `(1/2, 1/2)` do NOT imply record agreement;
    the independent joint table `T_{ab} = 1/4` has `P(a ≠ b) = 1/2 > 0`. -/
theorem equal_marginals_do_not_imply_record_agreement :
    let T : Fin 2 → Fin 2 → ℝ := fun _ _ => 1/4
    (∀ a b, 0 ≤ T a b) ∧
    (∀ a, ∑ b : Fin 2, T a b = 1/2) ∧
    (∀ b, ∑ a : Fin 2, T a b = 1/2) ∧
    T 0 1 + T 1 0 = 1/2 := by
  intro T
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b; norm_num [T]
  · intro a; norm_num [T, Fin.sum_univ_two]
  · intro b; norm_num [T, Fin.sum_univ_two]
  · norm_num [T]

/-- Counterexample (R1): commuting POVM effects `[K_aᴴ K_a, F_b] = 0` do NOT guarantee sequential
    Kraus record agreement; bit-flipping `K_a = X P_a` with `F_b = P_b` on `ρ = I/2` gives static
    joint disagreement `0` yet sequential disagreement `1`. -/
theorem commuting_effects_kraus_flip_counterexample :
    let P0 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]
    let P1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 0, 1]
    let X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
    let K0 : Matrix (Fin 2) (Fin 2) ℂ := X * P0
    let K1 : Matrix (Fin 2) (Fin 2) ℂ := X * P1
    let ρ : Matrix (Fin 2) (Fin 2) ℂ := !![(2⁻¹ : ℂ), 0; 0, (2⁻¹ : ℂ)]
    K0ᴴ * K0 = P0 ∧ K1ᴴ * K1 = P1 ∧ K0ᴴ * K0 + K1ᴴ * K1 = 1 ∧
    (P0 * P1 * ρ).trace + (P1 * P0 * ρ).trace = 0 ∧
    (P1 * (K0 * ρ * K0ᴴ)).trace + (P0 * (K1 * ρ * K1ᴴ)).trace = 1 := by
  intro P0 P1 X K0 K1 ρ
  have hK0 : K0 = !![0, 0; 1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [K0, X, P0]
  have hK1 : K1 = !![0, 1; 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [K1, X, P1]
  have hK0H : K0ᴴ = !![0, 1; 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hK0, Matrix.conjTranspose_apply]
  have hK1H : K1ᴴ = !![0, 0; 1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hK1, Matrix.conjTranspose_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [hK0, P0, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [hK1, P1, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [hK0, hK1, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [P0, P1, ρ, Matrix.trace, Fin.sum_univ_two]
  · rw [hK0H, hK1H, hK0, hK1]
    simp only [P0, P1, ρ, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    norm_num

/-- Concrete finite-dimensional Wigner's friend dilation (R1): unitary CNOT premeasurement `U_SF`
    on `|+⟩_S |0⟩_F` produces `|Φ⁺⟩_{SF}`, giving exact record-preserving CPL agreement
    `P(x_S ≠ x_F) = 0`, while Wigner's interference projector `|Φ⁺⟩⟨Φ⁺|` yields `1` on the coherent
    state vs. `1/2` on the record-dephased branch mixture. -/
theorem wigner_friend_record_preserving_vs_interference :
    let U_SF : Matrix (Fin 4) (Fin 4) ℝ :=
      !![1, 0, 0, 0;
         0, 1, 0, 0;
         0, 0, 0, 1;
         0, 0, 1, 0]
    let ρ_init : Matrix (Fin 4) (Fin 4) ℝ :=
      !![1/2, 0, 1/2, 0;
         0,   0, 0,   0;
         1/2, 0, 1/2, 0;
         0,   0, 0,   0]
    let ρ_coh : Matrix (Fin 4) (Fin 4) ℝ := U_SF * ρ_init * U_SFᵀ
    let P00 : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1, 0, 0, 0]
    let P01 : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![0, 1, 0, 0]
    let P10 : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![0, 0, 1, 0]
    let P11 : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![0, 0, 0, 1]
    let ρ_deph : Matrix (Fin 4) (Fin 4) ℝ :=
      P00 * ρ_coh * P00 + P01 * ρ_coh * P01 + P10 * ρ_coh * P10 + P11 * ρ_coh * P11
    U_SFᵀ * U_SF = 1 ∧
    (P01 * ρ_coh).trace + (P10 * ρ_coh).trace = 0 ∧
    (ρ_coh * ρ_coh).trace = 1 ∧
    (ρ_coh * ρ_deph).trace = 1/2 := by
  intro U_SF ρ_init ρ_coh P00 P01 P10 P11 ρ_deph
  have hUT : U_SFᵀ = U_SF := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [U_SF]
  have hCoh : ρ_coh = !![1/2, 0, 0, 1/2; 0, 0, 0, 0; 0, 0, 0, 0; 1/2, 0, 0, 1/2] := by
    change U_SF * ρ_init * U_SFᵀ = _
    rw [hUT]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [U_SF, ρ_init, Matrix.mul_apply, Fin.sum_univ_four]
  have hDeph : ρ_deph = !![1/2, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1/2] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [ρ_deph, hCoh, P00, P01, P10, P11, Matrix.mul_apply, Matrix.diagonal_apply,
        Fin.sum_univ_four]
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [U_SF, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four]
  · rw [hCoh]
    norm_num [P01, P10, Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_four]
  · rw [hCoh]
    norm_num [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_four]
  · rw [hCoh, hDeph]
    norm_num [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_four]

/-- Standard single-entry matrix unit `|i⟩⟨j|` on `Fin d`. -/
def matrixUnit (i j : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun a b => if a = i ∧ b = j then 1 else 0

/-- Finite-dimensional trace-duality (Riesz) representation (C1): every `ℂ`-linear functional `f`
    on `M_d(ℂ)` admits a unique representing matrix `E` with `f ρ = Tr(E ρ)` for all `ρ`. -/
theorem finite_dim_linear_functional_unique_povm_rep
    (f : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ℂ) :
    ∃! E : Matrix (Fin d) (Fin d) ℂ, ∀ ρ, f ρ = bornWeight E ρ := by
  refine ⟨Matrix.of fun i j => f (matrixUnit j i), ?_, ?_⟩
  · intro ρ
    have hdecomp : ρ = ∑ i : Fin d, ∑ j : Fin d, ρ i j • matrixUnit i j := by
      ext a b
      rw [Matrix.sum_apply]
      simp_rw [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, matrixUnit, Matrix.of_apply]
      rw [Finset.sum_eq_single a]
      · rw [Finset.sum_eq_single b]
        · simp
        · intro j _ hjb; simp [Ne.symm hjb]
        · intro hb; exact absurd (Finset.mem_univ b) hb
      · intro i _ hia
        refine Finset.sum_eq_zero fun j _ => ?_
        simp [Ne.symm hia]
      · intro ha; exact absurd (Finset.mem_univ a) ha
    conv_lhs => rw [hdecomp]
    simp_rw [map_sum, map_smul, smul_eq_mul]
    unfold bornWeight
    rw [Matrix.trace]
    simp_rw [Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · intro E hE
    ext i j
    have hunit := hE (matrixUnit j i)
    rw [Matrix.of_apply, hunit]
    unfold bornWeight
    rw [Matrix.trace]
    simp_rw [Matrix.diag_apply, Matrix.mul_apply, matrixUnit, Matrix.of_apply]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hbj; simp [hbj]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    · intro a _ hai
      refine Finset.sum_eq_zero fun b _ => ?_
      simp [hai]
    · intro hi; exact absurd (Finset.mem_univ i) hi

/-- Rank-one projector matrix `|v⟩⟨v|` on `Fin d`. -/
def rankOneProj (v : Fin d → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => v i * star (v j)

lemma bornWeight_rankOneProj (E : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) :
    bornWeight E (rankOneProj v) = dotProduct (star v) (E.mulVec v) := by
  unfold bornWeight rankOneProj
  rw [Matrix.trace]
  simp_rw [Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply, dotProduct, Matrix.mulVec,
    dotProduct, Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Complete finite-dimensional positive linear-functional POVM representation (RR-4):
    given `k` `ℂ`-linear functionals `fs : Fin k → (M_d(ℂ) →ₗ[ℂ] ℂ)` that take real nonnegative
    values on every rank-one projector `|v⟩⟨v|` and sum to `Tr(ρ)` on every matrix `ρ`,
    there exists a unique POVM family `Es : Fin k → M_d(ℂ)` satisfying:
    (1) exact trace representation `fs x ρ = Tr(Es x * ρ)` for all `x, ρ`,
    (2) Hermiticity `(Es x)ᴴ = Es x` for all `x`,
    (3) positive semidefiniteness `Im ⟨v, Es x v⟩ = 0 ∧ 0 ≤ Re ⟨v, Es x v⟩` for all `x, v`,
    (4) completeness `∑ x, Es x = 1`, and
    (5) effect upper bound `Re ⟨v, Es x v⟩ ≤ Re ⟨v, v⟩` for all `x, v`. -/
theorem finite_dim_complete_positive_functional_povm_rep
    (fs : Fin k → (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ℂ))
    (hReal : ∀ x : Fin k, ∀ v : Fin d → ℂ, (fs x (rankOneProj v)).im = 0)
    (hPos : ∀ x : Fin k, ∀ v : Fin d → ℂ, 0 ≤ (fs x (rankOneProj v)).re)
    (hComp : ∀ ρ : Matrix (Fin d) (Fin d) ℂ, (∑ x : Fin k, fs x ρ) = ρ.trace) :
    ∃! Es : Fin k → Matrix (Fin d) (Fin d) ℂ,
      (∀ x ρ, fs x ρ = bornWeight (Es x) ρ) ∧
      (∀ x, (Es x)ᴴ = Es x) ∧
      (∀ x (v : Fin d → ℂ),
        (dotProduct (star v) ((Es x).mulVec v)).im = 0 ∧
        0 ≤ (dotProduct (star v) ((Es x).mulVec v)).re) ∧
      (∑ x : Fin k, Es x) = 1 ∧
      (∀ x (v : Fin d → ℂ),
        (dotProduct (star v) ((Es x).mulVec v)).re ≤ (dotProduct (star v) v).re) := by
  let Es : Fin k → Matrix (Fin d) (Fin d) ℂ :=
    fun x => Matrix.of fun i j => fs x (matrixUnit j i)
  have hRep : ∀ x ρ, fs x ρ = bornWeight (Es x) ρ := by
    intro x ρ
    obtain ⟨E0, hE0, -⟩ := finite_dim_linear_functional_unique_povm_rep (fs x)
    have hEq : E0 = Es x := by
      ext i j
      have h1 := hE0 (matrixUnit j i)
      simp only [Es, Matrix.of_apply]
      rw [h1]
      unfold bornWeight
      rw [Matrix.trace]
      simp_rw [Matrix.diag_apply, Matrix.mul_apply, matrixUnit, Matrix.of_apply]
      rw [Finset.sum_eq_single i]
      · rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hbj; simp [hbj]
        · intro hj; exact absurd (Finset.mem_univ j) hj
      · intro a _ hai
        refine Finset.sum_eq_zero fun b _ => ?_
        simp [hai]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [← hEq]
    exact hE0 ρ
  have hQuad : ∀ x (v : Fin d → ℂ),
      (dotProduct (star v) ((Es x).mulVec v)).im = 0 ∧
      0 ≤ (dotProduct (star v) ((Es x).mulVec v)).re := by
    intro x v
    rw [← bornWeight_rankOneProj, ← hRep x (rankOneProj v)]
    exact ⟨hReal x v, hPos x v⟩
  have hHerm : ∀ x, (Es x)ᴴ = Es x := by
    intro x
    let E := Es x
    have hdiag : ∀ i : Fin d, (E i i).im = 0 := by
      intro i
      have hq := (hQuad x (Pi.single i (1 : ℂ))).1
      have hval : dotProduct (star (Pi.single i (1 : ℂ))) (E.mulVec (Pi.single i (1 : ℂ))) = E i i := by
        simp [dotProduct, Matrix.mulVec, Pi.single_apply]
      rw [hval] at hq
      exact hq
    ext i j
    rw [Matrix.conjTranspose_apply]
    change star (E j i) = E i j
    by_cases hij : i = j
    · subst hij
      apply Complex.ext
      · simp
      · simp [hdiag i]
    · have hsum_eval : ∀ (c : ℂ),
          let v : Fin d → ℂ := Pi.single i (1 : ℂ) + Pi.single j c
          dotProduct (star v) (E.mulVec v) =
            E i i + c * E i j + star c * E j i + star c * c * E j j := by
        intro c v
        have hv_i : v i = 1 := by simp [v, hij]
        have hv_j : v j = c := by simp [v, Ne.symm hij]
        have hv_ne : ∀ a : Fin d, a ≠ i → a ≠ j → v a = 0 := by
          intro a hai haj; simp [v, hai, haj]
        have hmv : ∀ a : Fin d, E.mulVec v a = E a i + c * E a j := by
          intro a
          rw [Matrix.mulVec, dotProduct]
          have hpair :
              (∑ b : Fin d, E a b * v b) = E a i * v i + E a j * v j := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
            congr 1
            rw [Finset.sum_eq_single j]
            · intro b hb hbj
              have hbi : b ≠ i := (Finset.mem_erase.mp hb).1
              rw [hv_ne b hbi hbj, mul_zero]
            · intro hj
              exact absurd (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩) hj
          rw [hpair, hv_i, hv_j]; ring
        rw [dotProduct]
        simp_rw [Pi.star_apply]
        have houter :
            (∑ a : Fin d, star (v a) * E.mulVec v a) =
              star (v i) * E.mulVec v i + star (v j) * E.mulVec v j := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
          congr 1
          rw [Finset.sum_eq_single j]
          · intro a ha haj
            have hai : a ≠ i := (Finset.mem_erase.mp ha).1
            rw [hv_ne a hai haj, star_zero, zero_mul]
          · intro hj
            exact absurd (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩) hj
        rw [houter, hv_i, hv_j, hmv i, hmv j]
        simp only [star_one, one_mul]
        ring
      have h1im : (E i i + (1 : ℂ) * E i j + star (1 : ℂ) * E j i + star (1 : ℂ) * 1 * E j j).im = 0 := by
        rw [← hsum_eval 1]
        exact (hQuad x _).1
      have hIim : (E i i + Complex.I * E i j + star Complex.I * E j i + star Complex.I * Complex.I * E j j).im = 0 := by
        rw [← hsum_eval Complex.I]
        exact (hQuad x _).1
      simp only [Complex.add_im, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
        Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, hdiag i, hdiag j,
        one_mul, zero_mul, mul_zero, mul_one, add_zero, zero_add, neg_zero] at h1im hIim
      apply Complex.ext
      · simp only [Complex.star_def, Complex.conj_re]; linarith
      · simp only [Complex.star_def, Complex.conj_im]; linarith
  have hSum : (∑ x : Fin k, Es x) = 1 := by
    ext i j
    rw [Matrix.sum_apply]
    simp_rw [Es, Matrix.of_apply]
    rw [hComp (matrixUnit j i), Matrix.trace]
    simp_rw [Matrix.diag_apply, matrixUnit, Matrix.of_apply]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq, Finset.sum_eq_single i]
      · simp
      · intro a _ hai; simp [hai]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    · rw [Matrix.one_apply_ne hij]
      refine Finset.sum_eq_zero fun a _ => ?_
      by_cases haj : a = j
      · subst haj; simp [Ne.symm hij]
      · simp [haj]
  have hLeOne : ∀ x (v : Fin d → ℂ),
      (dotProduct (star v) ((Es x).mulVec v)).re ≤ (dotProduct (star v) v).re := by
    intro x v
    have htot :
        (∑ y : Fin k, (dotProduct (star v) ((Es y).mulVec v)).re) = (dotProduct (star v) v).re := by
      rw [← Complex.re_sum]
      have hmat :
          (∑ y : Fin k, dotProduct (star v) ((Es y).mulVec v)) =
            dotProduct (star v) ((∑ y : Fin k, Es y).mulVec v) := by
        simp_rw [dotProduct, Matrix.mulVec, dotProduct, Matrix.sum_apply, Finset.sum_mul,
          Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
      rw [hmat, hSum, Matrix.one_mulVec]
    rw [← htot]
    exact Finset.single_le_sum (fun y _ => (hQuad y v).2) (Finset.mem_univ x)
  refine ⟨Es, ⟨hRep, hHerm, hQuad, hSum, hLeOne⟩, ?_⟩
  rintro Es' ⟨hRep', -, -, -, -⟩
  funext x
  obtain ⟨_, _, hUniq⟩ := finite_dim_linear_functional_unique_povm_rep (fs x)
  exact (hUniq (Es' x) (hRep' x)).trans (hUniq (Es x) (hRep x)).symm

/-- Replacer unraveling non-uniqueness counterexample (C1): for any density state `σ` (`Tr σ = 1`)
    and distinct weights `a ≠ b`, the two instruments `I_0^{(c)}(ρ) = c Tr(ρ) σ`,
    `I_1^{(c)}(ρ) = (1 - c) Tr(ρ) σ` produce the exact same Layer-1 replacer channel and the same
    normalized branch state `σ`, yet carry distinct branch weights `a ≠ b`. -/
theorem replacer_unraveling_weight_nonuniqueness
    (σ : Matrix (Fin d) (Fin d) ℂ) (hσ : σ.trace = 1) (a b : ℂ) (hab : a ≠ b) :
    let I0 := fun (c : ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ) => c • (ρ.trace • σ)
    let I1 := fun (c : ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ) => (1 - c) • (ρ.trace • σ)
    (∀ ρ, I0 a ρ + I1 a ρ = I0 b ρ + I1 b ρ) ∧
    (∀ ρ, ρ.trace = 1 → (I0 a ρ).trace = a ∧ (I0 b ρ).trace = b ∧ (I0 a ρ).trace ≠ (I0 b ρ).trace) := by
  intro I0 I1
  constructor
  · intro ρ
    simp only [I0, I1]
    rw [← add_smul, ← add_smul]
    have h1 : a + (1 - a) = 1 := by ring
    have h2 : b + (1 - b) = 1 := by ring
    rw [h1, h2]
  · intro ρ hρ
    simp [I0, hρ, hσ, hab]

/-- Necessary and sufficient Kraus criterion for all-input one-step sequential record agreement:
    for Kraus operators `{K_α}` (of outcome `a`) and any PSD subsequent effect `F = Rᴴ R`
    (of outcome `b ≠ a`), the disagreement probability `Re Tr(F ∑_α K_α |v⟩⟨v| K_αᴴ)` vanishes
    for every input vector `v` if and only if `∑_α K_αᴴ F K_α = 0`. -/
theorem sequential_record_agreement_iff_kraus_orthogonality
    (Ks : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (R : Matrix (Fin d) (Fin d) ℂ) :
    (∀ v : Fin d → ℂ,
      (∑ α : Fin m, ((Rᴴ * R) * (Ks α * rankOneProj v * (Ks α)ᴴ)).trace).re = 0) ↔
    (∑ α : Fin m, (Ks α)ᴴ * (Rᴴ * R) * Ks α) = 0 := by
  have hcyc : ∀ (α : Fin m) (ρ : Matrix (Fin d) (Fin d) ℂ),
      ((Rᴴ * R) * (Ks α * ρ * (Ks α)ᴴ)).trace =
        (((R * Ks α)ᴴ * (R * Ks α)) * ρ).trace := by
    intro α ρ
    have h1 : ((Rᴴ * R) * (Ks α * ρ * (Ks α)ᴴ)).trace =
        ((Ks α)ᴴ * (Rᴴ * R) * Ks α * ρ).trace := by
      calc ((Rᴴ * R) * (Ks α * ρ * (Ks α)ᴴ)).trace
          = (((Rᴴ * R) * Ks α * ρ) * (Ks α)ᴴ).trace := by simp [Matrix.mul_assoc]
        _ = ((Ks α)ᴴ * ((Rᴴ * R) * Ks α * ρ)).trace := Matrix.trace_mul_comm _ _
        _ = ((Ks α)ᴴ * (Rᴴ * R) * Ks α * ρ).trace := by simp [Matrix.mul_assoc]
    rw [h1]
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  constructor
  · intro hZero
    have hSumBasis : (∑ j : Fin d, rankOneProj (Pi.single j (1 : ℂ))) = 1 := by
      ext a b
      rw [Matrix.sum_apply]
      simp_rw [rankOneProj, Matrix.of_apply]
      by_cases hab : a = b
      · subst hab
        rw [Matrix.one_apply_eq, Finset.sum_eq_single a]
        · simp
        · intro j _ hja; simp [Ne.symm hja]
        · intro ha; exact absurd (Finset.mem_univ a) ha
      · rw [Matrix.one_apply_ne hab]
        refine Finset.sum_eq_zero fun j _ => ?_
        by_cases hja : a = j
        · subst hja; simp [Ne.symm hab]
        · simp [Pi.single_apply, hja]
    have hFrobSum : (∑ α : Fin m, frobNormSq (R * Ks α)) = 0 := by
      have htot :
          (∑ j : Fin d, ∑ α : Fin m,
            ((Rᴴ * R) * (Ks α * rankOneProj (Pi.single j (1 : ℂ)) * (Ks α)ᴴ)).trace).re = 0 := by
        rw [Complex.re_sum]
        refine Finset.sum_eq_zero fun j _ => hZero (Pi.single j (1 : ℂ))
      have hrw :
          (∑ j : Fin d, ∑ α : Fin m,
            ((Rᴴ * R) * (Ks α * rankOneProj (Pi.single j (1 : ℂ)) * (Ks α)ᴴ)).trace) =
          ∑ α : Fin m, ((R * Ks α)ᴴ * (R * Ks α)).trace := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun α _ => ?_
        simp_rw [hcyc α]
        rw [← Matrix.trace_sum, ← Finset.mul_sum, hSumBasis, mul_one]
      rw [hrw, Complex.re_sum] at htot
      simp_rw [trace_conjTranspose_mul_self_re] at htot
      exact htot
    have hEach : ∀ α : Fin m, R * Ks α = 0 := by
      intro α
      have h0 : frobNormSq (R * Ks α) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun β _ => frobNormSq_nonneg (R * Ks β))).mp
          hFrobSum α (Finset.mem_univ α)
      exact (frobNormSq_eq_zero_iff (R * Ks α)).mp h0
    refine Finset.sum_eq_zero fun α _ => ?_
    have hfac : (Ks α)ᴴ * (Rᴴ * R) * Ks α = (R * Ks α)ᴴ * (R * Ks α) := by
      simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [hfac, hEach α, Matrix.mul_zero]
  · intro hA v
    have hsum :
        (∑ α : Fin m, ((Rᴴ * R) * (Ks α * rankOneProj v * (Ks α)ᴴ)).trace) =
        ((∑ α : Fin m, (Ks α)ᴴ * (Rᴴ * R) * Ks α) * rankOneProj v).trace := by
      rw [Finset.sum_mul, Matrix.trace_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [hcyc α]
      simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [hsum, hA, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re]

/-- Minimal finite-dimensional two-path causal diamond (`O → M₁ → C` vs. `O → M₂ → C`) on
    `ℂ²_rec ⊗ ℂ²_env`: two unitary record-transfer paths `U₁ = 1 ⊗ 1` and `U₂ = 1 ⊗ X` agree
    identically on the Heisenberg pullback of every diagonal record observable `R ⊗ 1`, while
    differing on off-record environmental observables `1 ⊗ Z`. -/
theorem two_path_diamond_record_subalgebra_agreement :
    let I2 : Matrix (Fin 2) (Fin 2) ℂ := 1
    let X2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
    let Z2 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
    let U1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := Matrix.kroneckerMap (· * ·) I2 I2
    let U2 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := Matrix.kroneckerMap (· * ·) I2 X2
    let recObs := fun (r0 r1 : ℂ) =>
      Matrix.kroneckerMap (· * ·) (!![r0, 0; 0, r1] : Matrix (Fin 2) (Fin 2) ℂ) I2
    let envObs : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := Matrix.kroneckerMap (· * ·) I2 Z2
    U1ᴴ * U1 = 1 ∧
    U2ᴴ * U2 = 1 ∧
    (∀ r0 r1 : ℂ, U1ᴴ * recObs r0 r1 * U1 = recObs r0 r1 ∧
      U2ᴴ * recObs r0 r1 * U2 = recObs r0 r1) ∧
    U1ᴴ * envObs * U1 ≠ U2ᴴ * envObs * U2 := by
  intro I2 X2 Z2 U1 U2 recObs envObs
  have hXH : X2ᴴ = X2 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [X2]
  have hXX : X2 * X2 = I2 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [X2, I2, Matrix.mul_apply, Fin.sum_univ_two]
  have hXZX : X2 * Z2 * X2 = !![-1, 0; 0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [X2, Z2, Matrix.mul_apply, Fin.sum_univ_two]
  have hU1H : U1ᴴ = U1 := by
    ext ⟨a, b⟩ ⟨c, d⟩; simp [U1, I2, Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]
  have hU2H : U2ᴴ = U2 := by
    ext ⟨a, b⟩ ⟨c, d⟩
    simp only [U2, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply]
    have h1 : star (I2 c a) = I2 a c := by
      simp [I2, Matrix.one_apply, eq_comm]
    have h2 : star (X2 d b) = X2 b d := by
      have := congr_fun (congr_fun hXH b) d
      simpa [Matrix.conjTranspose_apply] using this
    rw [star_mul', h1, h2, mul_comm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hU1H]; simp only [U1, I2]; rw [← Matrix.mul_kronecker_mul]; simp
  · rw [hU2H]; simp only [U2]
    rw [← Matrix.mul_kronecker_mul, hXX]
    simp [I2]
  · intro r0 r1
    constructor
    · rw [hU1H]; simp only [U1, recObs, I2]
      rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]; simp
    · have hXI : X2 * I2 * X2 = I2 := by
        simp only [I2, mul_one]; exact hXX
      rw [hU2H]; simp only [U2, recObs]
      rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
      simp only [I2, one_mul, mul_one]
      exact congr_arg (Matrix.kroneckerMap (· * ·) !![r0, 0; 0, r1]) (by simpa [I2] using hXI)
  · intro hEq
    have hL : U1ᴴ * envObs * U1 = envObs := by
      rw [hU1H]; simp only [U1, envObs, I2]
      rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]; simp
    have hR : U2ᴴ * envObs * U2 = Matrix.kroneckerMap (· * ·) I2 !![-1, 0; 0, 1] := by
      rw [hU2H]; simp only [U2, envObs]
      rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, mul_one, one_mul, hXZX]
    rw [hL, hR] at hEq
    have h00 := congr_fun (congr_fun hEq (0, 0)) (0, 0)
    simp [envObs, I2, Z2, Matrix.kroneckerMap_apply] at h00
    norm_num at h00

/-- Premeasurement isometry `J |ψ⟩_S = U_CNOT (|ψ⟩_S |0⟩_F)` into the 4D Wigner's friend space
    (Theorem 2(b.2)): defining the effective Kraus operators `L_a = (P_a ⊗ 1_F) J = |a,a⟩⟨a|`
    from the 2D logical input space `H_S` to `H_S ⊗ H_F`, we have:
    (1) `Jᴴ J = 1_S`, (2) `L_0ᴴ L_0 + L_1ᴴ L_1 = 1_S`,
    (3) exact Eq. (10) Kraus orthogonality `L_0ᴴ (1_S ⊗ P_1) L_0 = 0` and
        `L_1ᴴ (1_S ⊗ P_0) L_1 = 0`,
    (4) restriction to `ran J` obeys `Jᴴ (P_01 + P_10) J = 0`,
    (5) all-logical-input sequential record disagreement vanishes identically for every
        2×2 matrix `ρ`, whereas
    (6) on the unrestricted 4D space, the off-code state `|01⟩⟨01|` yields disagreement `1`. -/
theorem wigner_friend_premeasurement_kraus_orthogonality :
    let J : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ :=
      Matrix.of fun sf a => if sf.1 = a ∧ sf.2 = a then 1 else 0
    let L0 : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ :=
      Matrix.of fun sf a => if sf.1 = 0 ∧ sf.2 = 0 ∧ a = 0 then 1 else 0
    let L1 : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ :=
      Matrix.of fun sf a => if sf.1 = 1 ∧ sf.2 = 1 ∧ a = 1 then 1 else 0
    let F0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      Matrix.of fun sf sf' => if sf = sf' ∧ sf.2 = 0 then 1 else 0
    let F1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      Matrix.of fun sf sf' => if sf = sf' ∧ sf.2 = 1 then 1 else 0
    let P01 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      Matrix.of fun sf sf' => if sf = (0, 1) ∧ sf' = (0, 1) then 1 else 0
    let P10 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      Matrix.of fun sf sf' => if sf = (1, 0) ∧ sf' = (1, 0) then 1 else 0
    Jᴴ * J = 1 ∧
    L0ᴴ * L0 + L1ᴴ * L1 = 1 ∧
    L0ᴴ * F1 * L0 = 0 ∧
    L1ᴴ * F0 * L1 = 0 ∧
    Jᴴ * (P01 + P10) * J = 0 ∧
    (∀ ρ : Matrix (Fin 2) (Fin 2) ℂ,
      (F1 * (L0 * ρ * L0ᴴ)).trace + (F0 * (L1 * ρ * L1ᴴ)).trace = 0) ∧
    ((P01 + P10) * P01).trace = 1 := by
  intro J L0 L1 F0 F1 P01 P10
  have h1 : Jᴴ * J = 1 := by
    ext a b
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    fin_cases a <;> fin_cases b <;>
      simp [J, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  have h2 : L0ᴴ * L0 + L1ᴴ * L1 = 1 := by
    ext a b
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      Fintype.sum_prod_type]
    fin_cases a <;> fin_cases b <;>
      simp [L0, L1, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  have h3 : L0ᴴ * F1 * L0 = 0 := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
    fin_cases a <;> fin_cases b <;>
      simp [L0, F1, Fin.sum_univ_two]
  have h4 : L1ᴴ * F0 * L1 = 0 := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
    fin_cases a <;> fin_cases b <;>
      simp [L1, F0, Fin.sum_univ_two]
  have h5 : Jᴴ * (P01 + P10) * J = 0 := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type]
    fin_cases a <;> fin_cases b <;>
      simp [J, P01, P10, Fin.sum_univ_two]
  have h6 : ∀ ρ : Matrix (Fin 2) (Fin 2) ℂ,
      (F1 * (L0 * ρ * L0ᴴ)).trace + (F0 * (L1 * ρ * L1ᴴ)).trace = 0 := by
    intro ρ
    have ht1 : (F1 * (L0 * ρ * L0ᴴ)).trace = ((L0ᴴ * F1 * L0) * ρ).trace := by
      calc (F1 * (L0 * ρ * L0ᴴ)).trace
          = ((F1 * L0 * ρ) * L0ᴴ).trace := by simp only [Matrix.mul_assoc]
        _ = (L0ᴴ * (F1 * L0 * ρ)).trace := Matrix.trace_mul_comm _ _
        _ = ((L0ᴴ * F1 * L0) * ρ).trace := by simp only [Matrix.mul_assoc]
    have ht2 : (F0 * (L1 * ρ * L1ᴴ)).trace = ((L1ᴴ * F0 * L1) * ρ).trace := by
      calc (F0 * (L1 * ρ * L1ᴴ)).trace
          = ((F0 * L1 * ρ) * L1ᴴ).trace := by simp only [Matrix.mul_assoc]
        _ = (L1ᴴ * (F0 * L1 * ρ)).trace := Matrix.trace_mul_comm _ _
        _ = ((L1ᴴ * F0 * L1) * ρ).trace := by simp only [Matrix.mul_assoc]
    rw [ht1, ht2, h3, h4]
    simp
  have h7 : ((P01 + P10) * P01).trace = 1 := by
    rw [Matrix.trace, Fintype.sum_prod_type]
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.add_apply, Fintype.sum_prod_type]
    simp [P01, P10, Fin.sum_univ_two]
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

end OSTQD_Layer2
