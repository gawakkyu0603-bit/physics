import OSTQD_Layer2.Basic

/-!
# OSTQD_Layer2.Theorem4_NonIsometricPullback

Formalizes Theorem 4 of `paper3_layer2_type2`:
1. Exact POVM pullback sum identity `∑_x Vᴴ E_{B,x} V = Vᴴ V` and cyclic Born-weight identity.
2. Kernel-state total probability annihilation (`V v = 0 ⟹ Tr(E_B V |v⟩⟨v| Vᴴ) = 0` and `Δ_norm = 1`).
3. Sharp polar singular-value perturbation bound `|σ - 1| ≤ ε / (1 + √(1 - ε))` for `|σ² - 1| ≤ ε < 1`.
4. Exact renormalized total-variation Born-weight defect inequality
   `∑_x |p_{B,x}/Z - p_{A,x}| ≤ |1 - Z| + ∑_x |p_{B,x} - p_{A,x}|`.
-/

open scoped Matrix BigOperators ComplexConjugate

namespace OSTQD_Layer2

variable {dE dF k : ℕ}

/-- Pulled-back effective operator `Ẽ_{A,x} = Vᴴ E_{B,x} V`. -/
def pullbackEffect (V : Matrix (Fin dF) (Fin dE) ℂ)
    (E : Matrix (Fin dF) (Fin dF) ℂ) : Matrix (Fin dE) (Fin dE) ℂ :=
  Vᴴ * E * V

/-- Exact pullback sum identity: `∑_x Vᴴ E_{B,x} V = Vᴴ V` for any complete fundamental POVM. -/
theorem pullback_povm_sum
    (V : Matrix (Fin dF) (Fin dE) ℂ)
    (Es : Fin k → Matrix (Fin dF) (Fin dF) ℂ)
    (hSum : (∑ x : Fin k, Es x) = 1) :
    (∑ x : Fin k, pullbackEffect V (Es x)) = Vᴴ * V := by
  unfold pullbackEffect
  ext i j
  rw [Matrix.sum_apply]
  have h1 : ∀ x : Fin k, (Vᴴ * Es x * V) i j =
      ∑ a : Fin dF, ∑ b : Fin dF, (Vᴴ i a * Es x a b) * V b j := by
    intro x
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ a : Fin dF,
      (∑ x : Fin k, ∑ b : Fin dF, (Vᴴ i a * Es x a b) * V b j) =
      ∑ b : Fin dF, (Vᴴ i a * (∑ x : Fin k, Es x a b)) * V b j := by
    intro a
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  simp_rw [h2]
  have h3 : ∀ a b : Fin dF, (∑ x : Fin k, Es x a b) = (1 : Matrix (Fin dF) (Fin dF) ℂ) a b := by
    intro a b
    rw [← Matrix.sum_apply, hSum]
  simp_rw [h3]
  simp [Matrix.mul_apply, Matrix.one_apply]

/-- Cyclic Born-weight pullback identity: `Tr(E_B (V ρ Vᴴ)) = Tr((Vᴴ E_B V) ρ)`. -/
theorem pullback_born_cyclic_identity
    (V : Matrix (Fin dF) (Fin dE) ℂ)
    (E : Matrix (Fin dF) (Fin dF) ℂ)
    (ρ : Matrix (Fin dE) (Fin dE) ℂ) :
    (E * (V * ρ * Vᴴ)).trace = (pullbackEffect V E * ρ).trace := by
  unfold pullbackEffect
  calc (E * (V * ρ * Vᴴ)).trace
      = ((E * V * ρ) * Vᴴ).trace := by simp [Matrix.mul_assoc]
    _ = (Vᴴ * (E * V * ρ)).trace := Matrix.trace_mul_comm _ _
    _ = (Vᴴ * E * V * ρ).trace := by simp [Matrix.mul_assoc]

/-- Pure-state matrix `|v⟩⟨v|` for a vector `v : Fin dE → ℂ`. -/
def rankOneState (v : Fin dE → ℂ) : Matrix (Fin dE) (Fin dE) ℂ :=
  Matrix.vecMulVec v (star v)

/-- Kernel annihilation: if `V v = 0`, then `V |v⟩⟨v| Vᴴ = 0`, every fundamental Born weight vanishes,
    and total normalization loss is identically `1`. -/
theorem kernel_vector_total_annihilation
    (V : Matrix (Fin dF) (Fin dE) ℂ) (v : Fin dE → ℂ)
    (hKer : V.mulVec v = 0)
    (E : Matrix (Fin dF) (Fin dF) ℂ) :
    V * rankOneState v * Vᴴ = 0 ∧
    (E * (V * rankOneState v * Vᴴ)).trace = 0 ∧
    (1 : ℂ) - ((Vᴴ * V) * rankOneState v).trace = 1 := by
  have hzero : V * rankOneState v * Vᴴ = 0 := by
    ext i j
    have hVi : (V.mulVec v) i = 0 := congr_fun hKer i
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    have hmul : (V * rankOneState v) i l = (V.mulVec v) i * star (v l) := by
      rw [Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.sum_mul]
      refine Finset.sum_congr rfl fun r _ => ?_
      simp [rankOneState, Matrix.vecMulVec_apply, mul_assoc]
    rw [hmul, hVi, zero_mul, zero_mul]
  refine ⟨hzero, ?_, ?_⟩
  · rw [hzero, Matrix.mul_zero, Matrix.trace_zero]
  · have htr : ((Vᴴ * V) * rankOneState v).trace = (V * rankOneState v * Vᴴ).trace := by
      calc ((Vᴴ * V) * rankOneState v).trace
          = (Vᴴ * (V * rankOneState v)).trace := by simp [Matrix.mul_assoc]
        _ = ((V * rankOneState v) * Vᴴ).trace := Matrix.trace_mul_comm _ _
    rw [htr, hzero, Matrix.trace_zero, sub_zero]

/-- Sharp polar singular-value perturbation bound:
    if `σ ≥ 0`, `ε < 1`, and `|σ² - 1| ≤ ε`, then `|σ - 1| ≤ ε / (1 + √(1 - ε))`. -/
theorem polar_singular_value_bound
    (σ ε : ℝ) (hσ : 0 ≤ σ) (hε1 : ε < 1)
    (hApprox : |σ ^ 2 - 1| ≤ ε) :
    |σ - 1| ≤ ε / (1 + Real.sqrt (1 - ε)) := by
  have h1m : 0 ≤ 1 - ε := by linarith
  have hσ2_ge : 1 - ε ≤ σ ^ 2 := by
    have := (abs_le.mp hApprox).1
    linarith
  have hσ_ge : Real.sqrt (1 - ε) ≤ σ := by
    rw [← Real.sqrt_sq hσ]
    exact Real.sqrt_le_sqrt hσ2_ge
  have hden_pos : 0 < 1 + Real.sqrt (1 - ε) := by
    have := Real.sqrt_nonneg (1 - ε)
    linarith
  have hσp1_ge : 1 + Real.sqrt (1 - ε) ≤ σ + 1 := by linarith
  have hσp1_pos : 0 < σ + 1 := by linarith
  rw [le_div_iff₀ hden_pos]
  have hfact : |σ - 1| * (σ + 1) = |σ ^ 2 - 1| := by
    have hpos_abs : |σ + 1| = σ + 1 := abs_of_pos hσp1_pos
    calc |σ - 1| * (σ + 1)
        = |σ - 1| * |σ + 1| := by rw [hpos_abs]
      _ = |(σ - 1) * (σ + 1)| := by rw [← abs_mul]
      _ = |σ ^ 2 - 1| := by ring_nf
  calc |σ - 1| * (1 + Real.sqrt (1 - ε))
      ≤ |σ - 1| * (σ + 1) := mul_le_mul_of_nonneg_left hσp1_ge (abs_nonneg _)
    _ = |σ ^ 2 - 1| := hfact
    _ ≤ ε := hApprox

/-- Exact renormalized total-variation Born-weight defect inequality:
    for any non-negative unnormalized weights `pB ≥ 0` with `Z = ∑ pB > 0` and reference
    weights `pA`, `∑ |pB x / Z - pA x| ≤ |1 - Z| + ∑ |pB x - pA x|`. -/
theorem renormalized_tv_defect_bound
    (pB pA : Fin k → ℝ)
    (hNonneg : ∀ x, 0 ≤ pB x)
    (hZpos : 0 < ∑ x : Fin k, pB x) :
    let Z := ∑ x : Fin k, pB x
    (∑ x : Fin k, |pB x / Z - pA x|) ≤ |1 - Z| + ∑ x : Fin k, |pB x - pA x| := by
  intro Z
  have htri : ∀ x : Fin k,
      |pB x / Z - pA x| ≤ |pB x / Z - pB x| + |pB x - pA x| := by
    intro x
    have hsplit : pB x / Z - pA x = (pB x / Z - pB x) + (pB x - pA x) := by ring
    rw [hsplit]
    exact abs_add_le _ _
  have hsum_le :
      (∑ x : Fin k, |pB x / Z - pA x|) ≤
        (∑ x : Fin k, |pB x / Z - pB x|) + (∑ x : Fin k, |pB x - pA x|) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun x _ => htri x
  have hZne : Z ≠ 0 := ne_of_gt hZpos
  have hfirst : (∑ x : Fin k, |pB x / Z - pB x|) = |1 - Z| := by
    have hterm : ∀ x : Fin k, |pB x / Z - pB x| = pB x * (|1 - Z| / Z) := by
      intro x
      have hrewrite : pB x / Z - pB x = pB x * ((1 - Z) / Z) := by
        field_simp [hZne]
      rw [hrewrite, abs_mul, abs_of_nonneg (hNonneg x), abs_div, abs_of_pos hZpos]
    simp_rw [hterm]
    rw [← Finset.sum_mul]
    have hZeq : (∑ x : Fin k, pB x) = Z := rfl
    rw [hZeq]
    field_simp [hZne]
  linarith

/-- Sharp uniform unnormalized polar pullback bound (C3, Eq. B) and saturation witness:
    for spectral endpoints `a, b` with `a² + b² = 2` (i.e. `a = √(1-ε), b = √(1+ε)`),
    any pure expectation pair `(s, Z)` satisfying `0 ≤ Z ≤ (a + b) s - a b` obeys
    `(Z + 1)² - 4 s² ≤ (b - a)²`, with exact equality at `s = (a + b)/2, Z = (a² + b²)/2`. -/
theorem sharp_polar_unnormalized_pure_bound
    (a b s Z : ℝ) (hsum : a ^ 2 + b ^ 2 = 2)
    (hZnn : 0 ≤ Z) (hZle : Z ≤ (a + b) * s - a * b) :
    (Z + 1) ^ 2 - 4 * s ^ 2 ≤ (b - a) ^ 2 ∧
    (((a ^ 2 + b ^ 2) / 2 + 1) ^ 2 - 4 * ((a + b) / 2) ^ 2 = (b - a) ^ 2) := by
  constructor
  · have hZ1_nn : 0 ≤ Z + 1 := by linarith
    have hZ1_le : Z + 1 ≤ (a + b) * s - a * b + 1 := by linarith
    have hsq : (Z + 1) ^ 2 ≤ ((a + b) * s - a * b + 1) ^ 2 := by nlinarith
    have hid :
        ((a + b) * s - a * b + 1) ^ 2 - 4 * s ^ 2 =
          (b - a) ^ 2 - (b - a) ^ 2 * (s - (a + b) / 2) ^ 2 := by
      nlinarith [hsum]
    have hrem : 0 ≤ (b - a) ^ 2 * (s - (a + b) / 2) ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    linarith
  · nlinarith [hsum]

/-- Sharp uniform normalized polar pullback bound (C3, Eq. C), `ε`-expression, and saturation witness:
    for `0 < a ≤ b`, `0 < Z ≤ (a + b) s - a b`, we have `4 a b / (a + b)² ≤ s² / Z` and
    `4 (1 - s² / Z) ≤ (2 (b - a) / (b + a))²`, saturated at `p_a = b/(a+b), p_b = a/(a+b)`,
    and when `a² = 1 - ε, b² = 1 + ε` (`0 ≤ ε < 1`), `2 (b - a) / (b + a) = 2 ε / (1 + a b)`. -/
theorem sharp_polar_normalized_pure_bound
    (a b s Z ε : ℝ) (ha : 0 < a) (hab : a ≤ b) (hZpos : 0 < Z)
    (hZle : Z ≤ (a + b) * s - a * b) (ha2 : a ^ 2 = 1 - ε) (hb2 : b ^ 2 = 1 + ε) :
    4 * (1 - s ^ 2 / Z) ≤ (2 * (b - a) / (b + a)) ^ 2 ∧
    4 * (1 - (b / (a + b) * a + a / (a + b) * b) ^ 2 /
      (b / (a + b) * a ^ 2 + a / (a + b) * b ^ 2)) = (2 * (b - a) / (b + a)) ^ 2 ∧
    2 * (b - a) / (b + a) = 2 * ε / (1 + a * b) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hab_pos : 0 < a + b := by linarith
  have hba_pos : 0 < b + a := by linarith
  have h1ab_pos : 0 < 1 + a * b := by nlinarith
  have hfid : 4 * a * b / (a + b) ^ 2 ≤ s ^ 2 / Z := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hab_pos) hZpos]
    have hquad : 4 * a * b * ((a + b) * s - a * b) ≤ s ^ 2 * (a + b) ^ 2 := by
      have hsq : 0 ≤ ((a + b) * s - 2 * a * b) ^ 2 := sq_nonneg _
      nlinarith
    have hmul : 4 * a * b * Z ≤ 4 * a * b * ((a + b) * s - a * b) :=
      mul_le_mul_of_nonneg_left hZle (by positivity)
    linarith
  refine ⟨?_, ?_, ?_⟩
  · have hident : 4 * (1 - 4 * a * b / (a + b) ^ 2) = (2 * (b - a) / (b + a)) ^ 2 := by
      field_simp [ne_of_gt hab_pos, ne_of_gt hba_pos]
      ring
    linarith
  · have hZval : b / (a + b) * a ^ 2 + a / (a + b) * b ^ 2 = a * b := by
      field_simp [ne_of_gt hab_pos]
    rw [hZval]
    field_simp [ne_of_gt hab_pos, ne_of_gt hba_pos, ne_of_gt ha, ne_of_gt hb]
    ring
  · rw [div_eq_div_iff (ne_of_gt hba_pos) (ne_of_gt h1ab_pos)]
    have hsum2 : b ^ 2 + a ^ 2 = 2 := by linarith
    have hdiff2 : b ^ 2 - a ^ 2 = 2 * ε := by linarith
    nlinarith [hsum2, hdiff2]

/-- Partial trace over the left factor `α` of a matrix on `α × β`. -/
def partialTraceLeft {α β : Type*} [Fintype α]
    (M : Matrix (α × β) (α × β) ℂ) : Matrix β β ℂ :=
  Matrix.of fun r r' => ∑ b : α, M (b, r) (b, r')

/-- Strictly causal sequential evaporation radiation compatibility (R4, Eq. A):
    for ANY isometric black-hole step `U : B_{n-1} → B_n ⊗ R_new` (`Uᴴ U = 1`) acting as identity
    on previously emitted radiation `R_{n-1}`, tracing out `(B_n, R_new)` reproduces the prior
    radiation marginal `Tr_{B_{n-1}}(ρ)` identically for EVERY input state `ρ`. -/
theorem sequential_evaporation_radiation_compatibility
    {αPrev αNext γ β : Type*} [Fintype αPrev] [Fintype αNext] [Fintype γ] [Fintype β]
    [DecidableEq αPrev] [DecidableEq β]
    (U : Matrix (αNext × γ) αPrev ℂ)
    (hIso : Uᴴ * U = 1)
    (ρ : Matrix (αPrev × β) (αPrev × β) ℂ) :
    let Uext : Matrix ((αNext × γ) × β) (αPrev × β) ℂ :=
      Matrix.kroneckerMap (· * ·) U (1 : Matrix β β ℂ)
    partialTraceLeft (Uext * ρ * Uextᴴ) = partialTraceLeft ρ := by
  intro Uext
  ext r r'
  rw [partialTraceLeft, partialTraceLeft, Matrix.of_apply, Matrix.of_apply]
  have hentry : ∀ p : αNext × γ,
      (Uext * ρ * Uextᴴ) (p, r) (p, r') =
        ∑ b1 : αPrev, ∑ b2 : αPrev, U p b1 * ρ (b1, r) (b2, r') * star (U p b2) := by
    intro p
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    have houter : ∀ b2 : αPrev,
        (∑ s2 : β, (Uext * ρ) (p, r) (b2, s2) * Uextᴴ (b2, s2) (p, r')) =
          (Uext * ρ) (p, r) (b2, r') * star (U p b2) := by
      intro b2
      rw [Finset.sum_eq_single r']
      · simp [Uext, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply]
      · intro s2 _ hs2
        have h1 : (1 : Matrix β β ℂ) r' s2 = 0 := Matrix.one_apply_ne (Ne.symm hs2)
        simp [Uext, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, h1]
      · intro hr'
        exact absurd (Finset.mem_univ r') hr'
    simp_rw [houter]
    have hinner : ∀ b2 : αPrev,
        (Uext * ρ) (p, r) (b2, r') = ∑ b1 : αPrev, U p b1 * ρ (b1, r) (b2, r') := by
      intro b2
      rw [Matrix.mul_apply, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun b1 _ => ?_
      rw [Finset.sum_eq_single r]
      · simp [Uext, Matrix.kroneckerMap_apply]
      · intro s1 _ hs1
        simp [Uext, Matrix.kroneckerMap_apply, Matrix.one_apply_ne (Ne.symm hs1)]
      · intro hr
        exact absurd (Finset.mem_univ r) hr
    simp_rw [hinner, Finset.sum_mul]
    rw [Finset.sum_comm]
  simp_rw [hentry]
  rw [Finset.sum_comm]
  have hswap : ∀ b1 : αPrev,
      (∑ p : αNext × γ, ∑ b2 : αPrev, U p b1 * ρ (b1, r) (b2, r') * star (U p b2)) =
        ∑ b2 : αPrev, ((Uᴴ * U) b2 b1) * ρ (b1, r) (b2, r') := by
    intro b1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b2 _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [Matrix.conjTranspose_apply]
    ring
  simp_rw [hswap]
  refine Finset.sum_congr rfl fun b1 _ => ?_
  rw [hIso]
  rw [Finset.sum_eq_single b1]
  · simp
  · intro b2 _ hb2
    simp [Matrix.one_apply_ne hb2]
  · intro hb1
    exact absurd (Finset.mem_univ b1) hb1

/-- Non-isometric kernel activation alone does NOT force sequential radiation incompatibility:
    for `N_{BH,0} = 2, d_C = 2`, the two scaled co-isometric dictionaries
    `V₁ = √2 (|0⟩⟨0,0| + |1⟩⟨1,0|) : ℂ²⊗ℂ² → ℂ²` and
    `V₂ = 2 (⟨0,(0,0)| + ⟨1,(0,1)|) : ℂ²⊗(ℂ²⊗ℂ²) → ℂ¹`
    both carry nontrivial kernels, yet their Bell-entangled code restrictions
    `Ṽ₁ = (V₁ ⊗ 1_{R₁}) ∘ ι₁` and `Ṽ₂ = (V₂ ⊗ 1_{R₂}) ∘ ι₂` are exact isometries whose
    emitted radiation states obey exact sequential compatibility `Tr_{R_new}(ρ_{R₂}) = ρ_{R₁}`
    for EVERY `2×2` input matrix `ρ`. -/
theorem nonisometric_kernel_compatible_two_step_witness :
    let s2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)
    let V1 : Matrix (Fin 2) (Fin 2 × Fin 2) ℂ :=
      Matrix.of fun b cl => if b = cl.1 ∧ cl.2 = 0 then s2 else 0
    let V2 : Matrix (Fin 1) (Fin 2 × (Fin 2 × Fin 2)) ℂ :=
      Matrix.of fun _ cl =>
        if (cl.1 = 0 ∧ cl.2.1 = 0 ∧ cl.2.2 = 0) ∨ (cl.1 = 1 ∧ cl.2.1 = 0 ∧ cl.2.2 = 1)
        then 2 else 0
    let Vtilde1 : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ :=
      Matrix.of fun br c => V1 br.1 (c, br.2) / s2
    let Vtilde2 : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ :=
      Matrix.of fun rr c => V2 0 (c, rr) / 2
    V1 * V1ᴴ = (2 : ℂ) • 1 ∧
    (∃ v1 : Fin 2 × Fin 2 → ℂ, v1 ≠ 0 ∧ V1.mulVec v1 = 0) ∧
    V2 * V2ᴴ = (8 : ℂ) • 1 ∧
    (∃ v2 : Fin 2 × (Fin 2 × Fin 2) → ℂ, v2 ≠ 0 ∧ V2.mulVec v2 = 0) ∧
    Vtilde1ᴴ * Vtilde1 = 1 ∧
    Vtilde2ᴴ * Vtilde2 = 1 ∧
    (∀ ρ : Matrix (Fin 2) (Fin 2) ℂ,
      Matrix.of (fun r1 r1' : Fin 2 =>
        ∑ rnew : Fin 2, (Vtilde2 * ρ * Vtilde2ᴴ) (r1, rnew) (r1', rnew)) =
      partialTraceLeft (Vtilde1 * ρ * Vtilde1ᴴ)) := by
  intro s2 V1 V2 Vtilde1 Vtilde2
  have hs2_ne : s2 ≠ 0 := by
    simp only [s2, ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hs2_mul : s2 * (starRingEnd ℂ) s2 = 2 := by
    simp only [s2, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hVt1 : ∀ br c, Vtilde1 br c = if br.1 = c ∧ br.2 = 0 then 1 else 0 := by
    intro ⟨b, r⟩ c
    simp only [Vtilde1, V1, Matrix.of_apply]
    split_ifs <;> simp [div_self hs2_ne]
  have hVt2 : ∀ rr c, Vtilde2 rr c = if rr.1 = 0 ∧ rr.2 = c then 1 else 0 := by
    intro ⟨r1, r2⟩ c
    simp only [Vtilde2, V2, Matrix.of_apply]
    fin_cases r1 <;> fin_cases r2 <;> fin_cases c <;> norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext b b'
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    fin_cases b <;> fin_cases b' <;>
      simp [V1, Matrix.conjTranspose_apply, Fin.sum_univ_two]
    · exact hs2_mul
    · exact hs2_mul
  · refine ⟨fun cl => if cl = (0, 1) then 1 else 0, ?_, ?_⟩
    · intro h
      have h01 := congr_fun h (0, 1)
      simp at h01
    · ext b
      rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
      fin_cases b <;> simp [V1, Fin.sum_univ_two]
  · ext a a'
    fin_cases a; fin_cases a'
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    simp [V2, Matrix.conjTranspose_apply, Fin.sum_univ_two]
    rw [map_ofNat]
    norm_num
  · refine ⟨fun cl => if cl = (0, (1, 0)) then 1 else 0, ?_, ?_⟩
    · intro h
      have h0 := congr_fun h (0, (1, 0))
      simp at h0
    · ext a
      fin_cases a
      rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      simp [V2, Fin.sum_univ_two]
  · ext c c'
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    simp_rw [Matrix.conjTranspose_apply, hVt1]
    fin_cases c <;> fin_cases c' <;> simp [Fin.sum_univ_two]
  · ext c c'
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    simp_rw [Matrix.conjTranspose_apply, hVt2]
    fin_cases c <;> fin_cases c' <;> simp [Fin.sum_univ_two]
  · intro ρ
    ext r1 r1'
    rw [partialTraceLeft, Matrix.of_apply, Matrix.of_apply]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hVt1, hVt2]
    fin_cases r1 <;> fin_cases r1' <;>
      simp [Fin.sum_univ_two]

/-- Postselection normalization vs. ensemble linearity (Theorem 4(b) & Proposition 1):
    for `M = diag(a, b)` with `a² = 1 - ε`, `b² = 1 + ε` (`0 < ε < 1`), applying the
    individually normalized filter `ρ ↦ M ρ M / Tr(M² ρ)` branch-by-branch to `Z`- vs.
    `X`-decompositions of `I₂/2` with equal weights `(1/2, 1/2)` produces an ensemble gap
    of `ε` in `⟨Z⟩` (trace distance `ε / 2`), whereas success-probability reweighting
    (equivalently linear unnormalized `M ρ M` / contractive Kraus `K = M / ‖M‖_op`)
    yields identical averages on both decompositions. -/
theorem postselected_normalized_gisin_bias_witness
    (a b ε : ℝ) (ha : 0 < a) (hb : 0 < b)
    (ha2 : a ^ 2 = 1 - ε) (hb2 : b ^ 2 = 1 + ε) :
    let M : Matrix (Fin 2) (Fin 2) ℝ := !![a, 0; 0, b]
    let Z : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
    let P0 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
    let P1 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 1]
    let Pp : Matrix (Fin 2) (Fin 2) ℝ := !![1/2, 1/2; 1/2, 1/2]
    let Pm : Matrix (Fin 2) (Fin 2) ℝ := !![1/2, -1/2; -1/2, 1/2]
    let normMap := fun (ρ : Matrix (Fin 2) (Fin 2) ℝ) =>
      ((M * ρ * M).trace)⁻¹ • (M * ρ * M)
    let avgZ_unrw := (1/2 : ℝ) • normMap P0 + (1/2 : ℝ) • normMap P1
    let avgX_unrw := (1/2 : ℝ) • normMap Pp + (1/2 : ℝ) • normMap Pm
    let avgZ_lin := (1/2 : ℝ) • (M * P0 * M) + (1/2 : ℝ) • (M * P1 * M)
    let avgX_lin := (1/2 : ℝ) • (M * Pp * M) + (1/2 : ℝ) • (M * Pm * M)
    (Z * (avgZ_unrw - avgX_unrw)).trace = ε ∧
    avgZ_lin = avgX_lin := by
  intro M Z P0 P1 Pp Pm normMap avgZ_unrw avgX_unrw avgZ_lin avgX_lin
  have ha2_ne : a ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos ha)
  have hb2_ne : b ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hb)
  have htr0 : (M * P0 * M).trace = a ^ 2 := by
    simp [M, P0, Matrix.trace, Fin.sum_univ_two]; ring
  have htr1 : (M * P1 * M).trace = b ^ 2 := by
    simp [M, P1, Matrix.trace, Fin.sum_univ_two]; ring
  have htrp : (M * Pp * M).trace = 1 := by
    simp only [M, Pp, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    nlinarith [ha2, hb2]
  have htrm : (M * Pm * M).trace = 1 := by
    simp only [M, Pm, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    nlinarith [ha2, hb2]
  have hAvgZ : avgZ_unrw = !![1/2, 0; 0, 1/2] := by
    ext i j
    simp only [avgZ_unrw, normMap, htr0, htr1]
    fin_cases i <;> fin_cases j <;> simp [M, P0, P1]
    · field_simp [ha2_ne]
    · field_simp [hb2_ne]
  have hAvgX : avgX_unrw = !![a ^ 2 / 2, 0; 0, b ^ 2 / 2] := by
    ext i j
    simp only [avgX_unrw, normMap, htrp, htrm, inv_one, one_smul]
    fin_cases i <;> fin_cases j <;> simp [M, Pp, Pm] <;> ring
  constructor
  · rw [hAvgZ, hAvgX]
    simp [Z, Matrix.trace, Fin.sum_univ_two]
    linarith [ha2, hb2]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [avgZ_lin, avgX_lin, M, P0, P1, Pp, Pm] <;> ring

end OSTQD_Layer2
