import OSTQD_Layer2.Basic

/-!
# OSTQD_Layer2.Theorem1_SteeringNoGo

Formalizes Theorem 1 of `paper3_layer2_type2`:
1. Exact Schmidt assemblage identity `Tr_R((E ⊗ I)|ψ⟩⟨ψ|) = D(√λ) Eᵀ D(√λ)` and non-selective no-signaling.
2. Zero-steering triviality equivalence `σ_{L,x} = p_x ρ_L ↔ E_x = p_x I` on full-Schmidt-rank pure states.
3. Quantitative Frobenius steering floor `λ_min² ‖E_x - p_x I‖_F² ≤ ‖σ_{L,x} - p_x ρ_L‖_F²`.
4. Negative controls: product states and classically correlated mixed states under X-basis measurements.
5. Exact rational Pythagorean CHSH/Local-Friendliness witness (`S = 14/5 > 2`) with Farkas impossibility
   over `Bool⁴` and Frauchiger–Renner `1/12` contradiction witness.
-/

open scoped Matrix BigOperators ComplexConjugate

namespace OSTQD_Layer2

variable {d k : ℕ}

/-- Partial trace over the first (exterior `R`) tensor factor on `Fin d × Fin d`. -/
def partialTraceR (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => ∑ r : Fin d, ρ (r, i) (r, j)

/-- Pure Schmidt state `|ψ⟩⟨ψ|` for `|ψ⟩ = ∑_i √(λ_i) |i_R, i_L⟩`. -/
noncomputable def schmidtPureState (lam : Fin d → ℝ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.of fun p q =>
    if p.1 = p.2 ∧ q.1 = q.2 then
      ((Real.sqrt (lam p.1) : ℂ) * (Real.sqrt (lam q.1) : ℂ))
    else 0

/-- Diagonal reduced state `ρ_L = diag(λ)` in the Schmidt basis. -/
def schmidtRhoL (lam : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun i => (lam i : ℂ))

/-- Square root `ρ_L^{1/2} = diag(√λ)` in the Schmidt basis. -/
noncomputable def schmidtSqrtRhoL (lam : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun i => (Real.sqrt (lam i) : ℂ))

/-- Conditional assemblage `σ_{L,x} = ρ_L^{1/2} E_xᵀ ρ_L^{1/2}`. -/
noncomputable def schmidtAssemblage (lam : Fin d → ℝ)
    (E : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  schmidtSqrtRhoL lam * Eᵀ * schmidtSqrtRhoL lam

/-- Entrywise evaluation of `schmidtAssemblage`. -/
lemma schmidtAssemblage_apply (lam : Fin d → ℝ) (E : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    schmidtAssemblage lam E i j =
      (Real.sqrt (lam i) : ℂ) * E j i * (Real.sqrt (lam j) : ℂ) := by
  unfold schmidtAssemblage schmidtSqrtRhoL
  simp [Matrix.mul_apply, Matrix.diagonal_apply]

/-- Exact equality between bipartite partial trace `Tr_R((E ⊗ I)|ψ⟩⟨ψ|)` and `ρ_L^{1/2} Eᵀ ρ_L^{1/2}`. -/
theorem partialTraceR_schmidt_eq_assemblage
    (lam : Fin d → ℝ) (E : Matrix (Fin d) (Fin d) ℂ) :
    partialTraceR (Matrix.kroneckerMap (· * ·) E (1 : Matrix (Fin d) (Fin d) ℂ) *
      schmidtPureState lam) = schmidtAssemblage lam E := by
  ext i j
  rw [partialTraceR, Matrix.of_apply, schmidtAssemblage_apply]
  have hsum : ∀ r : Fin d,
      (Matrix.kroneckerMap (· * ·) E (1 : Matrix (Fin d) (Fin d) ℂ) *
        schmidtPureState lam) (r, i) (r, j) =
      if r = j then E r i * ((Real.sqrt (lam i) : ℂ) * (Real.sqrt (lam r) : ℂ)) else 0 := by
    intro r
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    have hinner : ∀ a : Fin d,
        (∑ b : Fin d,
          Matrix.kroneckerMap (· * ·) E (1 : Matrix (Fin d) (Fin d) ℂ) (r, i) (a, b) *
            schmidtPureState lam (a, b) (r, j)) =
        E r a * (if a = i ∧ r = j then (Real.sqrt (lam a) : ℂ) * (Real.sqrt (lam r) : ℂ) else 0) := by
      intro a
      rw [Finset.sum_eq_single i]
      · simp [Matrix.kroneckerMap_apply, schmidtPureState]
      · intro b _ hbi
        simp [Matrix.kroneckerMap_apply, Ne.symm hbi]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    simp_rw [hinner]
    by_cases hrj : r = j
    · subst hrj
      rw [Finset.sum_eq_single i]
      · simp
      · intro a _ hai
        simp [hai]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    · simp [hrj]
  simp_rw [hsum]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- Non-selective no-signaling: summing `schmidtAssemblage` over any complete POVM recovers `ρ_L`. -/
theorem schmidt_nonselective_no_signaling
    (lam : Fin d → ℝ) (hPos : ∀ i, 0 ≤ lam i)
    (Es : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (hSum : (∑ x : Fin k, Es x) = 1) :
    (∑ x : Fin k, schmidtAssemblage lam (Es x)) = schmidtRhoL lam := by
  ext i j
  rw [Matrix.sum_apply]
  simp_rw [schmidtAssemblage_apply]
  have hfac : (∑ x : Fin k, (Real.sqrt (lam i) : ℂ) * Es x j i * (Real.sqrt (lam j) : ℂ)) =
      (Real.sqrt (lam i) : ℂ) * (∑ x : Fin k, Es x j i) * (Real.sqrt (lam j) : ℂ) := by
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [hfac]
  have h1 : (∑ x : Fin k, Es x j i) = (1 : Matrix (Fin d) (Fin d) ℂ) j i := by
    rw [← Matrix.sum_apply, hSum]
  rw [h1]
  unfold schmidtRhoL
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.one_apply_eq, Matrix.diagonal_apply_eq, mul_one]
    have hsq : (Real.sqrt (lam i) : ℂ) * (Real.sqrt (lam i) : ℂ) = (lam i : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hPos i)]
    exact hsq
  · simp [Matrix.one_apply_ne (Ne.symm hij), Matrix.diagonal_apply_ne _ hij]

/-- Zero-steering triviality equivalence on any full-Schmidt-rank pure state (`∀ i, 0 < λ_i`). -/
theorem zero_steering_iff_trivial_effect
    (lam : Fin d → ℝ) (hPos : ∀ i, 0 < lam i)
    (E : Matrix (Fin d) (Fin d) ℂ) (p : ℝ) :
    schmidtAssemblage lam E = (p : ℂ) • schmidtRhoL lam ↔ E = (p : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  constructor
  · intro h
    ext j i
    have hij := congr_fun (congr_fun h i) j
    rw [schmidtAssemblage_apply] at hij
    simp only [Matrix.smul_apply, smul_eq_mul, schmidtRhoL] at hij
    have hsi : (Real.sqrt (lam i) : ℂ) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (hPos i)))
    have hsj : (Real.sqrt (lam j) : ℂ) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (hPos j)))
    by_cases hji : j = i
    · subst hji
      simp only [Matrix.diagonal_apply_eq] at hij
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq, mul_one]
      have hsq : (Real.sqrt (lam j) : ℂ) * (Real.sqrt (lam j) : ℂ) = (lam j : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt (hPos j))]
      have hmul : E j j * ((Real.sqrt (lam j) : ℂ) * (Real.sqrt (lam j) : ℂ)) =
          (p : ℂ) * ((Real.sqrt (lam j) : ℂ) * (Real.sqrt (lam j) : ℂ)) := by
        rw [hsq]
        calc E j j * (lam j : ℂ)
            = (Real.sqrt (lam j) : ℂ) * E j j * (Real.sqrt (lam j) : ℂ) := by
                rw [← hsq]; ring
          _ = (p : ℂ) * (lam j : ℂ) := hij
      exact mul_right_cancel₀ (mul_ne_zero hsj hsj) hmul
    · simp only [Matrix.diagonal_apply_ne _ (Ne.symm hji), mul_zero] at hij
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_ne hji, mul_zero]
      have h1 : (Real.sqrt (lam i) : ℂ) * E j i = 0 :=
        (mul_eq_zero.mp hij).resolve_right hsj
      exact (mul_eq_zero.mp h1).resolve_left hsi
  · intro h
    subst h
    ext i j
    rw [schmidtAssemblage_apply]
    simp only [Matrix.smul_apply, smul_eq_mul, schmidtRhoL]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.one_apply_eq, Matrix.diagonal_apply_eq, mul_one]
      have hsq : (Real.sqrt (lam i) : ℂ) * (Real.sqrt (lam i) : ℂ) = (lam i : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt (hPos i))]
      calc (Real.sqrt (lam i) : ℂ) * (p : ℂ) * (Real.sqrt (lam i) : ℂ)
          = (p : ℂ) * ((Real.sqrt (lam i) : ℂ) * (Real.sqrt (lam i) : ℂ)) := by ring
        _ = (p : ℂ) * (lam i : ℂ) := by rw [hsq]
    · simp [Matrix.one_apply_ne (Ne.symm hij), Matrix.diagonal_apply_ne _ hij]

/-- Quantitative Frobenius steering lower bound: `λ_min² ‖E - p I‖_F² ≤ ‖σ_L - p ρ_L‖_F²`. -/
theorem steering_frobenius_lower_bound
    (lam : Fin d → ℝ) (lamMin : ℝ)
    (hMinNonneg : 0 ≤ lamMin) (hMin : ∀ i, lamMin ≤ lam i)
    (E : Matrix (Fin d) (Fin d) ℂ) (p : ℝ) :
    lamMin ^ 2 * frobNormSq (E - (p : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) ≤
      frobNormSq (schmidtAssemblage lam E - (p : ℂ) • schmidtRhoL lam) := by
  unfold frobNormSq
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have hli : 0 ≤ lam i := le_trans hMinNonneg (hMin i)
  have hlj : 0 ≤ lam j := le_trans hMinNonneg (hMin j)
  have hentry :
      (schmidtAssemblage lam E - (p : ℂ) • schmidtRhoL lam) i j =
        (Real.sqrt (lam i) : ℂ) * (Real.sqrt (lam j) : ℂ) *
          (E - (p : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) j i := by
    simp only [Matrix.sub_apply, schmidtAssemblage_apply, Matrix.smul_apply, smul_eq_mul, schmidtRhoL]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, mul_one]
      have hsq : (Real.sqrt (lam i) : ℂ) * (Real.sqrt (lam i) : ℂ) = (lam i : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt hli]
      calc (Real.sqrt (lam i) : ℂ) * E i i * (Real.sqrt (lam i) : ℂ) - (p : ℂ) * (lam i : ℂ)
          = (Real.sqrt (lam i) : ℂ) * E i i * (Real.sqrt (lam i) : ℂ) -
              (p : ℂ) * ((Real.sqrt (lam i) : ℂ) * (Real.sqrt (lam i) : ℂ)) := by rw [hsq]
        _ = (Real.sqrt (lam i) : ℂ) * (Real.sqrt (lam i) : ℂ) * (E i i - (p : ℂ)) := by ring
    · simp only [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne (Ne.symm hij), mul_zero, sub_zero]
      ring
  rw [hentry, map_mul, map_mul, Complex.normSq_ofReal, Complex.normSq_ofReal,
    Real.mul_self_sqrt hli, Real.mul_self_sqrt hlj]
  have hprod : lamMin ^ 2 ≤ lam i * lam j := by
    rw [sq]
    exact mul_le_mul (hMin i) (hMin j) hMinNonneg hli
  exact mul_le_mul_of_nonneg_right hprod (Complex.normSq_nonneg _)

/-- Negative control 1: on any product state `ρ_R ⊗ ρ_L`, every exterior effect produces zero steering. -/
theorem product_state_zero_steering_control
    (E ρR ρL : Matrix (Fin d) (Fin d) ℂ) :
    partialTraceR (Matrix.kroneckerMap (· * ·) E (1 : Matrix (Fin d) (Fin d) ℂ) *
      Matrix.kroneckerMap (· * ·) ρR ρL) = (E * ρR).trace • ρL := by
  ext i j
  rw [partialTraceR, Matrix.of_apply, ← Matrix.mul_kronecker_mul, one_mul]
  simp only [Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag_apply]
  rw [← Finset.sum_mul]

/-- Negative control 2: on the 2-qubit classically correlated state `½(|00⟩⟨00|+|11⟩⟨11|)`,
    the non-trivial X-basis projector `E_+ = |+⟩⟨+|` satisfies `E_+ ≠ ½ I` yet yields zero conditional change. -/
theorem classical_correlated_x_basis_zero_steering_control :
    let Eplus : Matrix (Fin 2) (Fin 2) ℂ := !![(2⁻¹ : ℂ), (2⁻¹ : ℂ); (2⁻¹ : ℂ), (2⁻¹ : ℂ)]
    let ρcc : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      Matrix.of fun p q =>
        if p = (0, 0) ∧ q = (0, 0) then (2⁻¹ : ℂ)
        else if p = (1, 1) ∧ q = (1, 1) then (2⁻¹ : ℂ)
        else 0
    let ρL : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![(2⁻¹ : ℂ), (2⁻¹ : ℂ)]
    Eplus ≠ (2⁻¹ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    partialTraceR (Matrix.kroneckerMap (· * ·) Eplus (1 : Matrix (Fin 2) (Fin 2) ℂ) * ρcc) =
      (2⁻¹ : ℂ) • ρL := by
  intro Eplus ρcc ρL
  constructor
  · intro h
    have h01 := congr_fun (congr_fun h 0) 1
    simp [Eplus] at h01
  · ext i j
    rw [partialTraceR, Matrix.of_apply]
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.sum_univ_two, Matrix.mul_apply, Fintype.sum_prod_type,
        Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
        Eplus, ρcc, ρL, Matrix.of_apply, Matrix.diagonal_apply] <;>
      norm_num

/-- Signed `±1` encoding of `Bool`. -/
def bSign (b : Bool) : ℝ := if b then 1 else -1

/-- CHSH polynomial `a0*b0 + a0*b1 + a1*b0 - a1*b1` on `Bool⁴`. -/
def chshPoly (a0 a1 b0 b1 : Bool) : ℝ :=
  bSign a0 * bSign b0 + bSign a0 * bSign b1 + bSign a1 * bSign b0 - bSign a1 * bSign b1

lemma chshPoly_le_two (a0 a1 b0 b1 : Bool) : chshPoly a0 a1 b0 b1 ≤ 2 := by
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> norm_num [chshPoly, bSign]

lemma neg_two_le_chshPoly (a0 a1 b0 b1 : Bool) : -2 ≤ chshPoly a0 a1 b0 b1 := by
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> norm_num [chshPoly, bSign]

/-- Exact rational Pythagorean CHSH/LF observables `A0=Z, A1=X, B0=(4/5)Z+(3/5)X, B1=(4/5)Z-(3/5)X`:
    all four are Hermitian involutions (`M² = I`) yielding Bell CHSH value `14/5 > 2`. -/
theorem rational_lf_observables_involutive_and_chsh :
    let A0 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
    let A1 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
    let B0 : Matrix (Fin 2) (Fin 2) ℝ := !![4/5, 3/5; 3/5, -4/5]
    let B1 : Matrix (Fin 2) (Fin 2) ℝ := !![4/5, -3/5; -3/5, -4/5]
    let bellExp := fun (A B : Matrix (Fin 2) (Fin 2) ℝ) => ((A * Bᵀ).trace) / 2
    A0 * A0 = 1 ∧ A1 * A1 = 1 ∧ B0 * B0 = 1 ∧ B1 * B1 = 1 ∧
    bellExp A0 B0 = 4/5 ∧ bellExp A0 B1 = 4/5 ∧ bellExp A1 B0 = 3/5 ∧ bellExp A1 B1 = -3/5 ∧
    bellExp A0 B0 + bellExp A0 B1 + bellExp A1 B0 - bellExp A1 B1 = 14/5 := by
  intro A0 A1 B0 B1 bellExp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [A0, Matrix.mul_apply]
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [A1, Matrix.mul_apply]
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [B0, Matrix.mul_apply]
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [B1, Matrix.mul_apply]
  · norm_num [bellExp, A0, B0, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  · norm_num [bellExp, A0, B1, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  · norm_num [bellExp, A1, B0, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  · norm_num [bellExp, A1, B1, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  · norm_num [bellExp, A0, A1, B0, B1, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]

/-- Farkas / Fine impossibility over `Bool⁴`: NO non-negative joint probability distribution
    `Q(a0,a1,b0,b1) ≥ 0` summing to `1` can reproduce the rational quantum correlations `(4/5, 4/5, 3/5, -3/5)`. -/
theorem rational_lf_no_nonnegative_global_section
    (Q : Bool → Bool → Bool → Bool → ℝ)
    (hNonneg : ∀ a0 a1 b0 b1, 0 ≤ Q a0 a1 b0 b1)
    (hNorm : ∑ a0 : Bool, ∑ a1 : Bool, ∑ b0 : Bool, ∑ b1 : Bool, Q a0 a1 b0 b1 = 1)
    (hE00 : ∑ a0 : Bool, ∑ a1 : Bool, ∑ b0 : Bool, ∑ b1 : Bool,
        bSign a0 * bSign b0 * Q a0 a1 b0 b1 = 4/5)
    (hE01 : ∑ a0 : Bool, ∑ a1 : Bool, ∑ b0 : Bool, ∑ b1 : Bool,
        bSign a0 * bSign b1 * Q a0 a1 b0 b1 = 4/5)
    (hE10 : ∑ a0 : Bool, ∑ a1 : Bool, ∑ b0 : Bool, ∑ b1 : Bool,
        bSign a1 * bSign b0 * Q a0 a1 b0 b1 = 3/5)
    (hE11 : ∑ a0 : Bool, ∑ a1 : Bool, ∑ b0 : Bool, ∑ b1 : Bool,
        bSign a1 * bSign b1 * Q a0 a1 b0 b1 = -3/5) :
    False := by
  have hS :
      ∑ a0 : Bool, ∑ a1 : Bool, ∑ b0 : Bool, ∑ b1 : Bool,
        chshPoly a0 a1 b0 b1 * Q a0 a1 b0 b1 = 14/5 := by
    have hcomb :
        ∀ a0 a1 b0 b1 : Bool,
          chshPoly a0 a1 b0 b1 * Q a0 a1 b0 b1 =
            bSign a0 * bSign b0 * Q a0 a1 b0 b1 +
            bSign a0 * bSign b1 * Q a0 a1 b0 b1 +
            bSign a1 * bSign b0 * Q a0 a1 b0 b1 -
            bSign a1 * bSign b1 * Q a0 a1 b0 b1 := by
      intro a0 a1 b0 b1; unfold chshPoly; ring
    simp_rw [hcomb, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    linarith
  have hBound :
      ∑ a0 : Bool, ∑ a1 : Bool, ∑ b0 : Bool, ∑ b1 : Bool,
        chshPoly a0 a1 b0 b1 * Q a0 a1 b0 b1 ≤
      ∑ a0 : Bool, ∑ a1 : Bool, ∑ b0 : Bool, ∑ b1 : Bool,
        2 * Q a0 a1 b0 b1 := by
    refine Finset.sum_le_sum fun a0 _ => Finset.sum_le_sum fun a1 _ =>
      Finset.sum_le_sum fun b0 _ => Finset.sum_le_sum fun b1 _ => ?_
    exact mul_le_mul_of_nonneg_right (chshPoly_le_two a0 a1 b0 b1) (hNonneg a0 a1 b0 b1)
  have hTwo :
      ∑ a0 : Bool, ∑ a1 : Bool, ∑ b0 : Bool, ∑ b1 : Bool, 2 * Q a0 a1 b0 b1 = 2 := by
    simp_rw [← Finset.mul_sum]
    rw [hNorm]
    ring
  linarith

/-- Exact rational Frauchiger–Renner (2018) `1/12` contradiction witness:
    on `|Ψ_FR⟩ = (|h,↓⟩ + |t,↓⟩ + |t,↑⟩)/√3`, all three FR certainty amplitudes vanish identically
    while `P(ok_R, ok_S) = 1/12 > 0`. -/
theorem frauchiger_renner_contradiction_witness :
    let psi : Fin 4 → ℝ := ![1, 0, 1, 1]
    let okR_okS : Fin 4 → ℝ := ![1, -1, -1, 1]
    let t_okS : Fin 4 → ℝ := ![0, 0, 1, -1]
    let h_up : Fin 4 → ℝ := ![0, 1, 0, 0]
    let okR_down : Fin 4 → ℝ := ![1, 0, -1, 0]
    let ip := fun (u v : Fin 4 → ℝ) => ∑ i : Fin 4, u i * v i
    ip t_okS psi = 0 ∧ ip h_up psi = 0 ∧ ip okR_down psi = 0 ∧
    (ip okR_okS psi) ^ 2 / (ip okR_okS okR_okS * ip psi psi) = 1 / 12 := by
  intro psi okR_okS t_okS h_up okR_down ip
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [ip, psi, okR_okS, t_okS, h_up, okR_down, Fin.sum_univ_four]

/-- Isotropic 2-qubit mixed Werner state `ρ_v = v |Φ⁺⟩⟨Φ⁺| + ((1 - v)/4) I₄`. -/
noncomputable def wernerState (v : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun p q =>
    (if p.1 = p.2 ∧ q.1 = q.2 then ((v / 2 : ℝ) : ℂ) else 0) +
    (if p = q then (((1 - v) / 4 : ℝ) : ℂ) else 0)

/-- Mixed-state control (C2): on any isotropic Werner state `ρ_v` with `v ≠ 0` (including mixed
    states `0 < v < 1`), the centered assemblage obeys `σ_L(E) - p ρ_L = (v/2)(Eᵀ - p I₂)`, so
    zero conditional steering is still equivalent to trivial scalar effect `E = p I₂`.
    Hence purity is not strictly necessary; centered-assemblage injectivity is the exact criterion. -/
theorem werner_mixed_state_zero_steering_iff_trivial
    (v : ℝ) (hv : v ≠ 0) (E : Matrix (Fin 2) (Fin 2) ℂ) :
    let p : ℂ := E.trace / 2
    let ρL : Matrix (Fin 2) (Fin 2) ℂ := (2⁻¹ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
    partialTraceR (Matrix.kroneckerMap (· * ·) E (1 : Matrix (Fin 2) (Fin 2) ℂ) * wernerState v) -
      p • ρL = ((v / 2 : ℝ) : ℂ) • (Eᵀ - p • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    (partialTraceR (Matrix.kroneckerMap (· * ·) E (1 : Matrix (Fin 2) (Fin 2) ℂ) * wernerState v) =
      p • ρL ↔ E = p • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  intro p ρL
  have hId :
      partialTraceR (Matrix.kroneckerMap (· * ·) E (1 : Matrix (Fin 2) (Fin 2) ℂ) * wernerState v) -
        p • ρL = ((v / 2 : ℝ) : ℂ) • (Eᵀ - p • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, partialTraceR, Matrix.of_apply,
        Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.kroneckerMap_apply,
        Matrix.one_apply, Matrix.transpose_apply, Matrix.trace, Matrix.diag_apply, wernerState,
        p, ρL, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_ofNat] <;>
      simp <;> ring
  refine ⟨hId, ?_⟩
  have hv2 : ((v / 2 : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (div_ne_zero hv two_ne_zero)
  constructor
  · intro h
    have hzero : ((v / 2 : ℝ) : ℂ) • (Eᵀ - p • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 0 := by
      rw [← hId, h, sub_self]
    have hT : Eᵀ - p • (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 :=
      (smul_eq_zero.mp hzero).resolve_left hv2
    have hTeq : Eᵀ = p • (1 : Matrix (Fin 2) (Fin 2) ℂ) := sub_eq_zero.mp hT
    ext i j
    have hji := congr_fun (congr_fun hTeq j) i
    simpa [Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, eq_comm] using hji
  · intro hE
    have hTeq : Eᵀ = p • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [hE, Matrix.transpose_smul, Matrix.transpose_one]
    have hsub :
        partialTraceR (Matrix.kroneckerMap (· * ·) E (1 : Matrix (Fin 2) (Fin 2) ℂ) * wernerState v) -
          p • ρL = 0 := by
      rw [hId, hTeq, sub_self, smul_zero]
    exact sub_eq_zero.mp hsub

end OSTQD_Layer2
