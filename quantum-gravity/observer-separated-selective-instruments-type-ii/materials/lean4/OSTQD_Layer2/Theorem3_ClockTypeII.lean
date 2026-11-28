import OSTQD_Layer2.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# OSTQD_Layer2.Theorem3_ClockTypeII

Formalizes the finite-dimensional clock-dressed algebra precursor and semifinite trace-scale
invariance of Theorem 3 in `paper3_layer2_type2`:
1. Finite cyclic clock constraint unitary group `W : Fin K → U(n)`.
2. Gauge-averaging map `condExp W X = K⁻¹ ∑_t W_t X W_tᴴ` proved to be a unital, trace-preserving,
   idempotent Umegaki bimodule conditional expectation onto the invariant subalgebra `A_O^{(K)}`.
3. Born-weight invariance under `condExp` for any gauge-invariant effect `E ∈ A_O^{(K)}`.
4. Exact semifinite Type II trace-rescaling invariance (`τ' = c τ`) of both Layer-1 entropy change
   `ΔS_L1` and the Type II Holevo deficit `χ_II = S(ρ̄) - ∑ p_x S(ρ_x)`.
-/

open scoped Matrix BigOperators ComplexConjugate

namespace OSTQD_Layer2

variable {K n m : ℕ}

/-- A finite cyclic unitary representation `W : Fin K → U(n)` implementing `e^{2π i t C_tot / K}`. -/
structure ClockUnitaryRep (K n : ℕ) [NeZero K] where
  W : Fin K → Matrix (Fin n) (Fin n) ℂ
  mul_hom : ∀ s t : Fin K, W (s + t) = W s * W t
  unitary_right : ∀ t : Fin K, W t * (W t)ᴴ = 1
  unitary_left : ∀ t : Fin K, (W t)ᴴ * W t = 1

/-- Gauge-invariant (clock-dressed) subalgebra `A_O^{(K)} = {A : W_t A W_tᴴ = A}`. -/
def IsClockInvariant [NeZero K] (rep : ClockUnitaryRep K n)
    (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ t : Fin K, rep.W t * A * (rep.W t)ᴴ = A

/-- Umegaki gauge-averaging conditional expectation `E_inv(X) = K⁻¹ ∑_t W_t X W_tᴴ`. -/
noncomputable def condExp [NeZero K] (rep : ClockUnitaryRep K n)
    (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ((K : ℂ)⁻¹) • ∑ t : Fin K, rep.W t * X * (rep.W t)ᴴ

lemma clockRep_conjTranspose_add [NeZero K] (rep : ClockUnitaryRep K n) (s t : Fin K) :
    (rep.W (s + t))ᴴ = (rep.W t)ᴴ * (rep.W s)ᴴ := by
  rw [rep.mul_hom, Matrix.conjTranspose_mul]

/-- The image of `condExp` lies strictly inside the clock-invariant subalgebra `A_O^{(K)}`. -/
theorem condExp_invariant [NeZero K] (rep : ClockUnitaryRep K n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    IsClockInvariant rep (condExp rep X) := by
  intro s
  unfold condExp
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  have hterm : ∀ t : Fin K,
      rep.W s * (rep.W t * X * (rep.W t)ᴴ) * (rep.W s)ᴴ =
        rep.W (s + t) * X * (rep.W (s + t))ᴴ := by
    intro t
    rw [rep.mul_hom, Matrix.conjTranspose_mul]
    simp [Matrix.mul_assoc]
  simp_rw [hterm]
  exact Fintype.sum_equiv (Equiv.addLeft s) _ _ (fun _ => rfl)

/-- Unitality: `E_inv(1) = 1`. -/
theorem condExp_unital [NeZero K] (rep : ClockUnitaryRep K n) :
    condExp rep (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  unfold condExp
  have hterm : ∀ t : Fin K, rep.W t * (1 : Matrix (Fin n) (Fin n) ℂ) * (rep.W t)ᴴ = 1 := by
    intro t
    rw [Matrix.mul_one, rep.unitary_right]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have hK : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne K)
  rw [inv_mul_cancel₀ hK, one_smul]

/-- Trace preservation: `Tr(E_inv(X)) = Tr(X)`. -/
theorem condExp_trace_preserving [NeZero K] (rep : ClockUnitaryRep K n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    (condExp rep X).trace = X.trace := by
  unfold condExp
  rw [Matrix.trace_smul, Matrix.trace_sum]
  have hterm : ∀ t : Fin K, (rep.W t * X * (rep.W t)ᴴ).trace = X.trace := by
    intro t
    rw [Matrix.trace_mul_cycle, rep.unitary_left, one_mul]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul, ← mul_assoc]
  have hK : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne K)
  rw [inv_mul_cancel₀ hK, one_mul]

/-- Umegaki bimodule property: `E_inv(A X B) = A E_inv(X) B` for all `A, B ∈ A_O^{(K)}`. -/
theorem condExp_bimodule [NeZero K] (rep : ClockUnitaryRep K n)
    (A B X : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsClockInvariant rep A) (hB : IsClockInvariant rep B) :
    condExp rep (A * X * B) = A * condExp rep X * B := by
  unfold condExp
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hAt : rep.W t * A = A * rep.W t := by
    calc rep.W t * A
        = rep.W t * A * 1 := by rw [Matrix.mul_one]
      _ = rep.W t * A * ((rep.W t)ᴴ * rep.W t) := by rw [rep.unitary_left]
      _ = (rep.W t * A * (rep.W t)ᴴ) * rep.W t := by simp [Matrix.mul_assoc]
      _ = A * rep.W t := by rw [hA t]
  have hBt : B * (rep.W t)ᴴ = (rep.W t)ᴴ * B := by
    calc B * (rep.W t)ᴴ
        = 1 * B * (rep.W t)ᴴ := by rw [Matrix.one_mul]
      _ = ((rep.W t)ᴴ * rep.W t) * B * (rep.W t)ᴴ := by rw [rep.unitary_left]
      _ = (rep.W t)ᴴ * (rep.W t * B * (rep.W t)ᴴ) := by simp [Matrix.mul_assoc]
      _ = (rep.W t)ᴴ * B := by rw [hB t]
  calc rep.W t * (A * X * B) * (rep.W t)ᴴ
      = (rep.W t * A) * X * (B * (rep.W t)ᴴ) := by simp [Matrix.mul_assoc]
    _ = (A * rep.W t) * X * ((rep.W t)ᴴ * B) := by rw [hAt, hBt]
    _ = A * (rep.W t * X * (rep.W t)ᴴ) * B := by simp [Matrix.mul_assoc]

/-- Idempotence: `E_inv(E_inv(X)) = E_inv(X)`. -/
theorem condExp_idempotent [NeZero K] (rep : ClockUnitaryRep K n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    condExp rep (condExp rep X) = condExp rep X := by
  have h1 : IsClockInvariant rep (1 : Matrix (Fin n) (Fin n) ℂ) := by
    intro t; rw [Matrix.mul_one, rep.unitary_right]
  have h := condExp_bimodule rep (condExp rep X) 1 1 (condExp_invariant rep X) h1
  rw [Matrix.mul_one, Matrix.mul_one, condExp_unital, Matrix.mul_one, Matrix.mul_one] at h
  exact h

/-- Clock-invariant Born weight preservation: `Tr(E * E_inv(ρ)) = Tr(E * ρ)` for `E ∈ A_O^{(K)}`. -/
theorem covariant_effect_born_invariance [NeZero K] (rep : ClockUnitaryRep K n)
    (E ρ : Matrix (Fin n) (Fin n) ℂ) (hE : IsClockInvariant rep E) :
    bornWeight E (condExp rep ρ) = bornWeight E ρ := by
  unfold bornWeight
  have h1 : IsClockInvariant rep (1 : Matrix (Fin n) (Fin n) ℂ) := by
    intro t; rw [Matrix.mul_one, rep.unitary_right]
  have hbim := condExp_bimodule rep E 1 ρ hE h1
  rw [Matrix.mul_one, Matrix.mul_one] at hbim
  rw [← hbim, condExp_trace_preserving]

/-- Semifinite Type II trace-rescaling invariance: shifting every Segal entropy `S_τ(ρ) ↦ S_τ(ρ) + ln c`
    under `τ' = c τ` leaves `ΔS_L1`, `ΔS_L2_avg`, and `χ_II = S(ρ̄) - ∑ p_x S(ρ_x)` strictly invariant. -/
theorem segal_entropy_scale_invariance
    (S_init S_bar : ℝ) (p S_cond : Fin m → ℝ)
    (hProbSum : (∑ x : Fin m, p x) = 1) (c : ℝ) :
    let shift := Real.log c
    ((S_bar + shift) - (S_init + shift) = S_bar - S_init) ∧
    ((∑ x : Fin m, p x * ((S_cond x + shift) - (S_init + shift))) =
      ∑ x : Fin m, p x * (S_cond x - S_init)) ∧
    ((S_bar + shift) - (∑ x : Fin m, p x * (S_cond x + shift)) =
      S_bar - ∑ x : Fin m, p x * S_cond x) := by
  intro shift
  refine ⟨by ring, ?_, ?_⟩
  · refine Finset.sum_congr rfl fun x _ => by ring
  · have hsplit :
        (∑ x : Fin m, p x * (S_cond x + shift)) =
          (∑ x : Fin m, p x * S_cond x) + shift := by
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
      rw [hProbSum, one_mul]
    linarith

/-- Scalar functional-calculus inequalities underlying the repaired Step 2 of Theorem 3(b) (RR-1):
    for any spectral point `u > 0` and regulator `0 < η ≤ 1`,
    (1) `max 0 (log (u + η)) ≤ log (u + 1)`,
    (2) `log (u + 1) ≤ max 0 (log u) + log 2`, and
    (3) `u * log u ≤ u * log (u + η)`. -/
theorem regularized_log_domination_bounds (u η : ℝ) (hu : 0 < u) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    max 0 (Real.log (u + η)) ≤ Real.log (u + 1) ∧
    Real.log (u + 1) ≤ max 0 (Real.log u) + Real.log 2 ∧
    u * Real.log u ≤ u * Real.log (u + η) := by
  refine ⟨?_, ?_, ?_⟩
  · exact max_le (Real.log_nonneg (by linarith)) (Real.log_le_log (by linarith) (by linarith))
  · by_cases h1 : u ≤ 1
    · have hlog : Real.log (u + 1) ≤ Real.log 2 :=
        Real.log_le_log (by linarith) (by linarith)
      have h0 : (0 : ℝ) ≤ max 0 (Real.log u) := le_max_left _ _
      linarith
    · have hu1 : 1 < u := lt_of_not_ge h1
      have hlog : Real.log (u + 1) ≤ Real.log (2 * u) :=
        Real.log_le_log (by linarith) (by linarith)
      have hmul : Real.log (2 * u) = Real.log 2 + Real.log u :=
        Real.log_mul (by norm_num) (ne_of_gt hu)
      have hmax : Real.log u ≤ max 0 (Real.log u) := le_max_right _ _
      linarith
  · exact mul_le_mul_of_nonneg_left (Real.log_le_log hu (by linarith)) (le_of_lt hu)

end OSTQD_Layer2
