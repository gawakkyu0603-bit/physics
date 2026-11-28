import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# OSTQD_Layer2.Basic

Core finite-dimensional matrix algebra, Frobenius norm, POVM / selective instrument
definitions, Born-weight normalization, and convex-combination linearity lemmas for
`paper3_layer2_type2`.
-/

open scoped Matrix BigOperators ComplexConjugate

namespace OSTQD_Layer2

variable {d m n k : ℕ}

/-- Matrix commutator `[A, B] = A B - B A`. -/
def comm (A B : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  A * B - B * A

/-- Squared Frobenius norm `‖A‖_F² = ∑_{i,j} |A_{ij}|²`. -/
def frobNormSq (A : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, Complex.normSq (A i j)

lemma star_mul_self_re (z : ℂ) : (star z * z).re = Complex.normSq z := by
  simp [Complex.normSq_apply]

lemma mul_star_self_re (z : ℂ) : (z * star z).re = Complex.normSq z := by
  simp [Complex.normSq_apply]

lemma frobNormSq_nonneg (A : Matrix (Fin m) (Fin n) ℂ) : 0 ≤ frobNormSq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- Exact vanishing characterization of the Frobenius norm. -/
theorem frobNormSq_eq_zero_iff (A : Matrix (Fin m) (Fin n) ℂ) :
    frobNormSq A = 0 ↔ A = 0 := by
  constructor
  · intro h
    unfold frobNormSq at h
    ext i j
    have hi : ∑ j' : Fin n, Complex.normSq (A i j') = 0 := by
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i' _ =>
        Finset.sum_nonneg (fun j' _ => Complex.normSq_nonneg (A i' j')))).mp h i (Finset.mem_univ i)
      exact h1
    have hij : Complex.normSq (A i j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j' _ => Complex.normSq_nonneg (A i j'))).mp hi j
        (Finset.mem_univ j)
    exact Complex.normSq_eq_zero.mp hij
  · intro h
    subst h
    simp [frobNormSq]

/-- Trace-Frobenius identity: `Re Tr(Aᴴ A) = ‖A‖_F²`. -/
theorem trace_conjTranspose_mul_self_re (A : Matrix (Fin m) (Fin n) ℂ) :
    ((Aᴴ * A).trace).re = frobNormSq A := by
  unfold frobNormSq
  rw [Matrix.trace, Complex.re_sum]
  simp_rw [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum,
    star_mul_self_re]
  rw [Finset.sum_comm]

/-- Trace-Frobenius identity (reverse order): `Re Tr(A Aᴴ) = ‖A‖_F²`. -/
theorem trace_mul_conjTranspose_self_re (A : Matrix (Fin m) (Fin n) ℂ) :
    ((A * Aᴴ).trace).re = frobNormSq A := by
  unfold frobNormSq
  rw [Matrix.trace, Complex.re_sum]
  simp_rw [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum,
    mul_star_self_re]

/-- Finite selective Kraus instrument branch `I_x(ρ) = K_x ρ K_xᴴ`. -/
def krausBranch (K ρ : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  K * ρ * Kᴴ

/-- Non-selective Layer-1 CPTP map obtained by summing selective branches. -/
def nonSelectiveMap (Ks : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (ρ : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ x : Fin k, krausBranch (Ks x) ρ

/-- POVM completeness condition `∑_x K_xᴴ K_x = 1`. -/
def IsCompleteKraus (Ks : Fin k → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∑ x : Fin k, (Ks x)ᴴ * Ks x) = 1

/-- Trace preservation of the non-selective Layer-1 map from Kraus completeness. -/
theorem nonSelectiveMap_trace_preserving
    (Ks : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (hComp : IsCompleteKraus Ks)
    (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (nonSelectiveMap Ks ρ).trace = ρ.trace := by
  unfold nonSelectiveMap krausBranch
  rw [Matrix.trace_sum]
  have hterm : ∀ x : Fin k, (Ks x * ρ * (Ks x)ᴴ).trace = ((Ks x)ᴴ * Ks x * ρ).trace := by
    intro x
    rw [Matrix.trace_mul_cycle]
  simp_rw [hterm]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hComp, one_mul]

/-- Born weight `Tr(E ρ)` associated with a POVM effect `E`. -/
def bornWeight (E ρ : Matrix (Fin d) (Fin d) ℂ) : ℂ :=
  (E * ρ).trace

/-- Born weights of any complete POVM `∑_x E_x = 1` sum to `Tr(ρ)`. -/
theorem bornWeight_sum_eq_trace
    (Es : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (hSum : (∑ x : Fin k, Es x) = 1)
    (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (∑ x : Fin k, bornWeight (Es x) ρ) = ρ.trace := by
  unfold bornWeight
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hSum, one_mul]

/-- Exact convex-combination affineness of Born weights. -/
theorem bornWeight_convex_affine
    (E ρ₁ ρ₂ : Matrix (Fin d) (Fin d) ℂ) (p : ℂ) :
    bornWeight E (p • ρ₁ + (1 - p) • ρ₂) =
      p * bornWeight E ρ₁ + (1 - p) * bornWeight E ρ₂ := by
  unfold bornWeight
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_smul]
  simp [smul_eq_mul]

end OSTQD_Layer2
