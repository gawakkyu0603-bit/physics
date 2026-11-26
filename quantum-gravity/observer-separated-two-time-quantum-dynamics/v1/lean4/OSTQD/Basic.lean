import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

/-!
# OSTQD.Basic

Core finite-dimensional matrix quantum mechanics and GKSL (Lindblad) superoperator
definitions for Observer-Separated Two-Time Quantum Dynamics (OSTQD).
-/

open scoped Matrix BigOperators ComplexConjugate

namespace OSTQD

variable {d m n : ℕ}

/-- Matrix commutator `[A, B] = A B - B A`. -/
def comm (A B : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  A * B - B * A

/-- Matrix anticommutator `{A, B} = A B + B A`. -/
def anticomm (A B : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  A * B + B * A

/-- Single-jump GKSL (Lindblad) Schrödinger generator
`L ρ L† - (1/2) {L† L, ρ}`. -/
noncomputable def gkslOne (L ρ : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  L * ρ * Lᴴ - (2⁻¹ : ℂ) • (Lᴴ * L * ρ + ρ * (Lᴴ * L))

/-- Multi-jump GKSL (Lindblad) Schrödinger generator. -/
noncomputable def gksl (Ls : List (Matrix (Fin d) (Fin d) ℂ))
    (ρ : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  (Ls.map (fun L => gkslOne L ρ)).sum

/-- Single-jump GKSL Heisenberg (dual) generator
`L† X L - (1/2) {L† L, X}`. -/
noncomputable def gkslDualOne (L X : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Lᴴ * X * L - (2⁻¹ : ℂ) • (Lᴴ * L * X + X * (Lᴴ * L))

/-- Multi-jump GKSL Heisenberg (dual) generator. -/
noncomputable def gkslDual (Ls : List (Matrix (Fin d) (Fin d) ℂ))
    (X : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  (Ls.map (fun L => gkslDualOne L X)).sum

/-- Single-jump carré du champ (dissipation form) on observable `X`:
`L†(X²) - X L†(X) - L†(X) X`. -/
noncomputable def carreDuChampOne (L X : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  gkslDualOne L (X * X) - X * gkslDualOne L X - gkslDualOne L X * X

/-- Multi-jump carré du champ (dissipation form) on observable `X`. -/
noncomputable def carreDuChamp (Ls : List (Matrix (Fin d) (Fin d) ℂ))
    (X : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  gkslDual Ls (X * X) - X * gkslDual Ls X - gkslDual Ls X * X

/-- Squared Frobenius (Hilbert–Schmidt) norm `‖A‖_F² = ∑_{i,j} |A_{ij}|²`. -/
def frobNormSq (A : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, Complex.normSq (A i j)

/-- Complex inner product `⟨u, v⟩ = ∑_i conj(u_i) * v_i` on `Fin n → ℂ`. -/
def vecInner {α : Type*} [Fintype α] (u v : α → ℂ) : ℂ :=
  ∑ i : α, star (u i) * v i

/-- Squared Euclidean norm `‖u‖² = ∑_i |u_i|²` on `α → ℂ`. -/
def vecNormSq {α : Type*} [Fintype α] (u : α → ℂ) : ℝ :=
  ∑ i : α, Complex.normSq (u i)

lemma star_mul_self_re (z : ℂ) : (star z * z).re = Complex.normSq z := by
  simp [Complex.normSq_apply]

lemma star_mul_self_im (z : ℂ) : (star z * z).im = 0 := by
  simp
  ring

lemma star_mul_self_eq_normSq (z : ℂ) : star z * z = (Complex.normSq z : ℂ) := by
  apply Complex.ext
  · simpa using star_mul_self_re z
  · simpa using star_mul_self_im z

lemma frobNormSq_nonneg (A : Matrix (Fin m) (Fin n) ℂ) : 0 ≤ frobNormSq A := by
  unfold frobNormSq
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

lemma frobNormSq_eq_zero_iff (A : Matrix (Fin m) (Fin n) ℂ) :
    frobNormSq A = 0 ↔ A = 0 := by
  constructor
  · intro h
    unfold frobNormSq at h
    have h1 : ∀ i ∈ (Finset.univ : Finset (Fin m)),
        ∑ j : Fin n, Complex.normSq (A i j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
        Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (A i j))).mp h
    ext i j
    have h2 : ∑ k : Fin n, Complex.normSq (A i k) = 0 := h1 i (Finset.mem_univ i)
    have h3 : Complex.normSq (A i j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Complex.normSq_nonneg (A i k))).mp h2 j
        (Finset.mem_univ j)
    exact Complex.normSq_eq_zero.mp h3
  · rintro rfl
    simp [frobNormSq]

lemma trace_conjTranspose_mul_self_re (A : Matrix (Fin m) (Fin n) ℂ) :
    ((Aᴴ * A).trace).re = frobNormSq A := by
  unfold frobNormSq
  rw [Matrix.trace, Complex.re_sum]
  simp_rw [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum,
    star_mul_self_re]
  rw [Finset.sum_comm]

lemma trace_conjTranspose_mul_self (A : Matrix (Fin m) (Fin n) ℂ) :
    (Aᴴ * A).trace = (frobNormSq A : ℂ) := by
  apply Complex.ext
  · simpa using trace_conjTranspose_mul_self_re A
  · rw [Matrix.trace, Complex.im_sum]
    simp_rw [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.im_sum,
      star_mul_self_im]
    simp

lemma vecInner_self_re {α : Type*} [Fintype α] (u : α → ℂ) :
    (vecInner u u).re = vecNormSq u := by
  unfold vecInner vecNormSq
  rw [Complex.re_sum]
  simp_rw [star_mul_self_re]

lemma vecNormSq_nonneg {α : Type*} [Fintype α] (u : α → ℂ) : 0 ≤ vecNormSq u :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

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

lemma trace_list_sum (Ms : List (Matrix (Fin d) (Fin d) ℂ)) :
    Ms.sum.trace = (Ms.map Matrix.trace).sum := by
  induction Ms with
  | nil => simp
  | cons M rest ih => simp [Matrix.trace_add, ih]

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

lemma mul_list_sum (A : Matrix (Fin d) (Fin d) ℂ) (Ms : List (Matrix (Fin d) (Fin d) ℂ)) :
    A * Ms.sum = (Ms.map (fun M => A * M)).sum := by
  induction Ms with
  | nil => simp
  | cons M rest ih => simp [Matrix.mul_add, ih]

lemma list_sum_mul (Ms : List (Matrix (Fin d) (Fin d) ℂ)) (A : Matrix (Fin d) (Fin d) ℂ) :
    Ms.sum * A = (Ms.map (fun M => M * A)).sum := by
  induction Ms with
  | nil => simp
  | cons M rest ih => simp [Matrix.add_mul, ih]

lemma carreDuChamp_eq_sum (Ls : List (Matrix (Fin d) (Fin d) ℂ))
    (X : Matrix (Fin d) (Fin d) ℂ) :
    carreDuChamp Ls X = (Ls.map (fun L => carreDuChampOne L X)).sum := by
  unfold carreDuChamp carreDuChampOne gkslDual
  induction Ls with
  | nil => simp
  | cons L rest ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Matrix.mul_add, Matrix.add_mul]
    calc (gkslDualOne L (X * X) + (rest.map fun L => gkslDualOne L (X * X)).sum)
          - (X * gkslDualOne L X + X * (rest.map fun L => gkslDualOne L X).sum)
          - (gkslDualOne L X * X + (rest.map fun L => gkslDualOne L X).sum * X)
        = (gkslDualOne L (X * X) - X * gkslDualOne L X - gkslDualOne L X * X)
          + ((rest.map fun L => gkslDualOne L (X * X)).sum
             - X * (rest.map fun L => gkslDualOne L X).sum
             - (rest.map fun L => gkslDualOne L X).sum * X) := by abel
      _ = _ := by rw [ih]

lemma re_list_sum (zs : List ℂ) : (zs.sum).re = (zs.map Complex.re).sum := by
  induction zs with
  | nil => simp
  | cons z rest ih => simp [ih]

lemma list_sum_nonneg_of_mem {xs : List ℝ} (h : ∀ x ∈ xs, 0 ≤ x) : 0 ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.sum_cons]
    exact add_nonneg (h x (List.mem_cons_self ..))
      (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

lemma list_sum_eq_zero_iff_of_nonneg {xs : List ℝ} (h : ∀ x ∈ xs, 0 ≤ x) :
    xs.sum = 0 ↔ ∀ x ∈ xs, x = 0 := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    have hx : 0 ≤ x := h x (List.mem_cons_self ..)
    have hrest : ∀ y ∈ rest, 0 ≤ y := fun y hy => h y (List.mem_cons_of_mem _ hy)
    have hsum : 0 ≤ rest.sum := list_sum_nonneg_of_mem hrest
    simp only [List.sum_cons, List.mem_cons, forall_eq_or_imp]
    constructor
    · intro h0
      have hx0 : x = 0 := by linarith
      have hr0 : rest.sum = 0 := by linarith
      exact ⟨hx0, (ih hrest).mp hr0⟩
    · rintro ⟨hx0, hr⟩
      rw [hx0, (ih hrest).mpr hr, add_zero]

end OSTQD
