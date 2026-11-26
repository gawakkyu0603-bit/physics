import OSTQD.Basic

/-!
# OSTQD.Theorem4_DoubleUncertainty

Theorem 4:
  (a) Parisi–Wu Arrow of Auxiliary Time `s`: for Hermitian jump operators `K_k`,
      `2 Re Tr(ρ L(ρ)) = - ∑_k ‖[K_k, ρ]‖_F² ≤ 0`, with equality iff `∀ k, [K_k, ρ] = 0`.
  (b) Exact Algebraic Double-Uncertainty Pythagorean Identity:
      for any complete orthogonal pinching `P(ρ) = ∑_α Π_α ρ Π_α`,
      `S_L(P(ρ)) = S_L(ρ) + ‖ρ - P(ρ)‖_F²`.
  (c) Weak-Gravity Observable Invisibility on fixed-point observables (`[K_k, M] = 0 ⇒ L†(M) = 0`).
  (d) Microcanonical Decoherence-Free Subspace Preservation:
      states supported inside a single energy shell `Π_α` are pointwise invariant under
      every energy-shell actualization generator (`L(ρ) = 0` and `P(ρ) = ρ`).
-/

open scoped Matrix BigOperators ComplexConjugate

namespace OSTQD

variable {d m : ℕ}

/-- Linear entropy `S_L(ρ) = 1 - Re Tr(ρ²)`. -/
def linearEntropy (ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  1 - ((ρ * ρ).trace).re

/-- Orthogonal pinching (conditional expectation onto block-diagonal algebra):
`P(ρ) = ∑_α Π_α ρ Π_α`. -/
def pinching (P : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (ρ : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ α : Fin m, P α * ρ * P α

lemma gkslOne_hermitian_jump_eq_double_comm {K : Matrix (Fin d) (Fin d) ℂ}
    (hK : Kᴴ = K) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    gkslOne K ρ = -(2⁻¹ : ℂ) • comm K (comm K ρ) := by
  unfold gkslOne comm
  rw [hK]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, neg_smul, smul_sub, smul_add]
  set A := K * (K * ρ)
  set B := K * (ρ * K)
  set C := ρ * (K * K)
  have h2 : (2⁻¹ : ℂ) • B + (2⁻¹ : ℂ) • B = B := by rw [← add_smul]; norm_num
  conv_lhs => rw [← h2]
  abel

lemma trace_rho_gkslOne_hermitian {K ρ : Matrix (Fin d) (Fin d) ℂ}
    (hK : Kᴴ = K) (hρ : ρᴴ = ρ) :
    2 * ((ρ * gkslOne K ρ).trace).re = -frobNormSq (comm K ρ) := by
  have hcomm_dag : (comm K ρ)ᴴ = -(comm K ρ) := by
    unfold comm
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hK, hρ]
    abel
  have htr_id : (2 : ℂ) * (ρ * gkslOne K ρ).trace = -((comm K ρ)ᴴ * comm K ρ).trace := by
    rw [hcomm_dag, Matrix.neg_mul, Matrix.trace_neg, neg_neg]
    unfold gkslOne comm
    rw [hK]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_add,
      Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
    have t1 : (ρ * (K * K * ρ)).trace = (K * ρ * (ρ * K)).trace := by
      calc (ρ * (K * K * ρ)).trace
          = ((ρ * K) * (K * ρ)).trace := by simp [Matrix.mul_assoc]
        _ = ((K * ρ) * (ρ * K)).trace := Matrix.trace_mul_comm _ _
    have t2 : (ρ * (ρ * (K * K))).trace = (K * ρ * (ρ * K)).trace := by
      calc (ρ * (ρ * (K * K))).trace
          = ((ρ * ρ * K) * K).trace := by simp [Matrix.mul_assoc]
        _ = (K * (ρ * ρ * K)).trace := Matrix.trace_mul_comm _ _
        _ = (K * ρ * (ρ * K)).trace := by simp [Matrix.mul_assoc]
    have t3 : (K * ρ * (K * ρ)).trace = (ρ * (K * ρ * K)).trace := by
      calc (K * ρ * (K * ρ)).trace
          = (K * (ρ * K * ρ)).trace := by simp [Matrix.mul_assoc]
        _ = ((ρ * K * ρ) * K).trace := Matrix.trace_mul_comm _ _
        _ = (ρ * (K * ρ * K)).trace := by simp [Matrix.mul_assoc]
    have t4 : (ρ * K * (K * ρ)).trace = (K * ρ * (ρ * K)).trace :=
      Matrix.trace_mul_comm _ _
    have t5 : (ρ * K * (ρ * K)).trace = (ρ * (K * ρ * K)).trace := by
      simp [Matrix.mul_assoc]
    rw [t1, t2, t3, t4, t5]
    ring
  have hre := congrArg Complex.re htr_id
  simpa [trace_conjTranspose_mul_self_re] using hre

/-- **Theorem 4(a)** (Parisi–Wu Purity Monotonicity / Directed Arrow of `s ≥ 0`):
For Hermitian jump operators `Ks` and Hermitian state `ρ`,
`2 Re Tr(ρ L(ρ)) = - ∑_k ‖[K_k, ρ]‖_F² ≤ 0`, with equality iff `ρ` commutes with every `K_k`. -/
theorem parisi_wu_purity_monotonicity (Ks : List (Matrix (Fin d) (Fin d) ℂ))
    (hKs : ∀ K ∈ Ks, Kᴴ = K) {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : ρᴴ = ρ) :
    2 * ((ρ * gksl Ks ρ).trace).re =
      -(Ks.map (fun K => frobNormSq (comm K ρ))).sum ∧
    2 * ((ρ * gksl Ks ρ).trace).re ≤ 0 ∧
    (2 * ((ρ * gksl Ks ρ).trace).re = 0 ↔ ∀ K ∈ Ks, comm K ρ = 0) := by
  have heq : 2 * ((ρ * gksl Ks ρ).trace).re =
      -(Ks.map (fun K => frobNormSq (comm K ρ))).sum := by
    unfold gksl
    induction Ks with
    | nil => simp
    | cons K rest ih =>
      simp only [List.map_cons, List.sum_cons, Matrix.trace_add,
        Complex.add_re, mul_add, neg_add]
      rw [trace_rho_gkslOne_hermitian (hKs K (List.mem_cons_self ..)) hρ,
        ih (fun K' h' => hKs K' (List.mem_cons_of_mem _ h'))]
  have hnonneg : ∀ x ∈ Ks.map (fun K => frobNormSq (comm K ρ)), 0 ≤ x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨K, _, rfl⟩
    exact frobNormSq_nonneg _
  have hsum_nn : 0 ≤ (Ks.map (fun K => frobNormSq (comm K ρ))).sum :=
    list_sum_nonneg_of_mem hnonneg
  refine ⟨heq, by linarith, ?_⟩
  rw [heq, neg_eq_zero, list_sum_eq_zero_iff_of_nonneg hnonneg]
  constructor
  · intro hall K hK
    exact (frobNormSq_eq_zero_iff _).mp (hall _ (List.mem_map_of_mem hK))
  · intro hall x hx
    rcases List.mem_map.mp hx with ⟨K, hK, rfl⟩
    exact (frobNormSq_eq_zero_iff _).mpr (hall K hK)

lemma pinching_hermitian (P : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hP_herm : ∀ α, (P α)ᴴ = P α) {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : ρᴴ = ρ) :
    (pinching P ρ)ᴴ = pinching P ρ := by
  unfold pinching
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  simp [Matrix.conjTranspose_mul, hP_herm α, hρ, Matrix.mul_assoc]

lemma trace_pinching_mul_self (P : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hP_orth : ∀ α β, P α * P β = if α = β then P α else 0)
    (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (pinching P ρ * ρ).trace = (pinching P ρ * pinching P ρ).trace := by
  unfold pinching
  rw [Finset.sum_mul, Finset.sum_mul, Matrix.trace_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum, Matrix.trace_sum]
  rw [Finset.sum_eq_single α]
  · have h1 : P α * ρ * P α * (P α * ρ * P α) = P α * ρ * (P α * P α) * ρ * P α := by
      simp [Matrix.mul_assoc]
    have h2 : P α * P α = P α := by simpa using hP_orth α α
    rw [h1, h2]
    calc (P α * ρ * P α * ρ).trace
        = ((P α * P α) * ρ * P α * ρ).trace := by rw [h2]
      _ = (P α * (P α * ρ * P α * ρ)).trace := by simp [Matrix.mul_assoc]
      _ = ((P α * ρ * P α * ρ) * P α).trace := Matrix.trace_mul_comm _ _
      _ = (P α * ρ * P α * ρ * P α).trace := by simp [Matrix.mul_assoc]
  · intro β _ hβα
    have h0 : P α * P β = 0 := by simpa [Ne.symm hβα] using hP_orth α β
    have : P α * ρ * P α * (P β * ρ * P β) = 0 := by
      calc P α * ρ * P α * (P β * ρ * P β)
          = P α * ρ * (P α * P β) * ρ * P β := by simp [Matrix.mul_assoc]
        _ = 0 := by simp [h0]
    rw [this, Matrix.trace_zero]
  · intro hα; exact (hα (Finset.mem_univ α)).elim

/-- **Theorem 4(b)** (Exact Algebraic Double-Uncertainty Pythagorean Law):
`S_L(P(ρ)) = S_L(ρ) + ‖ρ - P(ρ)‖_F²`, cleanly separating Layer 1 (unitary `t`-mixedness)
from Layer 2 (`s`-actualization coherence). -/
theorem double_uncertainty_pythagorean (P : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hP_herm : ∀ α, (P α)ᴴ = P α)
    (hP_orth : ∀ α β, P α * P β = if α = β then P α else 0)
    {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : ρᴴ = ρ) :
    linearEntropy (pinching P ρ) =
      linearEntropy ρ + frobNormSq (ρ - pinching P ρ) := by
  have hP_herm' := pinching_hermitian P hP_herm hρ
  have hcross1 : (pinching P ρ * ρ).trace = (pinching P ρ * pinching P ρ).trace :=
    trace_pinching_mul_self P hP_orth ρ
  have hcross2 : (ρ * pinching P ρ).trace = (pinching P ρ * pinching P ρ).trace := by
    rw [Matrix.trace_mul_comm, hcross1]
  have hdiff : ((ρ - pinching P ρ)ᴴ * (ρ - pinching P ρ)).trace =
      (ρ * ρ).trace - (pinching P ρ * pinching P ρ).trace := by
    rw [Matrix.conjTranspose_sub, hρ, hP_herm']
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, hcross1, hcross2]
    ring
  have hre := congrArg Complex.re hdiff
  rw [trace_conjTranspose_mul_self_re, Complex.sub_re] at hre
  unfold linearEntropy
  linarith

/-- **Theorem 4(c)** (Weak-Gravity Invisibility on Fixed-Point Observables):
Every observable `M` commuting with all Hermitian actualization operators `K_k`
satisfies `L†(M) = 0`. -/
theorem weak_gravity_invisibility (Ks : List (Matrix (Fin d) (Fin d) ℂ))
    (hKs : ∀ K ∈ Ks, Kᴴ = K) {M : Matrix (Fin d) (Fin d) ℂ}
    (hcomm : ∀ K ∈ Ks, comm K M = 0) :
    gkslDual Ks M = 0 := by
  unfold gkslDual
  have hmap : Ks.map (fun K => gkslDualOne K M) =
      Ks.map (fun _ => (0 : Matrix (Fin d) (Fin d) ℂ)) := by
    refine List.map_congr_left fun K hK => ?_
    have hKM : K * M = M * K := sub_eq_zero.mp (hcomm K hK)
    have hKd : Kᴴ = K := hKs K hK
    unfold gkslDualOne
    rw [hKd]
    have t1 : K * M * K = K * K * M := by rw [Matrix.mul_assoc, ← hKM, Matrix.mul_assoc]
    have t2 : M * (K * K) = K * K * M := by
      calc M * (K * K) = (M * K) * K := by rw [Matrix.mul_assoc]
        _ = (K * M) * K := by rw [hKM]
        _ = K * K * M := t1
    rw [t1, t2]
    have hh : (2⁻¹ : ℂ) • (K * K * M + K * K * M) = K * K * M := by
      rw [smul_add, ← add_smul]; norm_num
    rw [hh, sub_self]
  rw [hmap]
  induction Ks with
  | nil => simp
  | cons _ rest ih => simp

/-- **Theorem 4(d)** (Microcanonical Decoherence-Free Subspace Preservation):
Any state `ρ` supported inside a single eigen-sector `P_α` (`P_α ρ P_α = ρ`)
is pointwise invariant under every energy-shell actualization generator (`L(ρ) = 0`)
and under the pinching limit (`P(ρ) = ρ`). -/
theorem microcanonical_code_invariance (P : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hP_orth : ∀ α β, P α * P β = if α = β then P α else 0)
    (α : Fin m) (Ks : List (Matrix (Fin d) (Fin d) ℂ))
    (hKs : ∀ K ∈ Ks, Kᴴ = K)
    (hscalar : ∀ K ∈ Ks, ∃ c : ℂ, K * P α = c • P α ∧ P α * K = c • P α)
    {ρ : Matrix (Fin d) (Fin d) ℂ} (hsupp : P α * ρ * P α = ρ) :
    gksl Ks ρ = 0 ∧ pinching P ρ = ρ := by
  constructor
  · unfold gksl
    have hmap : Ks.map (fun K => gkslOne K ρ) =
        Ks.map (fun _ => (0 : Matrix (Fin d) (Fin d) ℂ)) := by
      refine List.map_congr_left fun K hK => ?_
      rcases hscalar K hK with ⟨c, hKL, hKR⟩
      have hcomm : comm K ρ = 0 := by
        unfold comm
        rw [← hsupp]
        calc K * (P α * ρ * P α) - P α * ρ * P α * K
            = (K * P α) * ρ * P α - P α * ρ * (P α * K) := by simp [Matrix.mul_assoc]
          _ = (c • P α) * ρ * P α - P α * ρ * (c • P α) := by rw [hKL, hKR]
          _ = 0 := by simp
      rw [gkslOne_hermitian_jump_eq_double_comm (hKs K hK) ρ, hcomm]
      simp [comm]
    rw [hmap]
    induction Ks with
    | nil => simp
    | cons _ rest ih => simp
  · unfold pinching
    rw [Finset.sum_eq_single α]
    · exact hsupp
    · intro β _ hβα
      rw [← hsupp]
      have h0 : P β * P α = 0 := by simpa [hβα] using hP_orth β α
      calc P β * (P α * ρ * P α) * P β
          = (P β * P α) * ρ * P α * P β := by simp [Matrix.mul_assoc]
        _ = 0 := by simp [h0]
    · intro hα; exact (hα (Finset.mem_univ α)).elim

/-- **Theorem 4(b')** (Exact Spectral-Block Decay Action Connecting `s`-Flow to Pinching):
When Hermitian jump operators `Ks` act as scalars `λ(K, α)` on orthogonal eigenprojections
`P α`, the GKSL generator acts on every off-diagonal block `P α * ρ * P β` as exact
multiplication by `-(1/2) ∑_k (λ_{k,α} - λ_{k,β})²`. Thus diagonal blocks (`α = β`) are
strictly fixed while off-diagonal blocks (`α ≠ β`) decay exponentially whenever separated
by at least one jump eigenvalue, directly linking `lim_{s→∞} exp(s L)(ρ) = pinching P ρ`. -/
theorem commuting_jumps_block_eigenvalue (P : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (Ks : List (Matrix (Fin d) (Fin d) ℂ))
    (hKs : ∀ K ∈ Ks, Kᴴ = K)
    (lam : Matrix (Fin d) (Fin d) ℂ → Fin m → ℝ)
    (hspec : ∀ K ∈ Ks, ∀ α : Fin m,
      K * P α = (lam K α : ℂ) • P α ∧ P α * K = (lam K α : ℂ) • P α)
    (α β : Fin m) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    gksl Ks (P α * ρ * P β) =
      (-(2⁻¹ : ℂ) * (Ks.map (fun K => (((lam K α - lam K β : ℝ) : ℂ) ^ 2))).sum) •
        (P α * ρ * P β) := by
  have hone : ∀ K ∈ Ks, gkslOne K (P α * ρ * P β) =
      (-(2⁻¹ : ℂ) * (((lam K α - lam K β : ℝ) : ℂ) ^ 2)) • (P α * ρ * P β) := by
    intro K hK
    have hL := (hspec K hK α).1
    have hR := (hspec K hK β).2
    have hcomm1 : comm K (P α * ρ * P β) = ((lam K α - lam K β : ℝ) : ℂ) • (P α * ρ * P β) := by
      unfold comm
      calc K * (P α * ρ * P β) - P α * ρ * P β * K
          = (K * P α) * ρ * P β - P α * ρ * (P β * K) := by simp [Matrix.mul_assoc]
        _ = ((lam K α : ℂ) • P α) * ρ * P β - P α * ρ * ((lam K β : ℂ) • P β) := by rw [hL, hR]
        _ = (lam K α : ℂ) • (P α * ρ * P β) - (lam K β : ℂ) • (P α * ρ * P β) := by
            simp
        _ = ((lam K α - lam K β : ℝ) : ℂ) • (P α * ρ * P β) := by
            rw [Complex.ofReal_sub, sub_smul]
    have hcomm2 : comm K (comm K (P α * ρ * P β)) =
        (((lam K α - lam K β : ℝ) : ℂ) ^ 2) • (P α * ρ * P β) := by
      rw [hcomm1]
      unfold comm
      rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub]
      change ((lam K α - lam K β : ℝ) : ℂ) • comm K (P α * ρ * P β) = _
      rw [hcomm1, smul_smul, sq]
    rw [gkslOne_hermitian_jump_eq_double_comm (hKs K hK), hcomm2, smul_smul]
  unfold gksl
  induction Ks with
  | nil => simp
  | cons K rest ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, add_smul]
    have hK := hone K (List.mem_cons_self ..)
    have hrest_hKs : ∀ K' ∈ rest, K'ᴴ = K' := fun K' h' => hKs K' (List.mem_cons_of_mem _ h')
    have hrest_spec : ∀ K' ∈ rest, ∀ γ : Fin m,
        K' * P γ = (lam K' γ : ℂ) • P γ ∧ P γ * K' = (lam K' γ : ℂ) • P γ :=
      fun K' h' γ => hspec K' (List.mem_cons_of_mem _ h') γ
    have hrest_one : ∀ K' ∈ rest, gkslOne K' (P α * ρ * P β) =
        (-(2⁻¹ : ℂ) * (((lam K' α - lam K' β : ℝ) : ℂ) ^ 2)) • (P α * ρ * P β) :=
      fun K' h' => hone K' (List.mem_cons_of_mem _ h')
    rw [hK, ih hrest_hKs hrest_spec hrest_one]

/-- **Theorem 4(d')** (Coarse-Grained Microcanonical Window Compatibility with Non-Trivial
`t`-Scrambling):
If `P_win` is a coarse-grained energy-window projection commuting with a (possibly non-scalar
inside `P_win`) Hamiltonian `H` (`[H, P_win] = 0`) on which every jump `K ∈ Ks` acts as a
scalar, then for any state `ρ` supported in `P_win`, BOTH:
  1. `gksl Ks ρ = 0` (exact `s`-actualization invariance / DFS protection), AND
  2. `P_win * [H, ρ] * P_win = [H, ρ]` (non-trivial `t`-scrambling stays strictly inside `P_win`). -/
theorem microcanonical_window_scrambling_compatible
    (P_win H : Matrix (Fin d) (Fin d) ℂ)
    (hH_win : comm H P_win = 0)
    (Ks : List (Matrix (Fin d) (Fin d) ℂ))
    (hKs : ∀ K ∈ Ks, Kᴴ = K)
    (hscalar : ∀ K ∈ Ks, ∃ c : ℂ, K * P_win = c • P_win ∧ P_win * K = c • P_win)
    {ρ : Matrix (Fin d) (Fin d) ℂ} (hsupp : P_win * ρ * P_win = ρ) :
    gksl Ks ρ = 0 ∧ P_win * comm H ρ * P_win = comm H ρ := by
  have hHP : H * P_win = P_win * H := sub_eq_zero.mp hH_win
  constructor
  · unfold gksl
    have hmap : Ks.map (fun K => gkslOne K ρ) =
        Ks.map (fun _ => (0 : Matrix (Fin d) (Fin d) ℂ)) := by
      refine List.map_congr_left fun K hK => ?_
      rcases hscalar K hK with ⟨c, hKL, hKR⟩
      have hcomm : comm K ρ = 0 := by
        unfold comm
        rw [← hsupp]
        calc K * (P_win * ρ * P_win) - P_win * ρ * P_win * K
            = (K * P_win) * ρ * P_win - P_win * ρ * (P_win * K) := by simp [Matrix.mul_assoc]
          _ = (c • P_win) * ρ * P_win - P_win * ρ * (c • P_win) := by rw [hKL, hKR]
          _ = 0 := by simp
      rw [gkslOne_hermitian_jump_eq_double_comm (hKs K hK) ρ, hcomm]
      simp [comm]
    rw [hmap]
    induction Ks with
    | nil => simp
    | cons _ rest ih => simp
  · unfold comm
    rw [Matrix.mul_sub, Matrix.sub_mul]
    have t1 : P_win * (H * ρ) * P_win = H * ρ := by
      calc P_win * (H * ρ) * P_win
          = (P_win * H) * ρ * P_win := by simp [Matrix.mul_assoc]
        _ = (H * P_win) * ρ * P_win := by rw [← hHP]
        _ = H * (P_win * ρ * P_win) := by simp [Matrix.mul_assoc]
        _ = H * ρ := by rw [hsupp]
    have t2 : P_win * (ρ * H) * P_win = ρ * H := by
      calc P_win * (ρ * H) * P_win
          = P_win * ρ * (H * P_win) := by simp [Matrix.mul_assoc]
        _ = P_win * ρ * (P_win * H) := by rw [hHP]
        _ = (P_win * ρ * P_win) * H := by simp [Matrix.mul_assoc]
        _ = ρ * H := by rw [hsupp]
    rw [t1, t2]

end OSTQD
