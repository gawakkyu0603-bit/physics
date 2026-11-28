import OSTQD.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# OSTQD.Theorem1_BPS

Theorem 1: Exact GKSL Carré-du-Champ Energy-Variance Identity,
Banks–Susskind–Peskin (BPS) Immunity Characterization, and Automatic
Two-Time `(t, s)` Commutation.
-/

open scoped Matrix BigOperators ComplexConjugate

namespace OSTQD

variable {d : ℕ}

lemma comm_conjTranspose_of_hermitian {L H : Matrix (Fin d) (Fin d) ℂ} (hH : Hᴴ = H) :
    (comm L H)ᴴ = H * Lᴴ - Lᴴ * H := by
  unfold comm
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hH]

lemma carreDuChampOne_eq_comm_sq {L H : Matrix (Fin d) (Fin d) ℂ} (hH : Hᴴ = H) :
    carreDuChampOne L H = (comm L H)ᴴ * comm L H := by
  unfold carreDuChampOne gkslDualOne
  rw [comm_conjTranspose_of_hermitian hH]
  unfold comm
  have hhalf : ∀ M : Matrix (Fin d) (Fin d) ℂ,
      (2⁻¹ : ℂ) • M + (2⁻¹ : ℂ) • M = M := by
    intro M
    rw [← add_smul]
    norm_num
  have h1 : (H * Lᴴ - Lᴴ * H) * (L * H - H * L) =
      H * Lᴴ * L * H - H * Lᴴ * H * L - Lᴴ * H * L * H + Lᴴ * H * H * L := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
    abel
  rw [h1]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_add, Matrix.add_mul, smul_add, Matrix.mul_assoc]
  have hcomb : (2⁻¹ : ℂ) • (H * (Lᴴ * (L * H))) + (2⁻¹ : ℂ) • (H * (Lᴴ * (L * H))) =
      H * (Lᴴ * (L * H)) := hhalf _
  -- Rearrange all terms cleanly via abel using hcomb
  calc Lᴴ * (H * (H * L)) - ((2⁻¹ : ℂ) • (Lᴴ * (L * (H * H))) + (2⁻¹ : ℂ) • (H * (H * (Lᴴ * L))))
        - (H * (Lᴴ * (H * L)) - ((2⁻¹ : ℂ) • (H * (Lᴴ * (L * H))) + (2⁻¹ : ℂ) • (H * (H * (Lᴴ * L)))))
        - (Lᴴ * (H * (L * H)) - ((2⁻¹ : ℂ) • (Lᴴ * (L * (H * H))) + (2⁻¹ : ℂ) • (H * (Lᴴ * (L * H)))))
      = ((2⁻¹ : ℂ) • (H * (Lᴴ * (L * H))) + (2⁻¹ : ℂ) • (H * (Lᴴ * (L * H))))
        - H * (Lᴴ * (H * L)) - Lᴴ * (H * (L * H)) + Lᴴ * (H * (H * L)) := by abel
    _ = H * (Lᴴ * (L * H)) - H * (Lᴴ * (H * L)) - Lᴴ * (H * (L * H)) + Lᴴ * (H * (H * L)) := by
        rw [hcomb]

/-- **Theorem 1(a)** (Exact Carré-du-Champ Energy-Variance Identity):
For any Hermitian Hamiltonian `H` and any GKSL jump list `Ls`,
`L†(H²) - H L†(H) - L†(H) H = ∑_k [L_k, H]† [L_k, H]`. -/
theorem carre_du_champ_eq_sum_comm_sq (Ls : List (Matrix (Fin d) (Fin d) ℂ))
    {H : Matrix (Fin d) (Fin d) ℂ} (hH : Hᴴ = H) :
    carreDuChamp Ls H = (Ls.map (fun L => (comm L H)ᴴ * comm L H)).sum := by
  rw [carreDuChamp_eq_sum]
  congr 1
  exact List.map_congr_left fun L _ => carreDuChampOne_eq_comm_sq hH

/-- **Theorem 1(b)** (Positive Semidefiniteness of Energy-Variance Production):
For any positive semidefinite state `ρ = Aᴴ * A` and Hermitian `H`,
`Re Tr(ρ Γ_L(H, H)) = ∑_k ‖[L_k, H] A†‖_F² ≥ 0`. -/
theorem carre_du_champ_trace_nonneg (Ls : List (Matrix (Fin d) (Fin d) ℂ))
    {H : Matrix (Fin d) (Fin d) ℂ} (hH : Hᴴ = H)
    (A : Matrix (Fin d) (Fin d) ℂ) :
    0 ≤ ((Aᴴ * A * carreDuChamp Ls H).trace).re := by
  rw [carre_du_champ_eq_sum_comm_sq Ls hH, mul_list_sum, trace_list_sum, re_list_sum]
  apply list_sum_nonneg_of_mem
  intro x hx
  rcases List.mem_map.mp hx with ⟨z, hz, rfl⟩
  rcases List.mem_map.mp hz with ⟨M, hM, rfl⟩
  rcases List.mem_map.mp hM with ⟨N, hN, rfl⟩
  rcases List.mem_map.mp hN with ⟨L, _, rfl⟩
  have hcyc : (Aᴴ * A * ((comm L H)ᴴ * comm L H)).trace =
      ((comm L H * Aᴴ)ᴴ * (comm L H * Aᴴ)).trace := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc (Aᴴ * A * ((comm L H)ᴴ * comm L H)).trace
        = (Aᴴ * (A * (comm L H)ᴴ * comm L H)).trace := by simp [Matrix.mul_assoc]
      _ = ((A * (comm L H)ᴴ * comm L H) * Aᴴ).trace := Matrix.trace_mul_comm _ _
      _ = (A * (comm L H)ᴴ * (comm L H * Aᴴ)).trace := by simp [Matrix.mul_assoc]
  rw [hcyc, trace_conjTranspose_mul_self_re]
  exact frobNormSq_nonneg _

lemma gkslDualOne_eq_zero_of_comm {L H : Matrix (Fin d) (Fin d) ℂ}
    (hH : Hᴴ = H) (hcomm : comm L H = 0) :
    gkslDualOne L H = 0 := by
  have hLH : L * H = H * L := sub_eq_zero.mp hcomm
  have hLdagH : H * Lᴴ = Lᴴ * H := by
    have := congrArg Matrix.conjTranspose hLH
    simpa [Matrix.conjTranspose_mul, hH] using this
  unfold gkslDualOne
  have hterm : Lᴴ * H * L = Lᴴ * L * H := by
    calc Lᴴ * H * L = Lᴴ * (H * L) := by rw [Matrix.mul_assoc]
      _ = Lᴴ * (L * H) := by rw [← hLH]
      _ = Lᴴ * L * H := by rw [Matrix.mul_assoc]
  have hterm2 : H * (Lᴴ * L) = Lᴴ * L * H := by
    calc H * (Lᴴ * L) = (H * Lᴴ) * L := by rw [Matrix.mul_assoc]
      _ = (Lᴴ * H) * L := by rw [hLdagH]
      _ = Lᴴ * L * H := hterm
  rw [hterm, hterm2]
  have hhalf : (2⁻¹ : ℂ) • (Lᴴ * L * H + Lᴴ * L * H) = Lᴴ * L * H := by
    rw [smul_add, ← add_smul]; norm_num
  rw [hhalf, sub_self]

lemma comm_mul_self_of_comm {L H : Matrix (Fin d) (Fin d) ℂ} (hcomm : comm L H = 0) :
    comm L (H * H) = 0 := by
  have hLH : L * H = H * L := sub_eq_zero.mp hcomm
  unfold comm
  calc L * (H * H) - H * H * L
      = (L * H) * H - H * (H * L) := by simp [Matrix.mul_assoc]
    _ = (H * L) * H - H * (L * H) := by rw [hLH]
    _ = H * (L * H) - H * (L * H) := by simp [Matrix.mul_assoc]
    _ = 0 := sub_self _

/-- **Theorem 1(c)** (Exact BPS-Immunity Characterization):
For Hermitian `H`, zero mean-energy drift AND zero energy-variance diffusion
(`L†(H) = 0 ∧ L†(H²) = 0`) holds **if and only if** every jump operator commutes with `H`. -/
theorem bps_immunity_iff_comm (Ls : List (Matrix (Fin d) (Fin d) ℂ))
    {H : Matrix (Fin d) (Fin d) ℂ} (hH : Hᴴ = H) :
    (gkslDual Ls H = 0 ∧ gkslDual Ls (H * H) = 0) ↔ ∀ L ∈ Ls, comm L H = 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    have hG : carreDuChamp Ls H = 0 := by
      unfold carreDuChamp
      rw [h1, h2]
      simp
    have htr : ((carreDuChamp Ls H).trace).re = 0 := by simp [hG]
    rw [carre_du_champ_eq_sum_comm_sq Ls hH, trace_list_sum, re_list_sum] at htr
    have hmap : ((Ls.map fun L => (comm L H)ᴴ * comm L H).map Matrix.trace).map Complex.re =
        Ls.map (fun L => frobNormSq (comm L H)) := by
      simp only [List.map_map]
      refine List.map_congr_left fun L _ => ?_
      exact trace_conjTranspose_mul_self_re (comm L H)
    rw [hmap] at htr
    have hnonneg : ∀ x ∈ Ls.map (fun L => frobNormSq (comm L H)), 0 ≤ x := by
      intro x hx
      rcases List.mem_map.mp hx with ⟨L, _, rfl⟩
      exact frobNormSq_nonneg _
    have hall := (list_sum_eq_zero_iff_of_nonneg hnonneg).mp htr
    intro L hL
    have hzero : frobNormSq (comm L H) = 0 :=
      hall (frobNormSq (comm L H)) (List.mem_map_of_mem hL)
    exact (frobNormSq_eq_zero_iff _).mp hzero
  · intro hall
    have hH2 : (H * H)ᴴ = H * H := by rw [Matrix.conjTranspose_mul, hH]
    constructor
    · unfold gkslDual
      have : Ls.map (fun L => gkslDualOne L H) = Ls.map (fun _ => (0 : Matrix (Fin d) (Fin d) ℂ)) :=
        List.map_congr_left fun L hL => gkslDualOne_eq_zero_of_comm hH (hall L hL)
      rw [this]
      induction Ls with
      | nil => simp
      | cons _ rest ih => simp
    · unfold gkslDual
      have : Ls.map (fun L => gkslDualOne L (H * H)) =
          Ls.map (fun _ => (0 : Matrix (Fin d) (Fin d) ℂ)) :=
        List.map_congr_left fun L hL =>
          gkslDualOne_eq_zero_of_comm hH2 (comm_mul_self_of_comm (hall L hL))
      rw [this]
      induction Ls with
      | nil => simp
      | cons _ rest ih => simp

lemma gkslOne_comm_of_comm {L H : Matrix (Fin d) (Fin d) ℂ}
    (hH : Hᴴ = H) (hcomm : comm L H = 0) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    gkslOne L (comm H ρ) = comm H (gkslOne L ρ) := by
  have hLH : L * H = H * L := sub_eq_zero.mp hcomm
  have hLdagH : Lᴴ * H = H * Lᴴ := by
    have := congrArg Matrix.conjTranspose hLH
    simpa [Matrix.conjTranspose_mul, hH] using this.symm
  have hLdLH : Lᴴ * L * H = H * (Lᴴ * L) := by
    rw [Matrix.mul_assoc Lᴴ L H, hLH, ← Matrix.mul_assoc Lᴴ H L, hLdagH, Matrix.mul_assoc H Lᴴ L]
  unfold gkslOne comm
  have a0 : L * (H * ρ) * Lᴴ = H * (L * ρ * Lᴴ) := by
    rw [← Matrix.mul_assoc L H ρ, hLH, Matrix.mul_assoc H L ρ, Matrix.mul_assoc H (L * ρ) Lᴴ]
  have b0 : L * (ρ * H) * Lᴴ = L * ρ * Lᴴ * H := by
    rw [Matrix.mul_assoc L (ρ * H) Lᴴ, Matrix.mul_assoc ρ H Lᴴ, ← hLdagH,
        ← Matrix.mul_assoc ρ Lᴴ H, ← Matrix.mul_assoc L (ρ * Lᴴ) H, ← Matrix.mul_assoc L ρ Lᴴ]
  have t1 : L * (H * ρ - ρ * H) * Lᴴ = H * (L * ρ * Lᴴ) - L * ρ * Lᴴ * H := by
    rw [Matrix.mul_sub, Matrix.sub_mul, a0, b0]
  have a1 : Lᴴ * L * (H * ρ) = H * (Lᴴ * L * ρ) := by
    rw [← Matrix.mul_assoc (Lᴴ * L) H ρ, hLdLH, Matrix.mul_assoc H (Lᴴ * L) ρ]
  have a2 : ρ * H * (Lᴴ * L) = ρ * (Lᴴ * L) * H := by
    rw [Matrix.mul_assoc ρ H (Lᴴ * L), ← hLdLH, ← Matrix.mul_assoc ρ (Lᴴ * L) H]
  have a3 : Lᴴ * L * (ρ * H) = Lᴴ * L * ρ * H := (Matrix.mul_assoc (Lᴴ * L) ρ H).symm
  have a4 : H * ρ * (Lᴴ * L) = H * (ρ * (Lᴴ * L)) := Matrix.mul_assoc H ρ (Lᴴ * L)
  have t2 : Lᴴ * L * (H * ρ - ρ * H) + (H * ρ - ρ * H) * (Lᴴ * L) =
      H * (Lᴴ * L * ρ + ρ * (Lᴴ * L)) - (Lᴴ * L * ρ + ρ * (Lᴴ * L)) * H := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, a1, a2, a3, a4]
    abel
  rw [t1, t2, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
  abel

/-- **Theorem 1(d)** (Automatic `(t, s)` Two-Time Commutation):
Every BPS-immune actualization generator commutes with unitary Hamiltonian evolution:
`L([H, ρ]) = [H, L(ρ)]`. -/
theorem two_time_commutation (Ls : List (Matrix (Fin d) (Fin d) ℂ))
    {H : Matrix (Fin d) (Fin d) ℂ} (hH : Hᴴ = H)
    (hcomm : ∀ L ∈ Ls, comm L H = 0) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    gksl Ls (comm H ρ) = comm H (gksl Ls ρ) := by
  unfold gksl
  induction Ls with
  | nil => simp [comm]
  | cons L rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have hL : comm L H = 0 := hcomm L (List.mem_cons_self ..)
    have hrest : ∀ L' ∈ rest, comm L' H = 0 := fun L' h' => hcomm L' (List.mem_cons_of_mem _ h')
    rw [gkslOne_comm_of_comm hH hL ρ, ih hrest]
    unfold comm
    rw [Matrix.mul_add, Matrix.add_mul]
    abel

/-- Exact initial derivative of energy variance `Var_ρ(H) = Tr(H² ρ) - (Tr(H ρ))²`
under a GKSL generator `Ls`:
`(d/ds) Var_ρ(H)|_{s=0} = Re Tr(L†(H²) ρ) - 2 Re Tr(H ρ) · Re Tr(L†(H) ρ)`. -/
noncomputable def varianceDeriv (Ls : List (Matrix (Fin d) (Fin d) ℂ))
    (H ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ((gkslDual Ls (H * H) * ρ).trace).re -
    2 * ((H * ρ).trace).re * ((gkslDual Ls H * ρ).trace).re

/-- **Theorem 1(e)** (Exact Full Variance-Derivative Decomposition with Drift Terms):
For arbitrary `Ls`, `H`, and `ρ`, the initial variance derivative splits into the
carré du champ expectation PLUS the mean-energy drift terms:
`varianceDeriv Ls H ρ = Re Tr(Γ_L(H, H) ρ) + Re Tr((H D + D H) ρ) - 2 Re Tr(H ρ) Re Tr(D ρ)`
where `D = L†(H)`. When `D ≠ 0` (e.g., `H_B`-conserving `L_B` evaluated on `H_A`),
the drift terms do NOT vanish on general mixed states such as `ρ = I / d`. -/
theorem variance_deriv_exact_decomp (Ls : List (Matrix (Fin d) (Fin d) ℂ))
    (H ρ : Matrix (Fin d) (Fin d) ℂ) :
    varianceDeriv Ls H ρ =
      ((carreDuChamp Ls H * ρ).trace).re +
      (((H * gkslDual Ls H + gkslDual Ls H * H) * ρ).trace).re -
      2 * ((H * ρ).trace).re * ((gkslDual Ls H * ρ).trace).re := by
  unfold varianceDeriv carreDuChamp
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.trace_sub, Matrix.trace_add,
    Complex.sub_re, Complex.add_re]
  ring

/-- **Theorem 1(f)** (Exact Eigenstate Drift-Cancellation Identity):
On ANY state `ρ` supported inside a single `H`-eigenspace with real eigenvalue `E`
(`H ρ = E ρ`, `ρ H = E ρ`, `Tr(ρ) = 1`, e.g., any pure energy eigenstate `|E⟩⟨E|`
including the infalling vacuum `|0_A⟩⟨0_A|`), the drift terms cancel IDENTICALLY even when
`L†(H) ≠ 0`, so the initial variance derivative equals the carré du champ expectation:
`varianceDeriv Ls H ρ = Re Tr(Γ_L(H, H) ρ)`. -/
theorem eigenstate_variance_deriv_eq_carre_du_champ
    (Ls : List (Matrix (Fin d) (Fin d) ℂ))
    (H ρ : Matrix (Fin d) (Fin d) ℂ) (E : ℝ)
    (hL : H * ρ = (E : ℂ) • ρ) (hR : ρ * H = (E : ℂ) • ρ)
    (htr : ρ.trace = 1) :
    varianceDeriv Ls H ρ = ((carreDuChamp Ls H * ρ).trace).re := by
  rw [variance_deriv_exact_decomp]
  set D := gkslDual Ls H
  have hHtr : (H * ρ).trace = (E : ℂ) := by
    rw [hL, Matrix.trace_smul, htr, smul_eq_mul, mul_one]
  have h1 : (H * D * ρ).trace = (E : ℂ) * (D * ρ).trace := by
    calc (H * D * ρ).trace
        = (H * (D * ρ)).trace := by rw [Matrix.mul_assoc]
      _ = ((D * ρ) * H).trace := Matrix.trace_mul_comm _ _
      _ = (D * (ρ * H)).trace := by rw [Matrix.mul_assoc]
      _ = (D * ((E : ℂ) • ρ)).trace := by rw [hR]
      _ = ((E : ℂ) • (D * ρ)).trace := by rw [Matrix.mul_smul]
      _ = (E : ℂ) * (D * ρ).trace := by rw [Matrix.trace_smul, smul_eq_mul]
  have h2 : (D * H * ρ).trace = (E : ℂ) * (D * ρ).trace := by
    calc (D * H * ρ).trace
        = (D * (H * ρ)).trace := by rw [Matrix.mul_assoc]
      _ = (D * ((E : ℂ) • ρ)).trace := by rw [hL]
      _ = ((E : ℂ) • (D * ρ)).trace := by rw [Matrix.mul_smul]
      _ = (E : ℂ) * (D * ρ).trace := by rw [Matrix.trace_smul, smul_eq_mul]
  have hdrift : (((H * D + D * H) * ρ).trace).re =
      2 * ((H * ρ).trace).re * ((D * ρ).trace).re := by
    rw [Matrix.add_mul, Matrix.trace_add, h1, h2, hHtr, Complex.add_re,
      Complex.re_ofReal_mul, Complex.ofReal_re]
    ring
  linarith

/-- **Theorem 1(g)** (Eigenbasis-Averaged Initial Variance Production):
For any complete family of `H`-eigenstate projections `ρ_j` (`∑_j ρ_j = 1`, each with
`H ρ_j = E_j ρ_j`, `ρ_j H = E_j ρ_j`, `Tr(ρ_j) = 1`), the sum of initial variance derivatives
over the eigenbasis equals `Re Tr(Γ_L(H, H))` identically. Thus `(1/d) Re Tr(Γ_L(H, H))`
is the exact eigenbasis-averaged initial energy-variance injection rate (not the variance
derivative of the maximally mixed state `I/d` itself). -/
theorem eigenbasis_sum_variance_deriv_eq_trace_carre_du_champ
    (Ls : List (Matrix (Fin d) (Fin d) ℂ))
    (H : Matrix (Fin d) (Fin d) ℂ)
    (ρ : Fin d → Matrix (Fin d) (Fin d) ℂ) (E : Fin d → ℝ)
    (hL : ∀ j, H * ρ j = (E j : ℂ) • ρ j)
    (hR : ∀ j, ρ j * H = (E j : ℂ) • ρ j)
    (htr : ∀ j, (ρ j).trace = 1)
    (hsum : ∑ j : Fin d, ρ j = 1) :
    ∑ j : Fin d, varianceDeriv Ls H (ρ j) = ((carreDuChamp Ls H).trace).re := by
  have hterm : ∀ j : Fin d, varianceDeriv Ls H (ρ j) =
      ((carreDuChamp Ls H * ρ j).trace).re := fun j =>
    eigenstate_variance_deriv_eq_carre_du_champ Ls H (ρ j) (E j) (hL j) (hR j) (htr j)
  simp_rw [hterm]
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.mul_sum, hsum, Matrix.mul_one]

/-!
### Structural Counterexamples: Non-Closure of `A_O` under `H_O` and Sufficiency of BPS
-/

/-- Membership predicate for the subalgebra `D_2 ⊗ M_2(ℂ) ⊂ M_4(ℂ)` in the tensor basis
`{|00⟩, |01⟩, |10⟩, |11⟩}`: off-diagonal `2×2` blocks vanish. -/
def inAlgD2xM2 (X : Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  (∀ i j : Fin 4, i.val < 2 → 2 ≤ j.val → X i j = 0) ∧
  (∀ i j : Fin 4, 2 ≤ i.val → j.val < 2 → X i j = 0)

/-- Counterexample Hamiltonian `H_O = σ_x ⊗ I_2` on `ℂ⁴`. -/
def nonclosedHO : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 1, 0;
     0, 0, 0, 1;
     1, 0, 0, 0;
     0, 1, 0, 0]

/-- Counterexample jump `L_O = I_2 ⊗ σ_z ∈ D_2 ⊗ M_2(ℂ)`. -/
def nonclosedLO : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![1, -1, 1, -1]

/-- Exact unitary `U(t) = exp(-i t (σ_x ⊗ I_2)) = cos(t) I_4 - i sin(t) (σ_x ⊗ I_2)`. -/
noncomputable def nonclosedU (t : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let c : ℂ := Real.cos t
  let is : ℂ := -Complex.I * (Real.sin t : ℂ)
  !![c, 0, is, 0;
     0, c, 0, is;
     is, 0, c, 0;
     0, is, 0, c]

/-- Two initial states `ρ_± = ((I ± σ_y)/2) ⊗ |0⟩⟨0|` agreeing on all of `D_2 ⊗ M_2(ℂ)`. -/
noncomputable def nonclosedRho (sgn : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(2⁻¹ : ℂ), 0, -((sgn : ℂ) * Complex.I / 2), 0;
     0, 0, 0, 0;
     ((sgn : ℂ) * Complex.I / 2), 0, (2⁻¹ : ℂ), 0;
     0, 0, 0, 0]

/-- Shared observable `Z_O = σ_z ⊗ I_2 ∈ D_2 ⊗ M_2(ℂ)`. -/
def nonclosedZO : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![1, 1, -1, -1]

/-- **Definition 1 Counterexample** (`[L_O, H_O] = 0` does NOT preserve `A_O` under `U_O(t)`):
On `M_4(ℂ)` with `A_O = D_2 ⊗ M_2(ℂ)`, `H_O = σ_x ⊗ I_2`, and `L_O = I_2 ⊗ σ_z`:
1. `L_O ∈ A_O` and `L_O` is strictly `H_O`-BPS-immune (`[L_O, H_O] = 0`), while `L_O` is
   nontrivial (`gksl [L_O]` does not vanish on `|+⟩⟨+|_2`).
2. `ρ_+` and `ρ_-` have unit trace and agree identically on every observable `X ∈ A_O`.
3. `U(t)` is unitary (`U(t)ᴴ U(t) = 1`), `Z_O ∈ A_O`, yet the Heisenberg-evolved expectations
   at time `t` split as `Re Tr(U(t)ᴴ Z_O U(t) ρ_+) = sin(2t)` and
   `Re Tr(U(t)ᴴ Z_O U(t) ρ_-) = -sin(2t)`. -/
theorem algebra_nonclosure_counterexample (t : ℝ) :
    inAlgD2xM2 nonclosedLO ∧
    inAlgD2xM2 nonclosedZO ∧
    comm nonclosedLO nonclosedHO = 0 ∧
    (nonclosedRho 1).trace = 1 ∧
    (nonclosedRho (-1)).trace = 1 ∧
    (∀ X : Matrix (Fin 4) (Fin 4) ℂ, inAlgD2xM2 X →
      (X * nonclosedRho 1).trace = (X * nonclosedRho (-1)).trace) ∧
    (nonclosedU t)ᴴ * nonclosedU t = 1 ∧
    (((nonclosedU t)ᴴ * nonclosedZO * nonclosedU t * nonclosedRho 1).trace).re = Real.sin (2 * t) ∧
    (((nonclosedU t)ᴴ * nonclosedZO * nonclosedU t * nonclosedRho (-1)).trace).re =
      -Real.sin (2 * t) := by
  have htrig : (Real.cos t) ^ 2 + (Real.sin t) ^ 2 = 1 := by
    rw [add_comm]; exact Real.sin_sq_add_cos_sq t
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor <;> intro i j hi hj <;> fin_cases i <;> fin_cases j <;> simp_all [nonclosedLO]
  · constructor <;> intro i j hi hj <;> fin_cases i <;> fin_cases j <;> simp_all [nonclosedZO]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [comm, nonclosedLO, nonclosedHO, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Matrix.diagonal_apply]
  · simp [Matrix.trace, Fin.sum_univ_four, nonclosedRho]; norm_num
  · simp [Matrix.trace, Fin.sum_univ_four, nonclosedRho]; norm_num
  · intro X hX
    have h02 : X 0 2 = 0 := hX.1 0 2 (by decide) (by decide)
    have h20 : X 2 0 = 0 := hX.2 2 0 (by decide) (by decide)
    simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_four, nonclosedRho, h02, h20]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [-Complex.ofReal_cos, -Complex.ofReal_sin, nonclosedU, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.conjTranspose_apply, Complex.ext_iff] <;>
      nlinarith [htrig]
  · rw [Real.sin_two_mul]
    simp [-Complex.ofReal_cos, -Complex.ofReal_sin, nonclosedU, nonclosedZO, nonclosedRho,
      Matrix.trace, Matrix.mul_apply, Fin.sum_univ_four, Matrix.conjTranspose_apply]
    ring
  · rw [Real.sin_two_mul]
    simp [-Complex.ofReal_cos, -Complex.ofReal_sin, nonclosedU, nonclosedZO, nonclosedRho,
      Matrix.trace, Matrix.mul_apply, Fin.sum_univ_four, Matrix.conjTranspose_apply]
    ring

/-- **Theorem 1(d) Precision** (BPS Immunity Is Sufficient, Not Necessary, for `(t,s)` Commutation):
For `d = 2`, `H = ω |1⟩⟨1|` (`ω ≠ 0`), and amplitude-damping jump `L = |0⟩⟨1|`, the GKSL
generator commutes identically with `ad_H` (`L([H, ρ]) = [H, L(ρ)]` for all `ρ`), yet
mean-energy conservation fails (`L†(H) = -H ≠ 0`). -/
theorem bps_sufficient_not_necessary_for_commutation (ω : ℝ) (hω : ω ≠ 0) :
    (∀ ρ : Matrix (Fin 2) (Fin 2) ℂ,
      gksl [!![(0 : ℂ), 1; 0, 0]] (comm (!![(0 : ℂ), 0; 0, (ω : ℂ)]) ρ) =
        comm (!![(0 : ℂ), 0; 0, (ω : ℂ)]) (gksl [!![(0 : ℂ), 1; 0, 0]] ρ)) ∧
    gkslDual [!![(0 : ℂ), 1; 0, 0]] (!![(0 : ℂ), 0; 0, (ω : ℂ)]) =
      -(!![(0 : ℂ), 0; 0, (ω : ℂ)]) ∧
    gkslDual [!![(0 : ℂ), 1; 0, 0]] (!![(0 : ℂ), 0; 0, (ω : ℂ)]) ≠ 0 := by
  have hdual : gkslDual [!![(0 : ℂ), 1; 0, 0]] (!![(0 : ℂ), 0; 0, (ω : ℂ)]) =
      -(!![(0 : ℂ), 0; 0, (ω : ℂ)]) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gkslDual, gkslDualOne, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_two, Matrix.conjTranspose_apply]
    ring
  refine ⟨?_, hdual, ?_⟩
  · intro ρ
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gksl, gkslOne, comm, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_two, Matrix.conjTranspose_apply] <;>
      ring
  · intro h0
    rw [hdual] at h0
    have h11 := congrFun (congrFun h0 1) 1
    simp at h11
    exact hω h11

/-- **Definition 1 Precision** (Non-Hermitian BPS-Immune Jump in a Degenerate Eigenspace Can Increase Purity):
Definition 1 permits non-Hermitian jump operators `L_k`. Even under strict self-clock BPS immunity
`[L, H] = 0`, population transfer inside a degenerate energy eigenspace can increase purity rather
than acting as pure dephasing: for `H = diag(0, 0, 1)`, `L = |0⟩⟨1|`, and `ρ = diag(3/4, 1/4, 0)`,
`[L, H] = 0` and `gkslDual [L] H = 0`, yet `L(ρ) = diag(1/4, -1/4, 0)` and the initial purity rate is
`2 Re Tr(ρ L(ρ)) = +1/4 > 0`. -/
theorem nonhermitian_bps_degenerate_purity_increase :
    let H : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![0, 0, 1]
    let L : Matrix (Fin 3) (Fin 3) ℂ := !![0, 1, 0; 0, 0, 0; 0, 0, 0]
    let ρ : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![(3 / 4 : ℂ), (1 / 4 : ℂ), 0]
    comm L H = 0 ∧
    gkslDual [L] H = 0 ∧
    ρ.trace = 1 ∧
    gksl [L] ρ = Matrix.diagonal ![(1 / 4 : ℂ), (-1 / 4 : ℂ), 0] ∧
    (2 * (ρ * gksl [L] ρ).trace).re = (1 / 4 : ℝ) := by
  dsimp only
  have hcomm : comm (!![(0 : ℂ), 1, 0; 0, 0, 0; 0, 0, 0]) (Matrix.diagonal ![(0 : ℂ), 0, 1]) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [comm, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.diagonal_apply]
  have hdual : gkslDual [!![(0 : ℂ), 1, 0; 0, 0, 0; 0, 0, 0]]
      (Matrix.diagonal ![(0 : ℂ), 0, 1]) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gkslDual, gkslDualOne, Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply]
  have htr : (Matrix.diagonal ![(3 / 4 : ℂ), (1 / 4 : ℂ), 0]).trace = 1 := by
    simp [Matrix.trace, Fin.sum_univ_three]
    norm_num
  have hgksl : gksl [!![(0 : ℂ), 1, 0; 0, 0, 0; 0, 0, 0]]
      (Matrix.diagonal ![(3 / 4 : ℂ), (1 / 4 : ℂ), 0]) =
      Matrix.diagonal ![(1 / 4 : ℂ), (-1 / 4 : ℂ), 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gksl, gkslOne, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_three, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    norm_num
  refine ⟨hcomm, hdual, htr, hgksl, ?_⟩
  rw [hgksl]
  simp [Matrix.trace, Fin.sum_univ_three]
  norm_num

end OSTQD
