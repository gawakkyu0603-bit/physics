import OSTQD_SK.Theorem1_CovariantKMS
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# OSTQD_SK.Theorem2_WardAndFDT

Theorem 2 and Proposition 2 (Composite Ward Identities, Semiclassical JT Saddle,
and Beyond-Gaussian Stochastic Schwarzian Cumulants):
  (a) Composite Gravity–Matter Energy Ward Identity (Strictly Two-Tiered):
      (a.1) Mean energy conservation `L_tot†(H_BH + H_rad) = 0` implies exact subsystem
            energy-flux balance `L_tot†(H_BH) = -L_tot†(H_rad)` (but NOT zero diffusion).
      (a.2) Full composite jump commutation `[H_BH + H_rad, L_k] = 0` implies BOTH
            mean conservation AND zero total carré du champ `Γ_{L_tot}(H_tot, H_tot) = 0`.
      (a.3) Explicit 3-level counterexample (`mean_energy_conservation_nonzero_diffusion`)
            proving `L†(H) = 0` with `Γ_L(H, H) = 2 |1⟩⟨1| ≠ 0`.
  (b) Semiclassical 2D JT Gravity + CFT Evaporating Saddle (`HasDerivAt` verification):
      exact ODE verification of `dE_BH/du = -(π c / 12) T_H(u)²`,
      `dE_BH/du = T_H(u) dS_BH/du`, and `dS_Hawk/du = (π c / 6) T_H(u) = -2 dS_BH/du`.
  (c) Linearized Gaussian Stochastic Schwarzian Model:
      algebraic leading-order equilibrium FDT `S_eq / (2 γ_E) = T_0² C_V(T_0) = 4 π² C T_0³`
      and exact `HasDerivAt` solution of the linearized evaporating variance ODE
      `dV/du = -2 γ_E V + (π c / 6) T_H(u)³`.
  (d) Beyond-Gaussian Bernard–Doyon JT Cumulants and Constructive `E ≥ 0` Detailed-Balance
      Jump Process (separating naive finite-`q` detailed-balance violation from the exact
      entropy-difference jump kernel on `E ≥ 0`).
-/

open scoped Matrix BigOperators ComplexConjugate

namespace OSTQD_SK

variable {d : ℕ}

lemma gkslDualOne_add (L X Y : Matrix (Fin d) (Fin d) ℂ) :
    gkslDualOne L (X + Y) = gkslDualOne L X + gkslDualOne L Y := by
  unfold gkslDualOne
  simp only [Matrix.mul_add, Matrix.add_mul, smul_add]
  abel

lemma gkslDual_add (Ls : List (Matrix (Fin d) (Fin d) ℂ))
    (X Y : Matrix (Fin d) (Fin d) ℂ) :
    gkslDual Ls (X + Y) = gkslDual Ls X + gkslDual Ls Y := by
  induction Ls with
  | nil => simp [gkslDual]
  | cons L rest ih =>
    unfold gkslDual at ih ⊢
    simp only [List.map_cons, List.sum_cons]
    rw [gkslDualOne_add, ih]
    abel

lemma list_sum_map_zero_mat (Ls : List (Matrix (Fin d) (Fin d) ℂ)) :
    (Ls.map (fun _ => (0 : Matrix (Fin d) (Fin d) ℂ))).sum = 0 := by
  induction Ls with
  | nil => simp
  | cons _ _ _ => simp

/-- **Theorem 2(a.1)** (Composite Energy Ward Identity):
Whenever `L_tot†(H_BH + H_rad) = 0`, the black-hole and radiation flux operators
are exact negatives of each other (`L_tot†(H_BH) = -L_tot†(H_rad)`), so for every
state `ρ`, `Tr(ρ L_tot†(H_BH)) + Tr(ρ L_tot†(H_rad)) = 0`. -/
theorem bipartite_energy_ward_identity
    (Ls : List (Matrix (Fin d) (Fin d) ℂ))
    (H_BH H_rad : Matrix (Fin d) (Fin d) ℂ)
    (hcons : gkslDual Ls (H_BH + H_rad) = 0) :
    gkslDual Ls H_BH = -gkslDual Ls H_rad ∧
    ∀ ρ : Matrix (Fin d) (Fin d) ℂ,
      (ρ * gkslDual Ls H_BH).trace + (ρ * gkslDual Ls H_rad).trace = 0 := by
  rw [gkslDual_add] at hcons
  have hneg : gkslDual Ls H_BH = -gkslDual Ls H_rad := eq_neg_of_add_eq_zero_left hcons
  refine ⟨hneg, fun ρ => ?_⟩
  rw [hneg, Matrix.mul_neg, Matrix.trace_neg, neg_add_cancel]

/-- **Theorem 2(a.2)** (Total Energy Conservation from Composite Jump Commutation):
If every composite jump `L ∈ Ls` commutes with `H_tot = H_BH + H_rad` (Hermitian),
then `L_tot†(H_BH + H_rad) = 0`, `Γ_{L_tot}(H_BH + H_rad, H_BH + H_rad) = 0`,
and exact flux balance `L_tot†(H_BH) = -L_tot†(H_rad)` follows automatically. -/
theorem bipartite_ward_from_commuting_jumps
    (Ls : List (Matrix (Fin d) (Fin d) ℂ))
    {H_BH H_rad : Matrix (Fin d) (Fin d) ℂ}
    (hHtot : (H_BH + H_rad)ᴴ = H_BH + H_rad)
    (hcomm : ∀ L ∈ Ls, comm (H_BH + H_rad) L = 0) :
    gkslDual Ls (H_BH + H_rad) = 0 ∧
    carreDuChamp Ls (H_BH + H_rad) = 0 ∧
    gkslDual Ls H_BH = -gkslDual Ls H_rad := by
  let Lpairs : List (Matrix (Fin d) (Fin d) ℂ × ℝ) := Ls.map (fun L => (L, (0 : ℝ)))
  have hmap_fst : Lpairs.map Prod.fst = Ls := by
    simp [Lpairs, Function.comp_def]
  have heig : ∀ p ∈ Lpairs, comm (H_BH + H_rad) p.1 = -(p.2 : ℂ) • p.1 := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨L, hL, rfl⟩
    simp [hcomm L hL]
  have hdrift : gkslDual Ls (H_BH + H_rad) = 0 := by
    rw [← hmap_fst, eigenoperator_energy_drift Lpairs hHtot heig]
    have hzero : (Lpairs.map (fun p => (p.2 : ℂ) • (p.1ᴴ * p.1))).sum = 0 := by
      simp only [Lpairs, List.map_map, Function.comp_def, Complex.ofReal_zero, zero_smul]
      exact list_sum_map_zero_mat Ls
    rw [hzero, neg_zero]
  have hcdc : carreDuChamp Ls (H_BH + H_rad) = 0 := by
    rw [← hmap_fst, eigenoperator_carre_du_champ Lpairs hHtot heig]
    simp only [Lpairs, List.map_map, Function.comp_def, Complex.ofReal_zero,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_smul]
    exact list_sum_map_zero_mat Ls
  exact ⟨hdrift, hcdc, (bipartite_energy_ward_identity Ls H_BH H_rad hdrift).1⟩

/-- **Theorem 2(a.3)** (Explicit 3-Level Counterexample Separating Mean Energy Conservation
from Zero Energy Diffusion):
On `ℂ³` with `H = diag(0, 1, 2)` and jumps `L_- = |0⟩⟨1|`, `L_+ = |2⟩⟨1|`, the total
Heisenberg energy drift vanishes identically (`L†(H) = 0`), yet the energy carré du champ
is strictly non-zero (`Γ_L(H, H) = 2 |1⟩⟨1| ≠ 0`). Thus mean energy conservation alone
implies subsystem flux balance (`bipartite_energy_ward_identity`) but does NOT imply
zero energy diffusion without commuting jumps (`bipartite_ward_from_commuting_jumps`) or
explicit second-moment conservation. -/
theorem mean_energy_conservation_nonzero_diffusion :
    let H3 : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal (fun i : Fin 3 => (i.val : ℂ))
    let Lm : Matrix (Fin 3) (Fin 3) ℂ := Matrix.of fun i j => if i = 0 ∧ j = 1 then 1 else 0
    let Lp : Matrix (Fin 3) (Fin 3) ℂ := Matrix.of fun i j => if i = 2 ∧ j = 1 then 1 else 0
    gkslDual [Lm, Lp] H3 = 0 ∧
    carreDuChamp [Lm, Lp] H3 = Matrix.of (fun i j => if i = 1 ∧ j = 1 then (2 : ℂ) else 0) ∧
    carreDuChamp [Lm, Lp] H3 ≠ 0 := by
  intro H3 Lm Lp
  have hdrift : gkslDual [Lm, Lp] H3 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gkslDual, gkslDualOne, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.diagonal_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul, Fin.sum_univ_three, H3, Lm, Lp]
    ring
  have hcdc : carreDuChamp [Lm, Lp] H3 =
      Matrix.of (fun i j => if i = 1 ∧ j = 1 then (2 : ℂ) else 0) := by
    unfold carreDuChamp
    rw [hdrift, Matrix.mul_zero, Matrix.zero_mul, sub_zero, sub_zero]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gkslDual, gkslDualOne, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.diagonal_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul, Fin.sum_univ_three, H3, Lm, Lp]
    norm_num
  refine ⟨hdrift, hcdc, ?_⟩
  rw [hcdc]
  intro hzero
  have h11 := congrFun (congrFun hzero (1 : Fin 3)) (1 : Fin 3)
  simp at h11

/-!
### 2D JT Gravity + CFT Evaporating Saddle and Stochastic Schwarzian Backreaction
-/

noncomputable def jtDecayRate (C c : ℝ) : ℝ := c / (48 * Real.pi * C)
noncomputable def jtEnergyRate (C c : ℝ) : ℝ := c / (24 * Real.pi * C)
noncomputable def jtTemp (C c T0 u : ℝ) : ℝ := T0 * Real.exp (-jtDecayRate C c * u)
noncomputable def jtEnergy (C c T0 u : ℝ) : ℝ := 2 * Real.pi ^ 2 * C * (jtTemp C c T0 u) ^ 2
noncomputable def jtEntropy (C c S0 T0 u : ℝ) : ℝ := S0 + 4 * Real.pi ^ 2 * C * jtTemp C c T0 u
noncomputable def jtHawkingEntropy (C c T0 u : ℝ) : ℝ :=
  8 * Real.pi ^ 2 * C * T0 * (1 - Real.exp (-jtDecayRate C c * u))
noncomputable def jtEnergyVar (C c T0 u : ℝ) : ℝ :=
  8 * Real.pi ^ 2 * C * (jtTemp C c T0 u) ^ 3 * (1 - Real.exp (-jtDecayRate C c * u))

lemma hasDerivAt_jtTemp (C c T0 u : ℝ) :
    HasDerivAt (fun τ => jtTemp C c T0 τ) (-jtDecayRate C c * jtTemp C c T0 u) u := by
  unfold jtTemp
  have h1 : HasDerivAt (fun τ => -jtDecayRate C c * τ) (-jtDecayRate C c) u := by
    simpa using (hasDerivAt_id u).const_mul (-jtDecayRate C c)
  have h2 := (h1.exp).const_mul T0
  convert h2 using 1
  ring

/-- **Theorem 2(b)** (Exact 2D JT + CFT Evaporating Saddle, Ward Identity, and First Law):
For `C > 0`, the closed-form JT evaporation trajectory satisfies identically:
  (1) `dE_BH/du = -(π c / 12) T_H(u)²` (diffeomorphism / clock Ward identity),
  (2) `dE_BH/du = T_H(u) · dS_BH/du` (dynamical first law),
  (3) `dS_Hawk/du = (π c / 6) T_H(u)` (2D CFT irreversible radiation entropy growth). -/
theorem jt_evaporation_ward_ode (C c S0 T0 u : ℝ) (hC : C ≠ 0) :
    HasDerivAt (fun τ => jtEnergy C c T0 τ) (-(Real.pi * c / 12) * (jtTemp C c T0 u) ^ 2) u ∧
    HasDerivAt (fun τ => jtEntropy C c S0 T0 τ) (-(Real.pi * c / 12) * jtTemp C c T0 u) u ∧
    HasDerivAt (fun τ => jtHawkingEntropy C c T0 τ) ((Real.pi * c / 6) * jtTemp C c T0 u) u := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hT := hasDerivAt_jtTemp C c T0 u
  refine ⟨?_, ?_, ?_⟩
  · -- dE_BH/du = -(π c / 12) T_H(u)²
    have hT2 : HasDerivAt (fun τ => (jtTemp C c T0 τ) ^ 2)
        ((-jtDecayRate C c * jtTemp C c T0 u) * jtTemp C c T0 u +
         jtTemp C c T0 u * (-jtDecayRate C c * jtTemp C c T0 u)) u := by
      convert hT.mul hT using 1
      funext τ; simp only [Pi.mul_apply]; ring
    have hE := hT2.const_mul (2 * Real.pi ^ 2 * C)
    unfold jtEnergy
    convert hE using 1
    unfold jtDecayRate
    field_simp [hC, hpi]
    ring
  · -- dS_BH/du = -(π c / 12) T_H(u)
    have hS := (hT.const_mul (4 * Real.pi ^ 2 * C)).const_add S0
    unfold jtEntropy
    convert hS using 1
    unfold jtDecayRate
    field_simp [hC, hpi]
    ring
  · -- dS_Hawk/du = (π c / 6) T_H(u)
    have h1 : HasDerivAt (fun τ => -jtDecayRate C c * τ) (-jtDecayRate C c) u := by
      simpa using (hasDerivAt_id u).const_mul (-jtDecayRate C c)
    have h2 : HasDerivAt (fun τ => 1 - Real.exp (-jtDecayRate C c * τ))
        (0 - Real.exp (-jtDecayRate C c * u) * (-jtDecayRate C c)) u :=
      (hasDerivAt_const u (1 : ℝ)).sub h1.exp
    have h3 := h2.const_mul (8 * Real.pi ^ 2 * C * T0)
    unfold jtHawkingEntropy
    convert h3 using 1
    unfold jtTemp jtDecayRate
    field_simp [hC, hpi]
    ring

/-- **Theorem 2(c.1)** (Leading-Order Semiclassical Equilibrium Stochastic Schwarzian FDT):
With gravitational energy relaxation rate `γ_E = c / (24 π C)` and two-channel CFT
thermal flux noise `S_eq = (π c / 3) T_0³`, the stationary linearized Langevin variance
`S_eq / (2 γ_E)` matches the leading large-`C T_0` semiclassical thermodynamic variance
`T_0² C_V(T_0) = 4 π² C T_0³` (distinct from 1-loop Schwarzian disk corrections `(3/2) T_0²`). -/
theorem jt_equilibrium_fdt_exact (C c T0 : ℝ) (hC : C ≠ 0) (hc : c ≠ 0) :
    ((Real.pi * c / 3) * T0 ^ 3) / (2 * jtEnergyRate C c) =
      T0 ^ 2 * (4 * Real.pi ^ 2 * C * T0) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold jtEnergyRate
  field_simp [hC, hc, hpi]
  ring

/-- **Theorem 2(c.2)** (Exact Out-of-Equilibrium Evaporating Energy-Variance ODE):
Under chiral outgoing Hawking flux noise `S_chiral(u) = (π c / 6) T_H(u)³`, the
closed-form variance `V(u) = 8 π² C T_H(u)³ (1 - exp(-k_JT u))` satisfies the exact
stochastic Schwarzian variance equation `dV/du = -2 γ_E V(u) + (π c / 6) T_H(u)³`
with `V(0) = 0` and `V(u) ≥ 0` for all `u ≥ 0` (`C ≥ 0, c ≥ 0, T0 ≥ 0`). -/
theorem jt_evaporating_variance_ode (C c T0 u : ℝ) (hC : 0 < C) (hc : 0 ≤ c) (hT0 : 0 ≤ T0)
    (hu : 0 ≤ u) :
    HasDerivAt (fun τ => jtEnergyVar C c T0 τ)
      (-2 * jtEnergyRate C c * jtEnergyVar C c T0 u + (Real.pi * c / 6) * (jtTemp C c T0 u) ^ 3) u ∧
    jtEnergyVar C c T0 0 = 0 ∧
    0 ≤ jtEnergyVar C c T0 u := by
  have hCne : C ≠ 0 := ne_of_gt hC
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hT := hasDerivAt_jtTemp C c T0 u
  have hT3 : HasDerivAt (fun τ => (jtTemp C c T0 τ) ^ 3)
      (3 * (jtTemp C c T0 u) ^ 2 * (-jtDecayRate C c * jtTemp C c T0 u)) u := by
    have h3 := (hT.mul hT).mul hT
    convert h3 using 1
    · funext τ; simp only [Pi.mul_apply]; ring
    · simp only [Pi.mul_apply]; ring
  have h1 : HasDerivAt (fun τ => -jtDecayRate C c * τ) (-jtDecayRate C c) u := by
    simpa using (hasDerivAt_id u).const_mul (-jtDecayRate C c)
  have hfac : HasDerivAt (fun τ => 1 - Real.exp (-jtDecayRate C c * τ))
      (0 - Real.exp (-jtDecayRate C c * u) * (-jtDecayRate C c)) u :=
    (hasDerivAt_const u (1 : ℝ)).sub h1.exp
  have hprod := (hT3.mul hfac).const_mul (8 * Real.pi ^ 2 * C)
  refine ⟨?_, ?_, ?_⟩
  · unfold jtEnergyVar
    convert hprod using 1
    · funext τ; simp only [Pi.mul_apply]; ring
    · unfold jtEnergyRate jtDecayRate
      field_simp [hCne, hpi]
      ring
  · unfold jtEnergyVar; simp
  · unfold jtEnergyVar jtTemp jtDecayRate
    have hk_nn : 0 ≤ c / (48 * Real.pi * C) :=
      div_nonneg hc (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt Real.pi_pos)) (le_of_lt hC))
    have hexp_le : Real.exp (-(c / (48 * Real.pi * C)) * u) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith
    have hT_nn : 0 ≤ T0 * Real.exp (-(c / (48 * Real.pi * C)) * u) :=
      mul_nonneg hT0 (le_of_lt (Real.exp_pos _))
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (le_of_lt hC))
        (pow_nonneg hT_nn 3))
      (sub_nonneg.mpr hexp_le)

/-!
### Beyond-Gaussian Bernard–Doyon JT Cumulants and Three-Tier Equilibrium FDT Hierarchy
-/

/-- Third cumulant `K_3(u) = -12 π² C T_H(u)⁴ (1 - exp(-2 k_JT u))` for linearized
Markov Bernard–Doyon evaporation in 2D JT gravity. -/
noncomputable def jtCumulant3 (C c T0 u : ℝ) : ℝ :=
  -12 * Real.pi ^ 2 * C * (jtTemp C c T0 u) ^ 4 * (1 - Real.exp (-2 * jtDecayRate C c * u))

/-- Fourth cumulant `K_4(u) = 32 π² C T_H(u)⁵ (1 - exp(-3 k_JT u))` for linearized
Markov Bernard–Doyon evaporation in 2D JT gravity. -/
noncomputable def jtCumulant4 (C c T0 u : ℝ) : ℝ :=
  32 * Real.pi ^ 2 * C * (jtTemp C c T0 u) ^ 5 * (1 - Real.exp (-3 * jtDecayRate C c * u))

/-- **Theorem 2(d.1)** (Exact Frozen-Coefficient Additive Bernard–Doyon Evaporating
Cumulant ODEs, `n = 3, 4`):
Under the linearized-drift, saddle-frozen additive Bernard–Doyon CFT cumulant injection rates
`-(π c / 2) T_H(u)⁴` and `+(2 π c) T_H(u)⁵`, the closed-form cumulants `K_3(u) ≤ 0` and
`K_4(u) ≥ 0` solve `dK_3/du = -3 γ_E K_3 - (π c / 2) T_H⁴` and
`dK_4/du = -4 γ_E K_4 + 2 π c T_H⁵` with `K_3(0) = K_4(0) = 0`.
(State-dependent feedback terms such as `3 D_2'(E_bar) K_2` lie outside this frozen-coefficient
additive closure.) -/
theorem jt_evaporating_nongaussian_cumulants_ode (C c T0 u : ℝ) (hC : 0 < C) (hc : 0 ≤ c)
    (hT0 : 0 ≤ T0) (hu : 0 ≤ u) :
    HasDerivAt (fun τ => jtCumulant3 C c T0 τ)
      (-3 * jtEnergyRate C c * jtCumulant3 C c T0 u - (Real.pi * c / 2) * (jtTemp C c T0 u) ^ 4) u ∧
    jtCumulant3 C c T0 0 = 0 ∧
    jtCumulant3 C c T0 u ≤ 0 ∧
    HasDerivAt (fun τ => jtCumulant4 C c T0 τ)
      (-4 * jtEnergyRate C c * jtCumulant4 C c T0 u + (2 * Real.pi * c) * (jtTemp C c T0 u) ^ 5) u ∧
    jtCumulant4 C c T0 0 = 0 ∧
    0 ≤ jtCumulant4 C c T0 u := by
  have hCne : C ≠ 0 := ne_of_gt hC
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hT := hasDerivAt_jtTemp C c T0 u
  have hT2 : HasDerivAt (fun τ => (jtTemp C c T0 τ) ^ 2)
      (2 * jtTemp C c T0 u * (-jtDecayRate C c * jtTemp C c T0 u)) u := by
    convert hT.mul hT using 1
    · funext τ; simp only [Pi.mul_apply]; ring
    · ring
  have hT4 : HasDerivAt (fun τ => (jtTemp C c T0 τ) ^ 4)
      (4 * (jtTemp C c T0 u) ^ 3 * (-jtDecayRate C c * jtTemp C c T0 u)) u := by
    convert hT2.mul hT2 using 1
    · funext τ; simp only [Pi.mul_apply]; ring
    · ring
  have hT5 : HasDerivAt (fun τ => (jtTemp C c T0 τ) ^ 5)
      (5 * (jtTemp C c T0 u) ^ 4 * (-jtDecayRate C c * jtTemp C c T0 u)) u := by
    convert hT4.mul hT using 1
    · funext τ; simp only [Pi.mul_apply]; ring
    · ring
  have h1_2 : HasDerivAt (fun τ => -2 * jtDecayRate C c * τ) (-2 * jtDecayRate C c) u := by
    simpa using (hasDerivAt_id u).const_mul (-2 * jtDecayRate C c)
  have hfac2 : HasDerivAt (fun τ => 1 - Real.exp (-2 * jtDecayRate C c * τ))
      (0 - Real.exp (-2 * jtDecayRate C c * u) * (-2 * jtDecayRate C c)) u :=
    (hasDerivAt_const u (1 : ℝ)).sub h1_2.exp
  have h1_3 : HasDerivAt (fun τ => -3 * jtDecayRate C c * τ) (-3 * jtDecayRate C c) u := by
    simpa using (hasDerivAt_id u).const_mul (-3 * jtDecayRate C c)
  have hfac3 : HasDerivAt (fun τ => 1 - Real.exp (-3 * jtDecayRate C c * τ))
      (0 - Real.exp (-3 * jtDecayRate C c * u) * (-3 * jtDecayRate C c)) u :=
    (hasDerivAt_const u (1 : ℝ)).sub h1_3.exp
  have hk_nn : 0 ≤ jtDecayRate C c :=
    div_nonneg hc (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt Real.pi_pos)) (le_of_lt hC))
  have hT_nn : 0 ≤ jtTemp C c T0 u := mul_nonneg hT0 (le_of_lt (Real.exp_pos _))
  have hexp2_le : Real.exp (-2 * jtDecayRate C c * u) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have hexp3_le : Real.exp (-3 * jtDecayRate C c * u) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hprod3 := (hT4.mul hfac2).const_mul (-12 * Real.pi ^ 2 * C)
    unfold jtCumulant3
    convert hprod3 using 1
    · funext τ; simp only [Pi.mul_apply]; ring
    · unfold jtEnergyRate jtDecayRate
      field_simp [hCne, hpi]
      ring
  · unfold jtCumulant3; simp
  · unfold jtCumulant3
    have hpos : 0 ≤ 12 * Real.pi ^ 2 * C * (jtTemp C c T0 u) ^ 4 *
        (1 - Real.exp (-2 * jtDecayRate C c * u)) :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (le_of_lt hC))
          (pow_nonneg hT_nn 4))
        (sub_nonneg.mpr hexp2_le)
    linarith
  · have hprod4 := (hT5.mul hfac3).const_mul (32 * Real.pi ^ 2 * C)
    unfold jtCumulant4
    convert hprod4 using 1
    · funext τ; simp only [Pi.mul_apply]; ring
    · unfold jtEnergyRate jtDecayRate
      field_simp [hCne, hpi]
      ring
  · unfold jtCumulant4; simp
  · unfold jtCumulant4
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (le_of_lt hC))
        (pow_nonneg hT_nn 5))
      (sub_nonneg.mpr hexp3_le)

/-- **Theorem 2(d.2)** (Equilibrium 3rd/4th-Order Non-Gaussian FDT Obstruction):
Comparing leading semiclassical canonical cumulants `κ_3^can = 12 π² C T_0⁴`,
`κ_4^can = 48 π² C T_0⁵` against:
  (Tier 1) Linearized additive two-channel Bernard–Doyon noise: `K_3^lin = 0 ≠ κ_3^can`
           and `K_4^lin = 24 π² C T_0⁵ = (1/2) κ_4^can ≠ κ_4^can`.
  (Tier 2) Purely Gaussian state-dependent two-channel diffusion `D_2(E) = (π c / 6)(T(E)³ + T_0³)`:
           repairs `K_3^Gauss = 12 π² C T_0⁴ = κ_3^can`, but overshoots `n = 4` by 50%:
           `K_4^Gauss = 72 π² C T_0⁵ = (3/2) κ_4^can ≠ κ_4^can`. -/
theorem jt_equilibrium_nongaussian_fdt_obstruction (C c T0 : ℝ)
    (hC : 0 < C) (hc : 0 < c) (hT0 : 0 < T0) :
    let γE := jtEnergyRate C c
    let E0 := 2 * Real.pi ^ 2 * C * T0 ^ 2
    let κ2 := 4 * Real.pi ^ 2 * C * T0 ^ 3
    let κ3 := 12 * Real.pi ^ 2 * C * T0 ^ 4
    let κ4 := 48 * Real.pi ^ 2 * C * T0 ^ 5
    let K3_lin := ((Real.pi * c / 2) * (T0 ^ 4 - T0 ^ 4)) / (3 * γE)
    let K4_lin := (4 * Real.pi * c * T0 ^ 5) / (4 * γE)
    let D2_1 := 3 * γE * T0
    let D2_2 := 3 * γE * T0 / (2 * E0)
    let K3_gauss := (3 * D2_1 * κ2) / (3 * γE)
    let K4_gauss := (6 * D2_1 * K3_gauss + 6 * D2_2 * κ2 ^ 2) / (4 * γE)
    K3_lin = 0 ∧ K3_lin ≠ κ3 ∧
    K4_lin = 24 * Real.pi ^ 2 * C * T0 ^ 5 ∧ K4_lin ≠ κ4 ∧
    K3_gauss = κ3 ∧
    K4_gauss = 72 * Real.pi ^ 2 * C * T0 ^ 5 ∧ K4_gauss ≠ κ4 := by
  intro γE E0 κ2 κ3 κ4 K3_lin K4_lin D2_1 D2_2 K3_gauss K4_gauss
  have hpi : 0 < Real.pi := Real.pi_pos
  have hCne : C ≠ 0 := ne_of_gt hC
  have hcne : c ≠ 0 := ne_of_gt hc
  have hpine : Real.pi ≠ 0 := ne_of_gt hpi
  have hT0ne : T0 ≠ 0 := ne_of_gt hT0
  have hγpos : 0 < γE := by
    dsimp only [γE, jtEnergyRate]; positivity
  have hγne : γE ≠ 0 := ne_of_gt hγpos
  have hE0ne : E0 ≠ 0 := by dsimp only [E0]; positivity
  have hκ3_pos : 0 < κ3 := by dsimp only [κ3]; positivity
  have hκ4_pos : 0 < κ4 := by dsimp only [κ4]; positivity
  have hK3_lin : K3_lin = 0 := by dsimp only [K3_lin]; ring
  have hK4_lin : K4_lin = 24 * Real.pi ^ 2 * C * T0 ^ 5 := by
    dsimp only [K4_lin, γE, jtEnergyRate]
    field_simp [hCne, hcne, hpine]
  have hK3_gauss : K3_gauss = κ3 := by
    dsimp only [K3_gauss, D2_1, κ2, κ3]
    field_simp [hγne]
    ring
  have hK4_gauss : K4_gauss = 72 * Real.pi ^ 2 * C * T0 ^ 5 := by
    dsimp only [K4_gauss]
    rw [hK3_gauss]
    dsimp only [D2_1, D2_2, E0, κ2, κ3]
    field_simp [hγne, hCne, hpine, hT0ne]
    ring
  refine ⟨hK3_lin, ?_, hK4_lin, ?_, hK3_gauss, hK4_gauss, ?_⟩
  · rw [hK3_lin]; exact ne_of_lt hκ3_pos
  · rw [hK4_lin]; dsimp only [κ4]; linarith
  · rw [hK4_gauss]; dsimp only [κ4]; linarith

/-- **Theorem 2(d.3)** (Algebraic Hamilton–Jacobi Factorization and Leading Fourth-Cumulant
Cancellation for the State-Dependent Bernard–Doyon JT Closure):
  (1) The two-channel state-dependent Bernard–Doyon Kramers–Moyal Hamiltonian
      `H_KM(E, p) = K_BD(-p; T(E)) + K_BD(+p; T_0)` factors identically as
      `(π c / 12) · p (β_E + β_0) (p - (β_0 - β_E)) / (β_0 β_E (β_0 - p) (β_E + p))`,
      vanishing identically along the leading canonical Gibbs slope `p = β_0 - β_E`
      (reflecting the Bernard–Doyon exchange fluctuation symmetry `H(E, p) = H(E, β_0 - β_E - p)`).
  (2) Including the state-dependent non-Gaussian 3rd and 4th Kramers–Moyal coefficients
      (`D_3'(E_0) = -12 γ_E T_0²`, `D_4(E_0) = 4 π c T_0⁵`) cancels the 50% Tier-2 Gaussian
      overshoot (`54 + 18 - 48 + 24 = 48`) and restores `κ_4^can = 48 π² C T_0⁵` at leading
      large-`C T_0` order (distinct from global jump-process boundary prescriptions or 1-loop
      disk corrections). -/
theorem jt_bernard_doyon_hj_canonical_fdt (C c T0 βE β0 p : ℝ)
    (hC : 0 < C) (hc : 0 < c) (hT0 : 0 < T0)
    (hβE : βE ≠ 0) (hβ0 : β0 ≠ 0) (h1 : βE + p ≠ 0) (h2 : β0 - p ≠ 0) :
    let H_KM := (Real.pi * c / 12) * (1 / (βE + p) - 1 / βE + 1 / (β0 - p) - 1 / β0)
    let γE := jtEnergyRate C c
    let E0 := 2 * Real.pi ^ 2 * C * T0 ^ 2
    let κ2 := 4 * Real.pi ^ 2 * C * T0 ^ 3
    let κ3 := 12 * Real.pi ^ 2 * C * T0 ^ 4
    let D2_1 := 3 * γE * T0
    let D2_2 := 3 * γE * T0 / (2 * E0)
    let D3_1 := -12 * γE * T0 ^ 2
    let D4_0 := 4 * Real.pi * c * T0 ^ 5
    H_KM = (Real.pi * c / 12) *
        (p * (βE + β0) * (p - (β0 - βE))) / (β0 * βE * (β0 - p) * (βE + p)) ∧
    (Real.pi * c / 12) *
        (1 / (βE + (β0 - βE)) - 1 / βE + 1 / (β0 - (β0 - βE)) - 1 / β0) = 0 ∧
    (6 * D2_1 * κ3 + 6 * D2_2 * κ2 ^ 2 + 4 * D3_1 * κ2 + D4_0) / (4 * γE) =
        48 * Real.pi ^ 2 * C * T0 ^ 5 := by
  intro H_KM γE E0 κ2 κ3 D2_1 D2_2 D3_1 D4_0
  have hCne : C ≠ 0 := ne_of_gt hC
  have hcne : c ≠ 0 := ne_of_gt hc
  have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
  have hT0ne : T0 ≠ 0 := ne_of_gt hT0
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [H_KM]
    field_simp [hβE, hβ0, h1, h2]
    ring
  · have hsum : βE + (β0 - βE) = β0 := by ring
    have hdiff : β0 - (β0 - βE) = βE := by ring
    rw [hsum, hdiff]
    ring
  · dsimp only [D2_1, D2_2, D3_1, D4_0, E0, κ2, κ3, γE, jtEnergyRate]
    field_simp [hCne, hcne, hpine, hT0ne]
    ring

/-- Classical JT microcanonical black-hole entropy above extremality `S_BH(E) = 2 π √(2 C E)`. -/
noncomputable def jtEntropyOfEnergy (C E : ℝ) : ℝ :=
  2 * Real.pi * Real.sqrt (2 * C * E)

/-- Classical JT inverse Hawking temperature `β(E) = S_BH'(E) = π √(2 C / E)`. -/
noncomputable def jtBetaOfEnergy (C E : ℝ) : ℝ :=
  Real.pi * Real.sqrt (2 * C / E)

/-- Classical JT canonical equilibrium weight `π(E) = exp(S_BH(E) - β_0 E)` on `E ≥ 0`. -/
noncomputable def jtCanonicalWeight (C β0 E : ℝ) : ℝ :=
  Real.exp (jtEntropyOfEnergy C E - β0 * E)

/-- **Proposition 2(e.1)** (Finite-`q` Detailed-Balance Obstruction for Naive State-Dependent
Bernard–Doyon Jump Rates):
For `C > 0, β_0 > 0, α > 0, E > 0, q > 0`, the strict concavity of `S_BH(E) = 2 π √(2 C E)` forces
  `q β(E + q) < S_BH(E + q) - S_BH(E) < q β(E)`.
Consequently, even when jumps `q > E` are rejected at the `E = 0` boundary, the naive emission rate
`w_-^{naive}(E, q) = α exp(-q β(E))` paired with `w_+(E, q) = α exp(-q β_0)` strictly violates
finite-`q` detailed balance for the canonical equilibrium weight `π(E) = exp(S_BH(E) - β_0 E)`:
  `π(E) w_+(E, q) ≠ π(E + q) w_-^{naive}(E + q, q)`. -/
theorem jt_naive_bd_finite_q_detailed_balance_obstruction
    (C β0 α E q : ℝ) (hC : 0 < C) (hα : 0 < α) (hE : 0 < E) (hq : 0 < q) :
    q * jtBetaOfEnergy C (E + q) < jtEntropyOfEnergy C (E + q) - jtEntropyOfEnergy C E ∧
    jtEntropyOfEnergy C (E + q) - jtEntropyOfEnergy C E < q * jtBetaOfEnergy C E ∧
    jtCanonicalWeight C β0 E * (α * Real.exp (-q * β0)) ≠
      jtCanonicalWeight C β0 (E + q) * (α * Real.exp (-q * jtBetaOfEnergy C (E + q))) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2C : 0 < 2 * C := by linarith
  have hEq : 0 < E + q := by linarith
  have hs2C : 0 < Real.sqrt (2 * C) := Real.sqrt_pos.mpr h2C
  have hsE : 0 < Real.sqrt E := Real.sqrt_pos.mpr hE
  have hsEq : 0 < Real.sqrt (E + q) := Real.sqrt_pos.mpr hEq
  have hlt_sq : Real.sqrt E < Real.sqrt (E + q) := Real.sqrt_lt_sqrt (le_of_lt hE) (by linarith)
  have hsum_pos : 0 < Real.sqrt (E + q) + Real.sqrt E := by linarith
  have hdiff_sqrt : Real.sqrt (E + q) - Real.sqrt E = q / (Real.sqrt (E + q) + Real.sqrt E) := by
    rw [eq_div_iff (ne_of_gt hsum_pos)]
    have h1 : Real.sqrt (E + q) ^ 2 = E + q := Real.sq_sqrt (le_of_lt hEq)
    have h2 : Real.sqrt E ^ 2 = E := Real.sq_sqrt (le_of_lt hE)
    nlinarith
  have hSdiff : jtEntropyOfEnergy C (E + q) - jtEntropyOfEnergy C E =
      2 * Real.pi * Real.sqrt (2 * C) * (q / (Real.sqrt (E + q) + Real.sqrt E)) := by
    unfold jtEntropyOfEnergy
    rw [Real.sqrt_mul (le_of_lt h2C) (E + q), Real.sqrt_mul (le_of_lt h2C) E, ← hdiff_sqrt]
    ring
  have hqβEq : q * jtBetaOfEnergy C (E + q) =
      2 * Real.pi * Real.sqrt (2 * C) * (q / (2 * Real.sqrt (E + q))) := by
    unfold jtBetaOfEnergy
    rw [Real.sqrt_div (le_of_lt h2C) (E + q)]
    have hne : Real.sqrt (E + q) ≠ 0 := ne_of_gt hsEq
    field_simp [hne]
  have hqβE : q * jtBetaOfEnergy C E =
      2 * Real.pi * Real.sqrt (2 * C) * (q / (2 * Real.sqrt E)) := by
    unfold jtBetaOfEnergy
    rw [Real.sqrt_div (le_of_lt h2C) E]
    have hne : Real.sqrt E ≠ 0 := ne_of_gt hsE
    field_simp [hne]
  have hpref : 0 < 2 * Real.pi * Real.sqrt (2 * C) := by positivity
  have hlow : q * jtBetaOfEnergy C (E + q) <
      jtEntropyOfEnergy C (E + q) - jtEntropyOfEnergy C E := by
    rw [hSdiff, hqβEq]
    apply mul_lt_mul_of_pos_left _ hpref
    exact div_lt_div_of_pos_left hq hsum_pos (by linarith)
  have hhigh : jtEntropyOfEnergy C (E + q) - jtEntropyOfEnergy C E <
      q * jtBetaOfEnergy C E := by
    rw [hSdiff, hqβE]
    apply mul_lt_mul_of_pos_left _ hpref
    exact div_lt_div_of_pos_left hq (by linarith) (by linarith)
  refine ⟨hlow, hhigh, ?_⟩
  intro heq
  have hcancel : Real.exp (jtEntropyOfEnergy C E - β0 * E) * Real.exp (-q * β0) =
      Real.exp (jtEntropyOfEnergy C (E + q) - β0 * (E + q)) *
        Real.exp (-q * jtBetaOfEnergy C (E + q)) := by
    unfold jtCanonicalWeight at heq
    have hαne : α ≠ 0 := ne_of_gt hα
    have h1 : α * (Real.exp (jtEntropyOfEnergy C E - β0 * E) * Real.exp (-q * β0)) =
        α * (Real.exp (jtEntropyOfEnergy C (E + q) - β0 * (E + q)) *
          Real.exp (-q * jtBetaOfEnergy C (E + q))) := by
      linarith
    exact mul_left_cancel₀ hαne h1
  rw [← Real.exp_add, ← Real.exp_add] at hcancel
  have hexp_eq := Real.exp_injective hcancel
  linarith

/-- Constructive `E ≥ 0` entropy-difference emission jump kernel `w_-(E, q)` vanishing for `q > E`. -/
noncomputable def jtEntropyDiffEmissionRate (C α E q : ℝ) : ℝ :=
  if q ≤ E then α * Real.exp (jtEntropyOfEnergy C (E - q) - jtEntropyOfEnergy C E) else 0

/-- **Proposition 2(e.2)** (Constructive `E ≥ 0` Exact Finite-`q` Detailed-Balance Jump Process
and Large-`C` Curvature Expansion):
Replacing the naive emission rate by `w_-(E, q) = α exp(S_BH(E - q) - S_BH(E))` for `0 < q ≤ E`
(and `0` for `q > E`) with incoming rate `w_+(E, q) = α exp(-q β_0)` satisfies:
  (1) **Exact finite-`q` detailed balance** on `E ≥ 0`:
      `π(E) w_+(E, q) = π(E + q) w_-(E + q, q)` for all `E ≥ 0, q > 0`,
  (2) **Strict positivity** `w_+(E, q) > 0` and `w_-(E + q, q) > 0`,
  (3) **Boundary preservation**: for `0 ≤ E < q`, `w_-(E, q) = 0` (the process cannot exit `E ≥ 0`),
  (4) **Exact thermodynamic first and second derivatives** for `E > 0`:
      `S_BH'(E) = β(E)` and `S_BH''(E) = -β(E) / (2 E) < 0`, matching the large-`C` exponent
      `S_BH(E - q) - S_BH(E) = -q β(E) + (1/2) S_BH''(E) q² + O(q³ / E²)`. -/
theorem jt_entropy_diff_jump_exact_detailed_balance
    (C β0 α E q : ℝ) (hC : 0 < C) (hα : 0 < α) (hE : 0 ≤ E) (_hq : 0 < q) :
    jtCanonicalWeight C β0 E * (α * Real.exp (-q * β0)) =
      jtCanonicalWeight C β0 (E + q) * jtEntropyDiffEmissionRate C α (E + q) q ∧
    0 < α * Real.exp (-q * β0) ∧
    0 < jtEntropyDiffEmissionRate C α (E + q) q ∧
    (E < q → jtEntropyDiffEmissionRate C α E q = 0) ∧
    (0 < E →
      HasDerivAt (fun x => jtEntropyOfEnergy C x) (jtBetaOfEnergy C E) E ∧
      HasDerivAt (fun x => jtBetaOfEnergy C x) (-jtBetaOfEnergy C E / (2 * E)) E ∧
      -jtBetaOfEnergy C E / (2 * E) < 0) := by
  have hle : q ≤ E + q := by linarith
  have hdb : jtCanonicalWeight C β0 E * (α * Real.exp (-q * β0)) =
      jtCanonicalWeight C β0 (E + q) * jtEntropyDiffEmissionRate C α (E + q) q := by
    unfold jtCanonicalWeight jtEntropyDiffEmissionRate
    simp only [hle, ↓reduceIte]
    have hsub : E + q - q = E := by ring
    rw [hsub]
    calc Real.exp (jtEntropyOfEnergy C E - β0 * E) * (α * Real.exp (-q * β0))
        = α * (Real.exp (jtEntropyOfEnergy C E - β0 * E) * Real.exp (-q * β0)) := by ring
      _ = α * Real.exp ((jtEntropyOfEnergy C E - β0 * E) + (-q * β0)) := by rw [← Real.exp_add]
      _ = α * Real.exp ((jtEntropyOfEnergy C (E + q) - β0 * (E + q)) +
            (jtEntropyOfEnergy C E - jtEntropyOfEnergy C (E + q))) := by congr 2; ring
      _ = α * (Real.exp (jtEntropyOfEnergy C (E + q) - β0 * (E + q)) *
            Real.exp (jtEntropyOfEnergy C E - jtEntropyOfEnergy C (E + q))) := by rw [Real.exp_add]
      _ = Real.exp (jtEntropyOfEnergy C (E + q) - β0 * (E + q)) *
            (α * Real.exp (jtEntropyOfEnergy C E - jtEntropyOfEnergy C (E + q))) := by ring
  have hw_plus : 0 < α * Real.exp (-q * β0) := mul_pos hα (Real.exp_pos _)
  have hw_minus : 0 < jtEntropyDiffEmissionRate C α (E + q) q := by
    unfold jtEntropyDiffEmissionRate
    simp only [hle, ↓reduceIte]
    exact mul_pos hα (Real.exp_pos _)
  have hbdry : E < q → jtEntropyDiffEmissionRate C α E q = 0 := by
    intro hlt
    unfold jtEntropyDiffEmissionRate
    simp only [not_le.mpr hlt, ↓reduceIte]
  refine ⟨hdb, hw_plus, hw_minus, hbdry, ?_⟩
  intro hEpos
  have h2C : 0 < 2 * C := by linarith
  have h2CE_ne : 2 * C * E ≠ 0 := ne_of_gt (mul_pos h2C hEpos)
  have h2CdivE_ne : 2 * C / E ≠ 0 := ne_of_gt (div_pos h2C hEpos)
  have hEne : E ≠ 0 := ne_of_gt hEpos
  have hsE : 0 < Real.sqrt E := Real.sqrt_pos.mpr hEpos
  have hsEne : Real.sqrt E ≠ 0 := ne_of_gt hsE
  have hs2C : 0 < Real.sqrt (2 * C) := Real.sqrt_pos.mpr h2C
  have hS_deriv : HasDerivAt (fun x => jtEntropyOfEnergy C x) (jtBetaOfEnergy C E) E := by
    have hlin : HasDerivAt (fun x => 2 * C * x) (2 * C) E := by
      simpa using (hasDerivAt_id E).const_mul (2 * C)
    have hsqrt : HasDerivAt (fun x => Real.sqrt (2 * C * x))
        (2 * C / (2 * Real.sqrt (2 * C * E))) E := hlin.sqrt h2CE_ne
    have hfull := hsqrt.const_mul (2 * Real.pi)
    unfold jtEntropyOfEnergy jtBetaOfEnergy
    convert hfull using 1
    rw [Real.sqrt_mul (le_of_lt h2C) E, Real.sqrt_div (le_of_lt h2C) E]
    have hsq : Real.sqrt (2 * C) ^ 2 = 2 * C := Real.sq_sqrt (le_of_lt h2C)
    have hs2Cne : Real.sqrt (2 * C) ≠ 0 := ne_of_gt hs2C
    field_simp [hs2Cne, hsEne]
    rw [hsq]
  have hβ_deriv : HasDerivAt (fun x => jtBetaOfEnergy C x) (-jtBetaOfEnergy C E / (2 * E)) E := by
    have hdiv : HasDerivAt (fun x => 2 * C / x) (-(2 * C) / E ^ 2) E := by
      have h := (hasDerivAt_const E (2 * C)).div (hasDerivAt_id E) hEne
      convert h using 1
      · funext x; simp
      · simp
    have hsqrt : HasDerivAt (fun x => Real.sqrt (2 * C / x))
        ((-(2 * C) / E ^ 2) / (2 * Real.sqrt (2 * C / E))) E := hdiv.sqrt h2CdivE_ne
    have hfull := hsqrt.const_mul Real.pi
    unfold jtBetaOfEnergy
    convert hfull using 1
    have hsq : Real.sqrt (2 * C / E) ^ 2 = 2 * C / E :=
      Real.sq_sqrt (le_of_lt (div_pos h2C hEpos))
    have hsne : Real.sqrt (2 * C / E) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (div_pos h2C hEpos))
    field_simp [hEne, hsne]
    rw [hsq]
    field_simp [hEne]
  have hβ_neg : -jtBetaOfEnergy C E / (2 * E) < 0 := by
    have hβpos : 0 < jtBetaOfEnergy C E := by
      unfold jtBetaOfEnergy
      exact mul_pos Real.pi_pos (Real.sqrt_pos.mpr (div_pos h2C hEpos))
    exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hβpos) (by linarith)
  exact ⟨hS_deriv, hβ_deriv, hβ_neg⟩

end OSTQD_SK
