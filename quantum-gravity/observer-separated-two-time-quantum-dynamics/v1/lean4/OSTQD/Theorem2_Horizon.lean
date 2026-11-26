import OSTQD.Theorem1_BPS
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# OSTQD.Theorem2_Horizon

Theorem 2:
  (a) Observer-Separation Necessity (No-Go for universal zero-heating actualization across
      irreducibly non-commuting Hamiltonians `{H_A, H_B}' = ℂ·1`).
  (b) Quantitative Horizon-Heating Lower Bound via operator incompatibility `γ(H_A, H_B)`.
  (c) Static Weak-Field Gravitational Redshift Invariance (`H_B = α H_A ⇒ γ = 0`).
  (d) Exact Two-Level Bogoliubov Incompatibility (`γ = ω² sin²θ`).
  (e) Exact 4D Fermionic Hawking-Pair Firewall–Entropy Identity (`Tr(H_A ρ_B(∞)) / (2 ω) = S_L(ρ_R)`).
-/

open scoped Matrix BigOperators ComplexConjugate

namespace OSTQD

variable {d : ℕ}

lemma gkslOne_scalar (c : ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    gkslOne (c • (1 : Matrix (Fin d) (Fin d) ℂ)) ρ = 0 := by
  unfold gkslOne
  have h1 : (c • (1 : Matrix (Fin d) (Fin d) ℂ))ᴴ = star c • (1 : Matrix (Fin d) (Fin d) ℂ) := by
    simp
  rw [h1]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
  have hc : c * star c = star c * c := mul_comm _ _
  rw [hc, ← smul_add, ← two_smul ℂ ρ, smul_smul, smul_smul]
  have h2 : (2⁻¹ : ℂ) * (star c * c) * 2 = star c * c := by ring
  rw [h2, sub_self]

/-- **Theorem 2(a)** (Observer-Separation Necessity / No-Go for Universal Actualization):
If `{H_A, H_B}' = ℂ·1`, then any universal GKSL generator that is BPS-immune for both
`H_A` and `H_B` vanishes identically (`L(ρ) = 0` for all `ρ`). -/
theorem universal_actualization_nogo (Ls : List (Matrix (Fin d) (Fin d) ℂ))
    {HA HB : Matrix (Fin d) (Fin d) ℂ} (hHA : HAᴴ = HA) (hHB : HBᴴ = HB)
    (hirr : ∀ X : Matrix (Fin d) (Fin d) ℂ,
      comm X HA = 0 → comm X HB = 0 → ∃ c : ℂ, X = c • (1 : Matrix (Fin d) (Fin d) ℂ))
    (hbA : gkslDual Ls HA = 0 ∧ gkslDual Ls (HA * HA) = 0)
    (hbB : gkslDual Ls HB = 0 ∧ gkslDual Ls (HB * HB) = 0)
    (ρ : Matrix (Fin d) (Fin d) ℂ) :
    gksl Ls ρ = 0 := by
  have hcA := (bps_immunity_iff_comm Ls hHA).mp hbA
  have hcB := (bps_immunity_iff_comm Ls hHB).mp hbB
  unfold gksl
  have hmap : Ls.map (fun L => gkslOne L ρ) =
      Ls.map (fun _ => (0 : Matrix (Fin d) (Fin d) ℂ)) := by
    refine List.map_congr_left fun L hL => ?_
    rcases hirr L (hcA L hL) (hcB L hL) with ⟨c, rfl⟩
    exact gkslOne_scalar c ρ
  rw [hmap]
  induction Ls with
  | nil => simp
  | cons _ rest ih => simp

/-- Traceless part `L̃ = L - (Tr(L)/d)·1`. -/
noncomputable def tracelessPart (L : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  L - (L.trace / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)

lemma trace_tracelessPart (hd : 0 < d) (L : Matrix (Fin d) (Fin d) ℂ) :
    (tracelessPart L).trace = 0 := by
  unfold tracelessPart
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  simp [smul_eq_mul, div_mul_cancel₀ _ hd0]

lemma comm_tracelessPart (L H : Matrix (Fin d) (Fin d) ℂ) :
    comm (tracelessPart L) H = comm L H := by
  unfold tracelessPart comm
  simp [Matrix.sub_mul, Matrix.mul_sub]

/-- **Theorem 2(b)** (Quantitative Horizon-Heating Lower Bound):
Any `H_B`-BPS-immune generator `L_B` injects energy variance into `H_A` bounded below
by the observer-generator incompatibility `γ` times the total traceless jump strength. -/
theorem quantitative_horizon_heating_bound (hd : 0 < d)
    (Ls : List (Matrix (Fin d) (Fin d) ℂ))
    {HA HB : Matrix (Fin d) (Fin d) ℂ} (hHA : HAᴴ = HA) (hHB : HBᴴ = HB)
    (hbB : gkslDual Ls HB = 0 ∧ gkslDual Ls (HB * HB) = 0)
    (γ : ℝ)
    (hγ : ∀ X : Matrix (Fin d) (Fin d) ℂ,
      X.trace = 0 → comm X HB = 0 → γ * frobNormSq X ≤ frobNormSq (comm X HA)) :
    γ * (Ls.map (fun L => frobNormSq (tracelessPart L))).sum ≤
      ((carreDuChamp Ls HA).trace).re := by
  have hcB := (bps_immunity_iff_comm Ls hHB).mp hbB
  rw [carre_du_champ_eq_sum_comm_sq Ls hHA, trace_list_sum, re_list_sum]
  have hmap : ((Ls.map fun L => (comm L HA)ᴴ * comm L HA).map Matrix.trace).map Complex.re =
      Ls.map (fun L => frobNormSq (comm L HA)) := by
    simp only [List.map_map]
    exact List.map_congr_left fun L _ => trace_conjTranspose_mul_self_re (comm L HA)
  rw [hmap]
  clear hmap
  induction Ls with
  | nil => simp
  | cons L rest ih =>
    simp only [List.map_cons, List.sum_cons, mul_add]
    have hL_comm : comm (tracelessPart L) HB = 0 := by
      rw [comm_tracelessPart]; exact hcB L (List.mem_cons_self ..)
    have hL_bound : γ * frobNormSq (tracelessPart L) ≤ frobNormSq (comm L HA) := by
      have := hγ (tracelessPart L) (trace_tracelessPart hd L) hL_comm
      rwa [comm_tracelessPart] at this
    have hrest_comm : ∀ L' ∈ rest, comm L' HB = 0 :=
      fun L' h' => hcB L' (List.mem_cons_of_mem _ h')
    have hrest_hb : gkslDual rest HB = 0 ∧ gkslDual rest (HB * HB) = 0 :=
      (bps_immunity_iff_comm rest hHB).mpr hrest_comm
    exact add_le_add hL_bound (ih hrest_hb hrest_comm)

/-- **Theorem 2(c)** (Static Weak-Field Gravitational Redshift Invariance):
If `H_B = α H_A` (`α ≠ 0`), then `[X, H_B] = 0 ↔ [X, H_A] = 0`, so static gravitational
redshift creates zero observer-separation conflict (`γ = 0`). -/
theorem static_redshift_zero_conflict {HA : Matrix (Fin d) (Fin d) ℂ}
    {α : ℝ} (hα : α ≠ 0) (X : Matrix (Fin d) (Fin d) ℂ) :
    comm X ((α : ℂ) • HA) = 0 ↔ comm X HA = 0 := by
  have hαc : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα
  unfold comm
  rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub]
  exact smul_eq_zero_iff_right hαc

/-- **Theorem 2(d)** (Exact Two-Level Bogoliubov Incompatibility):
On `ℂ²` with `H_B = (ω/2) σ_z` and `H_A = (ω/2)(cos θ σ_z + sin θ σ_x)` (`ω ≠ 0`),
every traceless matrix `X` commuting with `H_B` satisfies
`‖[X, H_A]‖_F² = (ω² sin²θ) ‖X‖_F²` identically. -/
theorem two_level_bogoliubov_incompatibility (ω θ : ℝ) (hω : ω ≠ 0)
    (X : Matrix (Fin 2) (Fin 2) ℂ)
    (htr : X.trace = 0)
    (hcomm : comm X (!![(ω / 2 : ℂ), 0; 0, -(ω / 2 : ℂ)]) = 0) :
    frobNormSq (comm X (!![(ω / 2 * Real.cos θ : ℂ), (ω / 2 * Real.sin θ : ℂ);
                           (ω / 2 * Real.sin θ : ℂ), -(ω / 2 * Real.cos θ : ℂ)]))
      = (ω ^ 2 * (Real.sin θ) ^ 2) * frobNormSq X := by
  have hωc : (ω : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hω
  have h01 : X 0 1 = 0 := by
    have h := congrFun (congrFun hcomm 0) 1
    simp only [comm, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.zero_apply] at h
    have h' : -(X 0 1 * (ω : ℂ)) = 0 := by linear_combination h
    exact (mul_eq_zero.mp (neg_eq_zero.mp h')).resolve_right hωc
  have h10 : X 1 0 = 0 := by
    have h := congrFun (congrFun hcomm 1) 0
    simp only [comm, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.zero_apply] at h
    have h' : X 1 0 * (ω : ℂ) = 0 := by linear_combination h
    exact (mul_eq_zero.mp h').resolve_right hωc
  have h11 : X 1 1 = -X 0 0 := by
    simp [Matrix.trace, Fin.sum_univ_two] at htr
    exact eq_neg_of_add_eq_zero_right htr
  unfold frobNormSq comm
  simp only [Fin.sum_univ_two, Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, h01, h10, h11]
  simp only [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, Complex.zero_im,
    Complex.div_ofNat_re, Complex.div_ofNat_im]
  ring

/-!
### Theorem 2(e): Exact 4D Fermionic Hawking-Pair Firewall–Entropy Identity

Basis of `ℂ⁴` in `(R, L)` exterior/interior occupation numbers:
`0 ↦ |00⟩`, `1 ↦ |01⟩`, `2 ↦ |10⟩`, `3 ↦ |11⟩`.
- Exterior number operator: `N_R = diag(0, 0, 1, 1)`.
- Killing boost Hamiltonian: `H_B = ω · diag(0, -1, 1, 0)`.
- Inertial Hamiltonian `H_A = ω (a_1† a_1 + a_2† a_2)` at Bogoliubov angle `r`
  (`tan r = exp(-ω / (2 T_H))`, `sin² r = n_FD`):
  on the `{|00⟩, |11⟩}` pair subspace it is
  `2ω [[sin² r, -sin r cos r], [-sin r cos r, cos² r]]`, and on `{|01⟩, |10⟩}` it is `ω · I₂`.
- Inertial vacuum `|0_A⟩ = cos r |00⟩ + sin r |11⟩`, so `ρ_0 = |0_A⟩⟨0_A|`.
- Under `B`'s Killing-conserving actualization `L_B(ρ) = -(Γ/2)[N_R, [N_R, ρ]]`,
  the exact trajectory at auxiliary time `s ≥ 0` is `ρ_B(s)` with off-diagonal factor `e^{-Γ s / 2}`,
  converging as `s → ∞` to `ρ_B(∞) = diag(cos² r, 0, 0, sin² r)`.
-/

noncomputable def fermNR : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![0, 0, 1, 1]

noncomputable def fermHB (ω : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![0, -(ω : ℂ), (ω : ℂ), 0]

noncomputable def fermHA (ω r : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let c : ℂ := Real.cos r
  let s : ℂ := Real.sin r
  !![(2 * (ω : ℂ) * s ^ 2), 0, 0, -(2 * (ω : ℂ) * s * c);
     0, (ω : ℂ), 0, 0;
     0, 0, (ω : ℂ), 0;
     -(2 * (ω : ℂ) * s * c), 0, 0, (2 * (ω : ℂ) * c ^ 2)]

noncomputable def fermRhoB (r Γ s : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let c : ℂ := Real.cos r
  let sn : ℂ := Real.sin r
  let d : ℂ := Real.exp (-(Γ * s) / 2)
  !![c ^ 2, 0, 0, d * sn * c;
     0, 0, 0, 0;
     0, 0, 0, 0;
     d * sn * c, 0, 0, sn ^ 2]

noncomputable def fermRhoInf (r : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let c : ℂ := Real.cos r
  let sn : ℂ := Real.sin r
  Matrix.diagonal ![c ^ 2, 0, 0, sn ^ 2]

noncomputable def fermRhoR (r : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let c : ℂ := Real.cos r
  let sn : ℂ := Real.sin r
  Matrix.diagonal ![c ^ 2, sn ^ 2]

lemma fermHB_hermitian (ω : ℝ) : (fermHB ω)ᴴ = fermHB ω := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fermHB]

lemma fermNR_comm_fermHB (ω : ℝ) : comm fermNR (fermHB ω) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [comm, fermNR, fermHB]

/-- **Theorem 2(e.1)**: Observer `B`'s exterior-number actualization `[√Γ • N_R]` is
strictly BPS-immune for `B`'s Killing Hamiltonian `H_B` (zero energy drift and zero variance drift). -/
theorem fermionic_hawking_HB_bps_immune (ω Γ : ℝ) :
    gkslDual [(Real.sqrt Γ : ℂ) • fermNR] (fermHB ω) = 0 ∧
    gkslDual [(Real.sqrt Γ : ℂ) • fermNR] (fermHB ω * fermHB ω) = 0 := by
  rw [bps_immunity_iff_comm _ (fermHB_hermitian ω)]
  intro L hL
  simp only [List.mem_singleton] at hL
  rw [hL]
  unfold comm
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
  change (Real.sqrt Γ : ℂ) • comm fermNR (fermHB ω) = 0
  rw [fermNR_comm_fermHB, smul_zero]

/-- **Theorem 2(e.2)**: Exact injected inertial energy at arbitrary auxiliary time `s ≥ 0`:
`Tr(H_A ρ_B(s)) = 4 ω sin²(r) cos²(r) (1 - exp(-Γ s / 2))`. -/
theorem fermionic_hawking_energy_at_s (ω r Γ s : ℝ) :
    ((fermHA ω r * fermRhoB r Γ s).trace).re =
      4 * ω * (Real.sin r) ^ 2 * (Real.cos r) ^ 2 * (1 - Real.exp (-(Γ * s) / 2)) := by
  unfold fermHA fermRhoB
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_four,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.isValue, Matrix.cons_val]
  norm_cast
  ring

/-- **Theorem 2(e.3)**: Exact Firewall–Entropy Identity in the actualized limit `s → ∞`:
`Tr(H_A ρ_B(∞)) = 2 ω · ‖ρ_0 - ρ_B(∞)‖_F²` AND `‖ρ_0 - ρ_B(∞)‖_F² = 1 - Tr(ρ_R²) = S_L(ρ_R)`. -/
theorem fermionic_hawking_firewall_entropy_identity (ω r : ℝ) :
    ((fermHA ω r * fermRhoInf r).trace).re =
      2 * ω * frobNormSq (fermRhoB r 0 0 - fermRhoInf r) ∧
    frobNormSq (fermRhoB r 0 0 - fermRhoInf r) =
      1 - ((fermRhoR r * fermRhoR r).trace).re := by
  have htrig : (Real.cos r) ^ 2 + (Real.sin r) ^ 2 = 1 := by
    rw [add_comm]; exact Real.sin_sq_add_cos_sq r
  have h_coh : frobNormSq (fermRhoB r 0 0 - fermRhoInf r) =
      2 * (Real.sin r) ^ 2 * (Real.cos r) ^ 2 := by
    unfold frobNormSq fermRhoB fermRhoInf
    simp [-Complex.ofReal_sin, -Complex.ofReal_cos, Fin.sum_univ_four, Complex.normSq_apply]
    ring
  have h_E : ((fermHA ω r * fermRhoInf r).trace).re =
      4 * ω * (Real.sin r) ^ 2 * (Real.cos r) ^ 2 := by
    unfold fermHA fermRhoInf
    simp [-Complex.ofReal_sin, -Complex.ofReal_cos, ← Complex.ofReal_pow,
      Matrix.trace, Matrix.vecMul, dotProduct, Fin.sum_univ_four]
    ring
  have h_SL : 1 - ((fermRhoR r * fermRhoR r).trace).re =
      2 * (Real.sin r) ^ 2 * (Real.cos r) ^ 2 := by
    unfold fermRhoR
    simp [-Complex.ofReal_sin, -Complex.ofReal_cos, ← Complex.ofReal_pow,
      Matrix.trace, Fin.sum_univ_two]
    nlinarith [htrig]
  rw [h_coh, h_E, h_SL]
  exact ⟨by ring, rfl⟩

/-!
### Theorem 2 (v2 Upgrades): Subalgebra-Restricted No-Go, Two-Sided Commutativity,
Exact Exterior-Local Incompatibility `γ_loc = 8 ω² n_FD (1 - n_FD)`, and Exact GKSL ODE
-/

/-- **Theorem 2(a')** (Subalgebra-Restricted No-Go for Simultaneous BPS Immunity):
If every jump operator lies in an accessible subalgebra predicate `inAlg` whose
intersection with `{H_A, H_B}'` is scalar (`inAlg X ∧ [X, H_A] = 0 ∧ [X, H_B] = 0 → X = c·1`),
then any GKSL generator with jumps in `inAlg` that is BPS-immune for both `H_A` and `H_B`
vanishes identically (`L(ρ) = 0`). -/
theorem local_actualization_nogo (inAlg : Matrix (Fin d) (Fin d) ℂ → Prop)
    (Ls : List (Matrix (Fin d) (Fin d) ℂ))
    (hLs_alg : ∀ L ∈ Ls, inAlg L)
    {HA HB : Matrix (Fin d) (Fin d) ℂ} (hHA : HAᴴ = HA) (hHB : HBᴴ = HB)
    (hirr : ∀ X : Matrix (Fin d) (Fin d) ℂ,
      inAlg X → comm X HA = 0 → comm X HB = 0 →
        ∃ c : ℂ, X = c • (1 : Matrix (Fin d) (Fin d) ℂ))
    (hbA : gkslDual Ls HA = 0 ∧ gkslDual Ls (HA * HA) = 0)
    (hbB : gkslDual Ls HB = 0 ∧ gkslDual Ls (HB * HB) = 0)
    (ρ : Matrix (Fin d) (Fin d) ℂ) :
    gksl Ls ρ = 0 := by
  have hcA := (bps_immunity_iff_comm Ls hHA).mp hbA
  have hcB := (bps_immunity_iff_comm Ls hHB).mp hbB
  unfold gksl
  have hmap : Ls.map (fun L => gkslOne L ρ) =
      Ls.map (fun _ => (0 : Matrix (Fin d) (Fin d) ℂ)) := by
    refine List.map_congr_left fun L hL => ?_
    rcases hirr L (hLs_alg L hL) (hcA L hL) (hcB L hL) with ⟨c, rfl⟩
    exact gkslOne_scalar c ρ
  rw [hmap]
  induction Ls with
  | nil => simp
  | cons _ rest ih => simp

/-- **Theorem 2(b')** (Subalgebra-Restricted Quantitative Dissipation Bound):
For any `H_B`-BPS-immune generator `Ls` whose jump operators belong to an accessible
unital subalgebra `inAlg` (closed under taking traceless parts), the dissipation-form
trace `Re Tr(Γ_{L_B}(H_A, H_A))` (which equals the eigenbasis sum of initial variance
derivatives by Theorem 1(g)) is bounded below by `γ_loc * ∑_k ‖L̃_{B,k}‖_F²`. -/
theorem local_dissipation_bound (hd : 0 < d)
    (inAlg : Matrix (Fin d) (Fin d) ℂ → Prop)
    (hAlg_tl : ∀ L, inAlg L → inAlg (tracelessPart L))
    (Ls : List (Matrix (Fin d) (Fin d) ℂ))
    (hLs_alg : ∀ L ∈ Ls, inAlg L)
    {HA HB : Matrix (Fin d) (Fin d) ℂ} (hHA : HAᴴ = HA) (hHB : HBᴴ = HB)
    (hbB : gkslDual Ls HB = 0 ∧ gkslDual Ls (HB * HB) = 0)
    (γ : ℝ)
    (hγ : ∀ X : Matrix (Fin d) (Fin d) ℂ,
      inAlg X → X.trace = 0 → comm X HB = 0 → γ * frobNormSq X ≤ frobNormSq (comm X HA)) :
    γ * (Ls.map (fun L => frobNormSq (tracelessPart L))).sum ≤
      ((carreDuChamp Ls HA).trace).re := by
  have hcB := (bps_immunity_iff_comm Ls hHB).mp hbB
  rw [carre_du_champ_eq_sum_comm_sq Ls hHA, trace_list_sum, re_list_sum]
  have hmap : ((Ls.map fun L => (comm L HA)ᴴ * comm L HA).map Matrix.trace).map Complex.re =
      Ls.map (fun L => frobNormSq (comm L HA)) := by
    simp only [List.map_map]
    exact List.map_congr_left fun L _ => trace_conjTranspose_mul_self_re (comm L HA)
  rw [hmap]
  clear hmap
  induction Ls with
  | nil => simp
  | cons L rest ih =>
    simp only [List.map_cons, List.sum_cons, mul_add]
    have hL_alg : inAlg (tracelessPart L) := hAlg_tl L (hLs_alg L (List.mem_cons_self ..))
    have hL_comm : comm (tracelessPart L) HB = 0 := by
      rw [comm_tracelessPart]; exact hcB L (List.mem_cons_self ..)
    have hL_bound : γ * frobNormSq (tracelessPart L) ≤ frobNormSq (comm L HA) := by
      have := hγ (tracelessPart L) hL_alg (trace_tracelessPart hd L) hL_comm
      rwa [comm_tracelessPart] at this
    have hrest_alg : ∀ L' ∈ rest, inAlg L' := fun L' h' => hLs_alg L' (List.mem_cons_of_mem _ h')
    have hrest_comm : ∀ L' ∈ rest, comm L' HB = 0 :=
      fun L' h' => hcB L' (List.mem_cons_of_mem _ h')
    have hrest_hb : gkslDual rest HB = 0 ∧ gkslDual rest (HB * HB) = 0 :=
      (bps_immunity_iff_comm rest hHB).mpr hrest_comm
    exact add_le_add hL_bound (ih hrest_alg hrest_hb hrest_comm)

/-- **Two-Sided Commutativity Fact**: On the full 4D two-sided Hawking-pair algebra
`M_4(ℂ)`, the inertial Hamiltonian `H_A` and Killing boost `H_B = ω (N_R - N_L)`
COMMUTE identically (`[H_A, H_B] = 0`). Thus full-algebra irreducibility fails, and
horizon-forced separation arises specifically from causal restriction to the exterior
local subalgebra `A_B = M_2(ℂ)_R ⊗ I_L`. -/
theorem fermionic_hawking_HA_comm_HB (ω r : ℝ) :
    comm (fermHA ω r) (fermHB ω) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [comm, fermHA, fermHB, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four]

/-- Exterior-local subalgebra `A_B = M_2(ℂ)_R ⊗ I_L ⊂ M_4(ℂ)` in the basis
`{|00⟩, |01⟩, |10⟩, |11⟩}`. -/
def isExteriorLocal (X : Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∃ a b c d : ℂ, X = !![a, 0, b, 0; 0, a, 0, b; c, 0, d, 0; 0, c, 0, d]

lemma isExteriorLocal_fermNR : isExteriorLocal fermNR := by
  refine ⟨0, 0, 0, 1, ?_⟩
  ext i j; fin_cases i <;> fin_cases j <;> simp [fermNR]

lemma isExteriorLocal_tracelessPart {X : Matrix (Fin 4) (Fin 4) ℂ}
    (hX : isExteriorLocal X) : isExteriorLocal (tracelessPart X) := by
  rcases hX with ⟨a, b, c, d, rfl⟩
  set t := (!![a, 0, b, 0; 0, a, 0, b; c, 0, d, 0; 0, c, 0, d] : Matrix (Fin 4) (Fin 4) ℂ).trace /
      (4 : ℂ)
  refine ⟨a - t, b, c, d - t, ?_⟩
  ext i j; fin_cases i <;> fin_cases j <;> simp [tracelessPart, t]

/-- **Theorem 2(e.0)** (Exact Exterior-Local Incompatibility on the 4D Fermionic Hawking Pair):
For every `ω ≠ 0` and Bogoliubov angle `r`, every traceless exterior-local operator
`X ∈ M_2(ℂ)_R ⊗ I_L` commuting with `H_B` satisfies
`‖[X, H_A]‖_F² = (8 ω² sin² r cos² r) ‖X‖_F² = 8 ω² n_FD (1 - n_FD) ‖X‖_F²` identically. -/
theorem fermionic_hawking_local_incompatibility (ω r : ℝ) (hω : ω ≠ 0)
    (X : Matrix (Fin 4) (Fin 4) ℂ)
    (hloc : isExteriorLocal X) (htr : X.trace = 0)
    (hcomm : comm X (fermHB ω) = 0) :
    frobNormSq (comm X (fermHA ω r)) =
      (8 * ω ^ 2 * (Real.sin r) ^ 2 * (Real.cos r) ^ 2) * frobNormSq X := by
  rcases hloc with ⟨a, b, c, d, rfl⟩
  have hωc : (ω : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hω
  have hb0 : b = 0 := by
    have h := congrFun (congrFun hcomm 0) 2
    simp [comm, fermHB, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four] at h
    exact h.resolve_right hω
  have hc0 : c = 0 := by
    have h := congrFun (congrFun hcomm 2) 0
    simp [comm, fermHB, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four] at h
    exact h.resolve_left hω
  have hd_eq : d = -a := by
    simp [Matrix.trace, Fin.sum_univ_four] at htr
    have h2 : (2 : ℂ) * (a + d) = 0 := by linear_combination htr
    have hsum : a + d = 0 := (mul_eq_zero.mp h2).resolve_left (by norm_num)
    exact eq_neg_of_add_eq_zero_right hsum
  subst hb0; subst hc0; subst hd_eq
  unfold frobNormSq comm fermHA
  simp [-Complex.ofReal_sin, -Complex.ofReal_cos, ← Complex.ofReal_pow,
    Fin.sum_univ_four, Complex.normSq_apply]
  ring

/-- **Theorem 2(e.0b)** (Exterior-Local Irreducibility for `T_H > 0`):
Whenever `ω ≠ 0`, `sin r ≠ 0`, and `cos r ≠ 0` (i.e., `0 < T_H < ∞` with `0 < r < π/2`),
any exterior-local operator commuting with both `H_A` and `H_B` is a scalar multiple of `1`. -/
theorem fermionic_hawking_local_nogo (ω r : ℝ)
    (hω : ω ≠ 0) (hsin : Real.sin r ≠ 0) (hcos : Real.cos r ≠ 0)
    (X : Matrix (Fin 4) (Fin 4) ℂ)
    (hloc : isExteriorLocal X)
    (hcA : comm X (fermHA ω r) = 0) (hcB : comm X (fermHB ω) = 0) :
    ∃ c : ℂ, X = c • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have htl_loc : isExteriorLocal (tracelessPart X) := isExteriorLocal_tracelessPart hloc
  have htl_tr : (tracelessPart X).trace = 0 := trace_tracelessPart (by norm_num) X
  have htl_cB : comm (tracelessPart X) (fermHB ω) = 0 := by
    rw [comm_tracelessPart]; exact hcB
  have htl_cA : comm (tracelessPart X) (fermHA ω r) = 0 := by
    rw [comm_tracelessPart]; exact hcA
  have hnorm := fermionic_hawking_local_incompatibility ω r hω (tracelessPart X)
    htl_loc htl_tr htl_cB
  rw [htl_cA] at hnorm
  have h0 : frobNormSq (0 : Matrix (Fin 4) (Fin 4) ℂ) = 0 := by simp [frobNormSq]
  rw [h0] at hnorm
  have hcoef : 8 * ω ^ 2 * (Real.sin r) ^ 2 * (Real.cos r) ^ 2 ≠ 0 := by positivity
  have htl_zero_norm : frobNormSq (tracelessPart X) = 0 :=
    (mul_eq_zero.mp hnorm.symm).resolve_left hcoef
  have htl_zero : tracelessPart X = 0 := (frobNormSq_eq_zero_iff _).mp htl_zero_norm
  refine ⟨X.trace / (4 : ℂ), ?_⟩
  unfold tracelessPart at htl_zero
  exact sub_eq_zero.mp htl_zero

/-- **Theorem 2(e.4)** (Exact GKSL Differential Equation Verification for `fermRhoB`):
For all `r, s : ℝ` and `Γ ≥ 0`, every matrix entry of `fermRhoB r Γ s` has exact
auxiliary-time derivative equal to the corresponding entry of
`gksl [(√Γ : ℂ) • fermNR] (fermRhoB r Γ s)`. -/
theorem fermionic_hawking_ode (r Γ s : ℝ) (hΓ : 0 ≤ Γ) (i j : Fin 4) :
    HasDerivAt (fun τ : ℝ => fermRhoB r Γ τ i j)
      (gksl [(Real.sqrt Γ : ℂ) • fermNR] (fermRhoB r Γ s) i j) s := by
  have hgksl_val :
      gksl [(Real.sqrt Γ : ℂ) • fermNR] (fermRhoB r Γ s) i j =
      (!![0, 0, 0, -((Γ : ℂ) / 2) * (Real.exp (-(Γ * s) / 2) : ℂ) * (Real.sin r : ℂ) * (Real.cos r : ℂ);
          0, 0, 0, 0;
          0, 0, 0, 0;
          -((Γ : ℂ) / 2) * (Real.exp (-(Γ * s) / 2) : ℂ) * (Real.sin r : ℂ) * (Real.cos r : ℂ), 0, 0, 0] :
        Matrix (Fin 4) (Fin 4) ℂ) i j := by
    unfold gksl gkslOne fermNR fermRhoB
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four,
        -Complex.ofReal_sin, -Complex.ofReal_cos, -Complex.ofReal_exp] <;>
      ring_nf <;>
      simp only [← Complex.ofReal_pow, Real.sq_sqrt hΓ] <;>
      ring
  rw [hgksl_val]
  have hexp : HasDerivAt (fun τ : ℝ => (Real.exp (-(Γ * τ) / 2) : ℂ))
      ((-(Γ / 2 : ℝ) * Real.exp (-(Γ * s) / 2) : ℝ) : ℂ) s := by
    have hlin : HasDerivAt (fun τ : ℝ => -(Γ * τ) / 2) (-(Γ / 2)) s := by
      have h1 : HasDerivAt (fun τ : ℝ => τ) 1 s := hasDerivAt_id s
      have h2 := h1.const_mul (-(Γ / 2))
      convert h2 using 1
      · funext τ; ring
      · ring
    have hre : HasDerivAt (fun τ : ℝ => Real.exp (-(Γ * τ) / 2))
        (Real.exp (-(Γ * s) / 2) * (-(Γ / 2))) s := hlin.exp
    have hre' : HasDerivAt (fun τ : ℝ => Real.exp (-(Γ * τ) / 2))
        (-(Γ / 2) * Real.exp (-(Γ * s) / 2)) s := by
      convert hre using 1; ring
    exact hre'.ofReal_comp
  fin_cases i <;> fin_cases j <;>
    (simp [fermRhoB, -Complex.ofReal_sin, -Complex.ofReal_cos, -Complex.ofReal_exp];
     first
     | exact hasDerivAt_const s _
     | (convert (hexp.mul_const (Real.sin r : ℂ)).mul_const (Real.cos r : ℂ) using 1;
        push_cast; ring))

end OSTQD
