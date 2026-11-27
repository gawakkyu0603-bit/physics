import OSTQD_SK.Theorem1_CovariantKMS
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# OSTQD_SK.Theorem4_NonIsometricThroat

Theorem 4 of Paper 2:
  (a) KMS Absorption–Emission Locking No-Go for Mid-Evaporation `N_in = 0`:
      at any finite Hawking temperature `T_H = β⁻¹ > 0` (`ω > 0`), closing inward
      absorption (`ρ_spec = 0`) is strictly equivalent to zero Keldysh noise (`D_K = 0`),
      zero downward rate (`γ_↓ = 0`), and zero Hawking emission (`γ_↑ = 0`), forcing
      the thermal GKSL dissipator to vanish identically.
  (b) Finite-Factorization Exterior–Interior Algebra Separation:
      on any assumed bipartite factorization `Fin dR × Fin dL`, exterior-local operators
      `X_R ⊗ I_L` and interior-local operators `I_R ⊗ Y_L` commute identically and intersect
      only in scalar multiples of `1` (`A_B ∩ A_int = ℂ·1`).
  (c) Non-Isometric Encoding Kernel Obstruction (`d_fund < d_eff`):
      every linear map `V : ℂ^{d_eff} → ℂ^{d_fund}` with `d_fund < d_eff` possesses
      a non-zero null state `ψ ≠ 0` (`V ψ = 0`) and cannot be an isometry (`V† V ≠ 1`).
  (d) Complete-Erasure Channel Identity and Bound at `d_f = 1`:
      when a quantum channel factors through a one-dimensional intermediate space `M_1(ℂ)`,
      every CPTP encoder/decoder pair obeys the exact complete-erasure identity
      `F_e(R ∘ E) = 1 / d_C²` (and hence the cap `F_e(R ∘ E) ≤ 1 / d_C²`).
-/

open scoped Matrix BigOperators ComplexConjugate

namespace OSTQD_SK

/-- **Theorem 4(a)** (KMS Absorption–Emission Locking No-Go at `T_H > 0`, unit coupling / effective kernels):
At any `β > 0, ω > 0` and unit coupling (`g = 1`, equivalently for effective coupled kernels
`ρ_eff = g² ρ_spec`, `D_{K,eff} = g² D_K`; for bare bath kernels with coupling `g`, `g ≠ 0` is required),
zero inward absorption (`ρ_spec = 0`) is strictly equivalent to zero Keldysh noise
(`D_K = 0`), zero absorption rate (`γ_↓ = 0`), and zero Hawking emission (`γ_↑ = 0`),
which in turn forces `kmsPairGksl γ_↓ γ_↑ L ρ = 0` for all `L, ρ`. -/
theorem kms_inward_port_locking_nogo {d : ℕ} (β ω ρ_spec : ℝ) (hβ : 0 < β) (hω : 0 < ω)
    (L ρ : Matrix (Fin d) (Fin d) ℂ) :
    let e := Real.exp (β * ω)
    let D_K := ((e + 1) / (e - 1)) * ρ_spec
    let γ_down := (D_K + ρ_spec) / 2
    let γ_up := (D_K - ρ_spec) / 2
    (ρ_spec = 0 ↔ D_K = 0) ∧
    (ρ_spec = 0 ↔ γ_down = 0) ∧
    (ρ_spec = 0 ↔ γ_up = 0) ∧
    (ρ_spec = 0 → kmsPairGksl γ_down γ_up L ρ = 0) := by
  intro e D_K γ_down γ_up
  have hbw : 0 < β * ω := mul_pos hβ hω
  have he_gt : 1 < e := Real.one_lt_exp_iff.mpr hbw
  have he_sub_ne : e - 1 ≠ 0 := ne_of_gt (sub_pos.mpr he_gt)
  have he_pos : 0 < e := lt_trans zero_lt_one he_gt
  have he_ne : e ≠ 0 := ne_of_gt he_pos
  have he_add_ne : e + 1 ≠ 0 := by linarith
  have hgd : γ_down = (e / (e - 1)) * ρ_spec := by
    dsimp only [γ_down, D_K]; field_simp [he_sub_ne]; ring
  have hgu : γ_up = (1 / (e - 1)) * ρ_spec := by
    dsimp only [γ_up, D_K]; field_simp [he_sub_ne]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [D_K]
    constructor
    · intro h0; simp [h0]
    · intro h0; exact (mul_eq_zero.mp h0).resolve_left (div_ne_zero he_add_ne he_sub_ne)
  · rw [hgd]
    constructor
    · intro h0; simp [h0]
    · intro h0; exact (mul_eq_zero.mp h0).resolve_left (div_ne_zero he_ne he_sub_ne)
  · rw [hgu]
    constructor
    · intro h0; simp [h0]
    · intro h0; exact (mul_eq_zero.mp h0).resolve_left (div_ne_zero one_ne_zero he_sub_ne)
  · intro h0
    have hgd0 : γ_down = 0 := by rw [hgd, h0, mul_zero]
    have hgu0 : γ_up = 0 := by rw [hgu, h0, mul_zero]
    unfold kmsPairGksl
    rw [hgd0, hgu0]
    simp

/-- Exterior-local operator `X_R ⊗ I_L` on bipartite index type `Fin dR × Fin dL`. -/
def extOp {dR dL : ℕ} (X : Matrix (Fin dR) (Fin dR) ℂ) :
    Matrix (Fin dR × Fin dL) (Fin dR × Fin dL) ℂ :=
  Matrix.of fun p q => if p.2 = q.2 then X p.1 q.1 else 0

/-- Interior-local operator `I_R ⊗ Y_L` on bipartite index type `Fin dR × Fin dL`. -/
def intOp {dR dL : ℕ} (Y : Matrix (Fin dL) (Fin dL) ℂ) :
    Matrix (Fin dR × Fin dL) (Fin dR × Fin dL) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then Y p.2 q.2 else 0

/-- **Theorem 4(b)** (Exterior–Interior Algebraic Commutation and Trivial Intersection):
For any non-empty bipartite factorization (`0 < dR`, `0 < dL`):
  (1) Every exterior operator `X_R ⊗ I_L` commutes with every interior operator `I_R ⊗ Y_L`.
  (2) Any operator lying in both `A_B` and `A_int` (`extOp X = intOp Y`) is a scalar
      multiple of the identity (`A_B ∩ A_int = ℂ·1`). -/
theorem exterior_interior_algebra_separation {dR dL : ℕ} (hdR : 0 < dR) (hdL : 0 < dL)
    (X : Matrix (Fin dR) (Fin dR) ℂ) (Y : Matrix (Fin dL) (Fin dL) ℂ) :
    extOp (dL := dL) X * intOp (dR := dR) Y = intOp (dR := dR) Y * extOp (dL := dL) X ∧
    (extOp (dL := dL) X = intOp (dR := dR) Y →
      ∃ c : ℂ, extOp (dL := dL) X = c • (1 : Matrix (Fin dR × Fin dL) (Fin dR × Fin dL) ℂ)) := by
  constructor
  · ext p q
    simp only [Matrix.mul_apply, extOp, intOp, Matrix.of_apply, Fintype.sum_prod_type]
    have hL : ∑ r : Fin dR, ∑ l : Fin dL,
        (if p.2 = l then X p.1 r else 0) * (if r = q.1 then Y l q.2 else 0) =
        X p.1 q.1 * Y p.2 q.2 := by
      rw [Finset.sum_eq_single q.1]
      · rw [Finset.sum_eq_single p.2]
        · simp
        · intro l _ hlp; simp [Ne.symm hlp]
        · intro hp; exact (hp (Finset.mem_univ p.2)).elim
      · intro r _ hrq
        apply Finset.sum_eq_zero
        intro l _; simp [hrq]
      · intro hq; exact (hq (Finset.mem_univ q.1)).elim
    have hR : ∑ r : Fin dR, ∑ l : Fin dL,
        (if p.1 = r then Y p.2 l else 0) * (if l = q.2 then X r q.1 else 0) =
        Y p.2 q.2 * X p.1 q.1 := by
      rw [Finset.sum_eq_single p.1]
      · rw [Finset.sum_eq_single q.2]
        · simp
        · intro l _ hlq; simp [hlq]
        · intro hq; exact (hq (Finset.mem_univ q.2)).elim
      · intro r _ hrp
        apply Finset.sum_eq_zero
        intro l _; simp [Ne.symm hrp]
      · intro hp; exact (hp (Finset.mem_univ p.1)).elim
    rw [hL, hR, mul_comm]
  · intro heq
    let r0 : Fin dR := ⟨0, hdR⟩
    let l0 : Fin dL := ⟨0, hdL⟩
    refine ⟨X r0 r0, ?_⟩
    ext p q
    have hdiag : ∀ r : Fin dR, X r r = X r0 r0 := by
      intro r
      have h1 := congrFun (congrFun heq (r, l0)) (r, l0)
      have h2 := congrFun (congrFun heq (r0, l0)) (r0, l0)
      simp only [extOp, intOp, Matrix.of_apply, ↓reduceIte] at h1 h2
      rw [h1, ← h2]
    have hoff : ∀ r1 r2 : Fin dR, r1 ≠ r2 → X r1 r2 = 0 := by
      intro r1 r2 hne
      have h1 := congrFun (congrFun heq (r1, l0)) (r2, l0)
      simpa [extOp, intOp, hne] using h1
    simp only [extOp, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hpq : p = q
    · subst hpq
      simp [hdiag p.1]
    · by_cases h2 : p.2 = q.2
      · have h1 : p.1 ≠ q.1 := fun h => hpq (Prod.ext h h2)
        simp [hpq, h2, hoff p.1 q.1 h1]
      · simp [hpq, h2]

/-- **Theorem 4(c)** (Non-Isometric Encoding Kernel Obstruction):
Whenever the effective bulk Hilbert-space dimension exceeds the fundamental exterior
dimension (`d_fund < d_eff`), EVERY linear encoding `V : ℂ^{d_eff} → ℂ^{d_fund}` has a
non-trivial kernel (`∃ ψ ≠ 0, V *ᵥ ψ = 0`) and consequently cannot be isometric
(`V† V ≠ 1`). -/
theorem nonisometric_kernel_nontrivial {d_fund d_eff : ℕ} (hlt : d_fund < d_eff)
    (V : Matrix (Fin d_fund) (Fin d_eff) ℂ) :
    (∃ ψ : Fin d_eff → ℂ, ψ ≠ 0 ∧ V.mulVec ψ = 0) ∧
    Vᴴ * V ≠ 1 := by
  have hker : ∃ ψ : Fin d_eff → ℂ, ψ ≠ 0 ∧ V.mulVec ψ = 0 := by
    let f : (Fin d_eff → ℂ) →ₗ[ℂ] (Fin d_fund → ℂ) := Matrix.toLin' V
    have hfin : Module.finrank ℂ (Fin d_fund → ℂ) < Module.finrank ℂ (Fin d_eff → ℂ) := by
      simpa [Module.finrank_pi] using hlt
    have hnotinj : ¬ Function.Injective f := by
      intro hinj
      have hle := LinearMap.finrank_le_finrank_of_injective hinj
      omega
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff] at hnotinj
    push Not at hnotinj
    rcases hnotinj with ⟨ψ, hψ_ker, hψ_ne⟩
    refine ⟨ψ, hψ_ne, ?_⟩
    simpa [f, Matrix.toLin'_apply] using LinearMap.mem_ker.mp hψ_ker
  refine ⟨hker, ?_⟩
  intro hiso
  rcases hker with ⟨ψ, hψ_ne, hVψ⟩
  have h1 : (Vᴴ * V).mulVec ψ = 0 := by
    rw [← Matrix.mulVec_mulVec, hVψ, Matrix.mulVec_zero]
  rw [hiso, Matrix.one_mulVec] at h1
  exact hψ_ne h1

/-- **Theorem 4(d.1)** (Exact Complete-Erasure Identity at `d_f = 1`):
When a channel factors through a one-dimensional intermediate space `M_1(ℂ)`, every CPTP
encoder `Es : M_{dC} → M_1` and CPTP decoder `Rs : M_1 → M_{dC}` is a replacer channel
whose entanglement fidelity equals `1 / d_C²` identically (exact equality). -/
theorem throat_closure_complete_erasure_eq {dC : ℕ} (hdC : 0 < dC)
    (Es : List (Matrix (Fin 1) (Fin dC) ℂ))
    (Rs : List (Matrix (Fin dC) (Fin 1) ℂ))
    (hE_tp : (Es.map (fun E => Eᴴ * E)).sum = 1)
    (hR_tp : (Rs.map (fun R => Rᴴ * R)).sum = 1) :
    ((Rs.map (fun R => (Es.map (fun E => Complex.normSq (R * E).trace)).sum)).sum) /
      ((dC : ℝ) ^ 2) = 1 / ((dC : ℝ) ^ 2) := by
  have _ : 0 < dC := hdC
  have hsingleR : ∀ R : Matrix (Fin dC) (Fin 1) ℂ,
      (Es.map (fun E => Complex.normSq (R * E).trace)).sum = ((Rᴴ * R).trace).re := by
    intro R
    have htrE : ∀ E : Matrix (Fin 1) (Fin dC) ℂ,
        Complex.normSq (R * E).trace =
          (∑ i : Fin dC, ∑ j : Fin dC, star (R i 0) * (Eᴴ * E) i j * R j 0).re := by
      intro E
      have htr : (R * E).trace = ∑ j : Fin dC, E 0 j * R j 0 := by
        rw [Matrix.trace_mul_comm, Matrix.trace]
        simp [Matrix.mul_apply]
      have hquad : ∑ i : Fin dC, ∑ j : Fin dC, star (R i 0) * (Eᴴ * E) i j * R j 0 =
          star (∑ i : Fin dC, E 0 i * R i 0) * (∑ j : Fin dC, E 0 j * R j 0) := by
        rw [star_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.mul_apply, Fin.sum_univ_one, Matrix.conjTranspose_apply, star_mul]
        ring
      rw [htr, hquad, star_mul_self_re]
    have hsumE : (Es.map (fun E => Complex.normSq (R * E).trace)).sum =
        (∑ i : Fin dC, ∑ j : Fin dC,
          star (R i 0) * ((Es.map (fun E => Eᴴ * E)).sum i j) * R j 0).re := by
      have hmap : Es.map (fun E => Complex.normSq (R * E).trace) =
          Es.map (fun E => (∑ i : Fin dC, ∑ j : Fin dC, star (R i 0) * (Eᴴ * E) i j * R j 0).re) :=
        List.map_congr_left fun E _ => htrE E
      rw [hmap]
      clear hE_tp htrE hmap
      induction Es with
      | nil => simp
      | cons E rest ih =>
        simp only [List.map_cons, List.sum_cons, Matrix.add_apply, mul_add, add_mul,
          Finset.sum_add_distrib, Complex.add_re]
        rw [ih]
    rw [hsumE, hE_tp]
    have hlhs : ∑ i : Fin dC, ∑ j : Fin dC,
        star (R i 0) * (1 : Matrix (Fin dC) (Fin dC) ℂ) i j * R j 0 =
        ∑ i : Fin dC, star (R i 0) * R i 0 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji; simp [Matrix.one_apply_ne (Ne.symm hji)]
      · intro hi; exact (hi (Finset.mem_univ i)).elim
    rw [hlhs]
    simp [Matrix.trace, Matrix.mul_apply]
  have hsumR : (Rs.map (fun R =>
      (Es.map (fun E => Complex.normSq (R * E).trace)).sum)).sum =
      (((Rs.map (fun R => Rᴴ * R)).sum).trace).re := by
    have h1 : (Rs.map (fun R =>
        (Es.map (fun E => Complex.normSq (R * E).trace)).sum)).sum =
        (Rs.map (fun R => ((Rᴴ * R).trace).re)).sum := by
      clear hR_tp
      induction Rs with
      | nil => simp
      | cons R rest ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [hsingleR R, ih]
    have h2 : (Rs.map (fun R => ((Rᴴ * R).trace).re)).sum =
        (((Rs.map (fun R => Rᴴ * R)).sum).trace).re := by
      clear hR_tp h1
      induction Rs with
      | nil => simp
      | cons R rest ih =>
        simp only [List.map_cons, List.sum_cons, Matrix.trace_add, Complex.add_re]
        rw [ih]
    rw [h1, h2]
  rw [hR_tp, Matrix.trace_one, Fintype.card_fin] at hsumR
  have hnum : (Rs.map (fun R =>
      (Es.map (fun E => Complex.normSq (R * E).trace)).sum)).sum = 1 := by
    simpa using hsumR
  rw [hnum]

/-- **Theorem 4(d.2)** (Complete-Erasure Entanglement-Fidelity Cap at `d_f = 1`):
Immediate inequality corollary `F_e(R ∘ E) ≤ 1 / d_C²` from `throat_closure_complete_erasure_eq`. -/
theorem throat_closure_complete_erasure_bound {dC : ℕ} (hdC : 0 < dC)
    (Es : List (Matrix (Fin 1) (Fin dC) ℂ))
    (Rs : List (Matrix (Fin dC) (Fin 1) ℂ))
    (hE_tp : (Es.map (fun E => Eᴴ * E)).sum = 1)
    (hR_tp : (Rs.map (fun R => Rᴴ * R)).sum = 1) :
    ((Rs.map (fun R => (Es.map (fun E => Complex.normSq (R * E).trace)).sum)).sum) /
      ((dC : ℝ) ^ 2) ≤ 1 / ((dC : ℝ) ^ 2) :=
  le_of_eq (throat_closure_complete_erasure_eq hdC Es Rs hE_tp hR_tp)

end OSTQD_SK
