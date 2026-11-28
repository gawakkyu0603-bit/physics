import OSTQD_SK.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# OSTQD_SK.Theorem1_CovariantKMS

Theorem 1 and Proposition 1 (Fixed- and Slowly Varying-Temperature Backgrounds):
  (a) Covariant `(t, s)` Two-Time Integrability for Eigenoperator Jumps (`[H, L_k] = -ω_k L_k`):
      `[L, ad_H] = 0` holds EXACTLY on a fixed-`T_H` background even for thermal
      energy-exchanging jumps (`ω_k ≠ 0`) that break subsystem BPS immunity
      (conservation of both first and second energy moments, `Γ_L(H, H) ≠ 0`).
  (b) Exact Subsystem Energy-Flux Operator `L†(H) = -∑_k ω_k L_k† L_k` and
      Energy-Variance Carré du Champ `Γ_L(H, H) = ∑_k ω_k² L_k† L_k ⪰ 0`.
  (c) Exact Dynamical KMS Detailed-Balance Stationarity `L(ρ_β) = 0`.
  (d) Finite-`T_H` GNS-Weighted Monotonicity and Symmetric Intertwining (Fixed-`T_H`
      Thermal Generalization of the Parisi–Wu Arrow):
      (d.1) `L_pair(S X S) = S L_pair†(X) S` for `S = S†` obeying `a (L S) = b (S L)`,
            connecting non-commuting density matrices `ρ = S (B + 1) S` to Hermitian `B = B†`.
      (d.2) `-2 Re Tr(ρ_β A L†(A)) = ∑ (γ_↓ Tr(ρ_β [L, A]†[L, A]) + γ_↑ Tr(ρ_β [L†, A]†[L†, A])) ≥ 0`.
  (e) Non-Secular Two-Level `σ_x` Bloch–Redfield Complete-Positivity Obstruction:
      exact negative-curvature polynomial witness for the Kossakowski matrix whenever `γ_↓ ≠ γ_↑`.
  (f) Dirichlet-kernel criterion for free-subsystem two-time autocorrelations under QRT.
  (g) Uniform-contraction Gibbs tracking Gronwall–Duhamel envelope and exact two-level
      adiabatic Gibbs population drift derivative (Proposition 1).
-/

open scoped Matrix BigOperators ComplexConjugate

namespace OSTQD_SK

variable {d : ℕ}

lemma eigenop_conjTranspose {H L : Matrix (Fin d) (Fin d) ℂ} {ω : ℝ}
    (hH : Hᴴ = H) (heig : comm H L = -(ω : ℂ) • L) :
    comm H Lᴴ = (ω : ℂ) • Lᴴ := by
  have h1 : (H * L - L * H)ᴴ = (-(ω : ℂ) • L)ᴴ := congrArg Matrix.conjTranspose heig
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hH,
      Matrix.conjTranspose_smul, star_neg, Complex.star_def, Complex.conj_ofReal] at h1
  unfold comm
  calc H * Lᴴ - Lᴴ * H = -(Lᴴ * H - H * Lᴴ) := by abel
    _ = -(-(ω : ℂ) • Lᴴ) := by rw [h1]
    _ = (ω : ℂ) • Lᴴ := by simp

lemma eigenop_LdL_comm {H L : Matrix (Fin d) (Fin d) ℂ} {ω : ℝ}
    (hH : Hᴴ = H) (heig : comm H L = -(ω : ℂ) • L) :
    comm H (Lᴴ * L) = 0 := by
  have hL : H * L = L * H - (ω : ℂ) • L := by
    unfold comm at heig
    calc H * L = (H * L - L * H) + L * H := by abel
      _ = -(ω : ℂ) • L + L * H := by rw [heig]
      _ = L * H - (ω : ℂ) • L := by rw [neg_smul]; abel
  have hLd : H * Lᴴ = Lᴴ * H + (ω : ℂ) • Lᴴ := by
    have h := eigenop_conjTranspose hH heig
    unfold comm at h
    calc H * Lᴴ = (H * Lᴴ - Lᴴ * H) + Lᴴ * H := by abel
      _ = (ω : ℂ) • Lᴴ + Lᴴ * H := by rw [h]
      _ = Lᴴ * H + (ω : ℂ) • Lᴴ := by abel
  unfold comm
  calc H * (Lᴴ * L) - Lᴴ * L * H
      = (H * Lᴴ) * L - Lᴴ * (L * H) := by simp [Matrix.mul_assoc]
    _ = (Lᴴ * H + (ω : ℂ) • Lᴴ) * L - Lᴴ * (L * H) := by rw [hLd]
    _ = Lᴴ * (H * L) + (ω : ℂ) • (Lᴴ * L) - Lᴴ * (L * H) := by
        simp [Matrix.add_mul, Matrix.mul_assoc]
    _ = Lᴴ * (L * H - (ω : ℂ) • L) + (ω : ℂ) • (Lᴴ * L) - Lᴴ * (L * H) := by rw [hL]
    _ = 0 := by
        simp [Matrix.mul_sub]

lemma gkslOne_comm_of_eigenop {H L : Matrix (Fin d) (Fin d) ℂ} {ω : ℝ}
    (hH : Hᴴ = H) (heig : comm H L = -(ω : ℂ) • L) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    gkslOne L (comm H ρ) = comm H (gkslOne L ρ) := by
  have hLH : L * H = H * L + (ω : ℂ) • L := by
    unfold comm at heig
    calc L * H = H * L - (H * L - L * H) := by abel
      _ = H * L - (-(ω : ℂ) • L) := by rw [heig]
      _ = H * L + (ω : ℂ) • L := by simp
  have hHLd : H * Lᴴ = Lᴴ * H + (ω : ℂ) • Lᴴ := by
    have h := eigenop_conjTranspose hH heig
    unfold comm at h
    calc H * Lᴴ = (H * Lᴴ - Lᴴ * H) + Lᴴ * H := by abel
      _ = (ω : ℂ) • Lᴴ + Lᴴ * H := by rw [h]
      _ = Lᴴ * H + (ω : ℂ) • Lᴴ := by abel
  have hLdLH : H * (Lᴴ * L) = Lᴴ * L * H := sub_eq_zero.mp (eigenop_LdL_comm hH heig)
  unfold gkslOne comm
  have t1 : L * (H * ρ - ρ * H) * Lᴴ = H * (L * ρ * Lᴴ) - L * ρ * Lᴴ * H := by
    have a0 : L * (H * ρ) * Lᴴ = H * (L * ρ * Lᴴ) + (ω : ℂ) • (L * ρ * Lᴴ) := by
      calc L * (H * ρ) * Lᴴ = (L * H) * ρ * Lᴴ := by simp [Matrix.mul_assoc]
        _ = (H * L + (ω : ℂ) • L) * ρ * Lᴴ := by rw [hLH]
        _ = H * (L * ρ * Lᴴ) + (ω : ℂ) • (L * ρ * Lᴴ) := by
            simp [Matrix.add_mul, Matrix.mul_assoc]
    have b0 : L * (ρ * H) * Lᴴ = L * ρ * Lᴴ * H + (ω : ℂ) • (L * ρ * Lᴴ) := by
      calc L * (ρ * H) * Lᴴ = L * ρ * (H * Lᴴ) := by simp [Matrix.mul_assoc]
        _ = L * ρ * (Lᴴ * H + (ω : ℂ) • Lᴴ) := by rw [hHLd]
        _ = L * ρ * Lᴴ * H + (ω : ℂ) • (L * ρ * Lᴴ) := by
            simp [Matrix.mul_add, Matrix.mul_assoc]
    rw [Matrix.mul_sub, Matrix.sub_mul, a0, b0]
    abel
  have t2 : Lᴴ * L * (H * ρ - ρ * H) + (H * ρ - ρ * H) * (Lᴴ * L) =
      H * (Lᴴ * L * ρ + ρ * (Lᴴ * L)) - (Lᴴ * L * ρ + ρ * (Lᴴ * L)) * H := by
    have a1 : Lᴴ * L * (H * ρ) = H * (Lᴴ * L * ρ) := by
      rw [← Matrix.mul_assoc (Lᴴ * L) H ρ, ← hLdLH, Matrix.mul_assoc H (Lᴴ * L) ρ]
    have a2 : ρ * H * (Lᴴ * L) = ρ * (Lᴴ * L) * H := by
      rw [Matrix.mul_assoc ρ H (Lᴴ * L), hLdLH, ← Matrix.mul_assoc ρ (Lᴴ * L) H]
    have a3 : Lᴴ * L * (ρ * H) = Lᴴ * L * ρ * H := (Matrix.mul_assoc (Lᴴ * L) ρ H).symm
    have a4 : H * ρ * (Lᴴ * L) = H * (ρ * (Lᴴ * L)) := Matrix.mul_assoc H ρ (Lᴴ * L)
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, a1, a2, a3, a4]
    abel
  rw [t1, t2, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
  abel

/-- **Theorem 1(a)** (Covariant `(t, s)` Two-Time Integrability for Thermal Eigenoperator Jumps):
Whenever every jump operator `L_k` is an eigenoperator of `ad_H` (`[H, L_k] = -ω_k L_k` with
`ω_k ∈ ℝ`), the GKSL generator commutes identically with unitary `t`-evolution (`[L, ad_H] = 0`)
even when `ω_k ≠ 0` breaks second-moment subsystem BPS immunity (`Γ_L(H, H) ≠ 0`, even in cases
where upward and downward mean fluxes cancel in `L†(H)`). -/
theorem eigenoperator_two_time_commutation
    (Ls : List (Matrix (Fin d) (Fin d) ℂ × ℝ))
    {H : Matrix (Fin d) (Fin d) ℂ} (hH : Hᴴ = H)
    (heig : ∀ p ∈ Ls, comm H p.1 = -(p.2 : ℂ) • p.1)
    (ρ : Matrix (Fin d) (Fin d) ℂ) :
    gksl (Ls.map Prod.fst) (comm H ρ) = comm H (gksl (Ls.map Prod.fst) ρ) := by
  unfold gksl
  induction Ls with
  | nil => simp [comm]
  | cons p rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have hp := heig p (List.mem_cons_self ..)
    have hrest : ∀ q ∈ rest, comm H q.1 = -(q.2 : ℂ) • q.1 :=
      fun q hq => heig q (List.mem_cons_of_mem _ hq)
    rw [gkslOne_comm_of_eigenop hH hp ρ, ih hrest]
    unfold comm
    rw [Matrix.mul_add, Matrix.add_mul]
    abel

lemma gkslDualOne_eigenop_energy {H L : Matrix (Fin d) (Fin d) ℂ} {ω : ℝ}
    (hH : Hᴴ = H) (heig : comm H L = -(ω : ℂ) • L) :
    gkslDualOne L H = -(ω : ℂ) • (Lᴴ * L) := by
  have hHL : H * L = L * H - (ω : ℂ) • L := by
    unfold comm at heig
    calc H * L = (H * L - L * H) + L * H := by abel
      _ = -(ω : ℂ) • L + L * H := by rw [heig]
      _ = L * H - (ω : ℂ) • L := by rw [neg_smul]; abel
  have hLdLH : H * (Lᴴ * L) = Lᴴ * L * H := sub_eq_zero.mp (eigenop_LdL_comm hH heig)
  unfold gkslDualOne
  have t1 : Lᴴ * H * L = Lᴴ * L * H - (ω : ℂ) • (Lᴴ * L) := by
    calc Lᴴ * H * L = Lᴴ * (H * L) := by rw [Matrix.mul_assoc]
      _ = Lᴴ * (L * H - (ω : ℂ) • L) := by rw [hHL]
      _ = Lᴴ * L * H - (ω : ℂ) • (Lᴴ * L) := by simp [Matrix.mul_sub, Matrix.mul_assoc]
  rw [t1, hLdLH]
  have hhalf : (2⁻¹ : ℂ) • (Lᴴ * L * H + Lᴴ * L * H) = Lᴴ * L * H := by
    rw [smul_add, ← add_smul]; norm_num
  rw [hhalf, neg_smul]
  abel

/-- **Theorem 1(b.1)** (Exact Subsystem Energy-Flux Operator):
For eigenoperator jumps `[H, L_k] = -ω_k L_k`, the mean-energy drift operator equals
`L†(H) = -∑_k ω_k L_k† L_k` (individual opposite-sign terms may cancel in the sum, whereas
`Γ_L(H, H) = ∑_k ω_k² L_k† L_k` strictly breaks second-moment BPS immunity whenever any nonzero
jump has `ω_k ≠ 0`). -/
theorem eigenoperator_energy_drift
    (Ls : List (Matrix (Fin d) (Fin d) ℂ × ℝ))
    {H : Matrix (Fin d) (Fin d) ℂ} (hH : Hᴴ = H)
    (heig : ∀ p ∈ Ls, comm H p.1 = -(p.2 : ℂ) • p.1) :
    gkslDual (Ls.map Prod.fst) H =
      -(Ls.map (fun p => (p.2 : ℂ) • (p.1ᴴ * p.1))).sum := by
  unfold gkslDual
  induction Ls with
  | nil => simp
  | cons p rest ih =>
    simp only [List.map_cons, List.sum_cons, neg_add]
    have hp := heig p (List.mem_cons_self ..)
    have hrest : ∀ q ∈ rest, comm H q.1 = -(q.2 : ℂ) • q.1 :=
      fun q hq => heig q (List.mem_cons_of_mem _ hq)
    rw [gkslDualOne_eigenop_energy hH hp, ih hrest]
    simp

lemma carreDuChampOne_eq_comm_sq {L H : Matrix (Fin d) (Fin d) ℂ} (hH : Hᴴ = H) :
    carreDuChampOne L H = (comm L H)ᴴ * comm L H := by
  unfold carreDuChampOne gkslDualOne
  have hdag : (comm L H)ᴴ = H * Lᴴ - Lᴴ * H := by
    unfold comm
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hH]
  rw [hdag]
  unfold comm
  have hhalf : ∀ M : Matrix (Fin d) (Fin d) ℂ,
      (2⁻¹ : ℂ) • M + (2⁻¹ : ℂ) • M = M := fun M => by rw [← add_smul]; norm_num
  have h1 : (H * Lᴴ - Lᴴ * H) * (L * H - H * L) =
      H * Lᴴ * L * H - H * Lᴴ * H * L - Lᴴ * H * L * H + Lᴴ * H * H * L := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
    abel
  rw [h1]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_add, Matrix.add_mul, smul_add, Matrix.mul_assoc]
  have hcomb : (2⁻¹ : ℂ) • (H * (Lᴴ * (L * H))) + (2⁻¹ : ℂ) • (H * (Lᴴ * (L * H))) =
      H * (Lᴴ * (L * H)) := hhalf _
  calc Lᴴ * (H * (H * L)) - ((2⁻¹ : ℂ) • (Lᴴ * (L * (H * H))) + (2⁻¹ : ℂ) • (H * (H * (Lᴴ * L))))
        - (H * (Lᴴ * (H * L)) - ((2⁻¹ : ℂ) • (H * (Lᴴ * (L * H))) + (2⁻¹ : ℂ) • (H * (H * (Lᴴ * L)))))
        - (Lᴴ * (H * (L * H)) - ((2⁻¹ : ℂ) • (Lᴴ * (L * (H * H))) + (2⁻¹ : ℂ) • (H * (Lᴴ * (L * H)))))
      = ((2⁻¹ : ℂ) • (H * (Lᴴ * (L * H))) + (2⁻¹ : ℂ) • (H * (Lᴴ * (L * H))))
        - H * (Lᴴ * (H * L)) - Lᴴ * (H * (L * H)) + Lᴴ * (H * (H * L)) := by abel
    _ = H * (Lᴴ * (L * H)) - H * (Lᴴ * (H * L)) - Lᴴ * (H * (L * H)) + Lᴴ * (H * (H * L)) := by
        rw [hcomb]

/-- **Theorem 1(b.2)** (Exact Energy-Variance Carré du Champ for Eigenoperator Jumps):
`Γ_L(H, H) = ∑_k ω_k² L_k† L_k`. -/
theorem eigenoperator_carre_du_champ
    (Ls : List (Matrix (Fin d) (Fin d) ℂ × ℝ))
    {H : Matrix (Fin d) (Fin d) ℂ} (hH : Hᴴ = H)
    (heig : ∀ p ∈ Ls, comm H p.1 = -(p.2 : ℂ) • p.1) :
    carreDuChamp (Ls.map Prod.fst) H =
      (Ls.map (fun p => ((p.2 : ℂ) ^ 2) • (p.1ᴴ * p.1))).sum := by
  unfold carreDuChamp gkslDual
  induction Ls with
  | nil => simp
  | cons p rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have hp := heig p (List.mem_cons_self ..)
    have hrest : ∀ q ∈ rest, comm H q.1 = -(q.2 : ℂ) • q.1 :=
      fun q hq => heig q (List.mem_cons_of_mem _ hq)
    have hcomm_LH : comm p.1 H = (p.2 : ℂ) • p.1 := by
      unfold comm at hp ⊢
      calc p.1 * H - H * p.1 = -(H * p.1 - p.1 * H) := by abel
        _ = -(-(p.2 : ℂ) • p.1) := by rw [hp]
        _ = (p.2 : ℂ) • p.1 := by simp
    have hsingle : carreDuChampOne p.1 H = ((p.2 : ℂ) ^ 2) • (p.1ᴴ * p.1) := by
      rw [carreDuChampOne_eq_comm_sq hH, hcomm_LH, Matrix.conjTranspose_smul,
          Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, smul_smul, sq]
    rw [Matrix.mul_add, Matrix.add_mul]
    calc (gkslDualOne p.1 (H * H) + ((rest.map Prod.fst).map fun L => gkslDualOne L (H * H)).sum)
          - (H * gkslDualOne p.1 H + H * ((rest.map Prod.fst).map fun L => gkslDualOne L H).sum)
          - (gkslDualOne p.1 H * H + ((rest.map Prod.fst).map fun L => gkslDualOne L H).sum * H)
        = carreDuChampOne p.1 H
          + (((rest.map Prod.fst).map fun L => gkslDualOne L (H * H)).sum
             - H * ((rest.map Prod.fst).map fun L => gkslDualOne L H).sum
             - ((rest.map Prod.fst).map fun L => gkslDualOne L H).sum * H) := by
              unfold carreDuChampOne; abel
      _ = ((p.2 : ℂ) ^ 2) • (p.1ᴴ * p.1) +
            (rest.map fun q => ((q.2 : ℂ) ^ 2) • (q.1ᴴ * q.1)).sum := by
              rw [hsingle, ih hrest]

/-!
### Dynamical KMS Detailed Balance, Stationarity, and Finite-`T_H` GNS Monotonicity
-/

/-- Weighted conjugate-pair thermal GKSL generator
`γ_↓ L_L(ρ) + γ_↑ L_{L†}(ρ)`. -/
noncomputable def kmsPairGksl (γ_down γ_up : ℝ) (L ρ : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (γ_down : ℂ) • gkslOne L ρ + (γ_up : ℂ) • gkslOne Lᴴ ρ

/-- Dual weighted conjugate-pair thermal GKSL generator
`γ_↓ L_L†(A) + γ_↑ L_{L†}†(A)`. -/
noncomputable def kmsPairGkslDual (γ_down γ_up : ℝ) (L A : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (γ_down : ℂ) • gkslDualOne L A + (γ_up : ℂ) • gkslDualOne Lᴴ A

lemma kms_intertwine_adj {γ_down γ_up : ℝ} {L ρβ : Matrix (Fin d) (Fin d) ℂ}
    (hρβ : ρβᴴ = ρβ)
    (hKMS : (γ_down : ℂ) • (L * ρβ) = (γ_up : ℂ) • (ρβ * L)) :
    (γ_down : ℂ) • (ρβ * Lᴴ) = (γ_up : ℂ) • (Lᴴ * ρβ) := by
  have h := congrArg Matrix.conjTranspose hKMS
  simpa [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hρβ] using h

/-- **Theorem 1(c)** (Exact Dynamical KMS Stationarity of the Gibbs State):
Whenever the Hermitian Gibbs state `ρ_β` obeys the KMS intertwining relation
`γ_↓ (L ρ_β) = γ_↑ (ρ_β L)` (which holds for `ρ_β = Z⁻¹ e^{-β H}`, `[H, L] = -ω L`,
and `γ_↑ / γ_↓ = e^{-β ω}`), `ρ_β` is an exact stationary state:
`γ_↓ L_L(ρ_β) + γ_↑ L_{L†}(ρ_β) = 0`. -/
theorem kms_detailed_balance_stationarity {γ_down γ_up : ℝ}
    {L ρβ : Matrix (Fin d) (Fin d) ℂ} (hρβ : ρβᴴ = ρβ)
    (hKMS : (γ_down : ℂ) • (L * ρβ) = (γ_up : ℂ) • (ρβ * L)) :
    kmsPairGksl γ_down γ_up L ρβ = 0 := by
  have hKMS_adj := kms_intertwine_adj hρβ hKMS
  have t1a : (γ_down : ℂ) • (L * ρβ * Lᴴ) = (γ_up : ℂ) • (ρβ * (L * Lᴴ)) := by
    calc (γ_down : ℂ) • (L * ρβ * Lᴴ)
        = ((γ_down : ℂ) • (L * ρβ)) * Lᴴ := by rw [Matrix.smul_mul]
      _ = ((γ_up : ℂ) • (ρβ * L)) * Lᴴ := by rw [hKMS]
      _ = (γ_up : ℂ) • (ρβ * (L * Lᴴ)) := by rw [Matrix.smul_mul, Matrix.mul_assoc]
  have t1b : (γ_down : ℂ) • (L * ρβ * Lᴴ) = (γ_up : ℂ) • (L * Lᴴ * ρβ) := by
    calc (γ_down : ℂ) • (L * ρβ * Lᴴ)
        = L * ((γ_down : ℂ) • (ρβ * Lᴴ)) := by rw [Matrix.mul_assoc, Matrix.mul_smul]
      _ = L * ((γ_up : ℂ) • (Lᴴ * ρβ)) := by rw [hKMS_adj]
      _ = (γ_up : ℂ) • (L * Lᴴ * ρβ) := by rw [Matrix.mul_smul, Matrix.mul_assoc]
  have t2a : (γ_up : ℂ) • (Lᴴ * ρβ * L) = (γ_down : ℂ) • (ρβ * (Lᴴ * L)) := by
    calc (γ_up : ℂ) • (Lᴴ * ρβ * L)
        = ((γ_up : ℂ) • (Lᴴ * ρβ)) * L := by rw [Matrix.smul_mul]
      _ = ((γ_down : ℂ) • (ρβ * Lᴴ)) * L := by rw [← hKMS_adj]
      _ = (γ_down : ℂ) • (ρβ * (Lᴴ * L)) := by rw [Matrix.smul_mul, Matrix.mul_assoc]
  have t2b : (γ_up : ℂ) • (Lᴴ * ρβ * L) = (γ_down : ℂ) • (Lᴴ * L * ρβ) := by
    calc (γ_up : ℂ) • (Lᴴ * ρβ * L)
        = Lᴴ * ((γ_up : ℂ) • (ρβ * L)) := by rw [Matrix.mul_assoc, Matrix.mul_smul]
      _ = Lᴴ * ((γ_down : ℂ) • (L * ρβ)) := by rw [← hKMS]
      _ = (γ_down : ℂ) • (Lᴴ * L * ρβ) := by rw [Matrix.mul_smul, Matrix.mul_assoc]
  have hhalf : ∀ M : Matrix (Fin d) (Fin d) ℂ,
      (2⁻¹ : ℂ) • M + (2⁻¹ : ℂ) • M = M := fun M => by rw [← add_smul]; norm_num
  unfold kmsPairGksl gkslOne
  rw [Matrix.conjTranspose_conjTranspose]
  simp only [smul_sub, smul_add]
  have s1 : (γ_down : ℂ) • (2⁻¹ : ℂ) • (Lᴴ * L * ρβ) + (γ_down : ℂ) • (2⁻¹ : ℂ) • (ρβ * (Lᴴ * L)) =
      (γ_up : ℂ) • (Lᴴ * ρβ * L) := by
    rw [smul_comm (γ_down : ℂ) (2⁻¹ : ℂ), smul_comm (γ_down : ℂ) (2⁻¹ : ℂ), ← t2b, ← t2a, hhalf]
  have s2 : (γ_up : ℂ) • (2⁻¹ : ℂ) • (L * Lᴴ * ρβ) + (γ_up : ℂ) • (2⁻¹ : ℂ) • (ρβ * (L * Lᴴ)) =
      (γ_down : ℂ) • (L * ρβ * Lᴴ) := by
    rw [smul_comm (γ_up : ℂ) (2⁻¹ : ℂ), smul_comm (γ_up : ℂ) (2⁻¹ : ℂ), ← t1b, ← t1a, hhalf]
  calc (γ_down : ℂ) • (L * ρβ * Lᴴ)
        - ((γ_down : ℂ) • (2⁻¹ : ℂ) • (Lᴴ * L * ρβ) + (γ_down : ℂ) • (2⁻¹ : ℂ) • (ρβ * (Lᴴ * L)))
        + ((γ_up : ℂ) • (Lᴴ * ρβ * L)
        - ((γ_up : ℂ) • (2⁻¹ : ℂ) • (L * Lᴴ * ρβ) + (γ_up : ℂ) • (2⁻¹ : ℂ) • (ρβ * (L * Lᴴ))))
      = ((γ_down : ℂ) • (L * ρβ * Lᴴ) - (γ_up : ℂ) • (Lᴴ * ρβ * L))
        + ((γ_up : ℂ) • (Lᴴ * ρβ * L) - (γ_down : ℂ) • (L * ρβ * Lᴴ)) := by rw [s1, s2]
    _ = 0 := by abel

lemma kms_gns_identity {γ_down γ_up : ℝ} {L ρβ A : Matrix (Fin d) (Fin d) ℂ}
    (hρβ : ρβᴴ = ρβ) (hA : Aᴴ = A)
    (hKMS : (γ_down : ℂ) • (L * ρβ) = (γ_up : ℂ) • (ρβ * L)) :
    (-2 : ℂ) * (ρβ * A * kmsPairGkslDual γ_down γ_up L A).trace =
      (γ_down : ℂ) * (ρβ * (comm L A)ᴴ * comm L A).trace +
      (γ_up : ℂ) * (ρβ * (comm Lᴴ A)ᴴ * comm Lᴴ A).trace := by
  have hKMS_adj := kms_intertwine_adj hρβ hKMS
  have h1 : (γ_down : ℂ) * (ρβ * (Lᴴ * (A * (L * A)))).trace =
      (γ_up : ℂ) * (ρβ * (A * (L * (A * Lᴴ)))).trace := by
    calc (γ_down : ℂ) * (ρβ * (Lᴴ * (A * (L * A)))).trace
        = (((γ_down : ℂ) • (ρβ * Lᴴ)) * (A * L * A)).trace := by
            rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]; simp [Matrix.mul_assoc]
      _ = (((γ_up : ℂ) • (Lᴴ * ρβ)) * (A * L * A)).trace := by rw [hKMS_adj]
      _ = (γ_up : ℂ) * (Lᴴ * (ρβ * A * L * A)).trace := by
            rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]; simp [Matrix.mul_assoc]
      _ = (γ_up : ℂ) * ((ρβ * A * L * A) * Lᴴ).trace := by rw [Matrix.trace_mul_comm]
      _ = (γ_up : ℂ) * (ρβ * (A * (L * (A * Lᴴ)))).trace := by simp [Matrix.mul_assoc]
  have h2 : (γ_up : ℂ) * (ρβ * (L * (A * (Lᴴ * A)))).trace =
      (γ_down : ℂ) * (ρβ * (A * (Lᴴ * (A * L)))).trace := by
    calc (γ_up : ℂ) * (ρβ * (L * (A * (Lᴴ * A)))).trace
        = (((γ_up : ℂ) • (ρβ * L)) * (A * Lᴴ * A)).trace := by
            rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]; simp [Matrix.mul_assoc]
      _ = (((γ_down : ℂ) • (L * ρβ)) * (A * Lᴴ * A)).trace := by rw [← hKMS]
      _ = (γ_down : ℂ) * (L * (ρβ * A * Lᴴ * A)).trace := by
            rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]; simp [Matrix.mul_assoc]
      _ = (γ_down : ℂ) * ((ρβ * A * Lᴴ * A) * L).trace := by rw [Matrix.trace_mul_comm]
      _ = (γ_down : ℂ) * (ρβ * (A * (Lᴴ * (A * L)))).trace := by simp [Matrix.mul_assoc]
  have h3 : (γ_down : ℂ) * (ρβ * (Lᴴ * (A * (A * L)))).trace =
      (γ_up : ℂ) * (ρβ * (A * (A * (L * Lᴴ)))).trace := by
    calc (γ_down : ℂ) * (ρβ * (Lᴴ * (A * (A * L)))).trace
        = (L * ((γ_down : ℂ) • (ρβ * Lᴴ)) * (A * A)).trace := by
            rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
            congr 1
            calc (ρβ * (Lᴴ * (A * (A * L)))).trace
                = ((ρβ * Lᴴ * (A * A)) * L).trace := by simp [Matrix.mul_assoc]
              _ = (L * (ρβ * Lᴴ * (A * A))).trace := Matrix.trace_mul_comm _ _
              _ = (L * (ρβ * Lᴴ) * (A * A)).trace := by simp [Matrix.mul_assoc]
      _ = (L * ((γ_up : ℂ) • (Lᴴ * ρβ)) * (A * A)).trace := by rw [hKMS_adj]
      _ = (γ_up : ℂ) * ((L * Lᴴ) * (ρβ * (A * A))).trace := by
            rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
            simp [Matrix.mul_assoc]
      _ = (γ_up : ℂ) * ((ρβ * (A * A)) * (L * Lᴴ)).trace := by rw [Matrix.trace_mul_comm]
      _ = (γ_up : ℂ) * (ρβ * (A * (A * (L * Lᴴ)))).trace := by simp [Matrix.mul_assoc]
  have h4 : (γ_up : ℂ) * (ρβ * (L * (A * (A * Lᴴ)))).trace =
      (γ_down : ℂ) * (ρβ * (A * (A * (Lᴴ * L)))).trace := by
    calc (γ_up : ℂ) * (ρβ * (L * (A * (A * Lᴴ)))).trace
        = (Lᴴ * ((γ_up : ℂ) • (ρβ * L)) * (A * A)).trace := by
            rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
            congr 1
            calc (ρβ * (L * (A * (A * Lᴴ)))).trace
                = ((ρβ * L * (A * A)) * Lᴴ).trace := by simp [Matrix.mul_assoc]
              _ = (Lᴴ * (ρβ * L * (A * A))).trace := Matrix.trace_mul_comm _ _
              _ = (Lᴴ * (ρβ * L) * (A * A)).trace := by simp [Matrix.mul_assoc]
      _ = (Lᴴ * ((γ_down : ℂ) • (L * ρβ)) * (A * A)).trace := by rw [← hKMS]
      _ = (γ_down : ℂ) * ((Lᴴ * L) * (ρβ * (A * A))).trace := by
            rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
            simp [Matrix.mul_assoc]
      _ = (γ_down : ℂ) * ((ρβ * (A * A)) * (Lᴴ * L)).trace := by rw [Matrix.trace_mul_comm]
      _ = (γ_down : ℂ) * (ρβ * (A * (A * (Lᴴ * L)))).trace := by simp [Matrix.mul_assoc]
  have hc1 : (ρβ * (comm L A)ᴴ * comm L A).trace =
      (ρβ * (A * (Lᴴ * (L * A)))).trace - (ρβ * (A * (Lᴴ * (A * L)))).trace -
      (ρβ * (Lᴴ * (A * (L * A)))).trace + (ρβ * (Lᴴ * (A * (A * L)))).trace := by
    unfold comm
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hA]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, Matrix.mul_assoc]
    ring
  have hc2 : (ρβ * (comm Lᴴ A)ᴴ * comm Lᴴ A).trace =
      (ρβ * (A * (L * (Lᴴ * A)))).trace - (ρβ * (A * (L * (A * Lᴴ)))).trace -
      (ρβ * (L * (A * (Lᴴ * A)))).trace + (ρβ * (L * (A * (A * Lᴴ)))).trace := by
    unfold comm
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, hA]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, Matrix.mul_assoc]
    ring
  rw [hc1, hc2]
  unfold kmsPairGkslDual gkslDualOne
  rw [Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_sub, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_sub, smul_eq_mul, Matrix.mul_assoc]
  have hd : (γ_down : ℂ) * ((ρβ * (A * (Lᴴ * (L * A)))).trace - (ρβ * (A * (Lᴴ * (A * L)))).trace -
        (ρβ * (Lᴴ * (A * (L * A)))).trace + (ρβ * (Lᴴ * (A * (A * L)))).trace) =
      (γ_down : ℂ) * (ρβ * (A * (Lᴴ * (L * A)))).trace -
      (γ_down : ℂ) * (ρβ * (A * (Lᴴ * (A * L)))).trace -
      (γ_down : ℂ) * (ρβ * (Lᴴ * (A * (L * A)))).trace +
      (γ_down : ℂ) * (ρβ * (Lᴴ * (A * (A * L)))).trace := by ring
  have hu : (γ_up : ℂ) * ((ρβ * (A * (L * (Lᴴ * A)))).trace - (ρβ * (A * (L * (A * Lᴴ)))).trace -
        (ρβ * (L * (A * (Lᴴ * A)))).trace + (ρβ * (L * (A * (A * Lᴴ)))).trace) =
      (γ_up : ℂ) * (ρβ * (A * (L * (Lᴴ * A)))).trace -
      (γ_up : ℂ) * (ρβ * (A * (L * (A * Lᴴ)))).trace -
      (γ_up : ℂ) * (ρβ * (L * (A * (Lᴴ * A)))).trace +
      (γ_up : ℂ) * (ρβ * (L * (A * (A * Lᴴ)))).trace := by ring
  rw [hd, hu, h1, h2, h3, h4]
  ring

/-- **Theorem 1(d)** (Finite-`T_H` GNS-Weighted Monotonicity / Thermal Parisi–Wu Arrow):
For any Hermitian Gibbs state `ρ_β = S† S` satisfying the KMS intertwining relation
`γ_↓ (L ρ_β) = γ_↑ (ρ_β L)` with `γ_↓, γ_↑ ≥ 0`, and any Hermitian observable `A = A†`,
  `-2 Tr(ρ_β A L_KMS†(A)) = γ_↓ Tr(ρ_β [L, A]† [L, A]) + γ_↑ Tr(ρ_β [L†, A]† [L†, A])`,
whose real part equals `γ_↓ ‖[L, A] S†‖_F² + γ_↑ ‖[L†, A] S†‖_F² ≥ 0`. -/
theorem kms_gns_monotonicity {γ_down γ_up : ℝ} (hgd : 0 ≤ γ_down) (hgu : 0 ≤ γ_up)
    {L S A : Matrix (Fin d) (Fin d) ℂ} (hA : Aᴴ = A)
    (hKMS : (γ_down : ℂ) • (L * (Sᴴ * S)) = (γ_up : ℂ) • ((Sᴴ * S) * L)) :
    let ρβ := Sᴴ * S
    (-2 : ℂ) * (ρβ * A * kmsPairGkslDual γ_down γ_up L A).trace =
      (γ_down : ℂ) * (ρβ * (comm L A)ᴴ * comm L A).trace +
      (γ_up : ℂ) * (ρβ * (comm Lᴴ A)ᴴ * comm Lᴴ A).trace ∧
    0 ≤ ((-2 : ℂ) * (ρβ * A * kmsPairGkslDual γ_down γ_up L A).trace).re := by
  intro ρβ
  have hρβ : ρβᴴ = ρβ := by simp [ρβ]
  have hid := kms_gns_identity hρβ hA hKMS
  refine ⟨hid, ?_⟩
  rw [hid, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  have hnn : ∀ X : Matrix (Fin d) (Fin d) ℂ, 0 ≤ ((Sᴴ * S * Xᴴ * X).trace).re := by
    intro X
    have hcyc : (Sᴴ * S * Xᴴ * X).trace = ((X * Sᴴ)ᴴ * (X * Sᴴ)).trace := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      calc (Sᴴ * S * Xᴴ * X).trace
          = (Sᴴ * (S * Xᴴ * X)).trace := by simp [Matrix.mul_assoc]
        _ = ((S * Xᴴ * X) * Sᴴ).trace := Matrix.trace_mul_comm _ _
        _ = (S * Xᴴ * (X * Sᴴ)).trace := by simp [Matrix.mul_assoc]
    rw [hcyc, trace_conjTranspose_mul_self_re]
    exact frobNormSq_nonneg _
  exact add_nonneg (mul_nonneg hgd (hnn (comm L A))) (mul_nonneg hgu (hnn (comm Lᴴ A)))

/-- **Theorem 1(d.1)** (Symmetric Similarity Intertwining for Non-Commuting States):
Given a Hermitian square root `S = S†` of `ρ_β = S²`, real amplitudes `a, b : ℝ` (rates
`γ_↓ = a²`, `γ_↑ = b²`), and square-root KMS intertwining `a (L S) = b (S L)`
(satisfied by `S = ρ_β^{1/2}` whenever `[H, L] = -ω L` and `b / a = e^{-β ω / 2}`),
the Schrödinger thermal generator intertwines identically with the Heisenberg dual on
every matrix `X` (commuting or non-commuting with `ρ_β`):
  `L_pair(S X S) = S · L_pair†(X) · S`.
Applying this to `ρ = S (B + 1) S` (so `B = S⁻¹ ρ S⁻¹ - 1 = B†`) bridges non-commuting
density-matrix evolution directly to the Hermitian Dirichlet identity `kms_gns_monotonicity`. -/
theorem kms_symmetric_intertwining {a b : ℝ} {L S X : Matrix (Fin d) (Fin d) ℂ}
    (hS : Sᴴ = S) (hsqrt : (a : ℂ) • (L * S) = (b : ℂ) • (S * L)) :
    kmsPairGksl (a ^ 2) (b ^ 2) L (S * X * S) =
      S * kmsPairGkslDual (a ^ 2) (b ^ 2) L X * S := by
  have hsqrt_adj : (a : ℂ) • (S * Lᴴ) = (b : ℂ) • (Lᴴ * S) := by
    have h := congrArg Matrix.conjTranspose hsqrt
    simpa [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hS] using h
  have ha2 : ((a ^ 2 : ℝ) : ℂ) = (a : ℂ) * (a : ℂ) := by push_cast; ring
  have hb2 : ((b ^ 2 : ℝ) : ℂ) = (b : ℂ) * (b : ℂ) := by push_cast; ring
  have t1 : ((a ^ 2 : ℝ) : ℂ) • (L * (S * X * S) * Lᴴ) =
      ((b ^ 2 : ℝ) : ℂ) • (S * (L * X * Lᴴ) * S) := by
    rw [ha2, hb2]
    calc ((a : ℂ) * (a : ℂ)) • (L * (S * X * S) * Lᴴ)
        = ((a : ℂ) • (L * S)) * X * ((a : ℂ) • (S * Lᴴ)) := by
            simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      _ = ((b : ℂ) • (S * L)) * X * ((b : ℂ) • (Lᴴ * S)) := by rw [hsqrt, hsqrt_adj]
      _ = ((b : ℂ) * (b : ℂ)) • (S * (L * X * Lᴴ) * S) := by
            simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  have t2 : ((b ^ 2 : ℝ) : ℂ) • (Lᴴ * (S * X * S) * L) =
      ((a ^ 2 : ℝ) : ℂ) • (S * (Lᴴ * X * L) * S) := by
    rw [ha2, hb2]
    calc ((b : ℂ) * (b : ℂ)) • (Lᴴ * (S * X * S) * L)
        = ((b : ℂ) • (Lᴴ * S)) * X * ((b : ℂ) • (S * L)) := by
            simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      _ = ((a : ℂ) • (S * Lᴴ)) * X * ((a : ℂ) • (L * S)) := by rw [← hsqrt_adj, ← hsqrt]
      _ = ((a : ℂ) * (a : ℂ)) • (S * (Lᴴ * X * L) * S) := by
            simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  have hcomm1 : ((a ^ 2 : ℝ) : ℂ) • (Lᴴ * L * S) = ((a ^ 2 : ℝ) : ℂ) • (S * (Lᴴ * L)) := by
    rw [ha2]
    calc ((a : ℂ) * (a : ℂ)) • (Lᴴ * L * S)
        = (a : ℂ) • (Lᴴ * ((a : ℂ) • (L * S))) := by
            simp only [Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      _ = (a : ℂ) • (Lᴴ * ((b : ℂ) • (S * L))) := by rw [hsqrt]
      _ = ((b : ℂ) • (Lᴴ * S)) * ((a : ℂ) • L) := by
            simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      _ = ((a : ℂ) • (S * Lᴴ)) * ((a : ℂ) • L) := by rw [← hsqrt_adj]
      _ = ((a : ℂ) * (a : ℂ)) • (S * (Lᴴ * L)) := by
            simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  have hcomm2 : ((b ^ 2 : ℝ) : ℂ) • (L * Lᴴ * S) = ((b ^ 2 : ℝ) : ℂ) • (S * (L * Lᴴ)) := by
    rw [hb2]
    calc ((b : ℂ) * (b : ℂ)) • (L * Lᴴ * S)
        = (b : ℂ) • (L * ((b : ℂ) • (Lᴴ * S))) := by
            simp only [Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      _ = (b : ℂ) • (L * ((a : ℂ) • (S * Lᴴ))) := by rw [← hsqrt_adj]
      _ = ((a : ℂ) • (L * S)) * ((b : ℂ) • Lᴴ) := by
            simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      _ = ((b : ℂ) • (S * L)) * ((b : ℂ) • Lᴴ) := by rw [hsqrt]
      _ = ((b : ℂ) * (b : ℂ)) • (S * (L * Lᴴ)) := by
            simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  have c1L : ((a ^ 2 : ℝ) : ℂ) • (Lᴴ * L * (S * X * S)) =
      ((a ^ 2 : ℝ) : ℂ) • (S * (Lᴴ * L * X) * S) := by
    calc ((a ^ 2 : ℝ) : ℂ) • (Lᴴ * L * (S * X * S))
        = (((a ^ 2 : ℝ) : ℂ) • (Lᴴ * L * S)) * (X * S) := by
            simp only [Matrix.smul_mul, Matrix.mul_assoc]
      _ = (((a ^ 2 : ℝ) : ℂ) • (S * (Lᴴ * L))) * (X * S) := by rw [hcomm1]
      _ = ((a ^ 2 : ℝ) : ℂ) • (S * (Lᴴ * L * X) * S) := by
            simp only [Matrix.smul_mul, Matrix.mul_assoc]
  have c1R : ((a ^ 2 : ℝ) : ℂ) • (S * X * S * (Lᴴ * L)) =
      ((a ^ 2 : ℝ) : ℂ) • (S * (X * (Lᴴ * L)) * S) := by
    calc ((a ^ 2 : ℝ) : ℂ) • (S * X * S * (Lᴴ * L))
        = (S * X) * (((a ^ 2 : ℝ) : ℂ) • (S * (Lᴴ * L))) := by
            simp only [Matrix.mul_smul, Matrix.mul_assoc]
      _ = (S * X) * (((a ^ 2 : ℝ) : ℂ) • (Lᴴ * L * S)) := by rw [← hcomm1]
      _ = ((a ^ 2 : ℝ) : ℂ) • (S * (X * (Lᴴ * L)) * S) := by
            simp only [Matrix.mul_smul, Matrix.mul_assoc]
  have c2L : ((b ^ 2 : ℝ) : ℂ) • (L * Lᴴ * (S * X * S)) =
      ((b ^ 2 : ℝ) : ℂ) • (S * (L * Lᴴ * X) * S) := by
    calc ((b ^ 2 : ℝ) : ℂ) • (L * Lᴴ * (S * X * S))
        = (((b ^ 2 : ℝ) : ℂ) • (L * Lᴴ * S)) * (X * S) := by
            simp only [Matrix.smul_mul, Matrix.mul_assoc]
      _ = (((b ^ 2 : ℝ) : ℂ) • (S * (L * Lᴴ))) * (X * S) := by rw [hcomm2]
      _ = ((b ^ 2 : ℝ) : ℂ) • (S * (L * Lᴴ * X) * S) := by
            simp only [Matrix.smul_mul, Matrix.mul_assoc]
  have c2R : ((b ^ 2 : ℝ) : ℂ) • (S * X * S * (L * Lᴴ)) =
      ((b ^ 2 : ℝ) : ℂ) • (S * (X * (L * Lᴴ)) * S) := by
    calc ((b ^ 2 : ℝ) : ℂ) • (S * X * S * (L * Lᴴ))
        = (S * X) * (((b ^ 2 : ℝ) : ℂ) • (S * (L * Lᴴ))) := by
            simp only [Matrix.mul_smul, Matrix.mul_assoc]
      _ = (S * X) * (((b ^ 2 : ℝ) : ℂ) • (L * Lᴴ * S)) := by rw [← hcomm2]
      _ = ((b ^ 2 : ℝ) : ℂ) • (S * (X * (L * Lᴴ)) * S) := by
            simp only [Matrix.mul_smul, Matrix.mul_assoc]
  unfold kmsPairGksl kmsPairGkslDual gkslOne gkslDualOne
  rw [Matrix.conjTranspose_conjTranspose]
  simp only [smul_sub, smul_add, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul]
  simp only [smul_comm ((a ^ 2 : ℝ) : ℂ) (2⁻¹ : ℂ), smul_comm ((b ^ 2 : ℝ) : ℂ) (2⁻¹ : ℂ)]
  rw [t1, t2, c1L, c1R, c2L, c2R]
  abel

/-- **Theorem 1(e)** (Non-Secular Bloch–Redfield Complete-Positivity Obstruction):
For a two-level thermal system with `γ_↓ ≠ γ_↑` (`T_H < ∞`), the non-secular
Bloch–Redfield Kossakowski matrix `K_Red = [[γ_↓, (γ_↓+γ_↑)/2], [(γ_↓+γ_↑)/2, γ_↑]]`
has strictly negative determinant `det K_Red = -(γ_↓ - γ_↑)² / 4 < 0` and admits
an explicit negative-curvature vector `v = (γ_↓ + γ_↑, -2 γ_↓)` with
`vᵀ K_Red v = -γ_↓ (γ_↓ - γ_↑)² < 0` whenever `γ_↓ > 0`. -/
theorem nonsecular_redfield_kossakowski_obstruction (γ_down γ_up : ℝ)
    (hgd : 0 < γ_down) (hne : γ_down ≠ γ_up) :
    let m12 := (γ_down + γ_up) / 2
    let detK := γ_down * γ_up - m12 ^ 2
    let v1 := γ_down + γ_up
    let v2 := -2 * γ_down
    detK = -((γ_down - γ_up) ^ 2) / 4 ∧
    detK < 0 ∧
    v1 * (γ_down * v1 + m12 * v2) + v2 * (m12 * v1 + γ_up * v2) =
      -γ_down * (γ_down - γ_up) ^ 2 ∧
    v1 * (γ_down * v1 + m12 * v2) + v2 * (m12 * v1 + γ_up * v2) < 0 := by
  intro m12 detK v1 v2
  have hsq_pos : 0 < (γ_down - γ_up) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  have hdet : detK = -((γ_down - γ_up) ^ 2) / 4 := by
    dsimp only [detK, m12]; ring
  have hquad : v1 * (γ_down * v1 + m12 * v2) + v2 * (m12 * v1 + γ_up * v2) =
      -γ_down * (γ_down - γ_up) ^ 2 := by
    dsimp only [v1, v2, m12]; ring
  refine ⟨hdet, ?_, hquad, ?_⟩
  · rw [hdet]; linarith
  · rw [hquad]; nlinarith

lemma frobNormSq_eq_zero_iff {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) :
    frobNormSq M = 0 ↔ M = 0 := by
  constructor
  · intro h0
    unfold frobNormSq at h0
    have hrow : ∀ i : Fin m, ∑ j : Fin n, Complex.normSq (M i j) = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
        Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _))).mp h0 i (Finset.mem_univ i)
    ext i j
    have hij : Complex.normSq (M i j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Complex.normSq_nonneg _)).mp
        (hrow i) j (Finset.mem_univ j)
    exact Complex.normSq_eq_zero.mp hij
  · intro h0
    subst h0
    simp [frobNormSq]

lemma gkslDualOne_eq_zero_of_comm {L A : Matrix (Fin d) (Fin d) ℂ}
    (hLA : comm L A = 0) (hLdA : comm Lᴴ A = 0) :
    gkslDualOne L A = 0 := by
  have h1 : L * A = A * L := sub_eq_zero.mp hLA
  have h2 : Lᴴ * A = A * Lᴴ := sub_eq_zero.mp hLdA
  have t1 : Lᴴ * A * L = Lᴴ * L * A := by
    calc Lᴴ * A * L = Lᴴ * (A * L) := by rw [Matrix.mul_assoc]
      _ = Lᴴ * (L * A) := by rw [← h1]
      _ = Lᴴ * L * A := by rw [← Matrix.mul_assoc]
  have t2 : A * (Lᴴ * L) = Lᴴ * L * A := by
    calc A * (Lᴴ * L) = (A * Lᴴ) * L := by rw [← Matrix.mul_assoc]
      _ = (Lᴴ * A) * L := by rw [← h2]
      _ = Lᴴ * L * A := t1
  unfold gkslDualOne
  rw [t1, t2]
  have hhalf : (2⁻¹ : ℂ) • (Lᴴ * L * A + Lᴴ * L * A) = Lᴴ * L * A := by
    rw [smul_add, ← add_smul]; norm_num
  rw [hhalf, sub_self]

/-- **Theorem 1(f)** (Dirichlet-Kernel Criterion for Preserving Free-Subsystem
Two-Time Autocorrelations under Quantum Regression):
For any faithful KMS stationary state `ρ_β = S† S` (with `S†` right-invertible) and
strictly positive detailed-balance rates `γ_↓ > 0`, `γ_↑ > 0`, vanishing initial real
discrepancy `Re Tr(ρ_β A L_pair†(A)) = 0` between the Markovian quantum-regression
autocorrelation `C_QRT(τ)` and the free-subsystem unitary autocorrelation `C_free(τ)` for a
Hermitian observable `A = A†` implies `[L, A] = 0`, `[L†, A] = 0`, and `L_pair†(A) = 0`.
Hence no nontrivial KMS dissipator acting on `A_B` (`L ∉ A_B'`) preserves the free-subsystem
autocorrelations of all Hermitian observables in `A_B` simultaneously. (This lemma compares
`C_QRT` against `C_free`; it makes no claim about interacting total-system unitary
correlations or general necessity of non-Markovian memory.) -/
theorem multitime_qrt_exterior_nogo {γ_down γ_up : ℝ} (hgd : 0 < γ_down) (hgu : 0 < γ_up)
    {L S A : Matrix (Fin d) (Fin d) ℂ} (hA : Aᴴ = A)
    (hSinv : ∃ T : Matrix (Fin d) (Fin d) ℂ, Sᴴ * T = 1)
    (hKMS : (γ_down : ℂ) • (L * (Sᴴ * S)) = (γ_up : ℂ) • ((Sᴴ * S) * L))
    (hzero : ((Sᴴ * S * A * kmsPairGkslDual γ_down γ_up L A).trace).re = 0) :
    comm L A = 0 ∧ comm Lᴴ A = 0 ∧ kmsPairGkslDual γ_down γ_up L A = 0 := by
  have hid := (kms_gns_monotonicity (le_of_lt hgd) (le_of_lt hgu) hA hKMS).1
  have hre : ((-2 : ℂ) * (Sᴴ * S * A * kmsPairGkslDual γ_down γ_up L A).trace).re = 0 := by
    have hm : ((-2 : ℂ) * (Sᴴ * S * A * kmsPairGkslDual γ_down γ_up L A).trace).re =
        (-2 : ℝ) * ((Sᴴ * S * A * kmsPairGkslDual γ_down γ_up L A).trace).re := by
      change (((-2 : ℝ) : ℂ) * (Sᴴ * S * A * kmsPairGkslDual γ_down γ_up L A).trace).re = _
      exact Complex.re_ofReal_mul (-2) _
    rw [hm, hzero, mul_zero]
  have hfrob : ∀ X : Matrix (Fin d) (Fin d) ℂ,
      ((Sᴴ * S * Xᴴ * X).trace).re = frobNormSq (X * Sᴴ) := by
    intro X
    have hcyc : (Sᴴ * S * Xᴴ * X).trace = ((X * Sᴴ)ᴴ * (X * Sᴴ)).trace := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      calc (Sᴴ * S * Xᴴ * X).trace
          = (Sᴴ * (S * Xᴴ * X)).trace := by simp [Matrix.mul_assoc]
        _ = ((S * Xᴴ * X) * Sᴴ).trace := Matrix.trace_mul_comm _ _
        _ = (S * Xᴴ * (X * Sᴴ)).trace := by simp [Matrix.mul_assoc]
    rw [hcyc, trace_conjTranspose_mul_self_re]
  have hsum : γ_down * frobNormSq (comm L A * Sᴴ) + γ_up * frobNormSq (comm Lᴴ A * Sᴴ) = 0 := by
    have h1 := congrArg Complex.re hid
    rw [hre, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
      hfrob (comm L A), hfrob (comm Lᴴ A)] at h1
    exact h1.symm
  have hnn1 : 0 ≤ frobNormSq (comm L A * Sᴴ) := frobNormSq_nonneg _
  have hnn2 : 0 ≤ frobNormSq (comm Lᴴ A * Sᴴ) := frobNormSq_nonneg _
  have hz1 : frobNormSq (comm L A * Sᴴ) = 0 := by nlinarith
  have hz2 : frobNormSq (comm Lᴴ A * Sᴴ) = 0 := by nlinarith
  have hm1 : comm L A * Sᴴ = 0 := (frobNormSq_eq_zero_iff _).mp hz1
  have hm2 : comm Lᴴ A * Sᴴ = 0 := (frobNormSq_eq_zero_iff _).mp hz2
  rcases hSinv with ⟨T, hST⟩
  have hLA : comm L A = 0 := by
    calc comm L A = comm L A * 1 := by rw [Matrix.mul_one]
      _ = comm L A * (Sᴴ * T) := by rw [← hST]
      _ = (comm L A * Sᴴ) * T := by rw [← Matrix.mul_assoc]
      _ = 0 := by rw [hm1, Matrix.zero_mul]
  have hLdA : comm Lᴴ A = 0 := by
    calc comm Lᴴ A = comm Lᴴ A * 1 := by rw [Matrix.mul_one]
      _ = comm Lᴴ A * (Sᴴ * T) := by rw [← hST]
      _ = (comm Lᴴ A * Sᴴ) * T := by rw [← Matrix.mul_assoc]
      _ = 0 := by rw [hm2, Matrix.zero_mul]
  have hdual : kmsPairGkslDual γ_down γ_up L A = 0 := by
    unfold kmsPairGkslDual
    have hLddA : comm (Lᴴ)ᴴ A = 0 := by rw [Matrix.conjTranspose_conjTranspose]; exact hLA
    rw [gkslDualOne_eq_zero_of_comm hLA hLdA, gkslDualOne_eq_zero_of_comm hLdA hLddA]
    simp
  exact ⟨hLA, hLdA, hdual⟩

/-- Exact Duhamel adiabatic tracking envelope
`g(t) = M e^{-λ t} ε_0 + (M / λ)(1 - e^{-λ t}) D`. -/
noncomputable def gibbsTrackingEnvelope (M lam ε0 D t : ℝ) : ℝ :=
  M * Real.exp (-lam * t) * ε0 + (M / lam) * (1 - Real.exp (-lam * t)) * D

/-- **Proposition 1 (Uniform-Contraction Gibbs Tracking Envelope & Two-Level Gibbs Drift)**:
Given uniform-contraction constants `M > 0`, `lam > 0`, initial error bound `ε0 ≥ 0`, and
adiabatic drift supremum `D ≥ 0`:
  (1) `g(t) = M e^{-lam t} ε0 + (M / lam)(1 - e^{-lam t}) D` satisfies the exact ODE
      `g'(t) = -lam g(t) + M D`, initial condition `g(0) = M ε0`, non-negativity `g(t) ≥ 0`,
      and uniform ceiling `g(t) ≤ M ε0 + (M / lam) D` for all `t ≥ 0`.
  (2) **Duhamel–Gronwall comparison**: any differentiable error curve `ε : ℝ → ℝ` satisfying
      `ε 0 ≤ M ε0` and `ε'(τ) ≤ -lam ε(τ) + M D` for all `τ ≥ 0` obeys `ε(t) ≤ g(t)` for all `t ≥ 0`.
  (3) **Two-level Gibbs population drift**: for `T(t) = T0 e^{-μ t}` (`T0 > 0`) and excited-level
      Gibbs population `p_Gibbs(t) = (1 + exp(ω / T(t)))⁻¹`, the exact derivative equals
      `-ω μ exp(ω / T(t)) / (T(t) (1 + exp(ω / T(t)))²)`, yielding trace-norm drift
      `‖σ̇_t‖_1 = 2 |ṗ_Gibbs(t)|`. -/
theorem uniform_contraction_gibbs_tracking_bound
    (M lam ε0 D ω T0 μ t : ℝ) (hM : 0 < M) (hlam : 0 < lam)
    (hε0 : 0 ≤ ε0) (hD : 0 ≤ D) (hT0 : 0 < T0) (ht : 0 ≤ t) :
    HasDerivAt (fun τ => gibbsTrackingEnvelope M lam ε0 D τ)
      (-lam * gibbsTrackingEnvelope M lam ε0 D t + M * D) t ∧
    gibbsTrackingEnvelope M lam ε0 D 0 = M * ε0 ∧
    0 ≤ gibbsTrackingEnvelope M lam ε0 D t ∧
    gibbsTrackingEnvelope M lam ε0 D t ≤ M * ε0 + (M / lam) * D ∧
    (∀ (ε ε' : ℝ → ℝ),
      (∀ τ : ℝ, HasDerivAt ε (ε' τ) τ) →
      ε 0 ≤ M * ε0 →
      (∀ τ : ℝ, 0 ≤ τ → ε' τ ≤ -lam * ε τ + M * D) →
      ε t ≤ gibbsTrackingEnvelope M lam ε0 D t) ∧
    HasDerivAt (fun τ => (1 + Real.exp (ω / (T0 * Real.exp (-μ * τ))))⁻¹)
      (-(ω * μ * Real.exp (ω / (T0 * Real.exp (-μ * t)))) /
        ((T0 * Real.exp (-μ * t)) * (1 + Real.exp (ω / (T0 * Real.exp (-μ * t)))) ^ 2)) t := by
  have hlamne : lam ≠ 0 := ne_of_gt hlam
  have hg_deriv : ∀ τ : ℝ, HasDerivAt (fun s => gibbsTrackingEnvelope M lam ε0 D s)
      (-lam * gibbsTrackingEnvelope M lam ε0 D τ + M * D) τ := by
    intro τ
    have hlin : HasDerivAt (fun s => -lam * s) (-lam) τ := by
      simpa using (hasDerivAt_id τ).const_mul (-lam)
    have hexp : HasDerivAt (fun s => Real.exp (-lam * s)) (Real.exp (-lam * τ) * (-lam)) τ := hlin.exp
    have hterm1 : HasDerivAt (fun s => M * Real.exp (-lam * s) * ε0)
        (M * (Real.exp (-lam * τ) * (-lam)) * ε0) τ := (hexp.const_mul M).mul_const ε0
    have hsub : HasDerivAt (fun s => 1 - Real.exp (-lam * s))
        (0 - Real.exp (-lam * τ) * (-lam)) τ := (hasDerivAt_const τ (1 : ℝ)).sub hexp
    have hterm2 : HasDerivAt (fun s => (M / lam) * (1 - Real.exp (-lam * s)) * D)
        ((M / lam) * (0 - Real.exp (-lam * τ) * (-lam)) * D) τ := (hsub.const_mul (M / lam)).mul_const D
    have hsum := hterm1.add hterm2
    unfold gibbsTrackingEnvelope
    convert hsum using 1
    field_simp [hlamne]
    ring
  have hg0 : gibbsTrackingEnvelope M lam ε0 D 0 = M * ε0 := by
    unfold gibbsTrackingEnvelope
    simp
  have hexp_le : Real.exp (-lam * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have hexp_pos : 0 < Real.exp (-lam * t) := Real.exp_pos _
  have hg_nonneg : 0 ≤ gibbsTrackingEnvelope M lam ε0 D t := by
    unfold gibbsTrackingEnvelope
    have h1 : 0 ≤ M * Real.exp (-lam * t) * ε0 := by positivity
    have h2 : 0 ≤ (M / lam) * (1 - Real.exp (-lam * t)) * D := by
      have hsub : 0 ≤ 1 - Real.exp (-lam * t) := sub_nonneg.mpr hexp_le
      positivity
    linarith
  have hg_le : gibbsTrackingEnvelope M lam ε0 D t ≤ M * ε0 + (M / lam) * D := by
    unfold gibbsTrackingEnvelope
    have h1 : M * Real.exp (-lam * t) * ε0 ≤ M * ε0 := by
      have : M * Real.exp (-lam * t) ≤ M * 1 :=
        mul_le_mul_of_nonneg_left hexp_le (le_of_lt hM)
      nlinarith
    have h2 : (M / lam) * (1 - Real.exp (-lam * t)) * D ≤ (M / lam) * D := by
      have hsub_le : 1 - Real.exp (-lam * t) ≤ 1 := by linarith
      have hMlam : 0 ≤ M / lam := div_nonneg (le_of_lt hM) (le_of_lt hlam)
      have : (M / lam) * (1 - Real.exp (-lam * t)) ≤ (M / lam) * 1 :=
        mul_le_mul_of_nonneg_left hsub_le hMlam
      nlinarith
    linarith
  have hgronwall : ∀ (ε ε' : ℝ → ℝ),
      (∀ τ : ℝ, HasDerivAt ε (ε' τ) τ) →
      ε 0 ≤ M * ε0 →
      (∀ τ : ℝ, 0 ≤ τ → ε' τ ≤ -lam * ε τ + M * D) →
      ε t ≤ gibbsTrackingEnvelope M lam ε0 D t := by
    intro ε ε' hε_deriv hε_init hε_ineq
    rcases eq_or_lt_of_le ht with rfl | ht_pos
    · rw [hg0]; exact hε_init
    · let h : ℝ → ℝ := fun τ => Real.exp (lam * τ) * (ε τ - gibbsTrackingEnvelope M lam ε0 D τ)
      let h' : ℝ → ℝ := fun τ => Real.exp (lam * τ) * (ε' τ + lam * ε τ - M * D)
      have hh_deriv : ∀ τ : ℝ, HasDerivAt h (h' τ) τ := by
        intro τ
        have hl : HasDerivAt (fun s => lam * s) lam τ := by
          simpa using (hasDerivAt_id τ).const_mul lam
        have he : HasDerivAt (fun s => Real.exp (lam * s)) (Real.exp (lam * τ) * lam) τ := hl.exp
        have hd : HasDerivAt (fun s => ε s - gibbsTrackingEnvelope M lam ε0 D s)
            (ε' τ - (-lam * gibbsTrackingEnvelope M lam ε0 D τ + M * D)) τ :=
          (hε_deriv τ).sub (hg_deriv τ)
        have hmul := he.mul hd
        dsimp only [h, h']
        convert hmul using 1
        ring
      have hcont : ContinuousOn h (Set.Icc 0 t) :=
        (continuous_iff_continuousAt.mpr fun τ => (hh_deriv τ).continuousAt).continuousOn
      obtain ⟨c, ⟨hc0, _⟩, hslope⟩ :=
        exists_hasDerivAt_eq_slope h h' ht_pos hcont (fun τ _ => hh_deriv τ)
      have hfac : ε' c + lam * ε c - M * D ≤ 0 := by
        have := hε_ineq c (le_of_lt hc0)
        linarith
      have hderiv_nonpos : h' c ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _)) hfac
      have hsub_nonpos : h t - h 0 ≤ 0 := by
        have hdiv : (h t - h 0) / (t - 0) ≤ 0 := by rw [← hslope]; exact hderiv_nonpos
        have htsub : 0 < t - 0 := by linarith
        exact (div_nonpos_iff.mp hdiv).elim (fun ⟨_, hle⟩ => by linarith) (fun ⟨hle, _⟩ => hle)
      have h0_nonpos : h 0 ≤ 0 := by
        dsimp only [h]
        rw [mul_zero, Real.exp_zero, one_mul, hg0]
        linarith
      have ht_nonpos : Real.exp (lam * t) * (ε t - gibbsTrackingEnvelope M lam ε0 D t) ≤ 0 := by
        change h t ≤ 0
        linarith
      have hdiff_nonpos : ε t - gibbsTrackingEnvelope M lam ε0 D t ≤ 0 :=
        nonpos_of_mul_nonpos_right ht_nonpos (Real.exp_pos _)
      linarith
  have hgibbs_deriv : HasDerivAt (fun τ => (1 + Real.exp (ω / (T0 * Real.exp (-μ * τ))))⁻¹)
      (-(ω * μ * Real.exp (ω / (T0 * Real.exp (-μ * t)))) /
        ((T0 * Real.exp (-μ * t)) * (1 + Real.exp (ω / (T0 * Real.exp (-μ * t)))) ^ 2)) t := by
    have hTpos : 0 < T0 * Real.exp (-μ * t) := mul_pos hT0 (Real.exp_pos _)
    have hTne : T0 * Real.exp (-μ * t) ≠ 0 := ne_of_gt hTpos
    have hden_pos : 0 < 1 + Real.exp (ω / (T0 * Real.exp (-μ * t))) := by
      linarith [Real.exp_pos (ω / (T0 * Real.exp (-μ * t)))]
    have hden_ne : 1 + Real.exp (ω / (T0 * Real.exp (-μ * t))) ≠ 0 := ne_of_gt hden_pos
    have hlin : HasDerivAt (fun τ => -μ * τ) (-μ) t := by
      simpa using (hasDerivAt_id t).const_mul (-μ)
    have hT_d : HasDerivAt (fun τ => T0 * Real.exp (-μ * τ))
        (T0 * (Real.exp (-μ * t) * (-μ))) t := hlin.exp.const_mul T0
    have harg_d : HasDerivAt (fun τ => ω / (T0 * Real.exp (-μ * τ)))
        ((0 * (T0 * Real.exp (-μ * t)) - ω * (T0 * (Real.exp (-μ * t) * (-μ)))) /
          (T0 * Real.exp (-μ * t)) ^ 2) t :=
      (hasDerivAt_const t ω).div hT_d hTne
    have h1e_d : HasDerivAt (fun τ => 1 + Real.exp (ω / (T0 * Real.exp (-μ * τ))))
        (Real.exp (ω / (T0 * Real.exp (-μ * t))) *
          ((0 * (T0 * Real.exp (-μ * t)) - ω * (T0 * (Real.exp (-μ * t) * (-μ)))) /
            (T0 * Real.exp (-μ * t)) ^ 2)) t :=
      (harg_d.exp).const_add (1 : ℝ)
    have hinv_d := h1e_d.inv hden_ne
    convert hinv_d using 1
    field_simp [hTne, hden_ne]
    ring
  exact ⟨hg_deriv t, hg0, hg_nonneg, hg_le, hgronwall, hgibbs_deriv⟩

end OSTQD_SK
