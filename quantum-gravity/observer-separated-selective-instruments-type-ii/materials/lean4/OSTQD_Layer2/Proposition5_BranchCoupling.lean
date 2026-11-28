import OSTQD_Layer2.Basic

/-!
# OSTQD_Layer2.Proposition5_BranchCoupling

Formalizes Proposition 1 (Active Exploratory Branch-Coupling Gate & Five-Property Audit;
module retains legacy filename `Proposition5_BranchCoupling.lean` for backward compatibility):
1. Control 0 (Gisin 1990 wall): globally trace-preserving nonlinear map `Φ_λ` giving exact
   EPR signaling bias `Re Tr(Z (ρ̄_Z - ρ̄_X)) = λ`.
2. Control 0' (R2): local CPTP semicausality `Tr_B((I_A ⊗ Φ_B)(ρ)) = Tr_B(ρ)` vs. SWAP gate
   counterexample (linear CPTP + Gisin ensemble-independent, yet spatially signaling).
3. Mechanism A (Non-isometric branch crosstalk, R2 & R3): arbitrary-dimension complex Welch bound,
   rank-forced off-diagonal branch-crosstalk floor, trine frame non-TP/non-TNI witness (`Tr = 3/2`)
   and normalized frame-POVM identity, plus full-rank duplicated-frame counterexample disproving
   any universal `O(r^{-1/2})` upper bound.
4. Mechanism B (Oppenheim CQ trade-off): exact `2×2` PSD equivalence `4 D2 D0 ≥ D1²`.
5. Mechanism C (Two-clock constraints, R6): factorized dressed commutativity and exact `C_tot = 0`
   bipolar-clock model with both entangled and product states in `ker C_tot` plus exact
   non-wrapping dressed operators satisfying `[C_tot, O_A^{ex}] = 0` identically.
-/

open scoped Matrix BigOperators ComplexConjugate

namespace OSTQD_Layer2

variable {r M dA dB : ℕ}

/-- Control 0 nonlinear state map `Φ_λ(ρ) = (1 - λ (Re Tr(ρ Z))²) ρ + λ (Re Tr(ρ Z))² |0⟩⟨0|`. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
def projZero : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]
def projOne : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 0, 1]
noncomputable def projPlus : Matrix (Fin 2) (Fin 2) ℂ := !![(2⁻¹ : ℂ), (2⁻¹ : ℂ); (2⁻¹ : ℂ), (2⁻¹ : ℂ)]
noncomputable def projMinus : Matrix (Fin 2) (Fin 2) ℂ := !![(2⁻¹ : ℂ), -(2⁻¹ : ℂ); -(2⁻¹ : ℂ), (2⁻¹ : ℂ)]

noncomputable def gisinNonlinearMap (lam : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  let w : ℂ := ((lam * ((ρ * pauliZ).trace.re) ^ 2 : ℝ) : ℂ)
  (1 - w) • ρ + w • projZero

/-- Exact trace preservation of `gisinNonlinearMap` for all `λ ∈ ℝ` whenever `Tr(ρ) = 1`. -/
theorem gisin_nonlinear_map_trace_preserving
    (lam : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) (hTr : ρ.trace = 1) :
    (gisinNonlinearMap lam ρ).trace = 1 := by
  unfold gisinNonlinearMap
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hTr]
  have hP0 : projZero.trace = 1 := by
    simp [projZero, Matrix.trace, Fin.sum_univ_two]
  rw [hP0]
  simp [smul_eq_mul]

/-- Control 0 Gisin signaling witness: on Bell-steered ensembles `Z` vs. `X` of `I/2`,
    `gisinNonlinearMap` creates exact superluminal signaling bias `Re Tr(Z (ρ̄_Z - ρ̄_X)) = λ`. -/
theorem gisin_epr_signaling_bias (lam : ℝ) :
    let rhoBarZ := (2⁻¹ : ℂ) • gisinNonlinearMap lam projZero +
      (2⁻¹ : ℂ) • gisinNonlinearMap lam projOne
    let rhoBarX := (2⁻¹ : ℂ) • gisinNonlinearMap lam projPlus +
      (2⁻¹ : ℂ) • gisinNonlinearMap lam projMinus
    ((pauliZ * (rhoBarZ - rhoBarX)).trace).re = lam := by
  intro rhoBarZ rhoBarX
  have h0 : (projZero * pauliZ).trace.re = 1 := by
    norm_num [projZero, pauliZ, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  have h1 : (projOne * pauliZ).trace.re = -1 := by
    norm_num [projOne, pauliZ, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  have hp : (projPlus * pauliZ).trace.re = 0 := by
    norm_num [projPlus, pauliZ, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  have hm : (projMinus * pauliZ).trace.re = 0 := by
    norm_num [projMinus, pauliZ, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [rhoBarZ, rhoBarX, gisinNonlinearMap, h0, h1, hp, hm]
  norm_num [pauliZ, projZero, projOne, projPlus, projMinus, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_two]
  ring

/-- Helper: `Re((V Vᴴ)_{aa}) = ∑_x |V_{ax}|²` and `Im((V Vᴴ)_{aa}) = 0`. -/
lemma mul_conjTranspose_diag_re (V : Matrix (Fin r) (Fin M) ℂ) (a : Fin r) :
    ((V * Vᴴ) a a).re = ∑ x : Fin M, Complex.normSq (V a x) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum, mul_star_self_re]

lemma mul_conjTranspose_diag_im (V : Matrix (Fin r) (Fin M) ℂ) (a : Fin r) :
    ((V * Vᴴ) a a).im = 0 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.im_sum]
  refine Finset.sum_eq_zero fun x _ => ?_
  simp [Complex.mul_im]
  ring

lemma conjTranspose_mul_diag_im (V : Matrix (Fin r) (Fin M) ℂ) (x : Fin M) :
    ((Vᴴ * V) x x).im = 0 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.im_sum]
  refine Finset.sum_eq_zero fun a _ => ?_
  simp [Complex.mul_im]
  ring

/-- Equality of Frobenius norms `‖Vᴴ V‖_F² = ‖V Vᴴ‖_F²` via trace cyclicity. -/
lemma frobNormSq_gram_eq_frame (V : Matrix (Fin r) (Fin M) ℂ) :
    frobNormSq (Vᴴ * V) = frobNormSq (V * Vᴴ) := by
  rw [← trace_conjTranspose_mul_self_re (Vᴴ * V), ← trace_conjTranspose_mul_self_re (V * Vᴴ)]
  have h1 : (Vᴴ * V)ᴴ = Vᴴ * V := by simp [Matrix.conjTranspose_mul]
  have h2 : (V * Vᴴ)ᴴ = V * Vᴴ := by simp [Matrix.conjTranspose_mul]
  rw [h1, h2]
  have htr : ((Vᴴ * V) * (Vᴴ * V)).trace = ((V * Vᴴ) * (V * Vᴴ)).trace := by
    calc ((Vᴴ * V) * (Vᴴ * V)).trace
        = (Vᴴ * (V * Vᴴ * V)).trace := by simp [Matrix.mul_assoc]
      _ = ((V * Vᴴ * V) * Vᴴ).trace := Matrix.trace_mul_comm _ _
      _ = ((V * Vᴴ) * (V * Vᴴ)).trace := by simp [Matrix.mul_assoc]
  rw [htr]

/-- Mechanism A (General arbitrary-dimension deterministic Welch bound):
    for ANY complex matrix `V : Fin r × Fin M` with Gram matrix `G = Vᴴ V`,
    `(Re Tr G)² ≤ r · ‖G‖_F²`. -/
theorem welch_gram_general_bound (V : Matrix (Fin r) (Fin M) ℂ) :
    ((Vᴴ * V).trace.re) ^ 2 ≤ (r : ℝ) * frobNormSq (Vᴴ * V) := by
  let H : Matrix (Fin r) (Fin r) ℂ := V * Vᴴ
  have htr : (Vᴴ * V).trace = H.trace := Matrix.trace_mul_comm Vᴴ V
  have hfn : frobNormSq (Vᴴ * V) = frobNormSq H := frobNormSq_gram_eq_frame V
  rw [htr, hfn]
  -- Drop off-diagonal entries of H in frobNormSq H:
  have hdiag_le : (∑ a : Fin r, Complex.normSq (H a a)) ≤ frobNormSq H := by
    unfold frobNormSq
    refine Finset.sum_le_sum fun a _ => ?_
    exact Finset.single_le_sum (fun b _ => Complex.normSq_nonneg (H a b)) (Finset.mem_univ a)
  -- For diagonal entries, Im(H a a) = 0, so normSq (H a a) = (Re (H a a))²:
  have hdiag_sq : ∀ a : Fin r, Complex.normSq (H a a) = ((H a a).re) ^ 2 := by
    intro a
    rw [Complex.normSq_apply, mul_conjTranspose_diag_im V a]
    ring
  simp_rw [hdiag_sq] at hdiag_le
  -- Self-contained Cauchy-Schwarz on Fin r: (∑ a, f a)² ≤ r * ∑ a, (f a)² via ∑_{a,b} (f a - f b)² ≥ 0
  have hcs : (∑ a : Fin r, (H a a).re) ^ 2 ≤ (r : ℝ) * ∑ a : Fin r, ((H a a).re) ^ 2 := by
    let f : Fin r → ℝ := fun a => (H a a).re
    have hnn : 0 ≤ ∑ a : Fin r, ∑ b : Fin r, (f a - f b) ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hexp :
        (∑ a : Fin r, ∑ b : Fin r, (f a - f b) ^ 2) =
          2 * ((r : ℝ) * (∑ a : Fin r, (f a) ^ 2) - (∑ a : Fin r, f a) ^ 2) := by
      have hterm : ∀ a b : Fin r, (f a - f b) ^ 2 = (f a) ^ 2 - 2 * (f a * f b) + (f b) ^ 2 := by
        intro a b; ring
      simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      ring
    change (∑ a : Fin r, f a) ^ 2 ≤ (r : ℝ) * ∑ a : Fin r, (f a) ^ 2
    linarith
  have htr_re : H.trace.re = ∑ a : Fin r, (H a a).re := by
    rw [Matrix.trace, Complex.re_sum]
    rfl
  rw [htr_re]
  calc (∑ a : Fin r, (H a a).re) ^ 2
      ≤ (r : ℝ) * ∑ a : Fin r, ((H a a).re) ^ 2 := hcs
    _ ≤ (r : ℝ) * frobNormSq H := mul_le_mul_of_nonneg_left hdiag_le (Nat.cast_nonneg r)

/-- Mechanism A (Rank-forced off-diagonal branch crosstalk floor):
    for `M` unit-norm effective branches (`(Vᴴ V)_{xx} = 1`) mapped into `ℂ^r`,
    `M (M - r) ≤ r · ∑_{x ≠ y} |G_{xy}|²`, strictly positive whenever `M > r`. -/
theorem welch_rank_forced_branch_crosstalk
    (V : Matrix (Fin r) (Fin M) ℂ)
    (hUnit : ∀ x : Fin M, ((Vᴴ * V) x x).re = 1) :
    (M : ℝ) * ((M : ℝ) - (r : ℝ)) ≤
      (r : ℝ) * ∑ x : Fin M, ∑ y : Fin M, if x ≠ y then Complex.normSq ((Vᴴ * V) x y) else 0 := by
  have hgen := welch_gram_general_bound V
  have htrG : (Vᴴ * V).trace.re = (M : ℝ) := by
    rw [Matrix.trace, Complex.re_sum]
    have hdiag : ∀ x : Fin M, ((Vᴴ * V).diag x).re = 1 := fun x => hUnit x
    simp_rw [hdiag]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hsplit :
      frobNormSq (Vᴴ * V) = (M : ℝ) +
        ∑ x : Fin M, ∑ y : Fin M, if x ≠ y then Complex.normSq ((Vᴴ * V) x y) else 0 := by
    unfold frobNormSq
    have hrow : ∀ x : Fin M,
        (∑ y : Fin M, Complex.normSq ((Vᴴ * V) x y)) =
          1 + ∑ y : Fin M, if x ≠ y then Complex.normSq ((Vᴴ * V) x y) else 0 := by
      intro x
      have hdiag : Complex.normSq ((Vᴴ * V) x x) = 1 := by
        rw [Complex.normSq_apply, hUnit x, conjTranspose_mul_diag_im V x]
        ring
      have hadd := (Finset.add_sum_erase Finset.univ
        (fun y => Complex.normSq ((Vᴴ * V) x y)) (Finset.mem_univ x)).symm
      rw [hadd, hdiag]
      congr 1
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext y
      simp [Finset.mem_erase, Finset.mem_filter, ne_comm]
    simp_rw [hrow]
    rw [Finset.sum_add_distrib]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [htrG, hsplit] at hgen
  nlinarith

/-- Mechanism B (Oppenheim CQ `2×2` PSD decoherence–diffusion trade-off):
    the real quadratic form `2 D2 x² + 2 D1 x y + 2 D0 y²` is nonnegative for all `x, y ∈ ℝ`
    if and only if `D2 ≥ 0`, `D0 ≥ 0`, and `D1² ≤ 4 D2 D0`. -/
theorem oppenheim_cq_psd_tradeoff (D2 D1 D0 : ℝ) :
    (∀ x y : ℝ, 0 ≤ 2 * D2 * x ^ 2 + 2 * D1 * x * y + 2 * D0 * y ^ 2) ↔
      0 ≤ D2 ∧ 0 ≤ D0 ∧ D1 ^ 2 ≤ 4 * D2 * D0 := by
  constructor
  · intro h
    have hD2 : 0 ≤ D2 := by
      have h1 := h 1 0
      linarith
    have hD0 : 0 ≤ D0 := by
      have h1 := h 0 1
      linarith
    refine ⟨hD2, hD0, ?_⟩
    by_cases h2z : D2 = 0
    · subst h2z
      have hD1 : D1 = 0 := by
        by_contra hne
        have hbad := h (-((D0 + 1) / D1)) 1
        have hcalc : 2 * 0 * (-((D0 + 1) / D1)) ^ 2 + 2 * D1 * (-((D0 + 1) / D1)) * 1 + 2 * D0 * 1 ^ 2 = -2 := by
          field_simp [hne]; ring
        linarith
      rw [hD1]; norm_num
    · have h2pos : 0 < D2 := lt_of_le_of_ne hD2 (Ne.symm h2z)
      have hmin := h (-D1) (2 * D2)
      have hfact :
          2 * D2 * (-D1) ^ 2 + 2 * D1 * (-D1) * (2 * D2) + 2 * D0 * (2 * D2) ^ 2 =
            2 * D2 * (4 * D2 * D0 - D1 ^ 2) := by ring
      rw [hfact] at hmin
      nlinarith
  · rintro ⟨hD2, hD0, hDisc⟩ x y
    by_cases h2z : D2 = 0
    · subst h2z
      have hD1 : D1 = 0 := by nlinarith
      rw [hD1]
      nlinarith [sq_nonneg y]
    · have h2pos : 0 < D2 := lt_of_le_of_ne hD2 (Ne.symm h2z)
      have hcomp :
          2 * D2 * (2 * D2 * x ^ 2 + 2 * D1 * x * y + 2 * D0 * y ^ 2) =
            (2 * D2 * x + D1 * y) ^ 2 + (4 * D2 * D0 - D1 ^ 2) * y ^ 2 := by ring
      have hnonneg : 0 ≤ (2 * D2 * x + D1 * y) ^ 2 + (4 * D2 * D0 - D1 ^ 2) * y ^ 2 := by
        nlinarith [sq_nonneg (2 * D2 * x + D1 * y), sq_nonneg y]
      nlinarith

/-- Mechanism C (Multi-observer clock-dressed commutativity): locally clock-dressed operators
    on distinct observer sectors `O_A ⊗ I_B` and `I_A ⊗ O_B` commute identically. -/
theorem two_clock_dressed_commutativity
    (OA : Matrix (Fin dA) (Fin dA) ℂ) (OB : Matrix (Fin dB) (Fin dB) ℂ) :
    Matrix.kroneckerMap (· * ·) OA (1 : Matrix (Fin dB) (Fin dB) ℂ) *
      Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin dA) (Fin dA) ℂ) OB =
    Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin dA) (Fin dA) ℂ) OB *
      Matrix.kroneckerMap (· * ·) OA (1 : Matrix (Fin dB) (Fin dB) ℂ) := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

/-- Partial trace over the second factor `B` on `Fin dA × Fin dB`. -/
def partialTraceB (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :
    Matrix (Fin dA) (Fin dA) ℂ :=
  Matrix.of fun a a' => ∑ b : Fin dB, ρ (a, b) (a', b)

/-- Local CPTP spatial semicausality (R2, Beckman et al. 2001): any complete local Kraus channel
    `I_A ⊗ Φ_B` leaves Alice's reduced state `Tr_B(ρ)` strictly invariant for every bipartite `ρ`. -/
theorem local_channel_spatial_semicausality
    {k : ℕ}
    (Ks : Fin k → Matrix (Fin dB) (Fin dB) ℂ)
    (hComp : IsCompleteKraus Ks)
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :
    partialTraceB
      (∑ x : Fin k,
        Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin dA) (Fin dA) ℂ) (Ks x) * ρ *
          (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin dA) (Fin dA) ℂ) (Ks x))ᴴ) =
      partialTraceB ρ := by
  ext a a'
  rw [partialTraceB, partialTraceB, Matrix.of_apply, Matrix.of_apply]
  simp_rw [Matrix.sum_apply]
  have hentry : ∀ b : Fin dB, ∀ x : Fin k,
      (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin dA) (Fin dA) ℂ) (Ks x) * ρ *
        (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin dA) (Fin dA) ℂ) (Ks x))ᴴ) (a, b) (a', b) =
        ∑ b1 : Fin dB, ∑ b2 : Fin dB, Ks x b b1 * ρ (a, b1) (a', b2) * star (Ks x b b2) := by
    intro b x
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single a']
    · have hinner : ∀ b2 : Fin dB,
          (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin dA) (Fin dA) ℂ) (Ks x) * ρ) (a, b) (a', b2) =
            ∑ b1 : Fin dB, Ks x b b1 * ρ (a, b1) (a', b2) := by
        intro b2
        rw [Matrix.mul_apply, Fintype.sum_prod_type]
        rw [Finset.sum_eq_single a]
        · refine Finset.sum_congr rfl fun b1 _ => ?_
          simp [Matrix.kroneckerMap_apply]
        · intro a1 _ ha1
          refine Finset.sum_eq_zero fun b1 _ => ?_
          simp [Matrix.kroneckerMap_apply, Matrix.one_apply_ne (Ne.symm ha1)]
        · intro ha; exact absurd (Finset.mem_univ a) ha
      have hconj : ∀ b2 : Fin dB,
          (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin dA) (Fin dA) ℂ) (Ks x))ᴴ (a', b2) (a', b) =
            star (Ks x b b2) := by
        intro b2; simp [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply]
      simp_rw [hinner, hconj, Finset.sum_mul]
      rw [Finset.sum_comm]
    · intro a2 _ ha2
      refine Finset.sum_eq_zero fun b2 _ => ?_
      have h1 : (1 : Matrix (Fin dA) (Fin dA) ℂ) a' a2 = 0 := Matrix.one_apply_ne (Ne.symm ha2)
      simp [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, h1]
    · intro ha'; exact absurd (Finset.mem_univ a') ha'
  simp_rw [hentry]
  rw [Finset.sum_comm]
  have hcollapse :
      (∑ x : Fin k, ∑ b : Fin dB, ∑ b1 : Fin dB, ∑ b2 : Fin dB,
        Ks x b b1 * ρ (a, b1) (a', b2) * star (Ks x b b2)) =
      ∑ b1 : Fin dB, ∑ b2 : Fin dB,
        ((∑ x : Fin k, (Ks x)ᴴ * Ks x) b2 b1) * ρ (a, b1) (a', b2) := by
    have hx : ∀ x : Fin k,
        (∑ b : Fin dB, ∑ b1 : Fin dB, ∑ b2 : Fin dB,
          Ks x b b1 * ρ (a, b1) (a', b2) * star (Ks x b b2)) =
        ∑ b1 : Fin dB, ∑ b2 : Fin dB, (((Ks x)ᴴ * Ks x) b2 b1) * ρ (a, b1) (a', b2) := by
      intro x
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b1 _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b2 _ => ?_
      rw [Matrix.mul_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp [Matrix.conjTranspose_apply]; ring
    simp_rw [hx]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b1 _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b2 _ => ?_
    rw [Matrix.sum_apply, Finset.sum_mul]
  rw [hcollapse, hComp]
  refine Finset.sum_congr rfl fun b1 _ => ?_
  rw [Finset.sum_eq_single b1]
  · simp
  · intro b2 _ hb2; simp [Matrix.one_apply_ne hb2]
  · intro hb1; exact absurd (Finset.mem_univ b1) hb1

/-- Control 0' (R2 counterexample): the 2-qubit SWAP gate is unitary CPTP and Gisin
    ensemble-independent, yet violates spatial semicausality (`Tr_B(SWAP (|00⟩⟨00|) SWAPᴴ) = |0⟩⟨0|`
    while `Tr_B(SWAP (|01⟩⟨01|) SWAPᴴ) = |1⟩⟨1|`). -/
theorem swap_gate_ensemble_independent_yet_signaling :
    let SWAP : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      Matrix.of fun p q => if p.1 = q.2 ∧ p.2 = q.1 then 1 else 0
    let ρZ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      (2⁻¹ : ℂ) • Matrix.kroneckerMap (· * ·) projZero projZero +
      (2⁻¹ : ℂ) • Matrix.kroneckerMap (· * ·) projOne projZero
    let ρX : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      (2⁻¹ : ℂ) • Matrix.kroneckerMap (· * ·) projPlus projZero +
      (2⁻¹ : ℂ) • Matrix.kroneckerMap (· * ·) projMinus projZero
    SWAPᴴ * SWAP = 1 ∧
    SWAP * ρZ * SWAPᴴ = SWAP * ρX * SWAPᴴ ∧
    partialTraceB (SWAP * Matrix.kroneckerMap (· * ·) projZero projZero * SWAPᴴ) = projZero ∧
    partialTraceB (SWAP * Matrix.kroneckerMap (· * ·) projZero projOne * SWAPᴴ) = projOne ∧
    projZero ≠ projOne := by
  intro SWAP ρZ ρX
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext ⟨a, b⟩ ⟨c, d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [SWAP, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.conjTranspose_apply]
  · have hEq : ρZ = ρX := by
      ext ⟨a, b⟩ ⟨c, d⟩
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        norm_num [ρZ, ρX, projZero, projOne, projPlus, projMinus, Matrix.kroneckerMap_apply]
    rw [hEq]
  · ext a a'
    fin_cases a <;> fin_cases a' <;>
      simp [partialTraceB, SWAP, projZero, Matrix.mul_apply, Fintype.sum_prod_type,
        Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply]
  · ext a a'
    fin_cases a <;> fin_cases a' <;>
      simp [partialTraceB, SWAP, projZero, projOne, Matrix.mul_apply, Fintype.sum_prod_type,
        Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply]
  · intro h
    have h00 := congr_fun (congr_fun h 0) 0
    simp [projZero, projOne] at h00

/-- Trine ETF non-TP/non-TNI witness and normalized frame POVM identity (R2 & R3):
    for `V : ℝ^{2×3}` with three unit columns at `120°` (`r = 2, M = 3`),
    (i) every column has unit norm, (ii) `V Vᵀ = (3/2) I₂` (so normalized frame POVM
    `F_x = (2/3) |v_x⟩⟨v_x|` sums to `I₂`), (iii) on the unit-trace eigenstate `ρ_max`,
    `Tr(V ρ_max Vᵀ) = 3/2 > 1` (neither TP nor TNI), and (iv) `∑_x |G_{x0}|² = 3/2 > 1`. -/
theorem trine_frame_exceeds_unit_trace_and_povm_norm :
    let s3 : ℝ := Real.sqrt 3 / 2
    let V : Matrix (Fin 2) (Fin 3) ℝ :=
      !![1, -1/2, -1/2;
         0,   s3,  -s3]
    let ρmax : Matrix (Fin 3) (Fin 3) ℝ :=
      !![ 2/3, -1/3, -1/3;
         -1/3,  1/6,  1/6;
         -1/3,  1/6,  1/6]
    (∀ k : Fin 3, (Vᵀ * V) k k = 1) ∧
    V * Vᵀ = (3/2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    (2/3 : ℝ) • (V * Vᵀ) = (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    ρmax.trace = 1 ∧
    (V * ρmax * Vᵀ).trace = 3/2 ∧
    (∑ x : Fin 3, ((Vᵀ * V) x 0) ^ 2) = 3/2 := by
  intro s3 V ρmax
  have hs3 : s3 * s3 = 3 / 4 := by
    simp only [s3]
    have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    nlinarith
  have hVVT : V * Vᵀ = (3/2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [V, Matrix.mul_apply, Fin.sum_univ_three] <;>
      linarith [hs3]
  have hG : Vᵀ * V = !![1, -1/2, -1/2; -1/2, 1, -1/2; -1/2, -1/2, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [V, Matrix.mul_apply, Fin.sum_univ_two] <;>
      linarith [hs3]
  refine ⟨?_, hVVT, ?_, ?_, ?_, ?_⟩
  · intro k
    rw [hG]; fin_cases k <;> norm_num
  · rw [hVVT, smul_smul]; norm_num
  · norm_num [ρmax, Matrix.trace, Fin.sum_univ_three]
  · have hcyc : (V * ρmax * Vᵀ).trace = ((Vᵀ * V) * ρmax).trace := by
      calc (V * ρmax * Vᵀ).trace
          = (Vᵀ * (V * ρmax)).trace := Matrix.trace_mul_comm _ _
        _ = ((Vᵀ * V) * ρmax).trace := by rw [Matrix.mul_assoc]
    rw [hcyc, hG]
    norm_num [ρmax, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_three]
  · rw [hG]
    norm_num [Fin.sum_univ_three]

/-- Full-rank duplicated-frame counterexample (R3): for ANY `r ≥ 2` and `M > r`, placing
    `M - r + 1` copies of `e_0` followed by `e_1, …, e_{r-1}` gives a unit-column matrix
    `V_dup : ℝ^{r×M}` whose columns span all standard basis vectors (full row rank `r`),
    with exact off-diagonal Gram overlap sum `(M - r + 1)(M - r)`.
    At `(r, M) = (8, 64)`, `RMS² = 19/24 > 1/9 = Welch²`, disproving reading Welch's lower
    bound as a universal `O(r^{-1/2})` upper bound. -/
theorem full_rank_duplicated_frame_exceeds_welch_lower_bound
    (r M : ℕ) (hr : 2 ≤ r) (hM : r < M) :
    let Vdup : Matrix (Fin r) (Fin M) ℝ :=
      Matrix.of fun j x =>
        if j.val = 0 then (if x.val ≤ M - r then 1 else 0)
        else (if x.val = M - r + j.val then 1 else 0)
    (∀ x : Fin M, (Vdupᵀ * Vdup) x x = 1) ∧
    (∀ j : Fin r, ∃ x : Fin M, ∀ i : Fin r, Vdup i x = if i = j then 1 else 0) ∧
    (∑ x : Fin M, ∑ y : Fin M, if x ≠ y then ((Vdupᵀ * Vdup) x y) ^ 2 else 0) =
      ((M - r + 1 : ℕ) : ℝ) * ((M - r : ℕ) : ℝ) ∧
    ((57 : ℝ) * 56) / (64 * 63) > (64 - 8 : ℝ) / (8 * 63) := by
  intro Vdup
  have hcol : ∀ x : Fin M, ∃ j : Fin r, ∀ i : Fin r, Vdup i x = if i = j then 1 else 0 := by
    intro x
    have hxlt := x.isLt
    by_cases hx : x.val ≤ M - r
    · refine ⟨⟨0, by omega⟩, fun i => ?_⟩
      by_cases hi : i.val = 0
      · have hieq : i = ⟨0, by omega⟩ := Fin.ext hi
        simp only [Vdup, Matrix.of_apply, hx, hieq, ite_true]
      · have hine : i ≠ ⟨0, by omega⟩ := fun h => hi (congr_arg Fin.val h)
        have hne_x : x.val ≠ M - r + i.val := by omega
        simp only [Vdup, Matrix.of_apply, hi, hine, hne_x, ite_false]
    · refine ⟨⟨x.val - (M - r), by omega⟩, fun i => ?_⟩
      by_cases hi : i.val = 0
      · have hine : i ≠ ⟨x.val - (M - r), by omega⟩ := fun h => by
          have hv := congr_arg Fin.val h; dsimp only at hv; omega
        simp only [Vdup, Matrix.of_apply, hi, hx, hine, ite_true, ite_false]
      · by_cases heq : i.val = x.val - (M - r)
        · have hieq : i = ⟨x.val - (M - r), by omega⟩ := Fin.ext heq
          have hxv : x.val = M - r + i.val := by omega
          conv_rhs => simp only [hieq, ite_true]
          simp only [Vdup, Matrix.of_apply, hi, hxv, ite_false, ite_true]
        · have hine : i ≠ ⟨x.val - (M - r), by omega⟩ := fun h => heq (congr_arg Fin.val h)
          have hxv : x.val ≠ M - r + i.val := by omega
          simp only [Vdup, Matrix.of_apply, hi, hine, hxv, ite_false]
  have hGram : ∀ x y : Fin M,
      (Vdupᵀ * Vdup) x y =
        if x = y then 1
        else if x.val ≤ M - r ∧ y.val ≤ M - r then 1 else 0 := by
    intro x y
    rw [Matrix.mul_apply]
    simp_rw [Matrix.transpose_apply]
    by_cases hxy : x = y
    · subst hxy
      rcases hcol x with ⟨j, hj⟩
      simp_rw [hj]
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij; simp [hij]
      · intro hj'; exact absurd (Finset.mem_univ j) hj'
    · by_cases hboth : x.val ≤ M - r ∧ y.val ≤ M - r
      · simp only [hxy, hboth, and_self, ite_false, ite_true]
        rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin r)]
        · simp only [Vdup, Matrix.of_apply, hboth.1, hboth.2, ite_true, mul_one]
        · intro i _ hi
          have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
          have hnx : x.val ≠ M - r + i.val := by omega
          simp only [Vdup, Matrix.of_apply, hi0, hnx, ite_false, zero_mul]
        · intro h0; exact absurd (Finset.mem_univ _) h0
      · simp only [hxy, hboth, ite_false]
        refine Finset.sum_eq_zero fun i _ => ?_
        by_cases hi0 : i.val = 0
        · simp only [Vdup, Matrix.of_apply, hi0, ite_true]
          by_cases hx : x.val ≤ M - r
          · have hy : ¬ y.val ≤ M - r := fun hy => hboth ⟨hx, hy⟩
            simp [hx, hy]
          · simp [hx]
        · simp only [Vdup, Matrix.of_apply, hi0, ite_false]
          by_cases hx : x.val = M - r + i.val
          · have hy : y.val ≠ M - r + i.val := fun hy => hxy (Fin.ext (by omega))
            simp [hx, hy]
          · simp [hx]
  refine ⟨?_, ?_, ?_, by norm_num⟩
  · intro x; rw [hGram x x]; simp
  · intro j
    have hjlt := j.isLt
    by_cases hj : j.val = 0
    · refine ⟨⟨0, by omega⟩, fun i => ?_⟩
      by_cases hi : i.val = 0
      · have hieq : i = j := Fin.ext (by omega)
        have h0le : (0 : ℕ) ≤ M - r := Nat.zero_le _
        simp only [Vdup, Matrix.of_apply, hieq, hj, h0le, ite_true]
      · have hine : i ≠ j := fun h => hi (by rw [h]; exact hj)
        have hne0 : (0 : ℕ) ≠ M - r + i.val := by omega
        simp only [Vdup, Matrix.of_apply, hi, hine, hne0, ite_false]
    · refine ⟨⟨M - r + j.val, by omega⟩, fun i => ?_⟩
      by_cases hi : i.val = 0
      · have hine : i ≠ j := fun h => hj (by rw [← h]; exact hi)
        have hnot : ¬ (M - r + j.val ≤ M - r) := by omega
        simp only [Vdup, Matrix.of_apply, hi, hine, hnot, ite_true, ite_false]
      · by_cases hij : i = j
        · subst hij
          simp only [Vdup, Matrix.of_apply, hi, ite_false, ite_true]
        · have hneq : M - r + j.val ≠ M - r + i.val := fun h =>
            hij (Fin.ext (by omega))
          simp only [Vdup, Matrix.of_apply, hi, hij, hneq, ite_false]
  · let S : Finset (Fin M) := Finset.univ.filter (fun x : Fin M => x.val ≤ M - r)
    have hcard : S.card = M - r + 1 := by
      have hbij : S = (Finset.range (M - r + 1)).attach.image
          (fun k => (⟨k.val, by have := Finset.mem_range.mp k.property; omega⟩ : Fin M)) := by
        ext x
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
          Finset.mem_attach, true_and, Subtype.exists, Finset.mem_range]
        constructor
        · intro hx; exact ⟨x.val, by omega, Fin.ext rfl⟩
        · rintro ⟨k, hk, rfl⟩; dsimp only; omega
      rw [hbij, Finset.card_image_of_injective]
      · simp
      · intro a b hab
        exact Subtype.ext (congr_arg Fin.val hab)
    have hterm : ∀ x y : Fin M,
        (if x ≠ y then ((Vdupᵀ * Vdup) x y) ^ 2 else 0) =
          if x ∈ S ∧ y ∈ S ∧ x ≠ y then (1 : ℝ) else 0 := by
      intro x y
      by_cases hxy : x = y
      · simp [hxy]
      · rw [hGram x y]
        simp only [hxy, ite_false, S, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq,
          not_false_eq_true, and_true]
        split_ifs <;> norm_num
    simp_rw [hterm]
    have hrow : ∀ x : Fin M,
        (∑ y : Fin M, if x ∈ S ∧ y ∈ S ∧ x ≠ y then (1 : ℝ) else 0) =
          if x ∈ S then ((S.card : ℝ) - 1) else 0 := by
      intro x
      by_cases hx : x ∈ S
      · simp only [hx, true_and, ite_true]
        have hflt : (∑ y : Fin M, if y ∈ S ∧ x ≠ y then (1 : ℝ) else 0) =
            ((S.erase x).card : ℝ) := by
          rw [← Finset.sum_filter]
          have hfeq : Finset.univ.filter (fun y : Fin M => y ∈ S ∧ x ≠ y) = S.erase x := by
            ext y; simp [Finset.mem_erase, ne_comm, and_comm]
          rw [hfeq, Finset.sum_const, nsmul_eq_mul, mul_one]
        rw [hflt, Finset.card_erase_of_mem hx, Nat.cast_sub (Finset.one_le_card.mpr ⟨x, hx⟩),
          Nat.cast_one]
      · simp [hx]
    simp_rw [hrow]
    rw [← Finset.sum_filter]
    have hfeq : Finset.univ.filter (fun x : Fin M => x ∈ S) = S := by
      ext x; simp
    rw [hfeq, Finset.sum_const, nsmul_eq_mul, hcard]
    push_cast
    ring

/-- Exact `C_tot = 0` finite-dimensional bipolar-clock model (R6):
    for arbitrary half-width `m ≥ 1` (`K = 2 m + 1`, clock spectrum `{-m, …, +m}` and system
    spectrum `{0, 1}`), the total Hamiltonian constraint `C_tot = H_{S_A} + H_{C_A} + H_{S_B} + H_{C_B}`
    satisfies:
    (1) `C_tot |ψ_ent⟩ = 0` for the maximally entangled clock state `∑_q |0, q, 0, -q⟩`,
    (2) `C_tot |ψ_prod⟩ = 0` for the unentangled product state `|0, 0, 0, 0⟩` (constraint permits
        but does not force entanglement),
    (3)-(5) non-wrapping dressed excitation operators `O_A^{ex}, O_B^{ex}` satisfy exact
        `[C_tot, O_A^{ex}] = 0`, `[C_tot, O_B^{ex}] = 0`, and `[O_A^{ex}, O_B^{ex}] = 0` on the
        entire Hilbert space, and
    (6) `O_A^{ex} |ψ_ent⟩ ≠ 0` (nontrivial action preserving `ker C_tot`). -/
theorem exact_bipolar_clock_constraint_entangled_and_product (m : ℕ) (hm : 1 ≤ m) :
    let K := 2 * m + 1
    let energy : (Fin 2 × Fin K) × (Fin 2 × Fin K) → ℝ := fun idx =>
      (idx.1.1.val : ℝ) + ((idx.1.2.val : ℝ) - (m : ℝ)) +
      (idx.2.1.val : ℝ) + ((idx.2.2.val : ℝ) - (m : ℝ))
    let Ctot : Matrix ((Fin 2 × Fin K) × (Fin 2 × Fin K))
        ((Fin 2 × Fin K) × (Fin 2 × Fin K)) ℝ := Matrix.diagonal energy
    let Lclock : Matrix (Fin K) (Fin K) ℝ :=
      Matrix.of fun q q' => if q.val + 1 = q'.val then 1 else 0
    let raiseS : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
    let OA : Matrix ((Fin 2 × Fin K) × (Fin 2 × Fin K))
        ((Fin 2 × Fin K) × (Fin 2 × Fin K)) ℝ :=
      Matrix.kroneckerMap (· * ·) (Matrix.kroneckerMap (· * ·) raiseS Lclock) 1
    let OB : Matrix ((Fin 2 × Fin K) × (Fin 2 × Fin K))
        ((Fin 2 × Fin K) × (Fin 2 × Fin K)) ℝ :=
      Matrix.kroneckerMap (· * ·) 1 (Matrix.kroneckerMap (· * ·) raiseS Lclock)
    let ψEnt : (Fin 2 × Fin K) × (Fin 2 × Fin K) → ℝ := fun idx =>
      if idx.1.1.val = 0 ∧ idx.2.1.val = 0 ∧ idx.1.2.val + idx.2.2.val = 2 * m then 1 else 0
    let ψProd : (Fin 2 × Fin K) × (Fin 2 × Fin K) → ℝ := fun idx =>
      if idx.1.1.val = 0 ∧ idx.2.1.val = 0 ∧ idx.1.2.val = m ∧ idx.2.2.val = m then 1 else 0
    Ctot.mulVec ψEnt = 0 ∧
    Ctot.mulVec ψProd = 0 ∧
    Ctot * OA = OA * Ctot ∧
    Ctot * OB = OB * Ctot ∧
    OA * OB = OB * OA ∧
    OA.mulVec ψEnt ≠ 0 := by
  intro K energy Ctot Lclock raiseS OA OB ψEnt ψProd
  have hRaise : ∀ a b : Fin 2, raiseS a b ≠ 0 → a.val = 1 ∧ b.val = 0 := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp [raiseS] at hab ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext idx
    simp only [Ctot, Matrix.mulVec_diagonal, Pi.zero_apply, ψEnt]
    split_ifs with h
    · rcases h with ⟨h1, h2, h3⟩
      have hcast : (idx.1.2.val : ℝ) + (idx.2.2.val : ℝ) = 2 * (m : ℝ) := by
        exact_mod_cast h3
      simp only [energy, h1, h2, Nat.cast_zero]
      linarith
    · ring
  · ext idx
    simp only [Ctot, Matrix.mulVec_diagonal, Pi.zero_apply, ψProd]
    split_ifs with h
    · rcases h with ⟨h1, h2, h3, h4⟩
      simp only [energy, h1, h2, h3, h4, Nat.cast_zero]
      ring
    · ring
  · ext p q
    simp only [Ctot, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases h0 : OA p q = 0
    · simp [h0]
    · have hspec : p.1.1.val = 1 ∧ q.1.1.val = 0 ∧ p.1.2.val + 1 = q.1.2.val ∧ p.2 = q.2 := by
        simp only [OA, Matrix.kroneckerMap_apply, Matrix.one_apply] at h0
        have hp2 : p.2 = q.2 := by
          by_contra hne; simp [hne] at h0
        have hleft : raiseS p.1.1 q.1.1 * Lclock p.1.2 q.1.2 ≠ 0 := by
          intro hz; simp [hz] at h0
        have hS := hRaise p.1.1 q.1.1 (left_ne_zero_of_mul hleft)
        have hL : Lclock p.1.2 q.1.2 ≠ 0 := right_ne_zero_of_mul hleft
        have hLval : p.1.2.val + 1 = q.1.2.val := by
          by_contra hne; simp [Lclock, hne] at hL
        exact ⟨hS.1, hS.2, hLval, hp2⟩
      have heeq : energy p = energy q := by
        rcases hspec with ⟨hp1, hq1, hq2, hp2⟩
        have hcast : (p.1.2.val : ℝ) + 1 = (q.1.2.val : ℝ) := by exact_mod_cast hq2
        simp only [energy, hp1, hq1, hp2, Nat.cast_one, Nat.cast_zero]
        linarith
      rw [heeq]; ring
  · ext p q
    simp only [Ctot, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases h0 : OB p q = 0
    · simp [h0]
    · have hspec : p.2.1.val = 1 ∧ q.2.1.val = 0 ∧ p.2.2.val + 1 = q.2.2.val ∧ p.1 = q.1 := by
        simp only [OB, Matrix.kroneckerMap_apply, Matrix.one_apply] at h0
        have hp1 : p.1 = q.1 := by
          by_contra hne; simp [hne] at h0
        have hright : raiseS p.2.1 q.2.1 * Lclock p.2.2 q.2.2 ≠ 0 := by
          intro hz; simp [hz] at h0
        have hS := hRaise p.2.1 q.2.1 (left_ne_zero_of_mul hright)
        have hL : Lclock p.2.2 q.2.2 ≠ 0 := right_ne_zero_of_mul hright
        have hLval : p.2.2.val + 1 = q.2.2.val := by
          by_contra hne; simp [Lclock, hne] at hL
        exact ⟨hS.1, hS.2, hLval, hp1⟩
      have heeq : energy p = energy q := by
        rcases hspec with ⟨hp1, hq1, hq2, hp2⟩
        have hcast : (p.2.2.val : ℝ) + 1 = (q.2.2.val : ℝ) := by exact_mod_cast hq2
        simp only [energy, hp1, hq1, hp2, Nat.cast_one, Nat.cast_zero]
        linarith
      rw [heeq]; ring
  · simp only [OA, OB]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp
  · intro hzero
    let p0 : (Fin 2 × Fin K) × (Fin 2 × Fin K) :=
      ((⟨1, by omega⟩, ⟨m - 1, by omega⟩), (⟨0, by omega⟩, ⟨m, by omega⟩))
    let q0 : (Fin 2 × Fin K) × (Fin 2 × Fin K) :=
      ((⟨0, by omega⟩, ⟨m, by omega⟩), (⟨0, by omega⟩, ⟨m, by omega⟩))
    have hp0 := congr_fun hzero p0
    rw [Matrix.mulVec, dotProduct, Pi.zero_apply] at hp0
    have hsum : (∑ q, OA p0 q * ψEnt q) = 1 := by
      rw [Finset.sum_eq_single q0]
      · have hm1 : m - 1 + 1 = m := by omega
        have hm2 : m + m = 2 * m := by omega
        simp [OA, raiseS, Lclock, ψEnt, p0, q0, Matrix.kroneckerMap_apply, hm1, hm2]
      · intro q _ hq
        rcases q with ⟨⟨q11, q12⟩, q2⟩
        by_cases h2 : p0.2 = q2
        · by_cases hs : q11 = ⟨0, by omega⟩
          · by_cases hl : m - 1 + 1 = q12.val
            · exfalso
              apply hq
              apply Prod.ext
              · apply Prod.ext
                · exact hs
                · exact Fin.ext (by dsimp only [q0]; omega)
              · exact h2.symm
            · simp [OA, Lclock, p0, Matrix.kroneckerMap_apply, hl]
          · fin_cases q11
            · exact absurd rfl hs
            · simp [OA, raiseS, p0, Matrix.kroneckerMap_apply]
        · have h1 : (1 : Matrix (Fin 2 × Fin K) (Fin 2 × Fin K) ℝ) p0.2 q2 = 0 :=
            Matrix.one_apply_ne h2
          simp only [OA, Matrix.kroneckerMap_apply, h1, mul_zero, zero_mul]
      · intro hq0; exact absurd (Finset.mem_univ q0) hq0
    linarith

/-- Exact `C_tot = 0` bipolar-clock local CPTP channel completion (RR-6):
    for any half-width `m ≥ 1` (`K = 2 m + 1`), pairing the local excitation Kraus operator
    `K₁ = |1⟩⟨0| ⊗ L_C` with the complementary projector
    `K₀ = |1⟩⟨1| ⊗ I_C + |0⟩⟨0| ⊗ |-m⟩⟨-m|` yields a genuine local CPTP channel
    `Φ_A^{ex}(ρ) = (K₀ ⊗ I_B) ρ (K₀ ⊗ I_B)ᵀ + (K₁ ⊗ I_B) ρ (K₁ ⊗ I_B)ᵀ` satisfying:
    (1) exact Kraus completeness `K₀ᵀ K₀ + K₁ᵀ K₁ = 1` on `S_A ⊗ C_A`,
    (2) exact total-constraint commutation `[C_tot, K₀ ⊗ I_B] = 0`, and
    (3) exact total-constraint commutation `[C_tot, K₁ ⊗ I_B] = 0`. -/
theorem exact_bipolar_clock_cptp_channel_completion (m : ℕ) (hm : 1 ≤ m) :
    let K := 2 * m + 1
    let energy : (Fin 2 × Fin K) × (Fin 2 × Fin K) → ℝ := fun idx =>
      (idx.1.1.val : ℝ) + ((idx.1.2.val : ℝ) - (m : ℝ)) +
      (idx.2.1.val : ℝ) + ((idx.2.2.val : ℝ) - (m : ℝ))
    let Ctot : Matrix ((Fin 2 × Fin K) × (Fin 2 × Fin K))
        ((Fin 2 × Fin K) × (Fin 2 × Fin K)) ℝ := Matrix.diagonal energy
    let Lclock : Matrix (Fin K) (Fin K) ℝ :=
      Matrix.of fun q q' => if q.val + 1 = q'.val then 1 else 0
    let raiseS : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
    let P0S : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
    let P1S : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 1]
    let Pbot : Matrix (Fin K) (Fin K) ℝ :=
      Matrix.of fun q q' => if q.val = 0 ∧ q'.val = 0 then 1 else 0
    let K1loc : Matrix (Fin 2 × Fin K) (Fin 2 × Fin K) ℝ :=
      Matrix.kroneckerMap (· * ·) raiseS Lclock
    let K0loc : Matrix (Fin 2 × Fin K) (Fin 2 × Fin K) ℝ :=
      Matrix.kroneckerMap (· * ·) P1S 1 + Matrix.kroneckerMap (· * ·) P0S Pbot
    let K0full : Matrix ((Fin 2 × Fin K) × (Fin 2 × Fin K))
        ((Fin 2 × Fin K) × (Fin 2 × Fin K)) ℝ :=
      Matrix.kroneckerMap (· * ·) K0loc 1
    let K1full : Matrix ((Fin 2 × Fin K) × (Fin 2 × Fin K))
        ((Fin 2 × Fin K) × (Fin 2 × Fin K)) ℝ :=
      Matrix.kroneckerMap (· * ·) K1loc 1
    K0locᵀ * K0loc + K1locᵀ * K1loc = 1 ∧
    Ctot * K0full = K0full * Ctot ∧
    Ctot * K1full = K1full * Ctot := by
  intro K energy Ctot Lclock raiseS P0S P1S Pbot K1loc K0loc K0full K1full
  have hK0_entry : ∀ (p q : Fin 2 × Fin K),
      K0loc p q = if p = q ∧ (p.1.val = 1 ∨ p.2.val = 0) then 1 else 0 := by
    intro ⟨a, q⟩ ⟨a', q'⟩
    simp only [K0loc, Matrix.add_apply, Matrix.kroneckerMap_apply, P1S, P0S, Pbot, Matrix.of_apply,
      Matrix.one_apply, Prod.mk.injEq]
    fin_cases a <;> fin_cases a'
    · by_cases hq : q = q'
      · subst hq
        by_cases h0 : q.val = 0 <;> simp [h0]
      · simp [hq]
        intro h1 h2
        exact hq (h1.trans h2.symm)
    · simp
    · simp
    · by_cases hq : q = q' <;> simp [hq]
  have hLL : ∀ q q' : Fin K,
      (Lclockᵀ * Lclock) q q' = if q = q' ∧ q.val ≠ 0 then 1 else 0 := by
    intro q q'
    rw [Matrix.mul_apply]
    simp_rw [Matrix.transpose_apply, Lclock, Matrix.of_apply]
    by_cases h0 : q.val = 0
    · simp only [h0, ne_eq, not_true_eq_false, and_false, ite_false]
      refine Finset.sum_eq_zero fun r _ => ?_
      simp
    · have hqlt := q.isLt
      let r0 : Fin K := ⟨q.val - 1, by omega⟩
      rw [Finset.sum_eq_single r0]
      · have hr0 : r0.val + 1 = q.val := by dsimp only [r0]; omega
        by_cases hqq : q = q'
        · subst hqq
          simp [hr0, h0]
        · have hvalne : q.val ≠ q'.val := fun h => hqq (Fin.ext h)
          simp [hr0, hqq, hvalne]
      · intro r _ hr
        have hne : r.val + 1 ≠ q.val := fun h => hr (Fin.ext (by dsimp only [r0]; omega))
        simp [hne]
      · intro hr0; exact absurd (Finset.mem_univ r0) hr0
  have hRR : raiseSᵀ * raiseS = P0S := by
    ext a a'; fin_cases a <;> fin_cases a' <;>
      simp [raiseS, P0S, Matrix.mul_apply, Fin.sum_univ_two]
  have hK1T : K1locᵀ = Matrix.kroneckerMap (· * ·) raiseSᵀ Lclockᵀ := by
    ext ⟨a1, q1⟩ ⟨a2, q2⟩
    simp [K1loc, Matrix.kroneckerMap_apply]
  have hK1_sq : ∀ (p q : Fin 2 × Fin K),
      (K1locᵀ * K1loc) p q = if p = q ∧ p.1.val = 0 ∧ p.2.val ≠ 0 then 1 else 0 := by
    intro ⟨a, q⟩ ⟨a', q'⟩
    have hmul : K1locᵀ * K1loc = Matrix.kroneckerMap (· * ·) (raiseSᵀ * raiseS) (Lclockᵀ * Lclock) := by
      rw [hK1T]
      exact (Matrix.mul_kronecker_mul raiseSᵀ raiseS Lclockᵀ Lclock).symm
    rw [hmul, hRR, Matrix.kroneckerMap_apply, hLL]
    simp only [P0S, Prod.mk.injEq]
    fin_cases a <;> fin_cases a'
    · by_cases h : q = q' ∧ q.val ≠ 0 <;> simp [h]
    · simp
    · simp
    · simp
  refine ⟨?_, ?_, ?_⟩
  · ext p q
    rw [Matrix.add_apply, hK1_sq p q]
    have hK0_sq : (K0locᵀ * K0loc) p q = if p = q ∧ (p.1.val = 1 ∨ p.2.val = 0) then 1 else 0 := by
      rw [Matrix.mul_apply]
      simp_rw [Matrix.transpose_apply, hK0_entry]
      rw [Finset.sum_eq_single p]
      · by_cases hpq : p = q
        · subst hpq
          split_ifs <;> ring
        · simp [hpq]
      · intro r _ hr
        simp only [hr, false_and, ite_false, zero_mul]
      · intro hp; exact absurd (Finset.mem_univ p) hp
    rw [hK0_sq, Matrix.one_apply]
    by_cases hpq : p = q
    · subst hpq
      rcases p with ⟨a, q0⟩
      fin_cases a
      · by_cases h0 : q0.val = 0 <;> simp [h0]
      · simp
    · simp [hpq]
  · ext p q
    simp only [Ctot, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hpq : p = q
    · subst hpq; ring
    · have h0 : K0full p q = 0 := by
        simp only [K0full, Matrix.kroneckerMap_apply, hK0_entry, Matrix.one_apply]
        by_cases h1 : p.1 = q.1
        · have h2 : p.2 ≠ q.2 := fun h2 => hpq (Prod.ext h1 h2)
          simp [h2]
        · simp [h1]
      simp [h0]
  · exact (exact_bipolar_clock_constraint_entangled_and_product m hm).2.2.1

/-- Local constraint-commuting dephasing invariance in the exact `C_tot = 0` bipolar-clock model:
    for arbitrary half-width `m : ℕ` (`K = 2 m + 1`), if local operators `O_A, O_B` commute with
    their respective local constraints `C_A = H_{S_A} + H_{C_A}` and `C_B = H_{S_B} + H_{C_B}`,
    then `⟨0, q' | O_A | 0, q⟩ = 0` and `⟨0, q' | O_B | 0, q⟩ = 0` whenever `q' ≠ q`, so the
    maximally entangled clock state `|ψ_ent⟩ = (1/√K) ∑_q |0, q, 0, -q⟩` and its `q`-dephased
    classical mixture `(1/K) ∑_q |0, q, 0, -q⟩⟨0, q, 0, -q|` yield identical expectation values
    for every product `O_A ⊗ O_B`. -/
theorem bipolar_clock_local_constraint_commuting_dephasing_invariance
    (m : ℕ)
    (OA OB : Matrix (Fin 2 × Fin (2 * m + 1)) (Fin 2 × Fin (2 * m + 1)) ℂ)
    (hCommA :
      Matrix.diagonal (fun idx : Fin 2 × Fin (2 * m + 1) =>
        ((idx.1.val : ℂ) + ((idx.2.val : ℂ) - (m : ℂ)))) * OA =
      OA * Matrix.diagonal (fun idx : Fin 2 × Fin (2 * m + 1) =>
        ((idx.1.val : ℂ) + ((idx.2.val : ℂ) - (m : ℂ)))))
    (hCommB :
      Matrix.diagonal (fun idx : Fin 2 × Fin (2 * m + 1) =>
        ((idx.1.val : ℂ) + ((idx.2.val : ℂ) - (m : ℂ)))) * OB =
      OB * Matrix.diagonal (fun idx : Fin 2 × Fin (2 * m + 1) =>
        ((idx.1.val : ℂ) + ((idx.2.val : ℂ) - (m : ℂ))))) :
    let K := 2 * m + 1
    let opp : Fin K → Fin K := fun q => ⟨2 * m - q.val, by omega⟩
    let ψEnt : (Fin 2 × Fin K) × (Fin 2 × Fin K) → ℂ := fun idx =>
      if idx.1.1 = 0 ∧ idx.2.1 = 0 ∧ idx.1.2.val + idx.2.2.val = 2 * m then 1 else 0
    let OAB : Matrix ((Fin 2 × Fin K) × (Fin 2 × Fin K))
        ((Fin 2 × Fin K) × (Fin 2 × Fin K)) ℂ :=
      Matrix.kroneckerMap (· * ·) OA OB
    (∀ q q' : Fin K, q' ≠ q → OA (0, q') (0, q) = 0) ∧
    (∀ q q' : Fin K, q' ≠ q → OB (0, q') (0, q) = 0) ∧
    dotProduct (star ψEnt) (OAB.mulVec ψEnt) / (K : ℂ) =
      (∑ q : Fin K, OA (0, q) (0, q) * OB (0, opp q) (0, opp q)) / (K : ℂ) := by
  intro K opp ψEnt OAB
  have hOff : ∀ (O : Matrix (Fin 2 × Fin K) (Fin 2 × Fin K) ℂ),
      Matrix.diagonal (fun idx : Fin 2 × Fin K =>
        ((idx.1.val : ℂ) + ((idx.2.val : ℂ) - (m : ℂ)))) * O =
      O * Matrix.diagonal (fun idx : Fin 2 × Fin K =>
        ((idx.1.val : ℂ) + ((idx.2.val : ℂ) - (m : ℂ)))) →
      ∀ q q' : Fin K, q' ≠ q → O (0, q') (0, q) = 0 := by
    intro O hComm q q' hne
    have hent := congr_fun (congr_fun hComm (0, q')) (0, q)
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Fin.val_zero, Nat.cast_zero, zero_add] at hent
    have hdiff : ((q'.val : ℂ) - (q.val : ℂ)) * O (0, q') (0, q) = 0 := by
      linear_combination hent
    have hqne : (q'.val : ℂ) - (q.val : ℂ) ≠ 0 := by
      intro h0
      have hcast : (q'.val : ℂ) = (q.val : ℂ) := sub_eq_zero.mp h0
      exact hne (Fin.ext (Nat.cast_injective hcast))
    exact (mul_eq_zero.mp hdiff).resolve_left hqne
  have hOffA := hOff OA hCommA
  have hOffB := hOff OB hCommB
  refine ⟨hOffA, hOffB, ?_⟩
  congr 1
  have hψ_iff : ∀ (sA sB : Fin 2) (qA qB : Fin K),
      (sA = 0 ∧ sB = 0 ∧ qA.val + qB.val = 2 * m) ↔
      (sA = 0 ∧ sB = 0 ∧ qB = opp qA) := by
    intro sA sB qA qB
    have hqAlt := qA.isLt
    have hqBlt := qB.isLt
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, Fin.ext ?_⟩
      dsimp only [opp]; omega
    · rintro ⟨h1, h2, h3⟩
      have hv : qB.val = 2 * m - qA.val := by
        have := congr_arg Fin.val h3; dsimp only [opp] at this; exact this
      refine ⟨h1, h2, ?_⟩
      omega
  have hInner : ∀ qA : Fin K,
      OAB.mulVec ψEnt ((0, qA), (0, opp qA)) =
        OA (0, qA) (0, qA) * OB (0, opp qA) (0, opp qA) := by
    intro qA
    rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single ((0, qA), (0, opp qA))]
    · have hself : (0 : Fin 2) = 0 ∧ (0 : Fin 2) = 0 ∧ qA.val + (opp qA).val = 2 * m := by
        dsimp only [opp]; have := qA.isLt; exact ⟨rfl, rfl, by omega⟩
      simp only [OAB, ψEnt, Matrix.kroneckerMap_apply, hself, and_self, ite_true, mul_one]
    · intro jdx _ hjne
      rcases jdx with ⟨⟨tA, rA⟩, ⟨tB, rB⟩⟩
      by_cases hj : tA = 0 ∧ tB = 0 ∧ rA.val + rB.val = 2 * m
      · have hj' := (hψ_iff tA tB rA rB).mp hj
        rcases hj' with ⟨htA, htB, hrB⟩
        subst htA; subst htB; subst hrB
        have hrne : qA ≠ rA := by
          intro hq; subst hq; exact hjne rfl
        simp only [OAB, Matrix.kroneckerMap_apply, hOffA rA qA hrne, zero_mul]
      · simp only [ψEnt, hj, ite_false, mul_zero]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  rw [dotProduct, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, Pi.star_apply]
  rw [Finset.sum_eq_single (0 : Fin 2)]
  · refine Finset.sum_congr rfl fun qA _ => ?_
    rw [Finset.sum_eq_single (0 : Fin 2)]
    · rw [Finset.sum_eq_single (opp qA)]
      · have hself : (0 : Fin 2) = 0 ∧ (0 : Fin 2) = 0 ∧ qA.val + (opp qA).val = 2 * m := by
          dsimp only [opp]; have := qA.isLt; exact ⟨rfl, rfl, by omega⟩
        simp only [ψEnt, hself, and_self, ite_true, star_one, one_mul]
        exact hInner qA
      · intro qB _ hqB
        have hnot : qA.val + qB.val ≠ 2 * m := fun h => hqB ((hψ_iff 0 0 qA qB).mp ⟨rfl, rfl, h⟩).2.2
        simp [ψEnt, hnot]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    · intro sB _ hsB
      refine Finset.sum_eq_zero fun qB _ => ?_
      simp [ψEnt, hsB]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  · intro sA _ hsA
    refine Finset.sum_eq_zero fun qA _ => Finset.sum_eq_zero fun sB _ =>
      Finset.sum_eq_zero fun qB _ => ?_
    have hnot : ¬ (sA = 0 ∧ sB = 0 ∧ qA.val + qB.val = 2 * m) := fun h => hsA h.1
    simp only [ψEnt, hnot, ite_false, star_zero, zero_mul]
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

end OSTQD_Layer2
