import OSTQD.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# OSTQD.Theorem3_CrossPerspective

Theorem 3:
  (a) Exact 3-party maximally-entangled projection algebra `P_A P_B P_A = (1/d²) P_A`
      on `(ℂ^d)⊗³` for arbitrary `d ≥ 1`.
  (b) Sharp universal Joint-Extension Monogamy Bound:
      for every normalized state `ψ` on `H_R ⊗ H_{A'} ⊗ H_{B'}` (and hence every density
      matrix mixture), `F_A(ψ) + F_B(ψ) ≤ 1 + 1/d`, ruling out simultaneous faithful
      recovery (`F_A = F_B = 1`) whenever `d ≥ 2`.
  (c) Constructive Observer-Separated Channels with Cross-Perspective Consistency (CPL):
      horizon-separated observers simultaneously attain `F_A = 1`, `F_B = 1`
      (`F_A + F_B = 2 > 1 + 1/d`) while agreeing identically on all shared overlap observables.
-/

open scoped Matrix BigOperators ComplexConjugate

namespace OSTQD

section JointExtension

variable (d : ℕ)

abbrev TriIdx (d : ℕ) := Fin d × Fin d × Fin d

/-- Maximally entangled projector `P_A = |Φ⁺⟩⟨Φ⁺|_{R A'} ⊗ I_{B'}` on `(ℂ^d)⊗³`. -/
noncomputable def projA : Matrix (TriIdx d) (TriIdx d) ℂ :=
  fun x y => if x.1 = x.2.1 ∧ y.1 = y.2.1 ∧ x.2.2 = y.2.2 then ((d : ℂ)⁻¹) else 0

/-- Maximally entangled projector `P_B = |Φ⁺⟩⟨Φ⁺|_{R B'} ⊗ I_{A'}` on `(ℂ^d)⊗³`. -/
noncomputable def projB : Matrix (TriIdx d) (TriIdx d) ℂ :=
  fun x y => if x.1 = x.2.2 ∧ y.1 = y.2.2 ∧ x.2.1 = y.2.1 then ((d : ℂ)⁻¹) else 0

lemma projA_hermitian : (projA d)ᴴ = projA d := by
  ext x y
  simp only [Matrix.conjTranspose_apply, projA]
  by_cases h : y.1 = y.2.1 ∧ x.1 = x.2.1 ∧ y.2.2 = x.2.2
  · have h' : x.1 = x.2.1 ∧ y.1 = y.2.1 ∧ x.2.2 = y.2.2 := ⟨h.2.1, h.1, h.2.2.symm⟩
    simp only [eq_true h, eq_true h', ↓reduceIte, star_inv₀, star_natCast]
  · have h' : ¬ (x.1 = x.2.1 ∧ y.1 = y.2.1 ∧ x.2.2 = y.2.2) :=
      fun hh => h ⟨hh.2.1, hh.1, hh.2.2.symm⟩
    simp only [eq_false h, eq_false h', ↓reduceIte, star_zero]

lemma projB_hermitian : (projB d)ᴴ = projB d := by
  ext x y
  simp only [Matrix.conjTranspose_apply, projB]
  by_cases h : y.1 = y.2.2 ∧ x.1 = x.2.2 ∧ y.2.1 = x.2.1
  · have h' : x.1 = x.2.2 ∧ y.1 = y.2.2 ∧ x.2.1 = y.2.1 := ⟨h.2.1, h.1, h.2.2.symm⟩
    simp only [eq_true h, eq_true h', ↓reduceIte, star_inv₀, star_natCast]
  · have h' : ¬ (x.1 = x.2.2 ∧ y.1 = y.2.2 ∧ x.2.1 = y.2.1) :=
      fun hh => h ⟨hh.2.1, hh.1, hh.2.2.symm⟩
    simp only [eq_false h, eq_false h', ↓reduceIte, star_zero]

lemma projA_mul_projA (hd : 0 < d) : projA d * projA d = projA d := by
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  ext ⟨r, a, b⟩ ⟨r', a', b'⟩
  rw [Matrix.mul_apply]
  simp only [projA]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  by_cases h : r = a ∧ r' = a' ∧ b = b'
  · rcases h with ⟨rfl, rfl, rfl⟩
    have hsum : ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d,
        (if r = r ∧ i = j ∧ b = k then (d : ℂ)⁻¹ else 0) *
        (if i = j ∧ r' = r' ∧ k = b then (d : ℂ)⁻¹ else 0) = (d : ℂ)⁻¹ := by
      calc ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d,
            (if r = r ∧ i = j ∧ b = k then (d : ℂ)⁻¹ else 0) *
            (if i = j ∧ r' = r' ∧ k = b then (d : ℂ)⁻¹ else 0)
          = ∑ i : Fin d, ((d : ℂ)⁻¹ * (d : ℂ)⁻¹) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.sum_eq_single i]
              · rw [Finset.sum_eq_single b]
                · simp
                · intro k _ hk; simp [Ne.symm hk]
                · intro hb; exact (hb (Finset.mem_univ b)).elim
              · intro j _ hj; simp [Ne.symm hj]
              · intro hi; exact (hi (Finset.mem_univ i)).elim
        _ = (d : ℂ) * ((d : ℂ)⁻¹ * (d : ℂ)⁻¹) := by simp
        _ = (d : ℂ)⁻¹ := by field_simp [hd0]
    simpa using hsum
  · simp only [h, ↓reduceIte]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ =>
      Finset.sum_eq_zero fun k _ => ?_
    by_cases h1 : r = a ∧ i = j ∧ b = k
    · by_cases h2 : i = j ∧ r' = a' ∧ k = b'
      · exact (h ⟨h1.1, h2.2.1, h1.2.2.trans h2.2.2⟩).elim
      · simp [h2]
    · simp [h1]

lemma projB_mul_projB (hd : 0 < d) : projB d * projB d = projB d := by
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  ext ⟨r, a, b⟩ ⟨r', a', b'⟩
  rw [Matrix.mul_apply]
  simp only [projB]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  by_cases h : r = b ∧ r' = b' ∧ a = a'
  · rcases h with ⟨rfl, rfl, rfl⟩
    have hsum : ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d,
        (if r = r ∧ i = k ∧ a = j then (d : ℂ)⁻¹ else 0) *
        (if i = k ∧ r' = r' ∧ j = a then (d : ℂ)⁻¹ else 0) = (d : ℂ)⁻¹ := by
      calc ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d,
            (if r = r ∧ i = k ∧ a = j then (d : ℂ)⁻¹ else 0) *
            (if i = k ∧ r' = r' ∧ j = a then (d : ℂ)⁻¹ else 0)
          = ∑ i : Fin d, ((d : ℂ)⁻¹ * (d : ℂ)⁻¹) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.sum_eq_single a]
              · rw [Finset.sum_eq_single i]
                · simp
                · intro k _ hk; simp [Ne.symm hk]
                · intro hi; exact (hi (Finset.mem_univ i)).elim
              · intro j _ hj; simp [Ne.symm hj]
              · intro ha; exact (ha (Finset.mem_univ a)).elim
        _ = (d : ℂ) * ((d : ℂ)⁻¹ * (d : ℂ)⁻¹) := by simp
        _ = (d : ℂ)⁻¹ := by field_simp [hd0]
    simpa using hsum
  · simp only [h, ↓reduceIte]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ =>
      Finset.sum_eq_zero fun k _ => ?_
    by_cases h1 : r = b ∧ i = k ∧ a = j
    · by_cases h2 : i = k ∧ r' = b' ∧ j = a'
      · exact (h ⟨h1.1, h2.2.1, h1.2.2.trans h2.2.2⟩).elim
      · simp [h2]
    · simp [h1]

lemma projA_mul_projB_entry (r a b r' a' b' : Fin d) :
    (projA d * projB d) (r, a, b) (r', a', b') =
      if r = a ∧ r' = b' ∧ b = a' then ((d : ℂ)⁻¹ * (d : ℂ)⁻¹) else 0 := by
  rw [Matrix.mul_apply]
  simp only [projA, projB]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  by_cases h : r = a ∧ r' = b' ∧ b = a'
  · rcases h with ⟨rfl, rfl, rfl⟩
    simp only [true_and, ↓reduceIte]
    rw [Finset.sum_eq_single b]
    · rw [Finset.sum_eq_single b]
      · rw [Finset.sum_eq_single b]
        · simp
        · intro k _ hk; simp [Ne.symm hk]
        · intro hb; exact (hb (Finset.mem_univ b)).elim
      · intro j _ hj
        refine Finset.sum_eq_zero fun k _ => ?_
        simp [Ne.symm hj]
      · intro hb; exact (hb (Finset.mem_univ b)).elim
    · intro i _ hi
      refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
      by_cases h1 : i = j ∧ b = k
      · by_cases h2 : i = k ∧ j = b
        · exact (hi (h2.1.trans h1.2.symm)).elim
        · simp [h2]
      · simp [h1]
    · intro hb; exact (hb (Finset.mem_univ b)).elim
  · simp only [h, ↓reduceIte]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ =>
      Finset.sum_eq_zero fun k _ => ?_
    by_cases h1 : r = a ∧ i = j ∧ b = k
    · by_cases h2 : i = k ∧ r' = b' ∧ j = a'
      · exact (h ⟨h1.1, h2.2.1, (h1.2.2.trans h2.1.symm).trans (h1.2.1.trans h2.2.2)⟩).elim
      · simp [h2]
    · simp [h1]

/-- **Theorem 3(a)** (Exact Projection Overlap Algebra):
`P_A P_B P_A = (1 / d²) · P_A` on `(ℂ^d)⊗³` for every `d ≥ 1`. -/
theorem projA_projB_projA (_hd : 0 < d) :
    projA d * projB d * projA d = ((d : ℂ) ^ 2)⁻¹ • projA d := by
  ext ⟨r, a, b⟩ ⟨r', a', b'⟩
  rw [Matrix.mul_apply, Matrix.smul_apply, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, projA_mul_projB_entry]
  simp only [projA, smul_eq_mul]
  by_cases h : r = a ∧ r' = a' ∧ b = b'
  · rcases h with ⟨rfl, rfl, rfl⟩
    simp only [true_and, ↓reduceIte]
    rw [Finset.sum_eq_single b]
    · rw [Finset.sum_eq_single b]
      · rw [Finset.sum_eq_single b]
        · simp [pow_two]
        · intro k _ hk; simp [hk]
        · intro hb; exact (hb (Finset.mem_univ b)).elim
      · intro j _ hj
        refine Finset.sum_eq_zero fun k _ => ?_
        simp [Ne.symm hj]
      · intro hb; exact (hb (Finset.mem_univ b)).elim
    · intro i _ hi
      refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
      by_cases h1 : i = k ∧ b = j
      · by_cases h2 : i = j ∧ k = b
        · exact (hi (h2.1.trans h1.2.symm)).elim
        · simp [h2]
      · simp [h1]
    · intro hb; exact (hb (Finset.mem_univ b)).elim
  · simp only [h, ↓reduceIte, mul_zero]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ =>
      Finset.sum_eq_zero fun k _ => ?_
    by_cases h1 : r = a ∧ i = k ∧ b = j
    · by_cases h2 : i = j ∧ r' = a' ∧ k = b'
      · exact (h ⟨h1.1, h2.2.1, (h1.2.2.trans h2.1.symm).trans (h1.2.1.trans h2.2.2)⟩).elim
      · simp [h2]
    · simp [h1]

/-- Vector-matrix adjoint identity: `⟨u, M v⟩ = ⟨Mᴴ u, v⟩`. -/
lemma vecInner_mulVec_right {α : Type*} [Fintype α]
    (M : Matrix α α ℂ) (u v : α → ℂ) :
    vecInner u (M.mulVec v) = vecInner (Mᴴ.mulVec u) v := by
  unfold vecInner Matrix.mulVec
  simp only [dotProduct, Matrix.conjTranspose_apply, Finset.mul_sum, star_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [star_mul, star_star]
  ring

/-- Cauchy–Schwarz inequality for `vecInner`: `(Re ⟨u, v⟩)² ≤ ‖u‖² ‖v‖²`. -/
lemma vecInner_re_sq_le {α : Type*} [Fintype α] (u v : α → ℂ) :
    (vecInner u v).re ^ 2 ≤ vecNormSq u * vecNormSq v := by
  have hnonneg : ∀ t : ℝ, 0 ≤ vecNormSq (fun i => (t : ℂ) * u i + v i) :=
    fun t => vecNormSq_nonneg _
  have hexp : ∀ t : ℝ,
      vecNormSq (fun i => (t : ℂ) * u i + v i) =
        t ^ 2 * vecNormSq u + 2 * t * (vecInner u v).re + vecNormSq v := by
    intro t
    unfold vecNormSq vecInner
    rw [Complex.re_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im]
    ring
  by_cases hu : vecNormSq u = 0
  · have hlin : ∀ t : ℝ, 0 ≤ 2 * t * (vecInner u v).re + vecNormSq v := by
      intro t; have := hnonneg t; rw [hexp t, hu] at this; linarith
    have hre0 : (vecInner u v).re = 0 := by
      by_contra hne
      have := hlin (-(vecNormSq v + 1) / (2 * (vecInner u v).re))
      have h2ne : 2 * (vecInner u v).re ≠ 0 := mul_ne_zero two_ne_zero hne
      have hval : 2 * (-(vecNormSq v + 1) / (2 * (vecInner u v).re)) * (vecInner u v).re =
          -(vecNormSq v + 1) := by field_simp [h2ne]
      linarith
    rw [hre0, hu]; norm_num
  · have hupos : 0 < vecNormSq u := lt_of_le_of_ne (vecNormSq_nonneg u) (Ne.symm hu)
    have hmin := hnonneg (-(vecInner u v).re / vecNormSq u)
    rw [hexp] at hmin
    have hcalc : (-(vecInner u v).re / vecNormSq u) ^ 2 * vecNormSq u +
        2 * (-(vecInner u v).re / vecNormSq u) * (vecInner u v).re + vecNormSq v =
        vecNormSq v - (vecInner u v).re ^ 2 / vecNormSq u := by
      field_simp [hu]; ring
    rw [hcalc] at hmin
    have hle : (vecInner u v).re ^ 2 / vecNormSq u ≤ vecNormSq v := by linarith
    have hmul := (div_le_iff₀ hupos).mp hle
    linarith

/-- **Theorem 3(b)** (Sharp Universal Joint-Extension Monogamy Bound):
For arbitrary `d ≥ 1` and ANY normalized 3-party state vector `ψ : (Fin d)³ → ℂ`
(`‖ψ‖² = 1`), the sum of entanglement fidelities satisfies
`F_A(ψ) + F_B(ψ) ≤ 1 + 1 / d`. -/
theorem joint_extension_fidelity_bound (hd : 0 < d)
    (ψ : TriIdx d → ℂ) (hψ : vecNormSq ψ = 1) :
    (vecInner ψ ((projA d).mulVec ψ)).re + (vecInner ψ ((projB d).mulVec ψ)).re ≤
      1 + (d : ℝ)⁻¹ := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  set u := (projA d).mulVec ψ
  set w := (projB d).mulVec ψ
  have hu_norm : vecNormSq u = (vecInner ψ u).re := by
    rw [← vecInner_self_re]
    have hstep : vecInner u u = vecInner ψ ((projA d).mulVec u) := by
      calc vecInner u u = vecInner ((projA d)ᴴ.mulVec ψ) u := by rw [projA_hermitian]
        _ = vecInner ψ ((projA d).mulVec u) := (vecInner_mulVec_right (projA d) ψ u).symm
    rw [hstep, show (projA d).mulVec u = (projA d * projA d).mulVec ψ from
      Matrix.mulVec_mulVec ψ (projA d) (projA d), projA_mul_projA d hd]
  have hw_norm : vecNormSq w = (vecInner ψ w).re := by
    rw [← vecInner_self_re]
    have hstep : vecInner w w = vecInner ψ ((projB d).mulVec w) := by
      calc vecInner w w = vecInner ((projB d)ᴴ.mulVec ψ) w := by rw [projB_hermitian]
        _ = vecInner ψ ((projB d).mulVec w) := (vecInner_mulVec_right (projB d) ψ w).symm
    rw [hstep, show (projB d).mulVec w = (projB d * projB d).mulVec ψ from
      Matrix.mulVec_mulVec ψ (projB d) (projB d), projB_mul_projB d hd]
  have hPBu_norm : vecNormSq ((projB d).mulVec u) = ((d : ℝ) ^ 2)⁻¹ * vecNormSq u := by
    rw [← vecInner_self_re]
    have hstep1 : vecInner ((projB d).mulVec u) ((projB d).mulVec u) =
        vecInner u ((projB d).mulVec u) := by
      calc vecInner ((projB d).mulVec u) ((projB d).mulVec u)
          = vecInner ((projB d)ᴴ.mulVec u) ((projB d).mulVec u) := by rw [projB_hermitian]
        _ = vecInner u ((projB d).mulVec ((projB d).mulVec u)) :=
            (vecInner_mulVec_right (projB d) u ((projB d).mulVec u)).symm
        _ = vecInner u ((projB d * projB d).mulVec u) := by rw [Matrix.mulVec_mulVec]
        _ = vecInner u ((projB d).mulVec u) := by rw [projB_mul_projB d hd]
    have hstep2 : vecInner u ((projB d).mulVec u) =
        vecInner ψ ((projA d * projB d * projA d).mulVec ψ) := by
      calc vecInner u ((projB d).mulVec u)
          = vecInner ((projA d)ᴴ.mulVec ψ) ((projB d).mulVec u) := by rw [projA_hermitian]
        _ = vecInner ψ ((projA d).mulVec ((projB d).mulVec ((projA d).mulVec ψ))) :=
            (vecInner_mulVec_right (projA d) ψ ((projB d).mulVec u)).symm
        _ = vecInner ψ ((projA d * projB d * projA d).mulVec ψ) := by
            rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [hstep1, hstep2, projA_projB_projA d hd]
    have hsmul : (((d : ℂ) ^ 2)⁻¹ • projA d).mulVec ψ = ((d : ℂ) ^ 2)⁻¹ • u := by
      ext x
      simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum, u, mul_assoc]
    rw [hsmul]
    have hlin : vecInner ψ (((d : ℂ) ^ 2)⁻¹ • u) = ((d : ℂ) ^ 2)⁻¹ * vecInner ψ u := by
      unfold vecInner; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Pi.smul_apply, smul_eq_mul]; ring
    rw [hlin, hu_norm]
    have hreal : ((d : ℂ) ^ 2)⁻¹ = ((((d : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [hreal, Complex.re_ofReal_mul]
  have huw_eq : vecInner u w = vecInner ((projB d).mulVec u) w := by
    calc vecInner u w = vecInner u ((projB d * projB d).mulVec ψ) := by
            rw [projB_mul_projB d hd]
      _ = vecInner u ((projB d).mulVec w) := by rw [← Matrix.mulVec_mulVec]
      _ = vecInner ((projB d)ᴴ.mulVec u) w := vecInner_mulVec_right (projB d) u w
      _ = vecInner ((projB d).mulVec u) w := by rw [projB_hermitian]
  have hcs_uw : (vecInner u w).re ^ 2 ≤ ((d : ℝ) ^ 2)⁻¹ * vecNormSq u * vecNormSq w := by
    rw [huw_eq]
    have h := vecInner_re_sq_le ((projB d).mulVec u) w
    rw [hPBu_norm] at h
    exact h
  have h2re : 2 * (vecInner u w).re ≤ (d : ℝ)⁻¹ * (vecNormSq u + vecNormSq w) := by
    have hnn_u := vecNormSq_nonneg u
    have hnn_w := vecNormSq_nonneg w
    have hinv_pos : 0 < (d : ℝ)⁻¹ := inv_pos.mpr hd_pos
    have hsq : (2 * (vecInner u w).re) ^ 2 ≤ ((d : ℝ)⁻¹ * (vecNormSq u + vecNormSq w)) ^ 2 := by
      have h1 : 4 * (vecInner u w).re ^ 2 ≤ 4 * (((d : ℝ) ^ 2)⁻¹ * vecNormSq u * vecNormSq w) := by
        linarith
      have h2 : 4 * vecNormSq u * vecNormSq w ≤ (vecNormSq u + vecNormSq w) ^ 2 := by
        nlinarith [sq_nonneg (vecNormSq u - vecNormSq w)]
      have h3 : 4 * (((d : ℝ) ^ 2)⁻¹ * vecNormSq u * vecNormSq w) =
          ((d : ℝ)⁻¹) ^ 2 * (4 * vecNormSq u * vecNormSq w) := by
        rw [inv_pow]; ring
      have h4 : ((d : ℝ)⁻¹ * (vecNormSq u + vecNormSq w)) ^ 2 =
          ((d : ℝ)⁻¹) ^ 2 * (vecNormSq u + vecNormSq w) ^ 2 := by ring
      have h5 : ((d : ℝ)⁻¹) ^ 2 * (4 * vecNormSq u * vecNormSq w) ≤
          ((d : ℝ)⁻¹) ^ 2 * (vecNormSq u + vecNormSq w) ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      nlinarith
    have hrhs_nn : 0 ≤ (d : ℝ)⁻¹ * (vecNormSq u + vecNormSq w) :=
      mul_nonneg (le_of_lt hinv_pos) (add_nonneg hnn_u hnn_w)
    nlinarith [sq_nonneg (2 * (vecInner u w).re - (d : ℝ)⁻¹ * (vecNormSq u + vecNormSq w))]
  have hsum_norm : vecNormSq (u + w) = vecNormSq u + vecNormSq w + 2 * (vecInner u w).re := by
    unfold vecNormSq vecInner
    rw [Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  have hsum_le : vecNormSq (u + w) ≤ (1 + (d : ℝ)⁻¹) * (vecNormSq u + vecNormSq w) := by
    linarith
  have hinner_add : (vecInner ψ (u + w)).re = vecNormSq u + vecNormSq w := by
    rw [hu_norm, hw_norm]
    unfold vecInner
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, Complex.add_re]
  have hcs_psi := vecInner_re_sq_le ψ (u + w)
  rw [hinner_add, hψ, one_mul] at hcs_psi
  set S := vecNormSq u + vecNormSq w
  have hS_nn : 0 ≤ S := add_nonneg (vecNormSq_nonneg u) (vecNormSq_nonneg w)
  have hS_sq : S ^ 2 ≤ (1 + (d : ℝ)⁻¹) * S := le_trans hcs_psi hsum_le
  have hfinal : S ≤ 1 + (d : ℝ)⁻¹ := by
    by_cases hS0 : S = 0
    · rw [hS0]; positivity
    · have hSpos : 0 < S := lt_of_le_of_ne hS_nn (Ne.symm hS0)
      nlinarith
  linarith [hu_norm, hw_norm]

/-- **Theorem 3(b) Corollary**: For `d ≥ 2`, no joint normalized state can achieve
simultaneous faithful recovery (`F_A = 1 ∧ F_B = 1`). -/
theorem joint_extension_no_simultaneous_faithful (hd : 2 ≤ d)
    (ψ : TriIdx d → ℂ) (hψ : vecNormSq ψ = 1) :
    ¬ ((vecInner ψ ((projA d).mulVec ψ)).re = 1 ∧
       (vecInner ψ ((projB d).mulVec ψ)).re = 1) := by
  rintro ⟨hA, hB⟩
  have hbound := joint_extension_fidelity_bound d (by omega) ψ hψ
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hinv : (d : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hd2
  linarith

/-- **Theorem 3(b.2)** (Mixed-State Convexity Extension):
For any finite convex mixture `∑_i p_i |ψ_i⟩⟨ψ_i|` of normalized 3-party states
(`p_i ≥ 0`, `∑ p_i = 1`), the sum of entanglement fidelities obeys `F_A(σ) + F_B(σ) ≤ 1 + 1/d`. -/
theorem joint_extension_fidelity_bound_mixed (hd : 0 < d) {k : ℕ}
    (p : Fin k → ℝ) (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i : Fin k, p i = 1)
    (ψ : Fin k → TriIdx d → ℂ) (hψ : ∀ i, vecNormSq (ψ i) = 1) :
    (∑ i : Fin k, p i * (vecInner (ψ i) ((projA d).mulVec (ψ i))).re) +
      (∑ i : Fin k, p i * (vecInner (ψ i) ((projB d).mulVec (ψ i))).re) ≤
      1 + (d : ℝ)⁻¹ := by
  rw [← Finset.sum_add_distrib]
  calc ∑ i : Fin k, (p i * (vecInner (ψ i) ((projA d).mulVec (ψ i))).re +
          p i * (vecInner (ψ i) ((projB d).mulVec (ψ i))).re)
      = ∑ i : Fin k, p i * ((vecInner (ψ i) ((projA d).mulVec (ψ i))).re +
          (vecInner (ψ i) ((projB d).mulVec (ψ i))).re) := by
        refine Finset.sum_congr rfl fun i _ => by ring
    _ ≤ ∑ i : Fin k, p i * (1 + (d : ℝ)⁻¹) := by
        refine Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (joint_extension_fidelity_bound d hd (ψ i) (hψ i)) (hp_nn i)
    _ = (∑ i : Fin k, p i) * (1 + (d : ℝ)⁻¹) := (Finset.sum_mul _ _ _).symm
    _ = 1 + (d : ℝ)⁻¹ := by rw [hp_sum, one_mul]

/-- **Theorem 3(b.3)** (Exact Sharpness via Valid CPTP Choi State `σ_*`):
For arbitrary `d > 0`, the uniform mixture `σ_* = (1/d) ∑_j |ψ_j⟩⟨ψ_j|` of the symmetric
states `|ψ_j⟩ = (|Φ^+⟩_{RA'}|j⟩_{B'} + |Φ^+⟩_{RB'}|j⟩_{A'}) / √(2 + 2/d)`:
  1. consists of normalized pure states (`‖ψ_j‖² = 1`);
  2. achieves `F_A(ψ_j) = F_B(ψ_j) = (1 + 1/d) / 2` for every `j`, saturating `F_A + F_B = 1 + 1/d`;
  3. satisfies the exact CPTP Choi-state marginal condition `Tr_{A'B'}(σ_*) = I_R / d`. -/
theorem joint_extension_bound_sharp (hd : 0 < d) :
    ∃ ψ : Fin d → TriIdx d → ℂ,
      (∀ j, vecNormSq (ψ j) = 1) ∧
      (∀ j, (vecInner (ψ j) ((projA d).mulVec (ψ j))).re = (1 + (d : ℝ)⁻¹) / 2 ∧
            (vecInner (ψ j) ((projB d).mulVec (ψ j))).re = (1 + (d : ℝ)⁻¹) / 2) ∧
      (∀ r r' : Fin d,
        ((d : ℂ)⁻¹ * ∑ j : Fin d, ∑ a : Fin d, ∑ b : Fin d,
          ψ j (r, a, b) * star (ψ j (r', a, b))) =
        if r = r' then (d : ℂ)⁻¹ else 0) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
  have hd_cne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  have h2d2_pos : (0 : ℝ) < 2 * (d : ℝ) + 2 := by linarith
  have h2d2_ne : (2 * (d : ℝ) + 2 : ℝ) ≠ 0 := ne_of_gt h2d2_pos
  have h2d2_cne : ((2 * (d : ℝ) + 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h2d2_ne
  let c : ℝ := (Real.sqrt (2 * (d : ℝ) + 2))⁻¹
  have hc_sq : c ^ 2 = (2 * (d : ℝ) + 2)⁻¹ := by
    simp only [c, inv_pow, Real.sq_sqrt (le_of_lt h2d2_pos)]
  let raw : Fin d → TriIdx d → ℂ := fun j x =>
    (if x.1 = x.2.1 ∧ x.2.2 = j then (1 : ℂ) else 0) +
    (if x.1 = x.2.2 ∧ x.2.1 = j then (1 : ℂ) else 0)
  let ψ : Fin d → TriIdx d → ℂ := fun j x => (c : ℂ) * raw j x
  refine ⟨ψ, ?_, ?_, ?_⟩
  · -- (1) Normalization: ‖ψ_j‖² = 1
    intro j
    unfold vecNormSq
    simp only [ψ, Complex.normSq_mul, Complex.normSq_ofReal]
    rw [← Finset.mul_sum, Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    have hraw_sum : ∑ r : Fin d, ∑ a : Fin d, ∑ b : Fin d, Complex.normSq (raw j (r, a, b)) =
        2 * (d : ℝ) + 2 := by
      have hterm : ∀ r : Fin d,
          ∑ a : Fin d, ∑ b : Fin d, Complex.normSq (raw j (r, a, b)) =
          if r = j then (4 : ℝ) else 2 := by
        intro r
        by_cases hrj : r = j
        · subst hrj
          rw [Finset.sum_eq_single r]
          · rw [Finset.sum_eq_single r]
            · simp [raw]; norm_num
            · intro b _ hbr
              simp [raw, hbr, Ne.symm hbr]
            · intro h; exact (h (Finset.mem_univ r)).elim
          · intro a _ har
            refine Finset.sum_eq_zero fun b _ => ?_
            simp [raw, har, Ne.symm har]
          · intro h; exact (h (Finset.mem_univ r)).elim
        · simp only [hrj, ↓reduceIte]
          have hpair : ∑ a : Fin d, ∑ b : Fin d, Complex.normSq (raw j (r, a, b)) =
              (∑ b : Fin d, Complex.normSq (raw j (r, r, b))) +
              (∑ b : Fin d, Complex.normSq (raw j (r, j, b))) := by
            have hsub : ∀ a : Fin d, a ≠ r → a ≠ j →
                ∑ b : Fin d, Complex.normSq (raw j (r, a, b)) = 0 := by
              intro a har haj
              refine Finset.sum_eq_zero fun b _ => ?_
              simp [raw, Ne.symm har, haj]
            rw [← Finset.sum_subset (Finset.subset_univ ({r, j} : Finset (Fin d)))]
            · rw [Finset.sum_pair hrj]
            · intro a _ ha
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
              exact hsub a ha.1 ha.2
          rw [hpair]
          have ht1 : ∑ b : Fin d, Complex.normSq (raw j (r, r, b)) = 1 := by
            rw [Finset.sum_eq_single j]
            · simp [raw, hrj]
            · intro b _ hbj; simp [raw, hbj, hrj]
            · intro h; exact (h (Finset.mem_univ j)).elim
          have ht2 : ∑ b : Fin d, Complex.normSq (raw j (r, j, b)) = 1 := by
            rw [Finset.sum_eq_single r]
            · simp [raw, hrj]
            · intro b _ hbr; simp [raw, Ne.symm hbr, hrj]
            · intro h; exact (h (Finset.mem_univ r)).elim
          rw [ht1, ht2]; norm_num
      simp_rw [hterm]
      have hsplit : ∑ r : Fin d, (if r = j then (4 : ℝ) else 2) =
          (∑ r : Fin d, (2 : ℝ)) + ∑ r : Fin d, (if r = j then (2 : ℝ) else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun r _ => ?_
        by_cases h : r = j
        · simp [h]; norm_num
        · simp [h]
      rw [hsplit]
      simp [Finset.sum_ite_eq']
      ring
    rw [hraw_sum, ← sq, hc_sq, inv_mul_cancel₀ h2d2_ne]
  · -- (2) Exact fidelities F_A(ψ_j) = F_B(ψ_j) = (1 + 1/d) / 2
    intro j
    have hPA : ∀ x : TriIdx d, ((projA d).mulVec (ψ j)) x =
        if x.1 = x.2.1 ∧ x.2.2 = j then (c : ℂ) * ((d : ℂ) + 1) * (d : ℂ)⁻¹ else 0 := by
      rintro ⟨r, a, b⟩
      simp only [Matrix.mulVec, dotProduct, projA, ψ, Fintype.sum_prod_type]
      by_cases h : r = a ∧ b = j
      · rcases h with ⟨rfl, rfl⟩
        simp only [true_and, ↓reduceIte]
        have hsum : ∑ i : Fin d, ∑ a' : Fin d, ∑ b' : Fin d,
            (if i = a' ∧ b = b' then (d : ℂ)⁻¹ else 0) * ((c : ℂ) * raw b (i, a', b')) =
            ∑ i : Fin d, (d : ℂ)⁻¹ * ((c : ℂ) * ((1 : ℂ) + if i = b then 1 else 0)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_eq_single i]
          · rw [Finset.sum_eq_single b]
            · simp [raw]
            · intro b' _ hb'; simp [Ne.symm hb']
            · intro h; exact (h (Finset.mem_univ b)).elim
          · intro a' _ ha'
            refine Finset.sum_eq_zero fun b' _ => ?_
            simp [Ne.symm ha']
          · intro h; exact (h (Finset.mem_univ i)).elim
        rw [hsum]
        simp_rw [mul_add, Finset.sum_add_distrib]
        have h1 : ∑ _i : Fin d, (d : ℂ)⁻¹ * ((c : ℂ) * 1) = (d : ℂ) * ((d : ℂ)⁻¹ * (c : ℂ)) := by
          simp
        have h2 : ∑ i : Fin d, (d : ℂ)⁻¹ * ((c : ℂ) * if i = b then (1 : ℂ) else 0) =
            (d : ℂ)⁻¹ * (c : ℂ) := by
          rw [Finset.sum_eq_single b]
          · simp
          · intro i _ hib; simp [hib]
          · intro h; exact (h (Finset.mem_univ b)).elim
        rw [h1, h2]
        field_simp [hd_cne]
      · simp only [h, ↓reduceIte]
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun a' _ =>
          Finset.sum_eq_zero fun b' _ => ?_
        by_cases h1 : r = a ∧ i = a' ∧ b = b'
        · rcases h1 with ⟨rfl, rfl, rfl⟩
          have hbj : b ≠ j := fun hbj => h ⟨rfl, hbj⟩
          simp [raw, hbj]
          intro hib hij
          exact (hbj (hib.symm.trans hij)).elim
        · simp [h1]
    have hPB : ∀ x : TriIdx d, ((projB d).mulVec (ψ j)) x =
        if x.1 = x.2.2 ∧ x.2.1 = j then (c : ℂ) * ((d : ℂ) + 1) * (d : ℂ)⁻¹ else 0 := by
      rintro ⟨r, a, b⟩
      simp only [Matrix.mulVec, dotProduct, projB, ψ, Fintype.sum_prod_type]
      by_cases h : r = b ∧ a = j
      · rcases h with ⟨rfl, rfl⟩
        simp only [true_and, ↓reduceIte]
        have hsum : ∑ i : Fin d, ∑ a' : Fin d, ∑ b' : Fin d,
            (if i = b' ∧ a = a' then (d : ℂ)⁻¹ else 0) * ((c : ℂ) * raw a (i, a', b')) =
            ∑ i : Fin d, (d : ℂ)⁻¹ * ((c : ℂ) * ((if i = a then 1 else 0) + 1)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_eq_single a]
          · rw [Finset.sum_eq_single i]
            · simp [raw]
            · intro b' _ hb'; simp [Ne.symm hb']
            · intro h; exact (h (Finset.mem_univ i)).elim
          · intro a' _ ha'
            refine Finset.sum_eq_zero fun b' _ => ?_
            simp [Ne.symm ha']
          · intro h; exact (h (Finset.mem_univ a)).elim
        rw [hsum]
        simp_rw [mul_add, Finset.sum_add_distrib]
        have h1 : ∑ i : Fin d, (d : ℂ)⁻¹ * ((c : ℂ) * if i = a then (1 : ℂ) else 0) =
            (d : ℂ)⁻¹ * (c : ℂ) := by
          rw [Finset.sum_eq_single a]
          · simp
          · intro i _ hia; simp [hia]
          · intro h; exact (h (Finset.mem_univ a)).elim
        have h2 : ∑ _i : Fin d, (d : ℂ)⁻¹ * ((c : ℂ) * 1) = (d : ℂ) * ((d : ℂ)⁻¹ * (c : ℂ)) := by
          simp
        rw [h1, h2]
        field_simp [hd_cne]
        ring
      · simp only [h, ↓reduceIte]
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun a' _ =>
          Finset.sum_eq_zero fun b' _ => ?_
        by_cases h1 : r = b ∧ i = b' ∧ a = a'
        · rcases h1 with ⟨rfl, rfl, rfl⟩
          have haj : a ≠ j := fun haj => h ⟨rfl, haj⟩
          simp [raw, haj]
          intro hia hij
          exact (haj (hia.symm.trans hij)).elim
        · simp [h1]
    have hFA : (vecInner (ψ j) ((projA d).mulVec (ψ j))).re = (1 + (d : ℝ)⁻¹) / 2 := by
      have hsq : (vecInner (ψ j) ((projA d).mulVec (ψ j))).re =
          vecNormSq ((projA d).mulVec (ψ j)) := by
        rw [← vecInner_self_re]
        have hstep : vecInner ((projA d).mulVec (ψ j)) ((projA d).mulVec (ψ j)) =
            vecInner (ψ j) ((projA d).mulVec (ψ j)) := by
          calc vecInner ((projA d).mulVec (ψ j)) ((projA d).mulVec (ψ j))
              = vecInner ((projA d)ᴴ.mulVec (ψ j)) ((projA d).mulVec (ψ j)) := by rw [projA_hermitian]
            _ = vecInner (ψ j) ((projA d).mulVec ((projA d).mulVec (ψ j))) :=
                (vecInner_mulVec_right (projA d) (ψ j) ((projA d).mulVec (ψ j))).symm
            _ = vecInner (ψ j) ((projA d * projA d).mulVec (ψ j)) := by rw [Matrix.mulVec_mulVec]
            _ = vecInner (ψ j) ((projA d).mulVec (ψ j)) := by rw [projA_mul_projA d hd]
        rw [hstep]
      rw [hsq]
      unfold vecNormSq
      simp_rw [hPA]
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      have hcalc : ∑ r : Fin d, ∑ a : Fin d, ∑ b : Fin d,
          Complex.normSq (if r = a ∧ b = j then (c : ℂ) * ((d : ℂ) + 1) * (d : ℂ)⁻¹ else 0) =
          (d : ℝ) * (c ^ 2 * ((d : ℝ) + 1) ^ 2 * ((d : ℝ) ^ 2)⁻¹) := by
        have hinner : ∀ r : Fin d,
            ∑ a : Fin d, ∑ b : Fin d,
              Complex.normSq (if r = a ∧ b = j then (c : ℂ) * ((d : ℂ) + 1) * (d : ℂ)⁻¹ else 0) =
            c ^ 2 * ((d : ℝ) + 1) ^ 2 * ((d : ℝ) ^ 2)⁻¹ := by
          intro r
          rw [Finset.sum_eq_single r]
          · rw [Finset.sum_eq_single j]
            · simp only [true_and, ↓reduceIte, Complex.normSq_mul, Complex.normSq_inv,
                Complex.normSq_ofReal, Complex.normSq_natCast]
              have hdp1 : Complex.normSq ((d : ℂ) + 1) = ((d : ℝ) + 1) ^ 2 := by
                have : (d : ℂ) + 1 = (((d : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
                rw [this, Complex.normSq_ofReal, sq]
              rw [hdp1, ← sq, ← sq]
            · intro b _ hbj; simp [hbj]
            · intro h; exact (h (Finset.mem_univ j)).elim
          · intro a _ har
            refine Finset.sum_eq_zero fun b _ => ?_
            simp [Ne.symm har]
          · intro h; exact (h (Finset.mem_univ r)).elim
        simp_rw [hinner]
        simp
      rw [hcalc, hc_sq]
      field_simp [hd_ne, h2d2_ne]
    have hFB : (vecInner (ψ j) ((projB d).mulVec (ψ j))).re = (1 + (d : ℝ)⁻¹) / 2 := by
      have hsq : (vecInner (ψ j) ((projB d).mulVec (ψ j))).re =
          vecNormSq ((projB d).mulVec (ψ j)) := by
        rw [← vecInner_self_re]
        have hstep : vecInner ((projB d).mulVec (ψ j)) ((projB d).mulVec (ψ j)) =
            vecInner (ψ j) ((projB d).mulVec (ψ j)) := by
          calc vecInner ((projB d).mulVec (ψ j)) ((projB d).mulVec (ψ j))
              = vecInner ((projB d)ᴴ.mulVec (ψ j)) ((projB d).mulVec (ψ j)) := by rw [projB_hermitian]
            _ = vecInner (ψ j) ((projB d).mulVec ((projB d).mulVec (ψ j))) :=
                (vecInner_mulVec_right (projB d) (ψ j) ((projB d).mulVec (ψ j))).symm
            _ = vecInner (ψ j) ((projB d * projB d).mulVec (ψ j)) := by rw [Matrix.mulVec_mulVec]
            _ = vecInner (ψ j) ((projB d).mulVec (ψ j)) := by rw [projB_mul_projB d hd]
        rw [hstep]
      rw [hsq]
      unfold vecNormSq
      simp_rw [hPB]
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      have hcalc : ∑ r : Fin d, ∑ a : Fin d, ∑ b : Fin d,
          Complex.normSq (if r = b ∧ a = j then (c : ℂ) * ((d : ℂ) + 1) * (d : ℂ)⁻¹ else 0) =
          (d : ℝ) * (c ^ 2 * ((d : ℝ) + 1) ^ 2 * ((d : ℝ) ^ 2)⁻¹) := by
        have hinner : ∀ r : Fin d,
            ∑ a : Fin d, ∑ b : Fin d,
              Complex.normSq (if r = b ∧ a = j then (c : ℂ) * ((d : ℂ) + 1) * (d : ℂ)⁻¹ else 0) =
            c ^ 2 * ((d : ℝ) + 1) ^ 2 * ((d : ℝ) ^ 2)⁻¹ := by
          intro r
          rw [Finset.sum_eq_single j]
          · rw [Finset.sum_eq_single r]
            · simp only [true_and, ↓reduceIte, Complex.normSq_mul, Complex.normSq_inv,
                Complex.normSq_ofReal, Complex.normSq_natCast]
              have hdp1 : Complex.normSq ((d : ℂ) + 1) = ((d : ℝ) + 1) ^ 2 := by
                have : (d : ℂ) + 1 = (((d : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
                rw [this, Complex.normSq_ofReal, sq]
              rw [hdp1, ← sq, ← sq]
            · intro b _ hbr; simp [Ne.symm hbr]
            · intro h; exact (h (Finset.mem_univ r)).elim
          · intro a _ haj
            refine Finset.sum_eq_zero fun b _ => ?_
            simp [haj]
          · intro h; exact (h (Finset.mem_univ j)).elim
        simp_rw [hinner]
        simp
      rw [hcalc, hc_sq]
      field_simp [hd_ne, h2d2_ne]
    exact ⟨hFA, hFB⟩
  · -- (3) Exact CPTP Choi marginal Tr_{A'B'}(σ_*) = I_R / d
    intro r r'
    have hfactor : ∀ j a b : Fin d,
        ψ j (r, a, b) * star (ψ j (r', a, b)) =
        (((c ^ 2 : ℝ) : ℂ)) * (raw j (r, a, b) * star (raw j (r', a, b))) := by
      intro j a b
      simp only [ψ, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.ofReal_pow]
      ring
    simp_rw [hfactor, ← Finset.mul_sum]
    have hsum_raw : ∑ j : Fin d, ∑ a : Fin d, ∑ b : Fin d,
        raw j (r, a, b) * star (raw j (r', a, b)) =
        if r = r' then (((2 * (d : ℝ) + 2 : ℝ) : ℂ)) else 0 := by
      have hexp : ∀ j a b : Fin d,
          raw j (r, a, b) * star (raw j (r', a, b)) =
          (if r = a ∧ b = j ∧ r' = a then (1 : ℂ) else 0) +
          (if r = a ∧ b = j ∧ r' = b ∧ a = j then (1 : ℂ) else 0) +
          (if r = b ∧ a = j ∧ r' = a ∧ b = j then (1 : ℂ) else 0) +
          (if r = b ∧ a = j ∧ r' = b then (1 : ℂ) else 0) := by
        intro j a b
        have hstar_ite : ∀ (P : Prop) [Decidable P],
            star (if P then (1 : ℂ) else 0) = if P then (1 : ℂ) else 0 := by
          intro P _; by_cases hP : P <;> simp [hP]
        have hmul_ite : ∀ (P Q : Prop) [Decidable P] [Decidable Q],
            (if P then (1 : ℂ) else 0) * (if Q then (1 : ℂ) else 0) =
            if P ∧ Q then (1 : ℂ) else 0 := by
          intro P Q _ _; by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]
        unfold raw
        simp only [star_add, hstar_ite, add_mul, mul_add, hmul_ite]
        have h1 : (if (r = a ∧ b = j) ∧ (r' = a ∧ b = j) then (1 : ℂ) else 0) =
            if r = a ∧ b = j ∧ r' = a then (1 : ℂ) else 0 :=
          if_congr (by tauto) rfl rfl
        have h2 : (if (r = a ∧ b = j) ∧ (r' = b ∧ a = j) then (1 : ℂ) else 0) =
            if r = a ∧ b = j ∧ r' = b ∧ a = j then (1 : ℂ) else 0 :=
          if_congr (by tauto) rfl rfl
        have h3 : (if (r = b ∧ a = j) ∧ (r' = a ∧ b = j) then (1 : ℂ) else 0) =
            if r = b ∧ a = j ∧ r' = a ∧ b = j then (1 : ℂ) else 0 :=
          if_congr (by tauto) rfl rfl
        have h4 : (if (r = b ∧ a = j) ∧ (r' = b ∧ a = j) then (1 : ℂ) else 0) =
            if r = b ∧ a = j ∧ r' = b then (1 : ℂ) else 0 :=
          if_congr (by tauto) rfl rfl
        rw [h1, h2, h3, h4]; ring
      simp_rw [hexp, Finset.sum_add_distrib]
      have ht1 : ∑ j : Fin d, ∑ a : Fin d, ∑ b : Fin d,
          (if r = a ∧ b = j ∧ r' = a then (1 : ℂ) else 0) = if r = r' then (d : ℂ) else 0 := by
        by_cases hrr : r = r'
        · subst hrr
          simp only [↓reduceIte]
          have h1 : ∀ j : Fin d, ∑ a : Fin d, ∑ b : Fin d,
              (if r = a ∧ b = j ∧ r = a then (1 : ℂ) else 0) = 1 := by
            intro j
            rw [Finset.sum_eq_single r]
            · rw [Finset.sum_eq_single j]
              · simp
              · intro b _ hbj; simp [hbj]
              · intro h; exact (h (Finset.mem_univ j)).elim
            · intro a _ har; refine Finset.sum_eq_zero fun b _ => ?_; simp [Ne.symm har]
            · intro h; exact (h (Finset.mem_univ r)).elim
          simp_rw [h1]; simp
        · simp only [hrr, ↓reduceIte]
          refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun a _ =>
            Finset.sum_eq_zero fun b _ => ?_
          by_cases h : r = a ∧ b = j ∧ r' = a
          · exact (hrr (h.1.trans h.2.2.symm)).elim
          · simp [h]
      have ht2 : ∑ j : Fin d, ∑ a : Fin d, ∑ b : Fin d,
          (if r = a ∧ b = j ∧ r' = b ∧ a = j then (1 : ℂ) else 0) = if r = r' then 1 else 0 := by
        by_cases hrr : r = r'
        · subst hrr
          simp only [↓reduceIte]
          rw [Finset.sum_eq_single r]
          · rw [Finset.sum_eq_single r]
            · rw [Finset.sum_eq_single r]
              · simp
              · intro b _ hbr; simp [hbr]
              · intro h; exact (h (Finset.mem_univ r)).elim
            · intro a _ har; refine Finset.sum_eq_zero fun b _ => ?_; simp [Ne.symm har]
            · intro h; exact (h (Finset.mem_univ r)).elim
          · intro j _ hjr; refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
            by_cases h : r = a ∧ b = j ∧ r = b ∧ a = j
            · exact (hjr (h.2.2.1.trans h.2.1).symm).elim
            · simp [h]
          · intro h; exact (h (Finset.mem_univ r)).elim
        · simp only [hrr, ↓reduceIte]
          refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun a _ =>
            Finset.sum_eq_zero fun b _ => ?_
          by_cases h : r = a ∧ b = j ∧ r' = b ∧ a = j
          · exact (hrr ((h.1.trans h.2.2.2).trans (h.2.2.1.trans h.2.1).symm)).elim
          · simp [h]
      have ht3 : ∑ j : Fin d, ∑ a : Fin d, ∑ b : Fin d,
          (if r = b ∧ a = j ∧ r' = a ∧ b = j then (1 : ℂ) else 0) = if r = r' then 1 else 0 := by
        by_cases hrr : r = r'
        · subst hrr
          simp only [↓reduceIte]
          rw [Finset.sum_eq_single r]
          · rw [Finset.sum_eq_single r]
            · rw [Finset.sum_eq_single r]
              · simp
              · intro b _ hbr; simp [hbr]
              · intro h; exact (h (Finset.mem_univ r)).elim
            · intro a _ har; refine Finset.sum_eq_zero fun b _ => ?_; simp [Ne.symm har]
            · intro h; exact (h (Finset.mem_univ r)).elim
          · intro j _ hjr; refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
            by_cases h : r = b ∧ a = j ∧ r = a ∧ b = j
            · exact (hjr (h.1.trans h.2.2.2).symm).elim
            · simp [h]
          · intro h; exact (h (Finset.mem_univ r)).elim
        · simp only [hrr, ↓reduceIte]
          refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun a _ =>
            Finset.sum_eq_zero fun b _ => ?_
          by_cases h : r = b ∧ a = j ∧ r' = a ∧ b = j
          · exact (hrr ((h.1.trans h.2.2.2).trans (h.2.2.1.trans h.2.1).symm)).elim
          · simp [h]
      have ht4 : ∑ j : Fin d, ∑ a : Fin d, ∑ b : Fin d,
          (if r = b ∧ a = j ∧ r' = b then (1 : ℂ) else 0) = if r = r' then (d : ℂ) else 0 := by
        by_cases hrr : r = r'
        · subst hrr
          simp only [↓reduceIte]
          have h1 : ∀ j : Fin d, ∑ a : Fin d, ∑ b : Fin d,
              (if r = b ∧ a = j ∧ r = b then (1 : ℂ) else 0) = 1 := by
            intro j
            rw [Finset.sum_eq_single j]
            · rw [Finset.sum_eq_single r]
              · simp
              · intro b _ hbr; simp [Ne.symm hbr]
              · intro h; exact (h (Finset.mem_univ r)).elim
            · intro a _ haj; refine Finset.sum_eq_zero fun b _ => ?_; simp [haj]
            · intro h; exact (h (Finset.mem_univ j)).elim
          simp_rw [h1]; simp
        · simp only [hrr, ↓reduceIte]
          refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun a _ =>
            Finset.sum_eq_zero fun b _ => ?_
          by_cases h : r = b ∧ a = j ∧ r' = b
          · exact (hrr (h.1.trans h.2.2.symm)).elim
          · simp [h]
      rw [ht1, ht2, ht3, ht4]
      by_cases hrr : r = r'
      · simp [hrr]; ring
      · simp [hrr]
    rw [hsum_raw, hc_sq]
    by_cases hrr : r = r'
    · simp only [hrr, ↓reduceIte]
      have hinv : (((2 * (d : ℝ) + 2)⁻¹ : ℝ) : ℂ) * (((2 * (d : ℝ) + 2 : ℝ) : ℂ)) = 1 := by
        rw [← Complex.ofReal_mul, inv_mul_cancel₀ h2d2_ne, Complex.ofReal_one]
      rw [hinv, mul_one]
    · simp [hrr]

/-!
### Theorem 3(c): Constructive Observer-Separated Channels with Cross-Perspective Consistency

We model a joint system `H_C ⊗ H_sh` (represented on `Fin d × Fin m`) where `H_C` is the
unknown infalling logical system (dimension `d`) and `H_sh` is the shared causal-overlap
sector (dimension `m`, e.g., ADM energy / classical pre-horizon records).
- Observer `A` (infalling) evolves via unitary `U_A = I_C ⊗ I_sh` (smooth interior).
- Observer `B` (exterior) evolves via unitary `U_B = V_B ⊗ I_sh` (arbitrary scrambling unitary
  `V_B` on the logical sector encoding `C` into late Hawking radiation, acting trivially on
  the shared overlap sector `H_sh`).
- Then:
  1. Both `A` and `B` achieve **exact entanglement fidelity 1** (`F_A = 1`, `F_B = 1`,
     hence `F_A + F_B = 2 > 1 + 1/d` for all `d ≥ 2`).
  2. For **every** shared overlap observable `I_C ⊗ X_sh` and **every** state `ρ`,
     **exact Cross-Perspective Consistency** holds:
     `Tr((I_C ⊗ X_sh) · Φ_A(ρ)) = Tr((I_C ⊗ X_sh) · Φ_B(ρ))`.
-/

/-- Block-diagonal tensor observable `I_C ⊗ X_sh` on `Fin d × Fin m`. -/
def sharedObs {d m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ :=
  fun x y => if x.1 = y.1 then X x.2 y.2 else 0

/-- Local-sector unitary `V ⊗ I_sh` on `Fin d × Fin m`. -/
def logicalUnitary {d m : ℕ} (V : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ :=
  fun x y => if x.2 = y.2 then V x.1 y.1 else 0

lemma logicalUnitary_comm_sharedObs {d m : ℕ}
    (V : Matrix (Fin d) (Fin d) ℂ) (X : Matrix (Fin m) (Fin m) ℂ) :
    logicalUnitary V * sharedObs X = sharedObs X * logicalUnitary V := by
  ext ⟨c, s⟩ ⟨c', s'⟩
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [logicalUnitary, sharedObs]
  have hlhs : ∑ i : Fin d, ∑ j : Fin m,
      (if s = j then V c i else 0) * (if i = c' then X j s' else 0) = V c c' * X s s' := by
    rw [Finset.sum_eq_single c']
    · rw [Finset.sum_eq_single s]
      · simp
      · intro j _ hjs; simp [Ne.symm hjs]
      · intro hs; exact (hs (Finset.mem_univ s)).elim
    · intro i _ hic'
      refine Finset.sum_eq_zero fun j _ => ?_
      simp [hic']
    · intro hc'; exact (hc' (Finset.mem_univ c')).elim
  have hrhs : ∑ i : Fin d, ∑ j : Fin m,
      (if c = i then X s j else 0) * (if j = s' then V i c' else 0) = X s s' * V c c' := by
    rw [Finset.sum_eq_single c]
    · rw [Finset.sum_eq_single s']
      · simp
      · intro j _ hjs'; simp [hjs']
      · intro hs'; exact (hs' (Finset.mem_univ s')).elim
    · intro i _ hic
      refine Finset.sum_eq_zero fun j _ => ?_
      simp [Ne.symm hic]
    · intro hc; exact (hc (Finset.mem_univ c)).elim
  rw [hlhs, hrhs, mul_comm]

lemma logicalUnitary_unitary {d m : ℕ} {V : Matrix (Fin d) (Fin d) ℂ}
    (hV : Vᴴ * V = 1) :
    (logicalUnitary (m := m) V)ᴴ * logicalUnitary (m := m) V = 1 := by
  ext ⟨c, s⟩ ⟨c', s'⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Matrix.conjTranspose_apply, logicalUnitary, Matrix.one_apply, Prod.mk.injEq]
  by_cases hs : s = s'
  · subst hs
    have hsum : ∑ i : Fin d, ∑ j : Fin m,
        star (if j = s then V i c else 0) * (if j = s then V i c' else 0) =
        (Vᴴ * V) c c' := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single s]
      · simp [Matrix.conjTranspose_apply]
      · intro j _ hjs; simp [hjs]
      · intro hs; exact (hs (Finset.mem_univ s)).elim
    rw [hsum, hV, Matrix.one_apply]
    simp
  · simp only [hs, and_false, ↓reduceIte]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j = s
    · subst hj; simp [hs]
    · simp [hj]

/-- **Theorem 3(c)** (Observer-Separated Channels Satisfy Exact Cross-Perspective Consistency
While Achieving `F_A = F_B = 1`):
For any unitary scrambling map `V_B` (`V_Bᴴ V_B = 1`), the observer-separated channels
`Φ_A(ρ) = ρ` and `Φ_B(ρ) = (V_B ⊗ I_sh) ρ (V_B ⊗ I_sh)ᴴ` are each exactly invertible
(entanglement fidelity 1 via `R_A = id`, `R_B(σ) = (V_Bᴴ ⊗ I_sh) σ (V_B ⊗ I_sh)`) AND
satisfy exact Cross-Perspective Consistency on every shared observable `I_C ⊗ X_sh`. -/
theorem observer_separated_cpl_consistency {d m : ℕ} (hd : 0 < d)
    (V : Matrix (Fin d) (Fin d) ℂ) (hV : Vᴴ * V = 1)
    (X : Matrix (Fin m) (Fin m) ℂ)
    (ρ : Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ) :
    (sharedObs (d := d) X *
      (logicalUnitary V * ρ * (logicalUnitary V)ᴴ)).trace =
      (sharedObs (d := d) X * ρ).trace ∧
    Complex.normSq ((Vᴴ * V).trace) / ((d : ℝ) ^ 2) = 1 := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hd2_ne : (d : ℝ) ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hd_pos)
  constructor
  · calc (sharedObs (d := d) X * (logicalUnitary V * ρ * (logicalUnitary V)ᴴ)).trace
        = ((sharedObs (d := d) X * logicalUnitary V * ρ) * (logicalUnitary V)ᴴ).trace := by
            simp [Matrix.mul_assoc]
      _ = ((logicalUnitary V * sharedObs (d := d) X * ρ) * (logicalUnitary V)ᴴ).trace := by
            rw [logicalUnitary_comm_sharedObs]
      _ = ((logicalUnitary V)ᴴ * (logicalUnitary V * sharedObs (d := d) X * ρ)).trace :=
            Matrix.trace_mul_comm _ _
      _ = (((logicalUnitary V)ᴴ * logicalUnitary V) * (sharedObs (d := d) X * ρ)).trace := by
            simp [Matrix.mul_assoc]
      _ = (sharedObs (d := d) X * ρ).trace := by
            rw [logicalUnitary_unitary hV, Matrix.one_mul]
  · rw [hV, Matrix.trace_one, Fintype.card_fin, Complex.normSq_natCast, ← sq, div_self hd2_ne]

/-!
### Theorem 3(c') and 3(e): Asymmetric Kay-Boundary Choi Saturation & Causal Shared-Record Instrument
-/

/-- **Theorem 3(c')** (Exact Valid CPTP Choi Attainment Along the Asymmetric Kay Curved Boundary):
For any `d ≥ 2` and any `x ∈ [0, 1]`, setting `a = 1/d`, `b = √(1 - a²)`,
`u_j = |Φ_d⟩_{RA'}|j⟩_{B'}`, `v_j = |Φ_d⟩_{RB'}|j⟩_{A'}`, `w_j = (v_j - a u_j) / b`,
the uniform mixture `σ(x) = (1/d) ∑_j |ψ_j(x)⟩⟨ψ_j(x)|` with
`ψ_j(x) = √x u_j + √(1-x) w_j` satisfies:
1. every `ψ_j(x)` is normalized (`‖ψ_j(x)‖² = 1`);
2. `F_A(ψ_j(x)) = x` and `F_B(ψ_j(x)) = (a √x + b √(1-x))²` (attaining the Kay curved bound);
3. the exact CPTP Choi marginal condition `Tr_{A'B'}(σ(x)) = I_R / d`. -/
theorem asymmetric_kay_choi_saturation (hd : 2 ≤ d) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∃ ψ : Fin d → TriIdx d → ℂ,
      (∀ j, vecNormSq (ψ j) = 1) ∧
      (∀ j, (vecInner (ψ j) ((projA d).mulVec (ψ j))).re = x ∧
            (vecInner (ψ j) ((projB d).mulVec (ψ j))).re =
              ((d : ℝ)⁻¹ * Real.sqrt x +
                Real.sqrt (1 - ((d : ℝ) ^ 2)⁻¹) * Real.sqrt (1 - x)) ^ 2) ∧
      (∀ r r' : Fin d,
        ((d : ℂ)⁻¹ * ∑ j : Fin d, ∑ a : Fin d, ∑ b : Fin d,
          ψ j (r, a, b) * star (ψ j (r', a, b))) =
        if r = r' then (d : ℂ)⁻¹ else 0) := by
  have hd_pos_nat : 0 < d := by omega
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd_pos_nat
  have hd_ge2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
  have hd_cne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd_pos_nat)
  set a : ℝ := (d : ℝ)⁻¹
  have hb2_pos : 0 < 1 - ((d : ℝ) ^ 2)⁻¹ := by
    have h4 : (4 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
    have hinv : ((d : ℝ) ^ 2)⁻¹ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h4
    linarith
  set b : ℝ := Real.sqrt (1 - ((d : ℝ) ^ 2)⁻¹)
  have hb_pos : 0 < b := Real.sqrt_pos.mpr hb2_pos
  have hb_ne : b ≠ 0 := ne_of_gt hb_pos
  have hb_sq : b ^ 2 = 1 - a ^ 2 := by
    have : 1 - ((d : ℝ) ^ 2)⁻¹ = 1 - a ^ 2 := by simp [a, inv_pow]
    rw [← this]; exact Real.sq_sqrt (le_of_lt hb2_pos)
  set α : ℝ := Real.sqrt x - a * Real.sqrt (1 - x) / b
  set β : ℝ := Real.sqrt (1 - x) / b
  have hαβ_norm : α ^ 2 + β ^ 2 + 2 * a * α * β = 1 := by
    have hsx : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx0
    have hs1x : (Real.sqrt (1 - x)) ^ 2 = 1 - x := Real.sq_sqrt (by linarith)
    have hkey : α ^ 2 + β ^ 2 + 2 * a * α * β =
        (Real.sqrt x) ^ 2 + (Real.sqrt (1 - x)) ^ 2 * ((1 - a ^ 2) / b ^ 2) := by
      simp only [α, β]; field_simp [hb_ne]; ring
    rw [hkey, ← hb_sq, div_self (pow_ne_zero 2 hb_ne), mul_one, hsx, hs1x]; ring
  have hα_aβ : α + a * β = Real.sqrt x := by
    simp only [α, β]; ring
  have haα_β : a * α + β = a * Real.sqrt x + b * Real.sqrt (1 - x) := by
    have h1 : a * α + β = a * Real.sqrt x + ((1 - a ^ 2) / b) * Real.sqrt (1 - x) := by
      simp only [α, β]; field_simp [hb_ne]; ring
    rw [h1, ← hb_sq, show b ^ 2 / b = b by field_simp [hb_ne]]
  set sd : ℝ := (Real.sqrt (d : ℝ))⁻¹
  have hsd_sq : sd ^ 2 = a := by
    simp only [sd, a, inv_pow, Real.sq_sqrt (le_of_lt hd_pos)]
  let rawU : Fin d → TriIdx d → ℂ := fun j y =>
    if y.1 = y.2.1 ∧ y.2.2 = j then (1 : ℂ) else 0
  let rawV : Fin d → TriIdx d → ℂ := fun j y =>
    if y.1 = y.2.2 ∧ y.2.1 = j then (1 : ℂ) else 0
  let ψ : Fin d → TriIdx d → ℂ := fun j y =>
    (sd : ℂ) * ((α : ℂ) * rawU j y + (β : ℂ) * rawV j y)
  have hU_norm : ∀ j, vecNormSq (fun y => (sd : ℂ) * rawU j y) = 1 := by
    intro j; unfold vecNormSq
    simp only [Complex.normSq_mul, Complex.normSq_ofReal, ← Finset.mul_sum, Fintype.sum_prod_type]
    have hs : ∑ r : Fin d, ∑ p : Fin d, ∑ q : Fin d, Complex.normSq (rawU j (r, p, q)) = (d : ℝ) := by
      have hr : ∀ r : Fin d, ∑ p : Fin d, ∑ q : Fin d, Complex.normSq (rawU j (r, p, q)) = 1 := by
        intro r; rw [Finset.sum_eq_single r]
        · rw [Finset.sum_eq_single j]
          · simp [rawU]
          · intro q _ hqj; simp [rawU, hqj]
          · intro h; exact (h (Finset.mem_univ j)).elim
        · intro p _ hpr; refine Finset.sum_eq_zero fun q _ => ?_; simp [rawU, Ne.symm hpr]
        · intro h; exact (h (Finset.mem_univ r)).elim
      simp_rw [hr]; simp
    rw [hs, ← sq, hsd_sq]; exact inv_mul_cancel₀ hd_ne
  have hV_norm : ∀ j, vecNormSq (fun y => (sd : ℂ) * rawV j y) = 1 := by
    intro j; unfold vecNormSq
    simp only [Complex.normSq_mul, Complex.normSq_ofReal, ← Finset.mul_sum, Fintype.sum_prod_type]
    have hs : ∑ r : Fin d, ∑ p : Fin d, ∑ q : Fin d, Complex.normSq (rawV j (r, p, q)) = (d : ℝ) := by
      have hr : ∀ r : Fin d, ∑ p : Fin d, ∑ q : Fin d, Complex.normSq (rawV j (r, p, q)) = 1 := by
        intro r; rw [Finset.sum_eq_single j]
        · rw [Finset.sum_eq_single r]
          · simp [rawV]
          · intro q _ hqr; simp [rawV, Ne.symm hqr]
          · intro h; exact (h (Finset.mem_univ r)).elim
        · intro p _ hpj; refine Finset.sum_eq_zero fun q _ => ?_; simp [rawV, hpj]
        · intro h; exact (h (Finset.mem_univ j)).elim
      simp_rw [hr]; simp
    rw [hs, ← sq, hsd_sq]; exact inv_mul_cancel₀ hd_ne
  have hUV_inner : ∀ j, vecInner (fun y => (sd : ℂ) * rawU j y) (fun y => (sd : ℂ) * rawV j y) = (a : ℂ) := by
    intro j; unfold vecInner
    have hterm : ∀ y : TriIdx d,
        star ((sd : ℂ) * rawU j y) * ((sd : ℂ) * rawV j y) =
        ((sd ^ 2 : ℝ) : ℂ) * (if y = (j, j, j) then (1 : ℂ) else 0) := by
      rintro ⟨r, p, q⟩
      simp only [star_mul', Complex.star_def, Complex.conj_ofReal, Complex.ofReal_pow, rawU, rawV]
      by_cases h : (r, p, q) = (j, j, j)
      · rcases Prod.mk.inj h with ⟨rfl, h2⟩; rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
        simp; ring
      · simp only [h, ↓reduceIte, mul_zero]
        by_cases h1 : r = p ∧ q = j
        · by_cases h2 : r = q ∧ p = j
          · rcases h1 with ⟨rfl, rfl⟩; rcases h2 with ⟨hrq, _⟩
            exact (h (by simp [hrq])).elim
          · rcases h1 with ⟨rfl, rfl⟩
            have hrq : r ≠ q := fun hrq => h2 ⟨hrq, hrq⟩
            simp [hrq]
        · simp [h1]
    simp_rw [hterm, ← Finset.mul_sum]
    rw [Finset.sum_eq_single (j, j, j)]
    · simp [hsd_sq]
    · intro y _ hy; simp [hy]
    · intro h; exact (h (Finset.mem_univ _)).elim
  have hPA_U : ∀ j, (projA d).mulVec (fun y => (sd : ℂ) * rawU j y) = fun y => (sd : ℂ) * rawU j y := by
    intro j; ext ⟨r, p, q⟩
    simp only [Matrix.mulVec, dotProduct, projA, rawU, Fintype.sum_prod_type]
    by_cases h : r = p ∧ q = j
    · rcases h with ⟨rfl, rfl⟩; simp only [true_and, ↓reduceIte, mul_one]
      have hs : ∑ i : Fin d, ∑ p' : Fin d, ∑ q' : Fin d,
          (if i = p' ∧ q = q' then (d : ℂ)⁻¹ else 0) * ((sd : ℂ) * if i = p' ∧ q' = q then 1 else 0) =
          (sd : ℂ) := by
        have hi : ∀ i : Fin d, ∑ p' : Fin d, ∑ q' : Fin d,
            (if i = p' ∧ q = q' then (d : ℂ)⁻¹ else 0) * ((sd : ℂ) * if i = p' ∧ q' = q then 1 else 0) =
            (d : ℂ)⁻¹ * (sd : ℂ) := by
          intro i; rw [Finset.sum_eq_single i]
          · rw [Finset.sum_eq_single q]
            · simp
            · intro q' _ hq'; simp [Ne.symm hq']
            · intro hh; exact (hh (Finset.mem_univ q)).elim
          · intro p' _ hp'; refine Finset.sum_eq_zero fun q' _ => ?_; simp [Ne.symm hp']
          · intro hh; exact (hh (Finset.mem_univ i)).elim
        simp_rw [hi]; simp; field_simp [hd_cne]
      exact hs
    · simp only [h, ↓reduceIte, mul_zero]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun p' _ =>
        Finset.sum_eq_zero fun q' _ => ?_
      by_cases h1 : r = p ∧ i = p' ∧ q = q'
      · rcases h1 with ⟨rfl, rfl, rfl⟩
        have hqj : q ≠ j := fun hqj => h ⟨rfl, hqj⟩
        simp [hqj]
      · simp [h1]
  have hPA_V : ∀ j, (projA d).mulVec (fun y => (sd : ℂ) * rawV j y) =
      fun y => (a : ℂ) * ((sd : ℂ) * rawU j y) := by
    intro j; ext ⟨r, p, q⟩
    simp only [Matrix.mulVec, dotProduct, projA, rawU, rawV, Fintype.sum_prod_type]
    by_cases h : r = p ∧ q = j
    · rcases h with ⟨rfl, rfl⟩; simp only [true_and, ↓reduceIte, mul_one]
      rw [Finset.sum_eq_single q]
      · rw [Finset.sum_eq_single q]
        · rw [Finset.sum_eq_single q]
          · simp [a]
          · intro q' _ hq'; simp [Ne.symm hq']
          · intro hh; exact (hh (Finset.mem_univ q)).elim
        · intro p' _ hp'; refine Finset.sum_eq_zero fun q' _ => ?_; simp [Ne.symm hp']
        · intro hh; exact (hh (Finset.mem_univ q)).elim
      · intro i _ hiq
        refine Finset.sum_eq_zero fun p' _ => Finset.sum_eq_zero fun q' _ => ?_
        by_cases hc : i = p' ∧ q = q'
        · rcases hc with ⟨rfl, rfl⟩; simp [hiq]
        · simp [hc]
      · intro hh; exact (hh (Finset.mem_univ q)).elim
    · simp only [h, ↓reduceIte, mul_zero]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun p' _ =>
        Finset.sum_eq_zero fun q' _ => ?_
      by_cases h1 : r = p ∧ i = p' ∧ q = q'
      · rcases h1 with ⟨rfl, rfl, rfl⟩
        have hqj : q ≠ j := fun hqj => h ⟨rfl, hqj⟩
        by_cases h2 : i = q ∧ i = j
        · exact (hqj (h2.1.symm.trans h2.2)).elim
        · simp [h2]
      · simp [h1]
  have hPB_V : ∀ j, (projB d).mulVec (fun y => (sd : ℂ) * rawV j y) = fun y => (sd : ℂ) * rawV j y := by
    intro j; ext ⟨r, p, q⟩
    simp only [Matrix.mulVec, dotProduct, projB, rawV, Fintype.sum_prod_type]
    by_cases h : r = q ∧ p = j
    · rcases h with ⟨rfl, rfl⟩; simp only [true_and, ↓reduceIte, mul_one]
      have hs : ∑ i : Fin d, ∑ p' : Fin d, ∑ q' : Fin d,
          (if i = q' ∧ p = p' then (d : ℂ)⁻¹ else 0) * ((sd : ℂ) * if i = q' ∧ p' = p then 1 else 0) =
          (sd : ℂ) := by
        have hi : ∀ i : Fin d, ∑ p' : Fin d, ∑ q' : Fin d,
            (if i = q' ∧ p = p' then (d : ℂ)⁻¹ else 0) * ((sd : ℂ) * if i = q' ∧ p' = p then 1 else 0) =
            (d : ℂ)⁻¹ * (sd : ℂ) := by
          intro i; rw [Finset.sum_eq_single p]
          · rw [Finset.sum_eq_single i]
            · simp
            · intro q' _ hq'; simp [Ne.symm hq']
            · intro hh; exact (hh (Finset.mem_univ i)).elim
          · intro p' _ hp'; refine Finset.sum_eq_zero fun q' _ => ?_; simp [Ne.symm hp']
          · intro hh; exact (hh (Finset.mem_univ p)).elim
        simp_rw [hi]; simp; field_simp [hd_cne]
      exact hs
    · simp only [h, ↓reduceIte, mul_zero]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun p' _ =>
        Finset.sum_eq_zero fun q' _ => ?_
      by_cases h1 : r = q ∧ i = q' ∧ p = p'
      · rcases h1 with ⟨rfl, rfl, rfl⟩
        have hpj : p ≠ j := fun hpj => h ⟨rfl, hpj⟩
        simp [hpj]
      · simp [h1]
  have hPB_U : ∀ j, (projB d).mulVec (fun y => (sd : ℂ) * rawU j y) =
      fun y => (a : ℂ) * ((sd : ℂ) * rawV j y) := by
    intro j; ext ⟨r, p, q⟩
    simp only [Matrix.mulVec, dotProduct, projB, rawU, rawV, Fintype.sum_prod_type]
    by_cases h : r = q ∧ p = j
    · rcases h with ⟨rfl, rfl⟩; simp only [true_and, ↓reduceIte, mul_one]
      rw [Finset.sum_eq_single p]
      · rw [Finset.sum_eq_single p]
        · rw [Finset.sum_eq_single p]
          · simp [a]
          · intro q' _ hq'; simp [Ne.symm hq']
          · intro hh; exact (hh (Finset.mem_univ p)).elim
        · intro p' _ hp'; refine Finset.sum_eq_zero fun q' _ => ?_; simp [Ne.symm hp']
        · intro hh; exact (hh (Finset.mem_univ p)).elim
      · intro i _ hip
        refine Finset.sum_eq_zero fun p' _ => Finset.sum_eq_zero fun q' _ => ?_
        by_cases hc : i = q' ∧ p = p'
        · rcases hc with ⟨rfl, rfl⟩; simp [hip]
        · simp [hc]
      · intro hh; exact (hh (Finset.mem_univ p)).elim
    · simp only [h, ↓reduceIte, mul_zero]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun p' _ =>
        Finset.sum_eq_zero fun q' _ => ?_
      by_cases h1 : r = q ∧ i = q' ∧ p = p'
      · rcases h1 with ⟨rfl, rfl, rfl⟩
        have hpj : p ≠ j := fun hpj => h ⟨rfl, hpj⟩
        by_cases h2 : i = p ∧ i = j
        · exact (hpj (h2.1.symm.trans h2.2)).elim
        · simp [h2]
      · simp [h1]
  have hψ_split : ∀ j, ψ j = fun y =>
      (α : ℂ) * ((sd : ℂ) * rawU j y) + (β : ℂ) * ((sd : ℂ) * rawV j y) := by
    intro j; ext y; simp only [ψ]; ring
  refine ⟨ψ, ?_, ?_, ?_⟩
  · intro j
    rw [hψ_split j]
    have hlin : vecNormSq (fun y => (α : ℂ) * ((sd : ℂ) * rawU j y) + (β : ℂ) * ((sd : ℂ) * rawV j y)) =
        α ^ 2 * vecNormSq (fun y => (sd : ℂ) * rawU j y) +
        β ^ 2 * vecNormSq (fun y => (sd : ℂ) * rawV j y) +
        2 * α * β * (vecInner (fun y => (sd : ℂ) * rawU j y) (fun y => (sd : ℂ) * rawV j y)).re := by
      unfold vecNormSq vecInner
      rw [Complex.re_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.star_def,
        Complex.conj_re, Complex.conj_im]
      ring
    rw [hlin, hU_norm j, hV_norm j, hUV_inner j, Complex.ofReal_re]
    linarith [hαβ_norm]
  · intro j
    have hPAψ : (projA d).mulVec (ψ j) = fun y => ((α + a * β : ℝ) : ℂ) * ((sd : ℂ) * rawU j y) := by
      rw [hψ_split j]
      have h1 : (projA d).mulVec (fun y => (α : ℂ) * ((sd : ℂ) * rawU j y) + (β : ℂ) * ((sd : ℂ) * rawV j y)) =
          fun y => (α : ℂ) * ((projA d).mulVec (fun y => (sd : ℂ) * rawU j y) y) +
                   (β : ℂ) * ((projA d).mulVec (fun y => (sd : ℂ) * rawV j y) y) := by
        ext y; simp only [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1 <;> refine Finset.sum_congr rfl fun z _ => by ring
      rw [h1, hPA_U j, hPA_V j]; ext y; push_cast; ring
    have hPBψ : (projB d).mulVec (ψ j) = fun y => ((a * α + β : ℝ) : ℂ) * ((sd : ℂ) * rawV j y) := by
      rw [hψ_split j]
      have h1 : (projB d).mulVec (fun y => (α : ℂ) * ((sd : ℂ) * rawU j y) + (β : ℂ) * ((sd : ℂ) * rawV j y)) =
          fun y => (α : ℂ) * ((projB d).mulVec (fun y => (sd : ℂ) * rawU j y) y) +
                   (β : ℂ) * ((projB d).mulVec (fun y => (sd : ℂ) * rawV j y) y) := by
        ext y; simp only [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1 <;> refine Finset.sum_congr rfl fun z _ => by ring
      rw [h1, hPB_U j, hPB_V j]; ext y; push_cast; ring
    constructor
    · have hsq : (vecInner (ψ j) ((projA d).mulVec (ψ j))).re = vecNormSq ((projA d).mulVec (ψ j)) := by
        rw [← vecInner_self_re]
        congr 1; symm
        calc vecInner ((projA d).mulVec (ψ j)) ((projA d).mulVec (ψ j))
            = vecInner ((projA d)ᴴ.mulVec (ψ j)) ((projA d).mulVec (ψ j)) := by rw [projA_hermitian]
          _ = vecInner (ψ j) ((projA d).mulVec ((projA d).mulVec (ψ j))) :=
              (vecInner_mulVec_right (projA d) (ψ j) ((projA d).mulVec (ψ j))).symm
          _ = vecInner (ψ j) ((projA d * projA d).mulVec (ψ j)) := by rw [Matrix.mulVec_mulVec]
          _ = vecInner (ψ j) ((projA d).mulVec (ψ j)) := by rw [projA_mul_projA d hd_pos_nat]
      rw [hsq, hPAψ]
      unfold vecNormSq
      simp only [Complex.normSq_mul, Complex.normSq_ofReal, ← Finset.mul_sum]
      have hU' : sd * sd * ∑ i : TriIdx d, Complex.normSq (rawU j i) = 1 := by
        have := hU_norm j; unfold vecNormSq at this
        simpa only [Complex.normSq_mul, Complex.normSq_ofReal, ← Finset.mul_sum] using this
      rw [hU', mul_one, ← sq, hα_aβ, Real.sq_sqrt hx0]
    · have hsq : (vecInner (ψ j) ((projB d).mulVec (ψ j))).re = vecNormSq ((projB d).mulVec (ψ j)) := by
        rw [← vecInner_self_re]
        congr 1; symm
        calc vecInner ((projB d).mulVec (ψ j)) ((projB d).mulVec (ψ j))
            = vecInner ((projB d)ᴴ.mulVec (ψ j)) ((projB d).mulVec (ψ j)) := by rw [projB_hermitian]
          _ = vecInner (ψ j) ((projB d).mulVec ((projB d).mulVec (ψ j))) :=
              (vecInner_mulVec_right (projB d) (ψ j) ((projB d).mulVec (ψ j))).symm
          _ = vecInner (ψ j) ((projB d * projB d).mulVec (ψ j)) := by rw [Matrix.mulVec_mulVec]
          _ = vecInner (ψ j) ((projB d).mulVec (ψ j)) := by rw [projB_mul_projB d hd_pos_nat]
      rw [hsq, hPBψ]
      unfold vecNormSq
      simp only [Complex.normSq_mul, Complex.normSq_ofReal, ← Finset.mul_sum]
      have hV' : sd * sd * ∑ i : TriIdx d, Complex.normSq (rawV j i) = 1 := by
        have := hV_norm j; unfold vecNormSq at this
        simpa only [Complex.normSq_mul, Complex.normSq_ofReal, ← Finset.mul_sum] using this
      rw [hV', mul_one, ← sq, haα_β]
  · intro r r'
    have hfactor : ∀ j p q : Fin d,
        ψ j (r, p, q) * star (ψ j (r', p, q)) =
        (((sd ^ 2 : ℝ) : ℂ)) * (
          (((α ^ 2 : ℝ) : ℂ)) * (if r = p ∧ q = j ∧ r' = p then (1 : ℂ) else 0) +
          (((α * β : ℝ) : ℂ)) * (if r = p ∧ q = j ∧ r' = q ∧ p = j then (1 : ℂ) else 0) +
          (((α * β : ℝ) : ℂ)) * (if r = q ∧ p = j ∧ r' = p ∧ q = j then (1 : ℂ) else 0) +
          (((β ^ 2 : ℝ) : ℂ)) * (if r = q ∧ p = j ∧ r' = q then (1 : ℂ) else 0)) := by
      intro j p q
      have hstar_ite : ∀ (P : Prop) [Decidable P],
          star (if P then (1 : ℂ) else 0) = if P then (1 : ℂ) else 0 := by
        intro P _; by_cases hP : P <;> simp [hP]
      have hmul_ite : ∀ (P Q : Prop) [Decidable P] [Decidable Q],
          (if P then (1 : ℂ) else 0) * (if Q then (1 : ℂ) else 0) =
          if P ∧ Q then (1 : ℂ) else 0 := by
        intro P Q _ _; by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]
      simp only [ψ, rawU, rawV, star_mul', star_add, Complex.star_def, Complex.conj_ofReal,
        hstar_ite, Complex.ofReal_pow, Complex.ofReal_mul]
      have h1 : (if r = p ∧ q = j then (1 : ℂ) else 0) * (if r' = p ∧ q = j then (1 : ℂ) else 0) =
          if r = p ∧ q = j ∧ r' = p then (1 : ℂ) else 0 := by
        rw [hmul_ite]; exact if_congr (by tauto) rfl rfl
      have h2 : (if r = p ∧ q = j then (1 : ℂ) else 0) * (if r' = q ∧ p = j then (1 : ℂ) else 0) =
          if r = p ∧ q = j ∧ r' = q ∧ p = j then (1 : ℂ) else 0 := by
        rw [hmul_ite]; exact if_congr (by tauto) rfl rfl
      have h3 : (if r = q ∧ p = j then (1 : ℂ) else 0) * (if r' = p ∧ q = j then (1 : ℂ) else 0) =
          if r = q ∧ p = j ∧ r' = p ∧ q = j then (1 : ℂ) else 0 := by
        rw [hmul_ite]; exact if_congr (by tauto) rfl rfl
      have h4 : (if r = q ∧ p = j then (1 : ℂ) else 0) * (if r' = q ∧ p = j then (1 : ℂ) else 0) =
          if r = q ∧ p = j ∧ r' = q then (1 : ℂ) else 0 := by
        rw [hmul_ite]; exact if_congr (by tauto) rfl rfl
      calc _
          = (sd : ℂ) ^ 2 * (
              (α : ℂ) ^ 2 * ((if r = p ∧ q = j then 1 else 0) * (if r' = p ∧ q = j then 1 else 0)) +
              ((α : ℂ) * (β : ℂ)) * ((if r = p ∧ q = j then 1 else 0) * (if r' = q ∧ p = j then 1 else 0)) +
              ((α : ℂ) * (β : ℂ)) * ((if r = q ∧ p = j then 1 else 0) * (if r' = p ∧ q = j then 1 else 0)) +
              (β : ℂ) ^ 2 * ((if r = q ∧ p = j then 1 else 0) * (if r' = q ∧ p = j then 1 else 0))) := by ring
        _ = _ := by rw [h1, h2, h3, h4]
    simp_rw [hfactor, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
    have ht1 : ∑ j : Fin d, ∑ p : Fin d, ∑ q : Fin d,
        (if r = p ∧ q = j ∧ r' = p then (1 : ℂ) else 0) = if r = r' then (d : ℂ) else 0 := by
      by_cases hrr : r = r'
      · subst hrr; simp only [↓reduceIte]
        have h1 : ∀ j : Fin d, ∑ p : Fin d, ∑ q : Fin d,
            (if r = p ∧ q = j ∧ r = p then (1 : ℂ) else 0) = 1 := by
          intro j; rw [Finset.sum_eq_single r]
          · rw [Finset.sum_eq_single j]
            · simp
            · intro q _ hqj; simp [hqj]
            · intro h; exact (h (Finset.mem_univ j)).elim
          · intro p _ hpr; refine Finset.sum_eq_zero fun q _ => ?_; simp [Ne.symm hpr]
          · intro h; exact (h (Finset.mem_univ r)).elim
        simp_rw [h1]; simp
      · simp only [hrr, ↓reduceIte]
        refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun p _ =>
          Finset.sum_eq_zero fun q _ => ?_
        by_cases h : r = p ∧ q = j ∧ r' = p
        · exact (hrr (h.1.trans h.2.2.symm)).elim
        · simp [h]
    have ht2 : ∑ j : Fin d, ∑ p : Fin d, ∑ q : Fin d,
        (if r = p ∧ q = j ∧ r' = q ∧ p = j then (1 : ℂ) else 0) = if r = r' then 1 else 0 := by
      by_cases hrr : r = r'
      · subst hrr; simp only [↓reduceIte]
        rw [Finset.sum_eq_single r]
        · rw [Finset.sum_eq_single r]
          · rw [Finset.sum_eq_single r]
            · simp
            · intro q _ hqr; simp [hqr]
            · intro h; exact (h (Finset.mem_univ r)).elim
          · intro p _ hpr; refine Finset.sum_eq_zero fun q _ => ?_; simp [Ne.symm hpr]
          · intro h; exact (h (Finset.mem_univ r)).elim
        · intro j _ hjr; refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
          by_cases h : r = p ∧ q = j ∧ r = q ∧ p = j
          · exact (hjr (h.2.2.1.trans h.2.1).symm).elim
          · simp [h]
        · intro h; exact (h (Finset.mem_univ r)).elim
      · simp only [hrr, ↓reduceIte]
        refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun p _ =>
          Finset.sum_eq_zero fun q _ => ?_
        by_cases h : r = p ∧ q = j ∧ r' = q ∧ p = j
        · exact (hrr ((h.1.trans h.2.2.2).trans (h.2.2.1.trans h.2.1).symm)).elim
        · simp [h]
    have ht3 : ∑ j : Fin d, ∑ p : Fin d, ∑ q : Fin d,
        (if r = q ∧ p = j ∧ r' = p ∧ q = j then (1 : ℂ) else 0) = if r = r' then 1 else 0 := by
      by_cases hrr : r = r'
      · subst hrr; simp only [↓reduceIte]
        rw [Finset.sum_eq_single r]
        · rw [Finset.sum_eq_single r]
          · rw [Finset.sum_eq_single r]
            · simp
            · intro q _ hqr; simp [hqr]
            · intro h; exact (h (Finset.mem_univ r)).elim
          · intro p _ hpr; refine Finset.sum_eq_zero fun q _ => ?_; simp [Ne.symm hpr]
          · intro h; exact (h (Finset.mem_univ r)).elim
        · intro j _ hjr; refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
          by_cases h : r = q ∧ p = j ∧ r = p ∧ q = j
          · exact (hjr (h.1.trans h.2.2.2).symm).elim
          · simp [h]
        · intro h; exact (h (Finset.mem_univ r)).elim
      · simp only [hrr, ↓reduceIte]
        refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun p _ =>
          Finset.sum_eq_zero fun q _ => ?_
        by_cases h : r = q ∧ p = j ∧ r' = p ∧ q = j
        · exact (hrr ((h.1.trans h.2.2.2).trans (h.2.2.1.trans h.2.1).symm)).elim
        · simp [h]
    have ht4 : ∑ j : Fin d, ∑ p : Fin d, ∑ q : Fin d,
        (if r = q ∧ p = j ∧ r' = q then (1 : ℂ) else 0) = if r = r' then (d : ℂ) else 0 := by
      by_cases hrr : r = r'
      · subst hrr; simp only [↓reduceIte]
        have h1 : ∀ j : Fin d, ∑ p : Fin d, ∑ q : Fin d,
            (if r = q ∧ p = j ∧ r = q then (1 : ℂ) else 0) = 1 := by
          intro j; rw [Finset.sum_eq_single j]
          · rw [Finset.sum_eq_single r]
            · simp
            · intro q _ hqr; simp [Ne.symm hqr]
            · intro h; exact (h (Finset.mem_univ r)).elim
          · intro p _ hpj; refine Finset.sum_eq_zero fun q _ => ?_; simp [hpj]
          · intro h; exact (h (Finset.mem_univ j)).elim
        simp_rw [h1]; simp
      · simp only [hrr, ↓reduceIte]
        refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun p _ =>
          Finset.sum_eq_zero fun q _ => ?_
        by_cases h : r = q ∧ p = j ∧ r' = q
        · exact (hrr (h.1.trans h.2.2.symm)).elim
        · simp [h]
    rw [ht1, ht2, ht3, ht4, hsd_sq]
    by_cases hrr : r = r'
    · simp only [hrr, ↓reduceIte]
      have hnormC : (((α ^ 2 + β ^ 2 + 2 * a * α * β : ℝ) : ℂ)) = 1 := by
        rw [hαβ_norm, Complex.ofReal_one]
      have hcalc : (d : ℂ)⁻¹ * ((a : ℂ) * ((α ^ 2 : ℂ) * (d : ℂ) + (α * β : ℂ) * 1 +
          (α * β : ℂ) * 1 + (β ^ 2 : ℂ) * (d : ℂ))) =
          (d : ℂ)⁻¹ * (((α ^ 2 + β ^ 2 + 2 * a * α * β : ℝ) : ℂ)) := by
        simp only [a, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_add,
          Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
        field_simp [hd_cne]; ring
      push_cast at hcalc hnormC ⊢
      rw [hcalc, hnormC, mul_one]
    · simp [hrr]

/-- Record-basis Lüders Kraus operator `M_x = I_C ⊗ |x⟩⟨x|_{rec}` on `Fin d × Fin m`. -/
def recordKraus {d m : ℕ} (x : Fin m) :
    Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ :=
  fun p q => if p.1 = q.1 ∧ p.2 = x ∧ q.2 = x then 1 else 0

/-- **Theorem 3(e)** (Causal Shared-Record Preparation, Decoding, and Sequential Readout Instrument):
On `H_C ⊗ H_{rec}` (`Fin d × Fin m`) with arbitrary logical encoding unitary `V_B` (`V_Bᴴ V_B = 1`)
and shared-record Lüders instrument `{M_x = I_C ⊗ |x⟩⟨x|_{rec}}`:
1. Complete positivity / trace preservation: `∑_x M_xᴴ M_x = 1`.
2. Exact single-trial sequential record agreement: for every state `ρ` and every `x ≠ y`,
   `M_y (V_B ⊗ I_{rec}) M_x ρ M_xᴴ (V_B ⊗ I_{rec})ᴴ M_yᴴ = 0` (zero disagreement probability).
3. Exact local marginal agreement on every classical record observable `I_C ⊗ diag(f)` under
   both `V_B ⊗ I_{rec}` and the non-selective instrument sum `∑_x M_x (·) M_xᴴ`. -/
theorem shared_causal_record_instrument_agreement {d m : ℕ}
    (V : Matrix (Fin d) (Fin d) ℂ) (hV : Vᴴ * V = 1)
    (f : Fin m → ℂ) (ρ : Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ) :
    (∑ x : Fin m, (recordKraus (d := d) x)ᴴ * recordKraus (d := d) x) = 1 ∧
    (∀ x y : Fin m, x ≠ y →
      recordKraus (d := d) y * logicalUnitary V * recordKraus (d := d) x * ρ *
        (recordKraus (d := d) x)ᴴ * (logicalUnitary V)ᴴ * (recordKraus (d := d) y)ᴴ = 0) ∧
    (sharedObs (d := d) (Matrix.diagonal f) *
      (∑ x : Fin m, recordKraus (d := d) x * (logicalUnitary V * ρ * (logicalUnitary V)ᴴ) *
        (recordKraus (d := d) x)ᴴ)).trace =
      (sharedObs (d := d) (Matrix.diagonal f) * ρ).trace := by
  have hM_dag : ∀ x : Fin m, (recordKraus (d := d) x)ᴴ = recordKraus (d := d) x := by
    intro x; ext p q
    simp only [Matrix.conjTranspose_apply, recordKraus]
    by_cases h : q.1 = p.1 ∧ q.2 = x ∧ p.2 = x
    · have h' : p.1 = q.1 ∧ p.2 = x ∧ q.2 = x := ⟨h.1.symm, h.2.2, h.2.1⟩
      have hL : (if q.1 = p.1 ∧ q.2 = x ∧ p.2 = x then (1 : ℂ) else 0) = 1 := by simp [h]
      have hR : (if p.1 = q.1 ∧ p.2 = x ∧ q.2 = x then (1 : ℂ) else 0) = 1 := by simp [h']
      rw [hL, hR, star_one]
    · have h' : ¬(p.1 = q.1 ∧ p.2 = x ∧ q.2 = x) := fun hh => h ⟨hh.1.symm, hh.2.2, hh.2.1⟩
      have hL : (if q.1 = p.1 ∧ q.2 = x ∧ p.2 = x then (1 : ℂ) else 0) = 0 := by simp [h]
      have hR : (if p.1 = q.1 ∧ p.2 = x ∧ q.2 = x then (1 : ℂ) else 0) = 0 := by simp [h']
      rw [hL, hR, star_zero]
  have hM_mul : ∀ x y : Fin m,
      recordKraus (d := d) x * recordKraus (d := d) y =
      if x = y then recordKraus (d := d) x else 0 := by
    intro x y; ext ⟨c, s⟩ ⟨c', s'⟩
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    by_cases hxy : x = y
    · subst hxy; simp only [↓reduceIte, recordKraus]
      by_cases hc : c = c' ∧ s = x ∧ s' = x
      · rcases hc with ⟨rfl, rfl, rfl⟩; simp only [true_and, ↓reduceIte]
        rw [Finset.sum_eq_single c]
        · rw [Finset.sum_eq_single s']
          · simp
          · intro j _ hjs; simp [hjs]
          · intro hh; exact (hh (Finset.mem_univ s')).elim
        · intro i _ hic; refine Finset.sum_eq_zero fun j _ => ?_; simp [Ne.symm hic]
        · intro hh; exact (hh (Finset.mem_univ c)).elim
      · simp only [hc, ↓reduceIte]
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
        by_cases h1 : c = i ∧ s = x ∧ j = x
        · by_cases h2 : i = c' ∧ j = x ∧ s' = x
          · exact (hc ⟨h1.1.trans h2.1, h1.2.1, h2.2.2⟩).elim
          · have hzero : (if i = c' ∧ j = x ∧ s' = x then (1 : ℂ) else 0) = 0 := by simp [h2]
            rw [hzero, mul_zero]
        · have hzero : (if c = i ∧ s = x ∧ j = x then (1 : ℂ) else 0) = 0 := by simp [h1]
          rw [hzero, zero_mul]
    · simp only [hxy, ↓reduceIte, Matrix.zero_apply, recordKraus]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      by_cases h1 : c = i ∧ s = x ∧ j = x
      · by_cases h2 : i = c' ∧ j = y ∧ s' = y
        · exact (hxy (h1.2.2.symm.trans h2.2.1)).elim
        · have hzero : (if i = c' ∧ j = y ∧ s' = y then (1 : ℂ) else 0) = 0 := by simp [h2]
          rw [hzero, mul_zero]
      · have hzero : (if c = i ∧ s = x ∧ j = x then (1 : ℂ) else 0) = 0 := by simp [h1]
        rw [hzero, zero_mul]
  have hM_comm_V : ∀ x : Fin m,
      recordKraus (d := d) x * logicalUnitary V = logicalUnitary V * recordKraus (d := d) x := by
    intro x
    have hEq : recordKraus (d := d) x = sharedObs (d := d) (Matrix.diagonal fun k => if k = x then 1 else 0) := by
      ext ⟨c, s⟩ ⟨c', s'⟩
      simp only [recordKraus, sharedObs, Matrix.diagonal_apply]
      by_cases h : c = c' ∧ s = x ∧ s' = x
      · rcases h with ⟨rfl, rfl, rfl⟩; simp
      · by_cases h1 : c = c'
        · subst h1
          by_cases h2 : s = s'
          · subst h2
            by_cases h3 : s = x
            · exact (h ⟨rfl, h3, h3⟩).elim
            · simp [h3]
          · have hnot : ¬(s = x ∧ s' = x) := fun hh => h2 (hh.1.trans hh.2.symm)
            simp [h2, hnot]
        · simp [h1]
    rw [hEq, logicalUnitary_comm_sharedObs]
  have hcomp : ∑ x : Fin m, (recordKraus (d := d) x)ᴴ * recordKraus (d := d) x = 1 := by
    ext ⟨c, s⟩ ⟨c', s'⟩
    simp only [hM_dag, hM_mul, ↓reduceIte, Matrix.sum_apply, recordKraus, Matrix.one_apply, Prod.mk.injEq]
    by_cases h : c = c' ∧ s = s'
    · rcases h with ⟨rfl, rfl⟩; simp only [true_and, ↓reduceIte]
      rw [Finset.sum_eq_single s]
      · simp
      · intro x _ hxs; simp [Ne.symm hxs]
      · intro hh; exact (hh (Finset.mem_univ s)).elim
    · simp only [h, ↓reduceIte]
      refine Finset.sum_eq_zero fun x _ => ?_
      by_cases hc : c = c' ∧ s = x ∧ s' = x
      · exact (h ⟨hc.1, hc.2.1.trans hc.2.2.symm⟩).elim
      · simp only [hc, ↓reduceIte]
  refine ⟨hcomp, ?_, ?_⟩
  · intro x y hxy
    have hprod : recordKraus (d := d) y * logicalUnitary V * recordKraus (d := d) x = 0 := by
      rw [Matrix.mul_assoc, ← hM_comm_V x, ← Matrix.mul_assoc, hM_mul y x]
      simp [Ne.symm hxy]
    rw [hprod, Matrix.zero_mul, Matrix.zero_mul, Matrix.zero_mul, Matrix.zero_mul]
  · have hsum_comm : ∀ x : Fin m,
        sharedObs (d := d) (Matrix.diagonal f) * recordKraus (d := d) x =
        recordKraus (d := d) x * sharedObs (d := d) (Matrix.diagonal f) := by
      intro x; ext ⟨c, s⟩ ⟨c', s'⟩
      rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_prod_type]
      simp only [sharedObs, recordKraus, Matrix.diagonal_apply]
      have hL : ∑ i : Fin d, ∑ j : Fin m,
          (if c = i then if s = j then f s else 0 else 0) *
          (if i = c' ∧ j = x ∧ s' = x then 1 else 0) =
          if c = c' ∧ s = x ∧ s' = x then f x else 0 := by
        rw [Finset.sum_eq_single c]
        · rw [Finset.sum_eq_single s]
          · by_cases hc : c = c' ∧ s = x ∧ s' = x
            · rcases hc with ⟨rfl, rfl, rfl⟩; simp
            · simp [hc]
          · intro j _ hjs; simp [Ne.symm hjs]
          · intro hh; exact (hh (Finset.mem_univ s)).elim
        · intro i _ hic; refine Finset.sum_eq_zero fun j _ => ?_; simp [Ne.symm hic]
        · intro hh; exact (hh (Finset.mem_univ c)).elim
      have hR : ∑ i : Fin d, ∑ j : Fin m,
          (if c = i ∧ s = x ∧ j = x then 1 else 0) *
          (if i = c' then if j = s' then f j else 0 else 0) =
          if c = c' ∧ s = x ∧ s' = x then f x else 0 := by
        rw [Finset.sum_eq_single c']
        · rw [Finset.sum_eq_single s']
          · by_cases hc : c = c' ∧ s = x ∧ s' = x
            · rcases hc with ⟨rfl, rfl, rfl⟩; simp
            · simp [hc]
          · intro j _ hjs; simp [hjs]
          · intro hh; exact (hh (Finset.mem_univ s')).elim
        · intro i _ hic; refine Finset.sum_eq_zero fun j _ => ?_; simp [hic]
        · intro hh; exact (hh (Finset.mem_univ c')).elim
      rw [hL, hR]
    set σ := logicalUnitary V * ρ * (logicalUnitary V)ᴴ
    have hpinch : (sharedObs (d := d) (Matrix.diagonal f) *
        ∑ x : Fin m, recordKraus (d := d) x * σ * (recordKraus (d := d) x)ᴴ).trace =
        (sharedObs (d := d) (Matrix.diagonal f) * σ).trace := by
      rw [Finset.mul_sum, Matrix.trace_sum]
      have hterm : ∀ x : Fin m,
          (sharedObs (d := d) (Matrix.diagonal f) *
            (recordKraus (d := d) x * σ * (recordKraus (d := d) x)ᴴ)).trace =
          ((recordKraus (d := d) x)ᴴ * recordKraus (d := d) x *
            (sharedObs (d := d) (Matrix.diagonal f) * σ)).trace := by
        intro x
        calc (sharedObs (d := d) (Matrix.diagonal f) *
                (recordKraus (d := d) x * σ * (recordKraus (d := d) x)ᴴ)).trace
            = ((sharedObs (d := d) (Matrix.diagonal f) * recordKraus (d := d) x) * σ *
                (recordKraus (d := d) x)ᴴ).trace := by simp [Matrix.mul_assoc]
          _ = ((recordKraus (d := d) x * sharedObs (d := d) (Matrix.diagonal f)) * σ *
                (recordKraus (d := d) x)ᴴ).trace := by rw [hsum_comm x]
          _ = ((recordKraus (d := d) x)ᴴ *
                (recordKraus (d := d) x * sharedObs (d := d) (Matrix.diagonal f) * σ)).trace :=
                Matrix.trace_mul_comm _ _
          _ = ((recordKraus (d := d) x)ᴴ * recordKraus (d := d) x *
                (sharedObs (d := d) (Matrix.diagonal f) * σ)).trace := by simp [Matrix.mul_assoc]
      simp_rw [hterm]
      rw [← Matrix.trace_sum, ← Finset.sum_mul, hcomp, Matrix.one_mul]
    rw [hpinch]
    calc (sharedObs (d := d) (Matrix.diagonal f) *
            (logicalUnitary V * ρ * (logicalUnitary V)ᴴ)).trace
        = ((sharedObs (d := d) (Matrix.diagonal f) * logicalUnitary V * ρ) *
            (logicalUnitary V)ᴴ).trace := by simp [Matrix.mul_assoc]
      _ = ((logicalUnitary V * sharedObs (d := d) (Matrix.diagonal f) * ρ) *
            (logicalUnitary V)ᴴ).trace := by rw [logicalUnitary_comm_sharedObs]
      _ = ((logicalUnitary V)ᴴ *
            (logicalUnitary V * sharedObs (d := d) (Matrix.diagonal f) * ρ)).trace :=
            Matrix.trace_mul_comm _ _
      _ = (((logicalUnitary V)ᴴ * logicalUnitary V) *
            (sharedObs (d := d) (Matrix.diagonal f) * ρ)).trace := by simp [Matrix.mul_assoc]
      _ = (sharedObs (d := d) (Matrix.diagonal f) * ρ).trace := by
            rw [logicalUnitary_unitary hV, Matrix.one_mul]

/-- Auxiliary family lemma: for any `d ≥ 2` and real coefficients `(α, β)` with
`α² + β² + 2 d⁻¹ α β = 1`, the equal-weight Choi mixture of `ψ_j = α u_j + β v_j`
consists of unit vectors with `F_A = (α + d⁻¹ β)²`, `F_B = (d⁻¹ α + β)²`, and exact
CPTP Choi marginal `I_R / d`. -/
private lemma choi_linear_family (hd : 2 ≤ d) (α β : ℝ)
    (hnorm : α ^ 2 + β ^ 2 + 2 * (d : ℝ)⁻¹ * α * β = 1) :
    ∃ ψ : Fin d → TriIdx d → ℂ,
      (∀ j, vecNormSq (ψ j) = 1) ∧
      (∀ j, (vecInner (ψ j) ((projA d).mulVec (ψ j))).re = (α + (d : ℝ)⁻¹ * β) ^ 2 ∧
            (vecInner (ψ j) ((projB d).mulVec (ψ j))).re = ((d : ℝ)⁻¹ * α + β) ^ 2) ∧
      (∀ r r' : Fin d,
        ((d : ℂ)⁻¹ * ∑ j : Fin d, ∑ a : Fin d, ∑ b : Fin d,
          ψ j (r, a, b) * star (ψ j (r', a, b))) =
        if r = r' then (d : ℂ)⁻¹ else 0) := by
  have hd_pos_nat : 0 < d := by omega
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd_pos_nat
  have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
  have hd_cne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd_pos_nat)
  set a : ℝ := (d : ℝ)⁻¹
  set sd : ℝ := (Real.sqrt (d : ℝ))⁻¹
  have hsd_sq : sd ^ 2 = a := by
    simp only [sd, a, inv_pow, Real.sq_sqrt (le_of_lt hd_pos)]
  let rawU : Fin d → TriIdx d → ℂ := fun j y =>
    if y.1 = y.2.1 ∧ y.2.2 = j then (1 : ℂ) else 0
  let rawV : Fin d → TriIdx d → ℂ := fun j y =>
    if y.1 = y.2.2 ∧ y.2.1 = j then (1 : ℂ) else 0
  let ψ : Fin d → TriIdx d → ℂ := fun j y =>
    (sd : ℂ) * ((α : ℂ) * rawU j y + (β : ℂ) * rawV j y)
  have hU_norm : ∀ j, vecNormSq (fun y => (sd : ℂ) * rawU j y) = 1 := by
    intro j; unfold vecNormSq
    simp only [Complex.normSq_mul, Complex.normSq_ofReal, ← Finset.mul_sum, Fintype.sum_prod_type]
    have hs : ∑ r : Fin d, ∑ p : Fin d, ∑ q : Fin d, Complex.normSq (rawU j (r, p, q)) = (d : ℝ) := by
      have hr : ∀ r : Fin d, ∑ p : Fin d, ∑ q : Fin d, Complex.normSq (rawU j (r, p, q)) = 1 := by
        intro r; rw [Finset.sum_eq_single r]
        · rw [Finset.sum_eq_single j]
          · simp [rawU]
          · intro q _ hqj; simp [rawU, hqj]
          · intro h; exact (h (Finset.mem_univ j)).elim
        · intro p _ hpr; refine Finset.sum_eq_zero fun q _ => ?_; simp [rawU, Ne.symm hpr]
        · intro h; exact (h (Finset.mem_univ r)).elim
      simp_rw [hr]; simp
    rw [hs, ← sq, hsd_sq]; exact inv_mul_cancel₀ hd_ne
  have hV_norm : ∀ j, vecNormSq (fun y => (sd : ℂ) * rawV j y) = 1 := by
    intro j; unfold vecNormSq
    simp only [Complex.normSq_mul, Complex.normSq_ofReal, ← Finset.mul_sum, Fintype.sum_prod_type]
    have hs : ∑ r : Fin d, ∑ p : Fin d, ∑ q : Fin d, Complex.normSq (rawV j (r, p, q)) = (d : ℝ) := by
      have hr : ∀ r : Fin d, ∑ p : Fin d, ∑ q : Fin d, Complex.normSq (rawV j (r, p, q)) = 1 := by
        intro r; rw [Finset.sum_eq_single j]
        · rw [Finset.sum_eq_single r]
          · simp [rawV]
          · intro q _ hqr; simp [rawV, Ne.symm hqr]
          · intro h; exact (h (Finset.mem_univ r)).elim
        · intro p _ hpj; refine Finset.sum_eq_zero fun q _ => ?_; simp [rawV, hpj]
        · intro h; exact (h (Finset.mem_univ j)).elim
      simp_rw [hr]; simp
    rw [hs, ← sq, hsd_sq]; exact inv_mul_cancel₀ hd_ne
  have hUV_inner : ∀ j, vecInner (fun y => (sd : ℂ) * rawU j y) (fun y => (sd : ℂ) * rawV j y) = (a : ℂ) := by
    intro j; unfold vecInner
    have hterm : ∀ y : TriIdx d,
        star ((sd : ℂ) * rawU j y) * ((sd : ℂ) * rawV j y) =
        ((sd ^ 2 : ℝ) : ℂ) * (if y = (j, j, j) then (1 : ℂ) else 0) := by
      rintro ⟨r, p, q⟩
      simp only [star_mul', Complex.star_def, Complex.conj_ofReal, Complex.ofReal_pow, rawU, rawV]
      by_cases h : (r, p, q) = (j, j, j)
      · rcases Prod.mk.inj h with ⟨rfl, h2⟩; rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
        simp; ring
      · simp only [h, ↓reduceIte, mul_zero]
        by_cases h1 : r = p ∧ q = j
        · by_cases h2 : r = q ∧ p = j
          · rcases h1 with ⟨rfl, rfl⟩; rcases h2 with ⟨hrq, _⟩
            exact (h (by simp [hrq])).elim
          · rcases h1 with ⟨rfl, rfl⟩
            have hrq : r ≠ q := fun hrq => h2 ⟨hrq, hrq⟩
            simp [hrq]
        · simp [h1]
    simp_rw [hterm, ← Finset.mul_sum]
    rw [Finset.sum_eq_single (j, j, j)]
    · simp [hsd_sq]
    · intro y _ hy; simp [hy]
    · intro h; exact (h (Finset.mem_univ _)).elim
  have hPA_U : ∀ j, (projA d).mulVec (fun y => (sd : ℂ) * rawU j y) = fun y => (sd : ℂ) * rawU j y := by
    intro j; ext ⟨r, p, q⟩
    simp only [Matrix.mulVec, dotProduct, projA, rawU, Fintype.sum_prod_type]
    by_cases h : r = p ∧ q = j
    · rcases h with ⟨rfl, rfl⟩; simp only [true_and, ↓reduceIte, mul_one]
      have hi : ∀ i : Fin d, ∑ p' : Fin d, ∑ q' : Fin d,
          (if i = p' ∧ q = q' then (d : ℂ)⁻¹ else 0) * ((sd : ℂ) * if i = p' ∧ q' = q then 1 else 0) =
          (d : ℂ)⁻¹ * (sd : ℂ) := by
        intro i; rw [Finset.sum_eq_single i]
        · rw [Finset.sum_eq_single q]
          · simp
          · intro q' _ hq'; simp [Ne.symm hq']
          · intro hh; exact (hh (Finset.mem_univ q)).elim
        · intro p' _ hp'; refine Finset.sum_eq_zero fun q' _ => ?_; simp [Ne.symm hp']
        · intro hh; exact (hh (Finset.mem_univ i)).elim
      simp_rw [hi]; simp; field_simp [hd_cne]
    · simp only [h, ↓reduceIte, mul_zero]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun p' _ =>
        Finset.sum_eq_zero fun q' _ => ?_
      by_cases h1 : r = p ∧ i = p' ∧ q = q'
      · rcases h1 with ⟨rfl, rfl, rfl⟩
        have hqj : q ≠ j := fun hqj => h ⟨rfl, hqj⟩
        simp [hqj]
      · simp [h1]
  have hPA_V : ∀ j, (projA d).mulVec (fun y => (sd : ℂ) * rawV j y) =
      fun y => (a : ℂ) * ((sd : ℂ) * rawU j y) := by
    intro j; ext ⟨r, p, q⟩
    simp only [Matrix.mulVec, dotProduct, projA, rawU, rawV, Fintype.sum_prod_type]
    by_cases h : r = p ∧ q = j
    · rcases h with ⟨rfl, rfl⟩; simp only [true_and, ↓reduceIte, mul_one]
      rw [Finset.sum_eq_single q]
      · rw [Finset.sum_eq_single q]
        · rw [Finset.sum_eq_single q]
          · simp [a]
          · intro q' _ hq'; simp [Ne.symm hq']
          · intro hh; exact (hh (Finset.mem_univ q)).elim
        · intro p' _ hp'; refine Finset.sum_eq_zero fun q' _ => ?_; simp [Ne.symm hp']
        · intro hh; exact (hh (Finset.mem_univ q)).elim
      · intro i _ hiq
        refine Finset.sum_eq_zero fun p' _ => Finset.sum_eq_zero fun q' _ => ?_
        by_cases hc : i = p' ∧ q = q'
        · rcases hc with ⟨rfl, rfl⟩; simp [hiq]
        · simp [hc]
      · intro hh; exact (hh (Finset.mem_univ q)).elim
    · simp only [h, ↓reduceIte, mul_zero]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun p' _ =>
        Finset.sum_eq_zero fun q' _ => ?_
      by_cases h1 : r = p ∧ i = p' ∧ q = q'
      · rcases h1 with ⟨rfl, rfl, rfl⟩
        have hqj : q ≠ j := fun hqj => h ⟨rfl, hqj⟩
        by_cases h2 : i = q ∧ i = j
        · exact (hqj (h2.1.symm.trans h2.2)).elim
        · simp [h2]
      · simp [h1]
  have hPB_V : ∀ j, (projB d).mulVec (fun y => (sd : ℂ) * rawV j y) = fun y => (sd : ℂ) * rawV j y := by
    intro j; ext ⟨r, p, q⟩
    simp only [Matrix.mulVec, dotProduct, projB, rawV, Fintype.sum_prod_type]
    by_cases h : r = q ∧ p = j
    · rcases h with ⟨rfl, rfl⟩; simp only [true_and, ↓reduceIte, mul_one]
      have hi : ∀ i : Fin d, ∑ p' : Fin d, ∑ q' : Fin d,
          (if i = q' ∧ p = p' then (d : ℂ)⁻¹ else 0) * ((sd : ℂ) * if i = q' ∧ p' = p then 1 else 0) =
          (d : ℂ)⁻¹ * (sd : ℂ) := by
        intro i; rw [Finset.sum_eq_single p]
        · rw [Finset.sum_eq_single i]
          · simp
          · intro q' _ hq'; simp [Ne.symm hq']
          · intro hh; exact (hh (Finset.mem_univ i)).elim
        · intro p' _ hp'; refine Finset.sum_eq_zero fun q' _ => ?_; simp [Ne.symm hp']
        · intro hh; exact (hh (Finset.mem_univ p)).elim
      simp_rw [hi]; simp; field_simp [hd_cne]
    · simp only [h, ↓reduceIte, mul_zero]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun p' _ =>
        Finset.sum_eq_zero fun q' _ => ?_
      by_cases h1 : r = q ∧ i = q' ∧ p = p'
      · rcases h1 with ⟨rfl, rfl, rfl⟩
        have hpj : p ≠ j := fun hpj => h ⟨rfl, hpj⟩
        simp [hpj]
      · simp [h1]
  have hPB_U : ∀ j, (projB d).mulVec (fun y => (sd : ℂ) * rawU j y) =
      fun y => (a : ℂ) * ((sd : ℂ) * rawV j y) := by
    intro j; ext ⟨r, p, q⟩
    simp only [Matrix.mulVec, dotProduct, projB, rawU, rawV, Fintype.sum_prod_type]
    by_cases h : r = q ∧ p = j
    · rcases h with ⟨rfl, rfl⟩; simp only [true_and, ↓reduceIte, mul_one]
      rw [Finset.sum_eq_single p]
      · rw [Finset.sum_eq_single p]
        · rw [Finset.sum_eq_single p]
          · simp [a]
          · intro q' _ hq'; simp [Ne.symm hq']
          · intro hh; exact (hh (Finset.mem_univ p)).elim
        · intro p' _ hp'; refine Finset.sum_eq_zero fun q' _ => ?_; simp [Ne.symm hp']
        · intro hh; exact (hh (Finset.mem_univ p)).elim
      · intro i _ hip
        refine Finset.sum_eq_zero fun p' _ => Finset.sum_eq_zero fun q' _ => ?_
        by_cases hc : i = q' ∧ p = p'
        · rcases hc with ⟨rfl, rfl⟩; simp [hip]
        · simp [hc]
      · intro hh; exact (hh (Finset.mem_univ p)).elim
    · simp only [h, ↓reduceIte, mul_zero]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun p' _ =>
        Finset.sum_eq_zero fun q' _ => ?_
      by_cases h1 : r = q ∧ i = q' ∧ p = p'
      · rcases h1 with ⟨rfl, rfl, rfl⟩
        have hpj : p ≠ j := fun hpj => h ⟨rfl, hpj⟩
        by_cases h2 : i = p ∧ i = j
        · exact (hpj (h2.1.symm.trans h2.2)).elim
        · simp [h2]
      · simp [h1]
  have hψ_split : ∀ j, ψ j = fun y =>
      (α : ℂ) * ((sd : ℂ) * rawU j y) + (β : ℂ) * ((sd : ℂ) * rawV j y) := by
    intro j; ext y; simp only [ψ]; ring
  refine ⟨ψ, ?_, ?_, ?_⟩
  · intro j
    rw [hψ_split j]
    have hlin : vecNormSq (fun y => (α : ℂ) * ((sd : ℂ) * rawU j y) + (β : ℂ) * ((sd : ℂ) * rawV j y)) =
        α ^ 2 * vecNormSq (fun y => (sd : ℂ) * rawU j y) +
        β ^ 2 * vecNormSq (fun y => (sd : ℂ) * rawV j y) +
        2 * α * β * (vecInner (fun y => (sd : ℂ) * rawU j y) (fun y => (sd : ℂ) * rawV j y)).re := by
      unfold vecNormSq vecInner
      rw [Complex.re_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.star_def,
        Complex.conj_re, Complex.conj_im]
      ring
    rw [hlin, hU_norm j, hV_norm j, hUV_inner j, Complex.ofReal_re]
    linarith [hnorm]
  · intro j
    have hPAψ : (projA d).mulVec (ψ j) = fun y => ((α + a * β : ℝ) : ℂ) * ((sd : ℂ) * rawU j y) := by
      rw [hψ_split j]
      have h1 : (projA d).mulVec (fun y => (α : ℂ) * ((sd : ℂ) * rawU j y) + (β : ℂ) * ((sd : ℂ) * rawV j y)) =
          fun y => (α : ℂ) * ((projA d).mulVec (fun y => (sd : ℂ) * rawU j y) y) +
                   (β : ℂ) * ((projA d).mulVec (fun y => (sd : ℂ) * rawV j y) y) := by
        ext y; simp only [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1 <;> refine Finset.sum_congr rfl fun z _ => by ring
      rw [h1, hPA_U j, hPA_V j]; ext y; push_cast; ring
    have hPBψ : (projB d).mulVec (ψ j) = fun y => ((a * α + β : ℝ) : ℂ) * ((sd : ℂ) * rawV j y) := by
      rw [hψ_split j]
      have h1 : (projB d).mulVec (fun y => (α : ℂ) * ((sd : ℂ) * rawU j y) + (β : ℂ) * ((sd : ℂ) * rawV j y)) =
          fun y => (α : ℂ) * ((projB d).mulVec (fun y => (sd : ℂ) * rawU j y) y) +
                   (β : ℂ) * ((projB d).mulVec (fun y => (sd : ℂ) * rawV j y) y) := by
        ext y; simp only [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1 <;> refine Finset.sum_congr rfl fun z _ => by ring
      rw [h1, hPB_U j, hPB_V j]; ext y; push_cast; ring
    constructor
    · have hsq : (vecInner (ψ j) ((projA d).mulVec (ψ j))).re = vecNormSq ((projA d).mulVec (ψ j)) := by
        rw [← vecInner_self_re]
        congr 1; symm
        calc vecInner ((projA d).mulVec (ψ j)) ((projA d).mulVec (ψ j))
            = vecInner ((projA d)ᴴ.mulVec (ψ j)) ((projA d).mulVec (ψ j)) := by rw [projA_hermitian]
          _ = vecInner (ψ j) ((projA d).mulVec ((projA d).mulVec (ψ j))) :=
              (vecInner_mulVec_right (projA d) (ψ j) ((projA d).mulVec (ψ j))).symm
          _ = vecInner (ψ j) ((projA d * projA d).mulVec (ψ j)) := by rw [Matrix.mulVec_mulVec]
          _ = vecInner (ψ j) ((projA d).mulVec (ψ j)) := by rw [projA_mul_projA d hd_pos_nat]
      rw [hsq, hPAψ]
      unfold vecNormSq
      simp only [Complex.normSq_mul, Complex.normSq_ofReal, ← Finset.mul_sum]
      have hU' : sd * sd * ∑ i : TriIdx d, Complex.normSq (rawU j i) = 1 := by
        have := hU_norm j; unfold vecNormSq at this
        simpa only [Complex.normSq_mul, Complex.normSq_ofReal, ← Finset.mul_sum] using this
      rw [hU', mul_one, ← sq]
    · have hsq : (vecInner (ψ j) ((projB d).mulVec (ψ j))).re = vecNormSq ((projB d).mulVec (ψ j)) := by
        rw [← vecInner_self_re]
        congr 1; symm
        calc vecInner ((projB d).mulVec (ψ j)) ((projB d).mulVec (ψ j))
            = vecInner ((projB d)ᴴ.mulVec (ψ j)) ((projB d).mulVec (ψ j)) := by rw [projB_hermitian]
          _ = vecInner (ψ j) ((projB d).mulVec ((projB d).mulVec (ψ j))) :=
              (vecInner_mulVec_right (projB d) (ψ j) ((projB d).mulVec (ψ j))).symm
          _ = vecInner (ψ j) ((projB d * projB d).mulVec (ψ j)) := by rw [Matrix.mulVec_mulVec]
          _ = vecInner (ψ j) ((projB d).mulVec (ψ j)) := by rw [projB_mul_projB d hd_pos_nat]
      rw [hsq, hPBψ]
      unfold vecNormSq
      simp only [Complex.normSq_mul, Complex.normSq_ofReal, ← Finset.mul_sum]
      have hV' : sd * sd * ∑ i : TriIdx d, Complex.normSq (rawV j i) = 1 := by
        have := hV_norm j; unfold vecNormSq at this
        simpa only [Complex.normSq_mul, Complex.normSq_ofReal, ← Finset.mul_sum] using this
      rw [hV', mul_one, ← sq]
  · intro r r'
    have hfactor : ∀ j p q : Fin d,
        ψ j (r, p, q) * star (ψ j (r', p, q)) =
        (((sd ^ 2 : ℝ) : ℂ)) * (
          (((α ^ 2 : ℝ) : ℂ)) * (if r = p ∧ q = j ∧ r' = p then (1 : ℂ) else 0) +
          (((α * β : ℝ) : ℂ)) * (if r = p ∧ q = j ∧ r' = q ∧ p = j then (1 : ℂ) else 0) +
          (((α * β : ℝ) : ℂ)) * (if r = q ∧ p = j ∧ r' = p ∧ q = j then (1 : ℂ) else 0) +
          (((β ^ 2 : ℝ) : ℂ)) * (if r = q ∧ p = j ∧ r' = q then (1 : ℂ) else 0)) := by
      intro j p q
      have hstar_ite : ∀ (P : Prop) [Decidable P],
          star (if P then (1 : ℂ) else 0) = if P then (1 : ℂ) else 0 := by
        intro P _; by_cases hP : P <;> simp [hP]
      have hmul_ite : ∀ (P Q : Prop) [Decidable P] [Decidable Q],
          (if P then (1 : ℂ) else 0) * (if Q then (1 : ℂ) else 0) =
          if P ∧ Q then (1 : ℂ) else 0 := by
        intro P Q _ _; by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]
      simp only [ψ, rawU, rawV, star_mul', star_add, Complex.star_def, Complex.conj_ofReal,
        hstar_ite, Complex.ofReal_pow, Complex.ofReal_mul]
      have h1 : (if r = p ∧ q = j then (1 : ℂ) else 0) * (if r' = p ∧ q = j then (1 : ℂ) else 0) =
          if r = p ∧ q = j ∧ r' = p then (1 : ℂ) else 0 := by
        rw [hmul_ite]; exact if_congr (by tauto) rfl rfl
      have h2 : (if r = p ∧ q = j then (1 : ℂ) else 0) * (if r' = q ∧ p = j then (1 : ℂ) else 0) =
          if r = p ∧ q = j ∧ r' = q ∧ p = j then (1 : ℂ) else 0 := by
        rw [hmul_ite]; exact if_congr (by tauto) rfl rfl
      have h3 : (if r = q ∧ p = j then (1 : ℂ) else 0) * (if r' = p ∧ q = j then (1 : ℂ) else 0) =
          if r = q ∧ p = j ∧ r' = p ∧ q = j then (1 : ℂ) else 0 := by
        rw [hmul_ite]; exact if_congr (by tauto) rfl rfl
      have h4 : (if r = q ∧ p = j then (1 : ℂ) else 0) * (if r' = q ∧ p = j then (1 : ℂ) else 0) =
          if r = q ∧ p = j ∧ r' = q then (1 : ℂ) else 0 := by
        rw [hmul_ite]; exact if_congr (by tauto) rfl rfl
      calc _
          = (sd : ℂ) ^ 2 * (
              (α : ℂ) ^ 2 * ((if r = p ∧ q = j then 1 else 0) * (if r' = p ∧ q = j then 1 else 0)) +
              ((α : ℂ) * (β : ℂ)) * ((if r = p ∧ q = j then 1 else 0) * (if r' = q ∧ p = j then 1 else 0)) +
              ((α : ℂ) * (β : ℂ)) * ((if r = q ∧ p = j then 1 else 0) * (if r' = p ∧ q = j then 1 else 0)) +
              (β : ℂ) ^ 2 * ((if r = q ∧ p = j then 1 else 0) * (if r' = q ∧ p = j then 1 else 0))) := by ring
        _ = _ := by rw [h1, h2, h3, h4]
    simp_rw [hfactor, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
    have ht1 : ∑ j : Fin d, ∑ p : Fin d, ∑ q : Fin d,
        (if r = p ∧ q = j ∧ r' = p then (1 : ℂ) else 0) = if r = r' then (d : ℂ) else 0 := by
      by_cases hrr : r = r'
      · subst hrr; simp only [↓reduceIte]
        have h1 : ∀ j : Fin d, ∑ p : Fin d, ∑ q : Fin d,
            (if r = p ∧ q = j ∧ r = p then (1 : ℂ) else 0) = 1 := by
          intro j; rw [Finset.sum_eq_single r]
          · rw [Finset.sum_eq_single j]
            · simp
            · intro q _ hqj; simp [hqj]
            · intro h; exact (h (Finset.mem_univ j)).elim
          · intro p _ hpr; refine Finset.sum_eq_zero fun q _ => ?_; simp [Ne.symm hpr]
          · intro h; exact (h (Finset.mem_univ r)).elim
        simp_rw [h1]; simp
      · simp only [hrr, ↓reduceIte]
        refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun p _ =>
          Finset.sum_eq_zero fun q _ => ?_
        by_cases h : r = p ∧ q = j ∧ r' = p
        · exact (hrr (h.1.trans h.2.2.symm)).elim
        · simp [h]
    have ht2 : ∑ j : Fin d, ∑ p : Fin d, ∑ q : Fin d,
        (if r = p ∧ q = j ∧ r' = q ∧ p = j then (1 : ℂ) else 0) = if r = r' then 1 else 0 := by
      by_cases hrr : r = r'
      · subst hrr; simp only [↓reduceIte]
        rw [Finset.sum_eq_single r]
        · rw [Finset.sum_eq_single r]
          · rw [Finset.sum_eq_single r]
            · simp
            · intro q _ hqr; simp [hqr]
            · intro h; exact (h (Finset.mem_univ r)).elim
          · intro p _ hpr; refine Finset.sum_eq_zero fun q _ => ?_; simp [Ne.symm hpr]
          · intro h; exact (h (Finset.mem_univ r)).elim
        · intro j _ hjr; refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
          by_cases h : r = p ∧ q = j ∧ r = q ∧ p = j
          · exact (hjr (h.2.2.1.trans h.2.1).symm).elim
          · simp [h]
        · intro h; exact (h (Finset.mem_univ r)).elim
      · simp only [hrr, ↓reduceIte]
        refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun p _ =>
          Finset.sum_eq_zero fun q _ => ?_
        by_cases h : r = p ∧ q = j ∧ r' = q ∧ p = j
        · exact (hrr ((h.1.trans h.2.2.2).trans (h.2.2.1.trans h.2.1).symm)).elim
        · simp [h]
    have ht3 : ∑ j : Fin d, ∑ p : Fin d, ∑ q : Fin d,
        (if r = q ∧ p = j ∧ r' = p ∧ q = j then (1 : ℂ) else 0) = if r = r' then 1 else 0 := by
      by_cases hrr : r = r'
      · subst hrr; simp only [↓reduceIte]
        rw [Finset.sum_eq_single r]
        · rw [Finset.sum_eq_single r]
          · rw [Finset.sum_eq_single r]
            · simp
            · intro q _ hqr; simp [hqr]
            · intro h; exact (h (Finset.mem_univ r)).elim
          · intro p _ hpr; refine Finset.sum_eq_zero fun q _ => ?_; simp [Ne.symm hpr]
          · intro h; exact (h (Finset.mem_univ r)).elim
        · intro j _ hjr; refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
          by_cases h : r = q ∧ p = j ∧ r = p ∧ q = j
          · exact (hjr (h.1.trans h.2.2.2).symm).elim
          · simp [h]
        · intro h; exact (h (Finset.mem_univ r)).elim
      · simp only [hrr, ↓reduceIte]
        refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun p _ =>
          Finset.sum_eq_zero fun q _ => ?_
        by_cases h : r = q ∧ p = j ∧ r' = p ∧ q = j
        · exact (hrr ((h.1.trans h.2.2.2).trans (h.2.2.1.trans h.2.1).symm)).elim
        · simp [h]
    have ht4 : ∑ j : Fin d, ∑ p : Fin d, ∑ q : Fin d,
        (if r = q ∧ p = j ∧ r' = q then (1 : ℂ) else 0) = if r = r' then (d : ℂ) else 0 := by
      by_cases hrr : r = r'
      · subst hrr; simp only [↓reduceIte]
        have h1 : ∀ j : Fin d, ∑ p : Fin d, ∑ q : Fin d,
            (if r = q ∧ p = j ∧ r = q then (1 : ℂ) else 0) = 1 := by
          intro j; rw [Finset.sum_eq_single j]
          · rw [Finset.sum_eq_single r]
            · simp
            · intro q _ hqr; simp [Ne.symm hqr]
            · intro h; exact (h (Finset.mem_univ r)).elim
          · intro p _ hpj; refine Finset.sum_eq_zero fun q _ => ?_; simp [hpj]
          · intro h; exact (h (Finset.mem_univ j)).elim
        simp_rw [h1]; simp
      · simp only [hrr, ↓reduceIte]
        refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun p _ =>
          Finset.sum_eq_zero fun q _ => ?_
        by_cases h : r = q ∧ p = j ∧ r' = q
        · exact (hrr (h.1.trans h.2.2.symm)).elim
        · simp [h]
    rw [ht1, ht2, ht3, ht4, hsd_sq]
    by_cases hrr : r = r'
    · simp only [hrr, ↓reduceIte]
      have hnormC : (((α ^ 2 + β ^ 2 + 2 * a * α * β : ℝ) : ℂ)) = 1 := by
        rw [hnorm, Complex.ofReal_one]
      have hcalc : (d : ℂ)⁻¹ * ((a : ℂ) * ((α ^ 2 : ℂ) * (d : ℂ) + (α * β : ℂ) * 1 +
          (α * β : ℂ) * 1 + (β ^ 2 : ℂ) * (d : ℂ))) =
          (d : ℂ)⁻¹ * (((α ^ 2 + β ^ 2 + 2 * a * α * β : ℝ) : ℂ)) := by
        simp only [a, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_add,
          Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
        field_simp [hd_cne]; ring
      push_cast at hcalc hnormC ⊢
      rw [hcalc, hnormC, mul_one]
    · simp [hrr]

/-- **Theorem 3(c.2)** (Complete Achievability of the Shaded Joint Region — Lower Curved Boundary,
Flat Zero Boundary via Shift Measure-and-Prepare Channel, and All Interior Points):
For every `d ≥ 2`, every `x ∈ [0, 1]`, and every `y` inside the band
`(max 0 (a √x - b √(1-x)))² ≤ y ≤ (a √x + b √(1-x))²` (with `a = d⁻¹`, `b = √(1 - a²)`),
there exists a finite convex ensemble `(w, ψ)` indexed by `Fin 3 × Fin d` of normalized 3-party
states forming a valid CPTP Choi state (`Tr_{A'B'}(σ) = I_R / d`) that attains `F_A(σ) = x` and
`F_B(σ) = y` exactly. -/
theorem achievable_joint_region_choi_complete (hd : 2 ≤ d) (x y : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy_lo : (max 0 ((d : ℝ)⁻¹ * Real.sqrt x -
      Real.sqrt (1 - ((d : ℝ) ^ 2)⁻¹) * Real.sqrt (1 - x))) ^ 2 ≤ y)
    (hy_hi : y ≤ ((d : ℝ)⁻¹ * Real.sqrt x +
      Real.sqrt (1 - ((d : ℝ) ^ 2)⁻¹) * Real.sqrt (1 - x)) ^ 2) :
    ∃ (w : Fin 3 × Fin d → ℝ) (ψ : Fin 3 × Fin d → TriIdx d → ℂ),
      (∀ k, 0 ≤ w k) ∧
      (∑ k : Fin 3 × Fin d, w k = 1) ∧
      (∀ k, vecNormSq (ψ k) = 1) ∧
      (∑ k : Fin 3 × Fin d, w k * (vecInner (ψ k) ((projA d).mulVec (ψ k))).re = x) ∧
      (∑ k : Fin 3 × Fin d, w k * (vecInner (ψ k) ((projB d).mulVec (ψ k))).re = y) ∧
      (∀ r r' : Fin d,
        (∑ k : Fin 3 × Fin d, (w k : ℂ) * ∑ a : Fin d, ∑ b : Fin d,
          ψ k (r, a, b) * star (ψ k (r', a, b))) =
        if r = r' then (d : ℂ)⁻¹ else 0) := by
  have hd_pos_nat : 0 < d := by omega
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd_pos_nat
  have hd_ge2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
  set a : ℝ := (d : ℝ)⁻¹
  have hb2_pos : 0 < 1 - ((d : ℝ) ^ 2)⁻¹ := by
    have h4 : (4 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
    have hinv : ((d : ℝ) ^ 2)⁻¹ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h4
    linarith
  set b : ℝ := Real.sqrt (1 - ((d : ℝ) ^ 2)⁻¹)
  have hb_pos : 0 < b := Real.sqrt_pos.mpr hb2_pos
  have hb_ne : b ≠ 0 := ne_of_gt hb_pos
  have hb_sq : b ^ 2 = 1 - a ^ 2 := by
    have : 1 - ((d : ℝ) ^ 2)⁻¹ = 1 - a ^ 2 := by simp [a, inv_pow]
    rw [← this]; exact Real.sq_sqrt (le_of_lt hb2_pos)
  have hb2_le1 : b ^ 2 ≤ 1 := by
    have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
    linarith
  have hb2_pos' : 0 < b ^ 2 := pow_pos hb_pos 2
  -- Upper boundary family ψ_hi at x
  set α_hi : ℝ := Real.sqrt x - a * Real.sqrt (1 - x) / b
  set β_hi : ℝ := Real.sqrt (1 - x) / b
  have hnorm_hi : α_hi ^ 2 + β_hi ^ 2 + 2 * a * α_hi * β_hi = 1 := by
    have hsx : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx0
    have hs1x : (Real.sqrt (1 - x)) ^ 2 = 1 - x := Real.sq_sqrt (by linarith)
    have hkey : α_hi ^ 2 + β_hi ^ 2 + 2 * a * α_hi * β_hi =
        (Real.sqrt x) ^ 2 + (Real.sqrt (1 - x)) ^ 2 * ((1 - a ^ 2) / b ^ 2) := by
      simp only [α_hi, β_hi]; field_simp [hb_ne]; ring
    rw [hkey, ← hb_sq, div_self (pow_ne_zero 2 hb_ne), mul_one, hsx, hs1x]; ring
  rcases choi_linear_family d hd α_hi β_hi hnorm_hi with ⟨ψ_hi, hψhi_norm, hψhi_fid, hψhi_marg⟩
  have hψhi_FA : ∀ j, (vecInner (ψ_hi j) ((projA d).mulVec (ψ_hi j))).re = x := by
    intro j; rw [(hψhi_fid j).1]
    have : α_hi + a * β_hi = Real.sqrt x := by simp only [α_hi, β_hi]; ring
    rw [this, Real.sq_sqrt hx0]
  have hψhi_FB : ∀ j, (vecInner (ψ_hi j) ((projB d).mulVec (ψ_hi j))).re =
      (a * Real.sqrt x + b * Real.sqrt (1 - x)) ^ 2 := by
    intro j; rw [(hψhi_fid j).2]
    have : a * α_hi + β_hi = a * Real.sqrt x + b * Real.sqrt (1 - x) := by
      have h1 : a * α_hi + β_hi = a * Real.sqrt x + ((1 - a ^ 2) / b) * Real.sqrt (1 - x) := by
        simp only [α_hi, β_hi]; field_simp [hb_ne]; ring
      rw [h1, ← hb_sq, show b ^ 2 / b = b by field_simp [hb_ne]]
    rw [this]
  -- Lower curved boundary family ψ_lo at x_lo = max x (b^2)
  set x_lo : ℝ := max x (b ^ 2)
  have hxlo_0 : 0 ≤ x_lo := le_trans (le_of_lt hb2_pos') (le_max_right _ _)
  have hxlo_1 : x_lo ≤ 1 := max_le hx1 hb2_le1
  set α_lo : ℝ := Real.sqrt x_lo + a * Real.sqrt (1 - x_lo) / b
  set β_lo : ℝ := -Real.sqrt (1 - x_lo) / b
  have hnorm_lo : α_lo ^ 2 + β_lo ^ 2 + 2 * a * α_lo * β_lo = 1 := by
    have hsx : (Real.sqrt x_lo) ^ 2 = x_lo := Real.sq_sqrt hxlo_0
    have hs1x : (Real.sqrt (1 - x_lo)) ^ 2 = 1 - x_lo := Real.sq_sqrt (by linarith)
    have hkey : α_lo ^ 2 + β_lo ^ 2 + 2 * a * α_lo * β_lo =
        (Real.sqrt x_lo) ^ 2 + (Real.sqrt (1 - x_lo)) ^ 2 * ((1 - a ^ 2) / b ^ 2) := by
      simp only [α_lo, β_lo]; field_simp [hb_ne]; ring
    rw [hkey, ← hb_sq, div_self (pow_ne_zero 2 hb_ne), mul_one, hsx, hs1x]; ring
  rcases choi_linear_family d hd α_lo β_lo hnorm_lo with ⟨ψ_lo, hψlo_norm, hψlo_fid, hψlo_marg⟩
  have hψlo_FA : ∀ j, (vecInner (ψ_lo j) ((projA d).mulVec (ψ_lo j))).re = x_lo := by
    intro j; rw [(hψlo_fid j).1]
    have : α_lo + a * β_lo = Real.sqrt x_lo := by simp only [α_lo, β_lo]; ring
    rw [this, Real.sq_sqrt hxlo_0]
  have hψlo_FB : ∀ j, (vecInner (ψ_lo j) ((projB d).mulVec (ψ_lo j))).re =
      (a * Real.sqrt x_lo - b * Real.sqrt (1 - x_lo)) ^ 2 := by
    intro j; rw [(hψlo_fid j).2]
    have : a * α_lo + β_lo = a * Real.sqrt x_lo - b * Real.sqrt (1 - x_lo) := by
      have h1 : a * α_lo + β_lo = a * Real.sqrt x_lo - ((1 - a ^ 2) / b) * Real.sqrt (1 - x_lo) := by
        simp only [α_lo, β_lo]; field_simp [hb_ne]; ring
      rw [h1, ← hb_sq, show b ^ 2 / b = b by field_simp [hb_ne]]
    rw [this]
  -- Shift measure-and-prepare (0,0) family φ_j = |j⟩_R |j+1 mod d⟩_{A'} |j+1 mod d⟩_{B'}
  let shift : Fin d → Fin d := fun j => ⟨(j.val + 1) % d, Nat.mod_lt _ hd_pos_nat⟩
  have hshift_ne : ∀ j : Fin d, shift j ≠ j := by
    intro j heq
    have hval : (j.val + 1) % d = j.val := congrArg Fin.val heq
    by_cases hlt : j.val + 1 < d
    · rw [Nat.mod_eq_of_lt hlt] at hval; omega
    · have hj : j.val + 1 = d := by omega
      rw [hj, Nat.mod_self] at hval; omega
  let φ : Fin d → TriIdx d → ℂ := fun j z =>
    if z.1 = j ∧ z.2.1 = shift j ∧ z.2.2 = shift j then (1 : ℂ) else 0
  have hφ_norm : ∀ j, vecNormSq (φ j) = 1 := by
    intro j; unfold vecNormSq
    rw [Finset.sum_eq_single (j, shift j, shift j)]
    · simp [φ]
    · intro z _ hz
      have hnot : ¬(z.1 = j ∧ z.2.1 = shift j ∧ z.2.2 = shift j) := by
        rintro ⟨h1, h2, h3⟩; apply hz; cases z with | mk r pq => cases pq with | mk p q => simp_all
      simp [φ, hnot]
    · intro h; exact (h (Finset.mem_univ _)).elim
  have hφ_FA : ∀ j, (vecInner (φ j) ((projA d).mulVec (φ j))).re = 0 := by
    intro j
    have hmul : (projA d).mulVec (φ j) = 0 := by
      ext ⟨r, p, q⟩
      simp only [Matrix.mulVec, dotProduct, projA, φ, Pi.zero_apply, Fintype.sum_prod_type]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun p' _ => Finset.sum_eq_zero fun q' _ => ?_
      by_cases h1 : i = j ∧ p' = shift j ∧ q' = shift j
      · rcases h1 with ⟨rfl, rfl, rfl⟩
        have hne : i ≠ shift i := (hshift_ne i).symm
        simp [hne]
      · simp [h1]
    rw [hmul]; simp [vecInner]
  have hφ_FB : ∀ j, (vecInner (φ j) ((projB d).mulVec (φ j))).re = 0 := by
    intro j
    have hmul : (projB d).mulVec (φ j) = 0 := by
      ext ⟨r, p, q⟩
      simp only [Matrix.mulVec, dotProduct, projB, φ, Pi.zero_apply, Fintype.sum_prod_type]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun p' _ => Finset.sum_eq_zero fun q' _ => ?_
      by_cases h1 : i = j ∧ p' = shift j ∧ q' = shift j
      · rcases h1 with ⟨rfl, rfl, rfl⟩
        have hne : i ≠ shift i := (hshift_ne i).symm
        simp [hne]
      · simp [h1]
    rw [hmul]; simp [vecInner]
  have hφ_marg : ∀ r r' : Fin d,
      ((d : ℂ)⁻¹ * ∑ j : Fin d, ∑ p : Fin d, ∑ q : Fin d,
        φ j (r, p, q) * star (φ j (r', p, q))) =
      if r = r' then (d : ℂ)⁻¹ else 0 := by
    intro r r'
    by_cases hrr : r = r'
    · subst hrr; simp only [↓reduceIte]
      have hs : ∑ j : Fin d, ∑ p : Fin d, ∑ q : Fin d,
          φ j (r, p, q) * star (φ j (r, p, q)) = 1 := by
        rw [Finset.sum_eq_single r]
        · rw [Finset.sum_eq_single (shift r)]
          · rw [Finset.sum_eq_single (shift r)]
            · simp [φ]
            · intro q _ hq; simp [φ, hq]
            · intro h; exact (h (Finset.mem_univ _)).elim
          · intro p _ hp; refine Finset.sum_eq_zero fun q _ => ?_; simp [φ, hp]
          · intro h; exact (h (Finset.mem_univ _)).elim
        · intro j _ hj; refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
          simp [φ, Ne.symm hj]
        · intro h; exact (h (Finset.mem_univ _)).elim
      rw [hs, mul_one]
    · simp only [hrr, ↓reduceIte]
      have hs : ∑ j : Fin d, ∑ p : Fin d, ∑ q : Fin d,
          φ j (r, p, q) * star (φ j (r', p, q)) = 0 := by
        refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
        by_cases h1 : r = j ∧ p = shift j ∧ q = shift j
        · have hne : r' ≠ j := fun h => hrr (h1.1.trans h.symm)
          simp [φ, hne]
        · simp [φ, h1]
      rw [hs, mul_zero]
  -- Assemble convex weights (λ, s) on Fin 3 × Fin d
  set F_hi : ℝ := (a * Real.sqrt x + b * Real.sqrt (1 - x)) ^ 2
  set F_lo : ℝ := (max 0 (a * Real.sqrt x - b * Real.sqrt (1 - x))) ^ 2
  set s : ℝ := if b ^ 2 ≤ x then 1 else x / b ^ 2
  have hs0 : 0 ≤ s := by
    dsimp only [s]; split_ifs
    · norm_num
    · exact div_nonneg hx0 (le_of_lt hb2_pos')
  have hs1 : s ≤ 1 := by
    dsimp only [s]; split_ifs with hbx
    · norm_num
    · have hlt : x < b ^ 2 := lt_of_not_ge hbx
      exact (div_le_one hb2_pos').mpr (le_of_lt hlt)
  have hs_xlo : s * x_lo = x := by
    dsimp only [s, x_lo]; split_ifs with hbx
    · rw [max_eq_left hbx, one_mul]
    · have hlt : x < b ^ 2 := lt_of_not_ge hbx
      rw [max_eq_right (le_of_lt hlt)]
      field_simp [ne_of_gt hb2_pos']
  have hs_Flo : s * (a * Real.sqrt x_lo - b * Real.sqrt (1 - x_lo)) ^ 2 = F_lo := by
    have hsx_sq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx0
    have hs1x_sq : (Real.sqrt (1 - x)) ^ 2 = 1 - x := Real.sq_sqrt (by linarith)
    dsimp only [s, x_lo, F_lo]; split_ifs with hbx
    · rw [max_eq_left hbx, one_mul]
      have hge : 0 ≤ a * Real.sqrt x - b * Real.sqrt (1 - x) := by
        have hsq_le : (b * Real.sqrt (1 - x)) ^ 2 ≤ (a * Real.sqrt x) ^ 2 := by
          rw [mul_pow, mul_pow, hs1x_sq, hsx_sq]
          nlinarith [hb_sq]
        have hnn1 : 0 ≤ a * Real.sqrt x := mul_nonneg (le_of_lt (inv_pos.mpr hd_pos)) (Real.sqrt_nonneg _)
        have hnn2 : 0 ≤ b * Real.sqrt (1 - x) := mul_nonneg (le_of_lt hb_pos) (Real.sqrt_nonneg _)
        nlinarith [sq_nonneg (a * Real.sqrt x - b * Real.sqrt (1 - x))]
      rw [max_eq_right hge]
    · have hlt : x < b ^ 2 := lt_of_not_ge hbx
      rw [max_eq_right (le_of_lt hlt)]
      have h1mb2 : 1 - b ^ 2 = a ^ 2 := by linarith [hb_sq]
      have ha_nn : 0 ≤ a := le_of_lt (inv_pos.mpr hd_pos)
      have hzero : a * Real.sqrt (b ^ 2) - b * Real.sqrt (1 - b ^ 2) = 0 := by
        rw [h1mb2, Real.sqrt_sq (le_of_lt hb_pos), Real.sqrt_sq ha_nn]; ring
      have hle0 : a * Real.sqrt x - b * Real.sqrt (1 - x) ≤ 0 := by
        have hsq_lt : (a * Real.sqrt x) ^ 2 ≤ (b * Real.sqrt (1 - x)) ^ 2 := by
          rw [mul_pow, mul_pow, hsx_sq, hs1x_sq]
          nlinarith [hb_sq]
        have hnn1 : 0 ≤ a * Real.sqrt x := mul_nonneg ha_nn (Real.sqrt_nonneg _)
        have hnn2 : 0 ≤ b * Real.sqrt (1 - x) := mul_nonneg (le_of_lt hb_pos) (Real.sqrt_nonneg _)
        nlinarith
      rw [hzero, max_eq_left hle0]; ring
  set lam : ℝ := if F_hi = F_lo then 1 else (y - F_lo) / (F_hi - F_lo)
  have hlam0 : 0 ≤ lam := by
    dsimp only [lam]; split_ifs with heq
    · norm_num
    · have hlt : F_lo < F_hi := lt_of_le_of_ne (le_trans hy_lo hy_hi) (Ne.symm heq)
      exact div_nonneg (by linarith) (by linarith)
  have hlam1 : lam ≤ 1 := by
    dsimp only [lam]; split_ifs with heq
    · norm_num
    · have hlt : F_lo < F_hi := lt_of_le_of_ne (le_trans hy_lo hy_hi) (Ne.symm heq)
      exact (div_le_one (by linarith)).mpr (by linarith)
  have hlam_y : lam * F_hi + (1 - lam) * F_lo = y := by
    dsimp only [lam]; split_ifs with heq
    · linarith
    · have hne : F_hi - F_lo ≠ 0 := sub_ne_zero.mpr heq
      field_simp [hne]; ring
  let w : Fin 3 × Fin d → ℝ := fun k =>
    match k.1 with
    | ⟨0, _⟩ => lam * (d : ℝ)⁻¹
    | ⟨1, _⟩ => (1 - lam) * s * (d : ℝ)⁻¹
    | ⟨2, _⟩ => (1 - lam) * (1 - s) * (d : ℝ)⁻¹
  let ψ : Fin 3 × Fin d → TriIdx d → ℂ := fun k =>
    match k.1 with
    | ⟨0, _⟩ => ψ_hi k.2
    | ⟨1, _⟩ => ψ_lo k.2
    | ⟨2, _⟩ => φ k.2
  have hcancel1 : ∀ u : ℝ, (d : ℝ) * (u * (d : ℝ)⁻¹) = u := fun u => by
    calc (d : ℝ) * (u * (d : ℝ)⁻¹) = ((d : ℝ) * (d : ℝ)⁻¹) * u := by ring
      _ = u := by rw [mul_inv_cancel₀ hd_ne, one_mul]
  have hcancel2 : ∀ u v : ℝ, (d : ℝ) * (u * (d : ℝ)⁻¹ * v) = u * v := fun u v => by
    calc (d : ℝ) * (u * (d : ℝ)⁻¹ * v) = ((d : ℝ) * (d : ℝ)⁻¹) * (u * v) := by ring
      _ = u * v := by rw [mul_inv_cancel₀ hd_ne, one_mul]
  refine ⟨w, ψ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨i, j⟩
    fin_cases i
    · exact mul_nonneg hlam0 (le_of_lt (inv_pos.mpr hd_pos))
    · exact mul_nonneg (mul_nonneg (by linarith) hs0) (le_of_lt (inv_pos.mpr hd_pos))
    · exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (le_of_lt (inv_pos.mpr hd_pos))
  · rw [Fintype.sum_prod_type, Fin.sum_univ_three]
    simp only [w, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hcancel1, hcancel1, hcancel1]; ring
  · rintro ⟨i, j⟩
    fin_cases i
    · exact hψhi_norm j
    · exact hψlo_norm j
    · exact hφ_norm j
  · rw [Fintype.sum_prod_type, Fin.sum_univ_three]
    simp only [w, ψ, hψhi_FA, hψlo_FA, hφ_FA, mul_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, add_zero]
    rw [hcancel2, hcancel2, mul_assoc, hs_xlo]; ring
  · rw [Fintype.sum_prod_type, Fin.sum_univ_three]
    simp only [w, ψ, hψhi_FB, hψlo_FB, hφ_FB, mul_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, add_zero]
    rw [hcancel2, hcancel2, mul_assoc, hs_Flo, hlam_y]
  · intro r r'
    rw [Fintype.sum_prod_type, Fin.sum_univ_three]
    simp only [w, ψ, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast,
      mul_assoc, ← Finset.mul_sum]
    rw [hψhi_marg r r', hψlo_marg r r', hφ_marg r r']
    by_cases hrr : r = r'
    · simp only [hrr, ↓reduceIte]
      have hsum1 : (lam : ℂ) + (1 - (lam : ℂ)) * (s : ℂ) +
          (1 - (lam : ℂ)) * (1 - (s : ℂ)) = 1 := by ring
      push_cast
      calc (lam : ℂ) * (d : ℂ)⁻¹ + (1 - (lam : ℂ)) * ((s : ℂ) * (d : ℂ)⁻¹) +
            (1 - (lam : ℂ)) * ((1 - (s : ℂ)) * (d : ℂ)⁻¹)
          = ((lam : ℂ) + (1 - (lam : ℂ)) * (s : ℂ) + (1 - (lam : ℂ)) * (1 - (s : ℂ))) *
              (d : ℂ)⁻¹ := by ring
        _ = (d : ℂ)⁻¹ := by rw [hsum1, one_mul]
    · simp [hrr]

/-- **Theorem 3(e.2)** (Finite-`s` Weak Record Measurement vs. Ideal Projective Readout):
For a qubit `Z`-record with weak-measurement Kraus operators `M_± = √((I ± η Z)/2)` where
`η ∈ [-1, 1]` and `c = √(1 - η²) = exp(-Γ s / 2)`:
1. `M_+ᴴ M_+ + M_-ᴴ M_- = I_2` (valid CPTP quantum instrument).
2. The non-selective map `M_+ ρ M_+ᴴ + M_- ρ M_-ᴴ` equals finite-`s` phase damping
   `!![ρ 0 0, c * ρ 0 1; c * ρ 1 0, ρ 1 1]` identically for every `ρ`.
3. Two consecutive identical weak measurements disagree with universal probability
   `Tr(M_- M_+ ρ M_+ᴴ M_-ᴴ + M_+ M_- ρ M_-ᴴ M_+ᴴ) = (1 - η²) / 2` for every unit-trace `ρ`.
4. Whenever `c > 0` (finite `s`), the non-selective weak-measurement map disagrees strictly with
   ideal projective pinching `P_0 ρ P_0 + P_1 ρ P_1` on `|+⟩⟨+|` (off-diagonal `c/2 ≠ 0` vs `0`). -/
theorem weak_record_measurement_vs_projective_readout (η : ℝ) (hη_lo : -1 ≤ η) (hη_hi : η ≤ 1)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) (htr : ρ.trace = 1) :
    let p := Real.sqrt ((1 + η) / 2)
    let q := Real.sqrt ((1 - η) / 2)
    let c := Real.sqrt (1 - η ^ 2)
    let Mp : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![(p : ℂ), (q : ℂ)]
    let Mm : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![(q : ℂ), (p : ℂ)]
    Mpᴴ * Mp + Mmᴴ * Mm = 1 ∧
    Mp * ρ * Mpᴴ + Mm * ρ * Mmᴴ = !![ρ 0 0, (c : ℂ) * ρ 0 1; (c : ℂ) * ρ 1 0, ρ 1 1] ∧
    (Mm * Mp * ρ * Mpᴴ * Mmᴴ + Mp * Mm * ρ * Mmᴴ * Mpᴴ).trace = (((1 - η ^ 2) / 2 : ℝ) : ℂ) ∧
    (0 < c →
      let plus : Matrix (Fin 2) (Fin 2) ℂ := !![(2⁻¹ : ℂ), (2⁻¹ : ℂ); (2⁻¹ : ℂ), (2⁻¹ : ℂ)]
      let P0 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, 0]
      let P1 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![0, 1]
      (Mp * plus * Mpᴴ + Mm * plus * Mmᴴ) 0 1 ≠ (P0 * plus * P0 + P1 * plus * P1) 0 1) := by
  have hp_nn : 0 ≤ (1 + η) / 2 := by linarith
  have hq_nn : 0 ≤ (1 - η) / 2 := by linarith
  have hp2 : (Real.sqrt ((1 + η) / 2)) ^ 2 = (1 + η) / 2 := Real.sq_sqrt hp_nn
  have hq2 : (Real.sqrt ((1 - η) / 2)) ^ 2 = (1 - η) / 2 := Real.sq_sqrt hq_nn
  have hpq : Real.sqrt ((1 + η) / 2) * Real.sqrt ((1 - η) / 2) = Real.sqrt (1 - η ^ 2) / 2 := by
    rw [← Real.sqrt_mul hp_nn]
    have hprod : (1 + η) / 2 * ((1 - η) / 2) = (1 - η ^ 2) / 4 := by ring
    rw [hprod, Real.sqrt_div (by nlinarith), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  dsimp only
  generalize hp : Real.sqrt ((1 + η) / 2) = p at hp2 hpq ⊢
  generalize hq : Real.sqrt ((1 - η) / 2) = q at hq2 hpq ⊢
  generalize hc : Real.sqrt (1 - η ^ 2) = c at hpq ⊢
  have hp2C : (p : ℂ) * (p : ℂ) = (((1 + η) / 2 : ℝ) : ℂ) := by
    exact_mod_cast (show p * p = (1 + η) / 2 by rw [← sq]; exact hp2)
  have hq2C : (q : ℂ) * (q : ℂ) = (((1 - η) / 2 : ℝ) : ℂ) := by
    exact_mod_cast (show q * q = (1 - η) / 2 by rw [← sq]; exact hq2)
  have hpqC : (p : ℂ) * (q : ℂ) = ((c / 2 : ℝ) : ℂ) := by
    exact_mod_cast hpq
  have hsum_pq : (((1 + η) / 2 : ℝ) : ℂ) + (((1 - η) / 2 : ℝ) : ℂ) = 1 := by
    push_cast; ring
  have hprod_pq : (((1 + η) / 2 : ℝ) : ℂ) * (((1 - η) / 2 : ℝ) : ℂ) =
      (((1 - η ^ 2) / 4 : ℝ) : ℂ) := by
    push_cast; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
    · rw [hp2C, hq2C, hsum_pq]
    · rw [hq2C, hp2C, add_comm, hsum_pq]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]
    · calc (p : ℂ) * ρ 0 0 * (p : ℂ) + (q : ℂ) * ρ 0 0 * (q : ℂ)
          = ((p : ℂ) * (p : ℂ) + (q : ℂ) * (q : ℂ)) * ρ 0 0 := by ring
        _ = ρ 0 0 := by rw [hp2C, hq2C, hsum_pq, one_mul]
    · calc (p : ℂ) * ρ 0 1 * (q : ℂ) + (q : ℂ) * ρ 0 1 * (p : ℂ)
          = 2 * ((p : ℂ) * (q : ℂ)) * ρ 0 1 := by ring
        _ = (c : ℂ) * ρ 0 1 := by rw [hpqC]; push_cast; ring
    · calc (q : ℂ) * ρ 1 0 * (p : ℂ) + (p : ℂ) * ρ 1 0 * (q : ℂ)
          = 2 * ((p : ℂ) * (q : ℂ)) * ρ 1 0 := by ring
        _ = (c : ℂ) * ρ 1 0 := by rw [hpqC]; push_cast; ring
    · calc (q : ℂ) * ρ 1 1 * (q : ℂ) + (p : ℂ) * ρ 1 1 * (p : ℂ)
          = ((p : ℂ) * (p : ℂ) + (q : ℂ) * (q : ℂ)) * ρ 1 1 := by ring
        _ = ρ 1 1 := by rw [hp2C, hq2C, hsum_pq, one_mul]
  · have htr_exp : ρ 0 0 + ρ 1 1 = 1 := by
      simpa [Matrix.trace, Fin.sum_univ_two] using htr
    simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]
    calc (q : ℂ) * (p : ℂ) * ρ 0 0 * (p : ℂ) * (q : ℂ) +
          (p : ℂ) * (q : ℂ) * ρ 0 0 * (q : ℂ) * (p : ℂ) +
          ((p : ℂ) * (q : ℂ) * ρ 1 1 * (q : ℂ) * (p : ℂ) +
           (q : ℂ) * (p : ℂ) * ρ 1 1 * (p : ℂ) * (q : ℂ))
        = 2 * (((p : ℂ) * (p : ℂ)) * ((q : ℂ) * (q : ℂ))) * (ρ 0 0 + ρ 1 1) := by ring
      _ = (1 - (η : ℂ) ^ 2) / 2 := by
          rw [hp2C, hq2C, hprod_pq, htr_exp, mul_one]
          push_cast; ring
  · intro hc_pos
    simp [Matrix.mul_apply, Matrix.diagonal_apply]
    have hL : (p : ℂ) * (2⁻¹ : ℂ) * (q : ℂ) + (q : ℂ) * (2⁻¹ : ℂ) * (p : ℂ) =
        ((c / 2 : ℝ) : ℂ) := by
      calc (p : ℂ) * (2⁻¹ : ℂ) * (q : ℂ) + (q : ℂ) * (2⁻¹ : ℂ) * (p : ℂ)
          = (p : ℂ) * (q : ℂ) := by ring
        _ = ((c / 2 : ℝ) : ℂ) := hpqC
    rw [hL]
    intro heq
    have hc0 : c / 2 = 0 := by exact_mod_cast heq
    linarith

end JointExtension

end OSTQD
