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

end JointExtension

end OSTQD
