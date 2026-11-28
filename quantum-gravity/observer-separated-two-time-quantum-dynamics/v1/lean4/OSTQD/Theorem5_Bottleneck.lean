import OSTQD.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# OSTQD.Theorem5_Bottleneck

Theorem 5: Exact Sharp Mass-Loss Bottleneck Re-Observation Bound.
For any CPTP encoder `E : M_{dC}(ℂ) → M_{df}(ℂ)` and CPTP decoder `R : M_{df}(ℂ) → M_{dC}(ℂ)`,
the Schumacher entanglement fidelity satisfies
`F_e(R ∘ E) = (1 / dC²) ∑_{R, E} |Tr(R E)|² ≤ df² / dC²`,
and this bound is exact (attained whenever `df ≤ dC`).
-/

open scoped Matrix BigOperators ComplexConjugate

namespace OSTQD

lemma complex_sum_normSq_le_card_mul_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    Complex.normSq (∑ i ∈ s, f i) ≤ (s.card : ℝ) * ∑ i ∈ s, Complex.normSq (f i) := by
  have hre : (∑ i ∈ s, (f i).re) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (f i).re ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => (f i).re)
    simpa using this
  have him : (∑ i ∈ s, (f i).im) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (f i).im ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => (f i).im)
    simpa using this
  rw [Complex.normSq_apply, Complex.re_sum, Complex.im_sum]
  simp_rw [Complex.normSq_apply, sq] at hre him ⊢
  rw [Finset.sum_add_distrib, mul_add]
  linarith

lemma sum_normSq_row_mul_le_normSq_vec {dC df : ℕ}
    (Es : List (Matrix (Fin df) (Fin dC) ℂ))
    (hE_tp : (Es.map (fun E => Eᴴ * E)).sum = 1)
    (a : Fin df) (w : Fin dC → ℂ) :
    (Es.map (fun E => Complex.normSq (∑ j : Fin dC, E a j * w j))).sum ≤
      ∑ j : Fin dC, Complex.normSq (w j) := by
  have hstep : ∀ E : Matrix (Fin df) (Fin dC) ℂ,
      Complex.normSq (∑ j : Fin dC, E a j * w j) ≤
        (∑ i : Fin dC, ∑ j : Fin dC, star (w i) * (Eᴴ * E) i j * w j).re := by
    intro E
    have hquad : (∑ i : Fin dC, ∑ j : Fin dC, star (w i) * (Eᴴ * E) i j * w j).re =
        ∑ b : Fin df, Complex.normSq (∑ j : Fin dC, E b j * w j) := by
      have halg : ∑ i : Fin dC, ∑ j : Fin dC, star (w i) * (Eᴴ * E) i j * w j =
          ∑ b : Fin df, star (∑ i : Fin dC, E b i * w i) * (∑ j : Fin dC, E b j * w j) := by
        symm
        calc ∑ b : Fin df, star (∑ i : Fin dC, E b i * w i) * (∑ j : Fin dC, E b j * w j)
            = ∑ b : Fin df, ∑ i : Fin dC, ∑ j : Fin dC,
                star (w i) * (star (E b i) * E b j) * w j := by
              refine Finset.sum_congr rfl fun b _ => ?_
              rw [star_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [star_mul]
              ring
          _ = ∑ i : Fin dC, ∑ b : Fin df, ∑ j : Fin dC,
                star (w i) * (star (E b i) * E b j) * w j := Finset.sum_comm
          _ = ∑ i : Fin dC, ∑ j : Fin dC, ∑ b : Fin df,
                star (w i) * (star (E b i) * E b j) * w j := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
          _ = ∑ i : Fin dC, ∑ j : Fin dC, star (w i) * (Eᴴ * E) i j * w j := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
              rw [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl fun b _ => ?_
              simp [Matrix.conjTranspose_apply]
      rw [halg, Complex.re_sum]
      simp_rw [star_mul_self_re]
    rw [hquad]
    exact Finset.single_le_sum (fun b _ => Complex.normSq_nonneg _) (Finset.mem_univ a)
  have hsum_le :
      (Es.map (fun E => Complex.normSq (∑ j : Fin dC, E a j * w j))).sum ≤
        (Es.map (fun E =>
          (∑ i : Fin dC, ∑ j : Fin dC, star (w i) * (Eᴴ * E) i j * w j).re)).sum := by
    clear hE_tp
    induction Es with
    | nil => simp
    | cons E rest ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (hstep E) ih
  have hsum_eq :
      (Es.map (fun E =>
        (∑ i : Fin dC, ∑ j : Fin dC, star (w i) * (Eᴴ * E) i j * w j).re)).sum =
      (∑ i : Fin dC, ∑ j : Fin dC,
        star (w i) * ((Es.map (fun E => Eᴴ * E)).sum i j) * w j).re := by
    clear hE_tp hsum_le
    induction Es with
    | nil => simp
    | cons E rest ih =>
      simp only [List.map_cons, List.sum_cons, Matrix.add_apply, mul_add, add_mul,
        Finset.sum_add_distrib, Complex.add_re]
      rw [ih]
  rw [hsum_eq, hE_tp] at hsum_le
  have h1 : (∑ i : Fin dC, ∑ j : Fin dC,
      star (w i) * (1 : Matrix (Fin dC) (Fin dC) ℂ) i j * w j).re =
      ∑ j : Fin dC, Complex.normSq (w j) := by
    have hinner : ∑ i : Fin dC, ∑ j : Fin dC,
        star (w i) * (1 : Matrix (Fin dC) (Fin dC) ℂ) i j * w j =
        ∑ i : Fin dC, star (w i) * w i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji; simp [Matrix.one_apply_ne (Ne.symm hji)]
      · intro hi; exact (hi (Finset.mem_univ i)).elim
    rw [hinner, Complex.re_sum]
    simp_rw [star_mul_self_re]
  linarith

/-- **Theorem 5(a)** (Exact Mass-Loss Bottleneck Re-Observation Bound):
For arbitrary dimensions `dC > 0`, `df`, any CPTP encoder `Es` (`∑ E†E = I_{dC}`)
and any CPTP decoder `Rs` (`∑ R†R = I_{df}`),
`(1 / dC²) ∑_{R ∈ Rs} ∑_{E ∈ Es} |Tr(R E)|² ≤ df² / dC²`. -/
theorem bottleneck_entanglement_fidelity_bound {dC df : ℕ} (hdC : 0 < dC)
    (Es : List (Matrix (Fin df) (Fin dC) ℂ))
    (Rs : List (Matrix (Fin dC) (Fin df) ℂ))
    (hE_tp : (Es.map (fun E => Eᴴ * E)).sum = 1)
    (hR_tp : (Rs.map (fun R => Rᴴ * R)).sum = 1) :
    ((Rs.map (fun R => (Es.map (fun E => Complex.normSq (R * E).trace)).sum)).sum) /
      ((dC : ℝ) ^ 2) ≤ ((df : ℝ) ^ 2) / ((dC : ℝ) ^ 2) := by
  have hdC2 : 0 < (dC : ℝ) ^ 2 := sq_pos_of_pos (Nat.cast_pos.mpr hdC)
  apply div_le_div_of_nonneg_right _ (le_of_lt hdC2)
  have hsingleR : ∀ R : Matrix (Fin dC) (Fin df) ℂ,
      (Es.map (fun E => Complex.normSq (R * E).trace)).sum ≤
        (df : ℝ) * ((Rᴴ * R).trace).re := by
    intro R
    have hstepE : ∀ E : Matrix (Fin df) (Fin dC) ℂ,
        Complex.normSq (R * E).trace ≤
          (df : ℝ) * ∑ a : Fin df, Complex.normSq (∑ j : Fin dC, E a j * R j a) := by
      intro E
      have htr : (R * E).trace = ∑ a : Fin df, ∑ j : Fin dC, E a j * R j a := by
        rw [Matrix.trace_mul_comm, Matrix.trace]
        simp_rw [Matrix.diag_apply, Matrix.mul_apply]
      rw [htr]
      simpa using complex_sum_normSq_le_card_mul_sum Finset.univ
        (fun a : Fin df => ∑ j : Fin dC, E a j * R j a)
    have hsumE : (Es.map (fun E => Complex.normSq (R * E).trace)).sum ≤
        (df : ℝ) * ∑ a : Fin df,
          (Es.map (fun E => Complex.normSq (∑ j : Fin dC, E a j * R j a))).sum := by
      have h1 : (Es.map (fun E => Complex.normSq (R * E).trace)).sum ≤
          (Es.map (fun E => (df : ℝ) *
            ∑ a : Fin df, Complex.normSq (∑ j : Fin dC, E a j * R j a))).sum := by
        clear hE_tp
        induction Es with
        | nil => simp
        | cons E rest ih =>
          simp only [List.map_cons, List.sum_cons]
          exact add_le_add (hstepE E) ih
      have h2 : (Es.map (fun E => (df : ℝ) *
          ∑ a : Fin df, Complex.normSq (∑ j : Fin dC, E a j * R j a))).sum =
          (df : ℝ) * ∑ a : Fin df,
            (Es.map (fun E => Complex.normSq (∑ j : Fin dC, E a j * R j a))).sum := by
        clear hE_tp h1
        induction Es with
        | nil => simp
        | cons E rest ih =>
          simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, mul_add]
          rw [ih]
      linarith
    have hsum_a : ∑ a : Fin df,
        (Es.map (fun E => Complex.normSq (∑ j : Fin dC, E a j * R j a))).sum ≤
        ∑ a : Fin df, ∑ j : Fin dC, Complex.normSq (R j a) :=
      Finset.sum_le_sum fun a _ =>
        sum_normSq_row_mul_le_normSq_vec Es hE_tp a (fun j => R j a)
    have hfrob : ∑ a : Fin df, ∑ j : Fin dC, Complex.normSq (R j a) =
        ((Rᴴ * R).trace).re := by
      rw [trace_conjTranspose_mul_self_re]
      unfold frobNormSq
      rw [Finset.sum_comm]
    have hdf_nn : (0 : ℝ) ≤ (df : ℝ) := Nat.cast_nonneg df
    calc (Es.map (fun E => Complex.normSq (R * E).trace)).sum
        ≤ (df : ℝ) * ∑ a : Fin df,
            (Es.map (fun E => Complex.normSq (∑ j : Fin dC, E a j * R j a))).sum := hsumE
      _ ≤ (df : ℝ) * ∑ a : Fin df, ∑ j : Fin dC, Complex.normSq (R j a) :=
            mul_le_mul_of_nonneg_left hsum_a hdf_nn
      _ = (df : ℝ) * ((Rᴴ * R).trace).re := by rw [hfrob]
  have hsumR : (Rs.map (fun R =>
      (Es.map (fun E => Complex.normSq (R * E).trace)).sum)).sum ≤
      (df : ℝ) * (((Rs.map (fun R => Rᴴ * R)).sum).trace).re := by
    have h1 : (Rs.map (fun R =>
        (Es.map (fun E => Complex.normSq (R * E).trace)).sum)).sum ≤
        (Rs.map (fun R => (df : ℝ) * ((Rᴴ * R).trace).re)).sum := by
      clear hR_tp
      induction Rs with
      | nil => simp
      | cons R rest ih =>
        simp only [List.map_cons, List.sum_cons]
        exact add_le_add (hsingleR R) ih
    have h2 : (Rs.map (fun R => (df : ℝ) * ((Rᴴ * R).trace).re)).sum =
        (df : ℝ) * (((Rs.map (fun R => Rᴴ * R)).sum).trace).re := by
      clear hR_tp h1
      induction Rs with
      | nil => simp
      | cons R rest ih =>
        simp only [List.map_cons, List.sum_cons, Matrix.trace_add, Complex.add_re, mul_add]
        rw [ih]
    linarith
  rw [hR_tp, Matrix.trace_one, Fintype.card_fin] at hsumR
  simpa [sq] using hsumR

/-- **Theorem 5(b)** (Exact Sharpness of the Mass-Loss Bottleneck Bound):
Whenever `0 < df ≤ dC`, there exist explicit CPTP Kraus families
`Es : List (Matrix (Fin df) (Fin dC) ℂ)` and `Rs : List (Matrix (Fin dC) (Fin df) ℂ)`
attaining `F_e(R ∘ E) = df² / dC²` identically (isometric embedding `V` with
orthogonal projection `Vᴴ` plus garbage reset on the complement). -/
theorem bottleneck_bound_sharp {dC df : ℕ} (hdf : 0 < df) (hle : df ≤ dC) :
    ∃ (Es : List (Matrix (Fin df) (Fin dC) ℂ))
      (Rs : List (Matrix (Fin dC) (Fin df) ℂ)),
      (Es.map (fun E => Eᴴ * E)).sum = 1 ∧
      (Rs.map (fun R => Rᴴ * R)).sum = 1 ∧
      ((Rs.map (fun R => (Es.map (fun E => Complex.normSq (R * E).trace)).sum)).sum) /
        ((dC : ℝ) ^ 2) = ((df : ℝ) ^ 2) / ((dC : ℝ) ^ 2) := by
  let V : Matrix (Fin dC) (Fin df) ℂ :=
    Matrix.of fun i a => if i.val = a.val then (1 : ℂ) else 0
  let G : Fin dC → Matrix (Fin df) (Fin dC) ℂ := fun k =>
    Matrix.of fun a j => if df ≤ k.val ∧ a.val = 0 ∧ j = k then (1 : ℂ) else 0
  let Es : List (Matrix (Fin df) (Fin dC) ℂ) := Vᴴ :: (List.finRange dC).map G
  let Rs : List (Matrix (Fin dC) (Fin df) ℂ) := [V]
  refine ⟨Es, Rs, ?_, ?_, ?_⟩
  · -- Prove ∑ E†E = I_{dC}
    have hV : ∀ i j : Fin dC,
        ((Vᴴ)ᴴ * Vᴴ) i j = if i.val < df ∧ i = j then (1 : ℂ) else 0 := by
      intro i j
      rw [Matrix.conjTranspose_conjTranspose, Matrix.mul_apply]
      by_cases hi : i.val < df
      · let a0 : Fin df := ⟨i.val, hi⟩
        rw [Finset.sum_eq_single a0]
        · by_cases hij : i = j
          · subst hij; simp [V, a0, hi]
          · have hne : j.val ≠ i.val := fun h => hij (Fin.ext h.symm)
            simp [V, a0, hi, hij, hne]
        · intro a _ ha
          have hne : i.val ≠ a.val := fun h => ha (Fin.ext h.symm)
          simp [V, hne]
        · intro h; exact (h (Finset.mem_univ a0)).elim
      · simp only [hi, false_and, ↓reduceIte]
        apply Finset.sum_eq_zero
        intro a _
        have hne : i.val ≠ a.val := by omega
        simp [V, hne]
    have hG_entry : ∀ (k i j : Fin dC),
        ((G k)ᴴ * G k) i j = if df ≤ k.val ∧ i = k ∧ j = k then (1 : ℂ) else 0 := by
      intro k i j
      rw [Matrix.mul_apply]
      let a0 : Fin df := ⟨0, hdf⟩
      rw [Finset.sum_eq_single a0]
      · by_cases hcond : df ≤ k.val ∧ i = k ∧ j = k
        · rcases hcond with ⟨hk, rfl, rfl⟩
          simp [G, a0, hk]
        · simp only [G, Matrix.conjTranspose_apply, Matrix.of_apply, a0, true_and]
          by_cases h1 : df ≤ k.val ∧ i = k
          · have h2 : ¬(df ≤ k.val ∧ j = k) := fun h => hcond ⟨h1.1, h1.2, h.2⟩
            simp [h1]
          · simp [h1, hcond]
      · intro a _ ha
        have hne : a.val ≠ 0 := fun h => ha (Fin.ext h)
        simp [G, hne]
      · intro h; exact (h (Finset.mem_univ a0)).elim
    have hsum_list : ∀ (l : List (Fin dC)) (i j : Fin dC),
        ((l.map (fun k => (G k)ᴴ * G k)).sum) i j =
        (l.map (fun k => ((G k)ᴴ * G k) i j)).sum := by
      intro l i j
      induction l with
      | nil => simp
      | cons k rest ih => simp [ih]
    ext i j
    simp only [Es, List.map_cons, List.sum_cons, List.map_map, Matrix.add_apply,
      Function.comp_def, hsum_list, hV, hG_entry]
    have hfin' : ((List.finRange dC).map
        (fun k : Fin dC => if df ≤ k.val ∧ i = k ∧ j = k then (1 : ℂ) else 0)).sum =
        ∑ k : Fin dC, if df ≤ k.val ∧ i = k ∧ j = k then (1 : ℂ) else 0 :=
      (Fin.sum_univ_def _).symm
    rw [hfin']
    rw [Finset.sum_eq_single i]
    · by_cases hij : i = j
      · subst hij
        by_cases hi : i.val < df
        · have hnot : ¬(df ≤ i.val) := by omega
          simp [hi, hnot]
        · have hge : df ≤ i.val := by omega
          simp [hi, hge]
      · simp [hij, Ne.symm hij]
    · intro k _ hki
      have hne : i ≠ k := Ne.symm hki
      simp [hne]
    · intro h; exact (h (Finset.mem_univ i)).elim
  · -- Prove ∑ R†R = I_{df}
    ext a b
    simp only [Rs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      Matrix.mul_apply]
    let i0 : Fin dC := ⟨a.val, Nat.lt_of_lt_of_le a.isLt hle⟩
    rw [Finset.sum_eq_single i0]
    · by_cases hab : a = b
      · subst hab; simp [V, i0]
      · have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
        simp [V, i0, hab, hne]
    · intro i _ hi
      have hne : i.val ≠ a.val := fun h => hi (Fin.ext h)
      simp [V, hne]
    · intro h; exact (h (Finset.mem_univ i0)).elim
  · -- Prove exact saturation F_e = df² / dC²
    congr 1
    simp only [Rs, Es, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      List.map_map, Function.comp_def]
    have htrV : (V * Vᴴ).trace = (df : ℂ) := by
      rw [Matrix.trace]
      simp_rw [Matrix.diag_apply]
      have hentry : ∀ i : Fin dC, (V * Vᴴ) i i = if i.val < df then (1 : ℂ) else 0 := by
        intro i
        rw [Matrix.mul_apply]
        by_cases hi : i.val < df
        · let a0 : Fin df := ⟨i.val, hi⟩
          rw [Finset.sum_eq_single a0]
          · simp [V, a0, hi]
          · intro a _ ha
            have hne : i.val ≠ a.val := fun h => ha (Fin.ext h.symm)
            simp [V, hne]
          · intro h; exact (h (Finset.mem_univ a0)).elim
        · simp only [hi, ↓reduceIte]
          apply Finset.sum_eq_zero
          intro a _
          have hne : i.val ≠ a.val := by omega
          simp [V, hne]
      simp_rw [hentry]
      have hcard : (Finset.univ.filter (fun i : Fin dC => i.val < df)).card = df := by
        have hbij : Finset.univ.filter (fun i : Fin dC => i.val < df) =
            Finset.univ.image (fun a : Fin df => (⟨a.val, Nat.lt_of_lt_of_le a.isLt hle⟩ : Fin dC)) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
          constructor
          · intro hi; exact ⟨⟨i.val, hi⟩, rfl⟩
          · rintro ⟨a, rfl⟩; exact a.isLt
        rw [hbij, Finset.card_image_of_injective]
        · simp
        · intro a b hab
          exact Fin.ext (by simpa using congrArg Fin.val hab)
      rw [Finset.sum_boole, hcard]
    have htrG : ∀ k : Fin dC, (V * G k).trace = 0 := by
      intro k
      rw [Matrix.trace]
      simp_rw [Matrix.diag_apply]
      apply Finset.sum_eq_zero
      intro i _
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro a _
      by_cases h1 : i.val = a.val
      · by_cases h2 : df ≤ k.val ∧ a.val = 0 ∧ i = k
        · rcases h2 with ⟨hk, _, rfl⟩
          omega
        · simp [V, G, h1, h2]
      · simp [V, h1]
    have htail : ((List.finRange dC).map (fun k => Complex.normSq (V * G k).trace)).sum = 0 := by
      apply List.sum_eq_zero
      intro x hx
      rcases List.mem_map.mp hx with ⟨k, _, rfl⟩
      rw [htrG k, map_zero]
    rw [htail, add_zero, htrV]
    simp [Complex.normSq_natCast, sq]

/-- **Theorem 5(c)** (Universal Entanglement Fidelity Upper Cap `F_e(R ∘ E) ≤ 1`):
For any CPTP encoder `Es` and CPTP decoder `Rs`, the entanglement fidelity never exceeds `1`. -/
theorem entanglement_fidelity_le_one {dC df : ℕ} (hdC : 0 < dC)
    (Es : List (Matrix (Fin df) (Fin dC) ℂ))
    (Rs : List (Matrix (Fin dC) (Fin df) ℂ))
    (hE_tp : (Es.map (fun E => Eᴴ * E)).sum = 1)
    (hR_tp : (Rs.map (fun R => Rᴴ * R)).sum = 1) :
    ((Rs.map (fun R => (Es.map (fun E => Complex.normSq (R * E).trace)).sum)).sum) /
      ((dC : ℝ) ^ 2) ≤ 1 := by
  have hdC2 : 0 < (dC : ℝ) ^ 2 := sq_pos_of_pos (Nat.cast_pos.mpr hdC)
  rw [div_le_one hdC2]
  have hsingle : ∀ (R : Matrix (Fin dC) (Fin df) ℂ) (E : Matrix (Fin df) (Fin dC) ℂ),
      Complex.normSq (R * E).trace ≤ (dC : ℝ) * (((R * E)ᴴ * (R * E)).trace).re := by
    intro R E
    have hcs : Complex.normSq (R * E).trace ≤
        (dC : ℝ) * ∑ i : Fin dC, Complex.normSq ((R * E) i i) := by
      rw [Matrix.trace]
      simp_rw [Matrix.diag_apply]
      simpa using complex_sum_normSq_le_card_mul_sum Finset.univ (fun i : Fin dC => (R * E) i i)
    have hdiag_le : ∑ i : Fin dC, Complex.normSq ((R * E) i i) ≤ frobNormSq (R * E) := by
      unfold frobNormSq
      refine Finset.sum_le_sum fun i _ =>
        Finset.single_le_sum (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
    rw [trace_conjTranspose_mul_self_re]
    exact le_trans hcs (mul_le_mul_of_nonneg_left hdiag_le (Nat.cast_nonneg dC))
  have hsum_R_fixed_E : ∀ E : Matrix (Fin df) (Fin dC) ℂ,
      (Rs.map (fun R => (((R * E)ᴴ * (R * E)).trace).re)).sum = ((Eᴴ * E).trace).re := by
    intro E
    have hlin : (Rs.map (fun R => (((R * E)ᴴ * (R * E)).trace).re)).sum =
        ((Eᴴ * (Rs.map (fun R => Rᴴ * R)).sum * E).trace).re := by
      clear hR_tp
      induction Rs with
      | nil => simp
      | cons R rest ih =>
        simp only [List.map_cons, List.sum_cons, Matrix.mul_add, Matrix.add_mul,
          Matrix.trace_add, Complex.add_re]
        rw [ih, Matrix.conjTranspose_mul]
        simp [Matrix.mul_assoc]
    rw [hlin, hR_tp, Matrix.mul_one]
  have hswap : (Rs.map (fun R => (Es.map (fun E => Complex.normSq (R * E).trace)).sum)).sum ≤
      (dC : ℝ) * (Es.map (fun E => (Rs.map (fun R => (((R * E)ᴴ * (R * E)).trace).re)).sum)).sum := by
    have h1 : (Rs.map (fun R => (Es.map (fun E => Complex.normSq (R * E).trace)).sum)).sum ≤
        (Rs.map (fun R => (Es.map (fun E => (dC : ℝ) * (((R * E)ᴴ * (R * E)).trace).re)).sum)).sum := by
      clear hE_tp hR_tp hsum_R_fixed_E
      induction Rs with
      | nil => simp
      | cons R rest ih =>
        simp only [List.map_cons, List.sum_cons]
        refine add_le_add ?_ ih
        clear ih
        induction Es with
        | nil => simp
        | cons E erest eih =>
          simp only [List.map_cons, List.sum_cons]
          exact add_le_add (hsingle R E) eih
    have h2 : (Rs.map (fun R => (Es.map (fun E => (dC : ℝ) * (((R * E)ᴴ * (R * E)).trace).re)).sum)).sum =
        (dC : ℝ) * (Es.map (fun E => (Rs.map (fun R => (((R * E)ᴴ * (R * E)).trace).re)).sum)).sum := by
      clear hE_tp hR_tp hsum_R_fixed_E h1
      induction Rs with
      | nil =>
        simp only [List.map_nil, List.sum_nil]
        have hzero : (Es.map (fun _ => (0 : ℝ))).sum = 0 := by
          induction Es with
          | nil => simp
          | cons _ _ _ => simp
        rw [hzero, mul_zero]
      | cons R rest ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [ih]
        have hdist : ∀ (l : List (Matrix (Fin df) (Fin dC) ℂ)),
            (l.map (fun E => (dC : ℝ) * (((R * E)ᴴ * (R * E)).trace).re)).sum +
            (dC : ℝ) * (l.map (fun E => (rest.map (fun R' => (((R' * E)ᴴ * (R' * E)).trace).re)).sum)).sum =
            (dC : ℝ) * (l.map (fun E => (((R * E)ᴴ * (R * E)).trace).re +
              (rest.map (fun R' => (((R' * E)ᴴ * (R' * E)).trace).re)).sum)).sum := by
          intro l
          induction l with
          | nil => simp
          | cons E erest eih =>
            simp only [List.map_cons, List.sum_cons]
            linarith
        exact hdist Es
    linarith
  have hsum_E : (Es.map (fun E => (Rs.map (fun R => (((R * E)ᴴ * (R * E)).trace).re)).sum)).sum =
      (dC : ℝ) := by
    have hmap : Es.map (fun E => (Rs.map (fun R => (((R * E)ᴴ * (R * E)).trace).re)).sum) =
        Es.map (fun E => ((Eᴴ * E).trace).re) :=
      List.map_congr_left fun E _ => hsum_R_fixed_E E
    rw [hmap]
    have hlinE : (Es.map (fun E => ((Eᴴ * E).trace).re)).sum =
        (((Es.map (fun E => Eᴴ * E)).sum).trace).re := by
      clear hE_tp hR_tp hsum_R_fixed_E hswap hmap
      induction Es with
      | nil => simp
      | cons E rest ih =>
        simp only [List.map_cons, List.sum_cons, Matrix.trace_add, Complex.add_re]
        rw [ih]
    rw [hlinE, hE_tp, Matrix.trace_one, Fintype.card_fin, Complex.natCast_re]
  rw [hsum_E] at hswap
  simpa [sq] using hswap

/-- **Theorem 5 (Combined Exact Min Bound)**:
`F_e(R ∘ E) ≤ min(1, df² / dC²)` for arbitrary CPTP channels `E` and `R`. -/
theorem bottleneck_entanglement_fidelity_min_bound {dC df : ℕ} (hdC : 0 < dC)
    (Es : List (Matrix (Fin df) (Fin dC) ℂ))
    (Rs : List (Matrix (Fin dC) (Fin df) ℂ))
    (hE_tp : (Es.map (fun E => Eᴴ * E)).sum = 1)
    (hR_tp : (Rs.map (fun R => Rᴴ * R)).sum = 1) :
    ((Rs.map (fun R => (Es.map (fun E => Complex.normSq (R * E).trace)).sum)).sum) /
      ((dC : ℝ) ^ 2) ≤ min 1 (((df : ℝ) ^ 2) / ((dC : ℝ) ^ 2)) :=
  le_min (entanglement_fidelity_le_one hdC Es Rs hE_tp hR_tp)
    (bottleneck_entanglement_fidelity_bound hdC Es Rs hE_tp hR_tp)

/-- **Theorem 5(b')** (Exact Sharpness for `0 < dC ≤ df`, Isometric Embedding + Reset Decoder):
Whenever `0 < dC ≤ df`, there exist explicit CPTP Kraus families `Es` (single isometry `V`) and
`Rs` (`Vᴴ` plus complement reset onto `|0⟩_C`) attaining `F_e(R ∘ E) = 1 = min(1, df²/dC²)`. -/
theorem bottleneck_bound_sharp_large_df {dC df : ℕ} (hdC : 0 < dC) (hle : dC ≤ df) :
    ∃ (Es : List (Matrix (Fin df) (Fin dC) ℂ))
      (Rs : List (Matrix (Fin dC) (Fin df) ℂ)),
      (Es.map (fun E => Eᴴ * E)).sum = 1 ∧
      (Rs.map (fun R => Rᴴ * R)).sum = 1 ∧
      ((Rs.map (fun R => (Es.map (fun E => Complex.normSq (R * E).trace)).sum)).sum) /
        ((dC : ℝ) ^ 2) = 1 := by
  have hdC2 : (dC : ℝ) ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos (Nat.cast_pos.mpr hdC))
  let V : Matrix (Fin df) (Fin dC) ℂ :=
    Matrix.of fun a i => if a.val = i.val then (1 : ℂ) else 0
  let Hk : Fin df → Matrix (Fin dC) (Fin df) ℂ := fun k =>
    Matrix.of fun i a => if dC ≤ k.val ∧ i.val = 0 ∧ a = k then (1 : ℂ) else 0
  let Es : List (Matrix (Fin df) (Fin dC) ℂ) := [V]
  let Rs : List (Matrix (Fin dC) (Fin df) ℂ) := Vᴴ :: (List.finRange df).map Hk
  refine ⟨Es, Rs, ?_, ?_, ?_⟩
  · -- Vᴴ * V = I_{dC}
    ext i j
    simp only [Es, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      Matrix.mul_apply]
    let a0 : Fin df := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hle⟩
    rw [Finset.sum_eq_single a0]
    · by_cases hij : i = j
      · subst hij; simp [V, a0]
      · have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
        simp [V, a0, hij, hne]
    · intro a _ ha
      have hne : a.val ≠ i.val := fun h => ha (Fin.ext h)
      simp [V, hne]
    · intro h; exact (h (Finset.mem_univ a0)).elim
  · -- V Vᴴ + ∑ Hkᴴ Hk = I_{df}
    have hV : ∀ a b : Fin df,
        ((Vᴴ)ᴴ * Vᴴ) a b = if a.val < dC ∧ a = b then (1 : ℂ) else 0 := by
      intro a b
      rw [Matrix.conjTranspose_conjTranspose, Matrix.mul_apply]
      by_cases ha : a.val < dC
      · let i0 : Fin dC := ⟨a.val, ha⟩
        rw [Finset.sum_eq_single i0]
        · by_cases hab : a = b
          · subst hab; simp [V, i0, ha]
          · have hne : b.val ≠ a.val := fun h => hab (Fin.ext h.symm)
            simp [V, i0, ha, hab, hne]
        · intro i _ hi
          have hne : a.val ≠ i.val := fun h => hi (Fin.ext h.symm)
          simp [V, hne]
        · intro h; exact (h (Finset.mem_univ i0)).elim
      · simp only [ha, false_and, ↓reduceIte]
        apply Finset.sum_eq_zero; intro i _
        have hne : a.val ≠ i.val := by omega
        simp [V, hne]
    have hH_entry : ∀ (k a b : Fin df),
        ((Hk k)ᴴ * Hk k) a b = if dC ≤ k.val ∧ a = k ∧ b = k then (1 : ℂ) else 0 := by
      intro k a b
      rw [Matrix.mul_apply]
      let i0 : Fin dC := ⟨0, hdC⟩
      rw [Finset.sum_eq_single i0]
      · by_cases hcond : dC ≤ k.val ∧ a = k ∧ b = k
        · rcases hcond with ⟨hk, rfl, rfl⟩; simp [Hk, i0, hk]
        · simp only [Hk, Matrix.conjTranspose_apply, Matrix.of_apply, i0, true_and]
          by_cases h1 : dC ≤ k.val ∧ a = k
          · have hb : b ≠ k := fun hb => hcond ⟨h1.1, h1.2, hb⟩
            simp [h1, hb]
          · simp [h1, hcond]
      · intro i _ hi
        have hne : i.val ≠ 0 := fun h => hi (Fin.ext h)
        simp [Hk, hne]
      · intro h; exact (h (Finset.mem_univ i0)).elim
    have hsum_list : ∀ (l : List (Fin df)) (a b : Fin df),
        ((l.map (fun k => (Hk k)ᴴ * Hk k)).sum) a b =
        (l.map (fun k => ((Hk k)ᴴ * Hk k) a b)).sum := by
      intro l a b; induction l with
      | nil => simp
      | cons k rest ih => simp [ih]
    ext a b
    simp only [Rs, List.map_cons, List.sum_cons, List.map_map, Matrix.add_apply,
      Function.comp_def, hsum_list, hV, hH_entry]
    have hfin' : ((List.finRange df).map
        (fun k : Fin df => if dC ≤ k.val ∧ a = k ∧ b = k then (1 : ℂ) else 0)).sum =
        ∑ k : Fin df, if dC ≤ k.val ∧ a = k ∧ b = k then (1 : ℂ) else 0 :=
      (Fin.sum_univ_def _).symm
    rw [hfin', Finset.sum_eq_single a]
    · by_cases hab : a = b
      · subst hab
        by_cases ha : a.val < dC
        · have hnot : ¬(dC ≤ a.val) := by omega
          simp [ha, hnot]
        · have hge : dC ≤ a.val := by omega
          simp [ha, hge]
      · simp [hab, Ne.symm hab]
    · intro k _ hka; simp [Ne.symm hka]
    · intro h; exact (h (Finset.mem_univ a)).elim
  · -- Exact fidelity F_e = 1
    simp only [Rs, Es, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      List.map_map, Function.comp_def]
    have htrV : (Vᴴ * V).trace = (dC : ℂ) := by
      rw [Matrix.trace]; simp_rw [Matrix.diag_apply]
      have hentry : ∀ i : Fin dC, (Vᴴ * V) i i = 1 := by
        intro i; rw [Matrix.mul_apply]
        let a0 : Fin df := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hle⟩
        rw [Finset.sum_eq_single a0]
        · simp [V, a0]
        · intro a _ ha; have hne : a.val ≠ i.val := fun h => ha (Fin.ext h); simp [V, hne]
        · intro h; exact (h (Finset.mem_univ a0)).elim
      simp_rw [hentry]; simp
    have htrH : ∀ k : Fin df, (Hk k * V).trace = 0 := by
      intro k; rw [Matrix.trace]; simp_rw [Matrix.diag_apply]
      apply Finset.sum_eq_zero; intro i _
      rw [Matrix.mul_apply]; apply Finset.sum_eq_zero; intro a _
      by_cases h1 : a.val = i.val
      · by_cases h2 : dC ≤ k.val ∧ i.val = 0 ∧ a = k
        · rcases h2 with ⟨hk, _, rfl⟩; omega
        · simp [V, Hk, h1, h2]
      · simp [V, h1]
    have htail : ((List.finRange df).map (fun k => Complex.normSq (Hk k * V).trace)).sum = 0 := by
      apply List.sum_eq_zero; intro x hx
      rcases List.mem_map.mp hx with ⟨k, _, rfl⟩
      rw [htrH k, map_zero]
    rw [htail, add_zero, htrV]
    simp [Complex.normSq_natCast, ← sq, div_self hdC2]

/-- **Theorem 5 Resource-Assumption Witness** (Classical Side-Channel Beats Unassisted Bottleneck):
For `d_C = 4, d_f = 2`, allowing a 1-bit classical flag alongside the 2D quantum channel realizes
the 2-block pinching channel with Kraus operators `P_0 = diag(1,1,0,0)` and `P_1 = diag(0,0,1,1)`.
This channel is CPTP (`P_0ᴴ P_0 + P_1ᴴ P_1 = I_4`) and achieves `F_e = 1/2 > 1/4 = d_f²/d_C²`,
demonstrating that forbidding classical side communication / radiation access is essential for
Theorem 5 (Farber–Gour 2026 unassisted single-shot compression). -/
theorem classical_flag_beats_unassisted_bottleneck :
    let P0 : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal ![1, 1, 0, 0]
    let P1 : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal ![0, 0, 1, 1]
    P0ᴴ * P0 + P1ᴴ * P1 = 1 ∧
    (Complex.normSq P0.trace + Complex.normSq P1.trace) / ((4 : ℝ) ^ 2) = 1 / 2 ∧
    ((2 : ℝ) ^ 2) / ((4 : ℝ) ^ 2) <
      (Complex.normSq P0.trace + Complex.normSq P1.trace) / ((4 : ℝ) ^ 2) := by
  dsimp only
  have htp : (Matrix.diagonal ![1, 1, 0, 0] : Matrix (Fin 4) (Fin 4) ℂ)ᴴ *
      Matrix.diagonal ![1, 1, 0, 0] +
      (Matrix.diagonal ![0, 0, 1, 1] : Matrix (Fin 4) (Fin 4) ℂ)ᴴ *
      Matrix.diagonal ![0, 0, 1, 1] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hfe : (Complex.normSq (Matrix.diagonal ![1, 1, 0, 0] : Matrix (Fin 4) (Fin 4) ℂ).trace +
      Complex.normSq (Matrix.diagonal ![0, 0, 1, 1] : Matrix (Fin 4) (Fin 4) ℂ).trace) /
      ((4 : ℝ) ^ 2) = 1 / 2 := by
    simp [Matrix.trace, Fin.sum_univ_four, Complex.normSq_apply]
    norm_num
  refine ⟨htp, hfe, ?_⟩
  rw [hfe]; norm_num

end OSTQD
