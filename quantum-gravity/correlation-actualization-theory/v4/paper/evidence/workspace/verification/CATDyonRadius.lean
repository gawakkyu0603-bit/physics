import analysis.inner_product_space.basic
import analysis.special_functions.pow.real
import measure_theory.integral.bochner
import tactic

noncomputable theory
open_locale big_operators
namespace cat_dyon_radius

-- z is squared frequency and k is squared wave number, both in vector-mass units.
def wave (z k x : ℝ) := (z-(k+1))^2 - 8*x*(k+1-2*x) - x*(1-2*x)

theorem band (k x : ℝ) : wave 0 k x = (k-(4*x-1))^2 - x*(1-2*x) :=
by { unfold wave, ring }
theorem homogeneous (x : ℝ) : wave 0 0 x = (3*x-1)*(6*x-1) :=
by { unfold wave, ring }
theorem growing_at_center (x : ℝ) (h : 1/3<x) (u : x≤4/9) :
 0<4*x-1 ∧ wave 0 (4*x-1) x < 0 :=
begin
 rw [band], simp only [sub_self,zero_pow (by norm_num : 0<2),zero_sub,neg_lt_zero],
 exact ⟨by linarith, mul_pos (by linarith) (by linarith)⟩
end
theorem fastest (k x : ℝ) : wave (-(1-2*x)/8) k x = (k-(34*x-9)/8)^2 :=
by { unfold wave, ring }
theorem physical_peak (x : ℝ) (h : 1/3<x) (u : x≤4/9) :
 0<(34*x-9)/8 ∧ 1/72 ≤ (1-2*x)/8 := ⟨by linarith,by linarith⟩
theorem root_bound (z k x : ℝ) (hx : x≤4/9) (hk : 0≤k)
 (hz : z < -(1-2*x)/8) : 0 < wave z k x :=
begin
 have h : 0 < (-(1-2*x)/8-z)*(2*(k+1)-z+(1-2*x)/8) :=
   mul_pos (by linarith) (by linarith),
 have e : wave z k x = (k-(34*x-9)/8)^2+
      (-(1-2*x)/8-z)*(2*(k+1)-z+(1-2*x)/8) := by {unfold wave,ring},
 rw [e], exact add_pos_of_nonneg_of_pos (sq_nonneg _) h
end

theorem orbital_multiplet (c : ℝ) : 4 + 2*c - 2 - 2*(1+c) = 0 := by ring
theorem character_sum {ι : Type*} (g : finset ι) (c t : ι → ℝ)
 (hc : ∀i∈g, c i≤4) (ht : ∀i∈g, 0≤t i) :
 (∑ i in g, (c i/4-1)*t i) ≤ 0 :=
finset.sum_nonpos (λ i hi, mul_nonpos_of_nonpos_of_nonneg (by linarith [hc i hi]) (ht i hi))
theorem fourier_gram (re im : ℝ) : 0 ≤ re^2+im^2 := by positivity
theorem kernel_integral (μ : measure_theory.measure ℝ) {f : ℝ → ℝ} (h : ∀s, f s ≤ 0) :
 (∫ s, f s ∂μ) ≤ 0 := measure_theory.integral_nonpos h

-- In an orthonormal frame the two residual Narain vectors have this Gram determinant.
theorem gram_pos {E : Type*} [normed_add_comm_group E] [inner_product_space ℝ E] (p q : E) :
 (inner p q : ℝ)^2 ≤ ‖p‖^2*‖q‖^2 :=
begin
 have h := abs_real_inner_le_norm p q,
 have m := mul_self_le_mul_self (abs_nonneg (inner p q : ℝ)) h,
 rw [abs_mul_abs_self] at m, nlinarith
end

theorem det_gain (c d p q z : ℝ) :
 (c+p)*(d+q)-z^2-c*d = c*q+d*p+(p*q-z^2) := by ring
theorem det_monotone (c d p q z : ℝ) (hc : 0<c) (hd : 0<d)
 (hp : 0≤p) (hq : 0≤q) (hg : z^2≤p*q) :
 c*d ≤ (c+p)*(d+q)-z^2 :=
by nlinarith [mul_nonneg hc.le hq,mul_nonneg hd.le hp]
theorem det_equal (c d p q z : ℝ) (hc : 0<c) (hd : 0<d)
 (hp : 0≤p) (hq : 0≤q) (hg : z^2≤p*q)
 (same : (c+p)*(d+q)-z^2 = c*d) : p=0 ∧ q=0 :=
begin
 split,
 { by_contra h, have t := mul_pos hd (lt_of_le_of_ne hp (ne.symm h)),
   nlinarith [mul_nonneg hc.le hq] },
 { by_contra h, have t := mul_pos hc (lt_of_le_of_ne hq (ne.symm h)),
   nlinarith [mul_nonneg hd.le hp] }
end
theorem trace_extra (p q a s : ℝ) :
 p^2-2*a*(p*q)+(a^2+s^2)*q^2 = (p-a*q)^2+(s*q)^2 := by ring
theorem axion_min (k l a s : ℝ) (hs : s≠0) :
 (4*k^2+4*l^2*(a^2+s^2))/s - 8*k*l = 4*((k-l*s)^2+(l*a)^2)/s :=
by { field_simp [hs], ring }
theorem axion_eq (k l a s : ℝ) (hl : 0<l) (h : (k-l*s)^2+(l*a)^2=0) :
 k=l*s ∧ a=0 :=
begin
 have e : (l*a)^2=0 := by nlinarith [sq_nonneg (k-l*s),sq_nonneg (l*a)],
 have f : (k-l*s)^2=0 := by linarith,
 exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp f),
        (mul_eq_zero.mp (sq_eq_zero_iff.mp e)).resolve_left (ne_of_gt hl)⟩
end
def mass2 (c d z a s : ℝ) := (c-2*a*z+(a^2+s^2)*d)/s+2*real.sqrt (c*d-z^2)
theorem mass_minimum (k l p q z a s : ℝ) (hk : 0<k) (hl : 0<l) (hs : 0<s)
 (hp : 0≤p) (hq : 0≤q) (hg : z^2≤p*q) (ht : 0≤p-2*a*z+(a^2+s^2)*q) :
 16*k*l ≤ mass2 (4*k^2+p) (4*l^2+q) z a s :=
begin
 have hdet := det_monotone (4*k^2) (4*l^2) p q z (by positivity) (by positivity) hp hq hg,
 have he : 4*k^2*(4*l^2)=(4*k*l)^2 := by ring,
 rw [he] at hdet, have hr := real.sqrt_le_sqrt hdet,
 rw [real.sqrt_sq (by positivity : 0≤4*k*l)] at hr,
 have h0 := axion_min k l a s (ne_of_gt hs),
 have htt := div_nonneg ht hs.le,
 have H : 0≤4*((k-l*s)^2+(l*a)^2)/s := by positivity,
 unfold mass2,
 have e : (4*k^2+p-2*a*z+(a^2+s^2)*(4*l^2+q))/s =
   (4*k^2+4*l^2*(a^2+s^2))/s+(p-2*a*z+(a^2+s^2)*q)/s := by ring,
 rw [e], linarith
end

theorem all_columns {ι : Type*} [fintype ι] (a : ι → ι → ℝ) (w : ι → ℝ)
 (hw : ∀j, 0 < w j) :
 (∑j, w j*(∑i, (a i j)^2))=0 ↔ ∀ i j, a i j=0 :=
begin
 split,
 { intros h i j,
   have pos : ∀k∈(finset.univ : finset ι), 0≤w k*(∑v, (a v k)^2) :=
      λ k hk, mul_nonneg (hw k).le (finset.sum_nonneg (λ v hv, sq_nonneg (a v k))),
   have zn := (finset.sum_eq_zero_iff_of_nonneg pos).mp h j (finset.mem_univ j),
   have col := (mul_eq_zero.mp zn).resolve_left (ne_of_gt (hw j)),
   have pcol : ∀v∈(finset.univ : finset ι), 0≤(a v j)^2 := λ v hv, sq_nonneg _,
   exact sq_eq_zero_iff.mp ((finset.sum_eq_zero_iff_of_nonneg pcol).mp col i (finset.mem_univ i)) },
 { intro h, simp [h] }
end
theorem mass_equality (k l p q z a s : ℝ) (hk : 0<k) (hl : 0<l) (hs : 0<s)
 (hp : 0≤p) (hq : 0≤q) (hg : z^2≤p*q) (ht : 0≤p-2*a*z+(a^2+s^2)*q)
 (hit : mass2 (4*k^2+p) (4*l^2+q) z a s=16*k*l) :
 p=0 ∧ q=0 ∧ a=0 ∧ k=l*s :=
begin
 let base := 4*k^2*(4*l^2),
 let det := (4*k^2+p)*(4*l^2+q)-z^2,
 have hb : base=(4*k*l)^2 := by {dsimp [base],ring},
 have hd : base≤det := det_monotone _ _ _ _ _ (by positivity) (by positivity) hp hq hg,
 have hr := real.sqrt_le_sqrt hd, rw [hb,real.sqrt_sq (by positivity : 0≤4*k*l)] at hr,
 have e : mass2 (4*k^2+p) (4*l^2+q) z a s - 16*k*l =
    (p-2*a*z+(a^2+s^2)*q)/s + 4*((k-l*s)^2+(l*a)^2)/s + 2*(real.sqrt det-4*k*l) :=
    by {unfold mass2, dsimp [det], field_simp [ne_of_gt hs], ring},
 have t1 := div_nonneg ht hs.le,
 have t2 : 0≤4*((k-l*s)^2+(l*a)^2)/s := by positivity,
 rw [hit] at e,
 have hroot : real.sqrt det=4*k*l := by linarith only [e,t1,t2,hr],
 have hdet : det=base, {rw [hb,←hroot,real.sq_sqrt (le_trans (by dsimp [base];positivity) hd)]},
 rcases det_equal (4*k^2) (4*l^2) p q z (by positivity) (by positivity) hp hq hg hdet with ⟨ep,eq⟩,
 have efrac : 4*((k-l*s)^2+(l*a)^2)/s=0 := by linarith only [e,t1,t2,hr],
 have et := (div_eq_zero_iff.mp efrac).resolve_right (ne_of_gt hs),
 have az := axion_eq k l a s hl (by linarith only [et]),
 exact ⟨ep,eq,az.2,az.1⟩
end
theorem symmetric_skew (g b : ℝ) (h : g+b=0) (v : g-b=0) : g=0 ∧ b=0 :=
⟨by linarith,by linarith⟩
theorem shape_mass (w r p : ℝ) (hp : p≠0) :
 r*w/16/(p^2/4)*2 = r*w/(2*p^2) := by {field_simp [hp],ring}
theorem long_range (r m p h : ℝ) (hp : 0<p) (hρ : r≤3*p^2*h^2)
 (hm : 2*p^2*m≤r) : m≤3*h^2/2 :=
begin
 by_contra hh, have v := mul_pos (sq_pos_of_pos hp) (sub_pos.mpr (lt_of_not_ge hh)), nlinarith
end

theorem brane_charge (d : ℝ) :
 (d/4+(6-d)/4)+1/2=2 := by ring
theorem two_sources (w r s : ℝ) : (w*r+(1-w)*s)-s = w*(r-s) := by ring
theorem mix_obstruction (alpha visible open_share sum_open limit : ℝ)
 (h : visible≤open_share*sum_open) (hw : open_share≤limit) (hp : 0≤sum_open)
 (ha : alpha=visible) : alpha≤limit*sum_open :=
ha.symm ▸ le_trans h (mul_le_mul_of_nonneg_right hw hp)
-- The four oriented triples (135), -(146), -(236), -(245) give two incidences per axis.
theorem rr_diagonal (a b c d e f : ℝ) :
 2*(a+b+c+d+e+f)-((a+c+e)+(a+d+f)+(b+c+f)+(b+d+e))=0 := by ring
theorem rectangle_product (a b c d e f : ℝ) :
 (a*c*e)*(a*d*f)*(b*c*f)*(b*d*e)=(a*b*c*d*e*f)^2 := by ring
theorem four_amgm (a b c d : ℝ) (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d) :
 4*real.sqrt (real.sqrt ((a*b)*(c*d)))≤a+b+c+d :=
begin
 have pair : ∀ x y : ℝ, 0≤x → 0≤y → 2*real.sqrt (x*y)≤x+y,
 { intros x y hx hy, rw [real.sqrt_mul hx],
   nlinarith only [sq_nonneg (real.sqrt x-real.sqrt y),real.sq_sqrt hx,real.sq_sqrt hy] },
 have p := pair a b ha hb, have q := pair c d hc hd,
 have r := pair _ _ (real.sqrt_nonneg (a*b)) (real.sqrt_nonneg (c*d)),
 rw [←real.sqrt_mul (mul_nonneg ha hb)] at r, linarith only [p,q,r]
end
theorem threshold_identity (h t b : ℝ) (unit : h^2+b^2=1) :
 (1+t^2)-(b-t*h)^2=(h+t*b)^2 :=
calc (1+t^2)-(b-t*h)^2 = (h+t*b)^2+(1+t^2)*(1-(h^2+b^2)) : by ring
 ... = (h+t*b)^2 : by {rw [unit],ring}
theorem separated_well (e m y r : ℝ) (hy : y≠0) (eq : e=m*r^2) :
 e/y+m*y-2*m*r=m*(y-r)^2/y := by {rw [eq],field_simp [hy],ring}
theorem composition_denominator (e t u : ℝ) :
 (2+e+t+4*e*t)-(2+e+u+4*e*u)=(1+4*e)*(t-u) := by ring
theorem two_materials (a b c d y cap : ℝ)
 (h1 : |a*y+b|≤cap) (h2 : |c*y+d|≤cap) :
 |c*b-a*d|≤(|c|+|a|)*cap :=
begin
 have eq : c*b-a*d=c*(a*y+b)-a*(c*y+d) := by ring,
 rw [eq,add_mul], refine le_trans (abs_sub _ _) _,
 rw [abs_mul,abs_mul], exact add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
   (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
end
def triples : fin 4 → finset ℕ := ![({1,3,5}:finset ℕ), {1,4,6}, {2,3,6}, {2,4,5}]
theorem rr_off_diagonal (i j : fin 4) (h : i≠j) : ((triples i)∩(triples j)).card=1 :=
by { fin_cases i; fin_cases j; try {exact (h rfl).elim}; dec_trivial }
end cat_dyon_radius
