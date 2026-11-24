import tactic
import analysis.special_functions.trigonometric.basic
import analysis.inner_product_space.basic

noncomputable theory
open_locale big_operators
namespace cat_colliding_fronts

-- Intertwining a conserved signed null momentum across a quadratic evolution.
theorem no_positive_negative_mixing (k l : ℝ) (b : ℂ) (hk : 0<k) (hl : 0<l)
 (commutes : ((k+l : ℝ) : ℂ)*b=0) : b=0 :=
begin
 have hn : (k+l : ℝ)≠0 := ne_of_gt (add_pos hk hl),
 have hc : ((k+l : ℝ):ℂ)≠0 := by exact_mod_cast hn,
 exact (mul_eq_zero.mp commutes).resolve_left hc
end

theorem oriented_neutral_pair (n m : ℤ) (pair : n=m) : n-m=0 := sub_eq_zero.mpr pair

theorem common_profile {R : Type*} [ring R] (f a z : R) (h : f*a=a*f) :
 f*(a*z)-(a*z)*f=a*(f*z-z*f) :=
by {rw [←mul_assoc,h,mul_assoc],noncomm_ring}

-- M is the positive *squared* asymptotic mass, a and b are the signed shifts.
theorem rectified_mass (M a b c : ℝ) (hM : 0<M) :
 (M+a^2+b^2+2*c*a*b)/((1+a^2/M)*(1+b^2/M)) =
 M+(2*c*a*b-a^2*b^2/M)/((1+a^2/M)*(1+b^2/M)) :=
begin
 have ha : 0<1+a^2/M := add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg (sq_nonneg a) hM.le),
 have hb : 0<1+b^2/M := add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg (sq_nonneg b) hM.le),
 have hn := ne_of_gt (mul_pos ha hb),
 apply (div_eq_iff hn).2, rw [add_mul,div_mul_cancel _ hn],
 field_simp [ne_of_gt hM]; ring
end

theorem mass_never_imaginary (M a b c : ℝ) (hc : c^2≤1) :
 M≤M+a^2+b^2+2*c*a*b :=
begin
 have h := add_nonneg (sq_nonneg (a+c*b)) (mul_nonneg (sub_nonneg.mpr hc) (sq_nonneg b)),
 nlinarith only [h]
end

theorem straightened_null_kernel (fu gv q C : ℝ) (hf : fu≠0) (hg : gv≠0) :
 4*(fu*gv*q)+C=0 ↔ 4*q+C/(fu*gv)=0 :=
begin
 have h := mul_ne_zero hf hg,
 split; intro a,
 { field_simp [h]; nlinarith only [a] },
 { field_simp [h] at a; nlinarith only [a] }
end

theorem ordered_double_bound (a : ℕ → ℝ) (L : ℝ) (lp : 0≤L)
 (base : a 0≤1)
 (step : ∀ n : ℕ, a (n+1)*((n+1:ℕ):ℝ)^2≤L*a n) :
 ∀ n : ℕ, a n*(n.factorial:ℝ)^2≤L^n :=
begin
 intro n, induction n with n ih,
 {simpa using base},
 rw [nat.factorial_succ,nat.cast_mul,mul_pow,pow_succ L n],
 calc a (n+1)*(((n+1:ℕ):ℝ)^2*(n.factorial:ℝ)^2) =
        (a (n+1)*((n+1:ℕ):ℝ)^2)*(n.factorial:ℝ)^2 : by ring
 ... ≤ (L*a n)*(n.factorial:ℝ)^2 : mul_le_mul_of_nonneg_right (step n) (sq_nonneg _)
 ... = L*(a n*(n.factorial:ℝ)^2) : by ring
 ... ≤ L*L^n : mul_le_mul_of_nonneg_left ih lp
end

theorem positive_retarded_iterates {ι : Type*} (g : ι → ℝ) (T : (ι → ℝ) → ι → ℝ)
 (v : ℕ → ι → ℝ) (hg : ∀ x, 0≤g x)
 (pos : ∀ f : ι → ℝ, (∀ x,0≤f x) → ∀ x, 0≤T f x)
 (base : v 0=g) (step : ∀ n x, v (n+1) x=g x+T (v n) x) :
 ∀ n x, g x≤v n x :=
begin
 intro n, induction n with n ih,
 { intro x, rw [base] },
 intro x, rw [step],
 exact le_add_of_nonneg_right (pos _ (λ y, le_trans (hg y) (ih y)) x)
end

theorem pair_packet_component (first actual e : ℝ) (h : |actual-first|≤e)
 (large : e<first) : 0<actual :=
begin have b:=abs_le.mp h, linarith end

theorem charged_mode_nonempty (n b : ℝ) (hb : 0≤b) (hn : b≤n) :
 b/(1+b)≤n/(1+n) :=
begin
 have bp : 0<1+b := by linarith, have np : 0<1+n := by linarith,
 apply (div_le_div_iff bp np).2, nlinarith only [hn]
end

-- Input is the normalized, smeared scattering estimate, M=1/16 is the packet width.
-- The constants are deliberately rounded outwards. This includes the probability
-- conversion for all occupations of the charged Gaussian output mode.
theorem reference_packet_probability (amp mean prob : ℝ)
 (packet : (31/2000:ℝ)*(1/16)/(8*(22/7)*(7/25))*
   ((1-(43/250:ℝ)^2/2)^2-4/1000) ≤ amp)
 (occupation : amp^2≤mean) (gaussian : prob=mean/(1+mean)) :
 (176/10000000000:ℝ) ≤ prob :=
begin
 have lo : (133/1000000:ℝ) ≤ amp := le_trans (by norm_num) packet,
 have sq : (133/1000000:ℝ)^2 ≤ amp^2 := pow_le_pow_of_le_left (by norm_num) lo 2,
 have nonempty := charged_mode_nonempty mean ((133/1000000:ℝ)^2)
   (sq_nonneg _) (le_trans sq occupation),
 rw [gaussian], exact le_trans (by norm_num) nonempty
end

-- On L² the translated profile difference is the pairing of its derivative
-- with the signed indicator of the segment cut by the compact derivative support.
theorem shifted_profile_energy {F : Type*} [normed_add_comm_group F] [inner_product_space ℝ F]
 (interval gradient : F) (L : ℝ) (cut : ‖interval‖^2≤2*L) :
 (inner interval gradient : ℝ)^2≤2*L*‖gradient‖^2 :=
begin
 have cs := pow_le_pow_of_le_left (abs_nonneg (inner interval gradient : ℝ))
    (abs_real_inner_le_norm interval gradient) 2,
 have bound : (inner interval gradient : ℝ)^2 ≤ ‖interval‖^2*‖gradient‖^2 :=
    by simpa only [sq_abs,mul_pow] using cs,
 exact le_trans bound (mul_le_mul_of_nonneg_right cut (sq_nonneg _))
end

theorem fixed_energy_fluence (L E d f support fluence : ℝ)
 (hL : 0≤L) (hE : 0≤E) (h : f^2≤2*L*E) (nonneg : 0≤support)
 (length : support≤d+2*L) (integrated : fluence≤f^2*support) :
 fluence≤2*L*E*(d+2*L) :=
begin
 exact le_trans integrated (mul_le_mul h length nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hL) hE))
end

theorem fixed_energy_collision (L ef eg F G dx dy M : ℝ) (p : 0<M)
 (hf : 0≤F) (hg : 0≤G)
 (af : F≤2*L*ef*(dx+2*L)) (ag : G≤2*L*eg*(dy+2*L)) :
 F*G/M ≤ L^2*(4*ef*eg*(dx+2*L)*(dy+2*L))/M :=
begin
 apply div_le_div_of_le p.le,
 calc F*G≤(2*L*ef*(dx+2*L))*(2*L*eg*(dy+2*L)) :
  mul_le_mul af ag hg (le_trans hf af)
 ... = L^2*(4*ef*eg*(dx+2*L)*(dy+2*L)) : by ring
end

theorem finite_energy_packet_weight (amp C S L D : ℝ) (abs_amp : 0≤amp)
 (c : 0≤C) (packet : amp≤C*S) (energy : S≤L^2*D) :
 amp^2≤L^4*(C*D)^2 :=
begin
 have bound := le_trans packet (mul_le_mul_of_nonneg_left energy c),
 calc amp^2≤(C*(L^2*D))^2 : pow_le_pow_of_le_left abs_amp bound 2
 ... = L^4*(C*D)^2 : by ring
end

theorem finite_energy_oblique_weight (amp S L C D D2 : ℝ)
 (a : 0≤amp) (c : 0≤C) (packet : amp≤C*S) (bounded : S≤L*D+L^2*D2) :
 amp^2≤L^2*(C*(D+L*D2))^2 :=
begin
 have bound := le_trans packet (mul_le_mul_of_nonneg_left bounded c),
 calc amp^2≤(C*(L*D+L^2*D2))^2 : pow_le_pow_of_le_left a bound 2
 ... = L^2*(C*(D+L*D2))^2 : by ring
end

theorem displaced_step_cancellation (a M : ℝ) (h : M≠0) :
 2*(a^2/(2*M))*a*a-(a*a)^2/M=0 := by {field_simp [h]; ring}

theorem step_packet_scaling (amp S L c C d D : ℝ) (p : 0≤L) (q : 0≤c) (r : 0≤C)
 (ds : 0≤d) (hlo : L*d≤S) (hhi : S≤L*D) (blo : c*S≤amp) (bhi : amp≤C*S) :
 L^2*(c*d)^2≤amp^2 ∧ amp^2≤L^2*(C*D)^2 :=
begin
 have low := le_trans (mul_le_mul_of_nonneg_left hlo q) blo,
 have high := le_trans bhi (mul_le_mul_of_nonneg_left hhi r),
 have nonneg := mul_nonneg q (mul_nonneg p ds),
 split,
 { calc L^2*(c*d)^2=(c*(L*d))^2 : by ring
    ... ≤ amp^2 : pow_le_pow_of_le_left nonneg low 2 },
 { calc amp^2≤(C*(L*D))^2 : pow_le_pow_of_le_left (le_trans nonneg low) high 2
    ... = L^2*(C*D)^2 : by ring }
end

theorem covariance_force_lower (J Y variance cross S c : ℝ)
 (v : 0≤variance) (jc : c≤J*Y) (s : 0≤S)
 (a : S*(J*Y)/8≤cross) : S*c/8≤cross+variance :=
begin have b := mul_le_mul_of_nonneg_left jc s, linarith end

theorem double_smearing_error (cross d M gamma e data : ℝ)
 (hd : gamma^2*d≤data)
 (h : |cross-data|≤M*(2*gamma*e+e^2)) :
 gamma^2*d-M*(2*gamma*e+e^2)≤cross :=
begin have b := abs_le.mp h, linarith end

-- Finite shifts transfer energy and momentum across a spatial bond.
theorem local_bond (f fp fm s sp sm : ℝ) :
 f*(sp-sm)+s*(fp-fm)=(f*sp+s*fp)-(fm*s+sm*f) := by ring

theorem cancel_opposite_forces (a b n : ℝ) : -2*(a-b)*n+-2*(b-a)*n=0 := by ring

theorem width_bound (A f : ℝ) (lo : 0≤f) (hi : f≤A) : f^2≤A*f :=
by {simpa [pow_two] using mul_le_mul_of_nonneg_right hi lo}

theorem displaced_bumps (l r : ℝ) (disjoint : l*r=0) : (l-r)^2=l^2+r^2 :=
by nlinarith only [disjoint]

theorem optical_trace (a b : ℝ) : ((a+b^2)+(-a+b^2))/2=b^2 := by ring

theorem edge_scale (x C : ℝ) : ((C*x^4)^2)/27=(C^2/27)*x^8 := by ring

theorem static_threshold_dark (EL ER M s : ℝ) (pL : 0<EL) (pR : 0<ER)
 (mass : (EL+ER)^2-M^2=4*EL*ER*s) (threshold : M=EL+ER) : s=0 :=
begin
 rw [threshold,sub_self] at mass,
 have p : 0<4*EL*ER := mul_pos (mul_pos (by norm_num) pL) pR,
 exact (mul_eq_zero.mp mass.symm).resolve_left (ne_of_gt p)
end

theorem wall_excursion (j w W : ℝ) (hj : 0<j) (greater : w<W) :
 0<j*W-j*w := sub_pos.mpr (mul_lt_mul_of_pos_left greater hj)

theorem only_left_enters (x delta : ℝ) (h : x<delta) : x-delta<0 := sub_neg.mpr h

-- With x=j^(1/10) and d=b/x^6 the clock and energy requirements can be
-- compared directly, without replacing a finite crossing by an infinite time.
theorem grazing_scales (x b : ℝ) (hx : x≠0) :
 x^5*(b/x^6)=b/x ∧ x^10*(b/x^6)^2=b^2/x^2 ∧
 (x^10)^2*(b/x^6)^3=b^3*x^2 ∧ (x^10*(b/x^6))^2/x^5=b^2*x^3 :=
by {refine ⟨_,_,_,_⟩; field_simp [hx]; ring}

theorem clock_and_resolution (a : ℝ) (lo : 1/2<a) (hi : a<2/3) :
 0<a-1/2 ∧ 0<2-3*a ∧ 0<3/2-2*a := by {refine ⟨_,_,_⟩; linarith}

theorem conditional_reflection (mu floor v amp diff inv : ℝ)
 (p : 0<floor) (q : 0≤amp) (f : 0≤inv)
 (gap : diff≤mu*v/floor) (inv_bound : inv≤1/(2*floor)) (h : 0≤mu*v/floor) :
 inv*diff*amp≤mu*v*amp/(2*floor^2) :=
begin
 calc inv*diff*amp≤inv*(mu*v/floor)*amp :
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left gap f) q
 ... ≤ (1/(2*floor))*(mu*v/floor)*amp :
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right inv_bound h) q
 ... = mu*v*amp/(2*floor^2) : by { field_simp [ne_of_gt p]; ring_nf; simp }
end

end cat_colliding_fronts
