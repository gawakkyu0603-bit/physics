import tactic
import analysis.calculus.deriv.pow
import analysis.calculus.deriv.add
import analysis.calculus.deriv.inv
import analysis.inner_product_space.basic
import analysis.special_functions.trigonometric.basic

noncomputable theory
open_locale big_operators
namespace cat_receiver_stability

-- Hessian on the divergence-free circular extremum. p is the transverse separation.
theorem extremal_force (a p j w J v : ℝ) :
 (a^2+p^2+j*w^2+J*v^2)-2*(j*w^2+J*v^2) =
 a^2+p^2-j*w^2-J*v^2 := by ring

theorem opposite_multiplicity (j w : ℝ) :
 j*w^2+(j-1)*(-w)^2=(2*j-1)*w^2 := by ring

theorem horizontal_correction {R : Type*} [ring R] (k a : R) :
 k+(4:ℕ) • a-a=k+(3:ℕ) • a := by { simp [succ_nsmul], abel }

theorem link_energy_derivative (u m p dx db : ℝ) :
 has_deriv_at (λ x:ℝ, ((x^2-m^2)^2+(p^2-x^2)^2)/8 +
                         (dx^2+db^2)*x^2/2)
 (u*(dx^2+db^2+u^2-(m^2+p^2)/2)) u :=
begin
 have h₁ := has_deriv_at.div_const (has_deriv_at_pow 4 u) (4:ℝ),
 have h₂ := has_deriv_at.const_mul ((dx^2+db^2)/2-(m^2+p^2)/4) (has_deriv_at_pow 2 u),
 have h := has_deriv_at.add (has_deriv_at.add h₁ h₂) (has_deriv_at_const u ((m^4+p^4)/8)),
 convert h using 1; try {ext t}; norm_num; ring
end

theorem coordinate_flux (l r zl z zr : ℝ) :
 has_deriv_at (λ x:ℝ, l^2*(x-zl)^2/2+r^2*(zr-x)^2/2)
 (l^2*(z-zl)-r^2*(zr-z)) z :=
begin
 have h₁ := has_deriv_at.const_mul ((l^2+r^2)/2) (has_deriv_at_pow 2 z),
 have h₂ := has_deriv_at.const_mul (-l^2*zl-r^2*zr) (has_deriv_at_id z),
 have h := has_deriv_at.add (has_deriv_at.add h₁ h₂) (has_deriv_at_const z ((l^2*zl^2+r^2*zr^2)/2)),
 convert h using 1; try {ext t}; simp [id]; ring
end

-- Canonical two-time commutator; the central scalar can be taken as i*g₁².
theorem seam_commutator {R : Type*} [ring R] (x v : R) (a b : R)
 (ha : x*a=a*x) (hb : x*b=b*x) :
 x*(a*x+b*v)-(a*x+b*v)*x=b*(x*v-v*x) :=
by { rw [mul_add,add_mul,←mul_assoc x a x,←mul_assoc x b v,ha,hb], noncomm_ring }

theorem radial_uncertainty (x y X Y c : ℝ)
 (hx : c/2≤x*X) (hy : c/2≤y*Y) :
 c≤x*X+y*Y := by linarith

theorem rms_product (x y X Y u v c : ℝ) (hu : 0≤u) (hv : 0≤v)
 (first : x^2+y^2≤u^2) (last : X^2+Y^2≤v^2)
 (one : c/2≤x*X) (two : c/2≤y*Y) : c≤u*v :=
begin
 have hsq : (x*X+y*Y)^2≤(x^2+y^2)*(X^2+Y^2) := by nlinarith only [sq_nonneg (x*Y-y*X)],
 have hn : 0≤X^2+Y^2 := add_nonneg (sq_nonneg X) (sq_nonneg Y),
 have h := le_trans hsq (mul_le_mul first last hn (sq_nonneg u)),
 have uv := mul_nonneg hu hv,
 have result : x*X+y*Y≤u*v :=
 begin
   by_contra hnot, have lt : u*v<x*X+y*Y := lt_of_not_ge hnot,
   have hp := mul_pos (sub_pos.mpr lt) (show 0<x*X+y*Y+u*v,by linarith only [uv,lt]),
   nlinarith only [h,hp]
 end,
 exact le_trans (radial_uncertainty x y X Y c one two) result
end

theorem simultaneous_smallness (R S r s c : ℝ) (hr : 0≤r) (hS : 0≤S)
 (h : c≤R*S) (big : r*s<c) : ¬(R≤r ∧ S≤s) :=
begin rintro ⟨h₁,h₂⟩, exact (not_lt_of_ge (le_trans h (mul_le_mul h₁ h₂ hS hr))) big end

-- At the unit crossing every interior Pauli doublet is at least one radius away.
theorem interior_gap (l m : ℝ) (hl : 1≤l) (hm : -l+1/2≤m) :
 (3/2:ℝ)^2≤(l+1/2)^2+2*m+1 :=
begin
 calc (3/2:ℝ)^2 ≤ (3/2:ℝ)^2+l*(l-1)+2*(m-(-l+1/2)) :
    le_trans (le_add_of_nonneg_right (mul_nonneg (show 0≤l,by linarith) (sub_nonneg.mpr hl)))
             (le_add_of_nonneg_right (mul_nonneg (by norm_num) (sub_nonneg.mpr hm)))
 ... = (l+1/2)^2+2*m+1 : by ring
end

theorem only_lowest_extreme (l : ℝ) : l-1=0 ↔ l=1 := sub_eq_zero

theorem angular_lower (l w d x : ℝ) :
 w^2*l*(l+1)+d^2+x^2-2*w*d*l-2*w^2*l =
 x^2-w*d-w^2/4+(w*l-d-w/2)^2 := by ring

theorem protected_square (l w d x : ℝ) (gap : w*d+w^2/4<x^2) :
 0<w^2*l*(l+1)+d^2+x^2-2*w*d*l-2*w^2*l :=
by { rw [angular_lower], nlinarith [sq_nonneg (w*l-d-w/2)] }

theorem wide_preparation (u : ℝ) (pu : 0≤u) :
 0<(2*u+2-(7/4:ℝ))^2-2*(2*u^2-1) ∧ 0<(2*u+2)^2-4*u^2 :=
begin
 have a : (2*u+2-(7/4:ℝ))^2-2*(2*u^2-1)=u+33/16 := by ring,
 have b : (2*u+2)^2-4*u^2=8*u+4 := by ring,
 rw [a,b],
 exact ⟨add_pos_of_nonneg_of_pos pu (by norm_num),
        add_pos_of_nonneg_of_pos (mul_nonneg (by norm_num) pu) (by norm_num)⟩
end

theorem left_guard_before_contact (d w : ℝ) (hw : 0≤w) (high : w≤1)
 (hd : d≤8/5) : 6/5 < (7/4:ℝ)^2-w*d-w^2/4 :=
begin
 have p : w*d≤8/5 :=
  calc w*d ≤ w*(8/5) : mul_le_mul_of_nonneg_left hd hw
       ... ≤ 1*(8/5) : mul_le_mul_of_nonneg_right high (by norm_num)
       ... = 8/5 : one_mul _,
 have f : w^2≤1 := by simpa only [one_pow] using (pow_le_pow_of_le_left hw high 2),
 have q : w^2/4≤1/4 := div_le_div_of_le (by norm_num : (0:ℝ)≤4) f,
 exact lt_of_lt_of_le (by norm_num : (6/5:ℝ)<(7/4:ℝ)^2-8/5-1/4)
   (sub_le_sub (sub_le_sub_left p _) q)
end

theorem coherent_windows (p q : ℂ) :
 (star (p+q)*(p+q)).re=(star p*p).re+(star q*q).re+2*(star p*q).re :=
begin
 change (p.re+q.re)*(p.re+q.re)-(-(p.im+q.im))*(p.im+q.im) =
  (p.re*p.re-(-p.im)*p.im)+(q.re*q.re-(-q.im)*q.im)+2*(p.re*q.re-(-p.im)*q.im),
 ring
end

theorem static_dressing (v phase : ℂ) :
 v-v*(1-phase)=v*phase := by ring

-- F and V are the squared displacement and velocity of a complex free oscillator.
theorem oscillator_energy_at {t flux dw : ℝ} {F V w : ℝ → ℝ}
 (hf : has_deriv_at F flux t) (hv : has_deriv_at V (-(w t)^2*flux) t)
 (hw : has_deriv_at w dw t) :
 has_deriv_at (λ x, V x+(w x)^2*F x) (2*w t*dw*F t) t :=
begin
 convert hv.add ((hw.pow 2).mul hf) using 1; try {ext x}; simp; ring
end

theorem scaled_oscillator_energy_at {t flux dw : ℝ} {F V w : ℝ → ℝ}
 (hf : has_deriv_at F flux t) (hv : has_deriv_at V (-(w t)^2*flux) t)
 (hw : has_deriv_at w dw t) (nz : w t ≠ 0) :
 has_deriv_at (λ x, (V x+(w x)^2*F x)/(w x)^2) (-2*dw*V t/(w t)^3) t :=
begin
 have h := (oscillator_energy_at hf hv hw).div (hw.pow 2) (pow_ne_zero 2 nz),
 convert h using 1; try {ext x}; simp; field_simp [nz]; ring
end

theorem copy_guard (l w d x : ℝ) (harmonic : l=1 ∨ 2≤l) (hw : 0≤w) (hd : d≤w)
 (hg : 0≤x^2+d^2-2*w*d) :
 0≤x^2+(l*w-d)^2-l*w^2 :=
begin
 rcases harmonic with h | ht,
 { rw [h], nlinarith },
 have hh : 0≤l*w-2*d := by nlinarith [mul_nonneg hw (sub_nonneg.mpr ht)],
 have id : x^2+(l*w-d)^2-l*w^2 =
  (x^2+d^2-2*w*d)+(l-1)*w*(l*w-2*d) := by ring,
 rw [id], exact add_nonneg hg (mul_nonneg (mul_nonneg (by linarith) hw) hh)
end

-- Norm error from any number of returns within the selected exchange channel.
theorem return_budget (A : ℝ) : has_deriv_at (λ x:ℝ, x^3/6) (A^2/2) A :=
by { convert (has_deriv_at_pow 3 A).div_const 6 using 1; norm_num; ring }

theorem exchange_interval (u v e : ℝ) (hu : 0≤u) (hv : 0≤v) (he : 0≤e)
 (diff : |v-u|≤e) : (max 0 (u-e))^2≤v^2 ∧ v^2≤(u+e)^2 :=
begin
 have h:=abs_le.mp diff,
 have low : max 0 (u-e)≤v := max_le hv (by linarith),
 exact ⟨pow_le_pow_of_le_left (le_max_left _ _) low 2,
        pow_le_pow_of_le_left hv (by linarith) 2⟩
end

def pair (x : ℝ) : ℝ := x+1/x
theorem pair_pos (x : ℝ) (p : 0<x) : 0<pair x := add_pos p (one_div_pos.mpr p)

theorem pair_mono {a b : ℝ} (ha : 1≤a) (hab : a≤b) : pair a≤pair b :=
begin
 have pa : 0<a := by linarith, have pb : 0<b := by linarith,
 have one : 1≤a*b := by nlinarith [mul_nonneg (sub_nonneg.mpr ha) pb.le],
 have h : pair b-pair a=(b-a)*(a*b-1)/(a*b) :=
  by { unfold pair, field_simp [ne_of_gt pa,ne_of_gt pb], ring },
 have hh : 0≤pair b-pair a := by {rw [h], exact div_nonneg (mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr one)) (mul_pos pa pb).le},
 exact sub_nonneg.mp hh
end

theorem pair_product (x y : ℝ) (px : 0<x) (py : 0<y) :
 pair x*pair y=pair (x*y)+pair (x/y) :=
by { unfold pair, field_simp [ne_of_gt px,ne_of_gt py], ring }

-- Weyl's top-one and top-two product inequalities imply the joint Gaussian ceiling,
-- even when the two incident packets are entangled.
theorem two_expansions (r q s t : ℝ)
 (hq : 1≤q) (hr : q≤r) (ht : 1≤t) (hs : t≤s)
 (one : r≤s) (two : r*q≤s*t) : pair r*pair q≤pair s*pair t :=
begin
 have pq : 0<q := lt_of_lt_of_le zero_lt_one hq,
 have pr : 0<r := lt_of_lt_of_le pq hr,
 have pt : 0<t := lt_of_lt_of_le zero_lt_one ht,
 have ps : 0<s := lt_of_lt_of_le pt hs,
 have rr : 1≤r := le_trans hq hr,
 have first : pair r≤pair s := pair_mono rr one,
 by_cases h : q≤t,
 { have second : pair q≤pair t := pair_mono hq h,
   exact mul_le_mul first second (le_of_lt (pair_pos q pq)) (le_of_lt (pair_pos s ps)) },
 have hp : 1≤r*q := one_le_mul_of_one_le_of_one_le rr hq,
 have tq : t≤q := (lt_of_not_ge h).le,
 have left : r*t≤r*q := mul_le_mul_of_nonneg_left tq pr.le,
 have right : r*q≤s*q := mul_le_mul_of_nonneg_right one pq.le,
 have ratio : r/q≤s/t := (div_le_div_iff pq pt).2 (le_trans left right),
 have unit : 1≤r/q := (le_div_iff pq).2 (by simpa only [one_mul] using hr),
 have add : pair (r*q)+pair (r/q)≤pair (s*t)+pair (s/t) :=
   add_le_add (pair_mono hp two) (pair_mono unit ratio),
 exact (pair_product r q pr pq).le.trans (add.trans (pair_product s t ps pt).symm.le)
end

theorem fidelity_ceiling (d r : ℝ) (pr : 0<r) (h : r≤d) :
 4/d≤4/r := div_le_div_of_le_left (show (0:ℝ)≤4,by norm_num) pr h

-- Detection at one of finitely many apertures on one output, using supplied
-- upper and lower one-variable probability bounds.
theorem aperture_telescope (F : ℕ → ℝ) (n : ℕ) :
 ∑ i in finset.range n, (F i-F (i+1))=F 0-F n :=
by { induction n with n ih, {simp}, {rw [finset.sum_range_succ,ih], ring} }

theorem one_aperture (F : ℕ → ℝ) (n : ℕ) (d : ℝ) (hn : 0<n)
 (gap : (n:ℝ)*d≤F 0-F n) :
 ∃ i∈finset.range n, d≤F i-F (i+1) :=
begin
 classical, by_contra h, push_neg at h,
 have lt : ∑ i in finset.range n,(F i-F (i+1)) < ∑ i in finset.range n,d :=
 finset.sum_lt_sum (λ i hi, (h i hi).le) ⟨0,finset.mem_range.mpr hn,h 0 (finset.mem_range.mpr hn)⟩,
 rw [aperture_telescope] at lt, simp at lt, linarith
end

theorem aperture_gap (p q tail small : ℝ)
 (large : 1-tail≤p) (near : q≤small) : 1-tail-small≤p-q := by linarith

theorem optimized_losses (A B a z : ℝ) (pa : 0<a) (pz : 0<z)
 (opt : A*z=a^3*B) : A/a^2+2*a*B/z=3*A/a^2 :=
begin
 have id : a*B/z=A/a^2 := (div_eq_div_iff (ne_of_gt pz) (ne_of_gt (pow_pos pa 2))).2
   (by nlinarith only [opt]),
 calc A/a^2+2*a*B/z=A/a^2+2*(a*B/z) : by ring
 ... = 3*A/a^2 : by {rw [id], ring}
end

theorem shifted_train (a : ℕ → ℝ) (n : ℕ) :
 ∑ i in finset.range n, a (i+1)*a i = ∑ i in finset.range n,a i*a (i+1) :=
by { apply finset.sum_congr rfl, intros, ring }

theorem sine_recurrence (t s : ℝ) :
 real.sin (t-s)+real.sin (t+s)=2*real.cos s*real.sin t :=
by {rw [real.sin_sub,real.sin_add],ring}

theorem coherent_train (a : ℕ → ℝ) (n : ℕ) (c : ℝ)
 (first : a 0=0) (last : a (n+1)=0)
 (norm : (∑ i in finset.range n, (a (i+1))^2)=1)
 (rec : ∀ i∈finset.range n, a i+a (i+2)=2*c*a (i+1)) :
 (∑ i in finset.range n, a i*a (i+1))=c :=
begin
 have tel := aperture_telescope (λ i, a i*a (i+1)) n,
 dsimp at tel,
 rw [finset.sum_sub_distrib,first,last,zero_mul,mul_zero,sub_zero] at tel,
 have comb : (∑ i in finset.range n,(a i*a (i+1)+a (i+1)*a (i+2)))=
    ∑ i in finset.range n,2*c*(a (i+1))^2 :=
 begin
   apply finset.sum_congr rfl, intros i hi,
   linear_combination a (i+1)*(rec i hi)
 end,
 rw [finset.sum_add_distrib,←finset.mul_sum,norm,mul_one] at comb,
 linarith
end

end cat_receiver_stability
