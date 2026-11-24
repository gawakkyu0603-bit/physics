import tactic
import analysis.special_functions.exp
import analysis.special_functions.integrals
import analysis.special_functions.arsinh

noncomputable theory
open_locale interval
open measure_theory
namespace material_dipole_surface

-- Two real quadratures may be added after each real energy identity.
theorem material_work (q y dy d l c : ℝ) (force : l*dy= -(y+c*q+d)) :
  l*y*dy+c*q*y= -y*(y+d) := by linear_combination y*force

theorem positive_near (q h : ℝ) :
  0≤q^2-q*h+h^2/2 := by nlinarith [sq_nonneg (q-h),sq_nonneg q]

theorem substrate_radius (r n e : ℝ) (hr : 0<r) (he : 0<e)
  (h : n/r≤e) : n/e≤r := (div_le_iff he).2 (by nlinarith [(div_le_iff hr).1 h])

def boost (z : ℝ) := (1/z+z)/2
def velocity (z : ℝ) := (1/z-z)/2

theorem field_normal (z : ℝ) (hz : z≠0) :
  boost z-velocity z=z ∧ (boost z+velocity z)*z=1 :=
by {dsimp [boost,velocity],split;field_simp [hz];ring}

theorem lab_energy_derivative (q y d e z : ℝ) (hz : z≠0) :
 let b:=boost z,v:=velocity z,h:=z*d,
     pressure:=((y+d)^2+y^2)/2-q^2,
     far:=y-z*q+b*h in
 v*(b*e-pressure)+b*(-y*(y+d)-v*e)+(2*q-h)*y+
 (h-q)*(z*q-b*h)-v*(q^2-q*h+h^2/2)+far^2/z=0 :=
by {dsimp [boost,velocity],field_simp [hz],ring}

def symp (a b c d : ℝ) := a*d-b*c

theorem symplectic_flux (q r y u d f c z : ℝ) (hz : z≠0) :
 let b:=boost z,h:=z*d,i:=z*f in
 symp q r (-(y+c*q+d)) (-(u+c*r+f))+
 symp (z*q-b*h) (z*r-b*i) q r+symp h i y u+
 symp (q-h) (r-i) (y-z*q+b*h) (u-z*r+b*i)=0 :=
by {dsimp [symp,boost],field_simp [hz],ring}

theorem general_shape_damping (l c b : ℝ) :
  (l*b+1)*(b+c)-l*(b*c+1)=b+c+l*(b^2-1) := by ring

theorem cubic_stable_margin (l c b : ℝ) (hl : 0<l) (hc : 0<c)
  (hb : 1≤b) : 0<(l*b+1)*(b+c)-l*(b*c+1) :=
begin rw [general_shape_damping],nlinarith [mul_nonneg (le_of_lt hl)
 (show 0≤b^2-1,by nlinarith [sq_nonneg (b-1)])] end

-- Elimination between the imaginary wave equation and normal pressure.
theorem oscillatory_inertia (l k t : ℝ) (hk : 0<k) (ht : 0<t)
 (impart : (2*k*l-1)*t+1=0) :
 l=(t-1)/(t*(2*k)) :=
by {apply (eq_div_iff (ne_of_gt (mul_pos ht (show 0<2*k,by linarith)))).2, nlinarith}

theorem shape_time_positive (l k t : ℝ) (hl : 0<l) (hk : 0<k) (ht : 0<t)
 (impart : (2*k*l-1)*t+1=0) : 1<t :=
by nlinarith [mul_pos (mul_pos hk hl) ht]

theorem decay_offset (k b energy t : ℝ) (he : 0<energy) (ht : 1<t)
 (balance : (2*k-b)*energy*t=2*t-1) : 0<2*k-b :=
begin
 by_contra hn, have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn)
   (le_of_lt (mul_pos he (by linarith : 0<t))),
 nlinarith [hm]
end

theorem shape_offset_lt_one (d f b : ℝ) (hd : 0<d) (hf : 0<f) (hb : 1≤b)
 (eqn : 2*d*f^2=(1-d^2)*(d+b*(1+2*f))) : d<1 :=
begin
 have pos : 0<2*d*f^2 := mul_pos (mul_pos (by norm_num) hd) (pow_pos hf 2),
 rw [eqn] at pos,
 have right : 0<d+b*(1+2*f) :=
   add_pos hd (mul_pos (lt_of_lt_of_le zero_lt_one hb)
     (add_pos zero_lt_one (mul_pos (by norm_num) hf))),
 have g := pos_of_mul_pos_left pos (le_of_lt right),
 by_contra h,
 have u : 1≤d := le_of_not_gt h,
 have sq := mul_le_mul u u zero_le_one (le_of_lt hd),
 nlinarith only [g,sq]
end

theorem shape_elimination (b d f e : ℝ)
 (ew : ((b+d)/2)*e*(1+f)=(f+b*d)*(1+f)-d*(b-(b+d)/2))
 (ep : d*e*(1+f)=2*(1+f)-1) :
 2*d*f^2=(1-d^2)*(d+b*(1+2*f)) :=
by linear_combination -2*d*ew+(b+d)*ep

theorem small_offset_bound (b d f : ℝ) (hb : 0<b) (hd : 0<d)
 (hf : 0<f) (dp : d<1)
 (eqn : 2*d*f^2=(1-d^2)*(d+b*(1+2*f))) : b*(1-d^2)<d*f :=
begin
 have hprod := mul_pos (sub_pos.mpr dp) (add_pos zero_lt_one hd),
 have gpos : 0<1-d^2 := by nlinarith only [hprod],
 have pos := mul_pos gpos (add_pos hd hb),
 have id : 2*((d*f-b*(1-d^2))*f)=(1-d^2)*(d+b) :=
   by linear_combination eqn,
 rw [←id] at pos,
 exact sub_pos.mp (pos_of_mul_pos_left (pos_of_mul_pos_right pos (by norm_num)) (le_of_lt hf))
end

theorem half_offset_bound (b d f : ℝ) (hb : 1≤b) (hd : 0<d) (fl : f<1)
 (small : b*(1-d^2)<d*f) : 1/2<d :=
begin
 by_contra hn,have dl : d≤1/2 := le_of_not_gt hn,
 have sq := mul_le_mul dl dl (le_of_lt hd) (by norm_num : (0:ℝ)≤1/2),
 have gp : 0≤1-d^2 := by nlinarith only [sq],
 have c := mul_le_mul_of_nonneg_right hb gp,
 have a := mul_lt_mul_of_pos_left fl hd,
 rw [one_mul] at c,rw [mul_one] at a,
 have upper := (lt_trans small a),
 have lower := lt_of_le_of_lt c upper,
 nlinarith only [sq,dl,lower]
end

theorem compression_gap (b d f : ℝ) (hb : 1≤b) (hd : 0<d) (hf : 0<f)
 (eqn : 2*d*f^2=(1-d^2)*(d+b*(1+2*f))) :
 2<1+f+b*d+(b+d)*d/f :=
begin
 have bp := lt_of_lt_of_le zero_lt_one hb,
 have bd := mul_le_mul_of_nonneg_right hb (le_of_lt hd),
 rw [one_mul] at bd,
 by_cases h : 1≤f,
 {have p1 := mul_pos bp hd,
  have p2 := div_pos (mul_pos (add_pos bp hd) hd) hf,linarith only [h,p1,p2]},
 have fl : f<1 := lt_of_not_ge h,
 have dp := shape_offset_lt_one d f b hd hf hb eqn,
 have dh := half_offset_bound b d f hb hd fl (small_offset_bound b d f bp hd hf dp eqn),
 have step : d*f < (b+d)*d :=
    calc d*f < d*1 : mul_lt_mul_of_pos_left fl hd
         ... = 1*d : mul_comm _ _
         ... < (b+d)*d : mul_lt_mul_of_pos_right (by linarith only [hd,hb]) hd,
 have last := (lt_div_iff hf).2 step,
 linarith only [last,dh,bd,hf]
end

theorem real_mode_compactness (v k h r : ℝ) (hr : 1<r) (hh : h≠0)
 (rel : v^2-k^2=2*r+1/h^2-1) : k^2<v^2 :=
by linarith only [rel,hr,div_nonneg (show (0:ℝ)≤1,by norm_num) (sq_nonneg h)]

-- Independent exact certificate at the rational example. Real/imag coordinates
-- use Q=1, Y=-k+i*nu, D=(b-k-i*nu)/t.
theorem witness_equations :
 let b:ℚ:=11139/10880,k:ℚ:=17667/21760,n:ℚ:=1221669879/473497600,
     l:ℚ:=10880/28539,c:ℚ:=461/315,t:ℚ:=21/8,
     dr:=(b-k)/t,di:=-1/t in
 (b-k)^2+n=t ∧ l*(k^2-n)-k+c+dr=0 ∧ -2*l*k+1+di=0 ∧
 (-k+dr)^2+n*(1+di)^2+k^2+n-2=b*(l*(k^2+n)+c) ∧
 c/l=208833/54400 ∧ 4*(b^2-1)<k^2 :=
by norm_num

theorem stable_witness_signs :
 let p:ℚ:=8913279/4624000,q:ℚ:=48093748167/2959360000,
 r:ℚ:=9932155041592449/547363225600000,u:ℚ:=4468405404497859/171051008000000 in
 0<p ∧ 0<p*q-r ∧ 0<(p*q-r)*r-p^2*u ∧ 0<u :=
by norm_num

theorem milne_wave (S L x : ℝ) :
 -- W=s*coth(chi), W'=-L, L'=-2*W*L. Plane wave e^(ix*xi)(W-ix).
 (2*S*L-2*L*S=0) ∧ (-2*x*L+2*L*x=0) := by split;ring

theorem milne_impedance (x b : ℝ) (hn : b^2+x^2≠0) :
 (x-x/(b^2+x^2))*(b^2+x^2)=x*(b^2-1+x^2) :=
by {field_simp [hn],ring}

theorem continuum_positive (x b : ℝ) (hx : 0<x) (hb : 1≤b) :
 0<x*(b^2-1+x^2)/(b^2+x^2) :=
begin
 have h : 0≤b^2-1 := by nlinarith [sq_nonneg (b-1)],
 exact div_pos (mul_pos hx (by nlinarith [pow_pos hx 2]))
   (by nlinarith [pow_pos hx 2])
end

theorem pair_integrands (x t : ℝ) :
 x*(t*x)*((1-t)*x)=x^3*(t-t^2) ∧
 x*(t*x)^3*((1-t)*x)^3=x^7*(t^3-3*t^4+3*t^5-t^6) := by split;ring

theorem pair_end_factors :
 (1/2-1/3:ℝ)=1/6 ∧ (1/4-3/5+3/6-1/7:ℝ)=1/140 := by norm_num

theorem square_completion (e f a g : ℝ) (he : e≠0) :
 e*(f+g*a/e)^2=e*f^2+2*g*f*a+g^2*a^2/e :=
by {field_simp [he],ring}

theorem reciprocal_bound (x y : ℝ) (hx : 0<x) (hy : 0<y) :
 1/(x^2+y^2)≤1/(2*x*y) :=
begin
 have hp : 0<2*x*y := by nlinarith [mul_pos hx hy],
 have hs : 0<x^2+y^2 := by nlinarith [pow_pos hx 2,sq_nonneg y],
 exact (div_le_div_iff hs hp).2 (by nlinarith [sq_nonneg (x-y)])
end

theorem energy_population (e gap r p : ℝ) (hr : 0<r) (hg : 0<gap)
 (budget : gap*p/r≤e) : p≤(e/gap)*r :=
begin
 have h := (div_le_iff hr).1 budget,
 rw [div_mul_eq_mul_div],apply (le_div_iff hg).2,nlinarith
end

-- Khalfin/Facchi--Lonigro is the cited spectral input. This theorem
-- supplies the physical energy condition and the contradiction.
theorem coasting_charge_obstruction (p : ℝ→ℝ) (e gap r s : ℝ)
 (he : 0<e) (hg : 0<gap) (hr : 0<r) (hs : 0<s)
 (spectral_input : ∀ C>0, ∀ a>0, ∃ w:ℝ,0≤w ∧ C*real.exp(-a*w)<p w) :
 ¬ (∀ w:ℝ,0≤w → gap*p w/(r*real.exp(-s*w))≤e) :=
begin
 intro budget,
 rcases spectral_input ((e/gap)*r) (mul_pos (div_pos he hg) hr) s hs with ⟨w,hw,h⟩,
 have hb:=energy_population e gap _ (p w) (mul_pos hr (real.exp_pos _)) hg (budget w hw),
 rw [←mul_assoc] at hb, linarith
end

-- Well-defined junction energy m B-Gm²/(2R), x=Gm/R, eta=R m'/m.
theorem adm_stationary (x a : ℝ) (h : (2-3*a)*(1-x)+x/2=0)
 (hx : x<1) : a=(4-3*x)/(6*(1-x)) :=
by {apply (eq_div_iff (show 6*(1-x)≠0,by nlinarith)).2,nlinarith}

theorem tension_exists (x : ℝ) (hx : x<1) :
 (4-3*x)/(6*(1-x))<1 ↔ x<2/3 :=
by {rw [div_lt_iff (show 0<6*(1-x),by linarith)],split;intro h;linarith}

theorem adm_second_variation (x : ℝ) (hx : x≠1) :
 4*(1-x)^2*(2*(1-x)-x*((-x/(2*(1-x)))-1)^2)=
 8*(1-x)^3-x*(2-x)^2 :=
by {have hz : 1-x≠0:=sub_ne_zero.mpr (ne.symm hx),field_simp [hz],ring}

theorem stability_monotone (x : ℝ) (hx : 0≤x) (hu : x<2/3) :
 0<24*(1-x)^2+(2-x)*(2-3*x) :=
by nlinarith [mul_pos (show 0<2-x,by linarith) (show 0<2-3*x,by linarith),sq_nonneg (1-x)]

theorem stability_bracket :
 0<8*(1-(48/100:ℝ))^3-(48/100)*(2-48/100)^2 ∧
 8*(1-(49/100:ℝ))^3-(49/100)*(2-49/100)^2<0 := by norm_num

theorem release_factor (x y : ℝ) (hy : y≠0) :
 (1-x/2)*y+x/(2*y^2)-1=(y-1)*(1-x/2-x*(y+1)/(2*y^2)) :=
by {field_simp [hy],ring}

theorem release_slope (x y : ℝ) (hx : 0≤x) (hu : x<2/3) (hy : 1≤y) :
 0<1-x/2-x*(y+1)/(2*y^2) :=
begin
 have y2 : 0<2*y^2 := by nlinarith [sq_nonneg (y-1)],
 have d : 0≤2*y^2-y-1 := by nlinarith [sq_nonneg (y-1)],
 have h : x*(y+1)/(2*y^2)≤x :=
   (div_le_iff y2).2 (by nlinarith [mul_nonneg hx d]),
 linarith
end

theorem outgoing_allowed (x y : ℝ) (hx : 0≤x) (hu : x<2/3) (hy : 1<y) :
 1<(1-x/2)*y+x/(2*y^2) :=
begin
 have h := release_factor x y (ne_of_gt (by linarith)),
 have c := mul_pos (sub_pos.mpr hy) (release_slope x y hx hu (le_of_lt hy)),linarith
end

theorem matching_mass (m x : ℝ) : m*(1-x/2)=m-m*x/2 := by ring

theorem outward_acceleration (x : ℝ) (hx : x<2/3) : 0<1-3*x/2 := by linarith

-- The conservation issue applies to each irreversible record with positive weight.
theorem history_energy (gap r e : ℝ) (hg : 0<gap) (hr : 0<r)
 (he : 0<e) (too_small : r<gap/e) : e<gap/r :=
 (lt_div_iff hr).2 (by nlinarith only [(lt_div_iff he).1 too_small])

theorem positive_survivor (g w : ℝ) : 0<real.exp(-g*w) := real.exp_pos _

theorem jump_balance (g s : ℝ) (h : s<g) :
 g/(g-s)=1+s/(g-s) :=
by {field_simp [ne_of_gt (sub_pos.mpr h)];ring}

theorem point_mass_no_jump {A B : Type*} [has_zero B]
 (V : A→B) (p : A→A) (q : B→B) (v : A)
 (intertwines : ∀ a, q (V a)=V (p a)) (point : p v=v)
 (no_atom : ∀ b,q b=0) : V v=0 :=
calc V v=V (p v) : congr_arg V point.symm
 ... = q (V v) : (intertwines v).symm
 ... = 0 : no_atom _

theorem time_overlap_defect (a b : ℝ) (h : a^2+b^2≠0) :
 1-2*a*b/(a^2+b^2)=(a-b)^2/(a^2+b^2) :=
by {field_simp [h],ring}

def cap_primitive (u : ℝ) := (real.sinh u*real.cosh u-u)/2

theorem cap_primitive_derivative (u : ℝ) : has_deriv_at cap_primitive (real.sinh u^2) u :=
begin
 have h := (((real.has_deriv_at_sinh u).mul (real.has_deriv_at_cosh u)).sub
            (has_deriv_at_id u)).div_const 2,
 convert h using 1, nlinarith only [real.cosh_sq_sub_sinh_sq u]
end

theorem cap_bounce_integral (h : ℝ) (hp : 0<h) :
 (4/(h*real.sqrt(1+h^2)))*(∫ z in (0:ℝ)..real.arsinh h,real.sinh z^2)=
 2*(1-real.arsinh h/(h*real.sqrt(1+h^2))) :=
begin
 have cont : continuous (λ t:ℝ,real.sinh t^2) := real.continuous_sinh.pow 2,
 rw [interval_integral.integral_eq_sub_of_has_deriv_at (λ t ht,cap_primitive_derivative t)
      (cont.interval_integrable _ _)],
 have hs : 0<real.sqrt (1+h^2) := real.sqrt_pos.2 (by nlinarith only [sq_nonneg h]),
 simp [cap_primitive],field_simp [ne_of_gt hp,ne_of_gt hs];ring
end

theorem sweep_transform (a b t : ℝ) (ha : 0<a) (hb : 0<b) (hb2 : b^2=1+a^2) :
 2*a/(a^2+(1+a^2)*t^2)=(2/b)*(b/a)/(1+((b/a)*t)^2) :=
begin
 have h1 : 0<a^2+(1+a^2)*t^2 :=
 add_pos_of_pos_of_nonneg (pow_pos ha 2)
   (mul_nonneg (by nlinarith only [sq_nonneg a]) (sq_nonneg t)),
 have h2 : 0<1+((b/a)*t)^2 := by nlinarith only [sq_nonneg ((b/a)*t)],
 apply (div_eq_div_iff (ne_of_gt h1) (ne_of_gt h2)).2,
 rw [←hb2],field_simp [ne_of_gt ha,ne_of_gt hb];ring
end

theorem cap_barrier_identity (u v a : ℝ) (unit : u^2+v^2=1) :
 (a*u+v)^2+(a*v-u)^2=1+a^2 := by linear_combination (1+a^2)*unit

theorem angular_cover (N f : ℝ) (hf : 0<f) (full : 1≤N*f) : 1/f≤N :=
 (div_le_iff hf).2 full

theorem extensive_cap_wall (x a y : ℝ) (hy : 0<y) (hx : 0≤x) (ha : 0≤a) :
 x*(1-a)*y ≤ x*(a/y^2+(1-a)*y) :=
begin
 have h:=mul_nonneg hx (div_nonneg ha (sq_nonneg y)),
 linarith only [show x*(a/y^2+(1-a)*y)=x*(a/y^2)+x*(1-a)*y,by ring,h]
end

theorem linear_tension_saturation (x u : ℝ) (hu : u^2=3) :
 (4*(1-x))*(1-u/2)-x*(2-3*x)=(u*(1-x)-1)^2 :=
by linear_combination -(1-x)^2*hu

theorem linear_tension_compactness (u : ℝ) (hu : u^2=3) :
 2*(1-u/2)-(1-u/2)^2=(1:ℝ)/4 := by linear_combination -hu/4

theorem short_rim_cannot_double (reach : ℝ) (h : reach<real.pi) :
 2*reach<2*real.pi := by linarith

theorem protected_roots (a r lo hi : ℝ) (hr : r≠0) :
 a*r+a*lo*hi/r-a*(lo+hi)=a*(r-lo)*(r-hi)/r :=
by {field_simp [hr],ring}

theorem winding_confines (a r lo hi : ℝ) (ha : 0<a) (hr : 0<r) (ord : lo≤hi)
 (allowed : a*r+a*lo*hi/r≤a*(lo+hi)) : lo≤r ∧ r≤hi :=
begin
 have id:= protected_roots a r lo hi (ne_of_gt hr),
 have neg : a*(r-lo)*(r-hi)/r≤0 := by linarith only [id,allowed],
 have h : a*(r-lo)*(r-hi)≤0 := by simpa using (div_le_iff hr).1 neg,
 split,
 {by_contra hn,have h1 : r<lo:=lt_of_not_ge hn,
  have hp := mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg ha (sub_neg.mpr h1))
    (sub_neg.mpr (lt_of_lt_of_le h1 ord)),
  exact (not_lt_of_ge h) hp},
 {by_contra hn,have h1 : hi<r:=lt_of_not_ge hn,
  have hp := mul_pos (mul_pos ha (sub_pos.mpr (lt_of_le_of_lt ord h1))) (sub_pos.mpr h1),
  exact (not_lt_of_ge h) hp}
end

theorem wound_speed_factor (lo hi r : ℝ) :
 ((hi+lo)*r)^2-(r^2+hi*lo)^2=(hi^2-r^2)*(r^2-lo^2) := by ring

theorem wound_time_coordinate (lo hi t : ℝ) :
 let r2:=lo^2+(hi^2-lo^2)*t in
 (hi^2-r2)*(r2-lo^2)=(hi^2-lo^2)^2*t*(1-t) := by {dsimp,ring}

theorem wall_lapse_angular (r k R : ℝ) (hr : r≠0) (hk : k≠0) (hR : R≠0) :
 (r/(k*R))/r=1/(k*R) := by {field_simp [hr,hk,hR];ring}

theorem capture_energy_at_turn (a r l : ℝ) (hr : r≠0) :
 a*r+(a*r*l)/r=a*(l+r) := by {field_simp [hr],ring}

theorem frobenius_rim (alpha g : ℝ) (h : alpha^2=g^2+1/4) :
 (alpha+1/2)*(alpha-1/2)=g^2 := by nlinarith only [h]

theorem radial_ground_equation (u A g r : ℝ) (hr : r≠0)
 (indicial : u*(u-1)=g^2) :
 -((u/r-A*r)^2-u/r^2-A)+(A*r+g/r)^2=A*(2*u+1+2*g) :=
calc -((u/r-A*r)^2-u/r^2-A)+(A*r+g/r)^2=
 A*(2*u+1+2*g)+(g^2-u*(u-1))/r^2 : by {field_simp [hr],ring}
 ... = A*(2*u+1+2*g) : by {rw [indicial],ring}

theorem laguerre_reduction (j alpha x L L1 L2 : ℝ)
 (lag : x*L2+(1+alpha-x)*L1+j*L=0) :
 -4*x*L2+4*(x-alpha-1)*L1=4*j*L :=
by linear_combination -4*lag

theorem ground_leakage (alpha z : ℝ) (hz : 0<z)
 (intg : interval_integrable (λ x:ℝ,x^alpha*real.exp(-x)) volume 0 z) :
 0<∫ x in (0:ℝ)..z,x^alpha*real.exp(-x) :=
 interval_integral.interval_integral_pos_of_pos_on intg
 (λ x hx, mul_pos (real.rpow_pos_of_pos hx.1 _) (real.exp_pos _)) hz

theorem nonzero_diagonal_weight (w p : ℕ→ℝ) (wn : ∀ n,0≤w n)
 (pn : ∀ n,0<p n) (nonempty : ∃ n,0<w n)
 (s : summable (λ n,w n*p n)) : 0<∑' n,w n*p n :=
begin
 rcases nonempty with ⟨n,hn⟩,
 exact lt_of_lt_of_le (mul_pos hn (pn n)) (le_tsum s n (λ j h, mul_nonneg (wn j) (pn j).le))
end

theorem cannot_remain_closed (p : ℝ→ℝ) (avg : ℝ)
 (positive_diag : 0<avg)
 (positive_energy : ∀ a b:ℝ,a<b → (∀ t∈set.Ioo a b,p t=0) → ∀ t,p t=0)
 (diagonal_mean : (∀ t,p t=0) → avg=0)
 (a b : ℝ) (hab : a<b) : ¬ (∀ t∈set.Ioo a b,p t=0) :=
begin intro h,exact (ne_of_gt positive_diag) (diagonal_mean (positive_energy a b hab h)) end

theorem thermal_winding_mean (beta v vdual : ℝ) (hb : 0<beta) (hv : 0<vdual)
 (poisson_derivative : beta*v=1/2-(real.pi^2/beta)*vdual) :
 beta*v<1/2 :=
begin
 have hp := mul_pos (div_pos (pow_pos real.pi_pos 2) hb) hv,
 linarith only [poisson_derivative,hp]
end

theorem thermal_mgf (p q d U V : ℝ) (hq : 0<q) (hd : 0≤d) (hU : 0<U)
 (mon : V≤U) (transform : p*U=q*d*V) : p/q≤d :=
begin
 apply (div_le_iff hq).2,
 apply le_of_mul_le_mul_right _ hU,
 have leq:=mul_le_mul_of_nonneg_left mon (mul_nonneg hq.le hd),
 nlinarith only [transform,leq]
end

theorem chernoff_optimization (n u : ℝ) (hu : 0<u) :
 -(1-1/u)*(n*u/2)-n/2*real.log (1/u)= -n*(u-1-real.log u)/2 :=
begin rw [one_div,real.log_inv],field_simp [ne_of_gt hu];ring end

theorem neutral_bypass (a : ℝ) : (1:ℝ)+a=0+(a+1) := by ring

-- Multisets represent occupation basis vectors, allowing arbitrary species
-- and any finite particle number, including two opposite ordinary charges.
theorem forbidden_multiset_empty {ι : Type*} (m : multiset ι) :
 m.card=0 ↔ m=0 := multiset.card_eq_zero

def exchange_ports {X : Type*} (ports : X×X) : X×X := (ports.2,ports.1)
def project_in {X : Type*} [has_zero X] (ports : X×X) : X×X := (ports.1,0)
def project_rim {X : Type*} [has_zero X] (ports : X×X) : X×X := (0,ports.2)

theorem exchange_involution {X : Type*} (ports : X×X) :
 exchange_ports (exchange_ports ports)=ports := by cases ports;refl

theorem receipt_transports_constraint {X : Type*} [has_zero X] (ports : X×X) :
 project_rim (exchange_ports ports)=exchange_ports (project_in ports) := rfl

theorem inward_absent {X : Type*} [has_zero X] (ports : X×X)
 (constraint : project_rim ports=ports) : ports.1=0 :=
 (congr_arg prod.fst constraint).symm

theorem opposite_charges_count {ι : Type*} (a b : ι) :
 (a ::ₘ b ::ₘ (0:multiset ι)).card=2 := by simp

theorem unchanged_reference {X R : Type*} [has_zero X] (x : X) (r : R) :
 (exchange_ports (x,(0:X)),r)=(((0:X),x),r) := rfl

theorem port_switch_work {X : Type*} (energyI energyS : X→ℝ) (work : ℝ)
 (matching : ∀ x,energyS x=energyI x+work) (x : X) :
 energyS x-energyI x=work := by rw [matching]; ring

end material_dipole_surface
