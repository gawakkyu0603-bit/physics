import tactic
import analysis.calculus.deriv.basic
import analysis.calculus.deriv.slope
import analysis.calculus.deriv.mul
import analysis.calculus.deriv.add
import analysis.calculus.deriv.comp
import analysis.special_functions.pow.real
import algebra.big_operators.order

/- Matrix clock and two-sphere adjoint reduction. The canonical representation,
   spin Casimir, trace density, ordinary low-energy matter transfer and the
   local observational likelihood are specified in the record, not postulated
   as universal properties of every CAT state. -/
namespace cat_sky_geometry
noncomputable theory
open_locale big_operators

theorem su2_double (a x : ℝ) : a^3*(2*x)+(-2*a^3)*x=0 := by ring
theorem radial_energy (a v : ℝ) : 2*v*(-2*a^3)+4*a^3*v=0 := by ring

theorem double_action {A : Type*} [ring A] (p x q : A) :
 p*(p*x-x*q)-(p*x-x*q)*q=p*p*x-2*(p*x*q)+x*(q*q) := by noncomm_ring
theorem spin_kernel (u v J ell : ℝ) :
 J*(u^2+v^2)-2*u*v*(J-ell/2)=J*(u-v)^2+u*v*ell := by ring
theorem scaled_difference (J d deriv : ℝ) (J0 : J≠0)
 (exact_diff : d=deriv/J) : J^2*d^2=deriv^2 :=
by {rw [exact_diff], field_simp [J0], ring}
theorem frame_metric (a C : ℝ) (ha : a≠0) (hc : C≠0) :
 (-(a^2*C))*(a^2/C)*C*C = -(a^2*C)^2 ∧
 (a^2*C)/(-(a^2*C))= -1 ∧ (a^2*C)/(a^2/C)=C^2 ∧ (a^2*C)/C=a^2 :=
begin
 have hn : a^2*C≠0 := mul_ne_zero (pow_ne_zero _ ha) hc,
 split, {field_simp [hc]; ring},
 split, {field_simp [hn]},
 split; field_simp [ha,hc]; ring
end

theorem first_integral (a v c E C : ℝ) (hE : E=v^2+a^4) (hC : C^2=c^2+v^2) :
 C^2+a^4=c^2+E := by linarith
theorem directional_relation (a v C B dose : ℝ) (ha : a≠0) (hc : C≠0)
 (hb : B≠0) (hu : dose≠0) (hs : C^2+a^4=B) :
 (-a^3*v/(C^2*dose)) =
  -(a^4/B)*((v/a+a^3*v/C^2)/dose) :=
begin
 field_simp [ha,hc,hb,hu],
 rw [←hs], ring
end

theorem quadrupole_floor (q : ℝ) (h : 0≤q) (hu : q≤1) :
 (1-2*q)^2≤(1+q)^2 := by nlinarith [mul_nonneg h (sub_nonneg.mpr hu)]
theorem no_positive_axes (hp q : ℝ) (hq : 0<q) : ¬(0<hp ∧ 0< -q*hp) :=
by {rintro ⟨h,h'⟩, nlinarith [mul_pos hq h]}
theorem coasting_product (D A z : ℝ) (hz : 1+z≠0) (hd : D=A/(1+z)) :
 (1+z)*D=A := by {rw [hd],field_simp [hz]; ring}
theorem coasting_drift (h z : ℝ) : (1+z)*h-h*(1+z)=0 := by ring

theorem angular_design_bound (x y z : ℝ) (hx : 0≤x) (hy : 0≤y) (hz : 0≤z)
 (hn : x+y+z=1) :
 (x-z)^2+(y-z)^2+4*x*y+4*x*z+4*y*z≤2 :=
begin
 calc (x-z)^2+(y-z)^2+4*x*y+4*x*z+4*y*z
     = 2*(x+y+z)^2-(x^2+y^2+2*x*z+2*y*z) : by ring
 ... ≤ 2*(x+y+z)^2 : sub_le_self _ (by positivity)
 ... = 2 : by rw [hn]; norm_num
end
theorem quoted_contrast (v1 v2 cov : ℝ) (h : -(v1*v2)≤cov) :
 v1^2+v2^2-2*cov≤(v1+v2)^2 := by linarith only [h]

theorem same_charge {A : Type*} [ring A] (P O : A) (p2 : P*P=P) (comm : P*O=O*P) :
 P*O*P+(1-P)*O*(1-P)=O :=
begin
 have hop : P*O*P=O*P := by rw [comm,mul_assoc,p2],
 calc P*O*P+(1-P)*O*(1-P)=O-P*O-O*P+2*(P*O*P) : by noncomm_ring
 ... = O : by rw [hop,comm]; noncomm_ring
end
theorem reset_phase (A B c : ℝ) :
 A^2+B^2+2*A*B*c-(A^2+B^2)=2*A*B*c := by ring
theorem counterkick (n v : ℝ) : n+n-2*n*v=2*n*(1-v) := by ring
theorem return_contrast (f I pu : ℝ) (hu : pu≤1) (hf : f≤1) (hi : I=(1-f)*pu) :
 f≤1-I := by nlinarith [mul_nonneg (sub_nonneg.mpr hf) (sub_nonneg.mpr hu)]
theorem weakest_magnetar (f : ℝ) (h : (85-15)/100≤1-f) : f≤3/10 := by linarith
theorem gain_on_resonance (r q mean en : ℝ) (hr : r^2≠1)
 (hq : 1-r*q≠0) (hm : (1-r*q)*mean=1)
 (he : (1-r^2)*en=1+2*r*q*mean) :
 (1-r^2)*(1-r*q)*en=1+r*q :=
begin
 calc (1-r^2)*(1-r*q)*en=(1-r*q)*((1-r^2)*en) : by ring
 ... =(1-r*q)+2*r*q*((1-r*q)*mean) : by rw [he]; ring
 ... =1+r*q : by rw [hm]; ring
end
theorem forced_shape (r q c re den : ℝ)
 (hd : den=1-2*r*q*c+(r*q)^2) (hm : re*den=r*q*c-(r*q)^2) :
 (1+2*re)*den=1-(r*q)^2 := by nlinarith
theorem occupation_line (n : ℝ) :
 (n+1)*(n+2)+n*(n-1)=2*(n^2+n+1) := by ring
theorem common_pair_transfer (u v : ℤ) : (u+2)+(v-2)=u+v := by ring
theorem preserves_parity (n : ℕ) : (n+2)%2=n%2 := nat.add_mod_right n 2
theorem squeezed_binary_missing (r total : ℝ) (h : total=1) :
 total-(1-r)^2=2*r-r^2 := by rw [h]; ring
theorem incoherent_neutrino (base amp phase : ℝ) :
 ((base+amp*(1-phase)/2)+(base+amp*(1+phase)/2))/2=base+amp/2 := by ring
theorem distance_test (f flux ratio : ℝ) (h : flux=1-f) (hr : ratio^2*flux=1) :
 ratio^2*(1-f)=1 := by rwa [←h]
theorem incomparable {A : Type*} [ring A] (u v ud vd h : A)
 (hk : u*v=v*u) (hd : vd*ud=ud*vd) :
 (u*v)*h*(vd*ud)=(v*u)*h*(ud*vd) := by rw [hk,hd]
theorem clock_relabel (scale lapse velocity : ℝ) (hs : scale≠0) (hl : lapse≠0) :
 (velocity/scale)/(lapse/scale)=velocity/lapse := by {field_simp [hs,hl]}
theorem divided_second_difference (r h m : ℝ) (hh : h≠0) :
 ((m*h+h^3*r)/h)-m=h^2*r := by {field_simp [hh]; ring}
open_locale topology
theorem symmetric_slope (a : ℝ → ℝ) (v t : ℝ) (ha : has_deriv_at a v t) :
 filter.tendsto (slope (λ k : ℝ, a (t+k/2)-a (t-k/2)) 0)
  (𝓝[≠] (0 : ℝ)) (𝓝 v) :=
begin
 apply has_deriv_at_iff_tendsto_slope.mp,
 have hp : has_deriv_at (λ k : ℝ, t+k/2) (1/2) 0 :=
   by convert (has_deriv_at_const (0:ℝ) t).add ((has_deriv_at_id (0:ℝ)).div_const 2) using 1; simp,
 have hm : has_deriv_at (λ k : ℝ, t-k/2) (-(1/2)) 0 :=
   by convert (has_deriv_at_const (0:ℝ) t).sub ((has_deriv_at_id (0:ℝ)).div_const 2) using 1; simp,
 have p : has_deriv_at (a ∘ (λ k : ℝ,t+k/2)) (v*(1/2)) 0 :=
   by {apply has_deriv_at.comp (0:ℝ) _ hp, simpa using ha},
 have m : has_deriv_at (a ∘ (λ k : ℝ,t-k/2)) (v*(-(1/2))) 0 :=
   by {apply has_deriv_at.comp (0:ℝ) _ hm, simpa using ha},
 convert p.sub m using 1; try {refl}; ring
end

theorem vector_energy_rate (x y vx vy : ℝ) :
 2*vx*(-2*(x^2+y^2)*x)+2*vy*(-2*(x^2+y^2)*y)
 +2*(x^2+y^2)*(2*x*vx+2*y*vy)=0 := by ring
theorem rotor_charge_rate (x y vx vy : ℝ) :
 vx*vy+x*(-2*(x^2+y^2)*y)-vy*vx-y*(-2*(x^2+y^2)*x)=0 := by ring
theorem averaged_weight (w like prob : ℝ) (hy : prob≠0) (hn : 1-prob≠0) :
 prob*(w*like/prob)+(1-prob)*(w*(1-like)/(1-prob))=w :=
by {field_simp [hy,hn]; ring}
theorem spin_frequency_positive (u v L J : ℝ) (hj : 0≤J) (hL : 0≤L) (hbound : L≤4*J) :
 0≤J*(u-v)^2+u*v*L :=
begin
 by_cases huv : 0≤u*v,
 {exact add_nonneg (mul_nonneg hj (sq_nonneg _)) (mul_nonneg huv hL)},
 have hid : J*(u-v)^2+u*v*L=J*(u+v)^2+(-(u*v))*(4*J-L) := by ring,
 rw [hid], exact add_nonneg (mul_nonneg hj (sq_nonneg _))
     (mul_nonneg (neg_nonneg.mpr (le_of_lt (lt_of_not_ge huv))) (sub_nonneg.mpr hbound))
end
theorem wronskian_rate (freq a b ad bd : ℝ) :
 ad*bd+a*(-freq*b)-((-freq*a)*b+ad*bd)=0 := by ring
theorem turning_polynomial (x : ℝ) :
 4*(-x^3+7/4*x-3/4)=4*(1-x)*(x-1/2)*(x+3/2) := by ring
theorem turning_phase (s co : ℝ) (trig : co^2+s^2=1) :
 (s*co)^2*((5-s^2)/2)=
 4*(1-(1-s^2/2))*((1-s^2/2)-1/2)*((1-s^2/2)+3/2) :=
by {have h : co^2=1-s^2 := by linarith, rw [mul_pow,h], ring}
theorem orbit_area_order (s t : ℝ) (hs : 0<s) (hst : s<t) :
 (t+3/2)/(t+3/4)<(s+3/2)/(s+3/4) :=
begin
 apply (div_lt_div_iff (by linarith : 0<t+3/4) (by linarith : 0<s+3/4)).2,
 nlinarith only [hst]
end
theorem orbit_area_range (u : ℝ) (hu : 0<u) :
 1<(u+3/2)/(u+3/4) ∧ (u+3/2)/(u+3/4)<2 :=
begin
 have hp : 0<u+3/4 := by linarith,
 split, {apply (lt_div_iff hp).2, linarith}, {apply (div_lt_iff hp).2, linarith}
end
theorem circular_minimum (x y : ℝ) (hx : 0<x) :
  x^2+2*y^3/x-3*y^2=(x-y)^2*(x+2*y)/x :=
by {field_simp [ne_of_gt hx]; ring}
theorem circular_gap_positive (x y : ℝ) (hx : 0<x) (hy : 0<y) (hne : x≠y) :
 0<x^2+2*y^3/x-3*y^2 :=
begin
 rw [circular_minimum x y hx],
 exact div_pos (mul_pos (sq_pos_of_ne_zero (x-y) (sub_ne_zero.mpr hne)) (by linarith)) hx
end
theorem orbit_area_covers (v : ℝ) (hl : 1<v) (hh : v<2) :
 ∃ u : ℝ, 0<u ∧ (u+3/2)/(u+3/4)=v :=
begin
 let u : ℝ := (3/4)*(2-v)/(v-1),
 have hp : 0<u := div_pos (mul_pos (by norm_num) (sub_pos.mpr hh)) (sub_pos.mpr hl),
 refine ⟨u,hp,_⟩,
 apply (div_eq_iff (ne_of_gt (show 0<u+3/4, by linarith))).2,
 dsimp [u], field_simp [ne_of_gt (sub_pos.mpr hl)]; ring
end
theorem phase_acceleration (s co : ℝ) (trig : co^2+s^2=1) :
 -(co^2-s^2)*((5-s^2)/2)+(s*co)^2/2=7/2-6*(1-s^2/2)^2 :=
by {have h : co^2=1-s^2 := by linarith, rw [mul_pow,h], ring}
theorem radial_reconstruction (r v acc E L2 : ℝ)
 (energy : r^2*v^2+L2+r^6=E*r^2)
 (accel : 2*v^2+2*r*acc=2*E-6*r^4) : r^3*acc=L2-2*r^6 :=
by linear_combination (r^2/2)*accel-energy
end cat_sky_geometry
