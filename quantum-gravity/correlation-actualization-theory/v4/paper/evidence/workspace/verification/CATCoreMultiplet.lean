import tactic
import analysis.special_functions.integrals
import analysis.calculus.deriv.mul
import analysis.calculus.deriv.pow
import analysis.inner_product_space.basic
import algebra.big_operators.order

namespace cat_core_multiplet
noncomputable theory
open measure_theory set
open_locale interval big_operators

def br {A : Type*} [ring A] (a b : A) := a*b-b*a
theorem linearized_force {A : Type*} [ring A] (a b x : A) :
 br a (br b x)+br b (br a x)=2*br (br x b) a-br x (br b a) :=
by {unfold br, noncomm_ring}
theorem gauss_orbit (a v c : ℝ) : a*(v*c)-v*(a*c)=0 := by ring
theorem vector_branches (l : ℝ) :
 l*(l+1)-2*l=l*(l-1) ∧ l*(l+1)+2*(l+1)=(l+1)*(l+2) :=
by {constructor;ring}
theorem physical_counts (l : ℝ) :
 6*(2*l+1)+(2*l+3)+(2*l-1)=8*(2*l+1) ∧
 4*((2*l+2)+2*l)=8*(2*l+1) := by {constructor;ring}
theorem fermion_cost_per_spin (l : ℝ) :
 4*((2*l+2)*l+(2*l)*(l+1))=16*l*(l+1) := by ring
theorem spin_sum (n : ℕ) :
 3*(∑ i in finset.range n, ((i:ℝ)+1)*((i:ℝ)+2))=(n:ℝ)*(n+1)*(n+2) :=
begin
 induction n with n ih,
 {simp},
 rw [finset.sum_range_succ,nat.cast_succ,mul_add,ih],ring
end
theorem normalized_fermi_work (n a : ℝ) (h : n*(n+1)*(n+2)≠0) :
 (16*a*n*(n+1)*(n+2)/3)/(n*(n+1)*(n+2)/4)=64*a/3 :=
begin
 have hn : n≠0 := λ e,h (by rw [e,zero_mul,zero_mul]),
 have hh : n+1≠0 := λ e,h (by rw [e,mul_zero,zero_mul]),
 have hk : n+2≠0 := λ e,h (by rw [e,mul_zero]),
 field_simp [hn,hh,hk];ring
end
theorem crossing_necessary (g v a : ℝ) (ha : 0<a) (hg : 0<g)
 (h : 64*a/3≤v^2/(2*g)) : g≤3*v^2/(128*a) :=
begin
 have hs:= (le_div_iff (by linarith : 0<2*g)).1 h,
 apply (le_div_iff (by linarith : 0<128*a)).2,nlinarith only [hs]
end
theorem quartic_floor (a t mu : ℝ) (h : 0≤mu) :
 -(3/2)*mu*t^4 ≤ mu*a^4/2-2*mu*t^3*a :=
begin
 have q : 0≤a^2+2*a*t+3*t^2 := by nlinarith [sq_nonneg (a+t),sq_nonneg t],
 nlinarith only [mul_nonneg h (mul_nonneg (sq_nonneg (a-t)) q)]
end
theorem positive_oscillator (p d : ℝ → ℝ) (a b w : ℝ)
 (hab : a≤b) (hp : continuous p) (hd : continuous d)
 (hf : ∀ x, has_deriv_at p (d x) x) (ha : p a=0) (hb : p b=0) :
 w*(∫ x in a..b,(p x)^2) ≤ ∫ x in a..b,(d x)^2+(w*x*p x)^2 :=
begin
 let q := λ x:ℝ, (p x)^2+2*x*p x*d x,
 have hq : continuous q := (hp.pow 2).add (((continuous_const.mul continuous_id).mul hp).mul hd),
 have der : ∀ x,has_deriv_at (λ t:ℝ,t*(p t)^2) (q x) x :=
 by {intro x, convert (has_deriv_at_id x).mul ((hf x).pow 2) using 1, dsimp [q],norm_num,ring},
 have zero : (∫ x in a..b,q x)=0 :=
 by {rw [interval_integral.integral_eq_sub_of_has_deriv_at (λ x hx,der x)
          (hq.interval_integrable _ _)], change b*(p b)^2-a*(p a)^2=0, rw [hb,ha],ring},
 let e := λ x:ℝ,(d x)^2+(w*x*p x)^2,
 have ce : continuous e := (hd.pow 2).add (((continuous_const.mul continuous_id).mul hp).pow 2),
 have point : ∀ x∈Icc a b,w*(p x)^2≤ e x+w*q x :=
 by {intros x hx,dsimp [q,e],nlinarith only [sq_nonneg (d x+w*x*p x)]},
 have ip : interval_integrable (λ x,(p x)^2) volume a b := (hp.pow 2).interval_integrable _ _,
 have iq : interval_integrable q volume a b := hq.interval_integrable _ _,
 have ie : interval_integrable e volume a b := ce.interval_integrable _ _,
 have is : interval_integrable (λ x,e x+w*q x) volume a b := ie.add (iq.const_mul w),
 have hint := interval_integral.integral_mono_on hab (ip.const_mul w) is point,
 rw [interval_integral.integral_const_mul,interval_integral.integral_add ie (iq.const_mul w),
     interval_integral.integral_const_mul,zero,mul_zero,add_zero] at hint, exact hint
end
theorem tail_bound {X : Type*} [measurable_space X] (μ : measure X) (event : X→Prop)
 [decidable_pred event] (energy : X→ℝ) (low high E : ℝ) (hh : low<high)
 (hi : integrable (λ x, if event x then (1:ℝ) else 0) μ)
 (he : integrable (λ x,energy x-low) μ) (lower : ∀ x, low≤energy x)
 (barrier : ∀ x,event x → high≤energy x) (hE : (∫ x, energy x-low ∂μ)≤E-low) :
 (∫ x, (if event x then (1:ℝ) else 0) ∂μ)≤(E-low)/(high-low) :=
begin
 apply (le_div_iff (sub_pos.mpr hh)).2, rw [mul_comm,←integral_mul_left],
 refine le_trans (integral_mono_ae (hi.const_mul _) he _) hE,
 apply filter.eventually_of_forall, intro x, by_cases h : event x,
 {simp only [if_pos h,mul_one], linarith only [barrier x h]},
 {simp only [if_neg h,mul_zero],linarith only [lower x]}
end
theorem supertrace_deficit (q : ℝ) :
 6*q^2+(q+1)*(q-1)+(q-1)*(q+1)=8*(q-1/2)*(q+1/2) := by ring
theorem root_deficit (x y : ℝ) (h : x+y≠0) (hs : y^2=x^2-1/4) :
 x-y=1/(4*(x+y)) := by {field_simp [h], nlinarith only [hs]}
theorem lc_square_diff (p m k : ℝ) : (p^2-m^2)/k=(p+m)*((p-m)/k) :=
by {rw [←mul_div_assoc],congr' 1,ring}
theorem fermion_clifford {A : Type*} [ring A] (x y z : A) :
 br (x*y) z =x*(y*z+z*y)-(x*z+z*x)*y := by {unfold br, noncomm_ring}
theorem direction_norm (d h x y z w : ℝ) :
 x*(d*w)+y*(-d*z)+z*(d*y+h*w)+w*(-d*x-h*z)=0 := by ring
theorem no_frequency_mixing (p q z : ℝ) (hp : 0<p) (hq : q<0) (h : p*z=q*z) :
 z=0 := (mul_eq_zero.mp (show (p-q)*z=0, by nlinarith only [h])).resolve_left
 (ne_of_gt (sub_pos.mpr (lt_trans hq hp)))
theorem endpoint_invariance (Q V : ℝ→ℝ) (a b : ℝ) (hd : ∀ x,has_deriv_at Q (V x) x)
 (hc : continuous V) (eqn : Q a=Q b) : (∫ x in a..b,V x)=0 :=
by {rw [interval_integral.integral_eq_sub_of_has_deriv_at (λ x hx,hd x) (hc.interval_integrable _ _),eqn,sub_self]}
theorem affine_match (a b d : ℝ) : (1+(a+d))-(1+b)=a-b+d := by ring
theorem central_cubic (a b c d u k : ℝ) (h : k≠0) :
 ((a+b*(u+k/2)+c*(u+k/2)^2+d*(u+k/2)^3)-
  (a+b*(u-k/2)+c*(u-k/2)^2+d*(u-k/2)^3))/k =
   b+2*c*u+3*d*u^2+d*k^2/4 := by {field_simp [h],ring}
theorem material_gain (s c x : ℝ) : c*s*x-s*c=s*c*(x-1) := by ring
theorem material_probability (x y : ℝ) (h : x^2+y^2≤1) :
 0≤((x-1)^2+y^2)/4 ∧ ((x-1)^2+y^2)/4≤1 :=
begin
 have hx : -1≤x := by nlinarith [sq_nonneg (x+1),sq_nonneg y],
 constructor; nlinarith [sq_nonneg (x-1),sq_nonneg y]
end
theorem two_axes_volume (a b c d e f y z : ℝ) :
 (a*y+b*z)*(c*f-e*d)+(c*y+d*z)*(e*b-a*f)+(e*y+f*z)*(a*d-c*b)=0 := by ring
theorem same_start_energy (r v w : ℝ) (h : v^2=2*r^4) (hc : w^2=2*r^2) :
 v^2+r^4=(r*w)^2+r^4 := by {rw [mul_pow,h,hc],ring}
theorem projector_difference {A : Type*} [ring A] (p q : A)
 (hp : p*p=p) (hq : q*q=q) : (p-q)^2=p+q-p*q-q*p :=
by {rw [pow_two,sub_mul,mul_sub,mul_sub,hp,hq],abel}
open_locale real_inner_product_space
theorem rotating_cost {X : Type*} [normed_add_comm_group X] [inner_product_space ℝ X]
 (K d : X) (E N gap : ℝ) (hg : 0<gap) (he : 0≤E)
 (hwork : ⟪K,d⟫_ℝ=2*E) (hproj : ‖d‖^2=2*N) (hgap : gap*N≤E) :
 E≤‖K‖^2/(2*gap) :=
begin
 by_cases hz : E=0,
 {rw [hz], positivity},
 have hepos : 0<E := lt_of_le_of_ne he (ne.symm hz),
 have hcs := real_inner_le_norm K d, rw [hwork] at hcs,
 have hh := pow_le_pow_of_le_left (show 0≤2*E, by linarith) hcs 2,
 rw [mul_pow,mul_pow,hproj] at hh,
 have h1 := mul_le_mul_of_nonneg_left hh hg.le,
 have h2 := mul_le_mul_of_nonneg_left hgap (sq_nonneg ‖K‖),
 apply (le_div_iff (by linarith : 0<2*gap)).2,
 apply le_of_mul_le_mul_right _ hepos,
 nlinarith only [h1,h2]
end
theorem normalized_rotation_bound (l r : ℝ) (hl : 0<l) (hr : 0<r) :
 (12*(2*l+1)*r/l)/(16*r*l*(l+1))=3*(2*l+1)/(4*l^2*(l+1)) :=
by {have hp : l+1≠0 := by linarith, field_simp [ne_of_gt hl,ne_of_gt hr,hp];ring}
theorem convex_arc_floor {ι : Type*} (s : finset ι) (w x : ι→ℝ) (c : ℝ)
 (hw : ∀ i∈s, 0≤w i) (hx : ∀ i∈s,c≤x i) (hn : ∑ i in s,w i=1) :
 c≤∑ i in s,w i*x i :=
begin
 calc c=(∑ i in s,w i)*c : by rw [hn,one_mul]
 ... =∑ i in s,w i*c : finset.sum_mul
 ... ≤∑ i in s,w i*x i : finset.sum_le_sum (λ i hi, mul_le_mul_of_nonneg_left (hx i hi) (hw i hi))
end
theorem paired_phase (c s : ℝ) (h : c^2+s^2=1) :
 1-((c+c)/2)^2=s^2 ∧ (s+(-s))/2=0 := by {have t : (c+c)/2=c := by ring, rw [t], constructor, {linarith only [h]}, ring}
end cat_core_multiplet
