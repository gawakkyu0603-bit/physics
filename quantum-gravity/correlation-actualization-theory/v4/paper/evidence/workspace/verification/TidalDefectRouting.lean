import tactic
import analysis.calculus.mean_value
import analysis.special_functions.integrals
import analysis.special_functions.trigonometric.inverse
import analysis.special_functions.trigonometric.arctan_deriv

noncomputable theory
open measure_theory
open_locale interval big_operators

namespace tidal_defect_routing

-- The normalized real part along the upper/lower closed half-plane paths
-- defines continuous angle lifts via +/- arccos.
theorem lifted_angles (v : ℝ → ℝ) (hv : continuous v) :
 continuous (λ x, -real.arccos (v x)) ∧ continuous (λ x, real.arccos (v x)) :=
⟨(real.continuous_arccos.comp hv).neg,real.continuous_arccos.comp hv⟩

theorem lift_matches (v : ℝ) (l : -1≤v) (h : v≤1) :
 real.cos (-real.arccos v)=v ∧ real.cos (real.arccos v)=v :=
by simp [real.cos_arccos l h]

theorem moving_winding (v : ℝ → ℝ) (T : ℝ) (s : v 0=1) (e : v T= -1) :
 (-real.arccos (v T) - (-real.arccos (v 0))) -
 (real.arccos (v T) - real.arccos (v 0)) = -2*real.pi :=
by {rw [s,e,real.arccos_one,real.arccos_neg_one],ring}

theorem common_record (a b k : ℤ) : (a+2*k)-(b+2*k)=a-b := by ring

theorem fold_derivative_numerator (r H : ℝ) :
 2*r*(r^2+H^2)-5*r^3=r*(2*H^2-3*r^2) := by ring

theorem opposite_arms (a x y den : ℝ) (ha : 0<a) (hx : 0<x)
 (hy : 0<y) (hd : 0<den) : -(a*(2*x*y))/den<0 ∧ 0< -(a*(2*x*(-y)))/den :=
begin
 have h : 0<a*(2*x*y)/den := by positivity,
 constructor; nlinarith only [h,show -(a*(2*x*y))/den= -(a*(2*x*y)/den), by ring,
 show -(a*(2*x*(-y)))/den=a*(2*x*y)/den, by ring]
end

theorem finite_resolution (q ε : ℝ) (hq : 0<q) (he : 0<ε) :
 q^2/(q^2+ε^2)<1 :=
(div_lt_one (by positivity)).2 (by nlinarith [sq_pos_of_pos he])

-- The cost is for the two outgoing vacuum ports with zero incoming current.
theorem quadratic_time_bound (g : ℝ → ℝ) (T m : ℝ) (hT : 0<T)
 (hm : (∫ x in 0..T,g x)=T*m) (hg : interval_integrable g volume 0 T)
 (hs : interval_integrable (λ x,g x^2) volume 0 T) :
 T*m^2 ≤ ∫ x in 0..T,g x^2 :=
begin
 have nonneg : 0 ≤ ∫ x in 0..T,(g x-m)^2 :=
 interval_integral.integral_nonneg hT.le (λ x hx,sq_nonneg _),
 have fun_eq : (λ x,(g x-m)^2)=(λ x,g x^2-2*m*g x+m^2) := funext (λ x,by ring),
 rw [fun_eq, interval_integral.integral_add (hs.sub (hg.const_mul _)) interval_integrable_const,
     interval_integral.integral_sub hs (hg.const_mul _),interval_integral.integral_const_mul,
     hm] at nonneg,
 dsimp only at nonneg,
 rw [interval_integral.integral_const] at nonneg,
 simp only [sub_zero,smul_eq_mul] at nonneg, nlinarith only [nonneg]
end

theorem deadline_cost (w2 s2 m θ T : ℝ) (hT : 0<T)
 (hr : T*m^2≤w2) (hs : T*θ^2≤s2) :
 T*m^2+(3/2)*(T*θ^2)≤w2+(3/2)*s2 := by linarith

theorem fixed_flux_forbids_switch (w2 s2 base : ℝ) (hr : base≤w2)
 (hs : 0<s2) : base<w2+3/2*s2 := by linarith

-- Differentiate the actual log-slope of the proposed profile.  The two input
-- log-slopes obey the Riccati equation for the same prescribed energy flux.
theorem joined_derivative (t l r : ℝ → ℝ) (x k g : ℝ)
 (ht : has_deriv_at t (k*(l x-r x)) x)
 (hl : has_deriv_at l (g-(l x)^2) x)
 (hr : has_deriv_at r (g-(r x)^2) x) :
 has_deriv_at (λ u,t u*l u+(1-t u)*r u)
 (g-(t x*l x+(1-t x)*r x)^2+
    (k-t x*(1-t x))*(l x-r x)^2) x :=
begin
 convert (ht.mul hl).add (((has_deriv_at_const x (1:ℝ)).sub ht).mul hr) using 1,
 ring
end

theorem current_supplies_turn (t k l r g v c : ℝ) (hc : c≠0)
 (rotation : v^2=(c/3)*(t*(1-t)-k)*(l-r)^2) :
 g+(k-t*(1-t))*(l-r)^2+3/c*v^2=g :=
by {rw [rotation],field_simp [hc],ring}

theorem left_join (a : ℝ) (ha : a≠0) :
 -(a-(-a))^2/(4*a)= -a ∧ (a-(-a))/(2*a)=1 :=
by {constructor; field_simp [ha]; ring}

theorem right_join (a : ℝ) : -(a-a)^2/(4*a)=0 ∧ (a-a)/(2*a)=0 := by simp

theorem blended_speed (a r : ℝ) (ha : a≠0) :
 ((a-r)/(2*a)*(1-(a-r)/(2*a))+1/(2*a))=(a^2+2*a-r^2)/(4*a^2) :=
by {field_simp [ha],ring}

theorem width_derivative (x : ℝ) :
 has_deriv_at (λ z : ℝ,z+(1+z^2)*real.arctan z) (2*(1+x*real.arctan x)) x :=
begin
 have h : (1+x^2)≠0 := ne_of_gt (by positivity),
 convert (has_deriv_at_id x).add (((has_deriv_at_const x (1:ℝ)).add ((has_deriv_at_id x).pow 2)).mul (real.has_deriv_at_arctan x)) using 1,
 dsimp, field_simp [h], ring
end

-- Natural units. If M'=-F(M), and Y=F dR/dM, then d²R/du²=K F R.
theorem mass_local_equation (m y : ℝ → ℝ) (u F K R : ℝ)
 (hm : has_deriv_at m (-F) u) (hy : has_deriv_at y (K*R) (m u)) :
 has_deriv_at (λ t,-y (m t)) (K*F*R) u :=
begin
 convert (hy.comp u hm).neg using 1, ring
end

theorem ramp_integral : (∫ x in (0:ℝ)..1,(6*x-6*x^2)^2)=6/5 :=
begin
 have h : ∀ x : ℝ, has_deriv_at (λ y : ℝ,12*y^3-18*y^4+(36/5)*y^5)
 ( (6*x-6*x^2)^2 ) x,
 { intro x, convert ((((has_deriv_at_pow 3 x).const_mul 12).sub ((has_deriv_at_pow 4 x).const_mul 18)).add ((has_deriv_at_pow 5 x).const_mul (36/5))) using 1, norm_num, ring },
 have cont : continuous (λ x : ℝ,(6*x-6*x^2)^2) := by continuity,
 rw [interval_integral.integral_eq_sub_of_has_deriv_at (λ x hx,h x) (cont.interval_integrable _ _)],
 norm_num
end

theorem bell_recovery (x : ℝ) (hx : x≤1) :
 (1+x)/2=1 ↔ x=1 := by split; intro h; linarith

theorem terminal_mass (s T : ℝ) (ht : T≠0) (hs : s≠0) :
 (1-s)+(1/(3*T*s^2))*(9*T*s^3)/3=1 :=
by {field_simp [ht,hs],ring}

-- Transport of a wave on both species and any spectator/reference index.
theorem joint_field_inverse {Time Port Ref A : Type*} (p : Time ≃ Time)
 (s : Time → Port ≃ Port) (f : Time → Port → Ref → A) (t : Time) (i : Port) (j : Ref) :
 f (p (p.symm t)) (s (p.symm t) ((s (p.symm t)).symm i)) j = f t i j :=
by rw [equiv.apply_symm_apply, equiv.apply_symm_apply]

theorem mass_series_step (p n : ℝ) (hp : p≠0) :
 (p*n)*(p*n+(2-p)-1)=p^2*n*(n-1+1/p) :=
by {field_simp [hp],ring}

theorem single_output_norm {ι : Type*} (w η : ι → ℝ) (I : finset ι) :
 (∑ i in I,w i*η i)+(∑ i in I,w i*(1-η i))=∑ i in I,w i :=
begin
 rw [←finset.sum_add_distrib], apply finset.sum_congr rfl, intros i hi, ring
end

-- Retained amplitude on a delayed ray. One genuine exchange during the
-- sequence makes the initial amplitude vanish and gives telescoping norm.
theorem loop_balance (r t a : ℝ) (unitary : r^2+t^2=1) :
 (r*a)^2+(t*a)^2=a^2 :=
by calc (r*a)^2+(t*a)^2=(r^2+t^2)*a^2 : by ring
                     ... = a^2 : by rw [unitary,one_mul]

theorem history_balance (R emitted : ℕ → ℝ)
 (step : ∀ n,R (n+1)+emitted n=R n) (n : ℕ) :
 R n+(∑ k in finset.range n,emitted k)=R 0 :=
begin
 induction n with n ih,
 {simp}, {rw [finset.sum_range_succ], nlinarith only [step n,ih]}
end

theorem circle_power (l r g : ℝ) :
 g-((l-r)/2)^2+(l-r)^2/4=g := by ring

theorem circle_weighted_flux (y dy ddy : ℝ → ℝ) (T : ℝ)
 (hy : ∀ x,has_deriv_at y (dy x) x) (hd : ∀ x,has_deriv_at dy (ddy x) x)
 (hc : continuous (λ x,dy x^2+y x*ddy x))
 (s : y 0=0) (e : y T=0) :
 (∫ x in 0..T,(dy x^2+y x*ddy x))=0 :=
begin
 have h : ∀ x,has_deriv_at (λ z,y z*dy z) (dy x^2+y x*ddy x) x,
 { intro x,convert (hy x).mul (hd x) using 1,ring },
 rw [interval_integral.integral_eq_sub_of_has_deriv_at (λ x hx,h x) (hc.interval_integrable _ _)],
 simp [s,e]
end

theorem separated_corner (A B x y : ℝ) (ha : A≠0) (hb : B≠0)
 (h : x+y≠0) : (A*B/(x+y)^2)/A/B=1/(x+y)^2 :=
by {field_simp [ha,hb,h],ring}

theorem flushes_all (retained fraction : ℝ) (zero : fraction=0) : fraction*retained=0 :=
by rw [zero,zero_mul]

end tidal_defect_routing
