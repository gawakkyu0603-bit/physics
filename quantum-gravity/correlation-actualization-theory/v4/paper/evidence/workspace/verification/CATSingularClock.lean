import tactic
import analysis.calculus.deriv.basic
import analysis.calculus.deriv.mul
import analysis.calculus.deriv.add
import analysis.calculus.mean_value
import analysis.special_functions.integrals

namespace cat_singular_clock
noncomputable theory

theorem schwarzschild_ratio (R h v : ℝ) (hR : R≠0) (hh : h≠0) (hr : h-R≠0) :
 v/R= -(2*(1-R/h))*(-h*v/(2*R*(h-R))) :=
by {field_simp [hR,hh,hr]; ring}
theorem deep_mismatch (r h q : ℝ) (hh : 0<h) (hr : r≤h/2) (hq : q<1) :
 q≠2*(1-r/h) :=
begin
 intro eq, have hx : r/h≤1/2 := (div_le_iff hh).2 (by linarith),
 linarith
end
theorem curvature_at_half (h : ℝ) (hh : h≠0) : 12*h^2/(h/2)^6=768/h^4 :=
by {field_simp [hh]; ring}
theorem affinity (r s h b : ℝ) (hs : s≠0) (hh : h≠0) (hb : b≠0)
 (hr : r^5=25/4*h*b^2*s^2) : s^2*(3/2*h*b^2/r^5)=6/25 :=
by {rw [hr], field_simp [hs,hh,hb]; ring}
theorem jacobi_powers :
 ((2:ℝ)/5)*((2:ℝ)/5-1)= -6/25 ∧ ((3:ℝ)/5)*((3:ℝ)/5-1)= -6/25 ∧
 ((6:ℝ)/5)*((6:ℝ)/5-1)=6/25 ∧ (-(1:ℝ)/5)*(-(1:ℝ)/5-1)=6/25 := by norm_num
theorem spherical_null (J L t k z y : ℝ) :
 J*(z*k)^2 + J*(t-(-t))^2 + (t*(-t))*L =
 J*(z*k)^2+(4*J-L)*t^2 := by ring
theorem top_spin_remainder (j : ℝ) : 4*j*(j+1)-(2*j)*(2*j+1)=2*j := by ring
theorem angular_remainder_nonneg (J L : ℝ) (h : L≤4*J) : 0≤4*J-L :=
sub_nonneg.mpr h
theorem cap_exterior (u b d : ℝ) (hn : b=0) :
 (1+d*b)/(u^2+b)=1/u^2 := by simp [hn]
theorem mixing_nonnegative (a b c d : ℝ) (det : a*d-b*c=1) :
 0≤a^2+b^2+c^2+d^2-2 :=
by {have h : a^2+b^2+c^2+d^2-2=(a-d)^2+(b+c)^2 :=
     by linear_combination 2*det, rw [h], positivity}
theorem vacuum_transfer (a b c d w : ℝ) (hw : w≠0) (h : a*d-b*c=1) :
 0≤(a^2+d^2+(w*b)^2+(c/w)^2-2)/4 :=
begin
 have hd : a*d-(w*b)*(c/w)=1 := by {convert h using 1; field_simp [hw]; ring},
 have hq := mixing_nonnegative a (w*b) (c/w) d hd,
 linarith only [hq]
end
theorem symplectic_wronskian (v a b pa pb : ℝ) :
 pa*pb+a*(-v*b)-((-v*a)*b+pa*pb)=0 := by ring
theorem lorentz_tide (t out : ℝ) (ht : t≠0) (h : 4*t^2*out=1) :
 4*out^2=1/(4*t^4) :=
begin
 have he : out=1/(4*t^2) := (eq_div_iff (by positivity : 4*t^2≠0)).2 (by linarith [h]),
 rw [he], field_simp [ht]; ring
end
theorem readout_total (p w : ℝ) : p*w+(1-p)*w=w := by ring
theorem radial_gap (l2 r E : ℝ) (hr : 0<r)
 (hl : 0<l2) (h : l2/r^2≤E) : l2≤E*r^2 := (div_le_iff (sq_pos_of_ne_zero r (ne_of_gt hr))).1 h
theorem growth_multiplicity (j : ℕ) :
 (j+1)^2-j^2=2*j+1 := by {have h : (j+1)^2=j^2+(2*j+1) := by ring, rw [h,nat.add_sub_cancel_left]}
theorem scaled_parabola (rate t mass : ℝ) (hr : rate≠0) :
 (mass+rate^2*t^2)/rate=mass/rate+rate*t^2 := by {field_simp [hr]; ring}
theorem field_energy_rate (r2 dot_uv lam x y vx vy : ℝ) :
 2*vx*(-lam*r2*x)+2*vy*(-lam*r2*y)
   +lam*(2*dot_uv*(x^2+y^2)+r2*(2*x*vx+2*y*vy))=
 2*lam*dot_uv*(x^2+y^2) := by ring
theorem coupled_energy_balance (r2 dot_uv gamma occupancy : ℝ) :
 2*dot_uv*(-(2*r2+gamma*occupancy))+4*r2*dot_uv+
 gamma*(2*dot_uv*occupancy)=0 := by ring
theorem radial_torque (x y vx vy k : ℝ) :
 vx*vy+x*(-k*y)-(vy*vx+y*(-k*x))=0 := by ring
theorem gap_with_field (x y vx vy field E : ℝ) (hf : 0≤field)
 (energy : E=vx^2+vy^2+(x^2+y^2)^2+field) :
 (x*vy-y*vx)^2≤E*(x^2+y^2) :=
begin
 rw [energy],
 have h : (vx^2+vy^2+(x^2+y^2)^2+field)*(x^2+y^2)-(x*vy-y*vx)^2=
 (x*vx+y*vy)^2+(x^2+y^2)^3+field*(x^2+y^2) := by ring,
 have hp : 0≤(x*vx+y*vy)^2+(x^2+y^2)^3+field*(x^2+y^2) := by positivity,
 linarith only [h,hp]
end
open set
theorem inward_deadline (R V k : ℝ → ℝ) (T : ℝ) (ht : 0≤T)
 (hr : ∀ t∈Icc 0 T, 0≤R t) (hk : ∀ t∈Icc 0 T, 0≤k t)
 (dr : ∀ t∈Icc 0 T, has_deriv_at R (V t) t)
 (dv : ∀ t∈Icc 0 T, has_deriv_at V (-(k t)*(R t)) t) :
 R T≤R 0+V 0*T :=
begin
 have vmono : antitone_on V (Icc 0 T) :=
 (convex_Icc (0:ℝ) T).antitone_on_of_deriv_nonpos (has_deriv_at.continuous_on dv)
 (λ z hz,(dv z (interior_subset hz)).differentiable_at.differentiable_within_at)
 (by {intros z hz, have h := interior_subset hz, rw [(dv z h).deriv],
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hk z h)) (hr z h)}),
 have deriv_g : ∀ t∈Icc 0 T, has_deriv_at (λ z : ℝ,R z-V 0*z) (V t-V 0) t :=
 by {intros t h, convert (dr t h).sub ((has_deriv_at_id t).const_mul (V 0)) using 1; simp},
 have gmono := (convex_Icc (0:ℝ) T).antitone_on_of_deriv_nonpos
   (has_deriv_at.continuous_on deriv_g)
   (λ z hz,(deriv_g z (interior_subset hz)).differentiable_at.differentiable_within_at)
   (by {intros z hz, have h := interior_subset hz, rw [(deriv_g z h).deriv],
        exact sub_nonpos.mpr (vmono ⟨le_rfl,ht⟩ h h.1)}),
 have hh := gmono (show (0:ℝ)∈Icc 0 T, from ⟨le_rfl,ht⟩)
                  (show T∈Icc 0 T, from ⟨ht,le_rfl⟩) ht,
 dsimp at hh, linarith
end
open_locale interval
theorem quantum_scales (h : ℝ) (hh : h≠0) :
 h^4/h^6=1/h^2 ∧ h^6*(1/h^2)^4=1/h^2 ∧ (1/h^2)^2*h^2=1/h^2 :=
by {split, {field_simp [hh]; ring}, split; field_simp [hh]; ring}
theorem angular_indicial (s m : ℝ) : s*(s-1)+s-m^2=(s-m)*(s+m) := by ring
theorem angular_density_integral (m : ℕ) (e : ℝ) :
 (∫ r in (0:ℝ)..e, r^(2*m+1))=e^((2*m+1)+1)/(((2*m+1:ℕ):ℝ)+1) :=
by simp
theorem near_origin_energy (E mu eps m p : ℝ) (hn : m≠0)
 (h : m^2*p≤2*mu*E*eps^2) : p≤2*mu*E*eps^2/m^2 :=
(le_div_iff (sq_pos_of_ne_zero m hn)).2 (by linarith only [h])
open measure_theory
theorem angular_barrier_probability {X : Type*} [measurable_space X] (ν : measure X)
 (r : X → ℝ) (eps m : ℝ)
 (hi : integrable (λ x, if 0<r x ∧ r x≤eps then (1:ℝ) else 0) ν)
 (hb : integrable (λ x,m^2/(r x)^2) ν) :
 m^2*(∫ x, (if 0<r x ∧ r x≤eps then (1:ℝ) else 0) ∂ν)
 ≤ eps^2*(∫ x,m^2/(r x)^2 ∂ν) :=
begin
 rw [←integral_mul_left,←integral_mul_left],
 apply integral_mono_ae (hi.const_mul _) (hb.const_mul _),
 apply filter.eventually_of_forall, intro x,
 by_cases h : 0<r x ∧ r x≤eps,
 { simp only [if_pos h,mul_one],
   calc m^2 = (r x)^2*(m^2/(r x)^2) : by {field_simp [ne_of_gt h.1]; ring}
        ... ≤ eps^2*(m^2/(r x)^2) : mul_le_mul_of_nonneg_right
          (pow_le_pow_of_le_left h.1.le h.2 _) (div_nonneg (sq_nonneg _) (sq_nonneg _)) },
 { simp only [if_neg h,mul_zero], exact mul_nonneg (sq_nonneg _) (div_nonneg (sq_nonneg _) (sq_nonneg _)) }
end
end cat_singular_clock
