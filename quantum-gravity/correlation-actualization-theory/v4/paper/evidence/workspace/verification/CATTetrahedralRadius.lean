import data.real.sqrt
import tactic

noncomputable theory
namespace cat_tetrahedral_radius

-- A common change is in the kernel of an incidence comparison, for any index set.
theorem common_contact {L E : Type*} (src dst : E → L) (v : ℝ) (e : E) :
  (λ _ : L, v) (src e) - (λ _ : L, v) (dst e) = 0 := sub_self v

-- Half turns erase unlike-axis coefficients. The cycle identifies the diagonal.
theorem tetrahedral_projection (cross a b c : ℝ) (h : cross= -cross)
  (h₁ : a=b) (h₂ : b=c) : cross=0 ∧ b=a ∧ c=a :=
⟨by linarith, h₁.symm, (h₁.trans h₂).symm⟩

-- Two real components of z and its time derivative. Gradient energy is additive.
theorem fixed_charge_square (x y vx vy w : ℝ) :
  (vx^2+vy^2+(x^2+y^2)^2)/2-w*(x*vy-y*vx)+w^4/8 =
  ((vx+w*y)^2+(vy-w*x)^2+(x^2+y^2-w^2/2)^2)/2 := by ring

theorem charge_bound (a b c gradient : ℝ) (hg : 0≤gradient) :
  0≤(a^2+b^2+c^2)/2+gradient :=
add_nonneg (div_nonneg (add_nonneg (add_nonneg (sq_nonneg a) (sq_nonneg b)) (sq_nonneg c))
  (by norm_num)) hg

theorem radial_roots (x b : ℝ) (hb : b^2=36+8*x) :
 (x+4-(x+6-b))*(x-(x+6-b))-8*(x+6-b)=0 := by linear_combination hb

theorem stable_radius (x : ℝ) (hx : 0≤x) : 0≤x+6-real.sqrt (36+8*x) :=
begin
  have h : 0≤x*(x+4) := mul_nonneg hx (by linarith),
  have d : (x+6)^2-(36+8*x)=x*(x+4) := by ring,
  have k : 36+8*x≤(x+6)^2 := sub_nonneg.mp (d.symm ▸ h),
  exact sub_nonneg.mpr ((real.sqrt_le_left (show 0≤x+6, by linarith)).mpr k)
end

theorem occupation_balance (curvature gradient slope r variance : ℝ)
 (eqn : curvature=gradient+4*r^2*slope*variance) (hs : slope≤0) (hv : 0≤variance) :
 curvature-gradient≤0 :=
begin
  have h := mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (show 0≤4*r^2, from mul_nonneg (by norm_num) (sq_nonneg r)) hs) hv,
  linarith only [eqn,h]
end

theorem adjoint_quadrupole (L a b : ℝ) (ha : 15*a=L*(3*L-1)) (hb : 6*b=L^2-3*a) :
 30*(a-b)=L*(4*L-3) := by linear_combination 3*ha-5*hb

-- The determinant for a pair of bifundamental amplitudes after a constant rotation.
theorem pair_polynomial (x a gap y : ℝ) :
 (x+a-y)^2-gap^2-8*y = y^2-(2*(x+a)+8)*y+(x+a)^2-gap^2 := by ring

theorem pair_band (b g : ℝ) (lo : -g<b) (hi : b<g) : b^2-g^2<0 :=
begin
  have d : b^2-g^2=(b-g)*(b+g) := by ring,
  rw [d], exact mul_neg_of_neg_of_pos (sub_neg.mpr hi) (by linarith)
end

theorem pair_peak_polynomial (g : ℝ) :
  ((-g^2/8)-(-g^2/8))^2-g^2-8*(-g^2/8)=0 := by ring

theorem pair_peak_bound (b g : ℝ) (hb : 0≤b+4+g^2/8) :
  -(g^2/8)≤b+4-real.sqrt (8*b+16+g^2) :=
begin
  have d : (b+4+g^2/8)^2-(8*b+16+g^2)=(b+g^2/8)^2 := by ring,
  have h : 8*b+16+g^2≤(b+4+g^2/8)^2 := sub_nonneg.mp (d.symm ▸ sq_nonneg _),
  have k := (real.sqrt_le_left hb).mpr h,
  linarith only [k]
end

theorem three_phase_frame (a b c d e f : ℝ)
 (h₁ : a^2+b^2=1) (h₂ : c^2+d^2=1) (h₃ : e^2+f^2=1) :
  3≤4*((a*c+b*d)^2+(a*e+b*f)^2+(c*e+d*f)^2) :=
begin
  let s := (a*c+b*d)^2+(a*e+b*f)^2+(c*e+d*f)^2,
  let u := a^2+c^2+e^2-b^2-d^2-f^2,
  let v := 2*(a*b+c*d+e*f),
  have k : 4*s+2*((a^2+b^2)^2+(c^2+d^2)^2+(e^2+f^2)^2)
    -((a^2+b^2)+(c^2+d^2)+(e^2+f^2))^2 = u^2+v^2 := by { dsimp [s,u,v], ring },
  rw [h₁,h₂,h₃] at k,
  change 3≤4*s,
  linarith only [k,sq_nonneg u,sq_nonneg v]
end

theorem phase_witness (x y z : ℝ) (h : 3≤4*(x+y+z)) :
  1/4≤x ∨ 1/4≤y ∨ 1/4≤z :=
begin
  by_contra hn, push_neg at hn, rcases hn with ⟨hx, hy, hz⟩, linarith
end

theorem opposite_masses (t : ℝ) :
  (1+t)/2-t=1/2-t/2 ∧ (1+t)/2+t=1/2+3*t/2 := by constructor; ring

-- First even antiperiodic trial component and its orthogonal complement.
theorem even_gap (q a b : ℝ) (hq : 0<q) (hsmall : 0<8-3*q) :
  0≤q*a^2-2*q*a*b+(8-2*q)*b^2 :=
begin
  have d : q*a^2-2*q*a*b+(8-2*q)*b^2=q*(a-b)^2+(8-3*q)*b^2 := by ring,
  rw [d], exact add_nonneg (mul_nonneg hq.le (sq_nonneg _)) (mul_nonneg hsmall.le (sq_nonneg _))
end

theorem regular_character (a b c : ℝ) (re : 2*a-b-c=0) (im : b-c=0) :
  a=b ∧ b=c := ⟨by linarith, by linarith⟩

theorem clock_form_factor (k2 m2 s : ℝ) (h : k2+m2≠0) :
  1-s*m2/(k2+m2)=(k2+(1-s)*m2)/(k2+m2) := by { field_simp [h], ring }

theorem particle_source_and_clock (t g s a : ℝ) :
  (1-s*t)*(1-a*t)*g = g-g*(s+a)*t+g*s*a*t^2 := by ring

theorem slip_sensitivity (s : ℝ) (hs : 1-s≠0) :
  (1+s)/(1-s)-1=2*s/(1-s) := by { field_simp [hs], ring }

theorem susceptibility (slope kp mu m2 alpha : ℝ) (hm : m2≠0)
 (measured : slope=(mu^2*kp/m2)*alpha) : m2*slope=mu^2*kp*alpha :=
by { rw [measured], field_simp [hm], ring }

theorem force_density (beta enthalpy l2 planck sound slope : ℝ)
 (den : 1-sound≠0)
 (rel : (1-sound)*(beta*enthalpy*l2)=2*planck^2*sound*slope^2) :
 beta*enthalpy*l2=2*planck^2*sound*slope^2/(1-sound) :=
(eq_div_iff den).mpr (by linear_combination rel)

theorem quartic_force (planck s i r : ℝ) (hi : i≠0) (hr : r≠0) :
  (2*planck^2*s^2/(i*r^2))*(3*i*r^4/2)*(1/(4*r^2))=3*planck^2*s^2/4 :=
by { field_simp [hi,hr], ring }

theorem conformal_scale (r xi i v : ℝ) (hr : r≠0) (hx : xi≠0) :
  i*r^2/(xi*r^2)=i/xi ∧ v*r^4/(xi*r^2)^2=v/xi^2 :=
by { constructor; field_simp [hr,hx]; ring }

theorem rotating_branches (i b deriv mu : ℝ) (hi : i≠0) (hb : b≠0)
  (stationary : i*b*(2*b^2-mu^2)*deriv=0) : deriv=0 ∨ 2*b^2=mu^2 :=
begin
  rcases mul_eq_zero.mp stationary with h|h,
  { right, exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (mul_ne_zero hi hb)) },
  { exact or.inl h }
end

theorem decoupled_curvature (i b bp bpp mu : ℝ) (h : bp=0) :
 i*((6*b^2-mu^2)*bp^2+b*(2*b^2-mu^2)*bpp)=i*b*(2*b^2-mu^2)*bpp :=
by { rw [h], ring }

theorem equilibrium_clock_sensitivity (b mu db : ℝ) (hb : b≠0)
  (mass : 2*b^2=mu^2) (tangent : 2*b*db=mu) : (mu/b)*db=1 :=
begin
  have z : (2*b)*(mu*db-b)=0 := by linear_combination mu*tangent-mass,
  have q : mu*db=b := sub_eq_zero.mp ((mul_eq_zero.mp z).resolve_left (mul_ne_zero (by norm_num) hb)),
  field_simp [hb], exact q
end

theorem local_minimum_sign (i b d c : ℝ) (hi : 0<i) (hb : 0<b) (h : 0<d*c) :
  0<i*b*d*c := by { rw [mul_assoc (i*b) d c], exact mul_pos (mul_pos hi hb) h }

theorem hydrostatic_clock (k m2 phi u : ℝ) (h : k^2+m2≠0)
  (eqn : (k^2+m2)*u= -m2*phi) : phi+u=k^2*phi/(k^2+m2) :=
by { apply (eq_div_iff h).mpr, linear_combination eqn }

theorem instantaneous_source_pair (d a b k2 m2 : ℝ)
 (hd : d=k2+m2) :
 (d-a*m2)*(d-b*m2)=(1-a)*(1-b)*d^2+(a+b-a*b)*k2*d-a*b*m2*k2 :=
by { rw [hd], ring }

theorem product_shape_condition (l j u v t f fp : ℝ)
  (force : fp*(l+t*j)=f*j) (st : fp*(u+v*t^2)=f*v*t) (hf : f≠0) :
  j*u=l*v*t :=
begin
  have h : f*(j*u-l*v*t)=0 := by linear_combination (l+t*j)*st-(u+v*t^2)*force,
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hf)
end

theorem two_spheres_stationarity (t : ℝ) :
 (2*t^2+4*t-1)*(1+t^2)-t*(2*t^2+t+2)*(1+t)=(t-1)*(t^2-t+1) := by ring

theorem only_equal_sizes (t : ℝ) (h : (t-1)*(t^2-t+1)=0) : t=1 :=
begin
  have pos : 0<t^2-t+1 := by nlinarith [sq_nonneg (t-1/2)],
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (ne_of_gt pos))
end

theorem two_spheres_saddle : (2:ℝ)*((9/2)/15-(1/2)^2)=1/10 := by norm_num

theorem transverse_singlet (r b c : ℝ) :
  2*r^2+2*b^2-4*r*b*c=2*(r-b)^2+4*r*b*(1-c) := by ring

theorem accessible_gap (cut low high : ℝ) (h : max cut low<high) :
  cut<(max cut low+high)/2 ∧ low<(max cut low+high)/2 ∧ (max cut low+high)/2<high :=
begin
  have m : max cut low<(max cut low+high)/2 := by linarith,
  exact ⟨lt_of_le_of_lt (le_max_left _ _) m, lt_of_le_of_lt (le_max_right _ _) m, by linarith⟩
end

end cat_tetrahedral_radius
