import analysis.special_functions.integrals
import data.real.sqrt
import tactic

noncomputable theory
namespace cat_charge_droplet

theorem half_turn_projection (a b c : ℝ) (ha : a= -a) (hb : b= -b) :
  a=0 ∧ b=0 ∧ c=c := ⟨by linarith,by linarith,rfl⟩

theorem projected_potential (x y h : ℝ) :
  (x*y)^2+(y*h)^2+(h*x)^2=h^2*(x^2+y^2)+x^2*y^2 := by ring

theorem flavour_mass_kernel (m x y : ℝ) (hm : m≠0)
  (kernel : m*y=0 ∧ m*x=0) : x=0 ∧ y=0 :=
⟨(mul_eq_zero.mp kernel.2).resolve_left hm,(mul_eq_zero.mp kernel.1).resolve_left hm⟩

theorem angular_gradient (x y dx dy : ℝ) :
  (x^2+y^2)*(dx^2+dy^2)-(x*dx+y*dy)^2=(x*dy-y*dx)^2 := by ring

theorem charged_kinetic (x y vx vy mu : ℝ) :
 vx^2+vy^2-2*mu*(x*vx-y*vy)+mu^2*(x^2+y^2)
 =(vx-mu*x)^2+(vy+mu*y)^2 := by ring

theorem angular_reduction (x y : ℝ) : 0≤x^2*y^2 :=
mul_nonneg (sq_nonneg x) (sq_nonneg y)

theorem matrix_radius (s c v : ℝ) (unit : s^2+c^2=1) :
  (v*s)^2+(v*c)^2=v^2 := by linear_combination v^2*unit

theorem commuting_core_wall (a b : ℝ) (sum_one : a+b=1) :
  a*b≤1/4 := by nlinarith [sq_nonneg (a-b),show (a+b)^2=1, by rw [sum_one]; norm_num]

theorem scalar_charge_ratio (m v p : ℝ) (hm : m≠0) (hv : v≠0) :
  (p^2*(m/v)^2)/m^2=p^2/v^2 := by { field_simp [hm,hv], ring }

theorem cassini_bound (b eps : ℝ) (hb : 0≤b) (he : eps<2) :
  2*b/(1+b)≤eps ↔ b≤eps/(2-eps) :=
begin
  rw [div_le_iff (show 0<1+b, by linarith),le_div_iff (sub_pos.mpr he)],
  split; intro h; linarith
end

theorem material_mass_slope (z d p : ℝ) (hz : 0<z) (hd : 0<1+d) :
  (2*(p-1/(1+d))^2) /
     (1/(z*(1+d))+6/(1+d)^2) =
  2*(p*(1+d)-1)^2/(6+(1+d)/z) :=
begin
  have h₁ : 0<1/(z*(1+d))+6/(1+d)^2 := by positivity,
  have h₂ : 0<6+(1+d)/z := by positivity,
  apply (div_eq_div_iff (ne_of_gt h₁) (ne_of_gt h₂)).mpr,
  field_simp [ne_of_gt hz,ne_of_gt hd], ring
end

theorem bare_force_interval (z d bound : ℝ) (hz : 0<z) (hd : 0<1+d) :
  2*d^2/(6+(1+d)/z) ≤ bound ↔ 2*d^2 ≤ bound*(6+(1+d)/z) :=
div_le_iff (by positivity)

theorem degenerate_sigma_potential (s c : ℝ) (unit : s^2+c^2=1) :
  8*(s^2/8-(1/2)*s^4/4)=s^2*c^2 :=
by linear_combination -s^2*unit

theorem minimal_bag_bound (pi v q r : ℝ) (hr : r≠0) :
 pi*q^2/r+4*pi*v^2*r-4*pi*v*q=pi*(q-2*v*r)^2/r :=
by { field_simp [hr], ring }

theorem scale_current (fr grad v lapf boxes : ℝ)
 (einstein : fr=grad+4*v+3*lapf) (scalar : boxes=4*v-fr) :
  grad+boxes+3*lapf=0 := by linarith

theorem sphere_metric (rho dr n d : ℝ) :
  (dr*n+rho*d)^2=dr^2*n^2+2*dr*rho*n*d+rho^2*d^2 := by ring

theorem homogeneous_units (s v mass f : ℝ) (hs : s≠0) (hf : f≠0) :
  (s*mass)^2/(s^2*f)=mass^2/f := by { field_simp [hs,hf], ring }

theorem quartic_units (s v f : ℝ) (hs : s≠0) (hf : f≠0) :
  s^4*v/(s^2*f)^2=v/f^2 := by { field_simp [hs,hf], ring }

theorem wall_completion (deriv s c m : ℝ) :
  deriv^2+m^2*s^2*c^2=(deriv-m*s*c)^2+2*m*s*c*deriv := by ring

theorem wall_cost (r p : ℝ) (hp : p*(p^2+1)≤35) :
  p*(p^2+1)*(r+1)^2≤35*(r+1)^2 := mul_le_mul_of_nonneg_right hp (sq_nonneg _)

theorem bound_below_free : 35*((16:ℝ)+1)^2+16384^2/(16*16^3)<16384 := by norm_num

theorem shell_balance (a b r : ℝ) (hr : r≠0) (eqn : 2*a*r^5=3*b) :
  b/r^3=2*a*r^2/3 :=
by { field_simp [hr], linear_combination -eqn }

theorem shell_stiffness (a b r : ℝ) (hr : r≠0) (eqn : 2*a*r^5=3*b) :
  2*a+12*b/r^5=10*a :=
by { field_simp [hr], linear_combination -4*eqn }

theorem wall_frequency (w r sig v : ℝ) (hv : v≠0) (hr : r≠0)
  (eqn : v^2*w^2*r=2*sig) : w^2=2*sig/(v^2*r) :=
by { apply (eq_div_iff (mul_ne_zero (pow_ne_zero _ hv) hr)).mpr, linear_combination eqn }

theorem pair_fission {a b c : ℝ} (ha : 0<a) (hb : 0<b) (hc : 0<c)
  (charge : c^5=a^5+b^5) : c^4<a^4+b^4 :=
begin
  have hac : a<c := lt_of_not_ge (λ h, by nlinarith only [pow_le_pow_of_le_left hc.le h 5,
    charge,pow_pos hb 5]),
  have hbc : b<c := lt_of_not_ge (λ h, by nlinarith only [pow_le_pow_of_le_left hc.le h 5,
    charge,pow_pos ha 5]),
  apply (lt_of_mul_lt_mul_left _ hc.le),
  nlinarith only [charge,mul_pos (pow_pos ha 4) (sub_pos.mpr hac),
    mul_pos (pow_pos hb 4) (sub_pos.mpr hbc)]
end

theorem angular_hessian (p s th : ℝ) :
  p^2+2*p*s*th+s^2*th^2=(p+s*th)^2 := by ring

theorem thin_surface_instability_test (l coeff wave : ℝ)
 (h : 2≤l) (hc : 0<coeff) (hw : 0<wave) :
  0<(l-2+wave^2)*coeff := mul_pos (by nlinarith [sq_pos_of_pos hw]) hc

theorem breathing_imaginary (z v d : ℝ) (hz : 0<z) (hv : 0<v) (hd : 0≤d)
 (ub : 3*d≤z*v) : 0<(z^2-2)*d+4*z*v :=
by nlinarith [mul_nonneg (sq_nonneg z) hd,mul_pos hz hv]

theorem angular_stress (u : ℝ) :
  6*(1-u^2)^2-8*(1-u^2)-((1-u^2)^2-4*u^2*(1-u^2))
  = -(1-u^2)*(3+u^2) := by ring

theorem positive_gravitational_integrand (u c : ℝ) (hu : u^2<1) (hc : 0<c) :
  0<(1-u^2)*(3+u^2)*c :=
mul_pos (mul_pos (sub_pos.mpr hu) (by nlinarith [sq_nonneg u])) hc

theorem adm_variation (w b v dk ddk db dv ddb ddv : ℝ) :
 w*(ddb+ddv-2*(db+dv)*dk+(b+v)*(dk^2-ddk))=
 w*(ddb+ddv)-2*w*(db+dv)*dk+w*(b+v)*dk^2-w*(b+v)*ddk := by ring

theorem mass_compactness (e r g n : ℝ) (hr : r≠0) (hn : n=1-2*g*e/r) :
 (1-n)*r=2*g*e := by { rw [hn], field_simp [hr] }

theorem flux_tail (a d negexp : ℝ) (hd : d≠0) :
  2*d*(a*negexp/(d/2))^2=8*a^2*negexp^2/d := by { field_simp [hd], ring }

theorem exchange_sign (curv coupling : ℝ) (hc : curv<0) (hj : 0<coupling) :
  0< -(2*curv*coupling) := neg_pos.mpr (mul_neg_of_neg_of_pos (by linarith) hj)

theorem lapse_step (curv j rate2 q mu phi shape : ℝ)
  (h : rate2= -2*curv*j) (e : rate2*q= -j*mu*phi*shape) (hj : j≠0) :
  2*curv*q=mu*phi*shape :=
begin
  have k : j*(2*curv*q-mu*phi*shape)=0 := by linear_combination -e+q*h,
  exact sub_eq_zero.mp ((mul_eq_zero.mp k).resolve_left hj)
end

theorem vacuum_threshold (xi lam v : ℝ) :
  4*(xi-1/6)*(lam*v)^2-4*(1/4-1/6)*(lam*v)^2=4*(xi-1/4)*(lam*v)^2 := by ring

theorem threshold_slope (l xi : ℝ) :
  2*l*xi+4*l*(xi-1/4)=l*(6*xi-1) := by ring

theorem electric_energy_ratio (g q v r p : ℝ)
  (hq : q≠0) (hv : v≠0) (hr : r≠0) (hp : p≠0) :
  (g^2*q^2/(8*p*r))/(3*q^2/(16*p*v^2*r^3))=2*(g*v*r)^2/3 :=
by { field_simp [hq,hv,hr,hp], ring }

theorem compact_mass_in_gravity_units (t h mu c p : ℝ)
  (ht : t≠0) (hh : h≠0) (hc : c≠0) (hp : p≠0) :
  (mu*t/h)^2/(2*c^2*t^2/(p^3*h^2))=p^3*mu^2/(2*c^2) :=
by { field_simp [ht,hh,hc,hp], ring }

theorem radial_curvature (a b t : ℝ) (balance : b=2*a*t^2) :
  12*a*t^2-2*b=8*a*t^2 := by rw [balance]; ring

theorem ordered_factors (x y u v : ℝ) (hx : u*x=1) (hy : v*y=1) :
  (v-u)*(x^3*y+x^2*y^2+x*y^3)=x^3-y^3 :=
by linear_combination (x^3+x^2*y+x*y^2)*hy-(x^2*y+x*y^2+y^3)*hx

theorem spin_shear_lower_bound (c : ℝ) (hc : 2≤c) :
  1/2 ≤ (8-4/c)*(4*c-3)/(30*c) :=
begin
  have posc : 0<c := by linarith,
  apply (le_div_iff (show 0<30*c, by positivity)).mpr,
  field_simp [posc.ne'],
  apply (le_div_iff posc).mpr,
  nlinarith [mul_nonneg (show 0≤c-2, by linarith) (show 0≤17*c-6, by linarith)]
end

theorem shape_saddle (k : ℝ) (hk : 1/2≤k) : 2/3-2*k≤ -(1/3) := by linarith

end cat_charge_droplet
