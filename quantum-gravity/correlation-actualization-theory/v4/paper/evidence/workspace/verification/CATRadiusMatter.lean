import data.complex.basic
import analysis.special_functions.log.deriv
import linear_algebra.dual
import tactic

noncomputable theory
open_locale big_operators
namespace cat_radius_matter

-- In a unitary frame the bottom scalar and the upper two-by-two minor
-- are the two harmonic lift tests for a primitive admissible line.
theorem lift_blocks {F : Type*} [field F] (a b d s : F)
  (h : s*(a*d-b*b)≠0) : s≠0 ∧ a*d-b*b≠0 :=
⟨λ hs, h (by simp [hs]), λ hd, h (by simp [hd])⟩

theorem unequal_takagi_axes (a b x y : ℝ) (ha : 0<a) (hb : 0<b) (hab : a≠b)
  (re : a*x=b*x) (im : a*y= -b*y) : x=0 ∧ y=0 :=
begin
  have hx : (a-b)*x=0 := by linear_combination re,
  have hy : (a+b)*y=0 := by linear_combination im,
  exact ⟨(mul_eq_zero.mp hx).resolve_left (sub_ne_zero.mpr hab),
         (mul_eq_zero.mp hy).resolve_left (ne_of_gt (by linarith))⟩
end

theorem isolated_exponential {F : Type*} [field F] (a q coeff : F)
  (ha : a≠0) (hq : q≠0) (stationary : -a*coeff*q=0) : coeff=0 :=
(mul_eq_zero.mp ((mul_eq_zero.mp stationary).resolve_right hq)).resolve_left (neg_ne_zero.mpr ha)

theorem primitive_axis_flat {P : Type*} (plane : P → ℂ) (a b t : ℂ) (ha : a≠0)
  (eq : -a*b*complex.exp (-a*t)=0) : ∀ (p : P) (v w : ℂ),
  plane p+b*complex.exp (-a*v)=plane p+b*complex.exp (-a*w) :=
begin
  have hb := isolated_exponential a _ b ha (complex.exp_ne_zero _) eq,
  intros, simp [hb]
end

-- x,y,z denote the three eigenvalues of A A†; this polynomial identity
-- and positivity do not require independent scanning of complex directions.
theorem curvature_trace (x y z : ℝ) :
  (x+y+z)^2 ≤ 3*(x^2+y^2+z^2) :=
by nlinarith [sq_nonneg (x-y),sq_nonneg (x-z),sq_nonneg (y-z)]

theorem curvature_bound (x y z : ℝ) (h : 0<x+y+z) :
  (2/3 : ℝ) ≤ 2*(x^2+y^2+z^2)/(x+y+z)^2 :=
begin
  apply (le_div_iff (pow_pos h 2)).mpr,
  linarith [curvature_trace x y z]
end

theorem projected_mass (r v m : ℝ) (h : 2/3≤r) (f : 0≤v+3*m) :
  2*m-r*(v+3*m) ≤ -2*v/3 :=
by nlinarith [mul_nonneg (sub_nonneg.mpr h) f]

theorem determinant_sector (s l : ℝ) (hs : 2≤s) (hl : l<2*s) :
  29≤1+8*s+4*s^2-l := by nlinarith [sq_nonneg (s-2)]

theorem light_charge_lower (k : ℝ) (hk : 29≤k) :
  (1/5 : ℝ)<(k-2)^2/(4*(k^2+2)) :=
begin
  apply (lt_div_iff (by positivity : 0<4*(k^2+2))).mpr,
  nlinarith [sq_nonneg (k-29)]
end

theorem mass_upper (l s : ℝ) (hl : 2<l) (hs : l<2*s) :
  l^2+l-2 < (2*s+1/2)^2 :=
begin
  have p : 0<(2*s-l)*(2*s+l+1) := mul_pos (by linarith) (by linarith),
  have id : (2*s+1/2)^2-(l^2+l-2)=(2*s-l)*(2*s+l+1)+9/4 := by ring,
  have h : 0<(2*s+1/2)^2-(l^2+l-2) := by { rw [id], linarith },
  exact sub_pos.mp h
end

theorem warped_charge (t : ℝ) (ht : 0≤t) :
  (1/3 : ℝ) ≤ 2*(2/3)*(1/2+t/4)^2 :=
begin
  have id : 2*(2/3)*(1/2+t/4)^2-1/3=t^2/12+t/3 := by ring,
  have h : 0≤2*(2/3)*(1/2+t/4)^2-1/3 := by { rw [id], positivity },
  exact sub_nonneg.mp h
end

theorem string_warp_factors (weyl warp dl : ℝ) (h : warp≠0) :
  (weyl/warp)*(warp*dl)=weyl*dl := by field_simp [h]; ring

theorem time_delay (b : ℝ) (hb : 1/3≤b) : (1-b)/(1+b)≤1/2 :=
by { apply (div_le_iff (by linarith : 0<1+b)).mpr, linarith }

theorem negative_wrap_curvature (weight delta denom : ℝ)
  (hw : 0≤weight) (hd : 0<denom) : -(weight*delta^2)/(4*denom)≤0 :=
div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg hw (sq_nonneg _))) (by positivity)

-- Euler's identity at a critical point of a linear-plus-quadratic W.
-- l is a^t x, q=x^t M x, c=a^t M^{-1}a.
theorem quadratic_value {F : Type*} [field F] [char_zero F] (l q c : F)
  (critical : l+2*q=0) (inverse : 2*l= -c) : l+q= -c/4 :=
by linear_combination critical/2 + inverse/4

-- M identifies the tangent space with its complex dual; for symmetric M
-- the differential of the quadratic term at x is 2 M x.
theorem quadratic_minkowski {V : Type*} [add_comm_group V] [module ℂ V]
  (M : V ≃ₗ[ℂ] (V →ₗ[ℂ] ℂ)) (p : V →ₗ[ℂ] ℂ) (x : V) :
  (p+(2:ℂ) • M x=0 ∧ p x+(M x) x=0) ↔
  (x=(-1/2:ℂ) • M.symm p ∧ p (M.symm p)=0) :=
begin
  have grad : p+(2:ℂ) • M x=0 ↔ x=(-1/2:ℂ) • M.symm p,
  { split,
    { intro h, apply M.injective,
      simp only [map_smul, M.apply_symm_apply], apply linear_map.ext, intro v,
      have hv := congr_arg (λ n : V →ₗ[ℂ] ℂ, n v) h,
      change p v+2*((M x) v)=0 at hv,
      change (M x) v=(-1/2:ℂ)*(p v),
      linear_combination hv/2 },
    { intro hx, rw [hx], apply linear_map.ext, intro v,
      simp only [map_smul,M.apply_symm_apply,linear_map.add_apply,linear_map.smul_apply,
                 linear_map.zero_apply,smul_eq_mul], ring } },
  rw [grad], apply and_congr_right, intro hx,
  have ev : p x+(M x) x=(-1/4:ℂ)*p (M.symm p) :=
  by { rw [hx], simp only [map_smul,M.apply_symm_apply,linear_map.smul_apply,smul_eq_mul], ring },
  rw [ev,mul_eq_zero], norm_num
end

theorem static_log_mass (c h mean : ℝ) (ha : c+h≠0) (hb : c+mean≠0) :
  has_deriv_at (λ t : ℝ, -(1/2:ℝ)*real.log (t+mean)-(1/4:ℝ)*real.log (t+h))
    (-(1/2:ℝ)/(c+mean)-(1/4:ℝ)/(c+h)) c :=
begin
  have p := ((has_deriv_at_id c).add_const mean).log hb,
  have q := ((has_deriv_at_id c).add_const h).log ha,
  convert (p.const_mul (-(1/2:ℝ))).sub (q.const_mul (1/4:ℝ)) using 1;
    dsimp; ring
end

theorem six_discriminant {F : Type*} [field F] (a b c d p m l : F)
  (branch : l^2=p*m) (balance : 2*d*a*b+l*c^2=0) :
  4*d^2*a^2*b^2=p*m*c^4 :=
begin
  have h : 2*d*a*b= -(l*c^2) := by linear_combination balance,
  calc 4*d^2*a^2*b^2 = (2*d*a*b)^2 : by ring
  ... = (-(l*c^2))^2 : by rw [h]
  ... = l^2*c^4 : by ring
  ... = p*m*c^4 : by rw [branch]
end

theorem six_critical {F : Type*} [field F] [char_zero F] (a b c d l x y z : F)
  (hl : l≠0) (hd : d≠0)
  (h₁ : a+2*l*y=0) (h₂ : b+2*l*x=0) (h₃ : c+2*d*z=0) :
  a*x+b*y+c*z+2*l*x*y+d*z^2=0 ↔ 2*d*a*b+l*c^2=0 :=
begin
  have ha : a= -2*l*y := by linear_combination h₁,
  have hb : b= -2*l*x := by linear_combination h₂,
  have hc : c= -2*d*z := by linear_combination h₃,
  have factor : 2*d*a*b+l*c^2= -4*d*l*(a*x+b*y+c*z+2*l*x*y+d*z^2) :=
    by { rw [ha,hb,hc], ring },
  rw [factor, mul_eq_zero],
  have nz : -4*d*l≠0 := mul_ne_zero (mul_ne_zero (by norm_num) hd) hl,
  tauto
end

theorem six_contributions {F : Type*} [field F] (v : F) :
  (-2*v)+(-2*v)+4*v+v+v-2*v=0 ∧
  -2*v+v+v=0 ∧ 4*v+2*(-2*v)=0 ∧ 2*v-2*v=0 :=
by { refine ⟨_,_,_,_⟩; ring }

theorem determinant_character {F : Type*} [field F] (t d : F)
  (ht : t≠0) (hd : d≠0) (eq : t^2*d=t^3*d) : t=1 :=
begin
  have factor : (t^2*d)*(t-1)=0 := by linear_combination -eq,
  exact sub_eq_zero.mp ((mul_eq_zero.mp factor).resolve_left (mul_ne_zero (pow_ne_zero 2 ht) hd))
end

theorem symmetric_sizes {F : Type*} [field F] (m c x y : F)
  (ha : m-c≠0) (grad : m*x+c*y=c*x+m*y) : x=y :=
begin
  have factor : (m-c)*(x-y)=0 := by linear_combination grad,
  exact sub_eq_zero.mp ((mul_eq_zero.mp factor).resolve_left ha)
end

theorem transverse_radius_ratio {F : Type*} [field F] (p q x z b : F)
  (hq : q≠0) (hx : x≠0) (w : 2*p*x+q*z+b=0) (dw : 2*p*x+q*z+2*b=0) :
  z/x= -2*p/q :=
begin
  field_simp [hx,hq],
  linear_combination 2*w-dw
end

theorem mass_mismatch_leading (e s : ℝ) (hs : s≠0) :
  (2*e)/(8*s^2)=e/(4*s^2) := by field_simp [hs]; ring

theorem heavy_elimination {F : Type*} [field F] [char_zero F]
  (h v x : F) (hh : h≠0) (e : h*x+v=0) :
  h*x^2/2+v*x= -v^2/(2*h) :=
begin
  have hv : v= -h*x := by linear_combination e,
  rw [hv], field_simp [hh], ring
end

theorem common_prefactor_obstruction {F : Type*} [field F] [char_zero F]
  (c f a l y : F) (hc : c≠0) (hl : l≠0) (hy : y≠0)
  (e₃ : c*f=0) (e₁ : a*f+2*l*y=0) : false :=
begin
  have hf := (mul_eq_zero.mp e₃).resolve_left hc,
  rw [hf,mul_zero,zero_add] at e₁,
  exact (mul_ne_zero (mul_ne_zero (by norm_num) hl) hy) e₁
end

theorem disconnected_pair (p : ℚ) : p^2/2 - p^2/2=0 := sub_self _

theorem matrix_mass_ratio (k h m rho ell : ℝ) (hk : k≠0) (hm : m≠0) (hr : rho≠0) :
  (h/(k*(m/rho)^2))*(ell*(m/rho)^2)=h*ell/k :=
by field_simp [hk,hm,hr]; ring

theorem matrix_scale_minimum (a b m s : ℝ) (hb : 0<b) (hs : s^2=a/(2*b)) :
  -a*m^2+b*m^4-(-a*s^2+b*s^4)=b*(m^2-s^2)^2 :=
begin
  have h : s^2*(2*b)=a := (eq_div_iff (ne_of_gt (by linarith))).mp hs,
  rw [←h], ring
end

theorem magnetic_moments (n : ℕ) :
  6*(∑ j in finset.range (n+1), (j:ℚ)^2)=(n:ℚ)*(n+1)*(2*n+1) ∧
  30*(∑ j in finset.range (n+1), (j:ℚ)^4)=(n:ℚ)*(n+1)*(2*n+1)*(3*(n:ℚ)^2+3*n-1) :=
begin
  induction n with n ih,
  { norm_num },
  { rcases ih with ⟨h₂,h₄⟩, constructor,
    { rw [finset.sum_range_succ], push_cast, linear_combination h₂ },
    { rw [finset.sum_range_succ], push_cast, linear_combination h₄ } }
end

theorem axial_variance (L : ℝ) (hL : 2≤L) :
  2≤4-24/3+36*((3*L-1)/(15*L)) :=
begin
  have hpos : 0<15*L := by linarith,
  have h :  (1:ℝ)/6 ≤ (3*L-1)/(15*L) :=
    (le_div_iff hpos).mpr (by linarith),
  linarith
end

theorem axial_saddle (w : ℝ) (hw : 2≤w) : -(2*(4*w)-8)/4 ≤ -2 := by linarith

theorem rotating_charge_balance (r q : ℝ) (hr : r≠0) :
  -q^2/r^3+2*r^3=0 ↔ q^2=2*r^6 :=
by { field_simp [hr], split; intro h; linear_combination -h }

theorem rotating_hessian (r x y z : ℝ) :
  r^2*(8*(x^2+y^2+z^2)+4*(x*y+y*z+z*x))=
  6*r^2*(x^2+y^2+z^2)+2*r^2*(x+y+z)^2 := by ring

theorem fixed_charge_slope (m chi c deriv : ℝ) (hc : c≠0)
  (slope : m= -(1/2:ℝ)*(deriv/c)*(-3*chi)) : m=3*chi*deriv/(2*c) :=
by { rw [slope], field_simp [hc], ring }

-- x=k²/r², y=frequency²/r². The rotating-shape determinant has
-- this root for positive as well as negative values of y.
theorem shape_dispersion (x b : ℝ) (hb : b^2=9+8*x) :
  (x-2-(x+3-b))*(x-(x+3-b))-8*(x+3-b)=0 := by linear_combination hb

theorem shape_unstable_band (x : ℝ) (hx : 0<x) (hu : x<2) :
  x+3-real.sqrt (9+8*x)<0 :=
begin
  have difference : 9+8*x-(x+3)^2=x*(2-x) := by ring,
  have positive : 0<9+8*x-(x+3)^2 := difference.symm ▸ (mul_pos hx (sub_pos.mpr hu)),
  have strict : (x+3)^2<9+8*x := sub_pos.mp positive,
  exact sub_neg.mpr (real.lt_sqrt_of_sq_lt strict)
end

theorem fastest_shape_growth (x : ℝ) (hx : 0≤x) :
  -(1/8:ℝ)≤x+3-real.sqrt (9+8*x) :=
begin
  have pos : 0≤x+25/8 := by linarith,
  have difference : (x+25/8)^2-(9+8*x)=(x-7/8)^2 := by ring,
  have bound : 9+8*x≤(x+25/8)^2 := sub_nonneg.mp (difference.symm ▸ sq_nonneg (x-7/8)),
  have root_bound := (real.sqrt_le_left pos).mpr bound,
  linarith only [root_bound]
end

theorem peak_attained : (7/8:ℝ)+3-real.sqrt (9+8*(7/8))= -1/8 :=
begin
  have root : real.sqrt 16=(4:ℝ) :=
    (real.sqrt_eq_iff_sq_eq (show (0:ℝ)≤16, by norm_num)
      (show (0:ℝ)≤4, by norm_num)).mpr (by norm_num),
  norm_num, rw [root], norm_num
end

theorem shape_stiffness (delta : ℝ) : 0≤ -2+delta ↔ 2≤delta := by split; intro h; linarith

end cat_radius_matter
