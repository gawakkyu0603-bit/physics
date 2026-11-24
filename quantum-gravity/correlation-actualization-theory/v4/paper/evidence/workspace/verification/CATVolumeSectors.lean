import analysis.inner_product_space.basic
import number_theory.sum_two_squares
import tactic

noncomputable theory
namespace cat_volume_sectors

-- A contact that reads a difference is blind to a common displacement.
theorem common_shift {I : Type*} (u : I → ℝ) (x : ℝ) (i j : I) :
  (u i+x)-(u j+x)=u i-u j := by ring

theorem flux_F_term {F : Type*} [field F] (w dw dk : F)
  (hw : w=0) (hdw : dw=0) : dw+dk*w=0 := by simp [hw,hdw]

theorem doubling_radius (r : ℝ) (hr : r≠0) :
  1/(2*r)^4=(1/r^4)/16 := by field_simp; ring

theorem scalar_charge_and_time_delay :
  (2*(9/24):ℚ)=3/4 ∧ ((1-2*(9/24))/(1+2*(9/24)):ℚ)=1/7 := by norm_num

-- For G of type (2,1), a real restriction H=0 forces G and conjugate G
-- to be zero once their two distinct type subspaces are disjoint.
theorem pure_real_restriction {V : Type*} {s t : set V} {g : V} (zero : V)
  (both : ∀ v ∈ s, v ∈ t → v=zero) (hg : g ∈ s) (hbar : g ∈ t) : g=zero :=
both g hg hbar

theorem anti_linear_axis {V : Type*} [add_comm_group V] [module ℂ V]
  (j : V → V) (anti : ∀ (l : ℂ) v, j (l • v)=star l • j v)
  (l : ℂ) (v : V) (h : j v=l • v) : j (j v)=(star l*l) • v :=
by rw [h,anti,h,smul_smul]

theorem phase_denominator {F : Type*} [field F] (z zbar : F)
  (unit_norm : z*zbar=1) : z*(1+zbar)=1+z := by rw [mul_add,mul_one,unit_norm,add_comm]

-- Both components of (P+iQ)(x+iy) = (a+ib)(x-iy), written for
-- one row. Here px,py,qx,qy are the already contracted row entries.
theorem realified_row (px py qx qy x y a b : ℝ) :
  (px-qy=a*x+b*y ∧ py+qx=b*x-a*y) ↔
  (px-a*x-qy-b*y=0 ∧ qx-b*x+py+a*y=0) := by split; rintro ⟨h,k⟩; constructor; linarith

-- Clearing a candidate rational Gaussian norm of 3 yields an
-- impossible odd 3-adic valuation on a sum of two integer squares.
theorem three_not_rational_norm (x y d : ℕ) (hd : d≠0) :
  3*d^2≠x^2+y^2 :=
begin
  intro h,
  haveI : fact (nat.prime 3) := ⟨by norm_num⟩,
  have ev : even (padic_val_nat 3 (3*d^2)) :=
    nat.eq_sq_add_sq_iff.mp ⟨x,y,h⟩ (by norm_num) (by norm_num),
  rw [padic_val_nat.mul (by norm_num : (3:ℕ)≠0) (pow_ne_zero _ hd),
      padic_val_nat.pow 2 hd, padic_val_nat.self (by norm_num : 1<(3:ℕ))] at ev;
    try { apply_instance },
  rw [add_comm] at ev,
  exact (nat.odd_iff_not_even.mp (odd_two_mul_add_one _)) ev
end

theorem cofactor_first_variation (t x y z : ℝ) :
  (t+x)*(t+y)-t^2-x*y=t*(x+y+z-z) := by ring

theorem all_shape_directions {E : Type*} [normed_add_comm_group E]
  [inner_product_space ℝ E] (K : submodule ℝ E) (v : E) (hv : v ∈ K)
  (d : ∀ h ∈ K, @inner ℝ E _ h v=0) : v=0 :=
(@inner_self_eq_zero ℝ E _ _ _ v).mp (d v hv)

-- Single exponential at W0=0. A^2 exp(-2at) is positive and drops
-- out of this sign test on the derivative of the potential.
theorem one_term_slope (a t : ℝ) (ha : 0<a) (ht : 0<t) :
  -2*a*(a^2/(6*t)+a/(2*t^2))-(a^2/(6*t^2)+a/t^3)<0 :=
begin
  have h : 0<2*a*(a^2/(6*t)+a/(2*t^2))+(a^2/(6*t^2)+a/t^3) := by positivity,
  linarith [h]
end

theorem two_term_balance (a b t x y : ℝ) (h : 2*t≠0) :
  -a*x+b*y-3*(x-y)/(2*t)=0 ↔ (2*a*t+3)*x=(2*b*t+3)*y :=
by field_simp [h]; constructor; intro eq; linarith

theorem ratio_log_slope (a b t : ℝ) (h₁ : 2*a*t+3≠0) (h₂ : 2*b*t+3≠0) :
  (b-a)+2*a/(2*a*t+3)-2*b/(2*b*t+3)=
  (b-a)*(1-6/((2*a*t+3)*(2*b*t+3))) := by field_simp [h₁,h₂]; ring

theorem ratio_slope_positive (a b t : ℝ) (ha : 0<a) (hab : a<b) (ht : 0<t) :
  0<(b-a)*(1-6/((2*a*t+3)*(2*b*t+3))) :=
begin
  have hb : 0<b := lt_trans ha hab,
  have hp : 0<(2*a*t+3)*(2*b*t+3) := by positivity,
  have hbig : 6<(2*a*t+3)*(2*b*t+3) :=
    by nlinarith [mul_pos ha ht,mul_pos hb ht,mul_pos (mul_pos ha ht) (mul_pos hb ht)],
  exact mul_pos (sub_pos.mpr hab) (sub_pos.mpr ((div_lt_one hp).mpr hbig))
end

theorem stable_pair (z : ℝ) (hz : 2<z) :
  0<z^2-2-z ∧ 0<z^2-2+z :=
begin
  have hp : 0<(z-2)*(z+1) := mul_pos (by linarith) (by linarith),
  constructor; nlinarith
end

-- In an orthogonal divisor basis the direction equations express each
-- summand as c/k_i. The scale equation has the opposite sign. The
-- conclusion also holds for complex c by taking both real components.
theorem orthogonal_balance (p q r t c : ℝ) (hp : 0<p) (hq : 0<q)
  (hr : 0<r) (ht : 0<t) (eq : c*p+c*q+c*r= -t*c) : c=0 :=
begin
  have f : (p+q+r+t)*c=0 := by linear_combination eq,
  exact (mul_eq_zero.mp f).resolve_left (ne_of_gt (by linarith))
end

theorem five_divisor_equations {F : Type*} [field F] [char_zero F]
  (s c : F) (x y : F) (hx : x=-(2+2*s)*c) (hy : y=(3+2*s)*c/2) :
  x+2*y=c ∧ 2*y-2*y=0 ∧ 2*x+c+2*y= -2*s*c :=
by { rw [hx,hy], refine ⟨_,_,_⟩; ring }

-- In the even two-dimensional sector, z is a signed eigenvalue of
-- minus the canonical fermion matrix. The two diagonal entries exceed
-- 2 and its characteristic polynomial cannot vanish below 2.
theorem even_mass_bound (s z : ℝ) (hs : 2≤s)
  (eigen : (1+8*s+4*s^2-z)*(2*s-z)=2) : 2<z :=
begin
  by_contra h,
  have hz : z≤2 := le_of_not_gt h,
  have h₁ : 3≤1+8*s+4*s^2-z := by nlinarith [sq_nonneg s],
  have h₂ : 2≤2*s-z := by linarith,
  have hh := mul_le_mul h₁ h₂ (by norm_num : (0:ℝ)≤2)
                             (le_trans (by norm_num : (0:ℝ)≤3) h₁),
  linarith
end

theorem other_mass_bounds (s : ℝ) (hs : 2≤s) :
  2<(1+2*s)^2 ∧ 2<4*s*(3+2*s)-1 :=
by { constructor; nlinarith [sq_nonneg s] }

end cat_volume_sectors
