import measure_theory.integral.fund_thm_calculus
import analysis.calculus.deriv.inv
import analysis.inner_product_space.basic
import analysis.special_functions.trigonometric.deriv
import analysis.special_functions.pow.deriv
import tactic

noncomputable theory
open measure_theory
open_locale interval
namespace landscape_receipts

theorem metric_density (N a b c : ℝ) (hN : N≠0) (ha : a≠0) (hb : b≠0) (hc : c≠0) :
 (a*b*c/N)*(N*b*c/a)*(N*a*c/b)*(N*a*b/c)=(N*a*b*c)^2 :=
by field_simp;ring
theorem metric_inverse (N a b c : ℝ) (hN : N≠0) (ha : a≠0) (hb : b≠0) (hc : c≠0) :
 (N*a*b*c)/(a*b*c/N)=N^2 ∧ (N*a*b*c)/(N*b*c/a)=a^2 :=
by split;field_simp;ring
theorem polynomial_sector (p : ℝ) (hp : p+2≠0) :
 (p/2)/(1+p/2)=p/(p+2) :=
begin have h : 1+p/2≠0 := by intro h;apply hp;linarith,
 apply (div_eq_div_iff h hp).mpr,ring,end
theorem sectors : ((2:ℝ)/(2+2)=1/2) ∧ ((4:ℝ)/(4+2)=2/3) := by norm_num
theorem nonaccelerating (p : ℝ) (h : 0≤p) : p/(p+2)<1 :=
by apply (div_lt_one (show 0<p+2,by linarith)).mpr;linarith
theorem link_additive (W : ℝ → ℝ) (a b c k : ℝ)
 (hab : interval_integrable W volume a b) (hbc : interval_integrable W volume b c)
 (la ta tb tc : ℝ) :
 (la*(tb-ta)-k*(∫ u in a..b, W u))+(la*(tc-tb)-k*(∫ u in b..c, W u))
 = la*(tc-ta)-k*(∫ u in a..c, W u) :=
begin rw [←interval_integral.integral_add_adjacent_intervals hab hbc];ring,end
theorem vary_internal_time (l r x : ℝ) :
 has_deriv_at (λ t : ℝ, l*t+r*(x-t)) (l-r) x :=
begin
 convert ((has_deriv_at_id x).const_mul l).add (((has_deriv_at_const x x).sub (has_deriv_at_id x)).const_mul r) using 1;simp;ring,
end
theorem volume_constraint (u v H m r L : ℝ) (ha : u≠0) (hb : v≠0)
 (hw : 4*v^2=3*(L*u^2+m+r)) (hh : 3*u*H=2*v) :
 3*H^2=L+(m+r)/u^2 :=
begin
 have ht : (3*u*H)^2=(2*v)^2 := congr_arg (λ x : ℝ,x^2) hh,
 field_simp [ha],linear_combination (ht+hw)/3,
end
theorem junction (m q r a f : ℝ) :
 (m-f*m)*a+(r+f*m*a)=m*a+r := by ring
theorem slopes (m f a b : ℝ) :
 (1-f)*m*b+f*m*a=m*b-f*m*(b-a) := by ring
theorem intercept (m f a : ℝ) : a*(m-(1-f)*m)=f*m*a := by ring
theorem normalization (m f a : ℝ) :
 1-m*(1-f*(1-a))+(1-f)*m+f*m*a=1 := by ring
theorem one_port (F : ℝ) (h : 0≤F) (h1 : F≤1) : 0≤F/2 ∧ F/2≤1/2 := by split;linarith
theorem half_deceleration (m r d q : ℝ) (hm : 0≤m) (hr : 0≤r)
 (hd : d=m+r) (hp : 0<d) (hq : 2*d*q=m+2*r) : 1/2≤q :=
begin by_contra n,push_neg at n,nlinarith [mul_pos hp (sub_pos.mpr n)],end

-- With y=sqrt(1+z'), the premise is the integrated expansion-rate comparison.
theorem distance_floor (s : ℝ) (h1 : 1≤s) (rate : ℝ → ℝ)
 (hreg : interval_integrable (λ y : ℝ,2*y*rate s/rate y) volume 1 s)
 (h : ∀ (y : ℝ), y∈set.Icc (1:ℝ) s → 2*s^3/y^2 ≤ 2*y*rate s/rate y) :
 2*s^2*(s-1)≤∫ y in (1:ℝ)..s,2*y*rate s/rate y :=
begin
 have hp : ∀ (y : ℝ), y∈set.uIcc (1:ℝ) s → y≠0 :=
 begin intros y hy,rw [set.uIcc_of_le h1] at hy,exact ne_of_gt (lt_of_lt_of_le zero_lt_one hy.1),end,
 have hc : continuous_on (λ y : ℝ,2*s^3/y^2) (set.uIcc 1 s) :=
   continuous_on_const.div (continuous_id.pow 2).continuous_on
   (λ y hy,pow_ne_zero 2 (hp y hy)),
 have hi : interval_integrable (λ y : ℝ,2*s^3/y^2) volume 1 s := hc.interval_integrable,
 have hd : ∀ (y : ℝ), y∈set.uIcc (1:ℝ) s →
  has_deriv_at (λ t : ℝ,-(2*s^3)*t⁻¹) (2*s^3/y^2) y :=
 begin intros y hy, convert (has_deriv_at_inv (hp y hy)).const_mul (-(2*s^3)) using 1;
       simp;field_simp;ring, end,
 have key := interval_integral.integral_mono_on h1 hi hreg h,
 rw [interval_integral.integral_eq_sub_of_has_deriv_at hd hi] at key,
 have hs : s≠0 := by linarith,
 convert key using 1;field_simp;ring,
end

theorem ap_lower_arithmetic (s : ℝ) (h : 139/100≤s) :
 (150:ℝ)/100 < 2*(1934/1000)*(s-1) := by linarith
theorem ap_excluded : ((150:ℝ)/100-1223/1000)/(19/1000)>14 := by norm_num
theorem vacuum_mass (r m l u : ℝ) (hr : r≠0) (hu : r*u^2-l*r^3/3=2*m) :
 1-u^2=1-2*m/r-l*r^2/3 := by field_simp;nlinarith
theorem critical_horizon (r m l : ℝ) (h : l*r^3=3*m) (hr : r≠0) :
 1-2*m/r-l*r^2/3=1-l*r^2 :=
by field_simp;nlinarith
theorem common_pivot (m l : ℝ) (hm : m≠0) :
 1-2*m/(3*m)-l*(3*m)^2/3=(1-9*l*m^2)/3 := by field_simp;ring
theorem observer_bound (l r m : ℝ) (hr : 0<r) (h : l*r/3<m/r^2) : l*r^3<3*m :=
begin
 have q := (lt_div_iff (sq_pos_of_pos hr)).mp h,
 nlinarith,
end
theorem pair_ladder (n : ℝ) : (n+1)^2-n^2=2*(n+1/2) := by ring

theorem form_identity (v x z : ℝ) :
 2*v-2*z*x=z*(2*v-2*x)+2*(1-z)*v := by ring

theorem geometric_release (v x z p : ℝ) (h : p=(1-z)/2) :
 2*v-2*z*x=(1-2*p)*(2*v-2*x)+4*p*v := by rw [h];ring

theorem mean_equation (v x z A : ℝ) :
 2*z*(A*x+2*z*v)=(4*z^2-A^2)*v+A*(A*v+2*z*x) := by ring

theorem count_first_integral (n d dd k z : ℝ) (h : dd=k*n+2*z^2) :
 2*d*dd-2*k*n*d-4*z^2*d=0 := by rw [h];ring

theorem hyperbolic_branch (z l : ℝ) (hz : 0≤z) :
 0<4*z^2-(l-2)^2 ↔ 2*(1-z)<l ∧ l<2*(1+z) :=
begin
 have fac : 4*z^2-(l-2)^2=(l-2*(1-z))*(2*(1+z)-l) := by ring,
 rw [fac,mul_pos_iff],split,
 { rintro (h|h), {split;linarith [h.1,h.2]}, {exfalso;linarith [h.1,h.2]} },
 { rintro ⟨h1,h2⟩,left,split;linarith },
end

theorem friedmann_from_count (n d k z H : ℝ) (hn : n≠0)
 (h : d^2=k*n^2+4*z^2*n) (hh : 3*n*H=d) :
 9*H^2=k+4*z^2/n :=
begin
 rw [←hh] at h,
 have he : n*(9*H^2*n-k*n-4*z^2)=0 := by nlinarith only [h],
 have hr := (mul_eq_zero.mp he).resolve_left hn,
 field_simp [hn]; nlinarith only [hr],
end

theorem empty_shift (v b k z : ℝ) (hv : v≠0) :
 (k*(v-b)^2+4*z^2*(v-b))/v^2=k+(4*z^2-2*k*b)/v+(k*b^2-4*z^2*b)/v^2 :=
by field_simp;ring

theorem empty_redshift (n b q : ℝ) (hq : 1<q) (past : b*q≤n+b) :
 b≤n/(q-1) := by apply (le_div_iff (sub_pos.mpr hq)).mpr;nlinarith

theorem independent_volume_variance (P n : ℝ) (hp : P≠0) (hn : n≠0) :
 (P*n*(1+n))/(P*n)^2=(1+1/n)/P := by field_simp;ring
theorem flat_band (f m a b L limit : ℝ) (hL : 0<L) (hm : 0<m) (hf : 0<f) (ha : 0<a)
 (bound : b*f*m*a/L≤limit) : b≤limit*L/(f*m*a) :=
begin
 apply (le_div_iff (mul_pos (mul_pos hf hm) ha)).mpr,
 have hh := (div_le_iff hL).mp bound,nlinarith,
end


-- Exact clock-time solutions with the vacuum initial data.  w^2 is |K|.
theorem count_growing (w z t : ℝ) (hw : w≠0) :
 let N := λ s : ℝ, (2*z^2/w^2)*(real.cosh (w*s)-1),
     D := λ s : ℝ, (2*z^2/w)*real.sinh (w*s) in
 has_deriv_at N (D t) t ∧ has_deriv_at D (w^2*N t+2*z^2) t ∧ N 0=0 ∧ D 0=0 :=
begin
 dsimp only,
 have ht : has_deriv_at (λ s : ℝ, w*s) w t := by simpa using (has_deriv_at_id t).const_mul w,
 refine ⟨_,_,by simp,by simp⟩,
 { convert (ht.cosh.sub_const 1).const_mul (2*z^2/w^2) using 1;field_simp [hw];ring },
 { convert ht.sinh.const_mul (2*z^2/w) using 1;field_simp [hw];ring },
end

theorem count_oscillating (w z t : ℝ) (hw : w≠0) :
 let N := λ s : ℝ, (2*z^2/w^2)*(1-real.cos (w*s)),
     D := λ s : ℝ, (2*z^2/w)*real.sin (w*s) in
 has_deriv_at N (D t) t ∧ has_deriv_at D (-(w^2)*N t+2*z^2) t ∧ N 0=0 ∧ D 0=0 :=
begin
 dsimp only,
 have ht : has_deriv_at (λ s : ℝ, w*s) w t := by simpa using (has_deriv_at_id t).const_mul w,
 refine ⟨_,_,by simp,by simp⟩,
 { convert ((has_deriv_at_const t (1:ℝ)).sub ht.cos).const_mul (2*z^2/w^2) using 1;field_simp [hw];ring },
 { convert ht.sin.const_mul (2*z^2/w) using 1;field_simp [hw];ring },
end

theorem count_critical (z t : ℝ) :
 has_deriv_at (λ s : ℝ, z^2*s^2) (2*z^2*t) t ∧
 has_deriv_at (λ s : ℝ, 2*z^2*s) (2*z^2) t :=
begin
 split,
 { convert ((has_deriv_at_id t).pow 2).const_mul (z^2) using 1;simp;ring },
 { simpa using (has_deriv_at_id t).const_mul (2*z^2) },
end

theorem hyperbolic_half_angle (x : ℝ) :
 real.cosh (2*x)-1=2*(real.sinh x)^2 :=
by rw [real.cosh_two_mul]; linarith only [real.cosh_sq_sub_sinh_sq x]

theorem circular_half_angle (x : ℝ) :
 1-real.cos (2*x)=2*(real.sin x)^2 :=
by rw [real.cos_two_mul']; linarith only [real.sin_sq_add_cos_sq x]

theorem vacuum_first_integral (N D : ℝ → ℝ) (k z : ℝ)
 (hN : ∀ t, has_deriv_at N (D t) t) (hD : ∀ t, has_deriv_at D (k*N t+2*z^2) t)
 (n0 : N 0=0) (d0 : D 0=0) (t : ℝ) :
 (D t)^2=k*(N t)^2+4*z^2*(N t) :=
begin
 let E := λ s : ℝ, (D s)^2-k*(N s)^2-4*z^2*N s,
 have he : ∀ s, has_deriv_at E 0 s,
 { intro s, dsimp only [E],
   convert (((hD s).pow 2).sub (((hN s).pow 2).const_mul k)).sub ((hN s).const_mul (4*z^2)) using 1;simp;ring },
 have hc := is_const_of_deriv_eq_zero (λ s,(he s).differentiable_at) (λ s,(he s).deriv) t 0,
 dsimp [E] at hc,rw [n0,d0] at hc,linarith,
end


-- The inner product is that of the sequences of weighted purification vectors.
section purification
variables {E : Type*} [normed_add_comm_group E] [inner_product_space ℂ E]

theorem purification_deficit (W U : E) (n S : ℝ)
 (hw : ‖W‖^2=n+1) (hu : ‖U‖^2=n)
 (hs : S=(n+1/2)^2-‖(@inner ℂ E _ W U)‖^2) : 1/4≤S :=
begin
 have hc : ‖(@inner ℂ E _ W U)‖≤‖W‖*‖U‖ := norm_inner_le_norm W U,
 have hq := pow_le_pow_of_le_left (norm_nonneg _) hc 2,
 rw [mul_pow,hw,hu] at hq,
 have hr : (n+1/2)^2=(n+1)*n+1/4 := by ring,
 rw [hr] at hs,rw [hs],linarith only [hq],
end

theorem equality_collinear (W U : E) (n : ℝ)
 (hw : ‖W‖^2=n+1) (hu : ‖U‖^2=n)
 (hs : (n+1/2)^2-‖(@inner ℂ E _ W U)‖^2=1/4) :
 ∃ r : ℂ, U=r • W :=
begin
 have hr : (n+1/2)^2=(n+1)*n+1/4 := by ring,
 rw [hr] at hs,
 have hh : ‖(@inner ℂ E _ W U)‖^2=(‖W‖*‖U‖)^2 := by rw [mul_pow,hw,hu];linarith only [hs],
 have he : ‖(@inner ℂ E _ W U)‖=‖W‖*‖U‖ :=
  (sq_eq_sq (norm_nonneg (@inner ℂ E _ W U)) (mul_nonneg (norm_nonneg W) (norm_nonneg U))).mp hh,
 have hn : 0≤n := by rw [←hu]; exact sq_nonneg _,
 have hW : W≠0 := by intro e;rw [e,norm_zero] at hw;norm_num at hw;linarith only [hw,hn],
 have hc : ‖(@inner ℂ E _ W U)‖=‖W‖*‖U‖ ↔ W=0 ∨ ∃ r : ℂ, U=r • W :=
   (@norm_inner_eq_norm_tfae ℂ E _ _ _ W U).out 0 2,
 exact (hc.mp he).resolve_left hW,
end

theorem cancel_ladder_weight (w r : ℂ) (a b : E) (hw : w≠0)
 (h : w • a=r • (w • b)) : a=r • b :=
calc a = w⁻¹ • (w • a) : (inv_smul_smul₀ hw a).symm
 ... = r • b : by rw [h,smul_comm r w b,inv_smul_smul₀ hw]

theorem factorized_coefficients (u : ℕ → E) (r : ℂ)
 (h : ∀ n, u (n+1)=r • u n) (n : ℕ) : u n=r^n • u 0 :=
begin induction n with n ih,
 { simp },
 { rw [nat.succ_eq_add_one,h,ih,smul_smul,pow_succ] },
end

end purification

theorem moment_length_constant (v x y A z : ℝ) :
 2*v*(2*z*y)-2*x*(-A*y)-2*y*(A*x+2*z*v)=0 := by ring

theorem all_state_count (v x y A z : ℝ) :
 let h := A*v+2*z*x, k := 4*z^2-A^2, S := v^2-x^2-y^2, n := v-1/2 in
 (2*z*y)^2=k*n^2+(k+2*A*h)*n-((h-A/2)^2+4*z^2*(S-1/4)) :=
by dsimp only;ring

theorem stiff_nonnegative (A h z S : ℝ) (hs : 1/4≤S) :
 0≤(h-A/2)^2+4*z^2*(S-1/4) :=
add_nonneg (sq_nonneg _) (mul_nonneg (by positivity) (sub_nonneg.mpr hs))

theorem zero_stiff (A h z S : ℝ) (hz : 0<z) (hs : 1/4≤S) :
 (h-A/2)^2+4*z^2*(S-1/4)=0 ↔ h=A/2 ∧ S=1/4 :=
begin
 have hn : 0≤4*z^2*(S-1/4) := mul_nonneg (by positivity) (sub_nonneg.mpr hs),
 have hp : 0<4*z^2 := by positivity,
 split,
 { intro he, have h1 : (h-A/2)^2=0 := by nlinarith only [he,hn,sq_nonneg (h-A/2)],
   have h2 : 4*z^2*(S-1/4)=0 := by linarith,
   split, { exact sub_eq_zero.mp (sq_eq_zero_iff.mp h1) }, { exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hp.ne') } },
 { rintro ⟨rfl,rfl⟩,ring },
end

theorem mixed_phase_deficit (q A z x y : ℝ) (hx : 2*z*x= -A*q)
 (hy : x^2+y^2=q*(1+q)) :
 (2*z*y)^2=4*z^2*q+(4*z^2-A^2)*q^2 :=
begin
 have h1 : (2*z*x)^2=(-A*q)^2 := congr_arg (λ t : ℝ,t^2) hx,
 linear_combination 4*z^2*hy - h1,
end

theorem two_sign_covariance (m b c : ℝ) :
 ((1+c)*(m+b)^2+2*(1-c)*(m+b)*(m-b)+(1+c)*(m-b)^2)/4-m^2=c*b^2 := by ring

theorem reachable_redshift (u m s : ℝ) (hu : 1<u)
 (he : 0≤1+m*(u-1)-s*(u^2-1)) : s≤(1+m*(u-1))/(u^2-1) :=
begin
 have hp : 0<u^2-1 := by nlinarith only [mul_pos (sub_pos.mpr hu) (show 0<u+1,by linarith)],
 apply (le_div_iff hp).mpr,linarith,
end

end landscape_receipts
