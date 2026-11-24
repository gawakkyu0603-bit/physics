import tactic
import analysis.calculus.mean_value
import analysis.inner_product_space.basic

noncomputable theory
open_locale big_operators
open filter
namespace cat_spherical_receipt

-- sigma is the tangential harmonic-map source. F=P/r², b=dr/dx, d=dF/dx.
theorem sourced_area (r F b d sigma : ℝ) (hr : r≠0) (hF : F≠0)
 (stress : sigma = -d-2*(F+1/F)*b/r) :
 4*r^3*b+2*(r^2*F)*(2*r*b*F+r^2*d) = -2*r^2*(r^2*F)*sigma :=
begin rw [stress], field_simp [hr,hF]; ring end

theorem finite_outer_radius (r P C : ℝ) (area_eq : r^4+P^2=C) : r^4≤C :=
by linarith [sq_nonneg P]

theorem integrated_outer_source (r P C work : ℝ) (balance : work=r^4+P^2-C) :
 r^4-C≤work := by linarith [sq_nonneg P]

theorem asymptotic_radial_force (F : ℝ) (h : 0<F) : -2*(F+1/F)≤-4 :=
begin
 have w : 2 ≤ F+1/F,
 { apply (le_of_mul_le_mul_right _ h),
   rw [add_mul,div_mul_cancel _ (ne_of_gt h)], nlinarith only [sq_nonneg (F-1)] },
 linarith
end

theorem area_along_curve (r P : ℝ → ℝ)
 (dr dP : ℝ → ℝ) (hr : ∀ t, has_deriv_at r (dr t) t)
 (hP : ∀ t, has_deriv_at P (dP t) t)
 (balance : ∀ t, 4*(r t)^3*dr t+2*(P t)*dP t=0) :
 ∀ t s : ℝ, (r t)^4+(P t)^2=(r s)^4+(P s)^2 :=
begin
 let k : ℝ → ℝ := λ t, (r t)^4+(P t)^2,
 have hk : ∀ t, has_deriv_at k 0 t,
 { intro t,
   have q := ((hr t).pow 4).add ((hP t).pow 2),
   convert q using 1,
   norm_num, linarith [balance t] },
 exact is_const_of_deriv_eq_zero (λ t, (hk t).differentiable_at) (λ t, (hk t).deriv)
end

-- x_i is w_i |b_i(0)|² for each angular multiplet, lambda_i ≥ 2.
theorem finite_angular_budget {ι : Type*} (s : finset ι) (x L : ι → ℝ)
 (hx : ∀ i∈s, 0≤x i) (hL : ∀ i∈s, 2≤L i) :
 2*(∑ i in s, x i) ≤ ∑ i in s, L i*x i :=
begin
 rw [finset.mul_sum],
 exact finset.sum_le_sum (λ i hi, mul_le_mul_of_nonneg_right (hL i hi) (hx i hi))
end

theorem centre_slope_impossible (P Q R slope : ℝ) (pos : 0<P)
 (budget : 2*P≤Q) (bounded_wave : R*slope = -2*Q) (conserved : slope=0) : false :=
by {rw [conserved,mul_zero] at bounded_wave, linarith}

-- Finite real components, including repeated copies of a representation.
-- The hypotheses are the centre coefficients of the ordinary angular wave
-- and the derivative of the conserved area; the contradiction uses both.
theorem bounded_harmonic_sheet_impossible {ι : Type*} (s : finset ι)
 (w L b d : ι → ℝ) (R : ℝ) (hw : ∀ i∈s, 0≤w i) (hL : ∀ i∈s, 2≤L i)
 (area : 0<∑ i in s, w i*b i^2)
 (wave : ∀ i∈s, R*d i= -(L i*b i))
 (stationary : (∑ i in s, 2*w i*b i*d i)=0) : false :=
begin
 have bound := finite_angular_budget s (λ i, w i*b i^2) L
   (λ i hi, mul_nonneg (hw i hi) (sq_nonneg _)) hL,
 have identity : R*(∑ i in s, 2*w i*b i*d i)=
       (-2)*(∑ i in s, L i*(w i*b i^2)),
 { rw [finset.mul_sum,finset.mul_sum],
   apply finset.sum_congr rfl, intros i hi,
   calc R*(2*w i*b i*d i)=2*w i*b i*(R*d i) : by ring
       ... =(-2)*(L i*(w i*b i^2)) : by {rw [wave i hi],ring} },
 rw [stationary,mul_zero] at identity, dsimp at bound, linarith
end

theorem forced_source_budget (q w R t d : ℝ) (slope : R*d = -2*(q+w))
 (area : d = -t) : q+w=R*t/2 := by {rw [area] at slope, linarith}

theorem normal_source_lower {E : Type*} [normed_add_comm_group E] [inner_product_space ℝ E] (b n : E)
 (hb : 0 < ‖b‖) (h : 2 * ‖b‖ ^ 2 ≤ -(inner b n : ℝ)) : 2 * ‖b‖ ≤ ‖n‖ :=
begin
 have u := abs_real_inner_le_norm b n,
 have v := neg_le_abs_self (inner b n : ℝ),
 by_contra H, push_neg at H,
 have w := mul_lt_mul_of_pos_left H hb, nlinarith
end

-- Volume stress is normal. The projected radial equation has three vanishing
-- terms at the centre and a strictly positive angular term.
theorem no_regular_volume_core {α : Type*} {f : filter α} [ne_bot f]
 (a b c angular : α → ℝ) (E : ℝ) (hE : 0<E)
 (ha : tendsto a f (nhds 0)) (hb : tendsto b f (nhds 0))
 (hc : tendsto c f (nhds 0)) (hd : tendsto angular f (nhds E))
 (equation : ∀ n, a n-b n+c n=angular n) : false :=
begin
 have z := (ha.sub hb).add hc,
 have eq : (λ n, a n-b n+c n)=angular := funext equation,
 change tendsto (λ n, a n-b n+c n) f (nhds ((0:ℝ)-0+0)) at z,
 rw [eq] at z, simp at z,
 exact (ne_of_gt hE) (tendsto_nhds_unique hd z)
end

theorem derivative_zero_on_metric_solution {E F : Type*}
 [normed_add_comm_group E] [normed_space ℝ E]
 [normed_add_comm_group F] [normed_space ℝ F]
 {S : F → ℝ} {G : E → F} {x : E} (D : E →L[ℝ] F)
 (stationary : has_fderiv_at S (0 : F →L[ℝ] ℝ) (G x)) (metric : has_fderiv_at G D x) :
 has_fderiv_at (S ∘ G) (0 : E →L[ℝ] ℝ) x :=
by simpa using stationary.comp x metric

theorem positive_diamond (q u v psi loop w : ℝ)
 (hq : 0<q) (hu : 0<u) (hv : 0<v) (hw : 0<w)
 (retarded : q*u*v/4≤psi) (curl : w*psi≤loop) : 0<loop :=
lt_of_lt_of_le (mul_pos hw (lt_of_lt_of_le (by positivity : 0<q*u*v/4) retarded)) curl

theorem signed_clock_mass (r a : ℝ) (hr : r≠0) (energy : r^4+a^4=1) :
 -(a^2/r^2)^2=1-1/r^4 :=
begin field_simp [hr]; nlinarith only [energy] end

theorem clock_from_matrices (a v : ℝ → ℝ) (t E : ℝ)
 (position : has_deriv_at a (v t) t)
 (acceleration : has_deriv_at v (-2*(a t)^3) t)
 (energy : (v t)^2+(a t)^4=E) :
 has_deriv_at (λ x, a x*v x) (E-3*(a t)^4) t :=
begin
 have p := position.mul acceleration,
 convert p using 1, nlinarith only [energy]
end

theorem intrinsic_clock_rate_positive (E a : ℝ) (near_turn : E<3*a^4) :
 0 < -(E-3*a^4)/2 := by linarith

theorem shell_deep (x y : ℝ) (hx : 1≤x) (hy : 0<y) : (1-x^2)/(2*x)-1/y<0 :=
begin
 have hx' : 0<x := by linarith,
 have w : x^2≥1 := by nlinarith only [hx, sq_nonneg (x-1)],
 exact sub_neg.mpr (lt_of_le_of_lt (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)) (by positivity))
end

theorem cubic_volume_discrepancy (k P R Q D E : ℝ) (d : D=0)
 (wave : 3*k*P*R*E-2*k*P*D=Q) (positive : 0<Q) : E≠0 :=
by {rintro rfl, rw [d] at wave, nlinarith}

theorem angular_force_from_wave (b d L R B : ℝ) (slope : -R*d-L*b=B) :
 R*(2*b*d) = -2*(b*B+L*b^2) :=
by {rw [←slope], ring}

theorem retarded_floor (q u v base shift : ℝ)
 (h : q*u*v/4≤base) (extra : 0≤shift) : q*u*v/4≤base+shift := by linarith

theorem current_curl (h dq sigma r : ℝ) (hh : 0<h) (hr : 0<r) :
 dq/(1+h)+dq/(h*(1+h))-3*sigma/(2*r)=dq/h-3*sigma/(2*r) :=
begin have h1 : 1+h≠0 := ne_of_gt (by linarith), field_simp [ne_of_gt hh,ne_of_gt hr,h1]; ring end

theorem flow_impulse (a b da db : ℂ) :
 db*star a+b*star da=star (star db*a+star b*da) :=
by simp [star_add,star_mul,mul_comm]

theorem shell_at_larger_radius (x y : ℝ) (hx : 0<x) (hy : 0<y) (hs : 0<1-x^2) :
 0≤(1-x^2)/(2*x)-1/y ↔ 2*x/(1-x^2)≤y :=
begin
 rw [sub_nonneg,div_le_div_iff hy (by positivity : (0:ℝ)<2*x),div_le_iff hs],
 split; intro h; nlinarith only [h]
end

theorem angular_junction (x y : ℝ) (hx : x≠0) (hy : y≠0) :
 -((1+y^2)/y-(1+x^2)/(2*x)-y+x)=(1-x^2)/(2*x)-1/y :=
begin field_simp [hx,hy]; ring end

-- A profile averaged over a common clock, before an irreversible reading:
-- tracing the two equal-prior projectors gives the signed-event frequency.
theorem common_clock_charge (p q : ℝ) (partition : p+q=1) :
 p*q+q*p=2*p*(1-p) := by {have h : q=1-p := by linarith, rw [h], ring}

theorem port_centres_neutral (n m : ℤ) : (n-m)+(m-n)=0 := by ring
theorem signed_probabilities (p : ℝ) : p^2+(1-p)^2+2*p*(1-p)=1 := by ring
theorem force_charge_covariance (j p : ℝ) :
 (2*j)*(1:ℝ)^2*p*(1-p)+(2*j)*(-1:ℝ)^2*p*(1-p)=2*j*(2*p*(1-p)) := by ring
theorem four_colour_bound (a b c d : ℝ) : (a+b+c+d)^2≤4*(a^2+b^2+c^2+d^2) :=
by nlinarith only [sq_nonneg (a-b),sq_nonneg (a-c),sq_nonneg (a-d),
                    sq_nonneg (b-c),sq_nonneg (b-d),sq_nonneg (c-d)]
theorem relative_inverse_inertia (j : ℝ) (hp : 0<j) :
 j^2/((2*j+1)*j*(j+1))+1/(2*j+1)+1/2+1/2=1+1/(j+1) :=
begin
 have h₁ : 2*j+1≠0 := ne_of_gt (by linarith),
 have h₂ : j+1≠0 := ne_of_gt (by linarith),
 field_simp [h₁,h₂,ne_of_gt hp]; ring
end
end cat_spherical_receipt
