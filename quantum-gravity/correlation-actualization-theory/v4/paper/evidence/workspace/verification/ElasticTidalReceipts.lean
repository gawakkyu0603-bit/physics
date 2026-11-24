import tactic
import measure_theory.integral.bochner
import analysis.special_functions.exp
import analysis.special_functions.gaussian
import analysis.special_functions.trigonometric.arctan_deriv
import measure_theory.integral.fund_thm_calculus

noncomputable theory
open measure_theory filter
open_locale topology
open_locale big_operators

namespace elastic_tidal_receipts

/-- Dimensionless Lamé coefficient l=lambda/mu and unit shear modulus, unit body force. -/
theorem static_free_sphere (l : ℝ) (h : 19*l+14 ≠ 0) :
  let A := (4*l+3)/(19*l+14),
      B := (l+1)/(19*l+14),
      C := -(5*l+4)/(2*(19*l+14)) in
  (10*l+14)*B + (4*l+14)*C = -1 ∧
  A+B+2*C = 0 ∧ (5*l+4)*B+(2*l+2)*C=0 ∧
  A/5+2*B/35+C/7=(35*l+26)/(70*(19*l+14)) :=
by {dsimp only, repeat {split}, all_goals {field_simp [h]; ring}}

def compliance (l : ℝ) := (35*l+26)/(70*(19*l+14))

theorem stable_compliance (l : ℝ) (h : 0 < l+2/3) :
    1/38 < compliance l ∧ compliance l < 1/35 :=
begin
  have pd : 0 < 70*(19*l+14) := by linarith,
  unfold compliance, split,
  {apply (lt_div_iff pd).mpr, linarith},
  {apply (div_lt_iff pd).mpr, linarith}
end

theorem flat_tide_budget (l strain speed : ℝ) (hl : 0 < l+2/3)
    (hs : 0 ≤ strain) (hs' : strain ≤ 1/10) (hv : 0 ≤ speed) (hv' : speed ≤ 1) :
    (4/3)*compliance l*strain^2*speed^2 ≤ 4/10500 :=
begin
  have ss : strain^2 ≤ (1/10:ℝ)^2 := by exact pow_le_pow_of_le_left hs hs' 2,
  have vv : speed^2 ≤ (1:ℝ)^2 := pow_le_pow_of_le_left hv hv' 2,
  have cp := stable_compliance l hl,
  have posc : 0 ≤ (4/3)*compliance l := by linarith [cp.1],
  have h1 := mul_le_mul_of_nonneg_left ss posc,
  have h2 := mul_le_mul_of_nonneg_left vv (mul_nonneg posc (sq_nonneg strain)),
  nlinarith [h1,h2,cp.2]
end

/-- Strain is the Frobenius norm of the STF forcing times radius squared / shear speed squared.
This bound needs no spherical model for the Galactic potential. -/
theorem arbitrary_tide_budget (l strain speed : ℝ) (hl : 0 < l+2/3)
    (hs : 0 ≤ strain) (hs' : strain ≤ 1/10) (hv : 0 ≤ speed) (hv' : speed ≤ 1) :
    compliance l*strain^2*speed^2/2 ≤ 1/7000 :=
begin
  have ss := pow_le_pow_of_le_left hs hs' 2,
  have vv := pow_le_pow_of_le_left hv hv' 2,
  have cp := stable_compliance l hl,
  have posc : 0 ≤ compliance l := by linarith [cp.1],
  have h1 := mul_le_mul_of_nonneg_left ss posc,
  have h2 := mul_le_mul_of_nonneg_left vv (mul_nonneg posc (sq_nonneg strain)),
  nlinarith [h1,h2,cp.2]
end

theorem local_mass_shortfall :
    (450:ℝ)*((84+2*12)/1000/7000) < (13-2*3)/1000 := by norm_num

def kernel (t u x : ℝ) := (t*u+x)/((t^2+x)*(u^2+x))

theorem kernel_cross (t u x y : ℝ) :
  (t*u+x)*((t^2+y)*(u^2+y))-(t*u+y)*((t^2+x)*(u^2+x)) =
  (y-x)*(t*u*((t-u)^2+t*u)+t*u*(x+y)+x*y) := by ring

theorem kernel_decreases (t u x y : ℝ) (ht : 0 < t) (hu : 0 < u)
    (hx : 0 ≤ x) (hxy : x ≤ y) : kernel t u y ≤ kernel t u x :=
begin
  have hy : 0 ≤ y := le_trans hx hxy,
  have dx : 0 < (t^2+x)*(u^2+x) := by positivity,
  have dy : 0 < (t^2+y)*(u^2+y) := by positivity,
  unfold kernel, apply (div_le_div_iff dy dx).mpr,
  have hg : 0 ≤ t*u*((t-u)^2+t*u)+t*u*(x+y)+x*y := by positivity,
  linarith [kernel_cross t u x y, mul_nonneg (sub_nonneg.mpr hxy) hg]
end

/-- Real part of a pair of Laplace propagators; the symmetric double integral is real. -/
theorem kernel_is_inner (t u z : ℝ) (ht : 0<t) (hu : 0<u) :
   (t/(t^2+z^2))*(u/(u^2+z^2))+
   (-z/(t^2+z^2))*(-z/(u^2+z^2))=kernel t u (z^2) :=
begin
  have h1 : 0<t^2+z^2 := by positivity,
  have h2 : 0<u^2+z^2 := by positivity,
  unfold kernel, field_simp [ne_of_gt h1,ne_of_gt h2], ring
end

theorem kernel_integral_decreases {α : Type*} [measurable_space α]
    (μ : measure α) (t u : α → ℝ) (x y : ℝ)
    (ht : ∀ i, 0<t i) (hu : ∀ i, 0<u i) (hx : 0 ≤ x) (hxy : x ≤ y)
    (ix : integrable (λ i, kernel (t i) (u i) x) μ)
    (iy : integrable (λ i, kernel (t i) (u i) y) μ) :
    (∫ i, kernel (t i) (u i) y ∂μ) ≤ ∫ i, kernel (t i) (u i) x ∂μ :=
integral_mono iy ix (λ i, kernel_decreases _ _ _ _ (ht i) (hu i) hx hxy)

theorem ramp_grows (early late ke kl : ℝ) (hl : 0 < late) (ht : late ≤ early)
    (hk : 0 ≤ ke) (h : ke ≤ kl) : ke/early^4 ≤ kl/late^4 :=
begin
  have he := lt_of_lt_of_le hl ht,
  have p := pow_le_pow_of_le_left (le_of_lt hl) ht 4,
  apply (div_le_div_iff (pow_pos he 4) (pow_pos hl 4)).mpr,
  exact le_trans (mul_le_mul_of_nonneg_left p hk)
    (mul_le_mul_of_nonneg_right h (le_of_lt (pow_pos he 4)))
end

theorem interval_rate (early late n : ℝ) (h : early ≤ late) (hn : 0 ≤ n) :
    0 ≤ (late-early)*(n+1) ∧ 0 ≤ (late-early)*n ∧
    (late-early)*(n+1)-(late-early)*n=late-early :=
by {have hi := sub_nonneg.mpr h, split, {positivity}, split, {positivity}, ring}

theorem increment_variance (v1 v2 rinc : ℝ) (h : v2=v1+rinc) (hr : 0 ≤ rinc) :
    v1 ≤ v2 := by linarith

theorem no_finite_escape_zero (hazard same : ℝ) (h : real.exp (-hazard) ≤ same) :
    0 < same := lt_of_lt_of_le (real.exp_pos _) h

theorem one_number_node : real.exp (-(1:ℝ)) * (1-1)^2=0 := by norm_num

theorem charge_work_on_ladders (stored source unit : ℝ) (k : ℤ) :
    (stored+(k:ℝ)*unit)+(source-(k:ℝ)*unit)=stored+source := by ring

theorem thermal_symbol (a n : ℝ) :
    a*(n+1)-a*n=a ∧ a*(n+1)+a*n=a*(2*n+1) := by {split; ring}

theorem diffusion_cumulants (a v n : ℝ) :
    (a+v)*(2*n+1)+v^2+2*a*v = a*(2*n+1)+v*(2*n+1+v+2*a) := by ring

/-- Bright projection of one of two normalized STF tensors with overlap -1/2. -/
theorem orthogonal_port : (1:ℝ)-(-1/2)^2=3/4 ∧
    (2:ℝ)^2+(-1)^2+(-1)^2=6 ∧ 2*(-1:ℝ)+(-1)*2+(-1)*(-1)= -3 :=
by norm_num

theorem asymmetric_decision (zero : ℝ) :
    (1/2:ℝ)*zero+(1/2)*0=zero/2 := by ring

theorem matched_pair (p : ℝ) (k : ℤ) : (k-k=0) ∧ p*(1:ℝ)=p :=
by simp

theorem radiative_width (g2 omega amplitude G c : ℝ) (hc : c ≠ 0) :
    (4*G*g2*omega^4/(5*c^5))*(omega^2*amplitude^2/2)
    = (G/(5*c^5))*(4*g2*omega^6*amplitude^2/2) :=
by {field_simp [hc]; ring}

theorem volume_scaling (r m cw : ℝ) (hr : r ≠ 0) (hm : m ≠ 0) (hw : cw ≠ 0) :
    (r^5 / (cw/r)^3 / m^4) * (1/((cw/r)*m)^2) * r =
    r^11/(cw^5*m^6) := by {field_simp [hr,hm,hw]; ring}

/-- The two real Gaussian integrations giving the signed-work law after additive diffusion.
d is the real coherent shift in the physical application; h is the complex counting symbol. -/
theorem displaced_work_gaussian (v d h : ℂ) (hv : v ≠ 0) (hb : 0 < (1/v-h).re) :
    ( (∫ x : ℝ, complex.exp (-(x:ℂ)^2/v+h*((x:ℂ)+d)^2)) *
      (∫ y : ℝ, complex.exp (-(1/v-h)*(y:ℂ)^2)) ) / ((real.pi:ℂ)*v)
      = complex.exp (d^2*h/(1-v*h))/(1-v*h) :=
begin
  let b : ℂ := 1/v-h,
  have bn : b ≠ 0, {intro hz, change 0 < b.re at hb, rw [hz] at hb, exact (lt_irrefl 0) hb},
  have eqb : v*b=1-v*h, {dsimp [b],field_simp [hv],ring},
  have dn : 1-v*h ≠ 0 := eqb ▸ mul_ne_zero hv bn,
  have pn : (real.pi:ℂ) ≠ 0 := complex.of_real_ne_zero.mpr real.pi_ne_zero,
  have square : ∀ x : ℂ, -x^2/v+h*(x+d)^2 =
      d^2*h/(1-v*h) + -b*(x+(-h*d/b))^2,
  {intro x, rw [←eqb], field_simp [hv,bn], dsimp [b],field_simp [hv],ring},
  simp_rw [square,complex.exp_add],
  rw [integral_mul_left,integral_cexp_neg_mul_sq_add_const hb,
      integral_gaussian_complex hb],
  rw [mul_assoc,←complex.cpow_add _ _ (div_ne_zero pn bn)],
  norm_num,
  rw [←eqb],
  field_simp [pn,bn,hv], ring
end

theorem finite_faithful_no_tag {ι : Type*} (I : finset ι) (p e : ι → ℝ)
    (hp : ∀ i∈I, 0 < p i) (he : ∀ i∈I, 0 ≤ e i)
    (hz : (∑ i in I, p i*e i)=0) (j : ι) (hj : j∈I) : e j=0 :=
begin
  have hn : ∀ i∈I, 0 ≤ p i*e i := λ i hi, mul_nonneg (hp i hi).le (he i hi),
  have hle := finset.single_le_sum hn hj, rw [hz] at hle,
  have hh := le_antisymm hle (hn j hj),
  exact (mul_eq_zero.mp hh).resolve_left (ne_of_gt (hp j hj))
end

theorem charge_diagonal_partition (K : finset ℤ) (m n : ℤ) (w : ℝ) (h : m-n∈K) :
    (∑ k in K, if k=m-n then w else 0)=w := by simp [h]

theorem charge_cross_term (k m n j : ℤ) (u v : ℂ) (h : n ≠ j) :
    (if m-n=k then u else 0)*(if m-j=k then v else 0)=0 :=
by {split_ifs; try {simp}; exfalso; apply h; linarith}

theorem passive_bath_excludes_equal_rates (gap down up : ℝ)
    (hg : 0 < gap) (hd : 0 < down) (kms : up=real.exp (-gap)*down) : up<down :=
begin
  have he : real.exp (-gap) < 1, {rw [real.exp_lt_one_iff],linarith},
  rw [kms], conv_rhs {rw [←one_mul down]}, exact mul_lt_mul_of_pos_right he hd
end

theorem thermal_covariance_product {ι : Type*} (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (s : finset ι) : 1+(∑ i in s,w i) ≤ ∏ i in s,(1+w i) :=
begin
  classical, induction s using finset.induction_on with a s ha ih,
  {simp}, {rw [finset.sum_insert ha,finset.prod_insert ha],
   have h1 := mul_le_mul_of_nonneg_left ih (show 0 ≤ 1+w a, by linarith [hw a]),
   have h2 := mul_nonneg (hw a) (finset.sum_nonneg (λ i hi,hw i) : 0 ≤ ∑ i in s,w i),
   nlinarith}
end

theorem finite_thermal_vacuum {ι : Type*} (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (s : finset ι) :
    real.exp (-(∑ i in s,w i)) ≤ 1/(∏ i in s,(1+w i)) :=
begin
  have hp : 0 < ∏ i in s,(1+w i) :=
    finset.prod_pos (λ i hi, by linarith [hw i]),
  have le : (∏ i in s,(1+w i)) ≤ real.exp (∑ i in s,w i),
  {rw real.exp_sum, apply finset.prod_le_prod,
   {intros i hi, linarith [hw i]}, {intros i hi, linarith [real.add_one_le_exp (w i)]}},
  rw [real.exp_neg,←one_div],
  exact one_div_le_one_div_of_le hp le
end

theorem neutral_receipt_survives (p pass other : ℝ) (hp : 0 < p) (hpass : 0 < pass)
    (ho : 0 ≤ other) : 0 < p*pass+other := add_pos_of_pos_of_nonneg (mul_pos hp hpass) ho

theorem clock_integral_derivative (k x : ℝ) (hk : 0 < k) :
    has_deriv_at (λ y : ℝ, 2*real.arctan (k*y)/k-real.log (1+(k*y)^2)/k^2)
      (2*(1-x)/(1+(k*x)^2)) x :=
begin
  have hpos : 0 < 1+(k*x)^2 := by positivity,
  have d := (has_deriv_at_id x).const_mul k,
  have l := ((d.pow 2).const_add 1).log (ne_of_gt hpos),
  have f := ((((real.has_deriv_at_arctan (k*x)).comp x d).const_mul 2).div_const k).sub
    (l.div_const (k^2)),
  convert f using 1,
  dsimp, field_simp [ne_of_gt hk,ne_of_gt hpos], ring
end

theorem clock_envelope_integral (k : ℝ) (hk : 0 < k) :
    (∫ y in (0:ℝ)..1, 2*(1-y)/(1+(k*y)^2)) =
    2*real.arctan k/k-real.log (1+k^2)/k^2 :=
begin
  have hc : continuous (λ y : ℝ, 2*(1-y)/(1+(k*y)^2)) :=
    (continuous_const.mul (continuous_const.sub continuous_id)).div
      (continuous_const.add ((continuous_const.mul continuous_id).pow 2))
      (λ y,ne_of_gt (by positivity : (0:ℝ)<1+(k*y)^2)),
  rw [interval_integral.integral_eq_sub_of_has_deriv_at
     (λ y hy,clock_integral_derivative k y hk) (hc.interval_integrable 0 1)],
  simp
end

theorem cooling_window (energy power elapsed : ℝ) (hp : 0 < power)
    (ht : elapsed ≤ energy/power) : power*elapsed ≤ energy :=
by {rw [mul_comm],exact (le_div_iff hp).mp ht}

theorem uniform_mass_count (m m0 a sat target : ℝ) (h : m0 ≤ m) (ha : 0 ≤ a)
    (hv : target ≤ a*m0) (hs : target ≤ sat) (full_window : Prop)
    [decidable full_window] : target ≤ (if full_window then a*m else sat) :=
by {split_ifs, exact le_trans hv (mul_le_mul_of_nonneg_left h ha),exact hs}

theorem cone_min (x : ℝ) (h3 : 3 ≤ x) (h5 : x ≤ 5) :
    (1/15000:ℝ) ≤ (1/100)*(1-1/x)/x^2/4 :=
begin
  have xp : 0 < x := by linarith,
  have h1 : 1/x ≤ (1/3:ℝ) := one_div_le_one_div_of_le (by norm_num) h3,
  have h2 : x^2 ≤ 5^2 := pow_le_pow_of_le_left xp.le h5 2,
  rw [le_div_iff (by norm_num : (0:ℝ)<4), le_div_iff (pow_pos xp 2)],
  nlinarith
end

def laplace_density (n : ℕ) (e : ℝ) : ℝ :=
  (1-real.exp (-((n:ℝ)+1)*e))/((n:ℝ)+1)

theorem laplace_density_bounds (n : ℕ) (e : ℝ) (he : 0 ≤ e) :
    0 ≤ laplace_density n e ∧ laplace_density n e ≤ e ∧
    laplace_density n e ≤ 1/((n:ℝ)+1) :=
begin
  have hn : 0 < (n:ℝ)+1 := by positivity,
  have hn' : -((n:ℝ)+1)*e ≤ 0 := by nlinarith [mul_nonneg hn.le he],
  have h := real.exp_le_one_iff.mpr hn',
  have hx := real.add_one_le_exp (-((n:ℝ)+1)*e),
  unfold laplace_density, split,
  {exact div_nonneg (sub_nonneg.mpr h) hn.le},
  split, {apply (div_le_iff hn).mpr, linarith},
  {apply div_le_div_of_le hn.le, linarith [real.exp_pos (-((n:ℝ)+1)*e)]}
end

/-- Finite mean energy; no assumption that the total expected number is finite. -/
theorem laplace_slope_zero {ι : Type*} [measurable_space ι] (μ : measure ι)
    (E : ι → ℝ) (hm : measurable E) (he : ∀ i, 0 ≤ E i) (hi : integrable E μ) :
    tendsto (λ n : ℕ, ∫ i, laplace_density n (E i) ∂μ) at_top (𝓝 0) :=
begin
  have measurable_terms : ∀ n : ℕ, ae_strongly_measurable (λ i,laplace_density n (E i)) μ,
  {intro n,
   have hc : continuous (λ x : ℝ, laplace_density n x),
   {unfold laplace_density, continuity},
   exact (hc.measurable.comp hm).ae_strongly_measurable},
  have bounded : ∀ n : ℕ, ∀ᵐ i ∂μ, ‖laplace_density n (E i)‖ ≤ E i,
  {intro n, exact filter.eventually_of_forall (λ i,by
    {rw [real.norm_eq_abs,abs_of_nonneg (laplace_density_bounds _ _ (he i)).1],
     exact (laplace_density_bounds _ _ (he i)).2.1})},
  have pointwise : ∀ᵐ i ∂μ, tendsto (λ n,laplace_density n (E i)) at_top (𝓝 0),
  {apply filter.eventually_of_forall, intro i, apply squeeze_zero,
   {intro n, exact (laplace_density_bounds _ _ (he i)).1},
   {intro n, exact (laplace_density_bounds _ _ (he i)).2.2},
   exact tendsto_one_div_add_at_top_nhds_0_nat},
  have conv : tendsto (λ n : ℕ, ∫ i, laplace_density n (E i) ∂μ) at_top (𝓝 (∫ i, (0:ℝ) ∂μ)) :=
    tendsto_integral_of_dominated_convergence E measurable_terms hi bounded pointwise,
  simpa using conv
end

theorem positive_small_energy (t h K p L : ℝ) (ht : 0<t) (hh : 0<h)
    (hk : K<t*h) (hl : real.exp (-K) ≤ L)
    (hu : L ≤ p+(1-p)*real.exp (-t*h)) : 0<p :=
begin
  have e1 : real.exp (-t*h) < real.exp (-K) := real.exp_lt_exp.mpr (by linarith),
  have e2 : real.exp (-t*h) < 1 := real.exp_lt_one_iff.mpr (by nlinarith [mul_pos ht hh]),
  by_contra hn, push_neg at hn,
  nlinarith [mul_nonneg (neg_nonneg.mpr hn) (sub_nonneg.mpr e2.le)]
end

theorem soft_return_positive (p floor rest : ℝ) (hp : 0<p) (hf : 0<floor)
    (hr : 0 ≤ rest) : 0 < floor*p+rest := add_pos_of_pos_of_nonneg (mul_pos hf hp) hr

theorem zero_charge_route (neutral : Prop) [decidable neutral] :
    (if neutral then (1:ℝ) else 0)+(if neutral then 0 else 1)=1 :=
by split_ifs; norm_num

theorem isotropic_stf_vanishes (isotropic : ℝ) : isotropic-(3*isotropic)/3=0 := by ring

end elastic_tidal_receipts
