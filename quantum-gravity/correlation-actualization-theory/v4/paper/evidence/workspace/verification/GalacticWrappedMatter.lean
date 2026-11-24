import tactic
import analysis.special_functions.trigonometric.deriv
import analysis.special_functions.log.deriv
import algebra.big_operators.basic
import measure_theory.integral.bochner

noncomputable theory
open_locale big_operators
namespace galactic_wrapped_matter

/-- An unsigned integer charge stands for an equally likely pair of opposite charges.
The total probability in the pair is t, and the remaining probability is at zero. -/
def regroup (energy : ℕ → ℝ) (stress : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ 1 →
    stress (t * (n:ℝ)^2) = (1-t)*energy 0 + t*energy n

theorem matched_width_forces_square (e : ℕ → ℝ) (s : ℝ → ℝ)
    (h : regroup e s) (n : ℕ) : e n = e 0 + (e 1-e 0)*(n:ℝ)^2 :=
begin
  cases n with m,
  {simp},
  {let a : ℝ := ((m.succ:ℕ):ℝ),
   have ha : 1 ≤ a, {dsimp [a],simp only [nat.cast_succ],linarith [(nat.cast_nonneg m : (0:ℝ) ≤ (m:ℝ))]},
   have hpos : 0 < a^2 := pow_pos (lt_of_lt_of_le zero_lt_one ha) 2,
   have hs : 1 ≤ a^2, {nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr ha)]},
   have h1 := h 1 1 (by norm_num) (by norm_num),
   norm_num at h1,
   have h2 := h m.succ (1/a^2) (by positivity) ((div_le_one hpos).mpr hs),
   change s (1/a^2*a^2) = (1-1/a^2)*e 0 + 1/a^2*e m.succ at h2,
   rw [div_mul_cancel _ (ne_of_gt hpos),h1] at h2,
   change e m.succ = e 0+(e 1-e 0)*a^2,
   field_simp [ne_of_gt hpos] at h2,
   nlinarith [h2]}
end

/-- The port may also read a real coordinate of a continuous layer family. -/
theorem continuum_width_forces_square (e s : ℝ → ℝ)
    (h : ∀ x t : ℝ, 0 ≤ t → t ≤ 1 →
      s (t*x^2)=(1-t)*e 0+t*e x) (x : ℝ) :
    e x=e 0+(e 1-e 0)*x^2 :=
begin
  have h1 := h 1 1 (by norm_num) (by norm_num),
  norm_num at h1,
  by_cases small : x^2 ≤ 1,
  {have hx := h x 1 (by norm_num) (by norm_num),
   have hr := h 1 (x^2) (sq_nonneg x) small,
   norm_num at hx hr, nlinarith [hx,hr]},
  {have hp : 0 < x^2 := by linarith,
   have hx := h x (1/x^2) (by positivity) ((div_le_one hp).mpr (le_of_not_ge small)),
   rw [div_mul_cancel _ (ne_of_gt hp),h1] at hx,
   field_simp [ne_of_gt hp] at hx,nlinarith [hx]}
end

theorem resolution_point (q2 d2 j2 : ℝ) (hd : 0 ≤ d2) (hq : 0 ≤ q2)
    (hj : q2 ≤ j2) :
    d2*(if d2 < q2 then 1 else 0) ≤ q2 ∧
    q2 ≤ d2+(j2-d2)*(if d2 < q2 then 1 else 0) :=
by {split_ifs; split; norm_num; linarith}

theorem resolution_sum {ι : Type*} (I : finset ι) (w q2 hit : ι → ℝ) (d2 j2 : ℝ)
    (h1 : (∑ i in I, w i)=1) (hw : ∀ i ∈ I, 0 ≤ w i)
    (hlo : ∀ i ∈ I, d2*hit i ≤ q2 i)
    (hhi : ∀ i ∈ I, q2 i ≤ d2+(j2-d2)*hit i) :
    d2*(∑ i in I, w i*hit i) ≤ (∑ i in I, w i*q2 i) ∧
    (∑ i in I, w i*q2 i) ≤ d2+(j2-d2)*(∑ i in I, w i*hit i) :=
begin
  split,
  {rw [finset.mul_sum],apply finset.sum_le_sum,intros i hi,
   calc d2*(w i*hit i)= w i*(d2*hit i) : by ring
   ... ≤ _ : mul_le_mul_of_nonneg_left (hlo i hi) (hw i hi)},
  {calc (∑ i in I, w i*q2 i) ≤ ∑ i in I, w i*(d2+(j2-d2)*hit i) :
          finset.sum_le_sum (λ i hi,mul_le_mul_of_nonneg_left (hhi i hi) (hw i hi))
   ... = ∑ i in I, (w i*d2+(j2-d2)*(w i*hit i)) : finset.sum_congr rfl (λ i hi,by ring)
   ... = _ : by rw [finset.sum_add_distrib,←finset.sum_mul,←finset.mul_sum,h1,one_mul]}
end

theorem resolution_integral {α : Type*} [measurable_space α]
    (μ : measure_theory.measure α) [measure_theory.is_probability_measure μ]
    (q h : α → ℝ) (d J : ℝ) (hi : measure_theory.integrable h μ)
    (qi : measure_theory.integrable q μ) (lo : ∀x, d*h x ≤ q x)
    (up : ∀x, q x ≤ d+(J-d)*h x) :
    d*(∫ x, h x ∂μ) ≤ (∫ x, q x ∂μ) ∧
    (∫ x, q x ∂μ) ≤ d+(J-d)*(∫ x, h x ∂μ) :=
begin
  have low := measure_theory.integral_mono (hi.const_mul d) qi lo,
  have high := measure_theory.integral_mono qi
                ((measure_theory.integrable_const d).add (hi.const_mul (J-d))) up,
  rw [measure_theory.integral_mul_left] at low,
  change (∫ x, q x ∂μ) ≤ ∫ x, d+(J-d)*h x ∂μ at high,
  rw [measure_theory.integral_add (measure_theory.integrable_const d) (hi.const_mul (J-d))] at high,
  dsimp only at high,
  refine ⟨low,_⟩,
  simpa [measure_theory.integral_mul_left] using high
end

theorem width_only_on_mixed_states (s : ℝ → ℝ) (e0 : ℝ)
    (h : regroup (λ _, e0) s) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (hu : t ≤ 1) :
    s (t*(n:ℝ)^2)=e0 :=
by {rw [h n t ht hu],ring}

theorem approximate_sector (a e0 e1 en tol : ℝ) (ha : 0 < a) (ht : 0 ≤ tol)
    (h : abs ((en-e0)/a-e1) ≤ tol) :
    abs (en-e0-a*e1) ≤ a*tol :=
begin
  have eq : en-e0-a*e1=a*((en-e0)/a-e1), {field_simp [ne_of_gt ha],ring},
  rw [eq,abs_mul,abs_of_pos ha], exact mul_le_mul_of_nonneg_left h (le_of_lt ha)
end

theorem mean_stress {ι : Type*} (I : finset ι) (w k : ι → ℝ) (e0 b m v : ℝ)
    (hn : (∑ i in I, w i)=1) (hv : (∑ i in I, w i*(k i)^2)=m^2+v) :
    (∑ i in I, w i*(e0+b*(k i)^2))=e0+b*(m^2+v) :=
begin
  calc (∑ i in I, w i*(e0+b*(k i)^2)) =
       ∑ i in I, (w i*e0+b*(w i*(k i)^2)) : finset.sum_congr rfl (λ i hi,by ring)
   ... = _ : by rw [finset.sum_add_distrib,← finset.sum_mul,← finset.mul_sum,hn,hv,one_mul]
end

theorem sharp_return_bounds {ι : Type*} (I : finset ι) (p q hit : ι → ℝ)
    (cap : ℝ) (hp : ∀ i ∈ I, 0 ≤ p i)
    (hlo : ∀ i ∈ I, hit i ≤ (q i)^2)
    (hhi : ∀ i ∈ I, (q i)^2 ≤ cap^2*hit i) :
    (∑ i in I, p i*hit i) ≤ (∑ i in I, p i*(q i)^2) ∧
    (∑ i in I, p i*(q i)^2) ≤ cap^2*(∑ i in I, p i*hit i) :=
begin
  split,
  {exact finset.sum_le_sum (λ i hi,mul_le_mul_of_nonneg_left (hlo i hi) (hp i hi))},
  {rw [finset.mul_sum],apply finset.sum_le_sum,intros i hi,
   calc p i*(q i)^2 ≤ p i*(cap^2*hit i) : mul_le_mul_of_nonneg_left (hhi i hi) (hp i hi)
   ... = _ : by ring}
end

theorem same_width_different_returns : (1:ℝ)/100*10^2=1 ∧ (1:ℝ)-1/100=99/100 :=
by norm_num

theorem source_target (s₁ s₂ t₁ t₂ : ℝ) :
    (s₁*t₁+s₂*t₂-s₁*t₂-s₂*t₁)/7 = (s₁-s₂)*(t₁-t₂)/7 := by ring

theorem respiration (a : ℝ) (ha : a^2=63/2) :
    2*((3/2:ℝ)/a)^2=1/7 :=
begin have h : a≠0 := by {intro h,rw [h] at ha,norm_num at ha},
      field_simp [h],nlinarith end

theorem mass_product (v2 v5 v7 t2 t5 k mp2 : ℝ)
    (hv : 0 < v7) (hk : 0 < k) (hq : k*t2*t5=real.pi) (hm : mp2=v7/k) :
    (t2*v2)*(t5*v5)=real.pi*(v2*v5/v7)*mp2 :=
by {rw [hm,←hq],field_simp [ne_of_gt hv,ne_of_gt hk],ring}

theorem pair_cost (x y m : ℝ) (hm : 0 ≤ m) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hp : x*y=m^2) : 4*m ≤ 2*(x+y) :=
begin
 by_contra h, push_neg at h,
 have hs := mul_pos (by linarith : 0 < 2*m-(x+y))
                    (by linarith : 0 < 2*m+(x+y)),
 nlinarith [sq_nonneg (x-y)]
end

theorem radius_curvature (eta : ℝ) :
    441-324*(4/3+eta)+81*(1/3+2*eta)=36-162*eta := by ring

theorem vacuum_asymmetry (eta : ℝ) (he : eta < 2/9) :
    (-9261 + 5832*(4/3+eta)-729*(1/3+2*eta) : ℝ) < 0 := by linarith

theorem range_flux (h k m eta : ℝ) (hh : 0 < h) (hm : 0 < m) (hk : 0 < k)
    (margin : 2*m < k*eta) (short : eta*(7+108*h^2) < 24*h^2) :
    9 + 7/(12*h^2) < k/m :=
begin
 have h0 : 0 < 7+108*h^2 := by positivity,
 have h1 := mul_lt_mul_of_pos_right margin h0,
 have h2 := mul_lt_mul_of_pos_left short hk,
 apply (lt_div_iff hm).mpr,
 have hdr : 0 < 12*h^2 := by positivity,
 have hh2 : h^2 ≠ 0 := ne_of_gt (pow_pos hh 2),
 have key : (9+7/(12*h^2))*m=((108*h^2+7)*m)/(12*h^2),
 {field_simp [hh2]; ring_nf; simp},
 rw [key],apply (div_lt_iff hdr).mpr,nlinarith [h1,h2]
end

theorem sign_mismatch (epsilon : ℝ) :
    2*((1+epsilon)/2)*((1-epsilon)/2)=(1-epsilon^2)/2 := by ring

theorem disk_calibration (q inner outer : ℝ) (hq : 0<q) :
    0 < (1-q*outer)-(1-q*inner) ↔ outer < inner :=
begin
 have he : (1-q*outer)-(1-q*inner)=q*(inner-outer) := by ring,
 rw [he],split,
 {intro h,by_contra hn,push_neg at hn,
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (le_of_lt hq) (sub_nonpos.mpr hn))) h},
 {intro h,exact mul_pos hq (sub_pos.mpr h)}
end

theorem derivative_energy_coupling (rho s : ℝ) :
    ((3/2:ℝ)^2/(63/2))*rho*s^2=(2/7)*(rho*s^2/4) := by ring

theorem production_range (m mu r sigma : ℝ) (hm : 0 < m) (hu : 2*m ≤ mu)
    (hr : 0 < r) (hv : 0 ≤ sigma) (hloc : 1 ≤ 2*m*r*sigma) :
    1/mu ≤ r*sigma :=
begin
 have hp : 0 < mu := by linarith,
 apply (div_le_iff hp).mpr,
 have h := mul_le_mul_of_nonneg_right hu (mul_nonneg (le_of_lt hr) hv),
 nlinarith
end

/-- The filled momentum ball minimizes the second moment at fixed occupancy integral. -/
theorem fermiball_integrand (p2 edge2 f : ℝ) (lo : 0 ≤ f) (hi : f ≤ 1) :
    0 ≤ (p2-edge2)*(f-(if p2 ≤ edge2 then 1 else 0)) :=
begin
 split_ifs with h,
 {apply mul_nonneg_of_nonpos_of_nonpos; linarith},
 {apply mul_nonneg;linarith}
end

theorem moment_integral {α : Type*} [measurable_space α]
    (μ : measure_theory.measure α) (p2 f : α → ℝ) (edge : ℝ)
    (lo : ∀x, 0 ≤ f x) (hi : ∀x, f x ≤ 1) :
    0 ≤ ∫ x, (p2 x-edge)*(f x-(if p2 x ≤ edge then 1 else 0)) ∂μ :=
measure_theory.integral_nonneg (λx, fermiball_integrand _ _ _ (lo x) (hi x))

theorem dust_difference_mode (d1 d2 : ℝ) :
    ((1+1/7:ℝ)*d1+(1-1/7:ℝ)*d2)-((1-1/7:ℝ)*d1+(1+1/7:ℝ)*d2) =
    (2/7:ℝ)*(d1-d2) := by ring

theorem growth_exponent (x : ℝ) (hx : x^2=1+24/7) :
    ((x-1)/4)^2+(1/2:ℝ)*((x-1)/4)=3/14 := by linear_combination (1/16:ℝ)*hx

theorem finite_halo_mass_floor (mass g sigma rho hbar coefficient : ℝ)
    (hg : 0<g) (hs : 0<sigma) (hb : 0<hbar) (hc : 0<coefficient)
    (hr : rho*hbar^3 ≤ coefficient*g*mass^4*sigma^3) :
    rho*hbar^3/(coefficient*g*sigma^3) ≤ mass^4 :=
by {apply (div_le_iff (by positivity : 0<coefficient*g*sigma^3)).2,nlinarith [hr]}

def comp_speed (x t : ℝ) : ℝ := -(1-(7/3)*x^2)*((3/2)*x+(3/14)*t)

theorem compensation_dissipation (y x : ℝ → ℝ) (n : ℝ)
    (h : 0 < 1-(7/3)*(x n)^2) (hy : has_deriv_at y (x n) n)
    (hx : has_deriv_at x (comp_speed (x n) (real.tanh (y n))) n) :
    has_deriv_at (λ s, (3/14:ℝ)*(real.log (real.cosh (y s))-real.log (1-(7/3)*(x s)^2)))
                 (-(3/2)*(x n)^2) n :=
begin
  let a := comp_speed (x n) (real.tanh (y n)),
  have hd0 := (has_deriv_at_const n (1:ℝ)).sub ((hx.pow 2).const_mul (7/3:ℝ)),
  have hd : has_deriv_at (λ s, 1-(7/3)*(x s)^2) (-(14/3)*(x n)*a) n,
  {convert hd0 using 1; norm_num [a]; ring},
  have hc := hy.cosh.log (ne_of_gt (real.cosh_pos (y n))),
  have hs := ((hc.sub (hd.log (ne_of_gt h))).const_mul (3/14:ℝ)),
  have ht : real.sinh (y n)*x n / real.cosh (y n) = real.tanh (y n)*x n,
  {rw [real.tanh_eq_sinh_div_cosh],ring},
  have hv : (-(14/3)*(x n)*a)/(1-(7/3)*(x n)^2) =
            (14/3)*(x n)*((3/2)*(x n)+(3/14)*real.tanh (y n)),
  {apply (div_eq_iff (ne_of_gt h)).2,dsimp [a,comp_speed],ring},
  convert hs using 1,
  rw [ht,hv],ring
end

theorem inward_edges (t : ℝ) (lo : -1 ≤ t) (hi : t ≤ 1) :
    comp_speed (1/7) t ≤ 0 ∧ 0 ≤ comp_speed (-1/7) t :=
by {unfold comp_speed,split; ring_nf; linarith}

end galactic_wrapped_matter
