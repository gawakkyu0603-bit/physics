import data.real.sqrt
import measure_theory.integral.bochner
import analysis.special_functions.integrals
import measure_theory.measure.haar.normed_space
import tactic

noncomputable theory
namespace cat_rotating_response

theorem pole_polynomial (p t x e : ℝ) :
  (p+6*t-x-e)*(p+2*t-x-e)-4*x*e =
  (e-(p+4*t+x))^2-4*(t^2+x*(p+4*t)) := by ring

theorem stable_product (p t x : ℝ) (hp : 0≤p) (ht : 0≤t) (hx : x≤2*t) :
  0≤(p+6*t-x)*(p+2*t-x) := mul_nonneg (by linarith) (by linarith)

theorem sum_squared (a b : ℝ) : (a+b)^2=a^2+b^2+2*a*b := by ring

theorem energy_tail (p d m2 : ℝ) (hp : 0<p) (h : p≤d) (disp : d^2=p^2+m2) :
  0≤d-p ∧ d-p≤m2/(2*p) :=
begin
  refine ⟨sub_nonneg.mpr h,(le_div_iff (show 0<2*p, by linarith)).mpr _⟩,
  nlinarith [sq_nonneg (d-p)]
end

theorem shifted_boundary (p a dp dm err : ℝ)
  (hp : 0≤dp-(p+a)) (hm : 0≤dm-(p-a))
  (up : dp-(p+a)≤err) (um : dm-(p-a)≤err) :
  |(dp-dm)-2*a|≤err := abs_le.mpr ⟨by linarith, by linarith⟩

theorem fermion_boundary_integral (a : ℝ) : 2*(∫ x in (0:ℝ)..a, x)=a^2 :=
by { rw [integral_id], ring }

theorem boson_shift_sign (u v : ℝ) (hv : 0<v) (hu : v<u) :
  2*(1-u/v)<0 :=
by { have h : 1<u/v := (lt_div_iff hv).mpr (by linarith), linarith }

theorem curvature_counterterms (mu2 xi : ℝ) :
  (-2*(mu2/2)-mu2)*(-3*xi)+(3-12*xi)*(mu2/2)=3*mu2/2 := by ring

theorem flat_log (m : ℝ) : -(m/2)^2-(m/2)*m= -3*m^2/4 := by ring

theorem pressure_derivative (h d dd : ℝ) :
  3*(4*h+d)-(12*h+7*d+dd)= -4*d-dd := by ring

theorem sound_coefficient (y q : ℝ) (hq : q≠0) (hy : y≠0) :
  -(-3/(16*q))/(9*(1/(4*y^2)))=y^2/(12*q) :=
by { field_simp [hy,hq], ring }

theorem tensor_improvement (xi jb it x : ℝ) :
  (it+xi*jb/2)-((6*xi-1)*jb/12-x/96)=it+jb/12+x/96 := by ring

theorem conformal_space (jb x : ℝ) :
  (6*(1/6:ℝ)-1)*jb/12-x/96= -x/96 := by ring

theorem speed_ratio (fs ft d : ℝ) (h : ft≠0) (relation : ft-fs=d) :
  fs/ft=1-d/ft := by { field_simp [h], linarith }

theorem delay_bound (ratio speed tolerance : ℝ) (hc : 0≤speed) (ht : tolerance≤1)
  (rel : speed^2=1-ratio) :
  1-tolerance≤speed ↔ ratio≤2*tolerance-tolerance^2 :=
begin
  split,
  { intro h, nlinarith [mul_nonneg (sub_nonneg.mpr h)
      (show 0≤speed+(1-tolerance), by linarith)] },
  { intro h, by_contra hn, push_neg at hn,
    have pos : 0<1-tolerance+speed := by linarith,
    nlinarith [mul_pos (sub_pos.mpr hn) pos] }
end

theorem chamber_mean (s u phi : ℝ) (eqn : s=u-phi) (charge : 2*s+u-phi=0) :
  u=phi ∧ s=0 := ⟨by linarith, by linarith⟩

theorem chamber_modes (k2 m2 phi s : ℝ) (h : k2+m2≠0)
  (eqn : (k2+m2)*s= -m2*phi) :
  phi+s=k2*phi/(k2+m2) :=
by { apply (eq_div_iff h).mpr, linear_combination eqn }

theorem rigid_spectrum (n e₁ e₂ : ℝ) :
  n*e₂-n*e₁=n*(e₂-e₁) := by ring

theorem density_slope (v n chi mu fracV fracMu : ℝ)
  (hn : v≠0) (hden : chi*mu≠0) (fixed : v*(n*fracV+chi*mu*fracMu)=0) :
  fracMu= -(n/(chi*mu))*fracV :=
begin
  have h := (mul_eq_zero.mp fixed).resolve_left hn,
  field_simp [hden, (mul_ne_zero_iff.mp hden).1, (mul_ne_zero_iff.mp hden).2],
  linear_combination h
end

theorem fixed_charge_scaling (l z v : ℝ) (hl : l≠0) :
  l^3*(z/l)*(v/l^2)=z*v := by { field_simp [hl], ring }

theorem energy_scaling (l kin grad quart : ℝ) (hl : l≠0) :
  l^3*(kin/l^4+grad/l^4+quart/l^4)=(kin+grad+quart)/l :=
by { field_simp [hl], ring }

theorem dilution_lowers (l energy : ℝ) (hl : 1<l) (he : 0<energy) :
  energy/l<energy :=
(div_lt_iff (show 0<l, by linarith)).mpr (by nlinarith [mul_pos he (sub_pos.mpr hl)])

open measure_theory
theorem dilation_integrals {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  [measurable_space E] [borel_space E] [finite_dimensional ℝ E]
  (ν : measure E) [measure.is_add_haar_measure ν] (dim : finite_dimensional.finrank ℝ E=3)
  (q e : E → ℝ) (l : ℝ) (hl : 0<l) :
  (∫ x, (1/l^3)*q (l⁻¹ • x) ∂ν)=(∫ x, q x ∂ν) ∧
  (∫ x, (1/l^4)*e (l⁻¹ • x) ∂ν)=(∫ x, e x ∂ν)/l :=
begin
  have hq := measure.integral_comp_inv_smul_of_nonneg ν q hl.le,
  have he := measure.integral_comp_inv_smul_of_nonneg ν e hl.le,
  rw [dim,smul_eq_mul] at hq he,
  constructor,
  { rw [integral_mul_left _ (λ x:E, q (l⁻¹ • x)),hq], field_simp [ne_of_gt hl], ring },
  { rw [integral_mul_left _ (λ x:E, e (l⁻¹ • x)),he], field_simp [ne_of_gt hl], ring }
end

theorem chamber_spring (c₁ c₂ k x₁ x₂ a₁ a₂ : ℝ) (h₁ : c₁≠0) (h₂ : c₂≠0)
  (left : c₁*a₁= -k*(x₁-x₂)) (right : c₂*a₂=k*(x₁-x₂)) :
  a₁-a₂= -k*(1/c₁+1/c₂)*(x₁-x₂) :=
by { field_simp [h₁,h₂], linear_combination c₂*left-c₁*right }

theorem driven_clock (w j s : ℝ) (h : w-j≠0) :
  1+s*j/(w-j)=(w-(1-s)*j)/(w-j) := by { field_simp [h], ring }

theorem weak_link_accuracy (w j tol : ℝ) (h : j<w) :
  j/(w-j)≤tol ↔ (1+tol)*j≤tol*w :=
by { rw [div_le_iff (sub_pos.mpr h)], split; intro a; linarith }

theorem passive_link_static (j : ℝ) (hj : j≠0) :
  1+j/(0-j)=0 := by { field_simp [hj] }

theorem charge_curvature (k2 r mass mu : ℝ) (h : k2=mass-mu^2) :
  k2*r+2*r^3=(mass-mu^2+2*r^2)*r := by { rw [h], ring }

-- Pointwise comparison at an interior extremum. Existence and regularity
-- of the one-dimensional boundary problem are inputs to the physics calculation.
theorem upper_barrier (k2 f g fpp gpp : ℝ) (hk : 0<k2) (hf : 0≤f)
  (eqf : fpp=k2*f+2*f^3) (eqg : gpp=k2*g) (maximum : fpp≤gpp) : f≤g :=
begin
  by_contra h, push_neg at h,
  nlinarith [mul_pos hk (sub_pos.mpr h), mul_nonneg (sq_nonneg f) hf]
end

theorem lower_barrier (k2 f r g fpp gpp : ℝ) (hk : 0<k2)
  (hf : 0≤f) (cap : f^2≤r^2) (eqf : fpp=k2*f+2*f^3)
  (eqg : gpp=(k2+2*r^2)*g) (minimum : gpp≤fpp) : g≤f :=
begin
  by_contra h, push_neg at h,
  have k : 0<k2+2*r^2 := by nlinarith [sq_nonneg r],
  nlinarith [mul_pos k (sub_pos.mpr h), mul_nonneg (sub_nonneg.mpr cap) hf]
end

theorem compliance_bound {α : Type*} [measurable_space α] (ν : measure_theory.measure α)
  (upper lower : α → ℝ) (hl : measure_theory.integrable lower ν)
  (hu : measure_theory.integrable upper ν) (h : ∀ z, lower z≤upper z) :
  (∫ z, lower z ∂ν) ≤ ∫ z, upper z ∂ν :=
measure_theory.integral_mono hl hu h

theorem twist_minimum (a b j : ℝ) :
  (a-j*b)^2=a^2-2*j*a*b+j^2*b^2 := by ring

theorem cylinder_null_stress (xi k m u uc grad : ℝ)
  (first_integral : grad=k*(u-uc)+u^2-uc^2) :
  m*u+(1-2*xi)*grad-2*xi*(k*u+2*u^2)=
  (1-6*xi)*u^2+(m+(1-4*xi)*k)*u-(1-2*xi)*(k*uc+uc^2) :=
by { rw [first_integral], ring }

theorem three_values (a b c u step : ℝ) (hs : step≠0)
  (h₀ : a*u^2+b*u+c=0)
  (h₁ : a*(u+step)^2+b*(u+step)+c=0)
  (h₂ : a*(u+2*step)^2+b*(u+2*step)+c=0) : a=0 ∧ b=0 :=
begin
  have h : a*(2*step^2)=0 := by linear_combination h₂-2*h₁+h₀,
  have ha : a=0 := (mul_eq_zero.mp h).resolve_right (mul_ne_zero (by norm_num) (pow_ne_zero _ hs)),
  have k : b*step=0 := by { rw [ha] at h₀ h₁, linear_combination h₁-h₀ },
  exact ⟨ha,(mul_eq_zero.mp k).resolve_right hs⟩
end

theorem no_sourced_cylinder (xi k m : ℝ) (hk : 0<k) (hm : 0≤m)
  (quartic : 1-6*xi=0) : 0<m+(1-4*xi)*k :=
by { have h : xi=1/6 := by linarith, rw [h], linarith }

theorem cylinder_interval_obstruction (xi k m c a b : ℝ) (hk : 0<k) (hm : 0≤m)
  (hab : a<b) (null_eq : ∀ u ∈ set.Icc a b,
     (1-6*xi)*u^2+(m+(1-4*xi)*k)*u+c=0) : false :=
begin
  let d := (b-a)/2,
  have hd : 0<d := by { dsimp [d], linarith },
  have h₀ := null_eq a ⟨le_refl _,hab.le⟩,
  have h₁ := null_eq (a+d) (show a+d ∈ set.Icc a b, by { split; dsimp [d]; linarith }),
  have h₂ := null_eq (a+2*d) (show a+2*d ∈ set.Icc a b, by { split; dsimp [d]; linarith }),
  rcases three_values _ _ _ a d (ne_of_gt hd) h₀ h₁ h₂ with ⟨ha,hb⟩,
  exact (ne_of_gt (no_sourced_cylinder xi k m hk hm ha)) hb
end

theorem null_focusing (area ricci acceleration : ℝ) (ha : 0<area)
  (hr : 0≤ricci) (eqn : 2*acceleration= -area*ricci) : acceleration≤0 :=
by nlinarith [mul_nonneg ha.le hr]

theorem central_block_mass {T : Type*} [comm_ring T] (left right entry : T) :
  left*(left*entry-entry*right)-(left*entry-entry*right)*right=(left-right)^2*entry := by ring

theorem energy_budget (r2 y h m : ℝ) (hy : 0<y) (hr : 0≤r2)
  (hh : 0≤h) (hm : 0≤m) (ineq : 3*r2^2≤3*y^2*m^2*h^2) : r2≤y*m*h :=
begin
  by_contra n, push_neg at n, have k := mul_nonneg (mul_nonneg hy.le hm) hh,
  have p : 0<r2+y*m*h := by linarith,
  nlinarith [mul_pos (sub_pos.mpr n) p]
end

theorem fixed_density_loop_shift (t u shape slope : ℝ)
  (tadpole : 2*t-4*u= -(2*shape-2*slope+3/2))
  (charge : t+u=slope) :
  u=shape/3+1/4 ∧ t/2=(slope-shape/3-1/4)/2 :=
⟨by linear_combination (1/3)*charge-(1/6)*tadpole,
 by linear_combination (1/12)*tadpole+(1/3)*charge⟩

theorem phonon_pair_shell (p q : ℝ) (root : q^2=7) (pvalue : p=1+2*q) :
  (p+3)^2=36+8*p := by { rw [pvalue], linear_combination 4*root }

theorem decay_vertex_square (p h : ℝ) (hp : p+3≠0) (hh : h^2=3) :
  ((p-5)/(2*h*(p+3))-2/(h*(p+3)))^2=(p-9)^2/(12*(p+3)^2) :=
begin
  have hne : h≠0 := by { rintro rfl, norm_num at hh },
  have step : (p-5)/(2*h*(p+3))-2/(h*(p+3))=(p-9)/(2*h*(p+3)) :=
    by { field_simp [hne,hp], ring },
  rw [step,div_pow,mul_pow,mul_pow,hh], norm_num
end

theorem decay_channel_open : (0:ℝ)<12 ∧ (12:ℝ)<4^2 := by norm_num

end cat_rotating_response
