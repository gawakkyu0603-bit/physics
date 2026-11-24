import tactic
import analysis.inner_product_space.basic
import analysis.special_functions.trigonometric.basic
import measure_theory.integral.bochner
import analysis.fourier.riemann_lebesgue_lemma

noncomputable theory
open measure_theory
open_locale big_operators topology fourier_transform complex_conjugate
namespace material_shell_discharge

-- Positive masses, the exterior branch of Israel's equation and spherical
-- surface stress are physical inputs to these algebraic consequences.
theorem pressure_work (K R : ℝ) (h : R ≠ 0) :
  K/R^2 = (K/(8*real.pi*R^3))*(8*real.pi*R) :=
by {field_simp [h,ne_of_gt real.pi_pos];ring}

theorem parent_equilibrium :
  (1:ℝ)-2/3/2=2/3 ∧ (1:ℝ)-(2/3)=1/3 ∧ (2:ℝ)*(2/3)*(2/3)=8/9 :=
by norm_num

theorem kinetic_fraction (h j p q : ℝ)
 (inner_mass : h^2=(1-q)^2-p^2) (outer_mass : j^2=q^2-p^2) :
 q=(1-h^2+j^2)/2 := by nlinarith

theorem inner_mass_gap (q h j : ℝ) (kin : 2*q=1-h^2+j^2) :
 (1-1/3)-((1-q)-h^2/3)=q/3+j^2/3 := by nlinarith

theorem middle_gradient (q h p : ℝ) (kin : h^2=(1-q)^2-p^2) :
 (1-(2/3:ℝ)*(1-q))^2-((2/3:ℝ)*p)^2 =
  1-(4/3:ℝ)*((1-q)-h^2/3) := by {rw [kin];ring}

theorem partition_outer_initial (q j p : ℝ) (kin : j^2=q^2-p^2)
 (hj : j≠0) : (q/(3*j))^2-1/9=(p/(3*j))^2 :=
by {field_simp [hj];nlinarith}

theorem shell_energy_radial (m h z : ℝ) : m*z*((1-h^2)/2)=m*z/2-m*z*h^2/2 := by ring

theorem radial_terminal_mass (m : ℝ) : m/2=(3/4:ℝ)*(m*(1-1/3)) := by ring

theorem radial_path_fails (h : ℝ) (hh : h < 1) (hp : 0 ≤ h) :
 16*h < (3+h^2)^2 :=
begin
 have A : 0<(1-h)*(1-h) := mul_pos (by linarith) (by linarith),
 have B : 0 < h^2+2*h+9 := by nlinarith [sq_nonneg h],
 nlinarith [mul_pos A B]
end

theorem bounce_minimum_discriminant (h q : ℝ) (hh : 0<h) :
 27*(h/3)*((1-q)/h-h/3)^2 < 4 ↔ (3*(1-q)-h^2)^2 < 4*h :=
begin
 have e : 27*(h/3)*((1-q)/h-h/3)^2*h=(3*(1-q)-h^2)^2 :=
 by {field_simp [ne_of_gt hh];ring},
 rw [←e], exact (mul_lt_mul_right hh).symm
end

theorem minimum_of_shell_energy (a b y : ℝ) (hp : 0 < y)
  (turn : a*y^3=2*b) :
 (a*y+b/y^2)^3=(27/4:ℝ)*b*a^2 :=
begin
 have hb : b=a*y^3/2 := by linarith,
 rw [hb], field_simp [ne_of_gt hp];ring
end

theorem limiting_recoil_numerator (t : ℝ) :
 (t^4+2*t)^2-9*t^4 = t^2*(1-t)^2*(t+2)*(t^3+3*t+2) := by ring

theorem limiting_recoil_denominator (t : ℝ) :
 3-t^4-2*t=(1-t)*(t^3+t^2+t+3) := by ring

theorem small_split_recoil_sq :
 (1:ℝ)^2*(1+2)*(1^3+3*1+2)/(1^3+1^2+1+3)^2=1/2 := by norm_num

theorem bounce_outside (x : ℝ) (hx : x < 2/3) :
 x*(2-x)<8/9 :=
begin
 have h : 0 < (2/3-x)*(4/3-x) := mul_pos (by linarith) (by linarith),
 nlinarith
end

theorem escape_polynomial (y a : ℝ) :
 y^3-9*a*y+8*a=(y-4/3)^2*(y+8/3)+(16/27-a)*(9*y-8) := by ring

theorem sufficient_escape (y a : ℝ) (hy : 1≤y) (ha : a<16/27) :
 0<y^3-9*a*y+8*a :=
begin
 rw [escape_polynomial],
 exact add_pos_of_nonneg_of_pos
 (mul_nonneg (sq_nonneg _) (by linarith)) (mul_pos (by linarith) (by linarith))
end

theorem outer_potential (a b c y : ℝ) (hy : y≠0) :
 (a*y-b/y^2)^2-(1-c/y)=a^2*y^2-1+(c-2*a*b)/y+b^2/y^4 :=
by {field_simp [hy];ring}

theorem stationary_equation (a b c y : ℝ) (hy : y≠0) :
 (2*a^2*y-c/y^2-4*b^2/y^5)*y^5=2*a^2*(y^3)^2-c*y^3-4*b^2 :=
by {field_simp [hy];ring}

theorem sign_for_arrival_order (a b c d y : ℝ) (hy : y≠0) :
 ((a*y+b/y^2)-(c*y-d/y^2))*y^2=(a-c)*y^3+(b+d) :=
by {field_simp [hy];ring}

theorem later_arrival_endpoints {f : ℝ → ℝ} (l mid high : ℝ)
 (left : 0 < f l) (right : 0 < f high)
 (rising : ∀ x, l≤x → x≤mid → f l≤f x)
 (falling : ∀ x, mid≤x → x≤high → f high≤f x)
 (x : ℝ) (hx : l≤x) (hy : x≤high) : 0<f x :=
by {cases le_total x mid with h h,
 exact lt_of_lt_of_le left (rising x hx h),
 exact lt_of_lt_of_le right (falling x h hy)}

theorem stress_decomposition (u v omega s : ℝ) (hv : 0<v) (hw : 0<omega) :
 (u^2+v^2+omega^2*s^2)/(2*omega*v)=s+(u^2+(v-omega*s)^2)/(2*omega*v) :=
by {field_simp [ne_of_gt hv,ne_of_gt hw];ring}

theorem wave_recoil_above_ray (u v omega s : ℝ) (hv : 0<v) (hw : 0<omega) :
 s≤(u^2+v^2+omega^2*s^2)/(2*omega*v) :=
begin
 rw [stress_decomposition u v omega s hv hw],
 exact le_add_of_nonneg_right (div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
 (le_of_lt (mul_pos (mul_pos (by norm_num) hw) hv)))
end

theorem sphere_line (a b : ℝ) : (a+1/2)+(b+1/2)=a+b+1 := by ring

theorem axial_gradient_weight (j x : ℝ) :
 (1+x^2)*(1-x^2)+(1-j)*(1+x^2)^2 =
 (1+x^2)*(2-j-j*x^2) := by ring

theorem highest_mode_derivative_sign (j x : ℝ) (hj : 2≤j) (hx : 0≤x) :
 2*x*(2-j-j*x^2) ≤ 0 :=
begin
 have h : 0≤j*x^2 := mul_nonneg (by linarith) (sq_nonneg _),
 exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
end

-- The spectral theorem for a singular Friedrichs Hamiltonian, its static
-- Green function and the positive-frequency Wronskian are cited inputs.
theorem inverse_moment_bound (k c j extra : ℝ) (hk : 0≤k) (hc : 0<c)
 (hj : 0<j) (he : 0≤extra) :
 k/(c*(j+extra))≤k/(c*j) :=
begin
 apply div_le_div_of_le_left hk (mul_pos hc hj),
 exact mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hc)
end

theorem pole_exclusion (gap moment self E : ℝ)
 (h : moment<gap) (hi : self≤moment) (he : E≤0) :
 0<gap-E-self := by linarith

theorem no_positive_pole (im_self : ℝ) (h : 0<im_self) : -im_self≠0 := by linarith

theorem resolvent_moment {α : Type*} [measurable_space α] (μ : measure α)
 (g nu : α → ℝ) (E : ℝ) (he : E≤0) (hn : ∀ x, 0<nu x)
 (hi : integrable (λ x, (g x)^2/(nu x-E)) μ)
 (hj : integrable (λ x, (g x)^2/nu x) μ) :
 (∫ x, (g x)^2/(nu x-E) ∂μ) ≤ ∫ x, (g x)^2/nu x ∂μ :=
begin
 apply integral_mono hi hj,
 intro x,
 have denom : nu x ≤ nu x - E := by simpa only [sub_zero] using (sub_le_sub_left he (nu x)),
 exact div_le_div_of_le_left (sq_nonneg _) (hn x) denom
end

theorem clockwise_root (a b y : ℝ) (hy : y≠0) :
 a*y+b/y^2-(a+b)=(y-1)*((a-2*b)+b*(y-1)*(3+2*(y-1))/y^2) :=
by {field_simp [hy];ring}

theorem force_starts_outward (h q : ℝ) (hh : 0<h) (branch : h^2<1-q) :
 0 < (1-q)/h-h :=
by {rw [sub_pos,lt_div_iff hh],nlinarith}

theorem zero_form_function (gap moment self E : ℝ) (hi : self≤moment)
 (positive : moment<gap) (he : E≤0) : gap-E-self≠0 :=
ne_of_gt (pole_exclusion gap moment self E positive hi he)

theorem spectral_kernel_bound (field alpha u v : ℝ) (g : 0≤v)
 (field_norm : field≤u+v) (interaction : alpha≤v*field) :
 alpha≤v*u+v^2 :=
by nlinarith [mul_le_mul_of_nonneg_left field_norm g]

theorem quadratic_cap_root (t s : ℝ) (ht : t≠0) (h : s^2=1+4/t) :
 t*(((s-1)/2)^2+(s-1)/2)=1 :=
begin
 have hh : t*(s^2-1)=4 := by {rw [h],field_simp [ht];ring},
 calc t * (((s-1)/2)^2+(s-1)/2) = t*(s^2-1)/4 : by ring
 ... = 1 : by rw [hh];norm_num
end

theorem positive_cap_denominator (t s : ℝ) (ht : 0<t) (hs : 1<s)
 (h : s^2=1+4/t) : (s-1)/2=2/(t*(s+1)) :=
begin
 have hh : t*(s^2-1)=4 := by {rw [h],field_simp [ne_of_gt ht];ring},
 have hp : 0<s+1 := by linarith,
 apply (eq_div_iff (ne_of_gt (mul_pos ht hp))).2,
 calc (s-1)/2*(t*(s+1)) = t*(s^2-1)/2 : by ring
 ... = 2 : by rw [hh];norm_num
end

theorem completed_square (gap a b g : ℝ) :
 gap*a^2+b^2+2*g*a*b=(gap-g^2)*a^2+(b+g*a)^2 := by ring

theorem energy_controls_field (x u v gap a : ℝ) (hu : 0≤u) (hv : 0≤v)
 (stability : v^2≤gap) (energy : x^2-2*v*a*x+gap*a^2≤u^2)
 (ha : 0≤a) (upper : a≤1) : x≤u+v :=
begin
 by_contra' bad,
 have av : v*a≤v := by nlinarith [mul_nonneg hv (sub_nonneg.mpr upper)],
 have pos : 0 < (x-v*a-u)*(x-v*a+u) := mul_pos (by linarith) (by linarith),
 nlinarith [mul_nonneg (sub_nonneg.mpr stability) (sq_nonneg a)]
end

theorem capture_probability (a k norm : ℝ) (ha : 0≤a) (hn : 0≤norm) (h : a≤norm)
 (hprob : k≤1-norm^2) : k≤1-a^2 :=
by nlinarith [mul_nonneg (sub_nonneg.mpr h) (add_nonneg hn ha)]

theorem emitter_inverse_capture {E : Type*} [normed_add_comm_group E]
 [inner_product_space ℂ E] (state retained : E)
 (unitary_norm : ‖state‖=1) (overlap : @inner ℂ E _ (state-retained) retained=0) :
 ‖state-retained‖^2=1-‖retained‖^2 :=
begin
 have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (state-retained) retained overlap,
 rw [sub_add_cancel,unitary_norm] at h,
 nlinarith
end

theorem width_from_elapsed (gap radius redshift advanced : ℝ)
 (hr : radius≠0) : (gap*redshift/radius)*advanced=gap*(redshift*advanced/radius) :=
by {field_simp [hr];ring}

theorem bound_from_accumulated_rotation (delta t i w : ℝ) (ht : 0≤t)
 (h : delta≤t*(i*w+i^2)) : 1-t*(i*w+i^2)≤1-delta := by linarith

theorem exact_gate_needs_orthogonality (prob survival : ℝ)
 (p : prob=1) (bound : prob≤1-survival^2) : survival=0 :=
by nlinarith [sq_nonneg survival]

theorem largest_mode_average {ι : Type*} [fintype ι] (f : ι→ℝ) (hi mean : ℝ)
 (hb : ∀ i, f i ≤ hi) (trace_id : (∑ i, f i)=fintype.card ι*mean)
 (hcount : 0 < (fintype.card ι:ℝ)) : mean≤hi :=
begin
 have h := finset.sum_le_sum (λ i (_ : i∈(finset.univ:finset ι)), hb i),
 simp only [finset.sum_const,finset.card_univ,nsmul_eq_mul] at h,
 rw [trace_id] at h,
 exact le_of_mul_le_mul_left h hcount
end

theorem hemispheres_pair (top bottom full : ℝ) (equal_halves : top=bottom)
 (partition : top+bottom=full) : top=full/2 := by linarith

theorem common_gain_ratio (gain lo hi x : ℝ) (g : 0≤gain) (hlo : 0≤lo)
 (hhi : 0<hi) (upper : gain*hi≤1) (lower : x≤gain*lo) :
 x≤lo/hi :=
begin
 apply (le_div_iff hhi).2,
 have p := mul_le_mul_of_nonneg_right lower (le_of_lt hhi),
 nlinarith [mul_le_mul_of_nonneg_right upper hlo]
end

theorem speed_cost (s t y : ℝ) (ht : 0<t) (hy : 0≤y) (hs : 0≤s)
 (root : t*(s+s^2)=1) (capture : 1≤t*(y+y^2)) : s^2≤y^2 :=
begin
 have sy : s≤y,
 {by_contra' bad,
  have H : 0<(s-y)*(1+s+y) := mul_pos (by linarith) (by linarith),
  have yy : y+y^2 < s+s^2 := by nlinarith,
  linarith [mul_lt_mul_of_pos_left yy ht]},
 nlinarith [mul_nonneg (sub_nonneg.mpr sy) (add_nonneg hy hs)]
end

theorem eigenvalue_envelope (low high edge mean : ℝ) (hmean : 0<mean)
 (hlo : 0≤low) (hmax : mean≤high) (hmin : low≤edge) :
 low/high≤edge/mean :=
begin
 apply (div_le_div_iff (lt_of_lt_of_le hmean hmax) hmean).2,
 nlinarith [mul_nonneg hlo (sub_nonneg.mpr hmax),
  mul_nonneg (sub_nonneg.mpr hmin) (le_of_lt (lt_of_lt_of_le hmean hmax))]
end

theorem angular_dark (g a b : ℝ) (h : a+b=0) : g*a+g*b=0 := by rw [←mul_add,h,mul_zero]

theorem no_joint_recovery (exact small threshold : ℝ)
 (h1 : threshold≤exact) (h2 : exact≤small) (h3 : small<threshold) : false := by linarith

-- Extend the absolutely continuous spectral density by zero below threshold.
-- Frequency here is in cycles per time; the state phase is exp(-2*pi*i*f*t).
theorem decay_of_material_amplitude (density : ℝ → ℂ) (mass : integrable density) :
 filter.tendsto (𝓕 density) (filter.cocompact ℝ) (𝓝 0) :=
real.zero_at_infty_fourier_integral density

theorem gate_obstruction_at_nonnegative_energy (theta t gap : ℝ) (g : 0<gap)
 (slow : t*gap<theta) (orthogonality_time : theta≤t*gap) : false :=
(not_le_of_gt slow) orthogonality_time

theorem free_delay_on_multiplet (phase inv entry : ℂ) (h : phase*inv=1) :
 phase*entry*inv=entry :=
calc phase*entry*inv=(phase*inv)*entry : by ring
 ... = entry : by rw [h,one_mul]

theorem required_time_modes (n : ℕ) (span : 37≤5*n) : 8≤n := by omega

theorem vacuum_count_for_code {E ι : Type*} [normed_add_comm_group E]
 [inner_product_space ℂ E] [fintype ι] (v : ι → E) (vac : E)
 (hv : orthonormal ℂ v) (unit : ‖vac‖=1) :
 (∑ i, ‖@inner ℂ E _ (v i) vac‖^2)≤1 :=
begin
 have b : (∑ i, ‖@inner ℂ E _ (v i) vac‖^2) ≤ ‖vac‖^2 := hv.sum_inner_products_le vac,
 simpa only [unit,one_pow] using b
end

theorem average_requires_photon (d prob photons : ℝ) (hd : 0<d)
 (vacuum : d*prob≤1) (number : 1-prob≤photons) : 1-1/d≤photons :=
begin
 have h : prob≤1/d := (le_div_iff hd).2 (by simpa only [mul_comm] using vacuum),
 linarith
end

theorem evaporation_rate_integral (M a j tail : ℝ) (ha : a≠0) :
 (j*tail/(16*real.pi^2*a))*M =
  2*M*(j*tail/(32*real.pi^2*a)) :=
by {field_simp [ha,ne_of_gt real.pi_pos];ring}

theorem late_code_obstruction (lower coeff Mi Mf : ℝ) (hc : 0≤coeff)
 (budget : coeff*Mi^2 < lower) (needed : lower≤coeff*(Mi^2-Mf^2)) : false :=
by nlinarith [mul_nonneg hc (sq_nonneg Mf)]

theorem vacuum_swap_overlap {ι : Type*} [fintype ι] (p : ι → ℂ) :
 (∑ i, p i * conj (p i)) = (∑ i, ((complex.norm_sq (p i):ℝ):ℂ)) :=
by simp_rw [complex.mul_conj]

theorem bell_blank_value (D tr : ℝ) (h : tr=1) : tr/D^2=1/D^2 := by rw [h]

theorem ideal_decoder_vacuum_bound {E : Type*} [normed_add_comm_group E]
 [inner_product_space ℂ E] (full projected rest : E) (unit : ‖full‖=1)
 (perp : @inner ℂ E _ full rest=0) :
 ‖@inner ℂ E _ full (projected+rest)‖ ≤ ‖projected‖ :=
begin
 rw [inner_add_right,perp,add_zero],
 have c := @norm_inner_le_norm ℂ E _ _ _ full projected,
 simpa only [unit,one_mul] using c
end

theorem independent_early_radiation (vac d : ℝ) (h : 0<d) (v : 0≤vac)
 (upper : vac^2≤(1/d)^2) : 1-1/d≤1-vac :=
begin
 have a : 0<1/d := one_div_pos.mpr h,
 by_contra' bad,
 have hh : 0<(vac-1/d)*(vac+1/d) := mul_pos (by linarith) (by linarith),
 nlinarith
end

theorem early_recovery_required (n early vac : ℝ) (hn : n≤1)
 (photons : 1-n≤vac) (overlap : vac^2≤early) : 1-early≤n*(2-n) :=
by nlinarith [mul_nonneg (sub_nonneg.mpr photons) (show 0≤vac+(1-n), by linarith)]

theorem squared_overlap_angle (a b c d : ℝ) :
 (a*b+c*d)^2+(a*d-c*b)^2=(a^2+c^2)*(b^2+d^2) := by ring

theorem same_photon_references {E F ι : Type*} [normed_add_comm_group E]
 [inner_product_space ℂ E] [normed_add_comm_group F] [inner_product_space ℂ F]
 (w : E →ₗᵢ[ℂ] F) (v : ι→E) (i j : ι) :
 @inner ℂ F _ (w (v i)) (w (v j)) = @inner ℂ E _ (v i) (v j) :=
 w.inner_map_map _ _

end material_shell_discharge
