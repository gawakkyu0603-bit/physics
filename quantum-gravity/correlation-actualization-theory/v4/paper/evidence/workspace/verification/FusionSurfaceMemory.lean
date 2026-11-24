import tactic
import analysis.special_functions.trigonometric.deriv
import analysis.special_functions.trigonometric.arctan
import analysis.special_functions.log.basic
import measure_theory.integral.bochner
import measure_theory.group.add_circle

noncomputable theory
open measure_theory measure_theory.measure
open_locale big_operators ennreal

namespace fusion_surface_memory

-- Algebra of the Israel rest-energy functional on the ordinary exterior branch.
theorem rest_energy (R G F : ℝ) (hR : R ≠ 0) (hG : G ≠ 0) :
  R*F/G-G*(R*F/G)^2/(2*R) = R/G*(F-F^2/2) :=
by { field_simp [hR,hG];ring }

theorem example_static_energy (r : ℝ) (hr : r≠0) :
 let F := (1+1/r^3)/4 in r*(F-F^2/2)=7*r/32+3/(16*r^2)-1/(32*r^5) :=
by {dsimp,field_simp [hr];ring}

theorem pressure_work (F A b : ℝ) :
 (1/2:ℝ)*b*F+b*A-b*F=b*(A-F/2) := by ring

theorem equilibrium_slope (z A : ℝ) (hz : z ≠ 0) (hF : 1-z ≠ 0)
 (eq : 4*z*A=1-z^2) : A/(1-z)=(1+z)/(4*z) :=
begin
 apply (div_eq_div_iff hF (show 4*z≠0, from mul_ne_zero (by norm_num) hz)).2,
 nlinarith
end

theorem radial_mode (z s : ℝ) (hz : z ≠ 0) :
 let g := (1+z)/(4*z) in
  2*g*(z-2*g*(1-z)+2*z*s) = (1+z)*(s-(1-3*z^2)/(4*z^2)) :=
by { dsimp,field_simp [hz];ring }

theorem sound_ceiling (z s : ℝ) (hz : 0 < z) :
 let g := (1+z)/(4*z) in
 (g*(1+s)-1/4)/(g+1/2) ≤ 1 ↔ s ≤ 3*z/(1+z) :=
begin
 dsimp,
 have h : (0:ℝ)<(1+z)/(4*z)+1/2 := by positivity,
 rw [div_le_iff h, le_div_iff (show 0<1+z, by linarith)],
 have ident : ((1+z)/(4*z)*(1+s)-1/4-(1*((1+z)/(4*z)+1/2)))*(4*z)=s*(1+z)-3*z :=
 by {field_simp [ne_of_gt hz];ring},
 have hz' : (0:ℝ)<4*z := by linarith,
 constructor;intro hh,
 { have t := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hh) hz'.le,
   linarith },
 { have t : ((1+z)/(4*z)*(1+s)-1/4-(1*((1+z)/(4*z)+1/2)))*(4*z) ≤ (0:ℝ)*(4*z) :=
   by {rw [zero_mul, ident],linarith},
   linarith [(mul_le_mul_right hz').mp t] }
end

theorem stability_window (z : ℝ) (hz : 0 < z) :
 (1-3*z^2)/(4*z^2)<3*z/(1+z) ↔ 0<15*z^3+3*z^2-z-1 :=
begin
 rw [div_lt_div_iff (show 0<4*z^2, by positivity) (show 0<1+z, by linarith)],
 split;intro h;nlinarith
end

theorem convex_empty_slope (z : ℝ) (hz : 0<z) (h : 1≤(1+z)/(4*z)) :
 z≤1/3 := by { rw [le_div_iff (show 0<4*z, by positivity)] at h,linarith }

theorem small_lapse_fails (z : ℝ) (hp : 0≤z) (h : z≤1/3) :
 15*z^3+3*z^2-z-1<0 :=
begin
 have h1 : z*z≤(1/3)*z := mul_le_mul_of_nonneg_right h hp,
 have h2 := mul_le_mul_of_nonneg_right h1 hp,
 nlinarith
end

theorem example_response :
 let z : ℝ := 1/2, g : ℝ := 3/4, s : ℝ := 1/2 in
 (1+z)*(s-(1-3*z^2)/(4*z^2))=3/8 ∧
 (g*(s+1)-1/4)/(g+1/2)=7/10 ∧ g-1/2=1/4 ∧
 ((1/4:ℝ)-(1/4)^2/2)/((1/2)-(1/2)^2/2)=7/12 := by norm_num

theorem bending_unstable (p D k : ℝ) (hk : 0 < k) (h : D*k^2 < p) :
 -p*k^2+D*k^4 < 0 := by nlinarith [mul_pos (sub_pos.mpr h) (sq_pos_of_pos hk)]

-- Spin channel Cayley phases can be compared before division by a nonzero denominator.
theorem cayley_opposite (a b : ℂ) :
 (1-complex.I*a)*(1+complex.I*b)+(1-complex.I*b)*(1+complex.I*a)=2*(1+a*b) :=
by { linear_combination (-(2*a*b)) * complex.I_sq }

-- Eliminate the displacement of a bonded tensile sheet at fixed wave number.
theorem bonded_square (K t q a b : ℝ) (hn : K+t*q≠0) :
 K*(a-b)^2+t*q*b^2=(K+t*q)*(b-K*a/(K+t*q))^2+K*t*q/(K+t*q)*a^2 :=
by {field_simp [hn];ring}

theorem bonded_sufficient (K t p D q : ℝ) (hK : 0<K) (ht : 0≤t) (hq : 0≤q)
 (hpt : p≤t) (bend : p*t≤K*D) (hD : 0≤D) :
 0 ≤ K*t*q/(K+t*q)+D*q^2-p*q :=
begin
 have h : 0<K+t*q := add_pos_of_pos_of_nonneg hK (mul_nonneg ht hq),
 have id : (K*t*q/(K+t*q)+D*q^2-p*q)*(K+t*q) =
 q*(K*(t-p)+(K*D-p*t)*q+D*t*q^2) := by {field_simp [ne_of_gt h];ring},
 apply (mul_le_mul_right h).mp, rw [zero_mul,id],
 exact mul_nonneg hq (add_nonneg (add_nonneg (mul_nonneg hK.le (sub_nonneg.mpr hpt))
 (mul_nonneg (sub_nonneg.mpr bend) hq)) (mul_nonneg (mul_nonneg hD ht) (sq_nonneg q)))
end

theorem static_total_pressure (z : ℝ) (hp : 0<z) (hq : z<1) : 0<(1-z)/(4*z) :=
div_pos (sub_pos.mpr hq) (by positivity)

theorem exterior_reference (z u : ℝ) (hz : 0<z) (hu : 0<u) (flat_or_ds : u≤1)
 (massive : z<1) : 0<(1+z^2)/(2*z)-(2*u-1/u) :=
begin
 have hs : 0<(1-z)^2 := sq_pos_of_pos (sub_pos.mpr massive),
 have ha : 1<(1+z^2)/(2*z) := (lt_div_iff (show 0<2*z, by positivity)).2 (by nlinarith),
 have hb : 1≤1/u := (le_div_iff hu).2 (by linarith),
 linarith
end

-- One-sided exterior, with the outward normal at its inner boundary pointing
-- toward decreasing radius. Lapse constraint and the matching radial actions.
theorem boundary_static_shift (u F : ℝ) : u-(u-1+F)=1-F := by ring

theorem exterior_lapse_constraint (R G M V D : ℝ) (hR : R ≠ 0) (hG : G ≠ 0)
 (h : 1-2*G*M/R+V^2=D^2) : M=R/(2*G)*(1-D^2+V^2) :=
begin
 have eq : (1-2*G*M/R+V^2)*R=D^2*R := congr_arg (λ t : ℝ, t*R) h,
 field_simp [hR] at eq,
 field_simp [hG];nlinarith
end

theorem geometric_static_pressure (u : ℝ) (hp : u≠0) :
 2*u-1/u-(u^2-1)/u=u := by {field_simp [hp];ring}

theorem tensile_matter (u : ℝ) (hp : (5/4:ℝ)<u) :
 (5/4-u)/(2*(u-1/2))<0 :=
div_neg_of_neg_of_pos (sub_neg.mpr hp) (by linarith)

theorem material_density_response (u : ℝ) (hu : u≠0) :
 (-(u-3/4)/4+1/2)+(u^2-1)^2/(4*u^3)=11/16-1/(2*u)+1/(4*u^3) :=
by {field_simp [hu];ring}

theorem material_inertia (u : ℝ) (hu : u≠0) :
 (u-3/4)/2+1/2-(u^2-1)/(2*u)=1/8+1/(2*u) :=
by {field_simp [hu];ring}

theorem slice_stiffness : (1-(1/2:ℝ))*(3/8)=3/16 := by norm_num

-- Coefficients of sqrt(u^2+V^2+2 R A) to second order about R=1.
theorem square_root_quadratic (u X V A : ℝ) (hu : u≠0) :
 let h1 := A/u, h2 := (V^2+2*X*A)/(2*u)-A^2/(2*u^3) in
 2*u*h1=2*A ∧ h1^2+2*u*h2=V^2+2*X*A :=
by {dsimp;split;field_simp [hu];ring}

theorem curvature_quadratic_work (u X V A : ℝ) (hu : u≠0) :
 X*(A/u)+(V^2+2*X*A)/(2*u)-A^2/(2*u^3)=
 -3*V^2/(2*u)-A^2/(2*u^3)+(2/u)*(V^2+X*A) :=
by {field_simp [hu];ring}

theorem radial_force_variation (u X A S : ℝ) (hu : u≠0) :
 (2*A-9*X/8)-(-3*X/2)-(3*A/u-S/u^3)=
 S/u^3+(2-3/u)*A+3*X/8 := by {field_simp [hu];ring}

theorem complex_root_example (u : ℝ) (hu : 0<u) (sqr : u^2=2) :
 (2-3/u)^2-3/(2*u^3)<0 :=
begin
 have h1 : u<3/2 :=
 begin
  cases lt_or_ge u (3/2) with H H,
  {exact H},
  {exfalso,
   have hp : 0≤(u-3/2)*(u+3/2) := mul_nonneg (sub_nonneg.mpr H) (by linarith only [hu]),
   nlinarith only [hp,sqr]}
 end,
 have id : ((2-3/u)^2-3/(2*u^3))*(2*u^3)=8*u^3-24*u^2+18*u-3 :=
 by {field_simp [ne_of_gt hu];ring},
 have hc : u^3=2*u := by {calc u^3=u*u^2 : by ring
                            ... = 2*u : by rw [sqr,mul_comm]},
 apply (mul_lt_mul_right (show 0<2*u^3, by positivity)).mp,
 rw [zero_mul,id,hc,sqr], linarith only [h1]
end

theorem opposite_residue_polynomial (x : ℝ) :
 x^2/8-x/2+3/8=(x-1)*(x-3)/8 := by ring

theorem opposite_residues (x : ℝ) (h1 : x-1 ≠ 0) (h3 : x-3 ≠ 0) :
 8/((x-1)*(x-3))=4/(x-3)-4/(x-1) := by {field_simp [h1,h3];ring}

theorem empty_marker_flight (x v : ℝ) (hx : x≠0)
 (h : x*((7/16:ℝ)+v^2)=7/16) : v^2=(7/16)*(1/x-1) :=
by {field_simp [hx];nlinarith}

theorem empty_marker_horizon : (7/16:ℝ)*(1/(7/16)-1)=(3/4)^2 := by norm_num

theorem empty_clock_primitive (θ a : ℝ) :
 has_deriv_at (λ x : ℝ, (x+real.sin x*real.cos x)/a) (2*(real.cos θ)^2/a) θ :=
begin
 convert (((has_deriv_at_id θ).add ((real.has_deriv_at_sin θ).mul (real.has_deriv_at_cos θ))).div_const a) using 1,
 apply congr_arg (λ v : ℝ, v/a),
 nlinarith [real.sin_sq_add_cos_sq θ]
end

theorem empty_clock_trajectory (s c a : ℝ) (circle : s^2+c^2=1) (hc : c≠0) (ha : a≠0) :
 ((-2*c*s)/(2*c^2/a))^2=a^2*(1/c^2-1) :=
begin
 have hs : s^2=1-c^2 := by linarith,
 have move : ((-2*c*s)/(2*c^2/a))^2=a^2*s^2/c^2 := by {field_simp [hc,ha];ring},
 rw [move,hs],field_simp [hc];ring
end

theorem exchange_tuning (h : ℝ) (tune : 3*h^2=64) :
 1+(h/8)*(-3*h/8)=0 := by nlinarith

theorem exchange_unit_denominator (a : ℝ) : 0 < 1+a^2 := by nlinarith [sq_nonneg a]

theorem swap_components (trip sing : ℂ) (h : sing = -trip) :
 (trip+sing)/2=0 ∧ (trip-sing)/2=trip := by {rw [h];constructor;ring}

theorem defect_entropy_step (N k s : ℝ) :
 (N*s-s*2)-((N-k)*s-s*2)=k*s := by ring

theorem parity_step (m k : ℕ) (h : k≤m) :
 2^(m-k)*2^k=(2:ℕ)^m := by rw [←pow_add,nat.sub_add_cancel h]

theorem singleton_recoil (M E D : ℝ) (hM : M ≠ 0) (mass_shell : D^2=M^2-2*M*E) :
 E=(M^2-D^2)/(2*M) :=
by { field_simp [hM];nlinarith }

theorem pair_recoil (M x y E c : ℝ) (hM : M ≠ 0)
 (vertex : 2*M*(x+y)-2*x*y*(1-c)=2*M*E) :
 x+y=E+x*y*(1-c)/M :=
by { field_simp [hM];nlinarith }

theorem recoil_moment_cost (x y c : ℝ) (hx : 0≤x) (hy : 0≤y)
 (hc : -1≤c) : x*y*(1-c)≤x^2+y^2 :=
begin
 have h := mul_nonneg (mul_nonneg hx hy) (show 0≤1+c, by linarith),
 nlinarith [sq_nonneg (x-y)]
end

theorem sine_distance (x y : ℝ) : |real.sin x-real.sin y| ≤ |x-y| :=
begin
 have d : ∀ t : ℝ, ‖deriv real.sin t‖ ≤ (1:ℝ) :=
  λ t, by {rw [real.deriv_sin,real.norm_eq_abs],exact real.abs_cos_le_one t},
 have h := (convex_univ : convex ℝ (set.univ : set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (λ t ht, real.differentiable_sin t) (λ t ht, d t)
    (set.mem_univ y) (set.mem_univ x),
 simpa only [one_mul, real.norm_eq_abs] using h
end

theorem reflected_pair (u v : ℝ) (j : ℤ) :
 |real.sin u+real.sin v| ≤ |u+v-(j:ℝ)*(2*real.pi)| :=
begin
 have h := sine_distance v ((j:ℝ)*(2*real.pi)-u),
 rw [real.sin_int_mul_two_pi_sub] at h,
 rw [show real.sin u+real.sin v=real.sin v-(-real.sin u), by ring,
     show u+v-(j:ℝ)*(2*real.pi)=v-((j:ℝ)*(2*real.pi)-u), by ring], exact h
end

theorem support_reflection {A : Type*} [add_comm_group A] (s t : A) :
 s+t+(-s-t)=0 ∧ -s-(-s-t)=t ∧ -s-t = -t-s :=
by { split, abel,split;abel }

theorem triple_positive (a b c : ℝ) (ha : 2/3≤a) (hb : 2/3≤b) (hc : 2/3≤c) :
 0≤a+b+c-2 := by linarith

-- Haar probability on the circle is invariant under t ↦ -s-t.
-- This lemma integrates a row of the proposed three-particle joint density.
theorem triple_marginal {A : Type*} [measurable_space A] {μ : measure A}
 [is_probability_measure μ] (p : A → ℝ) (hp : integrable p μ)
 (hn : ∫ t, p t ∂μ = 1) (s : A) (e : A ≃ᵐ A) (he : measure_preserving e μ μ) :
 (∫ t, (p s+p t+p (e t)-2) ∂μ)=p s :=
begin
 have hpe : integrable (λ t, p (e t)) μ := (integrable_map_equiv e p).mp (by rwa [he.map_eq]),
 have ha : integrable (λ t : A, p s+p t) μ := (integrable_const _).add hp,
 have hb : integrable (λ t : A, p s+p t+p (e t)) μ := ha.add hpe,
 rw [integral_sub hb (integrable_const _), integral_add ha hpe,
     integral_add (integrable_const _) hp, he.integral_comp e.measurable_embedding p, hn],
 simp;ring
end

-- Instantiate the reflection for any normalized, translation- and inversion-
-- invariant measure on the additive circle (in particular its Haar probability).
theorem circle_triple_row (μ : measure (add_circle (1:ℝ))) [is_probability_measure μ]
 [is_add_left_invariant μ] [is_neg_invariant μ] (p : add_circle (1:ℝ) → ℝ)
 (hp : integrable p μ) (hn : ∫ t, p t ∂μ = 1) (s : add_circle (1:ℝ)) :
 (∫ t, (p s+p t+p (-s-t)-2) ∂μ)=p s :=
triple_marginal p hp hn s (measurable_equiv.sub_left (-s)) (measure_preserving_sub_left μ (-s))

-- At fixed first residue, exchange the other two. Testing against an arbitrary
-- function g establishes the equality of the second and third marginals.
theorem third_residue_test (μ : measure (add_circle (1:ℝ)))
 [is_add_left_invariant μ] [is_neg_invariant μ] (p g : add_circle (1:ℝ) → ℝ)
 (s : add_circle (1:ℝ)) :
 (∫ t, (p s+p t+p (-s-t)-2)*g (-s-t) ∂μ)=
 (∫ t, (p s+p t+p (-s-t)-2)*g t ∂μ) :=
begin
 let e := measurable_equiv.sub_left (-s),
 have h : measure_preserving e μ μ := measure_preserving_sub_left μ (-s),
 have hchange := h.integral_comp e.measurable_embedding (λ t, (p s+p t+p (-s-t)-2)*g t),
 calc
 (∫ t, (p s+p t+p (-s-t)-2)*g (-s-t) ∂μ)
     = ∫ t, (p s+p (e t)+p (-s-e t)-2)*g (e t) ∂μ :
   begin
     apply integral_congr_ae, filter_upwards with t,
     change (p s+p t+p (-s-t)-2)*g (-s-t)=(p s+p (-s-t)+p (-s-(-s-t))-2)*g (-s-t),
     rw [(support_reflection s t).2.1], ring
   end
 ... = _ : hchange
end

theorem symmetric_rows {A : Type*} [add_comm_group A] (p : A → ℝ) (s t : A) :
 p s+p t+p (-s-t)-2=p t+p s+p (-t-s)-2 :=
by {rw [(support_reflection s t).2.2];ring}

theorem lift_bin (g f p δ : ℝ) (h : p≠0) (hδ : δ≠0) (eq : g=δ*f/p) :
 p*g/δ=f := by {rw [eq],field_simp [h,hδ];ring}

theorem modular_weight (u T : ℝ) (hT : 0<T) : u*(T-u)/T ≤ T/4 :=
begin
 apply (div_le_iff hT).2,
 have h : T/4*T-u*(T-u)=(u-T/2)^2 := by ring,
 linarith [sq_nonneg (u-T/2)]
end

theorem binary_readout_cost (a b : ℝ) (ha : 0<a) (hA : a<1)
 (hb : 0<b) (hB : b<1) :
 (1-a)*(-real.log b)+(a*real.log a+(1-a)*real.log (1-a)) ≤
 a*real.log (a/(1-b))+(1-a)*real.log ((1-a)/b) :=
begin
 rw [real.log_div (ne_of_gt ha) (ne_of_gt (sub_pos.mpr hB)),
     real.log_div (ne_of_gt (sub_pos.mpr hA)) (ne_of_gt hb)],
 have h := real.log_nonpos (sub_nonneg.mpr hB.le) (show 1-b≤1, by linarith),
 nlinarith [mul_nonpos_of_nonneg_of_nonpos ha.le h]
end

theorem positive_miss (a b K h : ℝ) (ha : a<1) (hb : 0<b)
 (cost : (1-a)*(-real.log b)-h≤K) : real.exp (-(K+h)/(1-a))≤b :=
begin
 rw [←real.exp_log hb], apply real.exp_le_exp.mpr,
 apply (div_le_iff (sub_pos.mpr ha)).2,nlinarith [cost]
end

theorem symmetric_binary_cost (a : ℝ) (hp : 0<a) (hq : a<1) :
 a*real.log (a/(1-a))+(1-a)*real.log ((1-a)/a)=(1-2*a)*real.log ((1-a)/a) :=
by {rw [real.log_div (ne_of_gt hp) (ne_of_gt (sub_pos.mpr hq)),
        real.log_div (ne_of_gt (sub_pos.mpr hq)) (ne_of_gt hp)],ring}

theorem finite_pulse_miss (x : ℝ) : (2*real.arctan x)/real.pi<1 :=
by {apply (div_lt_iff real.pi_pos).2, linarith [real.arctan_lt_pi_div_two x]}

theorem inverse_mixture (a b η : ℝ) (hη : η ≠ 0) :
 (1-η)*((a+b)/2)+η*((a+b)/2+(a-b)/(2*η))=a :=
by {field_simp [hη]; ring}

theorem sufficient_mixture_floor (even odd η : ℝ) (hη : 0<η)
 (bound : |odd| ≤ η*(even-2/3)) : 2/3 ≤ even+odd/η :=
begin
 have h := (abs_le.mp bound).1,
 have key : 2/3-even ≤ odd/η := (le_div_iff hη).2 (by nlinarith),
 linarith
end

theorem asymmetric_residual (p q a b η : ℝ) (hp : 0≤a) (hq : 0≤b)
 (frac : 0≤η) (cancel : p-q=η*(a-b)) : |p-q|≤η*(a+b) :=
begin
 rw [cancel,abs_mul,abs_of_nonneg frac],
 apply mul_le_mul_of_nonneg_left _ frac,
 exact abs_le.mpr ⟨by linarith,by linarith⟩
end

theorem cluster_mass_shell (M E S a : ℝ) (h : 2*M*E*(a-1)=a^2*S) :
 M^2-2*M*a*E+a^2*S=M^2-2*M*E := by nlinarith

theorem cluster_rescaling (M E b : ℝ) (hb : 1+b ≠ 0) :
  let a := 2/(1+b), S := M*E*(1-b^2)/2 in
  2*M*E*(a-1)=a^2*S := by {dsimp,field_simp [hb];ring}

theorem orthogonal_helicities (a b : ℂ) :
 (a+b)/2+(a-b)/2=a ∧ (a+b)/2-(a-b)/2=b := by {split;ring}

theorem terminal_recoil (m : ℝ) :
 m/2+m/2=m ∧ m/2-m/2=0 := by {split;ring}

end fusion_surface_memory
