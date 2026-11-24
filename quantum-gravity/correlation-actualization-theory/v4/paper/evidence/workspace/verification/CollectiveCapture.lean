import analysis.special_functions.integrals
import algebra.geom_sum
import tactic

noncomputable theory
open_locale big_operators interval
open measure_theory

namespace collective_capture

-- A relative number constraint has an integer, positive-energy lowest state.
theorem imbalance_cost (p m : ℤ) (hp : 0 ≤ p) (hm : 0 ≤ m) :
 abs (p-m) ≤ p+m :=
begin rw [abs_le], split; linarith end

theorem attainable (d : ℤ) :
 0 ≤ max d 0 ∧ 0 ≤ max (-d) 0 ∧ max d 0 - max (-d) 0 = d ∧
 max d 0 + max (-d) 0 = abs d :=
begin by_cases hd : 0≤d,
 { simp [max_eq_left hd,max_eq_right (neg_nonpos.mpr hd),abs_of_nonneg hd,hd] },
 { have h := le_of_lt (lt_of_not_ge hd), have hn := neg_nonneg.mpr h,
   simp [max_eq_right h,max_eq_left hn,abs_of_nonpos h,hn] }
end

theorem refinement (a b c z z' : ℝ) :
 ((a+b)*c)*abs (z-z') = a*c*abs (z-z')+b*c*abs (z-z') := by ring

theorem unresolved_binary {α : Type*} [measurable_space α] (μ : measure α)
 [is_probability_measure μ] (f : α→ℝ) (hf : integrable f μ) :
 (∫ x,(∫ y,f x*(1-f y)+(1-f x)*f y ∂μ) ∂μ) =
 2*(∫x,f x ∂μ)*(1-(∫x,f x ∂μ)) :=
begin
 have hg : integrable (λ y,1-f y) μ := (integrable_const (1:ℝ)).sub hf,
 let a := ∫ x,f x ∂μ,
 have g : (∫y,1-f y ∂μ)=1-a := by rw [integral_sub (integrable_const (1:ℝ)) hf];simp [a],
 have inner : ∀x, (∫ y,f x*(1-f y)+(1-f x)*f y ∂μ)=f x*(1-a)+(1-f x)*a,
 { intro x, rw [integral_add (hg.const_mul _) (hf.const_mul _),integral_mul_left,integral_mul_left,g] },
 simp_rw [inner],
 rw [integral_add (hf.mul_const _) (hg.mul_const _),integral_mul_right,integral_mul_right,g],
 dsimp [a], ring
end

theorem merged_receipts {ι : Type*} (s : finset ι) (x y : ι→ℝ) :
 abs ((∑ i in s,x i)-(∑ i in s,y i))≤∑ i in s,abs (x i-y i) :=
begin rw [←finset.sum_sub_distrib], exact finset.abs_sum_le_sum_abs _ _ end

theorem common_shift (x y u : ℝ) : abs ((x+u)-(y+u))=abs (x-y) :=
by congr' 1; ring

theorem thermal_denominator (a θ : ℝ) (ha : 0≤a) : 0<1+2*a*(1-real.cos θ) :=
by nlinarith [mul_nonneg ha (sub_nonneg.mpr (real.cos_le_one θ))]

theorem thermal_width_from_integrals (a d : ℝ) (hd : 0<d) (h : d^2=1+4*a) :
 a*(1/d+(1+2*a)/d^3)=2*a*(1+3*a)/d^3 :=
begin
  calc a*(1/d+(1+2*a)/d^3)=a*(d^2+(1+2*a))/d^3 : by field_simp [ne_of_gt hd];ring
  ... = _ : by rw [h];ring
end

theorem thermal_zero (z : ℝ) : 1/(1+0*(1-real.cos z))=(1:ℝ) := by norm_num

theorem quadrupole_angular (v : ℝ) (h : v^2=4/45) : (3/2:ℝ)*v^2=2/15 :=
by rw [h];norm_num

theorem graviton_line (G hbar omega c I : ℝ) (hc : c≠0) (hh : hbar≠0)
 (h : I*omega=3*hbar) :
 2*G*omega^5/(5*hbar*c^5)*(2/15:ℝ)*I^2=(12/25:ℝ)*G*hbar*omega^3/c^5 :=
begin
 calc 2*G*omega^5/(5*hbar*c^5)*(2/15:ℝ)*I^2 = (4*G*omega^3)*(I*omega)^2/(75*hbar*c^5) :
   by field_simp [hh,hc];ring
 ... = _ : by rw [h];field_simp [hh,hc];ring
end

theorem rate_addition (n t g p : ℝ) : (n*p)*(g*t)=n*(p*g)*t := by ring

theorem stellar_mass_budget (n w u : ℝ) (hn : 0<n) : n*u < n*w ↔ u<w :=
mul_lt_mul_left hn

theorem dark_on_common (t : ℝ) : abs (t-t)=0 := by simp

-- Rationalized advanced-time integrand of the two ingoing rays.
theorem advanced_difference (f b2 h2 photon particle : ℝ)
 (hf : f≠0) (hp : 0<photon) (hm : 0<particle)
 (h1 : photon^2=1-f*b2) (h2' : particle^2=1-f*h2) :
 (1/particle-1/photon)/f=(h2-b2)/(particle*photon*(particle+photon)) :=
begin
 calc (1/particle-1/photon)/f =
   (photon^2-particle^2)/(f*(particle*photon*(particle+photon))) :
   by field_simp [hf,ne_of_gt hp,ne_of_gt hm,ne_of_gt (add_pos hm hp)];ring
 ... = _ : by rw [h1,h2'];field_simp [hf,ne_of_gt hp,ne_of_gt hm,ne_of_gt (add_pos hm hp)];ring
end

theorem early_cone (b2 h2 photon particle : ℝ) (hb : b2<h2)
 (hp : 0<photon) (hm : 0<particle) :
 0<(h2-b2)/(particle*photon*(particle+photon)) :=
div_pos (sub_pos.mpr hb) (mul_pos (mul_pos hm hp) (add_pos hm hp))

theorem aberration (u b : ℝ) (hb : 1-b*u≠0) :
 (1-(u-b)/(1-b*u))/2=(1-u)*(1+b)/(2*(1-b*u)) := by field_simp;ring

theorem kerr_off_axis_term (d a s : ℝ) (hd : 0<d) :
 0≤a^2*s^2/d := div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (le_of_lt hd)

theorem relay_before (ray lateral absorb deadline : ℝ)
 (h : lateral+absorb<deadline-ray) : ray+lateral+absorb<deadline := by linarith

theorem radial_flux (k s : ℝ) (h : 0<k+s) :
 ((k-s)/(k+s))^2+4*k*s/(k+s)^2=1 := by field_simp [ne_of_gt h];ring

theorem real_momentum_closed (E W m : ℝ) (h : E<W) (hm : 0<m) :
 ¬ ∃ k:ℝ,k^2=2*m*(E-W) :=
begin rintro ⟨k,hk⟩, have hneg := mul_neg_of_pos_of_neg (show (0:ℝ)<2*m, by linarith)
 (sub_neg.mpr h), linarith [sq_nonneg k] end

theorem strict_routes (a lo hi b e : ℝ) (ha : a<lo) (hb : hi<b)
 (hlo : lo≤e) (hhi : e≤hi) : a<e ∧ e<b :=
⟨lt_of_lt_of_le ha hlo, lt_of_le_of_lt hhi hb⟩

theorem marker_variance_bound (x ceiling : ℝ) (hx : 0≤x) (hc : x≤ceiling) :
 x^2≤ceiling*x := by nlinarith [mul_nonneg hx (sub_nonneg.mpr hc)]

theorem finite_time_tail (p T width delay : ℝ) (ht : 0<T)
 (h : p*T^2≤width^2+delay^2) : p≤(width^2+delay^2)/T^2 :=
(le_div_iff (sq_pos_of_pos ht)).mpr h

theorem phase_gradient (a b fp f : ℝ) (h : a^2+b^2=1) :
 (a*fp-b*f)^2+(b*fp+a*f)^2=fp^2+f^2 :=
begin calc (a*fp-b*f)^2+(b*fp+a*f)^2=(a^2+b^2)*(fp^2+f^2) : by ring
 ... = _ : by rw [h,one_mul] end

theorem leakage_margin (heat fraction W E : ℝ) (h : heat*fraction<W-E) :
 E+heat*fraction<W := by linarith

theorem source_only_bayes (mass grav photon : ℝ) (hm : mass≠0)
 (h : grav+photon≠0) : mass*grav/(mass*(grav+photon))=grav/(grav+photon) :=
by field_simp;ring

theorem finite_flux_off (q : ℕ) (z : ℂ) (hq : z^q=1) (hz : z≠1) :
 (∑ j in finset.range q,z^j)=0 :=
begin have h := geom_sum_mul z q, rw [hq,sub_self] at h,
 exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hz) end

theorem finite_flux_neutral (q : ℕ) (hq : 0<q) :
 (∑ j in finset.range q,(1:ℂ)^j)/(q:ℂ)=1 := by simp [ne_of_gt hq]

theorem two_population_return {α : Type*} [decidable_eq α] (s : finset α)
 (p q : α→ℝ) :
 (∑ x in s, ∑ y in s, if x=y then p x*q y else 0) = ∑ x in s,p x*q x :=
begin apply finset.sum_congr rfl, intros x hx, simp [hx] end

theorem direct_count_return (L : ℝ) :
 (∑' n:ℕ,(real.exp (-L)*(L^n/(n.factorial:ℝ)))^2) =
 real.exp (-(2*L))*(∑' n:ℕ,(L^n/(n.factorial:ℝ))^2) :=
begin
 have h : (real.exp (-L))^2 = real.exp (-(2*L)),
 { rw [pow_two,←real.exp_add],congr' 1,ring },
 simp_rw [mul_pow,h],rw [tsum_mul_left]
end

theorem neutral_cap (z1 z2 : ℤ) : z1-z2=0 ↔ z1=z2 := sub_eq_zero

theorem shared_vertex (common x y : ℤ) : (common+x)-(common+y)=x-y := by ring

theorem screenable (d : ℤ) (s : ℤ) : (∃ q:ℤ, abs q≤s ∧ d+q=0) ↔ abs d≤s :=
begin split,
 { rintro ⟨q,hq,he⟩,have h : q= -d := by linarith, simpa [h] using hq },
 { intro h,exact ⟨-d,by simpa using h,by ring⟩ } end

theorem uniform_exposure (delta e : ℝ) (he : e≠0) :
 (1/e)*(delta^2/e^2)*((2/5:ℝ)/(4*26))=delta^2/(260*e^3) :=
by field_simp [he];ring

theorem sparse_charge_lower (x : ℝ) (hx : 0≤x) (h : x≤1) (n : ℕ) :
 0≤x^n ∧ x^n≤1 := ⟨pow_nonneg hx _,pow_le_one _ hx h⟩

end collective_capture
