import analysis.special_functions.integrals
import analysis.special_functions.trigonometric.deriv
import tactic

noncomputable theory
open filter
namespace matrix_circle_layers

-- The straight-line integral after u = vt/sqrt(b^2+y^2+v^2*t^2).
def primitive (u : ℝ) := u-(2/3:ℝ)*u^3+u^5/5
theorem time_integrand (u : ℝ) :
 has_deriv_at primitive ((1-u^2)^2) u :=
begin
 have h := ((has_deriv_at_id u).sub (((has_deriv_at_id u).pow 3).const_mul (2/3:ℝ))).add
   (((has_deriv_at_id u).pow 5).div_const 5),
 convert h using 1; try {ext x}; simp [primitive]; ring
end

theorem time_prefactor : (15/16:ℝ)*(primitive 1-primitive (-1))=1 :=
by norm_num [primitive]

def membrane_density (t eta h : ℝ) := -t*h+eta*t*(h-1)
theorem membrane_difference (t eta h k : ℝ) :
 membrane_density t eta k-membrane_density t eta h=t*(eta-1)*(k-h) :=
by unfold membrane_density;ring
theorem charged_no_force (t eta h k : ℝ) (ht : 0<t) (hk : k≠h) :
 membrane_density t eta k=membrane_density t eta h ↔ eta=1 :=
begin
 rw [←sub_eq_zero,membrane_difference],
 have hn : k-h≠0 := sub_ne_zero.mpr hk,
 split,
 { intro a, have prod := (mul_eq_zero.mp a).resolve_right hn,
   exact sub_eq_zero.mp ((mul_eq_zero.mp prod).resolve_left (ne_of_gt ht)) },
 { intro a,rw [a],ring }
end

def harmonic (a : ℝ) := 1+a+a^2/3
theorem variance_polynomial (a : ℝ) :
 (harmonic a)^2=1+2*a+(5/3:ℝ)*a^2+(2/3:ℝ)*a^3+a^4/9 := by unfold harmonic;ring

-- Periodic phases at physically separated arms of a prepared material receiver.
def dark (u v : ℝ) := (real.sin ((u-v)/2))^2
theorem arm_probability (u v : ℝ) :
 dark u v+(real.cos ((u-v)/2))^2=1 := real.sin_sq_add_cos_sq _
theorem dark_exchange (u v : ℝ) : dark u v=dark v u :=
begin
 unfold dark, have h : (u-v)/2 = -((v-u)/2) := by ring,
 rw [h,real.sin_neg],ring
end
theorem no_gravity (u : ℝ) : dark u u=0 := by simp [dark]
theorem reference_gauge (ys yo path ls lo : ℝ) :
 (ys+ls)-(yo+lo)+(path-ls+lo)=ys-yo+path := by ring

-- A common graviton may see both occupied areas. Equal marginal stress does not fix this.
theorem occupation_example :
 ((1:ℝ)*1= (2+0)/2) ∧ ((1:ℝ)*1=(0+2)/2) ∧
 ((1:ℝ)*1 - (2*0+0*2)/2=1) := by norm_num

def loss (a b : ℝ) := 1-((1-a)^2+b^2)
theorem lost_forward_power (a b : ℝ) : loss a b=2*a-a^2-b^2 := by unfold loss;ring
theorem dilution_identity (t c j : ℝ) :
 loss (t*c) (t*j)=t*(2*c-t*(c^2+j^2)) := by unfold loss;ring

-- The estimate uses a probability-normalized angular measure in the physical application.
theorem cos_defect_bound (x : ℝ) (hx : 0≤x) : 1-real.cos x≤x :=
begin
 have hh : (∫ t in (0:ℝ)..x,real.sin t) ≤ ∫ t in (0:ℝ)..x,(1:ℝ) := interval_integral.integral_mono_on hx
   (real.continuous_sin.interval_integrable 0 x)
   ((continuous_const : continuous (λ t:ℝ,(1:ℝ))).interval_integrable 0 x)
   (λ t _,real.sin_le_one t),
 simpa using hh
end

open measure_theory
theorem uniform_transfer_bound {α : Type*} [measurable_space α] (μ : measure α)
 (d : α → ℝ) (j Q R b : ℝ) (hr : R≠0) (hb : b≠0) (positive : ∀ x,0≤d x)
 (hf : integrable (λ x,1-real.cos (d x)) μ) (hd : integrable d μ)
 (mean_phase : (∫ x,d x ∂μ) = 3*Q/(16*R*b^5)) :
 loss (∫ x,(1-real.cos (d x)) ∂μ) j ≤ 3*Q/(8*R*b^5) :=
begin
 have h := integral_mono hf hd (λ x, cos_defect_bound (d x) (positive x)),
 rw [mean_phase] at h,
 unfold loss, have hscale : 3*Q/(8*R*b^5)=2*(3*Q/(16*R*b^5)) :=
 by { field_simp [hr,hb]; ring },
 rw [hscale],nlinarith [sq_nonneg (∫ x,(1-real.cos (d x)) ∂μ),sq_nonneg j]
end

-- Complex forward overlap is 1 - t*c(t) + i*t*j(t), t = 1/radius.
-- The c,j limits come from the absolutely integrable continuum phase.
theorem uniform_coefficient {c j : ℝ → ℝ} {C J : ℝ}
 (hc : tendsto c (nhds 0) (nhds C)) (hj : tendsto j (nhds 0) (nhds J)) :
 tendsto (λ t,2*c t-t*((c t)^2+(j t)^2)) (nhds 0) (nhds (2*C)) :=
begin
 have ht : tendsto (λ t:ℝ,t) (nhds 0) (nhds 0) := tendsto_id,
 have hh := ((tendsto_const_nhds : tendsto (λ t:ℝ,(2:ℝ)) (nhds 0) (nhds 2)).mul hc).sub
   (ht.mul ((hc.pow 2).add (hj.pow 2))),
 simpa using hh
end

theorem localized_probability {f g : ℝ → ℝ} {F G : ℝ}
 (hf : tendsto f (nhds 0) (nhds F)) (hg : tendsto g (nhds 0) (nhds G)) :
 tendsto (λ t,dark (f t) (g t)) (nhds 0) (nhds (dark F G)) :=
begin
 have h := (hf.sub hg).div_const (2:ℝ),
 exact (real.continuous_sin.continuous_at.tendsto.comp h).pow 2
end

-- Formation/no formation are orthogonal outgoing spaces. z is residual real coherence.
def return_prob (p z : ℝ) := (1-p)^2+p^2+2*z*p*(1-p)
theorem return_loss (p z : ℝ) : 1-return_prob p z=2*(1-z)*p*(1-p) :=
by unfold return_prob;ring
theorem full_recovery_iff (p z : ℝ) (hp : 0<p) (hq : p<1) :
 return_prob p z=1 ↔ z=1 :=
begin
 split,
 { intro h, have eq := return_loss p z, rw [h,sub_self] at eq,
   have nz : 2*p*(1-p)≠0 := ne_of_gt (mul_pos (mul_pos (by norm_num) hp) (sub_pos.mpr hq)),
   have hh : (1-z)*(2*p*(1-p))=0 := by linarith only [eq],
   exact (sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right nz)).symm },
 { intro h,rw [h],unfold return_prob,ring }
end

-- Positional readout is a different question from transferring circle momentum.
theorem kick_at_fixed_transfer (p c s : ℝ) (h : c^2+s^2=1) :
 (p*c)^2+(p*s)^2=p^2 := by linear_combination p^2*h
theorem phase_visibility (u v : ℝ) :
 real.cos (u-v)=real.cos u*real.cos v+real.sin u*real.sin v := real.cos_sub u v

def impulse (p z g e : ℝ) := return_prob p z*g+(1-return_prob p z)*e
theorem later_force (p z g e : ℝ) :
 impulse p z g e-g=2*(1-z)*p*(1-p)*(e-g) := by unfold impulse return_prob;ring
theorem no_causal_difference (p z g : ℝ) : impulse p z g g=g :=
by unfold impulse;ring

-- beta is the noncompact outgoing speed; c is the base scattering cosine.
theorem hard_angle_denominator (beta c : ℝ) :
 ((1-beta*c)*(1+beta*c))^2=(1-beta^2*c^2)^2 := by ring
theorem coarse_sign_gap (p : ℝ) :
 (p^2+(1-p)^2)-(p^2+2*((1-p)/2)^2)=(1-p)^2/2 := by ring

open_locale big_operators
theorem detailed_return_bound {ι : Type*} [fintype ι] (w : ι → ℝ) (p : ℝ)
 (hn : ∀ i,0≤w i) (hm : ∀ i,w i≤p) (norm : ∑ i,w i=1) :
 ∑ i,(w i)^2≤p :=
calc ∑ i,(w i)^2 ≤ ∑ i,p*w i :
      finset.sum_le_sum (λ i _,by simpa [pow_two] using mul_le_mul_of_nonneg_right (hm i) (hn i))
 ... = p : by rw [←finset.mul_sum,norm,mul_one]

def hard_weight (A n : ℝ) := (real.sqrt (1-(n/A)^2))^7
theorem half_band_weight (A n : ℝ) (hA : 0<A) (hn : 0≤n) (hband : 2*n≤A) :
 (1/8:ℝ)≤hard_weight A n :=
begin
 have hlo : 0≤n/A := div_nonneg hn hA.le,
 have hhi : n/A≤1/2 := (div_le_iff hA).2 (by linarith),
 have hsq := mul_nonneg (sub_nonneg.mpr hhi) (show 0≤(1/2:ℝ)+n/A, by linarith),
 have habs : 0≤1-(n/A)^2 := by nlinarith,
 have hs := real.sq_sqrt habs, have hz := real.sqrt_nonneg (1-(n/A)^2),
 have hh : (3/4:ℝ)≤real.sqrt (1-(n/A)^2) :=
   by { by_contra h, push_neg at h,
        nlinarith [mul_pos (sub_pos.mpr h) (show 0<(3/4:ℝ)+real.sqrt (1-(n/A)^2),by linarith)] },
 unfold hard_weight, exact le_trans (by norm_num : (1/8:ℝ)≤(3/4:ℝ)^7)
   (pow_le_pow_of_le_left (by norm_num) hh 7)
end

theorem open_mode_floor (A : ℝ) (m : ℕ) (hA : 0<A) (hm : 2*(m:ℝ)≤A) :
 1+(m:ℝ)/4 ≤ 1+2*∑ i in finset.range m,hard_weight A ((i:ℝ)+1) :=
begin
 have h : ∀ i∈finset.range m,(1/8:ℝ)≤hard_weight A ((i:ℝ)+1) :=
 begin
   intros i hi,
   have hnat : i+1≤m := nat.succ_le_iff.mpr (finset.mem_range.mp hi),
   have hreal : (i:ℝ)+1≤(m:ℝ) := by exact_mod_cast hnat,
   exact half_band_weight A _ hA (by positivity) (by linarith)
 end,
 have hs := finset.sum_le_sum h, simp at hs,
 rw [show (8:ℝ)⁻¹=(1:ℝ)/8,by norm_num] at hs,linarith only [hs]
end

theorem counting_integral : (∫ x in (0:ℝ)..real.pi,(real.sin x)^8)=35*real.pi/128 :=
begin
 have h := integral_sin_pow_even 4,
 norm_num [finset.prod_range_succ] at h, linarith only [h]
end

theorem hard_coarse_limit {f : ℝ → ℝ} (h : tendsto f (nhds 0) (nhds 0)) :
 tendsto (λ t,(f t)^2+(1-f t)^2) (nhds 0) (nhds 1) :=
begin
 have hc : tendsto (λ t:ℝ,(1:ℝ)) (nhds 0) (nhds 1) := tendsto_const_nhds,
 simpa using (h.pow 2).add ((hc.sub h).pow 2)
end
theorem hard_signed_limit {f : ℝ → ℝ} (h : tendsto f (nhds 0) (nhds 0)) :
 tendsto (λ t,(f t)^2+(1-f t)^2/2) (nhds 0) (nhds (1/2)) :=
begin
 have hc : tendsto (λ t:ℝ,(1:ℝ)) (nhds 0) (nhds 1) := tendsto_const_nhds,
 simpa using (h.pow 2).add (((hc.sub h).pow 2).div_const (2:ℝ))
end

-- In the span of a pure rotor and its one-charge translate, these are entries of
-- (rho - W rho W*)^2. c is the absolute first circular moment.
theorem rotor_contrast_square (c s : ℝ) (unit : c^2+s^2=1) :
 (1-c^2)^2+(c*s)^2=1-c^2 ∧
 (c*s)^2+(-s^2)^2=1-c^2 ∧
 (1-c^2)*(-c*s)+(-c*s)*(-s^2)=0 :=
begin
 split, {linear_combination c^2*unit},
 split, {linear_combination (s^2+1)*unit}, {linear_combination (c*s)*unit}
end
theorem same_rotor_tradeoff (p u : ℝ) (hu : u≤1)
 (hp : p=(1+real.sqrt (1-u))/2) : (2*p-1)^2+u=1 :=
begin
 rw [hp,show 2*((1+real.sqrt (1-u))/2)-1=real.sqrt (1-u),by ring,
     real.sq_sqrt (sub_nonneg.mpr hu)],ring
end

-- Absorption at two sites. r = +/-1 are the two material excitations; the blank has
-- probability 1-eta. h is the signed contrast sin(n*d/R) at a quarter-phase reference.
def site (eta h r : ℝ) := eta*(1+r*h)/2
theorem site_with_blank (eta h : ℝ) : (1-eta)+site eta h 1+site eta h (-1)=1 :=
by unfold site;ring
theorem signed_receipt (eta h : ℝ) : site eta h 1-site eta (-h) 1=eta*h :=
by unfold site;ring
theorem blind_without_absorption (h r : ℝ) : site 0 h r=0 := by simp [site]
theorem site_correct (eta h : ℝ) :
 (1-eta)/2+(site eta h 1+site eta (-h) (-1))/2=(1+eta*h)/2 :=
by unfold site;ring
theorem absorption_slope : (1/9:ℝ)/(35*real.pi/256)=256/(315*real.pi) :=
by field_simp [real.pi_ne_zero];ring

theorem angular_uncertainty (v vc vs c s : ℝ)
 (rc : v*vc≥s^2/4) (rs : v*vs≥c^2/4) (circle : vc+vs=1-(c^2+s^2)) :
 c^2+s^2≤4*v*(1-(c^2+s^2)) :=
by rw [←circle];linarith only [rc,rs]

-- e denotes 2*mu*radius^2*available_energy.
theorem energetic_resolution (u v e : ℝ) (h : u≤4*v*(1-u)) (hv : v≤e)
 (hu : u≤1) (he : 0≤e) : u≤4*e/(1+4*e) :=
begin
 apply (le_div_iff (by linarith : 0<1+4*e)).2,
 have hmul := mul_le_mul_of_nonneg_right hv (sub_nonneg.mpr hu),
 linarith only [h,hmul]
end
theorem rare_sharp (p cost budget : ℝ) (positive : 0<cost)
 (funding : p*cost≤budget) : p≤budget/cost := (le_div_iff positive).2 funding

theorem opposite_ports (p : ℝ) : (p+(1-p))/2=(1/2:ℝ) := by ring
theorem symmetric_one_tag (n w : ℝ) (h : n*w=1) (hn : n≠0) : w=1/n :=
by apply (eq_div_iff hn).2;linarith only [h]
theorem retained_two : ((1/2:ℝ)*(3/4)^2)/((1/2:ℝ)*(3/4)^2+(1/2:ℝ)*(1/4)^2)=9/10 :=
by norm_num
end matrix_circle_layers
