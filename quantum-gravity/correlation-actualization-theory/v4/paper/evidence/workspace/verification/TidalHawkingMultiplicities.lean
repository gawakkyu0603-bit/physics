import tactic
import analysis.special_functions.integrals
import analysis.special_functions.improper_integrals
import data.complex.basic
import analysis.special_functions.gamma.beta

noncomputable theory
open measure_theory set filter
open_locale big_operators real topology complex_conjugate
namespace tidal_hawking

theorem radial_radius_bound (s w : ℝ) (hs : 0<s) (hw : 0<w) :
    2/(9*s^2)*w^2 < 1 ↔ 2*w^2 < 9*s^2 :=
by {have h : 0<9*s^2 := by positivity, rw [div_mul_eq_mul_div,(div_lt_iff h)],simp}

theorem weak_mode_lower (k v : ℝ) (hk : k^2≤1) (hv : v<1) :
  0 < 1-(k^2+v)/2 := by linarith

theorem retarded_impulse_negative (f : ℝ → ℝ) (w μ : ℝ) (hw : 0<w) (hm : 0<μ)
    (hf : interval_integrable f volume 0 w) (hp : ∀ x∈Ioo 0 w, 0<f x) :
    -μ*(∫ t in (0:ℝ)..w, f t)<0 :=
mul_neg_of_neg_of_pos (neg_neg_of_pos hm)
  (interval_integral.interval_integral_pos_of_pos_on hf hp hw)

theorem phase_window (w v k δ : ℝ) (hw : 0<w) (hv : v*w^2<1)
    (hk : 1<k*w) (hl : 0<δ) (hu : δ≤v*w/k) : 0<δ ∧ δ<1 :=
begin
 have kp : 0<k := pos_of_mul_pos_left (lt_trans zero_lt_one hk) hw.le,
 have hh := (le_div_iff kp).mp hu,
 have hl' : v*w < k := (mul_lt_mul_right hw).mp (by nlinarith only [hv,hk]),
 exact ⟨hl,(lt_of_mul_lt_mul_right (show δ*k<1*k, by linarith) kp.le)⟩
end

theorem prufer_identity (k v s c : ℝ) (hk : k≠0) (h : s^2+c^2=1) :
  k*c^2+(k^2+v)*s^2/k=k+v*s^2/k :=
by {field_simp [hk], linear_combination k^2*h}

theorem free_recoil (y μ s : ℝ) (hy : 0<y) (hl : y<1) (hs : 0<s) (hm : 0<μ) :
  -μ*(2*(1-y)/(3*s*y^2))<0 := by
 {have h : 0<1-y := sub_pos.mpr hl, exact mul_neg_of_neg_of_pos (neg_neg_of_pos hm) (by positivity)}

theorem two_endpoints_cancel (p c : ℝ) : ((p+c)-p)+((-p-c)-(-p))=0 := by ring

theorem recoil_entropy (g m e : ℝ) :
  4*real.pi*g*m^2-4*real.pi*g*(m^2-2*m*e)=8*real.pi*g*m*e := by ring

/-- Diagonal of an output projection in an orthonormal basis is at most one.
Sum over the r remaining states and the selected angular output basis. -/
theorem angular_bound {α β : Type*} (a : finset α) (b : finset β)
  (entry : α → β → ℝ) (h : ∀ i∈a, ∀ j∈b, entry i j≤1) :
  (∑ i in a, ∑ j in b, entry i j) ≤ (a.card:ℝ)*b.card :=
begin
 calc (∑ i in a, ∑ j in b, entry i j) ≤ ∑ i in a, ∑ j in b, (1:ℝ) :
   finset.sum_le_sum (λ i hi,finset.sum_le_sum (h i hi))
 ... = _ : by simp
end

theorem no_fit (d r g w : ℝ) (hd : 0<d) (h : r*g<d*w) : ¬(w≤r*g/d) :=
by {intro hh, exact (not_le_of_gt h) (by simpa [mul_comm] using (le_div_iff hd).mp hh)}

theorem lambda_square (u v : ℝ) :
 (1-u*v-(1-u)*(1-v))^2-4*(u*v)*((1-u)*(1-v))=(u-v)^2 := by ring

theorem phase_jacobian (u v : ℝ) :
 v*(u-1)-u*(v-1)=u-v := by ring

theorem shape_moments (a b c : ℝ) (ha : a=1) (hb : b=3/7) (hc : c=4/21) :
   b-(3/7)*a=0 ∧ c-2*(3/7)*b+(3/7)^2*a=1/147 :=
by {rw [ha,hb,hc], norm_num}

theorem beta_difference (a b t : ℝ) (ha : 0<a) (hb : 0<b) :
 t^2*((a+1)*(a+2)/((a+b+2)*(a+b+3))-((a+1)/(a+b+2))^2)
 = t^2*((a+1)*(b+1)/((a+b+2)^2*(a+b+3))) :=
by {have h : a+b+2≠0 := by linarith,have j : a+b+3≠0 := by linarith,
 field_simp [h,j];ring}

theorem quadrupole (a b c s : ℝ) (h : c^2+s^2=1) :
  (a+b*c)^2+(b*s)^2=a^2+b^2+2*a*b*c :=
by linear_combination b^2*h

theorem shape_from_quadrupole (a b c D : ℝ) (ha : a≠0) (hb : b≠0)
    (hd : D=a^2+b^2+2*a*b*c) : (D-a^2-b^2)/(2*a*b)=c :=
by {rw [hd], field_simp [ha,hb];ring}

def wave (n : ℤ) (t : ℝ) := real.cos ((n:ℝ)*t)

theorem wave_integral (n : ℤ) (hn : n≠0) :
 (∫ t in (0:ℝ)..real.pi, wave n t)=0 :=
begin
 have h : (n:ℝ)≠0 := by exact_mod_cast hn,
 have hd : ∀ t : ℝ, has_deriv_at (λ x:ℝ, real.sin ((n:ℝ)*x)/(n:ℝ)) (wave n t) t,
 {intro t, convert (((has_deriv_at_id t).const_mul (n:ℝ)).sin.div_const (n:ℝ)) using 1,
  unfold wave, field_simp [h]},
 rw [interval_integral.integral_eq_sub_of_has_deriv_at (λ t ht, hd t)
    ((real.continuous_cos.comp (continuous_const.mul continuous_id)).interval_integrable _ _)],
 simp [real.sin_int_mul_pi]
end

theorem wave_gram (m n : ℤ) :
  (∫ t in (0:ℝ)..real.pi, wave m t*wave n t)=
  ((∫ t in (0:ℝ)..real.pi, wave (m-n) t)+(∫ t in (0:ℝ)..real.pi, wave (m+n) t))/2 :=
begin
 have hc : ∀ j:ℤ, continuous (wave j) :=
 λ j, real.continuous_cos.comp (continuous_const.mul continuous_id),
 have h : (λ t:ℝ,wave m t*wave n t)=(λ t:ℝ,(wave (m-n) t+wave (m+n) t)/2),
 {funext t, unfold wave, push_cast, rw [sub_mul,add_mul,real.cos_sub,real.cos_add],ring},
 rw [h, interval_integral.integral_div, interval_integral.integral_add
   ((hc _).interval_integrable _ _) ((hc _).interval_integrable _ _)]; apply_instance
end

theorem wave_orthogonal (m n : ℤ) (hd : m≠n) (hs : m+n≠0) :
 (∫ t in (0:ℝ)..real.pi, wave m t*wave n t)=0 :=
by rw [wave_gram,wave_integral _ (sub_ne_zero.mpr hd),wave_integral _ hs];norm_num

theorem wave_norm (n : ℤ) (hn : n≠0) :
 (∫ t in (0:ℝ)..real.pi, wave n t*wave n t)=real.pi/2 :=
by {have h : n+n≠0 := by omega, rw [wave_gram,sub_self,wave_integral _ h],
 simp [wave]}

theorem complex_conjugate_abs (z : ℂ) : complex.abs (conj z)=complex.abs z :=
complex.abs_conj _

/-- For any number of photons the modulus of the local chiral vertex is
identical on every polarization word, pointwise in its hard momenta. -/
theorem polarization_modulus {ι : Type*} (s : finset ι) (z : ι → ℂ) (h : ι → Prop)
 [decidable_pred h] :
 complex.abs (∏ i in s, if h i then z i else conj (z i))=∏ i in s,complex.abs (z i) :=
begin
 classical,
 induction s using finset.induction_on with a s ha ih,
 {simp},
 {rw [finset.prod_insert ha,finset.prod_insert ha,complex.abs.map_mul,ih],split_ifs;simp}
end

/-- After fixing all momenta, the squared normalized amplitude equals the
common scalar on every disjoint helicity class, including a partial mark. -/
theorem polarization_weight {ι : Type*} (fibre kept : finset ι) (w : ℝ) (h : fibre.card≠0) :
  (∑ i in kept, w/(fibre.card:ℝ))=w*(kept.card:ℝ)/(fibre.card:ℝ) :=
by {simp [div_eq_mul_inv];ring}

theorem all_hard_momenta {ι : Type*} (s : finset ι) (w : ℝ) (h : s.card≠0) :
 (∑ i in s, w/(s.card:ℝ))=w :=
by {rw [polarization_weight s s w h],exact mul_div_cancel _ (by exact_mod_cast h)}

theorem complement_mark (n k : ℝ) (hn : n≠0) (h : n=2*k) :
  k/n=1/2 := by {field_simp [hn];linarith}

theorem disjoint_helicity {ι : Type*} (s : finset ι) (f g : ι → ℂ)
  (h : ∀ i∈s, f i=0 ∨ g i=0) : (∑ i in s,conj (f i)*g i)=0 :=
finset.sum_eq_zero (λ i hi, by {rcases h i hi with ha|ha;simp [ha]})

theorem helicity_match (n j : ℝ) (hn : n≠0) (h1 : n-1≠0) :
 (j*(j-1)+(n-j)*(n-j-1))/(n*(n-1))=1-2*j*(n-j)/(n*(n-1)) :=
by {field_simp [hn,h1];ring}

theorem four_helicity_values :
 (1-2*(0:ℝ)*(4-0)/(4*3)=1) ∧ (1-2*(1:ℝ)*(4-1)/(4*3)=1/2) ∧
 (1-2*(2:ℝ)*(4-2)/(4*3)=1/3) := by norm_num

theorem scalar_chain {α : Type*} (s : finset α) (rate : α → ℝ)
 (survival logical : ℝ) :
 (∏ i in s,rate i)*(survival*logical)=((∏ i in s,rate i)*survival)*logical :=
by ring

theorem finite_hazard (rate time accumulated : ℝ) (h : rate*time≤accumulated) :
 real.exp (-accumulated)≤real.exp (-(rate*time)) :=
real.exp_le_exp.mpr (neg_le_neg h)

theorem no_finite_cutoff (w : ℝ) : 0<real.exp (-w) := real.exp_pos _

theorem markov_mean (rate : ℝ) (h : 0<rate) :
 (∫ t in Ioi (0:ℝ), real.exp ((-rate)*t))=1/rate :=
by {have h' := integral_comp_mul_left_Ioi (λ t:ℝ, real.exp (-t)) 0 h,
 simpa [abs_of_pos (inv_pos.mpr h),smul_eq_mul,integral_exp_neg_Ioi_zero,one_div] using h'}

theorem smooth_only_survival (x : ℝ) (hx : 0≤x) :
  1/(1+x)≥real.exp (-x) :=
begin
 rw [real.exp_neg,one_div], apply (inv_le_inv_of_le (by linarith : 0<1+x)),
 linarith [real.add_one_le_exp x]
end
theorem reduced_inertia (a b : ℝ) (ha : 0<a) (hb : 0<b) :
 (a*b/(a+b))*(1/a+1/b)=1 :=
by {field_simp [ha.ne',hb.ne',(add_pos ha hb).ne'];ring}

theorem volterra_gap (B L D : ℝ) (hb : 0≤B) (hc : B<1/2)
 (hL : L≤1+B*L) (hD : D+1≤B*L) : D<0 :=
begin
 have h : 0<1-B := by linarith,
 have h' : L≤1/(1-B) := (le_div_iff h).mpr (by nlinarith only [hL]),
 have bound := mul_le_mul_of_nonneg_left h' hb,
 have small : B/(1-B)<1 := (div_lt_iff h).mpr (by linarith),
 rw [mul_one_div] at bound,linarith
end

theorem actual_meter_current (P F : ℝ → ℝ) (w : ℝ) (hw : 0<w)
 (hd : ∀ t∈uIcc 0 w, has_deriv_at P (F t) t)
 (hi : interval_integrable F volume 0 w) (hs : ∀ t∈Ioo 0 w, F t<0) :
 P w-P 0<0 :=
begin
 have hh := interval_integral.interval_integral_pos_of_pos_on hi.neg
    (λ t ht,neg_pos.mpr (hs t ht)) hw,
 change 0 < ∫ t in (0:ℝ)..w,-F t at hh,
 rw [interval_integral.integral_neg,interval_integral.integral_eq_sub_of_has_deriv_at hd hi] at hh,
 linarith
end

theorem inactive_meter_current (P : ℝ → ℝ) (w : ℝ)
 (hd : ∀ t∈uIcc 0 w, has_deriv_at P 0 t) : P w=P 0 :=
begin
 have h := interval_integral.integral_eq_sub_of_has_deriv_at hd
  (show interval_integrable (λ t:ℝ, (0:ℝ)) volume 0 w,from continuous_const.interval_integrable _ _),
 simp at h,linarith
end

/-- Components of the three photons left after losing a known leg. The
four columns are (logical 0,+), (logical 1,+), (logical 0,-), (logical 1,-)
of the parity-even qubit. The common normalization squared is six. -/
theorem scaled_photon (s a e:ℂ) (hs : conj s*s=3) :
 conj (s*a)*(s*e)=3*(conj a*e) :=
calc conj (s*a)*(s*e) = (conj s*s)*(conj a*e) : by {rw [map_mul];ring}
 ... = _ : by rw [hs]

theorem erased_gram (s a b c d e f g h:ℂ) (hs : conj s*s=3) :
 conj (s*a)*(s*e)+conj d*h+conj d*h+conj b*f+conj d*h+conj b*f+conj b*f+conj (s*c)*(s*g)=
 3*(conj a*e+conj b*f+conj c*g+conj d*h) :=
by {rw [scaled_photon s a e hs,scaled_photon s c g hs];ring}

/-- The exact unnormalized cut moment is the product of two ordinary
beta integrals minus the square of one: expand the Jacobian (u-v)^2. -/
theorem product_beta_moments (a b c : ℝ) :
 ((c*a)-2*(b*b)+(a*c))/2=c*a-b^2 := by ring

theorem positive_laplace_divisor (w l p : ℝ) (hl : l≠0) :
   w*(p/l)*l=w*p := by {field_simp [hl]}

theorem diagonal_recovery_finite {ι : Type*} (s : finset ι) (weight : ι → ℝ)
 (g : ℝ) (h : ∀ i∈s, weight i = g) :
 (∑ i in s, weight i)=(s.card:ℝ)*g :=
by {rw [finset.sum_congr rfl h],simp}

theorem string_boundary_flux (m z ao ai vo vi F : ℝ)
 (h : m*(ao+ai)+z*(vo+vi)=F+2*z*vi) :
 (m*ao+z*vo)+(m*ai-z*vi)=F := by linarith

theorem damping_kernel (v : ℝ) : 1-real.exp (-v)≤v :=
by linarith [real.add_one_le_exp (-v)]

theorem causal_input_cut (t d c : ℝ) (hd : 0<d) (hc : 0<c) :
 t-d/c<t+d/c := by linarith [div_pos hd hc]

theorem integrating_factor (Y : ℝ → ℝ) (a F t : ℝ)
 (h : has_deriv_at Y (F-a*Y t) t) :
 has_deriv_at (λ u:ℝ,real.exp (a*u)*Y u) (real.exp (a*t)*F) t :=
by {convert (((has_deriv_at_id t).const_mul a).exp.mul h) using 1; simp only [id.def];ring}

theorem beta_factorials (a b : ℕ) :
 (nat.factorial (a+b+1):ℂ)*complex.beta_integral ((a:ℂ)+1) ((b:ℂ)+1)
 =(nat.factorial a:ℂ)*(nat.factorial b:ℂ) :=
begin
 have pa : 0<complex.re ((a:ℂ)+1) := by {simp;positivity},
 have pb : 0<complex.re ((b:ℂ)+1) := by {simp;positivity},
 have eqn := (complex.Gamma_mul_Gamma_eq_beta_integral pa pb).symm,
 rw [complex.Gamma_nat_eq_factorial,complex.Gamma_nat_eq_factorial] at eqn,
 convert eqn using 2,
 calc (nat.factorial (a+b+1):ℂ) = complex.Gamma (((a+b+1:ℕ):ℂ)+1) :
     (complex.Gamma_nat_eq_factorial _).symm
 ... = complex.Gamma (((a:ℂ)+1)+((b:ℂ)+1)) : by {congr' 1;push_cast;ring}
end

theorem finite_product_survival {ι : Type*} (s : finset ι) (x : ι → ℝ)
 (h : ∀ i, 0≤x i) :
 real.exp (-(∑ i in s,x i))≤∏ i in s, (1/(1+x i)) :=
begin
 classical, induction s using finset.induction_on with j s hj ih,
 {simp},
 {rw [finset.sum_insert hj,finset.prod_insert hj,neg_add,real.exp_add],
  exact mul_le_mul (smooth_only_survival _ (h j)) ih (real.exp_pos _).le
    (by {have hh := h j, positivity})}
end

/-- Dicke-state expectation of any two-leg operator, expressed in its
three symmetric diagonal entries. Weight separation kills inter-weight terms. -/
def two_spin (w A B C : ℝ) : ℝ :=
 ((12-w)*(11-w)*A+2*w*(12-w)*B+w*(w-1)*C)/132

theorem two_spin_even (A B C : ℝ) :
 (two_spin 0 A B C+6*two_spin 6 A B C+two_spin 12 A B C)/8=
 (13*A+18*B+13*C)/44 := by {unfold two_spin;ring}

theorem two_spin_odd (A B C : ℝ) :
 (two_spin 3 A B C+two_spin 9 A B C)/2=
 (13*A+18*B+13*C)/44 := by {unfold two_spin;ring}

theorem distinct_cross_weights (a b : ℤ) (ha : a=0 ∨ a=6 ∨ a=12) (hb : b=3 ∨ b=9) :
 2<abs (a-b) := by {rcases ha with h|h|h;rcases hb with hh|hh;rw [h,hh];norm_num;
 simp only [abs_of_pos (show (0:ℤ)<3,by norm_num),abs_of_pos (show (0:ℤ)<9,by norm_num)]; norm_num}

theorem hard_product_derivative {ι : Type*} (s : finset ι) (leg : ι → ℝ → ℂ)
 (slope : ι → ℂ) (t : ℝ)
 (hd : ∀ i, has_deriv_at (leg i) (slope i*leg i t) t) :
 has_deriv_at (λ u:ℝ,∏ i in s,leg i u)
   ((∑ i in s,slope i)*(∏ i in s,leg i t)) t :=
begin
 classical, induction s using finset.induction_on with j s hj ih,
 {simp, exact has_deriv_at_const _ _},
 {simp only [finset.sum_insert hj,finset.prod_insert hj],
  convert (hd j).mul ih using 1;ring}
end

/-- Equal error-product matrices remain equal for unresolved coherent sums
of soft radiation attached to different hard legs. -/
theorem coherent_error_compression {ι : Type*} (s : finset ι)
 (u v : ι → ℂ) (left right : ι → ι → ℂ) (h : ∀ i j, left i j=right i j) :
 (∑ i in s,∑ j in s,conj (u i)*v j*left i j)=
 ∑ i in s,∑ j in s,conj (u i)*v j*right i j :=
by simp only [h]

end tidal_hawking
