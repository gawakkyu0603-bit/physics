import analysis.special_functions.trigonometric.euler_sine_prod
import analysis.special_functions.gaussian
import analysis.special_functions.integrals
import analysis.analytic.isolated_zeros
import analysis.analytic.linear
import analysis.analytic.composition
import analysis.normed_space.exponential
import analysis.complex.basic
import analysis.special_functions.trigonometric.arctan_deriv
import analysis.special_functions.log.deriv
import analysis.inner_product_space.basic
import tactic

noncomputable theory
open set filter
open_locale topology big_operators
namespace autonomous_gravity_cascade

-- X is minus multiplication by relative time on a finite observation window.
section window
variables {A F : Type*} [normed_ring A] [normed_algebra ℂ A] [complete_space A]
variables [normed_add_comm_group F] [normed_space ℂ F]
def response (X : A) (L : A →L[ℂ] F) (z : ℂ) := L (exp ℂ (z • X))

theorem response_entire (X : A) (L : A →L[ℂ] F) :
 analytic_on ℂ (response X L) univ :=
begin
  intros z hz,
  let m := continuous_linear_map.to_span_singleton ℂ X,
  exact (L.analytic_at _).comp ((exp_analytic (m z)).comp (m.analytic_at z)),
end

theorem finite_window_no_exact_read (X : A) (L : A →L[ℂ] F) (C : set ℂ) (edge target : ℂ)
 (hEdge : edge ∈ closure (C \ {edge})) (hMiss : ∀ z ∈ C, response X L z = 0) :
 response X L target = 0 :=
begin
  have hz : edge ∈ closure ({z | response X L z = 0} \ {edge}),
  { apply closure_mono _ hEdge, exact λ z h, ⟨hMiss z h.1, h.2⟩ },
  exact (response_entire X L).eq_on_zero_of_preconnected_of_mem_closure
    is_preconnected_univ (mem_univ edge) hz (mem_univ target),
end
end window

-- A geometric derivation of the largest success probability for ONE target.
section target
variables {H : Type*} [normed_add_comm_group H] [normed_space ℂ H]
theorem upper_on_residual (D : H →L[ℂ] H) (x y : H) (kill : D y=0)
 (hcontract : ∀ v, norm (D v) ≤ norm v) : norm (D x) ≤ norm (x-y) :=
by simpa [map_sub,kill] using hcontract (x-y)
end target

theorem schur_one_pole (z w p q : ℂ) (a : z+w≠0) (b : z+q≠0) (c : p+w≠0) :
 1/(z+w) - (p+q)/((z+q)*(p+w)) =
 ((z-p)/(z+q))*((w-q)/(p+w))/(z+w) :=
by field_simp; ring

theorem schur_weighted (u v up vp z w p q : ℂ) (a : z+w≠0) (b : z+q≠0)
 (c : p+w≠0) (hp : p+q≠0) (hu : up≠0) (hv : vp≠0) :
 u*v/(z+w)-(u*vp/(z+q))*(up*v/(p+w))/(up*vp/(p+q)) =
 (u*((z-p)/(z+q)))*(v*((w-q)/(p+w)))/(z+w) :=
by field_simp; ring

theorem two_pole_loss (d a b : ℝ) (pos : 0 < d^2+(a+b)^2/4) :
 (d^2+(a-b)^2/4)/(d^2+(a+b)^2/4)=1-a*b/(d^2+(a+b)^2/4) :=
begin
 rw [div_eq_iff pos.ne'], rw [sub_mul,one_mul,div_mul_cancel _ pos.ne'], ring,
end

theorem rydberg_ratio (A B n m : ℝ) (hA : A≠0) (hn : n≠0)
 (hm : m≠0) (h1 : n-m≠0) (h2 : n+m≠0) :
 (B/n^3)*(B/m^3)/(A*(1/m^2-1/n^2))^2 =
 (B/A)^2*(n*m)/((n+m)^2*(n-m)^2) :=
begin
 have hd : 1/m^2-1/n^2=(n-m)*(n+m)/(m^2*n^2) := by field_simp; ring,
 have hdelta : A*(1/m^2-1/n^2)=A*(n-m)*(n+m)/(m^2*n^2) := by rw [hd]; ring,
 rw [hdelta, div_pow (A*(n-m)*(n+m)) (m^2*n^2), div_div_eq_mul_div],
 field_simp, ring,
end

theorem neighbour_bound (n m : ℝ) : 4*n*m ≤ (n+m)^2 := by nlinarith [sq_nonneg (n-m)]

theorem factor_lower (d u v r : ℝ) (D : 0<d) (R : 0≤r) (V : 0≤v)
 (UV : 0≤u) (AM : u≤v) (small : u≤r*d) :
 1/(1+r) ≤ 1-u/(d+v) :=
begin
 have h1 : 0<1+r := by linarith,
 have h2 : 0<d+v := by linarith,
 have H : u/(d+v) ≤ r/(1+r) := (div_le_div_iff h2 h1).2
   (by nlinarith [mul_nonneg R (sub_nonneg.mpr AM)]),
 have hsum : 1/(1+r)+r/(1+r)=1 := by rw [←add_div,div_self h1.ne'],
 linarith,
end

-- Atomic inputs are the Laguerre and regular Coulomb radial integrals.
theorem quadrupole_3d : 4096*(3:ℚ)^9*(3^2-4)/(3^2-1)^7*
 (((3:ℚ)-1)/(3+1))^(2*3) = 98415/32768 := by norm_num

theorem gravity_line_3d : (4:ℚ)/75*((1-1/3^2)/2)^5*(98415/32768)=1/360 :=
by norm_num

theorem threshold_coefficient (e : ℝ) : (4/75:ℝ)*(1/2)^5*4096*e=(512/75)*e :=
by ring

theorem radial_log_derivative (n : ℝ) (hn : 1<n) :
 (n+3)/(1+1/n)-(n-3)/(1-1/n)=4*n^2/(n^2-1) :=
begin
 have h1 : n ≠ 0 := by linarith,
 have h2 : n+1 ≠ 0 := by linarith,
 have h3 : n-1 ≠ 0 := by linarith,
 have h4 : n^2-1 ≠ 0 := by nlinarith [mul_pos (sub_pos.mpr hn) (show 0<n+1, by linarith)],
 field_simp, ring,
end

theorem continuum_derivative (k i : ℂ) (hi : i^2=-1) (hk : k≠0)
 (h : 1+k^2≠0) (hp : 1+i*k≠0) (hm : 1-i*k≠0) :
 (3-i/k)/(1+i*k)+(3+i/k)/(1-i*k)=4/(1+k^2) :=
begin
 field_simp, ring_nf, simp only [hi], ring,
end

theorem equal_edge_log_cancels (lower upper logterm rlow rhigh : ℝ) (same : lower=upper) :
 (lower/2*logterm+rlow)+(-upper/2*logterm+rhigh)=rlow+rhigh :=
by rw [same]; ring

theorem adjacent_bins (v w : ℝ) (hv : v ≠ 0) (hw : w ≠ 0) :
 (v-w)^2/(v*w)=v/w+w/v-2 := by field_simp; ring

theorem rank_one_feedback (bare loop input output : ℂ) (hnz : 1+loop≠0)
 (equation : output=bare*input-loop*output) : output=bare*input/(1+loop) :=
by apply (eq_div_iff hnz).2; linear_combination equation

theorem optical_test (b : ℝ) (h : 0 ≤ b-b^2) : b ≤ 1 :=
begin by_contra h', push_neg at h', nlinarith [mul_pos (show 0<b, by linarith) (sub_pos.mpr h')] end

-- The same static force fixes a noise/work budget for a specified class of mediators.
theorem displaced_overlap_work (g j omega x : ℝ) (ho : omega≠0) :
 4*(g*j/omega)^2*x=2/omega*(2*omega*(g*j/omega)^2*x) := by field_simp; ring

theorem stopped_mediator_work (g j omega k : ℝ) (ho : omega≠0) (hd : k^2+omega^2≠0) :
 2*omega*(g*j/omega)^2*(1-k^2/(k^2+omega^2))=
 j^2*(2*g^2/omega)*(omega^2/(k^2+omega^2)) := by field_simp; ring

theorem gap_spectral_bound (k x low : ℝ) (hk : 0<k) (hl : 0≤low) (h : low≤x) :
 low^2/(k^2+low^2) ≤ x^2/(k^2+x^2) :=
begin
 apply (div_le_div_iff _ _).2,
 { nlinarith [mul_nonneg (sq_nonneg k) (show 0 ≤ x^2-low^2,
      by nlinarith [mul_nonneg (sub_nonneg.mpr h) (show 0≤x+low,by linarith)])] },
 all_goals {nlinarith [sq_pos_of_pos hk,sq_nonneg low,sq_nonneg x]},
end

theorem discrete_mediator_bound {ι : Type*} (indices : finset ι) (w f : ι → ℝ)
 (lower : ℝ) (h : ∀ i ∈ indices, 0≤w i ∧ lower≤f i) :
 (∑ i in indices,w i)*lower ≤ ∑ i in indices,w i*f i :=
begin
 rw [finset.sum_mul], apply finset.sum_le_sum, intros i hi,
 exact mul_le_mul_of_nonneg_left (h i hi).2 (h i hi).1,
end

theorem parity_direct (j : ℝ) : (-j)^2=j^2 := by ring

-- Dimension-independent inverse bound. m1^2 <= m0*m2 is positivity
-- of the reweighted measure, obtained by integrating a square.
theorem spectral_variance (m0 m1 m2 : ℝ) (positive : 0<m0)
 (sq_integral : ∀ z : ℝ, 0≤m2-2*z*m1+z^2*m0) : m1^2 ≤ m0*m2 :=
begin
 have h := mul_nonneg positive.le (sq_integral (m1/m0)),
 have hred : m0*(m2-2*(m1/m0)*m1+(m1/m0)^2*m0)=m0*m2-m1^2 :=
   by field_simp [positive.ne']; ring,
 linarith [hred],
end

theorem moment_gap (x y m0 m1 m2 : ℝ) :
 (m2+(x+y)*m1+x*y*m0)*(y*(m2+x*m1)-x*(m2+y*m1))-
 (y-x)*(m2+y*m1)*(m2+x*m1)=(y-x)*x*y*(m0*m2-m1^2) := by ring

theorem two_width_bound (x y rx ry total m0 m1 m2 : ℝ) (hx : 0<x) (hy : x<y)
 (hden : 0<y*ry-x*rx) (ht : total=m2+(x+y)*m1+x*y*m0)
 (hrx : rx=m2+y*m1) (hry : ry=m2+x*m1) (hvar : m1^2≤m0*m2) :
 (y-x)*rx*ry/(y*ry-x*rx) ≤ total :=
begin
 apply (div_le_iff hden).2,
 rw [ht,hrx,hry],
 have hpos : 0 ≤ (y-x)*x*y*(m0*m2-m1^2) := by
   exact mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr hy.le) hx.le)
         (le_trans hx.le hy.le)) (sub_nonneg.mpr hvar),
 linarith [moment_gap x y m0 m1 m2],
end

theorem single_mode_recovery (x y t L : ℝ) (h1 : x+t≠0) (h2 : y+t≠0)
 (hd : 0<y-x) (hp : 0<t) (hL : 0<L) :
 (y*(L*t/(y+t))-x*(L*t/(x+t)))=
 t*(L*t/(x+t)-L*t/(y+t)) := by field_simp; ring

theorem positive_reweighted_square {ι : Type*} (S : finset ι) (w t : ι → ℝ)
 (h : ∀ i∈S, 0 ≤ w i) (z : ℝ) : 0 ≤ ∑ i in S,w i*(t i-z)^2 :=
finset.sum_nonneg (λ i hi, mul_nonneg (h i hi) (sq_nonneg _))

theorem variance_zero_support {ι : Type*} (S : finset ι) (w t : ι → ℝ)
 (h : ∀ i∈S, 0 < w i) (z : ℝ) (zero : (∑ i in S,w i*(t i-z)^2)=0) :
 ∀ i∈S, t i=z :=
begin
 intros i hi,
 have hsingle := (finset.sum_eq_zero_iff_of_nonneg
    (λ j hj, mul_nonneg (h j hj).le (sq_nonneg (t j-z)))).1 zero i hi,
 have hsq := (mul_eq_zero.mp hsingle).resolve_left (h i hi).ne',
 nlinarith,
end

-- Passive write amplitudes are allowed by the inclusive optical loss exactly
-- when the whitened row is a contraction, including complex amplitudes.
theorem optical_row_iff {H : Type*} [normed_add_comm_group H] [inner_product_space ℂ H]
 (u : H) : (∀ v : H, ‖(inner u v : ℂ)‖ ≤ ‖v‖) ↔ ‖u‖≤1 :=
begin
 split,
 { intro h, have hs := h u,
   rw [inner_self_eq_norm_sq_to_K, norm_pow] at hs,
   simp only [is_R_or_C.norm_coe_norm] at hs,
   by_contra hn, push_neg at hn, nlinarith [mul_pos (sub_pos.mpr hn) (lt_trans zero_lt_one hn)] },
 { intros hu v, exact le_trans (norm_inner_le_norm u v)
     (by simpa using mul_le_mul_of_nonneg_right hu (norm_nonneg v)) },
end

-- With finitely many competitors, every normalized Gram elimination
-- contributes the corresponding diagonal factor, in any order.
theorem iterated_residual (weights : list ℝ) (initial : ℝ) :
 weights.foldl (λ a f, a*f) initial=initial*weights.prod :=
begin
 induction weights with a tail ih generalizing initial,
 { simp },
 { simp only [list.foldl_cons,list.prod_cons], rw [ih,mul_assoc] },
end

theorem finite_offset_squeeze {ι : Type*} (I : finset ι) (g f : ι → ℝ)
 (cmp : ∀ i∈I, g i≤f i) (hg : ∀ i∈I, 0≤g i) :
 (∏ i in I,g i) ≤ ∏ i in I,f i := finset.prod_le_prod hg cmp

theorem squeeze_window_limit {s upper : ℕ → ℝ} {l : ℝ}
 (lower : ∀ n, l≤s n) (up : ∀ k, ∀ᶠ n in at_top, s n≤upper k)
 (hlim : tendsto upper at_top (𝓝 l)) : tendsto s at_top (𝓝 l) :=
begin
 apply tendsto_order.2, split,
 { intros a ha, exact filter.eventually_of_forall (λ n, lt_of_lt_of_le ha (lower n)) },
 { intros b hb, obtain ⟨k,hk⟩ := (hlim.eventually (gt_mem_nhds hb)).exists,
   exact (up k).mono (λ n hn, lt_of_le_of_lt hn hk) },
 all_goals { apply_instance },
end

theorem euler_at_imaginary (r : ℂ) :
 tendsto (λ n:ℕ, (real.pi:ℂ)*(r*complex.I)*
   (∏ j in finset.range n, (1-(r*complex.I)^2/((j:ℂ)+1)^2)))
 at_top (𝓝 (complex.sinh ((real.pi:ℂ)*r)*complex.I)) :=
begin
 have h := complex.tendsto_euler_sin_prod (r*complex.I),
 rw [←mul_assoc (real.pi:ℂ) r complex.I, complex.sin_mul_I] at h,
 simpa only [mul_assoc] using h,
end

theorem imaginary_euler_factor (r k : ℂ) :
 1-(r*complex.I)^2/k^2=1+r^2/k^2 :=
by rw [mul_pow,complex.I_sq]; ring

-- P A+ = A- P at the inverse-propagator level implies the same intertwining
-- for the propagator. The first/last material states supply a parity sign.
theorem parity_inverse {R : Type*} [ring R] (p ap am rp rm : R)
 (h : p*ap=am*p) (hr : ap*rp=1) (hl : rm*am=1) : p*rp=rm*p :=
calc p*rp=(rm*am)*(p*rp) : by rw [hl,one_mul]
 ... =rm*((am*p)*rp) : by simp only [mul_assoc]
 ... =rm*((p*ap)*rp) : by rw [h]
 ... =rm*p : by rw [mul_assoc,hr,mul_one]

theorem parity_amplitude {R : Type*} [ring R] (l r rp rm p sign : R)
 (h : p*rp=rm*p) (hleft : l*p=sign*l) (initial : p*r=r) :
 l*rm*r=sign*(l*rp*r) :=
calc l*rm*r=l*rm*(p*r) : by rw [initial]
 ... =l*(rm*p)*(r) : by simp only [mul_assoc]
 ... =l*(p*rp)*r : by rw [h]
 ... =sign*(l*rp*r) : by rw [←mul_assoc l p rp,hleft]; simp only [mul_assoc]

theorem signed_parity_coherence {ι : Type*} (S : finset ι) (p odd : ι → ℝ)
 (normed : (∑ i in S,p i)=1) :
 (∑ i in S,(1-2*odd i)*p i)=1-2*∑ i in S,odd i*p i :=
begin
 simp_rw [sub_mul,one_mul,mul_assoc], rw [finset.sum_sub_distrib,normed,finset.mul_sum],
end

theorem energy_limits_coherence {ι : Type*} (S : finset ι) (p n odd : ι → ℝ)
 (hp : ∀ i∈S,0≤p i) (ho : ∀ i∈S,odd i≤n i) (frequency : ℝ) (hf : 0<frequency) :
 2*(∑ i in S,odd i*p i) ≤ 2*(frequency*∑ i in S,n i*p i)/frequency :=
begin
 have h : (∑ i in S,odd i*p i) ≤ ∑ i in S,n i*p i := finset.sum_le_sum (λ i hi, mul_le_mul_of_nonneg_right (ho i hi) (hp i hi)),
 rw [le_div_iff hf], nlinarith [mul_nonneg hf.le (sub_nonneg.mpr h)],
end

theorem one_sideband_coherence (p0 p1 omega : ℝ) (complete : p0+p1=1) (hn : omega≠0) :
 p0-p1=1-2*(omega*p1)/omega := by rw [show 2*(omega*p1)/omega=2*p1, by field_simp; ring]; linarith

theorem log_bound_edge :
 tendsto (λ x : ℝ, (real.log (1-x)-real.log (1+x))/x) (𝓝[≠] (0:ℝ)) (𝓝 (-2)) :=
begin
 have hm : has_deriv_at (λ x : ℝ, 1-x) (-1) 0 := by
   simpa using (has_deriv_at_id (0:ℝ)).const_sub (1:ℝ),
 have hp : has_deriv_at (λ x : ℝ, 1+x) 1 0 := by
   simpa using (has_deriv_at_id (0:ℝ)).const_add (1:ℝ),
 have h := (hm.log (by norm_num)).sub (hp.log (by norm_num)),
 have eqn : slope (λ x : ℝ, real.log (1-x)-real.log (1+x)) 0 =
    (λ x : ℝ, (real.log (1-x)-real.log (1+x))/x) := by {funext z, simp [slope_def_field]},
 have t := has_deriv_at_iff_tendsto_slope.1 h,
 rw [← eqn], norm_num at t, exact t,
end

theorem arctan_continuum_edge :
 tendsto (λ x : ℝ, real.arctan x/x) (𝓝[≠] (0:ℝ)) (𝓝 1) :=
begin
 have eqn : slope real.arctan 0 = (λ x : ℝ, real.arctan x/x) := by {funext z, simp [slope_def_field]},
 rw [← eqn], simpa using (has_deriv_at_iff_tendsto_slope.1 (real.has_deriv_at_arctan 0)),
end

theorem bound_edge_exp :
 tendsto (λ x : ℝ,real.exp (2*((real.log (1-x)-real.log (1+x))/x)))
 (𝓝[≠] (0:ℝ)) (𝓝 (real.exp (-4))) :=
begin
 have h := (real.continuous_exp.tendsto _).comp (log_bound_edge.const_mul 2),
 norm_num [function.comp] at h ⊢, exact h,
end

theorem continuum_edge_exp :
 tendsto (λ x : ℝ,real.exp ((-4)*(real.arctan x/x)))
 (𝓝[≠] (0:ℝ)) (𝓝 (real.exp (-4))) :=
begin
 have h := (real.continuous_exp.tendsto _).comp (arctan_continuum_edge.const_mul (-4)),
 simpa [function.comp] using h,
end

theorem definite_phase_bin (e o : ℝ) (he : 0≤e) (ho : 0≤o) :
 (abs (e-o)=e+o) ↔ e=0 ∨ o=0 :=
begin
 split,
 { intro h, have hsq := congr_arg (λ t : ℝ,t^2) h,
   change (abs (e-o))^2=(e+o)^2 at hsq,
   rw [sq_abs] at hsq,
   have hz : e*o=0 := by nlinarith, exact mul_eq_zero.mp hz },
 { rintro (rfl|rfl); simp [abs_of_nonneg he,abs_of_nonneg ho] },
end

theorem minimum_parity_loss (e o : ℝ) : abs (e-o)=e+o-2*min e o :=
begin
 by_cases h : e≤o,
 { rw [min_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)], ring },
 { rw [min_eq_right (le_of_not_ge h),abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h))], ring },
end

theorem best_sign (p q : ℝ) (sign : ℝ) (h : sign=1 ∨ sign= -1) :
 sign*(p-q)≤abs (p-q) :=
begin
 rcases h with rfl|rfl,
 { simpa using le_abs_self (p-q) },
 { simpa using neg_le_abs_self (p-q) },
end

theorem recovery_loss {ι : Type*} (S : finset ι) (e o : ι → ℝ)
 (total : (∑ i in S,(e i+o i))=1) :
 (∑ i in S, abs (e i-o i))=1-2*∑ i in S,min (e i) (o i) :=
begin
 simp_rw [minimum_parity_loss], rw [finset.sum_sub_distrib,total,finset.mul_sum],
end

theorem one_received_bin {ι : Type*} (S : finset ι) (k c : ι → ℝ)
 (pos : ∀ i∈S,0≤k i) :
 abs (∑ i in S,k i*c i) ≤ ∑ i in S,k i*abs (c i) :=
begin
 apply le_trans (finset.abs_sum_le_sum_abs _ _),
 apply finset.sum_le_sum, intros i hi,
 rw [abs_mul,abs_of_nonneg (pos i hi)],
end

theorem stochastic_loss {ι ν : Type*} (S : finset ι) (U : finset ν)
 (k : ν → ι → ℝ) (c : ι → ℝ) (pos : ∀ j∈U, ∀ i∈S,0≤k j i)
 (normalized : ∀ i∈S, (∑ j in U,k j i)=1) :
 (∑ j in U,abs (∑ i in S,k j i*c i)) ≤ ∑ i in S,abs (c i) :=
calc (∑ j in U,abs (∑ i in S,k j i*c i)) ≤
       ∑ j in U, ∑ i in S,k j i*abs (c i) :
     finset.sum_le_sum (λ j hj, one_received_bin S (k j) c (pos j hj))
 ... = ∑ i in S,abs (c i) : begin
   rw [finset.sum_comm], apply finset.sum_congr rfl, intros i hi,
   rw [←finset.sum_mul,normalized i hi,one_mul],
 end

open measure_theory

theorem finite_delay_overlap (z : ℂ) (T : ℝ) (h : z≠0) :
 (∫ t in (0:ℝ)..T, complex.exp ((-z)*t))=(1-complex.exp ((-z)*T))/z :=
begin
 rw [integral_exp_mul_complex (neg_ne_zero.mpr h)],
 rw [complex.of_real_zero,mul_zero,complex.exp_zero,div_neg_eq_neg_div,←neg_div], congr' 1, ring,
end

theorem overlap_equal_diagonal (p u t : ℝ) (hu : 0≤u) (huv : u≤p) :
 (0≤t ∧ 0≤p-t ∧ u^2≤(p-t)^2) ↔ 0≤t ∧ t≤p-u :=
begin
 split,
 { rintro ⟨ht,ha,hb⟩, refine ⟨ht,_⟩,
   by_contra h, push_neg at h,
   nlinarith [mul_pos (show 0<u-(p-t),by linarith) (show 0<u+(p-t),by linarith)] },
 { rintro ⟨ht,hb⟩, refine ⟨ht,by linarith,_⟩,
   nlinarith [mul_nonneg (show 0≤p-t-u,by linarith) (show 0≤p-t+u,by linarith)] },
end

section positive_measure
variables {B : Type*} [measurable_space B] (ν : measure B)

theorem zero_variance_measure (v : B → ℝ) (z : ℝ)
 (hi : integrable (λ b, (v b-z)^2) ν) (hz : (∫ b,(v b-z)^2 ∂ν)=0) :
 ∀ᵐ b ∂ν,v b=z :=
begin
 have hn : (0:B→ℝ) ≤ᵐ[ν] (λ b,(v b-z)^2) := filter.eventually_of_forall (λ b,sq_nonneg _),
 have h := (integral_eq_zero_iff_of_nonneg_ae hn hi).1 hz,
 filter_upwards [h] with b hb, change (v b-z)^2=0 at hb, nlinarith,
end

theorem recovered_continuum (e o : B → ℝ)
 (hm : integrable (λ b,min (e b) (o b)) ν) (hs : integrable (λ b,e b+o b) ν)
 (ht : (∫ b,(e b+o b) ∂ν)=1) :
 (∫ b,abs (e b-o b) ∂ν)=1-2*∫ b,min (e b) (o b) ∂ν :=
begin
 simp_rw [minimum_parity_loss],
 rw [integral_sub hs (hm.const_mul 2),integral_mul_left,ht],
end

theorem integrated_square [is_finite_measure ν] (v : B → ℝ) (h1 : integrable v ν)
 (h2 : integrable (λ b,(v b)^2) ν) (z : ℝ) :
 0 ≤ (∫ b,(v b)^2 ∂ν)-2*z*(∫ b,v b ∂ν)+z^2*(∫ b,(1:ℝ) ∂ν) :=
begin
 have h := @integral_nonneg B _ ν (λ b,(v b-z)^2) (λ b,sq_nonneg _),
 have eqn : (λ b,(v b-z)^2)=(λ b,(v b)^2-(2*z)*(v b)+z^2*(1:ℝ)) := by {funext b,ring},
 have hs : integrable (λ b,(v b)^2-(2*z)*v b) ν := h2.sub (h1.const_mul (2*z)),
 have hc : integrable (λ b:B,z^2*(1:ℝ)) ν := (integrable_const 1).const_mul (z^2),
 rw [eqn,integral_add hs hc,integral_sub h2 (h1.const_mul (2*z)),integral_mul_left,integral_mul_left] at h,
 exact h,
end

theorem strict_positive_integral [filter.ne_bot ν.ae] (f : B → ℝ)
 (hf : integrable f ν) (hp : ∀ᵐ b ∂ν,0<f b) : 0 < ∫ b,f b ∂ν :=
begin
 have hn : 0 ≤ᵐ[ν] f := hp.mono (λ b hb,hb.le),
 have h0 := integral_nonneg_of_ae hn, apply lt_of_le_of_ne h0, intro heq,
 have hz := (integral_eq_zero_iff_of_nonneg_ae hn hf).1 heq.symm,
 obtain ⟨b,hb,hz⟩ := (hp.and hz).exists, exact (ne_of_gt hb) hz,
end

end positive_measure

-- Exact test for grouping populated compact-charge sectors in one phase bin.
theorem unit_phases_coincide {ι : Type*} (S : finset ι) (w c s : ι → ℝ) (C D : ℝ)
 (positive : ∀ i∈S,0<w i) (unit : ∀ i∈S,(c i)^2+(s i)^2=1)
 (ref_unit : C^2+D^2=1) (wn : (∑ i in S,w i)=1)
 (wc : (∑ i in S,w i*c i)=C) (ws : (∑ i in S,w i*s i)=D) :
 ∀ i∈S,c i=C ∧ s i=D :=
begin
 have he : ∀ i∈S,w i*((c i-C)^2+(s i-D)^2)=
       2*w i-(2*C)*(w i*c i)-(2*D)*(w i*s i),
 { intros i hi, linear_combination w i*(unit i hi)+w i*ref_unit },
 have hsum : (∑ i in S,w i*((c i-C)^2+(s i-D)^2))=0,
 { rw [finset.sum_congr rfl he], simp_rw [finset.sum_sub_distrib,←finset.mul_sum],
   rw [wc,ws,wn], nlinarith },
 intros i hi,
 have hnon : ∀ i∈S,0≤w i*((c i-C)^2+(s i-D)^2) :=
    λ i hi,mul_nonneg (positive i hi).le (add_nonneg (sq_nonneg _) (sq_nonneg _)),
 have hsq := (mul_eq_zero.mp ((finset.sum_eq_zero_iff_of_nonneg hnon).1 hsum i hi)).resolve_left
       (positive i hi).ne',
 split; nlinarith [sq_nonneg (c i-C), sq_nonneg (s i-D)],
end

theorem character_partition (q r delta : ℂ) :
 complex.exp (q*delta)=complex.exp (r*delta) ↔
 ∃ n:ℤ, (q-r)*delta=(n:ℂ)*((2*(real.pi:ℂ))*complex.I) :=
by rw [complex.exp_eq_exp_iff_exp_sub_eq_one, ←sub_mul, complex.exp_eq_one_iff]

theorem transfer_conserves_rank (n m k : ℤ) : (n+k)+(m-k)=n+m := by ring

theorem global_charge_no_relative_phase (k n : ℤ) (h : k+n=n) : k=0 := by linarith

def schwinger_kernel (w s : ℝ) := s*real.exp (-s-w^2/(4*s))

theorem schwinger_monotone (x y s : ℝ) (hs : 0<s) (hx : 0≤x) (hy : x<y) :
 schwinger_kernel y s < schwinger_kernel x s :=
begin
 unfold schwinger_kernel, apply mul_lt_mul_of_pos_left _ hs, apply real.exp_lt_exp.mpr,
 have h : x^2<y^2 := by nlinarith [mul_pos (sub_pos.mpr hy) (show 0<y+x,by linarith)],
 linarith [div_lt_div_of_lt (show 0<4*s, by linarith) h],
end

theorem membrane_order {B : Type*} [measurable_space B] (ν : measure B)
 [filter.ne_bot ν.ae] (s : B → ℝ) (x y : ℝ) (hx : 0≤x) (hy : x<y)
 (hs : ∀ᵐ b ∂ν,0<s b) (h1 : integrable (λ b,schwinger_kernel x (s b)) ν)
 (h2 : integrable (λ b,schwinger_kernel y (s b)) ν) :
 (∫ b,schwinger_kernel y (s b) ∂ν) < ∫ b,schwinger_kernel x (s b) ∂ν :=
begin
 have hi : integrable (λ b,schwinger_kernel x (s b)-schwinger_kernel y (s b)) ν := h1.sub h2,
 have hp := strict_positive_integral ν _ hi (hs.mono
    (λ b hb,sub_pos.mpr (schwinger_monotone x y (s b) hb hx hy))),
 rw [integral_sub h1 h2] at hp, linarith,
end

theorem membrane_character (one two : ℝ) (h1 : 0<one) (h2 : 0<two) (h : two<one) :
 (two^2-one^2)/(two^2+one^2)<0 :=
div_neg_of_neg_of_pos (by nlinarith [mul_pos (sub_pos.mpr h) (add_pos h2 h1)])
 (by nlinarith [sq_pos_of_pos h1,sq_nonneg two])

theorem normalized_membrane_ratio (x a b : ℝ) (hx : x≠0) (ha : a≠0) :
 (((2*x)^2*b/2)/(x^2*a/2))^2=(4*b/a)^2 := by field_simp; ring

theorem compact_fourier_gaussian (u : ℝ) (hu : 0<u) (q : ℂ) :
 (∫ y : ℝ, complex.exp (complex.I*(-q)*y)*complex.exp (-(u:ℂ)*(y:ℂ)^2)) =
 complex.exp (-q^2/(4*(u:ℂ)))*((real.pi:ℂ)/u)^(1/2:ℂ) :=
begin
 have h := fourier_transform_gaussian (show 0<(u:ℂ).re,from hu) (-q),
 simpa only [neg_sq] using h,
end

theorem encounter_gaussian (u v : ℝ) :
 (∫ t:ℝ, real.exp (-(u*v^2)*t^2))=real.sqrt (real.pi/(u*v^2)) :=
integral_gaussian (u*v^2)

theorem schwinger_change_exponent (b u q : ℝ) (hb : b≠0) (hu : u≠0) :
 -(b^2*u)-(q*b)^2/(4*(b^2*u))= -b^2*u-q^2/(4*u) := by field_simp; ring

theorem integer_circle_partition (q r d : ℤ) (hd : d≠0) :
 complex.exp ((q:ℂ)*((2*(real.pi:ℂ))*complex.I/d)) =
 complex.exp ((r:ℂ)*((2*(real.pi:ℂ))*complex.I/d)) ↔ d ∣ q-r :=
begin
 rw [character_partition], have hd' : (d:ℂ)≠0 := by exact_mod_cast hd,
 set p : ℂ := (2*(real.pi:ℂ))*complex.I with hp,
 have hp' : p≠0 := complex.two_pi_I_ne_zero,
 split,
 { rintro ⟨k,hk⟩, use k,
   have eqn : ((q:ℂ)-r)*p=((k:ℂ)*d)*p,
   { rw [←mul_div_assoc] at hk, have h := (div_eq_iff hd').1 hk, linear_combination h },
   have heq := mul_right_cancel₀ hp' eqn,
   rw [mul_comm] at heq, exact_mod_cast heq },
 { rintro ⟨k,hk⟩, use k,
   have heq : (q:ℂ)-r=d*k := by exact_mod_cast hk,
   rw [heq], field_simp, ring },
end

theorem second_moment_gap (x y m1 m2 m3 : ℝ) :
 (m3+(x+y)*m2+x*y*m1)*((m2+y*m1)-(m2+x*m1))-
 (y-x)*(m2+y*m1)*(m2+x*m1)=(y-x)*(m1*m3-m2^2) := by ring

theorem microscopic_moment_bound (x y m1 m2 m3 rx ry M : ℝ) (xy : x<y)
 (h : ry<rx) (hx : rx=m2+y*m1) (hy : ry=m2+x*m1)
 (hM : M=m3+(x+y)*m2+x*y*m1) (var : m2^2≤m1*m3) :
 (y-x)*rx*ry/(rx-ry) ≤ M :=
begin
 apply (div_le_iff (sub_pos.mpr h)).2,
 rw [hM,hx,hy],
 linarith [second_moment_gap x y m1 m2 m3,
   mul_nonneg (sub_nonneg.mpr xy.le) (sub_nonneg.mpr var)],
end

theorem inverse_moment_remainder (w x : ℝ) (hw : 0<w) (hx : 0≤x) :
 1/w^3-1/(w*(w^2+x))=x/(w^3*(w^2+x)) :=
begin
 have hw' : w≠0 := hw.ne', have h2 : w^2+x≠0 := by nlinarith [sq_pos_of_pos hw],
 field_simp, ring,
end

def reduced_radial (r P dP ddP : ℝ) := -ddP/2+(1-1/r)*dP+3*P/r^2
def qfirst (r : ℝ) := r^2+2*r^3/3
def qsecond (r : ℝ) := 13*r^2/12+13*r^3/18+r^4/6

theorem first_radial_deriv (r : ℝ) : has_deriv_at qfirst (2*r+2*r^2) r :=
begin
 change has_deriv_at (λ t:ℝ,t^2+2*t^3/3) _ r,
 convert ((has_deriv_at_pow 2 r).add (((has_deriv_at_pow 3 r).const_mul 2).div_const 3)) using 1; norm_num; ring,
end

theorem second_radial_deriv (r : ℝ) :
 has_deriv_at qsecond (13*r/6+13*r^2/6+2*r^3/3) r :=
begin
 change has_deriv_at (λ t:ℝ,13*t^2/12+13*t^3/18+t^4/6) _ r,
 convert (((((has_deriv_at_pow 2 r).const_mul 13).div_const 12).add
   (((has_deriv_at_pow 3 r).const_mul 13).div_const 18)).add
    ((has_deriv_at_pow 4 r).div_const 6)) using 1; norm_num; ring,
end

theorem inverse_radial_equations (r : ℝ) (hr : r≠0) :
 reduced_radial r (qfirst r) (2*r+2*r^2) (2+4*r)=2*r^2 ∧
 reduced_radial r (qsecond r) (13*r/6+13*r^2/6+2*r^3/3)
 (13/6+13*r/3+2*r^2)=qfirst r :=
by split; unfold reduced_radial qfirst qsecond; field_simp; ring

def radial_moment (m : ℕ) : ℚ := (nat.factorial m:ℚ)/2^(m+1)

theorem hydrogen_moment_values :
 4*(radial_moment 6+2/3*radial_moment 7)=75 ∧
 2*(13/12*radial_moment 6+(13/18+2/3*(13/12))*radial_moment 7+
 (1/6+2/3*(13/18))*radial_moment 8+2/3*(1/6)*radial_moment 9)=11995/48 :=
by norm_num [radial_moment,nat.factorial]

theorem hydrogen_clock_ratio :
 (11995/48:ℚ)/75=2399/720 ∧
 (((196608/48828125:ℚ)/(4076863488/4747561509943))^2)=
 22539340290692258087863249/1025156250000000000000000 := by norm_num

theorem two_clock_ratio_limit {α : Type*} {F : filter α} (a b : α → ℝ) (A B : ℝ)
 (ha : tendsto a F (𝓝 A)) (hb : tendsto b F (𝓝 B)) (hp : B≠0) :
 tendsto (λ i,a i/b i) F (𝓝 (A/B)) := ha.div hb hp

theorem matrix_receiver_moments :
 let R := λ u:ℚ,(8/(1+u)+4/(4+u))/9 in
 R 1=8/15 ∧ R 4=7/30 ∧
 (4-1)*R 1*R 4/(4*R 4-R 1)=14/15 ∧
 ((4-1)*R 1*R 4/(R 1-R 4))/(4/3)=14/15 := by norm_num

end autonomous_gravity_cascade
