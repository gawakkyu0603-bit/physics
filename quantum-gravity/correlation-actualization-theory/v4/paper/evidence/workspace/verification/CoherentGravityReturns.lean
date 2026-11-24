import analysis.special_functions.trigonometric.bounds
import analysis.special_functions.exp
import analysis.specific_limits.normed
import analysis.normed_space.exponential
import data.int.gcd
import data.complex.module
import analysis.fourier.add_circle
import algebra.geom_sum
import analysis.special_functions.integrals
import analysis.calculus.mean_value
import analysis.p_series
import analysis.inner_product_space.pi_L2
import linear_algebra.matrix.nonsingular_inverse
import tactic

noncomputable theory
open filter
open_locale big_operators topology complex_conjugate
namespace coherent_gravity_returns

-- Kernel of the Heisenberg pinching map, including countable charge labels.
variables {ι α : Type*} [decidable_eq α]
def pinch (r : ι → α) (F : ι → ι → ℂ) (i j : ι) : ℂ :=
if r i = r j then F i j else 0

theorem pinch_fixed (r : ι → α) (F : ι → ι → ℂ) :
 pinch r F = F ↔ ∀ i j, F i j ≠ 0 → r i = r j :=
begin
 split,
 { intros h i j hn, by_contra hh, apply hn,
   have he := congr_fun (congr_fun h i) j, simpa [pinch,hh] using he.symm },
 { intro h, funext i j, by_cases he : r i = r j,
   { simp [pinch,he] }, { have hz : F i j=0 := by_contra (λ hn,he (h i j hn)),
                            simp [pinch,he,hz] } },
end

theorem fixed_on_paths (R : ι → ι → Prop) (r : ι → α)
 (h : ∀ i j, R i j → r i = r j) {i j : ι} (p : relation.refl_trans_gen R i j) :
 r i = r j :=
begin induction p with j k p edge ih, { refl }, { exact ih.trans (h _ _ edge) } end

theorem quotient_lattice (d g k : ℤ) :
 (↑(int.gcd d g) : ℤ) ∣ k ↔ ∃ a b : ℤ, k = d*a+g*b :=
begin
 split,
 { rintro ⟨c,rfl⟩, refine ⟨int.gcd_a d g*c,int.gcd_b d g*c,_⟩,
   rw [int.gcd_eq_gcd_ab], ring },
 { rintro ⟨a,b,rfl⟩, exact dvd_add (dvd_mul_of_dvd_left (int.gcd_dvd_left d g) _)
                          (dvd_mul_of_dvd_left (int.gcd_dvd_right d g) _) },
end

theorem phase_compatible (a d g : ℤ) :
 a ∣ (int.gcd d g : ℤ) ↔ a∣d ∧ a∣g :=
⟨λ h, ⟨dvd_trans h (int.gcd_dvd_left d g),dvd_trans h (int.gcd_dvd_right d g)⟩,
 λ h,int.dvd_gcd h.1 h.2⟩

-- Relative coordinates (b,c); the generator columns have total charge zero.
theorem three_cluster_kernel (b c : ℤ) :
 6 ∣ 3*b+2*c ↔ ∃ x y z : ℤ, b=(-4)*x+6*y ∧ c=(-6)*y+9*z :=
begin
 split,
 { rintro ⟨w,hw⟩,
   have hb : 2 ∣ b := ⟨3*w-b-c, by linarith⟩,
   rcases hb with ⟨v,hv⟩,
   have hc : 3 ∣ c := ⟨w-v, by linarith⟩,
   rcases hc with ⟨u,hu⟩,
   -- y must obey y=v mod 2 and y=u mod 3.
   refine ⟨(3*(3*v-2*u)-v)/2,3*v-2*u,(u+2*(3*v-2*u))/3,_,_⟩,
   { have he : 3*(3*v-2*u)-v=2*(4*v-3*u) := by ring,
     rw [he, int.mul_div_cancel_left _ (by norm_num : (2:ℤ) ≠ 0)], linarith },
   { have he : u+2*(3*v-2*u)=3*(2*v-u) := by ring,
     rw [he, int.mul_div_cancel_left _ (by norm_num : (3:ℤ) ≠ 0)], linarith } },
 { rintro ⟨x,y,z,hb,hc⟩, refine ⟨-2*x+y+3*z,_⟩, rw [hb,hc], ring },
end

theorem partial_pinching (q : ℂ) (a b : ℂ) (h : a=b) :
 (1-q)*a+q*b=a := by rw [h]; ring

theorem partial_fixed_iff (q x y : ℂ) (hq : q≠0) :
 (1-q)*x+q*y=x ↔ y=x :=
begin
 split, { intro h, have hc : q*(y-x)=0 := by linear_combination h,
          exact sub_eq_zero.mp ((mul_eq_zero.mp hc).resolve_left hq) },
 { intro h, rw [h], ring },
end

theorem root_parity (e o : ℝ) :
 (e*e+o*o)-(e*o+o*e)=(e-o)^2 := by ring

theorem root_cannot_be_negative (e o : ℝ) :
 0 ≤ (e*e+o*o)-(e*o+o*e) := by rw [root_parity]; exact sq_nonneg _

theorem independent_integrated_parity (mass : ℝ) : 0 < real.exp (-2*mass) := real.exp_pos _

theorem parity_balance (even odd rate : ℝ) :
 (rate*odd-rate*even)-(rate*even-rate*odd) = -2*rate*(even-odd) := by ring

theorem geometric_odd_index (n : ℕ) : 2*n+1 ≤ 3^n :=
begin induction n with n ih, { norm_num }, { calc 2*n.succ+1 ≤ 3*(2*n+1) : by { clear ih, rw [nat.succ_eq_add_one], nlinarith }
          ... ≤ 3*(3^n) : nat.mul_le_mul_left 3 ih
          ... = 3^n.succ : by rw [pow_succ] } end

def jt (n : ℕ) : ℝ := 4^n/(n.factorial : ℝ)^2

theorem bessel_step (n : ℕ) : jt (n+1) * (n+1 : ℝ)^2 = 4*jt n :=
begin
 have hn : (0:ℝ)<n.factorial := by exact_mod_cast nat.factorial_pos n,
 have hm : (0:ℝ)<n+1 := by positivity,
 simp only [jt,nat.factorial_succ,nat.cast_mul,nat.cast_succ,mul_pow],
 rw [pow_succ (4:ℝ) n], field_simp [ne_of_gt hn,ne_of_gt hm]; ring,
end

theorem bessel_decrease (n : ℕ) (hn : 1 ≤ n) : jt (n+1) ≤ jt n :=
begin
 have h : (1:ℝ) ≤ n := by exact_mod_cast hn,
 have h0 : 0 ≤ jt (n+1) := by unfold jt; positivity,
 have h1 := bessel_step n, nlinarith [mul_nonneg h0 (show (0:ℝ)≤(n+1:ℝ)^2-4, by nlinarith)],
end

theorem bessel_four : jt 0-jt 1+jt 2-jt 3+jt 4=-(1/3:ℝ) :=
by norm_num [jt,nat.factorial]

def upper_partial (n : ℕ) : ℝ := jt 0-jt 1+jt 2-jt 3+jt 4 +
 ∑ i in finset.range n, (jt (2*i+6)-jt (2*i+5))

theorem bessel_even_bound (n : ℕ) : upper_partial n ≤ -(1/3:ℝ) :=
begin
 unfold upper_partial, rw [bessel_four], apply add_le_of_nonpos_right,
 apply finset.sum_nonpos, intros i hi,
 exact sub_nonpos.mpr (bessel_decrease (2*i+5) (by omega)),
end

theorem bessel_limit_bound (J : ℝ) (h : tendsto upper_partial at_top (𝓝 J)) :
 J ≤ -(1/3:ℝ) := le_of_tendsto' h bessel_even_bound

theorem geometric_tail : has_sum (λ n : ℕ, (9/1024:ℝ)^(n+1)) (9/1015:ℝ) :=
begin
 have h:= (has_sum_geometric_of_lt_1 (by norm_num : (0:ℝ)≤9/1024)
   (by norm_num : (9/1024:ℝ)<1)).mul_right (9/1024:ℝ),
 convert h using 1,
 { funext n, rw [pow_succ,mul_comm] }, { norm_num },
end

theorem negative_inclusive (C J : ℝ) (hJ : J ≤ -(1/3:ℝ)) (he : |C-J|≤36/1015) :
 C < -(1/4:ℝ) ∧ (5/8:ℝ)<(1-C)/2 :=
begin have ht := (abs_le.mp he).2, split; linarith end

theorem contaminated (C D r : ℝ) (hC : C < -(1/4:ℝ)) (hD : D≤1)
 (hr : 0≤r) (small : r<1/5) : (1-r)*C+r*D<0 :=
begin have h := mul_lt_mul_of_pos_left hC (show 0<1-r, by linarith),
      have hd := mul_le_mul_of_nonneg_left hD hr, linarith end

-- A half translation has order two. Both kicks act by ordinary multiplication.
theorem half_turn_echo {T : Type*} (p : T → T) (pp : function.involutive p)
 (S : T → ℂ) (t : T) : S (p t) * S (p (p t))=S t*S (p t) :=
by rw [pp t,mul_comm]

theorem recoil_even (k : ℤ) : 2 ∣ k*k-k :=
begin rcases int.even_or_odd k with ⟨i,hi⟩|⟨i,hi⟩;
      [refine ⟨2*i^2-i,_⟩,refine ⟨2*i^2+i,_⟩]; rw [hi]; ring end

-- Parity expectation at an intermediate charge mark; translations by t
-- commute with the half shift. z,w,v,u denote its four unit phase samples.
theorem autocorrelation_factor (z w v u : ℂ) :
 conj (z*u)*(w*v) = conj (z*conj w)*(v*conj u) :=
by simp only [map_mul,complex.conj_conj]; ring

theorem parity_twirl (a b : ℂ) :
 ((a+b)/2)*conj ((a+b)/2) + ((a-b)/2)*conj ((a-b)/2)
 = (a*conj a+b*conj b)/2 :=
by simp only [map_div₀,map_add,map_sub,map_bit0,map_one]; ring

theorem residue_filter {I J : Type*} (A : finset I) (T : finset J) (w : I→ℂ)
 (v : I→J→ℂ) (keep : I→Prop) [decidable_pred keep]
 (filter_values : ∀ i∈A, (∑ j in T,v i j)=if keep i then 1 else 0) :
 (∑ j in T,∑ i in A,w i*v i j)=∑ i in A,if keep i then w i else 0 :=
begin rw [finset.sum_comm], apply finset.sum_congr rfl,
 intros i hi, rw [←finset.mul_sum,filter_values i hi], by_cases h : keep i; simp [h] end

theorem complete_charge_odd (e o : ℝ) (normal : e+o=1) :
 2*e*o=(1-(e-o)^2)/2 := by nlinarith [congr_arg (λ x:ℝ,x^2) normal]

theorem reading_fraction (p n q : ℝ) :
 (1-q)*p+q*((p+n)/2)=(1-q/2)*p+(q/2)*n := by ring

theorem fraction_from_two_controls (p n q : ℝ) (h : n≠p) :
 2*(((1-q/2)*p+(q/2)*n)-p)/(n-p)=q :=
by apply (div_eq_iff (sub_ne_zero.mpr h)).2; ring

theorem certified_write_floor (odd phase q overlap : ℝ)
 (base : 0 ≤ 1-phase) (gram : overlap≤1-q) (id : odd=(1-overlap)*(1-phase)/4) :
 q*(1-phase)/4 ≤ odd :=
begin rw [id], nlinarith [mul_nonneg (show 0≤1-q-overlap,by linarith) base] end

theorem no_early_write (q phase : ℝ) (positive : phase<1)
 (nonneg : 0≤q) (nullreturn : q*(1-phase)≤0) : q=0 :=
by by_contra hn; exact (not_lt_of_ge nullreturn) (mul_pos (lt_of_le_of_ne nonneg (ne.symm hn)) (sub_pos.mpr positive))

-- Finite total-energy fibres. Difference of the two orderings is the odd part.
theorem commutator_vector {V : Type*} [add_comm_group V] (P U : V→+V)
 (PP : ∀ x, P (P x)=x) (x : V) (even : P x=x) :
 let B : V→V := λ v, P (U (P v)), y := U (P (U x)) in
 y - P y = U (B x) - B (U x) := by simp [even]

theorem boundary_commutation {A : Type*} [ring A] (X : A) (a : A)
 (central : a*X=X*a) : X*(a-X)=(a-X)*X := by rw [mul_sub,sub_mul,central]

-- Oscillator coherent displacements for the two orderings. Both complex
-- phases are common for antipodal odd drives. The distance controls visibility.
theorem displacement_difference (a b s : ℂ) :
 (a+s*b)-(b+s*a)=(1-s)*(a-b) := by ring

theorem antipodal_displacement (a s : ℂ) :
 (a+s*(-a))-((-a)+s*a)=2*(1-s)*a := by ring

theorem plain_displacement (a s : ℂ) :
 (a+s*a)-((-a)+s*(-a))=2*(1+s)*a := by ring

theorem damping_nonincrease (x : ℝ) (hx : 0≤x) : 0<real.exp(-x) ∧ real.exp(-x)≤1 :=
⟨real.exp_pos _, real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)⟩

theorem three_transfer_noise (a b c : ℝ) (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) :
 a+b+c=0 ↔ a=0 ∧ b=0 ∧ c=0 :=
begin split, { intro h, refine ⟨_,_,_⟩; linarith }, { rintro ⟨rfl,rfl,rfl⟩, norm_num } end

theorem no_report_from_two_decompositions (affine : ℝ) (charge : affine=0)
 (h : ℝ) (pos : 0<h) (phase : affine=h) : false := by linarith

-- The energy of the difference between two coherent packets may be positive
-- even if their mean energies are equal.
theorem energy_cost_gap {I : Type*} (T : finset I) (w n : I→ℝ) (gap : ℝ)
 (hn : ∀ i∈T, 0≤n i) (hg : ∀ i∈T, gap≤w i) :
 gap*(∑ i in T,n i) ≤ (∑ i in T,w i*n i) :=
begin rw [finset.mul_sum], exact finset.sum_le_sum (λ i hi,mul_le_mul_of_nonneg_right (hg i hi) (hn i hi)) end

theorem overlap_from_gap (gap E N : ℝ) (hg : 0<gap) (h : gap*N≤E) :
 real.exp (-(E/gap)/2) ≤ real.exp (-N/2) :=
begin apply real.exp_le_exp.mpr, have h1 : N≤E/gap := (le_div_iff hg).mpr (by linarith), linarith end

theorem spectral_echo_mid (x c : ℝ) (hx : 0≤x) (hc : c≠0) (xx : x≠0) :
 real.exp (-2*x*c^2)<1 :=
begin apply real.exp_lt_one_iff.mpr, nlinarith [mul_pos (lt_of_le_of_ne hx (ne.symm xx)) (sq_pos_of_ne_zero c hc)] end

theorem ohmic_energy (x : ℝ) (h : x≠-1) : 1-1/(1+x)=x/(1+x) :=
begin have hh : 1+x≠0 := by intro z; apply h; linarith,
 field_simp [hh]; ring end

theorem squared_kick_phase (s c : ℝ) (unit : s^2+c^2=1) : (1-c)^2+s^2=2*(1-c) := by linarith only [unit] <|> nlinarith

theorem equal_current_two_ensembles (h : ℝ) (hh : 0≤h) :
 (abs h + abs (-h))/2=h ∧ ((0:ℝ)+0)/2=0 :=
by rw [abs_neg,abs_of_nonneg hh]; constructor; ring

-- Exact energy and the probability balance at an escaping gravitational exit.
theorem neutral_line (m f w : ℝ) (hm : m≠0) (balance : (m-w)^2=f^2+w^2) :
 w=(m^2-f^2)/(2*m) :=
begin apply (eq_div_iff (mul_ne_zero (by norm_num : (2:ℝ)≠0) hm)).mpr, nlinarith end

theorem compact_mass_difference (u d l : ℝ) : (u^2+l^2)-(d^2+l^2)=u^2-d^2 := by ring

theorem escape_budget (S : finset ι) (p s : ι→ℝ) (hp : (∑ i in S,p i)=1) :
 (∑ i in S,p i*(1-s i))+(∑ i in S,p i*s i)=1 :=
begin
 rw [←finset.sum_add_distrib], transitivity (∑ i in S,p i),
 { apply finset.sum_congr rfl, intros, ring }, { exact hp },
end

theorem survival_variance (S : finset ι) (p r t : ι→ℝ) (a b : ℝ)
 (hp : (∑ i in S,p i)=1) (hr : (∑ i in S,p i*r i)=a) (ht : (∑ i in S,p i*t i)=b) :
 (∑ i in S,p i*((r i-a)^2+(t i-b)^2)) =
 (∑ i in S,p i*((r i)^2+(t i)^2))-(a^2+b^2) :=
begin
 have term : ∀ i:ι, p i*((r i-a)^2+(t i-b)^2)=
  p i*(r i^2+t i^2) - (p i*r i)*(2*a) - (p i*t i)*(2*b) + p i*(a^2+b^2) :=
 λ i, by ring,
 simp only [term,finset.sum_add_distrib,finset.sum_sub_distrib,←finset.sum_mul,hp,hr,ht],
 ring,
end

theorem survivor_contraction {H : Type*} [normed_add_comm_group H] [normed_space ℂ H]
 (M : H →L[ℂ] H) (x y : H) (null : M x=0) (contract : ∀ v,norm (M v)≤norm v) (a : ℂ) :
 norm (M y) ≤ norm (y-a • x) :=
by simpa [map_sub,M.map_smul,null] using contract (y-a • x)

theorem integrate_gravity_width (w t : ℝ) : has_deriv_at (λ s:ℝ, 1-real.exp (-w*s))
 (w*real.exp(-w*t)) t :=
begin
 have h := (has_deriv_at_id t).const_mul (-w),
 convert (has_deriv_at_const t (1:ℝ)).sub h.exp using 1;
 simp [id.def]; ring,
end

-- The normalized root-of-unity filter includes all harmonics.
theorem root_filter (z : ℂ) (n : ℕ) (hn : n≠0) (hz : z^n=1) :
 (∑ j in finset.range n,z^j)/(n:ℂ) = if z=1 then 1 else 0 :=
begin
 by_cases h:z=1, { subst z, simp [hn] },
 { rw [if_neg h,geom_sum_eq h,hz], simp },
end

open_locale complex_inner_product_space
theorem charge_resolved_inner {H : Type*} [normed_add_comm_group H] [inner_product_space ℂ H]
 [complete_space H] (b : hilbert_basis ℤ ℂ H) (x y : H) (w : ℤ→ℂ)
 (diag : ∀ i, ⟪b i,y⟫=w i*⟪b i,x⟫) :
 has_sum (λ i:ℤ, w i * (⟪x,b i⟫*⟪b i,x⟫)) ⟪x,y⟫ :=
begin convert b.has_sum_inner_mul_inner x y using 1, funext i, rw [diag i], ring end

open measure_theory
theorem circle_parseval {T : ℝ} [ht : fact (0<T)]
 (h : Lp ℂ 2 (@add_circle.haar_add_circle T ht)) :
 (∑' k:ℤ, norm (fourier_coeff h k)^2) =
 ∫ t:add_circle T, norm (h t)^2 ∂add_circle.haar_add_circle :=
tsum_sq_fourier_coeff h

theorem positive_bessel_kernel (t k z : ℝ) (hk : 1≤k) (hz : 0≤z) :
 real.exp (-k*z*real.cosh t) ≤ real.exp (-(k-1)*z)*real.exp(-z*real.cosh t) :=
begin
 rw [←real.exp_add], apply real.exp_le_exp.mpr,
 have h1 := mul_nonneg (sub_nonneg.mpr hk) hz,
 nlinarith [mul_nonneg h1 (sub_nonneg.mpr (real.one_le_cosh t))],
end

theorem normalized_integral_error {B : Type*} [measurable_space B] (μ : measure B)
 [is_probability_measure μ] (f g : B→ℝ) (c : ℝ) (hf : integrable f μ) (hg : integrable g μ)
 (bound : ∀ᵐ x ∂μ, norm (f x-g x) ≤ c) :
 norm ((∫ x,f x ∂μ)-(∫ x,g x ∂μ)) ≤ c :=
begin
 rw [←integral_sub hf hg],
 simpa using norm_integral_le_of_norm_le_const bound,
end

theorem continuum_gap {B : Type*} [measurable_space B] (μ : measure B)
 (ω n : B→ℝ) (gap : ℝ) (gn : ∀ᵐ x ∂μ, 0≤n x ∧ gap≤ω x)
 (hn : integrable n μ) (hE : integrable (λ x,ω x*n x) μ) :
 gap*(∫ x,n x ∂μ) ≤ ∫ x,ω x*n x ∂μ :=
begin
 rw [←integral_mul_left], apply integral_mono_ae (hn.const_mul gap) hE,
 exact gn.mono (λ x hx,mul_le_mul_of_nonneg_right hx.2 hx.1),
end

theorem carrier_phase (k n : ℝ) (hk : k≠0) :
 ((k+n)^2-k^2)/(2*k)=n+n^2/(2*k) :=
begin field_simp [hk]; ring end

theorem flight_ratio (p R b k : ℝ) (hp : p≠0) (hR : R≠0) (hb : b≠0) (hk : k≠0) :
 (real.pi*p*R^2/k)/b=real.pi*(p*R)/(k*(b/R)) :=
begin field_simp; ring end

theorem cos_difference (x y : ℝ) : norm (real.cos y-real.cos x) ≤ norm (y-x) :=
begin
 have h : ∀ t∈(set.univ : set ℝ), norm (deriv real.cos t)≤(1:ℝ),
 { intros t ht, rw [real.deriv_cos], simpa [real.norm_eq_abs] using real.abs_sin_le_one t },
 simpa using convex.norm_image_sub_le_of_norm_deriv_le
  (λ t (ht:t∈(set.univ:set ℝ)),real.differentiable_at_cos)
  h convex_univ (set.mem_univ x) (set.mem_univ y),
end

theorem inclusive_from_phase {B : Type*} [measurable_space B] (μ : measure B)
 [is_probability_measure μ] (p b : B→ℝ) (C J : ℝ)
 (hp : integrable (λ x,real.cos (p x)) μ) (hb : integrable (λ x,real.cos (b x)) μ)
 (c : C=∫ x,real.cos (p x) ∂μ) (j : J=∫ x,real.cos (b x) ∂μ)
 (tail : ∀ᵐ x ∂μ, norm (p x-b x)≤36/1015) (hj : tendsto upper_partial at_top (𝓝 J)) :
 C < -(1/4:ℝ) ∧ (5/8:ℝ)<(1-C)/2 :=
begin
 apply negative_inclusive C J (bessel_limit_bound J hj), rw [c,j,←real.norm_eq_abs],
 apply normalized_integral_error μ _ _ _ hp hb,
 exact tail.mono (λ x hx,(cos_difference (b x) (p x)).trans hx),
end

theorem return_measure_revival {B : Type*} [measurable_space B] (μ : measure B)
 (noise : B→ℝ) (pos : ∀ᵐ x ∂μ,0≤noise x) (ok : integrable noise μ) :
 (∫ x,noise x ∂μ)=0 ↔ noise=ᵐ[μ] 0 :=
integral_eq_zero_iff_of_nonneg_ae pos ok

theorem regular_ir_energy (s : ℝ) (h : 0<s) :
 interval_integrable (λ w:ℝ,w^(s-1)) volume 0 1 :=
interval_integral.interval_integrable_rpow' (by linarith)

theorem regular_ir_number (s : ℝ) (h : 1<s) :
 interval_integrable (λ w:ℝ,w^(s-2)) volume 0 1 :=
interval_integral.interval_integrable_rpow' (by linarith)

theorem window_join (s : ℝ) :
 s-2≤-1 ∧ -1<s-1 ↔ 0<s ∧ s≤1 :=
by constructor; rintro ⟨a,b⟩; split; linarith

theorem derivative_count (D : ℤ) : (D-3)+2*2=D+1 := by ring

-- Charge sign is relative to a material orientation.
theorem orientation_covariance (j k : ℤ) : (-j)*(-k)=j*k ∧ (-k)^2=k^2 :=
by constructor; ring

theorem two_path_minimax (c : ℝ) : (1/2:ℝ) ≤ max (abs c) (abs (2*c^2-1)) :=
begin
 by_cases h : (1/2:ℝ) ≤ abs c, { exact le_trans h (le_max_left _ _) },
 have hh := abs_lt.mp (lt_of_not_ge h),
 have prod := mul_nonneg (show 0 ≤ (1/2:ℝ)-c,by linarith) (show 0 ≤ (1/2:ℝ)+c,by linarith),
 apply le_trans _ (le_max_right _ _),
 have nh := le_abs_self (-(2*c^2-1)), rw [abs_neg] at nh, nlinarith,
end

theorem two_path_equal : max (abs (1/2:ℝ)) (abs (2*(1/2:ℝ)^2-1))=1/2 := by norm_num

theorem receiver_dimension {m d : ℕ} (v : fin (m+1) → euclidean_space ℂ (fin d))
 (h : orthonormal ℂ v) : m+1≤d :=
by simpa using finite_dimensional.fintype_card_le_finrank_of_linear_independent h.linear_independent

theorem orthogonal_charge_columns {m d : ℕ} (v : fin (m+1) → euclidean_space ℂ (fin d))
 (H : ∀ i j, ⟪v i,v j⟫=if i=j then 1 else 0) : m+1≤d :=
receiver_dimension v (orthonormal_iff_ite.mpr H)

open_locale matrix
theorem minimal_weights {d : ℕ} (A B : matrix (fin d) (fin d) ℂ)
 (cols : B ⬝ A=1) (w : fin d→ℂ) (row : ∀ r j,A r j*B j r=w r) (r : fin d) :
 (d:ℂ)*w r=1 :=
begin
 have rows : A ⬝ B=1 := matrix.mul_eq_one_comm.mp cols,
 have h := congr_fun (congr_fun rows r) r,
 simpa [matrix.mul_apply,row] using h,
end

theorem distinct_row_moments {d : ℕ} (A B : matrix (fin d) (fin d) ℂ)
 (cols : B ⬝ A=1) (r t : fin d) (hrt : r≠t) (c z : ℂ) (hc : c≠0)
 (row : ∀ j:fin d, A r j*B j t=c*z^(j:ℕ)) : z^d=1 :=
begin
 have rows : A ⬝ B=1 := matrix.mul_eq_one_comm.mp cols,
 have ho := congr_fun (congr_fun rows r) t,
 have he : c*(∑ j:fin d,z^(j:ℕ))=0,
 { rw [finset.mul_sum], simpa [matrix.mul_apply,row,matrix.one_apply,hrt] using ho },
 have hzero := (mul_eq_zero.mp he).resolve_left hc,
 have hh : (∑ j in finset.range d,z^j)=0 := by rwa [←fin.sum_univ_eq_sum_range] at *,
 have eqn := geom_sum_mul z d, rw [hh,zero_mul] at eqn, exact sub_eq_zero.mp eqn.symm,
end

theorem neutral_sign_probability (w plus minus : ℝ) (hp : plus=w/2) (hm : minus=w/2) :
 min plus minus=w/2 := by rw [hp,hm,min_self]

-- Conjugating the projected propagator gives Duhamel's omitted source.
theorem lost_source {A : Type*} [ring A] (P H U V : A) (hp : P*P=P) :
 -((V*(P*H*P))*P)*U+(V*P)*(H*U)=V*P*H*(1-P)*U :=
begin
 have he : V*(P*H*P)*P=V*P*H*P,
 { calc V*(P*H*P)*P = (V*P*H)*(P*P) : by noncomm_ring
                   ... = V*P*H*P : by rw [hp] },
 rw [he], noncomm_ring,
end

theorem projected_derivative {A : Type*} [normed_ring A] [normed_algebra ℝ A]
 (P H : A) (U V : ℝ→A) (t : ℝ) (hp : P*P=P)
 (hU : has_deriv_at U (H*U t) t)
 (hV : has_deriv_at V (-(V t*(P*H*P))) t) :
 has_deriv_at (λ s,V s*P*U s) (V t*P*H*(1-P)*U t) t :=
begin
 convert (hV.mul_const P).mul hU using 1,
 simpa only [neg_mul,add_comm] using (lost_source P H (U t) (V t) hp).symm,
end

theorem duhamel_window {H : Type*} [normed_add_comm_group H] [normed_space ℝ H]
 (f df : ℝ→H) (t b tail : ℝ) (ht : 0≤t)
 (hd : ∀ s∈set.Icc 0 t, has_deriv_at f (df s) s)
 (hbound : ∀ s∈set.Ico 0 t, norm (df s)≤b*tail) :
 norm (f t-f 0)≤t*b*tail :=
begin
 have hh := norm_image_sub_le_of_norm_deriv_le_segment' (λ s hs,(hd s hs).has_deriv_within_at)
   hbound t (set.right_mem_Icc.mpr ht),
 simpa only [sub_zero,mul_comm,mul_left_comm,mul_assoc] using hh,
end

theorem compress_error {H : Type*} [normed_add_comm_group H] (x y z : H) (τ b tail : ℝ)
 (outside : norm (x-y)≤tail) (inside : norm (y-z)≤τ*b*tail) :
 norm (x-z)≤(1+τ*b)*tail :=
begin
 have sub := dist_triangle x y z, simp only [dist_eq_norm] at sub,
 nlinarith,
end

-- At the logarithmic infrared endpoint, every period can contribute a
-- fixed positive multiple of the harmonic series.
theorem harmonic_window (D : ℕ→ℝ) (c : ℝ) (hc : 0<c)
 (lower : ∀ n, c*(∑ k in finset.range n,(1:ℝ)/(k+1))≤D n) :
 tendsto D at_top at_top :=
begin
 apply tendsto_at_top_mono lower,
 exact filter.tendsto.const_mul_at_top hc real.tendsto_sum_range_one_div_nat_succ_at_top,
end

end coherent_gravity_returns
