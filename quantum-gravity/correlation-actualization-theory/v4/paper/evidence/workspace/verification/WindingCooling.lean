import analysis.inner_product_space.basic
import analysis.special_functions.exp_deriv
import analysis.special_functions.exponential
import analysis.special_functions.integrals
import data.nat.choose.vandermonde
import data.int.gcd
import linear_algebra.basic
import tactic

noncomputable theory
open_locale big_operators interval
open filter measure_theory
namespace winding_cooling

theorem dark_recurrence (n k : ℕ) :
 (n.choose (k+1))*(k+1)=n.choose k*(n-k) := nat.choose_succ_right_eq n k

theorem binomial_norm (n : ℕ) :
 ∑ k in finset.range (n+1), (n.choose k)^2=(n+n).choose n :=
begin
 rw [nat.add_choose_eq,finset.nat.sum_antidiagonal_eq_sum_range_succ (λ a b : ℕ, n.choose a*n.choose b)],
 apply finset.sum_congr rfl,intros k hk,
 have hc : n.choose (n-k)=n.choose k := nat.choose_symm (nat.lt_succ_iff.mp (finset.mem_range.mp hk)),
 change n.choose k^2=n.choose k*n.choose (n-k),rw [hc],ring,
end

-- Solves the triangular recursion in the first occupation coordinate.
noncomputable def triangular (a b t : ℕ → ℝ) (k : ℕ) : ℝ :=
 nat.rec_on k (0:ℝ) (λ n prior,(t n-b n*prior)/a n)

theorem triangular_onto (a b t : ℕ → ℝ) (ha : ∀ n,a n≠0) :
 ∃ x : ℕ → ℝ, ∀ k, a k*x (k+1)+b k*x k=t k :=
begin
 refine ⟨triangular a b t,λ k,_⟩,
 change a k*((t k-b k*triangular a b t k)/a k)+b k*triangular a b t k=t k,
 field_simp [ha k];ring,
end

-- Integral in a nonzero squared singular direction of the no-count operator.
theorem single_survival_deriv (s t : ℝ) :
 has_deriv_at (λ x : ℝ,1-real.exp (-(s*x))) (s*real.exp (-(s*t))) t :=
begin
 have h : has_deriv_at (λ x : ℝ,s*x) s t := by simpa using (has_deriv_at_id t).const_mul s,
 convert (has_deriv_at_const t (1:ℝ)).sub h.neg.exp using 1;simp;ring,
end

theorem singular_integral (s T : ℝ) :
 (∫ t in (0:ℝ)..T, s*real.exp (-(s*t)))=1-real.exp (-(s*T)) :=
begin
 have hc : continuous (λ t : ℝ,s*real.exp (-(s*t))) := by continuity,
 rw [interval_integral.integral_eq_sub_of_has_deriv_at
   (λ t ht,single_survival_deriv s t) (hc.interval_integrable 0 T)],simp,
end

theorem singular_tail (s : ℝ) (hs : 0<s) :
 tendsto (λ t : ℝ, real.exp (-(s*t))) at_top (nhds 0) :=
real.tendsto_exp_neg_at_top_nhds_0.comp (tendsto_const_nhds.mul_at_top hs tendsto_id)

-- P is the kernel projector; invA is the inverse on its orthogonal complement.
theorem integrated_surjection {U V : Type*} [add_comm_group U] [module ℂ U]
 [add_comm_group V] [module ℂ V] (J : U →ₗ[ℂ] V) (adj : V → U)
 (invA P : U → U) (onto : function.surjective J)
 (hs : ∀ x, invA (adj (J x))=x-P x) (hd : ∀ x, J (P x)=0) (y : V) :
 J (invA (adj y))=y :=
begin rcases onto y with ⟨x,rfl⟩, rw [hs,J.map_sub,hd,sub_zero], end

theorem group_kernel_dimension (p n : ℕ) :
 (n+p+1).choose (p+1)=(n+p).choose p+(n+p).choose (p+1) :=
nat.choose_succ_succ _ _

theorem two_strand_thermal (q : ℝ) (e d : ℕ) :
 (1-q)^2*q^(d+e)=((1-q)*q^d)*((1-q)*q^e) := by rw [pow_add];ring

theorem classes_gf (q x y : ℝ) (g s : ℕ) : ∀ n : ℕ,
 (((1-q)/(1-q*x))^g*((1-q)/(1-q*y))^s)*
 ((1-q)/(1-q*x))^n=((1-q)/(1-q*x))^(g+n)*((1-q)/(1-q*y))^s :=
by intro n;rw [pow_add];ring

theorem p0_full_rank (z x y : ℝ) (hz : 0≤z) :
 (1-z)*(x^2+y^2)≤x^2+y^2+2*z*x*y :=
begin nlinarith only [mul_nonneg hz (sq_nonneg (x+y))],end

theorem number_lower_bound (x y : ℝ) : (x+y)^2/2≤x^2+y^2 :=
by nlinarith only [sq_nonneg (x-y)]

theorem chiral_imbalance (x y p r : ℝ) (hx : 0≤x) (hy : 0≤y) (hp : 0≤p) (hr : 0≤r) :
 (x+y)^2/2≤x*(x+p)+y*(y+r) :=
by nlinarith only [number_lower_bound x y,mul_nonneg hx hp,mul_nonneg hy hr]

theorem bounded_wait (f g : ℕ → ℝ) (n : ℕ)
 (h : ∀ k∈finset.range n, f k≤g k) :
 ∑ k in finset.range n,f k≤∑ k in finset.range n,g k := finset.sum_le_sum h

theorem dark_rate (z second cross : ℝ) (hd : second+cross=0) :
 second+z*cross=(1-z)*second := by rw [show cross= -second,by linarith];ring

theorem dark_second (n : ℝ) (h : 2*n-1≠0) :
 2*((n/2)^2+n^2/(4*(2*n-1)))=n^3/(2*n-1) :=
begin field_simp;ring,end

theorem bright_rate_step (n d p : ℝ) :
 (n+1-d)*(n+1+d+p+1)-(n-d)*(n+d+p+1)=2*n+p+2 := by ring

theorem waiting_gap (n d : ℕ) (hd : d<n) :
 2*n≤(n-d)*(n+d+1) :=
begin
 obtain ⟨k,hk⟩ := nat.exists_eq_add_of_le (show d+1≤n,from hd),
 subst n,have hs : d+1+k-d=1+k := by omega,
 rw [hs],nlinarith,
end

theorem heralded_bound (weight leakage tail : ℝ) (h : 0<weight) (hn : 0≤leakage)
 (hb : leakage≤tail) : weight/(weight+tail)≤weight/(weight+leakage) :=
begin
 have h1 : 0<weight+tail := by linarith,
 have h2 : 0<weight+leakage := by linarith,
 apply (div_le_div_iff h1 h2).mpr,nlinarith only [mul_nonneg h.le (sub_nonneg.mpr hb)],end

theorem spin_factor (w : ℝ) : ∀ (n : ℕ), w*w^n=w^(n+1) :=
by intro n;rw [pow_succ];ring

theorem negative_eigenvalue (c : ℝ) (hc : 0≤c) :
 min (-c/2) (c/2)= -c/2 := min_eq_left (by linarith)

theorem fading_exposure (g d t : ℝ) (ht : t≠0) (u : ℝ) :
 has_deriv_at (λ x : ℝ, g*d*t*(1-real.exp (-(x/t)))) (g*d*real.exp (-(u/t))) u :=
begin
 have h : has_deriv_at (λ x : ℝ,x/t) (1/t) u := by simpa using (has_deriv_at_id u).div_const t,
 convert ((has_deriv_at_const u (1:ℝ)).sub h.neg.exp).const_mul (g*d*t) using 1;simp;field_simp [ht];ring,
end

theorem detuned_poles (g z d r : ℝ) (h : r^2=g^2*z^2-d^2) :
 ((-g+r)/2)^2+g*((-g+r)/2)+(g^2*(1-z^2)+d^2)/4=0 := by linear_combination h/4

def integral_mode (x : ℝ) (w : ℕ) := ∃ m : ℤ, x*w=m

theorem harmonic_gcd (f : ℝ) (l r : ℕ) :
 integral_mode f l ∧ integral_mode f r ↔ integral_mode f (nat.gcd l r) :=
begin
 split,
 { rintro ⟨⟨i,hi⟩,⟨j,hj⟩⟩,
   have hg : ((nat.gcd l r : ℕ):ℝ)=
     (l:ℝ)*(nat.gcd_a l r:ℤ)+(r:ℝ)*(nat.gcd_b l r:ℤ) := by exact_mod_cast nat.gcd_eq_gcd_ab l r,
   refine ⟨i*nat.gcd_a l r+j*nat.gcd_b l r,_⟩,
   push_cast,rw [hg,mul_add,←mul_assoc,hi,←mul_assoc,hj] },
 { rintro ⟨i,hi⟩,
   have aux : ∀ w : ℕ, nat.gcd l r ∣ w → integral_mode f w,
   { rintro w ⟨k,rfl⟩,refine ⟨i*(k:ℤ),_⟩,push_cast,rw [←mul_assoc,hi] },
   exact ⟨aux l (nat.gcd_dvd_left _ _),aux r (nat.gcd_dvd_right _ _)⟩ },
end

theorem below_first_charged (d h : ℕ) (hd : d≤2) (hp : 0<h) : ¬2*h<d := by omega
theorem winding_examples : nat.gcd 300 600=300 ∧ nat.gcd 299 601=1 :=
begin
 split,
 { exact nat.gcd_eq_left ⟨2,by norm_num⟩ },
 { rw [nat.gcd_rec 299 601],change nat.gcd 3 299=1,
   rw [nat.gcd_rec 3 299],change nat.gcd 2 3=1,
   rw [nat.gcd_rec 2 3],change nat.gcd 1 2=1,simp },
end

theorem trine_probabilities :
 (1684:ℚ)/4225+2547/8450+1/5+1/10=1 ∧ (2547:ℚ)/8450-3/10=6/4225 :=
by norm_num

theorem first_flux (a b z xy : ℝ) (h : xy=0) : a+b+2*z*xy=a+b := by rw [h];ring
theorem energy_exchange (w n e : ℝ) : w*(n-e)+w*e=w*n := by ring

theorem retarded_clock (v : ℝ) (h1 : 1-v≠0) (h2 : 1+v≠0) :
 (1+v)/(1-v^2)=1/(1-v) :=
by rw [show 1-v^2=(1-v)*(1+v),by ring];field_simp;ring

theorem puncture_degeneracy (s t : ℝ) (hs : 0≤s) (ht : 0≤t)
 (h1 : s^2=3/4) (h2 : t^2=12) : 8*s=2*t :=
begin have h : (4*s)^2=t^2 := by nlinarith only [h1,h2],
 have he := (sq_eq_sq (show 0≤4*s,by linarith) ht).mp h, linarith,end


-- Both destinations are isometries on mutually orthogonal comparison sectors.
theorem seam_norm {E : Type*} [normed_add_comm_group E] [inner_product_space ℝ E]
 (x y : E) (orth : ⟪x,y⟫_ℝ=0) :
 ‖x+y‖^2=‖x‖^2+‖y‖^2 :=
begin
 have back : ⟪y,x⟫_ℝ=0 := (real_inner_comm _ _).trans orth,
 calc ‖x+y‖^2 = ⟪x+y,x+y⟫_ℝ : (real_inner_self_eq_norm_sq _).symm
 ... = ‖x‖^2+‖y‖^2 : by rw [inner_add_left,inner_add_right,inner_add_right,orth,back,
  real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq];ring,
end

theorem copies_bound (p lambda : ℝ) (m : ℕ) (hl : 0<lambda)
 (h : p≤1-lambda^m) : p<1 := by linarith only [h,pow_pos hl m]

theorem same_marginal_example :
 (1-((1:ℝ)/2)^2-((1:ℝ)/2)^2)/2=1/4 := by norm_num

theorem branch_at_contact (c i b : ℝ) (h : i+b=1) : c*i+c*b=c :=
by linear_combination c*h

-- An outward signal from a boundary into a region reaching infinity would itself reach infinity.
theorem causal_boundary {X : Type*} (reach : X → X → Prop)
 (trans : ∀ p q r,reach p q → reach q r → reach p r) (p q infinity : X)
 (h : ¬reach p infinity) (hq : reach q infinity) : ¬reach p q :=
λ hp, h (trans p q infinity hp hq)

theorem moving_edge (vel dr : ℝ) (h : vel<0) (outgoing : 2*dr=0) :
 2*vel<0 ∧ 0<dr-vel := by split;linarith

theorem edge_proper_time (R a c : ℝ) (hc : c≠0) (h : c^2=2*a)
 (hr : R≠0) : (c/R)^2=2*a/R^2 := by field_simp;linear_combination h

theorem area_clock_deriv (C R : ℝ) :
 has_deriv_at (λ r : ℝ, C*r^2) (2*C*R) R :=
begin convert ((has_deriv_at_id R).pow 2).const_mul C using 1;simp;ring,end

theorem radial_release_time (T i r : ℝ) (hi : 0≤i) (hr : 0≤r)
 (hq : 0≤T) (h : r≤1) : i*r*T≤i*T :=
by nlinarith only [mul_nonneg (mul_nonneg hi hq) (sub_nonneg.mpr h)]

theorem two_windows (x y : ℝ) :
 x+(1-x)*y+(1-x)*(1-y)=1 := by ring

theorem rising_capture (s t : ℝ) :
 has_deriv_at (λ x : ℝ,real.exp (s*x)) (s*real.exp (s*t)) t :=
begin have h : has_deriv_at (λ x : ℝ,s*x) s t := by simpa using (has_deriv_at_id t).const_mul s,
 convert h.exp using 1;ring,end

theorem gravitational_port_peak (x s : ℝ) (hs : s^2=17) (hx : x=(9+s)/8) :
 -12*x^2+27*x-12=0 := by rw [hx];linear_combination -3*hs/16

-- D denotes the adjoint of C in the application. This identity holds in any operator ring.
theorem seam_effect {A : Type*} [ring A] (C D P Q U L V M : A)
 (hu : L*U=1) (hv : M*V=1) (hp : P*P=P) (hq : Q*Q=Q)
 (hs : P+Q=1) :
 (D*P*L)*(U*P*C)+(D*Q*M)*(V*Q*C)=D*C :=
calc (D*P*L)*(U*P*C)+(D*Q*M)*(V*Q*C) = D*(P*(L*U)*P+Q*(M*V)*Q)*C : by noncomm_ring
 ... = _ : by simp [hu,hv,hp,hq,hs]

-- Surviving comparison projectors are nested as a physical receipt is added.
theorem nested_survival {A : Type*} [ring A] (S P r : A)
 (ha : S*P=S) (hb : P*S=S) : S*(P*r*P)*S=S*r*S :=
calc S*(P*r*P)*S = (S*P)*r*(P*S) : by noncomm_ring
 ... = _ : by rw [ha,hb]

theorem receipt_recurrence (u v : ℝ) : ∀ m : ℕ,
 (u-v)*(∑ k in finset.range (m+1),u^k*v^(m-k))=u^(m+1)-v^(m+1) :=
begin
 intro m,induction m with m ih,
 { simp },
 { have sm : (∑ k in finset.range (m+1+1),u^k*v^(m+1-k))
      = (∑ k in finset.range (m+1),u^k*v^(m-k))*v + u^(m+1) :=
   begin rw [finset.sum_range_succ,finset.sum_mul],simp only [nat.sub_self,pow_zero,mul_one],
     congr' 1, apply finset.sum_congr rfl,intros k hk,
     have hle : k≤m := nat.lt_succ_iff.mp (finset.mem_range.mp hk),
     have he : m+1-k=(m-k)+1 := by omega,
     rw [he,pow_succ],ring,end,
   rw [sm],calc (u-v)*((∑ k in finset.range (m+1),u^k*v^(m-k))*v+u^(m+1))
      = ((u-v)*(∑ k in finset.range (m+1),u^k*v^(m-k)))*v+(u-v)*u^(m+1) : by ring
   ... = _ : by rw [ih,pow_succ u (m+1),pow_succ v (m+1)];ring },
end

theorem mixed_receipt_pair (v : ℝ) :
 1-(((1+v)/2)^2+((1+v)/2)*((1-v)/2)+((1-v)/2)^2)=(1-v^2)/4 := by ring

theorem cooling_shift (e00 e10 e01 e11 : ℝ) :
 (e11-e01)-(e10-e00)=e11-e10-e01+e00 := by ring

-- Loss of the distinction between two inputs prevents every subsequent deterministic recovery.
theorem lost_relative_phase {A B : Type*} (write : A → B) (x y : A)
 (distinct : x≠y) (h : write x=write y) :
 ¬∃ decode : B → A, decode (write x)=x ∧ decode (write y)=y :=
begin rintro ⟨f,hx,hy⟩,exact distinct (hx.symm.trans ((congr_arg f h).trans hy)),end

theorem matched_thermal_line (a b q spectral : ℝ) (hd : 1-q≠0)
 (h1 : a-b=spectral) (h2 : b=q*a) : b=spectral*q/(1-q) :=
begin apply (eq_div_iff hd).mpr,rw [←h1,h2],ring,end

theorem evaporation_clock_derivative (g k M : ℝ) (hk : k≠0) :
 has_deriv_at (λ x : ℝ,g^2*x^3/(3*k)) (g^2*M^2/k) M :=
begin convert (((has_deriv_at_id M).pow 3).const_mul (g^2)).div_const (3*k) using 1;simp;field_simp [hk];ring,end

theorem radiation_information (logical info grav coarse : ℝ)
 (hc : 2*logical≤info) (ha : info≤2*grav) (hs : grav≤coarse) : logical≤coarse := by linarith

theorem page_tensor_ceiling :
 (1379:ℚ)/10000 < (13481:ℚ)/10000*3836/(33638+3836) ∧
 (13481:ℚ)/10000*3836/(33638+3836)<1381/10000 := by norm_num

def arrival_weight (e : ℝ) (n : ℕ) := real.exp (-e)*e^n/(n.factorial:ℝ)

theorem poisson_generating (e t : ℝ) :
 has_sum (λ n : ℕ, arrival_weight e n*t^n) (real.exp (e*(t-1))) :=
begin
 have a := exp_series_div_has_sum_exp ℝ (e*t),
 rw [←real.exp_eq_exp_ℝ] at a,
 have b := a.mul_left (real.exp (-e)),
 convert b using 1,
 { funext n,dsimp [arrival_weight],rw [mul_pow],ring },
 { rw [←real.exp_add],congr' 1,ring },
end

theorem poisson_receipt_survival (e u d : ℝ) (hne : u≠d) :
 has_sum (λ n : ℕ, arrival_weight e n*(∑ k in finset.range (n+1),u^k*d^(n-k)))
 ((u*real.exp (e*(u-1))-d*real.exp (e*(d-1)))/(u-d)) :=
begin
 have h := (((poisson_generating e u).mul_left u).sub ((poisson_generating e d).mul_left d)).div_const (u-d),
 convert h using 1,funext n,apply (eq_div_iff (sub_ne_zero.mpr hne)).mpr,
 calc (arrival_weight e n*(∑ k in finset.range (n+1),u^k*d^(n-k)))*(u-d)
   = arrival_weight e n*((u-d)*(∑ k in finset.range (n+1),u^k*d^(n-k))) : by ring
 ... = _ : by rw [receipt_recurrence,pow_succ,pow_succ];ring,
end

theorem equal_receipts_derivative (t : ℝ) :
 has_deriv_at (λ x : ℝ, (1+x/2)*real.exp (-(x/2))) (-(t/4)*real.exp (-(t/2))) t :=
begin
 have h : has_deriv_at (λ x : ℝ,x/2) (1/2:ℝ) t := by simpa using (has_deriv_at_id t).div_const 2,
 convert ((has_deriv_at_const t (1:ℝ)).add h).mul h.neg.exp using 1;simp;ring,
end

-- Eigenvalues of the positive boundary effect control the Schmidt coefficients of the
-- normalized, heralded Stinespring vector; n is any negativity after discarding outputs.
theorem boundary_bias_versus_recovery (p q n : ℝ) (hp : 0≤p) (hq : 0≤q)
 (hs : 0<p+q) (hn : 0≤n) (hb : n≤real.sqrt (p*q)/(p+q)) :
 (2*n)^2+((p-q)/(p+q))^2≤1 :=
begin
 have ha : 0≤n*(p+q) := mul_nonneg hn hs.le,
 have hm : n*(p+q)≤real.sqrt (p*q) := (le_div_iff hs).mp hb,
 have sq : (n*(p+q))^2≤(real.sqrt (p*q))^2 := by simpa only [pow_two] using mul_self_le_mul_self ha hm,
 rw [real.sq_sqrt (mul_nonneg hp hq)] at sq,
 rw [div_pow],have den : 0<(p+q)^2 := pow_pos hs _,
 apply (mul_le_mul_right den).mp,
 rw [add_mul, div_mul_cancel _ (ne_of_gt den),one_mul],
 nlinarith only [sq],
end

theorem continuity_null_sectors (all deficit completed : ℝ)
 (h : all=deficit+completed) : (1-completed)-(1-all)=deficit := by linarith

theorem insufficient_receipts_deriv (t : ℝ) :
 has_deriv_at (λ x : ℝ,(1+x)*real.exp (-x)) (-t*real.exp (-t)) t :=
begin
 convert ((has_deriv_at_const t (1:ℝ)).add (has_deriv_at_id t)).mul (has_deriv_at_id t).neg.exp using 1;simp;ring,
end

theorem mixed_continuity_deriv (t : ℝ) :
 has_deriv_at (λ x : ℝ,(1+x/2)*real.exp (-(x/2))-(1+x)*real.exp (-x))
 (t*real.exp (-(t/2))*(real.exp (-(t/2))-1/4)) t :=
begin
 convert (equal_receipts_derivative t).sub (insufficient_receipts_deriv t) using 1,
 rw [show -t= -(t/2)+ -(t/2),by ring,real.exp_add],ring,
end

theorem mixed_continuity_peak (L t a : ℝ) (ht : t=2*L) (ha : a=1/4) :
 (1+t/2)*a-(1+t)*a^2=(3+2*L)/16 := by rw [ht,ha];ring

theorem mixed_slope_sign (t a : ℝ) (ht : 0<t) (ha : 0<a) :
 0≤t*a*(a-1/4) ↔ 1/4≤a :=
begin
 have h : t*a*0≤t*a*(a-1/4) ↔ (0:ℝ)≤a-1/4 := mul_le_mul_left (mul_pos ht ha),
 simpa only [mul_zero,sub_nonneg] using h,
end

end winding_cooling
