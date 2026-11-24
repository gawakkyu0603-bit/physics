import tactic
import analysis.special_functions.integrals
import analysis.calculus.mean_value
import analysis.inner_product_space.basic
import linear_algebra.matrix.trace

noncomputable theory
open_locale big_operators real
open measure_theory set
namespace horizon_pair_conversion

theorem clock_roll (F t s c : ℝ) (ht : t≠0) :
 F*((s/t)*c/t)=F*s*c/t^2 := by {field_simp [ht];ring}

theorem clock_work (inertia speed force dmass variance vacuum : ℝ)
 (eom : inertia*force= -(dmass*(variance-vacuum)/2)) :
 inertia*speed*force+(speed*dmass)*(variance-vacuum)/2=0 :=
by linear_combination speed*eom

theorem clock_crossing_requires_energy (surplus kinetic excitation : ℝ)
 (ener : surplus=kinetic+excitation) (h : 0≤kinetic) : excitation≤surplus := by linarith

theorem quench_below_thermal (a b x : ℝ) (hb : 0≤b) (hba : b<a) (ha : a<1) (hx : 0<x) :
 0<x*((1-a)/(1-b))^2 ∧ x*((1-a)/(1-b))^2<x :=
begin
 have h : 0<(1-a)/(1-b) := div_pos (by linarith) (by linarith),
 have k : (1-a)/(1-b)<1 := (div_lt_one (by linarith)).2 (by linarith),
 have s := mul_pos h (sub_pos.mpr k),
 exact ⟨mul_pos hx (pow_pos h 2),by nlinarith [mul_pos hx (show 0<1-((1-a)/(1-b))^2,by nlinarith)]⟩
end

theorem fixed_level_log_error {ι : Type*} [fintype ι] (n j e : ι→ℝ) (δ N : ℝ)
 (n_pos : ∀ i,0≤n i) (bound : ∀ i,abs(e i)≤δ*j i)
 (level : ∑ i,n i*j i=N) : abs(∑ i,n i*e i)≤δ*N :=
calc abs(∑ i,n i*e i) ≤ ∑ i,abs(n i*e i) : finset.abs_sum_le_sum_abs _ _
 ... ≤ ∑ i,δ*(n i*j i) : finset.sum_le_sum (λ i hi,by
 {rw [abs_mul,abs_of_nonneg (n_pos i)],nlinarith [mul_le_mul_of_nonneg_left (bound i) (n_pos i)]})
 ... = δ*N : by rw [←finset.mul_sum,level]

theorem front_doppler (h : ℝ) (h1 : h≠1) (hm : h≠-1) :
 (1/(1+h)+1/(1-h))/2=1/(1-h^2) :=
begin
 have a : 1+h≠0 := by intro z; apply hm; linarith,
 have b : 1-h≠0 := sub_ne_zero.mpr (ne.symm h1),
 have c : 1-h^2=(1+h)*(1-h) := by ring,
 rw [c];field_simp [a,b];ring
end

theorem front_energy (h : ℝ) :
 (1+h)^2-(1-h)^2=4*h ∧ (1+h)^2+(1-h)^2=2*(1+h^2) := by split;ring

theorem front_release (h : ℝ) : 1-2*h/(1+h^2)=(1-h)^2/(1+h^2) :=
by {have hp : 1+h^2≠0 := by nlinarith [sq_nonneg h],field_simp [hp];ring}

theorem bounded_front_flow (released energy flux speed : ℝ) (hs : 0<speed)
 (h : flux≤(energy-released)/speed) : released≤energy-speed*flux :=
by {have := (le_div_iff hs).mp h,nlinarith}

theorem infall_budget (x r : ℝ) (hx : 1≤x) (hph : x≤3/2) (hr : 1≤r) :
 x/(1+r)≤3/4 := by {rw [div_le_iff (by linarith : 0<1+r)],linarith}

theorem fall_integral (x : ℝ) (hx : 1≤x) (hph : x≤3/2) (f : ℝ→ℝ)
 (hi : interval_integrable f volume x (3/2)) (hb : ∀ t∈Icc x (3/2:ℝ),f t≤3/4) :
 (∫ t in x..(3/2),f t)≤3/8 :=
begin
 have h := interval_integral.integral_mono_on hph hi (continuous_const.interval_integrable _ _) hb,
 simp only [interval_integral.integral_const,smul_eq_mul] at h,
 linarith
end

theorem warmup_gap (z rs integ : ℝ) (hz : 0<z) (hr : 0<rs) (hb : integ≤3/8) :
 z*rs*integ<2*rs*z :=
by nlinarith [mul_pos (mul_pos hz hr) (show 0<2-integ,by linarith)]

theorem common_correlation (n d m A : ℝ) (hd : d≠0) (hplus : d+1≠0)
 (mean : d*m=n) (pair : d*(d+1)*A=n*(n-1)) :
 d*(2*A+m)+d*(d-1)*A=n^2 := by nlinarith

theorem numerator_denominator (x q : ℝ) (h : x≠1) (hz : 1+x*q≠0) :
 ((x/(1-x))^2+((x/(1-x))^2+x/(1-x))*q)/
 ((1+x/(1-x))^2+((x/(1-x))^2+x/(1-x))*q)=(x^2+x*q)/(1+x*q) :=
begin
 have n : 1-x≠0 := sub_ne_zero.mpr (ne.symm h),
 have a : (x/(1-x))^2+((x/(1-x))^2+x/(1-x))*q=(x^2+x*q)/(1-x)^2 := by {field_simp [n];ring},
 have b : (1+x/(1-x))^2+((x/(1-x))^2+x/(1-x))*q=(1+x*q)/(1-x)^2 := by {field_simp [n];ring},
 rw [a,b],field_simp [n,hz];ring
end

theorem thermal_iff_dark (x q : ℝ) (hx : 0<x) (ho : x<1) (hq : 0≤q) :
 (x^2+x*q)/(1+x*q)=x^2 ↔ q=0 :=
begin
 have pos : 0<1+x*q := by nlinarith [mul_nonneg hx.le hq],
 rw [div_eq_iff (ne_of_gt pos)],split,
 {intro h,by_contra hn,
  have k := mul_pos (mul_pos hx (lt_of_le_of_ne hq (ne.symm hn)))
    (show 0<1-x^2,by nlinarith [mul_pos (sub_pos.mpr ho) (show 0<1+x,by linarith)]),
  nlinarith},
 {rintro rfl,ring}
end

theorem one_percent (q : ℝ) (h : 0≤q) :
 (((1/2:ℝ)^2+(1/2)*q)/(1+(1/2)*q)≤(101/100)*(1/2)^2) ↔ q≤2/299 :=
by {rw [div_le_iff (by linarith : 0<1+(1/2:ℝ)*q)],split;intro h;ring_nf at *;linarith}

theorem scalar_width (gamma : ℝ) (h : 0≤gamma) :
 2*gamma/(3+gamma)≤2/299 ↔ gamma≤3/298 :=
by {rw [div_le_iff (by linarith : 0<3+gamma)],split;intro h;linarith}

theorem detuning_test (D : ℝ) :
 (1/16:ℝ)/(D^2+1/4)≤3/298 ↔ 143/24≤D^2 :=
by {rw [div_le_iff (by nlinarith [sq_nonneg D] : 0<D^2+1/4)],split;intro h;linarith}

theorem oscillator_pair_extremum (d : ℝ) (peak : ℕ→ℝ) (vac : peak 0=0)
 (comm : ∀ n,peak (n+1)=peak n+2*(n:ℝ)+d) :
 ∀ n : ℕ, peak n=(n:ℝ)*(n+d-1) :=
begin
 intro n,induction n with n ih,
 {simpa using vac},
 {rw [comm,ih],push_cast,ring}
end

theorem traceless_gap (d n peak : ℝ) (hd : 0<d) (h : peak≤n*(n+d-1)) :
 (d-1)*n*(n-1)/d≤n^2-peak/d :=
by {rw [le_sub_iff_add_le,←add_div,div_le_iff hd],nlinarith}

theorem telescoping_wait (n : ℝ) (hn : 0<n) :
 1/(n*(n+1))=1/n-1/(n+1) :=
by {have hp : n+1≠0 := by linarith,field_simp [ne_of_gt hn,hp];ring}

theorem finite_wait_sum (n : ℕ) :
 (∑ j in finset.range n,1/(((j:ℝ)+1)*(j+2)))=1-1/((n:ℝ)+1) :=
begin
 induction n with n ih,
 {simp},
 {rw [finset.sum_range_succ,ih],push_cast,
  have h : 0<(n:ℝ)+1 := by positivity,
  have a : (n:ℝ)+2=n+1+1 := by ring,
  rw [a,telescoping_wait _ h],ring}
end

-- Positivity of a Gram form for an arbitrary time/port measure.
theorem integrated_square {α : Type*} [measurable_space α] (μ : measure α)
 (a b c : α→ℝ) (ha : integrable a μ) (hb : integrable b μ) (hc : integrable c μ)
 (pos : ∀ t k,0≤a t-2*k*c t+k^2*b t) (k : ℝ) :
 0≤(∫ t,a t ∂μ)-2*k*(∫ t,c t ∂μ)+k^2*(∫ t,b t ∂μ) :=
begin
 have h := @integral_nonneg α _ μ (λ t,a t-(2*k)*c t+k^2*b t) (λ t,pos t k),
 have ha' : integrable (λ t,a t-(2*k)*c t) μ := ha.sub (hc.const_mul (2*k)),
 change 0≤∫ t,(a t-(2*k)*c t)+k^2*b t ∂μ at h,
 rw [integral_add ha' (hb.const_mul (k^2)),integral_sub ha (hc.const_mul (2*k)),integral_mul_left,integral_mul_left] at h,
 exact h
end

theorem necessary_free_exposure (s I C : ℝ) (hs : 0≤s) (hl : s<1)
 (overlap : 2*(1-s)≤C)
 (gram : ∀ k : ℝ,0≤I-2*k*C+k^2*(1-s^2)) :
 4*(1-s)/(1+s)≤I :=
begin
 have h : 0<1+s := by linarith,
 have key := gram (2/(1+s)),
 have ident : (2/(1+s))^2*(1-s^2)=4*(1-s)/(1+s) :=
 by {field_simp [ne_of_gt h];ring},
 rw [ident] at key,
 have positive : 0<(2:ℝ)/(1+s) := div_pos (by norm_num) h,
 have use := mul_le_mul_of_nonneg_left overlap (mul_nonneg (by norm_num : (0:ℝ)≤2) positive.le),
 have id2 : 2*(2/(1+s))*(2*(1-s))=8*(1-s)/(1+s) := by ring,
 rw [id2] at use,
 have twice : 8*(1-s)/(1+s)=2*(4*(1-s)/(1+s)) := by ring,
 rw [twice] at use,linarith
end

theorem time_bound_at_one_percent (I W : ℝ) (gram : 36/11≤I) (spectrum : I≤(2/299)*W) :
 (5382/11:ℝ)≤W := by linarith

theorem reciprocal_speed (r deriv : ℝ) (hr : r<1) (h : deriv≤(1-r)^2/4) :
 deriv/(1-r)^2≤1/4 :=
by {rw [div_le_iff (sq_pos_of_pos (sub_pos.mpr hr))],linarith}

theorem riccati_barrier (r x : ℝ) (hr : r<1) (hx : 0≤x)
 (bound : r/(1-r)≤x/4) : r≤x/(4+x) :=
by {rw [div_le_iff (sub_pos.mpr hr)] at bound,rw [le_div_iff (by linarith : 0<4+x)],nlinarith}

theorem maximal_output_fraction (a b : ℝ) (ha : 0≤a) (hr : a≤b) :
 a^2/(1+a^2)≤b^2/(1+b^2) :=
begin
 rw [div_le_div_iff (by nlinarith [sq_nonneg a] : 0<1+a^2)
   (by nlinarith [sq_nonneg b] : 0<1+b^2)],
 nlinarith [mul_nonneg (sub_nonneg.mpr hr) (show 0≤b+a,by linarith)]
end

theorem two_level_loss (a b c d g k D : ℝ) :
 2*(a*(g*d)+b*(-g*c)+c*(g*b-k*c/2+D*d)+d*(-g*a-k*d/2-D*c))
 = -k*(c^2+d^2) := by ring

theorem critical_decay (x : ℝ) :
 has_deriv_at (λ u : ℝ,real.exp (-u/2)*((1+u/4)^2+(u/4)^2))
  (-(real.exp (-x/2)*(x/4)^2)) x :=
begin
 have q := (has_deriv_at_id x).div_const (4:ℝ),
 have e := ((has_deriv_at_id x).neg.div_const (2:ℝ)).exp,
 convert e.mul (((q.const_add 1).pow 2).add (q.pow 2)) using 1; simp; ring
end

theorem redshift_contrast (za zb m r l : ℝ) (rp : r≠0) (bp : r+l≠0)
 (np : za+zb≠0) (diff : zb^2-za^2=2*m/r-2*m/(r+l)) :
 zb-za=2*m*l/(r*(r+l)*(za+zb)) :=
begin
 have h : (zb-za)*(za+zb)=2*m*l/(r*(r+l)) :=
 by {calc (zb-za)*(za+zb)=zb^2-za^2 : by ring
 ... = 2*m/r-2*m/(r+l) : diff
 ... = _ : by {field_simp [rp,bp];ring}},
 field_simp [rp,bp,np] at h ⊢;nlinarith
end

theorem two_path_residual (p visibility : ℝ) :
 p^2+(1-p)^2-2*p*(1-p)*visibility=
 (2*p-1)^2+2*p*(1-p)*(1-visibility) := by ring

theorem perfect_port (p v : ℝ) (hp : 0<p) (ho : p<1) (hv : v≤1) :
 p^2+(1-p)^2-2*p*(1-p)*v=0 ↔ p=1/2 ∧ v=1 :=
begin
 rw [two_path_residual],split,
 {intro h,have k : 0<2*p*(1-p) := mul_pos (mul_pos (by norm_num) hp) (sub_pos.mpr ho),
  have n := mul_nonneg k.le (sub_nonneg.mpr hv),
  have a : 2*p-1=0 := by nlinarith [sq_nonneg (2*p-1)],
  have b : 2*p*(1-p)*(1-v)=0 := by nlinarith,
  rcases mul_eq_zero.mp b with h'|h',
  {linarith}, {split;linarith}},
 {rintro ⟨rfl,rfl⟩,norm_num}
end

theorem flavour_swap {E : Type*} [add_comm_group E] [module ℝ E] (a b : E) :
 (1/2:ℝ) • ((a+b)-(a-b))=b ∧ (1/2:ℝ) • ((a+b)+(a-b))=a :=
begin
 have H : ∀ x : E,(1/2:ℝ) • (x+x)=x,
 {intro x, rw [←two_smul ℝ x,smul_smul],norm_num},
 have k : (a+b)-(a-b)=b+b := by abel,
 have j : (a+b)+(a-b)=a+a := by abel,
 rw [k,j],exact ⟨H _,H _⟩
end
theorem fock_two_contractions {ι : Type*} [fintype ι] [decidable_eq ι]
 (c : ι→ι→ℝ) (A m : ℝ) :
 (∑ a, ∑ b, A*(c a b)^2) + (∑ a,∑ b,(A+m)*(c a a)*(c b b))=
 A*(∑ a,∑ b,(c a b)^2)+(A+m)*(∑ a,c a a)^2 :=
begin
 simp_rw [←finset.mul_sum],
 rw [pow_two,finset.sum_mul],
 congr' 1,
 rw [finset.mul_sum],
 apply finset.sum_congr rfl,intros i hi,ring
end

theorem complete_loss_basis {ι : Type*} [fintype ι] (x y : ι→ℝ) (n : ℝ)
 (hl : ∑ i,x i=n) (hr : ∑ i,y i=n) :
 (∑ i,∑ j,x i*y j)=n^2 :=
by {simp_rw [←finset.mul_sum],rw [←finset.sum_mul,hl,hr],ring}

theorem charged_clock_separatrix (t T : ℝ) (ht : T≠0) :
 has_deriv_at (λ u : ℝ,real.exp (u/T)) (real.exp (t/T)/T) t :=
begin
 convert ((has_deriv_at_id t).div_const T).exp using 1;simp;ring
end

theorem log_coordinate_speed (y v : ℝ) (h : y<1) :
 has_deriv_at (λ t : ℝ, t/(1-t)) (1/(1-y)^2) y :=
begin
 have nz : 1-y≠0 := ne_of_gt (sub_pos.mpr h),
 convert (has_deriv_at_id y).div ((has_deriv_at_const y (1:ℝ)).sub (has_deriv_at_id y)) nz using 1;simp;ring
end

theorem riccati_phase_bound (r w : ℝ) (hz : 0≤r) (hw : w≤1) :
 w*(1+r^2)/4-r/2≤(1-r)^2/4 :=
by nlinarith [mul_nonneg (sub_nonneg.mpr hw) (show 0≤1+r^2,by nlinarith [sq_nonneg r])]

theorem linear_response_norm (re im are aim : ℝ) :
 (re^2+im^2)*(are^2+aim^2)-(re*are+im*aim)^2=(re*aim-im*are)^2 := by ring

theorem width_from_advanced (s ri rf eps omega : ℝ) (hs : s≠0) :
 eps*omega*((ri-rf)/s)=eps*omega*(ri-rf)/s := by ring

theorem fixed_delays_across_band (eta v : ℝ) (h : 0<eta) (h1 : eta<1) :
 eta^2+(1-eta)^2-2*eta*(1-eta)*0≥1/2 :=
by nlinarith [sq_nonneg (2*eta-1)]

theorem time_integral_slope (T : ℝ) (hT : 0≤T) (f g : ℝ→ℝ) (c : ℝ)
 (init : f 0=0) (hd : ∀ t∈uIcc 0 T,has_deriv_at f (g t) t)
 (hi : interval_integrable g volume 0 T) (hb : ∀ t∈Icc (0:ℝ) T,g t≤c) :
 f T≤T*c :=
begin
 have integral := interval_integral.integral_eq_sub_of_has_deriv_at hd hi,
 have upper := interval_integral.integral_mono_on hT hi
    (interval_integrable_const : interval_integrable (λ _:ℝ,c) volume 0 T) hb,
 rw [integral,init,sub_zero] at upper,
 change f T≤∫ t in (0:ℝ)..T,c at upper,
 simpa only [interval_integral.integral_const,sub_zero,smul_eq_mul] using upper
end

theorem critical_ratio_on_interval (T : ℝ) (hT : 0≤T) (r v : ℝ→ℝ) (zero : r 0=0)
 (one : ∀ t∈uIcc 0 T,r t<1) (dr : ∀ t∈uIcc 0 T,has_deriv_at r (v t) t)
 (speed : ∀ t∈Icc (0:ℝ) T,v t≤(1-r t)^2/4)
 (hi : interval_integrable (λ t,v t/(1-r t)^2) volume 0 T) :
 r T≤T/(4+T) :=
begin
 have zero' : r 0/(1-r 0)=0 := by simp [zero],
 have hd : ∀ t∈uIcc 0 T,has_deriv_at (λ y,r y/(1-r y)) (v t/(1-r t)^2) t,
 {intros t ht,
  convert (log_coordinate_speed (r t) 0 (one t ht)).comp t (dr t ht) using 1;ring},
 have h := time_integral_slope T hT (λ t,r t/(1-r t)) (λ t,v t/(1-r t)^2)
    (1/4) zero' hd hi (λ t ht,reciprocal_speed _ _ (one t (by rwa [set.uIcc_of_le hT])) (speed t ht)),
 exact riccati_barrier _ _ (one T (by {rw [set.uIcc_of_le hT],exact ⟨hT,le_rfl⟩})) hT (by linarith)
end

theorem passive_dark_positive {ι : Type*} [fintype ι] (g S : ι→ℝ)
 (hg : ∀ i,0<g i) (hS : ∀ i,0≤S i) (hz : ∑ i,g i*S i=0) : ∀ i,S i=0 :=
begin
 intro i,have h := finset.single_le_sum (λ j (hj : j∈(finset.univ : finset ι)),mul_nonneg (hg j).le (hS j)) (finset.mem_univ i),
 rw [hz] at h,
 have zero := le_antisymm h (mul_nonneg (hg i).le (hS i)),
 exact (mul_eq_zero.mp zero).resolve_left (ne_of_gt (hg i))
end

theorem equal_transfer_of_phase {E : Type*} [add_comm_group E] [module ℝ E] (a b : E) :
 (1/2:ℝ) • ((a+b)+(a-b))=a ∧ (1/2:ℝ) • ((a+b)-(a-b))=b :=
(flavour_swap a b).symm

theorem last_budget (epsilon omega ri rf s nf u : ℝ)
 (hp : 0<rf) (hv : 0<s) (he : 0≤epsilon) (hr : rf≤ri)
 (hw : omega*rf≤nf) (ratio : ri≤u*rf) (hn : 0≤nf) :
 epsilon*omega*(ri-rf)/s≤epsilon*nf*(u-1)/s :=
begin
 apply div_le_div_of_le hv.le,
 have k := mul_le_mul_of_nonneg_right ((le_div_iff hp).mpr hw) (sub_nonneg.mpr hr),
 have t : nf/rf*(ri-rf)≤nf*(u-1),
 {have z : nf/rf*(ri-rf)=nf*((ri-rf)/rf) := by ring,
  rw [z],apply mul_le_mul_of_nonneg_left _ hn,rw [div_le_iff hp],nlinarith},
 nlinarith [mul_le_mul_of_nonneg_left (k.trans t) he]
end

theorem increasing_charge (ri rf qi qf M : ℝ)
 (hi : 0≤ri) (hr : 0<rf) (hq : 0<qf) (mono : qf≤qi)
 (same : ri^2*qi=M*(rf^2*qf)) : (ri/rf)^2≤M :=
begin
 rw [div_pow,div_le_iff (sq_pos_of_pos hr)],
 have h := mul_le_mul_of_nonneg_left mono (sq_nonneg ri),
 apply le_of_mul_le_mul_right _ hq,
 nlinarith
end

theorem release_coverage (v lambda e s D cap : ℝ)
 (hp : 0<lambda) (hs : 0<s) (hv : 0≤v) (he : 0≤e)
 (energy : v≤cap*lambda) (path : D=v*e/(lambda*s)) : D≤cap*e/s :=
begin
 rw [path, div_le_div_iff (mul_pos hp hs) hs],
 nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right energy he) hs.le]
end
section maxwell
theorem measured_stress (D C L V : ℝ) (h : V≠1) (k : V≠-1) :
 ((D^2+C^2)/2-L^2+2*V*(D*C)+V^2*((D^2+C^2)/2+L^2))/(1-V^2)=
 (1+V)/(1-V)*((D+C)/2)^2+(1-V)/(1+V)*((D-C)/2)^2-L^2 :=
begin
 have a : 1-V≠0 := sub_ne_zero.mpr (ne.symm h),
 have c : 1+V≠0 := by intro z;apply k;linarith,
 have b : 1-V^2=(1+V)*(1-V) := by ring,
 rw [b],field_simp [a,c];ring
end

-- Derivatives of the three boundary terms with w=1/R, w'=alpha*w^2.
theorem dipole_primitives {p d w : ℝ→ℝ} {t A α : ℝ}
 (h : has_deriv_at p (d t) t) (hd : has_deriv_at d A t)
 (hw : has_deriv_at w (α*(w t)^2) t) :
 has_deriv_at (λ x,w x*(d x)^2) (2*A*(d t*w t)+α*(d t*w t)^2) t ∧
 has_deriv_at (λ x,(w x)^2*p x*d x)
   ((d t*w t)^2+A*(p t*(w t)^2)+2*α*(d t*w t)*(p t*(w t)^2)) t ∧
 has_deriv_at (λ x,(w x)^3*(p x)^2)
   (2*(d t*w t)*(p t*(w t)^2)+3*α*(p t*(w t)^2)^2) t :=
begin
 refine ⟨_,_,_⟩,
 {convert hw.mul (hd.pow 2) using 1;norm_num;ring},
 {convert ((hw.pow 2).mul h).mul hd using 1;norm_num;ring},
 {convert (hw.pow 3).mul (h.pow 2) using 1;norm_num;ring}
end

theorem pressure_is_bulk_plus_boundary (A H J α : ℝ) :
 (A+H+J/2)^2+(1-2*α)^2*J^2/4-(1-2*α)*(H+J)^2=
 A^2-(1-α)*H^2-(1-α)*(1-4*α)*J^2/2+
 ((2*A*H+α*H^2)+(H^2+A*J+2*α*H*J)+(α-1/2)*(2*H*J+3*α*J^2)) := by ring

theorem moving_energy_is_bulk_plus_boundary (A H J α : ℝ) :
 (A+H+J)*(A+H)+α*((H+J)^2+J^2/2)=
 A^2+((2*A*H+α*H^2)+(H^2+A*J+2*α*H*J)+(2*H*J+3*α*J^2)/2) := by ring

theorem integrated_surface_balance (T : ℝ) (p base boundary slope : ℝ→ℝ)
 (hs : ∀ t,p t=base t+slope t) (hb : ∀ t∈uIcc 0 T,has_deriv_at boundary (slope t) t)
 (endpoints : boundary T=boundary 0)
 (hi : interval_integrable base volume 0 T) (hj : interval_integrable slope volume 0 T) :
 (∫ t in (0:ℝ)..T,p t)=∫ t in (0:ℝ)..T,base t :=
begin
 have f := funext hs,
 rw [f,interval_integral.integral_add hi hj,interval_integral.integral_eq_sub_of_has_deriv_at hb hj,
     endpoints,sub_self,add_zero]
end

theorem stored_field_nonneg (p d w : ℝ) (hw : 0≤w) :
 0≤w*(d^2+w*p*d+w^2*p^2/2) :=
begin
 apply mul_nonneg hw,
 have h : d^2+w*p*d+w^2*p^2/2=(d+w*p/2)^2+(w*p/2)^2 := by ring,
 rw [h],exact add_nonneg (sq_nonneg _) (sq_nonneg _)
end

theorem dirichlet_pressure_bound (A H J c e z : ℝ) (hc : 0≤c) (he : 0≤e)
 (first : H≤z^2*A) (second : J≤z^4*A) :
 (1-c*z^2-e*z^4)*A≤A-c*H-e*J :=
by nlinarith [mul_le_mul_of_nonneg_left first hc,mul_le_mul_of_nonneg_left second he]

theorem early_dipole_energy (α A H J : ℝ) :
 (1-α)*(A-α*H-α*(1-4*α)*J/2)-
 α*(A-(1-α)*H-(1-α)*(1-4*α)*J/2)=(1-2*α)*A := by ring

theorem logarithmic_moments (f v a : ℝ) :
 (a-2*v+3*f/4)^2=
 a^2+(5/2)*v^2+(9/16)*f^2+(-4*a*v+(3/2)*(a*f+v^2)-3*v*f) ∧
 (v-3*f/2)^2=v^2+9*f^2/4-3*v*f := by split;ring

theorem pulse_polynomial (α f0 f1 f2 : ℝ) :
 α^4*(f2+5*f1/2+9*f0/16)-(1-α)*α^2*(f1+9*f0/4)-(1-α)*(1-4*α)*f0/2=
 α^4*f2+(5*α^4/2-(1-α)*α^2)*f1+
 (9*α^4/16-9*(1-α)*α^2/4-(1-α)*(1-4*α)/2)*f0 := by ring

theorem sine_fourier_moments :
 ((3/8:ℝ)^2+((1/2:ℝ)^2+(1/8:ℝ)^2)/2)=35/128 ∧
 ((1:ℝ)^2+(1/2:ℝ)^2)/2=5/8 ∧ ((2:ℝ)^2+2^2)/2=4 := by norm_num

theorem unique_positive_pulse_root (A B C x y : ℝ) (ha : 0<A) (hc : C<0)
 (hx : 0<x) (hy : 0<y) (hx0 : A*x^2+B*x+C=0) (hy0 : A*y^2+B*y+C=0) : x=y :=
begin
 have h : (x-y)*(A*(x+y)+B)=0 := by nlinarith,
 rcases mul_eq_zero.mp h with eq|sum,
 {linarith},
 {have k := mul_pos (mul_pos ha hx) hy,nlinarith [congr_arg (λ z:ℝ,z*x) sum]}
end
theorem dirichlet_twice (a b c lam f0 f1 f2 : ℝ) (ha : 0≤a)
 (hp : 0≤a*lam+b) (d1 : lam*f0≤f1) (d2 : lam*f1≤f2) :
 (a*lam^2+b*lam+c)*f0≤a*f2+b*f1+c*f0 :=
by nlinarith [mul_le_mul_of_nonneg_left d2 ha,mul_le_mul_of_nonneg_left d1 hp]

theorem clamped_integration (A B C F M L fourth second : ℝ)
 (by_parts_twice : fourth=F) (by_parts_once : second= -M)
 (euler : A*fourth-B*second+C*L=0) : A*F+B*M+C*L=0 := by {rw [by_parts_twice,by_parts_once] at euler,nlinarith}

theorem even_impulse_mode (a b c k h x z : ℝ)
 (osc : a*k^4+b*k^2+c=0) (hyp : a*h^4-b*h^2+c=0) :
 a*(k^4*x-h^4*z)-b*(-k^2*x-h^2*z)+c*(x-z)=0 :=
by linear_combination x*osc-z*hyp

theorem end_slope (k h si co sh ch : ℝ) (hc : co≠0) (hh : ch≠0) :
 -k*si-(co/ch)*h*sh=0 ↔ k*(si/co)+h*(sh/ch)=0 :=
begin
 have ident : -k*si-(co/ch)*h*sh= -co*(k*(si/co)+h*(sh/ch)) := by {field_simp [hh,hc];ring},
 rw [ident,mul_eq_zero],simp [hc]
end

theorem integrated_clamped_derivatives (T : ℝ) (f g h j k : ℝ→ℝ)
 (df : ∀ x∈uIcc 0 T,has_deriv_at f (g x) x) (dg : ∀ x∈uIcc 0 T,has_deriv_at g (h x) x)
 (dh : ∀ x∈uIcc 0 T,has_deriv_at h (j x) x) (dj : ∀ x∈uIcc 0 T,has_deriv_at j (k x) x)
 (f0 : f 0=0) (fT : f T=0) (g0 : g 0=0) (gT : g T=0)
 (ii : interval_integrable (λ x,(h x)^2) volume 0 T)
 (jj : interval_integrable (λ x,f x*k x-(h x)^2) volume 0 T) :
 (∫ x in (0:ℝ)..T,f x*k x)=∫ x in (0:ℝ)..T,(h x)^2 :=
begin
 apply integrated_surface_balance T (λ x,f x*k x) (λ x,(h x)^2) (λ x,f x*j x-g x*h x)
     (λ x,f x*k x-(h x)^2) (λ t,by ring) _ _ ii jj,
 {intros x hx,
  convert ((df x hx).mul (dj x hx)).sub ((dg x hx).mul (dh x hx)) using 1;ring},
 {simp [f0,fT,g0,gT]}
end
end maxwell

end horizon_pair_conversion
