import analysis.special_functions.trigonometric.complex
import analysis.special_functions.gaussian
import analysis.special_functions.integrals
import tactic

noncomputable theory
open_locale big_operators real interval
open measure_theory set interval_integral

namespace visible_body_flux

theorem focusing_flux (kap theta thetad flux G : ℝ) (hg : G≠0)
 (e : thetad=kap*theta-8*real.pi*G*flux) :
 (kap*theta-thetad)/(8*real.pi*G)=flux :=
by rw [e];field_simp [hg,ne_of_gt real.pi_pos];ring

theorem boost_phase (area kap energy time G h : ℝ) (hg : G≠0) (hh : h≠0)
 (he : kap*area=8*real.pi*G*energy) :
 area*(kap*time)/(8*real.pi*G*h)=energy*time/h :=
begin
 calc area*(kap*time)/(8*real.pi*G*h)=(kap*area)*time/(8*real.pi*G*h) : by ring
 ... = _ : by rw [he];field_simp [hg,hh,ne_of_gt real.pi_pos];ring
end

theorem partition_coefficient (n g : ℝ) (hg : g^2≤n^2) : 2*n≤2*(n+n^2-g^2) := by linarith

theorem paired_determinant (n g u v : ℝ) (h : u^2+v^2=1) :
 (1+n*(1-u))^2+(n*v)^2-g^2*((1-u)^2+v^2)=1+2*(n+n^2-g^2)*(1-u) :=
begin
 calc (1+n*(1-u))^2+(n*v)^2-g^2*((1-u)^2+v^2)
 = 1+2*(n+n^2-g^2)*(1-u)+(n^2-g^2)*((u^2+v^2)-1) : by ring
 ... = _ : by rw [h];ring
end

theorem chord_lower (y : ℝ) (hy : 0≤y) (hp : y≤real.pi) :
 2*(y/real.pi)^2 ≤ 1-real.cos y :=
begin
 have a := real.mul_le_sin (show 0≤y/2,by linarith) (show y/2≤real.pi/2,by linarith),
 have b : (y/real.pi)≤real.sin (y/2) :=
 calc y/real.pi=(2/real.pi)*(y/2) : by ring
 ... ≤ _ : a,
 have hsq := pow_le_pow_of_le_left (div_nonneg hy (le_of_lt real.pi_pos)) b 2,
 have hc := real.cos_two_mul (y/2),
 have ht : 2*(y/2)=y := by ring,
 rw [ht] at hc,
 nlinarith [real.sin_sq_add_cos_sq (y/2)]
end

theorem lower_log (x : ℝ) (hx : 0≤x) : x/(1+x)≤real.log (1+x) :=
begin
 have h : 0<1+x := by linarith,
 have hi := real.log_le_sub_one_of_pos (inv_pos.mpr h),
 rw [real.log_inv] at hi,
 have h' : x/(1+x)=1-(1+x)⁻¹ := by field_simp [ne_of_gt h];ring,
 rw [h'],linarith
end

theorem bounded_mode (x cap : ℝ) (hx : 0≤x) (hc : x≤cap) :
 x/(1+cap)≤real.log (1+x) :=
begin apply le_trans _ (lower_log x hx),
 exact div_le_div_of_le_left hx (by linarith) (by linarith) end

theorem spectral_product {ι : Type*} (s : finset ι) (p h : ι→ℝ)
 (hp : ∀ i∈s, 0≤p i) (hh : ∀ i∈s,p i≤real.exp (-h i)) :
 (∏i in s,p i)≤real.exp (-(∑i in s,h i)) :=
begin
 calc (∏i in s,p i) ≤ ∏i in s,real.exp (-h i) : finset.prod_le_prod hp hh
 ... = _ : by rw [←real.exp_sum,finset.sum_neg_distrib]
end

theorem gaussian_half (b : ℝ) (hb : 0<b) :
 (∫x:ℝ in set.Ioi 0,real.exp (-b*x^2))=real.sqrt (real.pi/b)/2 :=
begin
  exact integral_gaussian_Ioi b
end

theorem clock_triangle (T d : ℝ) (ht : 0<T) (hd : 0≤d) (hh : d≤T) :
 0≤2/T*(1-d/T) ∧ 2/T*(1-d/T)≤2/T :=
begin have h2 : 0≤2/T := by positivity, have h3 : 0≤d/T := div_nonneg hd ht.le,
 have h4 : d/T≤1 := (div_le_one ht).mpr hh,
 exact ⟨mul_nonneg h2 (by linarith), by simpa using
 (mul_le_mul_of_nonneg_left (show 1-d/T≤1,by linarith) h2)⟩ end

theorem finite_clock_partition (p : ℕ→ℝ) (pts : finset ℕ) (amp : ℕ→ℝ)
 (C : ℝ) (h : ∀i∈pts,amp i ≤ C) (hp : ∀i∈pts,0≤p i)
 (hn : ∑i in pts,p i=1) : (∑i in pts,p i*amp i)≤C :=
begin calc (∑i in pts,p i*amp i) ≤ ∑i in pts,p i*C :
 finset.sum_le_sum (λ i hi,mul_le_mul_of_nonneg_left (h i hi) (hp i hi))
 ... = C : by rw [←finset.sum_mul,hn,one_mul] end

theorem timing_prefix (E D t a b : ℝ) :
 E/D*(t-a)-E/D*(t-b)=E/D*(b-a) := by ring

theorem proper_window (E D h s : ℝ) (hD : D≠0) (hE : E≠0) (hs : s≠0) :
 2*real.pi*h*D/(E*s*(D/4))=8*real.pi*h/(E*s) := by field_simp;ring

theorem nearby_ray (s u : ℝ) (hd : 1+u≠0) :
 -(u*(s-s*u/(1+u)))= -(s*u/(1+u)) := by field_simp [hd];ring

theorem local_charge_locked (a b d : ℝ) (h : a=b+d) : a-b-d=0 := by linarith

theorem thermal_threshold (C p count : ℝ) (hc : 0≤C) (hp : 0<p) (hn : 0<count)
 (margin : C^2 ≤ p^2*count) : C/real.sqrt count≤p :=
begin
 have hs := real.sqrt_pos.mpr hn,
 apply (div_le_iff hs).mpr,
 have hp' : 0≤p*real.sqrt count := mul_nonneg hp.le hs.le,
 have sq : C^2≤(p*real.sqrt count)^2 := by rw [mul_pow,real.sq_sqrt hn.le];exact margin,
 nlinarith [sq_nonneg (C-p*real.sqrt count)]
end

theorem packet_spread (x t m p h : ℝ) (hm : 0<m) (hx : 0≤x) (hp : 0≤p)
 (ht : 0≤t) (hu : h/2≤x*p) : h*t/m≤x^2+((t/m)*p)^2 :=
begin
 have hh := mul_le_mul_of_nonneg_right hu (div_nonneg ht hm.le),
 have hs := sq_nonneg (x-(t/m)*p),
 calc h*t/m=2*(h/2*(t/m)) : by ring
 ... ≤ 2*(x*p*(t/m)) : by linarith only [hh]
 ... ≤ _ : by nlinarith only [hs]
end

theorem equal_seed_record (z : ℤ) :
 (if z=z then (1:ℝ) else 0)=1 := by simp

theorem diagonal_purity {ι : Type*} [decidable_eq ι] (s : finset ι)
 (f : ι→ι→ℝ) (hf : ∀i j,0≤f i j) :
 (∑i in s,f i i)≤∑i in s,∑j in s,f i j :=
begin apply finset.sum_le_sum, intros i hi,
 exact finset.single_le_sum (λ j hj,hf i j) hi end

theorem aberration_rewrite (beta C x : ℝ) (h : 1-beta≠0)
 (hc : 1+C≠0) (hx : 1-C^2=x*(1-beta^2)) :
 1-beta*C=(1-beta)*(1+beta*x*(1+beta)/(1+C)) :=
begin
 field_simp [hc],
 apply sub_eq_zero.mp,
 calc (1-beta*C)*(1+C)-(1-beta)*(1+C+beta*x*(1+beta))
    = beta*((1-C^2)-x*(1-beta^2)) : by ring
 ... = 0 : by rw [hx];ring
end

theorem speed_factor (beta : ℝ) (hb : 0<beta) : 4≤(1+beta)^2/beta :=
begin apply (le_div_iff hb).mpr,nlinarith [sq_nonneg (1-beta)] end

theorem spin_cancellation (r a M x : ℝ) (hr : r≠0) (hm : M≠0)
 (hd : x^2+(a/r)^2≠0) (hp : r^2+a^2=2*M*r) :
 r/(2*M)*((1+(a/r)^2)/(x^2+(a/r)^2))=1/(x^2+(a/r)^2) :=
begin
 have e : r/(2*M)*(1+(a/r)^2)=1,
 { calc r/(2*M)*(1+(a/r)^2)=(r^2+a^2)/(2*M*r) : by field_simp [hr,hm];ring
   ... = _ : by rw [hp,div_self];exact mul_ne_zero (mul_ne_zero (by norm_num) hm) hr },
 rw [←mul_div_assoc,e]
end

theorem finite_clock_pair_sum (n : ℕ) (diag off : ℝ) (hn : n≠0) :
 ((n:ℝ)*diag+(n:ℝ)*off)/(n:ℝ)^2=diag/(n:ℝ)+off/(n:ℝ) :=
begin
 have h : (n:ℝ)≠0 := by exact_mod_cast hn,
 rw [←add_div,←mul_add,pow_two],
 exact mul_div_mul_left _ _ h
end

theorem neutral_recoil (a b n : ℤ) : (a+n)+(b-n)=a+b := by ring

theorem angle_difference (x y : ℝ) :
 ((1+real.cos x)/2-(1+real.cos y)/2) =
 -real.sin ((x+y)/2)*real.sin ((x-y)/2) :=
begin
 have a : (x+y)/2+(x-y)/2=x := by ring,
 have b : (x+y)/2-(x-y)/2=y := by ring,
 have c := real.cos_add ((x+y)/2) ((x-y)/2),
 have d := real.cos_sub ((x+y)/2) ((x-y)/2),
 rw [a] at c, rw [b] at d, linarith only [c,d]
end

theorem scaled_sine (u : ℝ) (hu : 0≤u) (hp : u≤real.pi/2) :
 (2/real.pi)*u≤real.sin u := real.mul_le_sin hu hp

theorem finite_band_envelope (u s t : ℝ) (hu : 4≤u)
 (hs : -1≤s) (ht : t≤1) : (1/2:ℝ)≤1-(t-s)/u :=
begin
 have h : t-s≤u/2 := by linarith,
 have pos : 0<u := by linarith,
 have c : (t-s)/u≤1/2 := (div_le_iff pos).mpr (by linarith),
 linarith
end

theorem circular_envelope (f : ℝ→ℝ) (a : ℝ) (ha : 0<a) (hb : a≤1)
 (hf : continuous f) (hleft : ∀ x∈set.Icc (0:ℝ) a,f x≤1)
 (hright : ∀x∈set.Icc a (1:ℝ),f x≤a*x⁻¹) :
 (∫ x in (0:ℝ)..1,f x) ≤ a*(1-real.log a) :=
begin
 have hj : (0:ℝ)∉set.uIcc a 1 := not_mem_uIcc_of_lt ha zero_lt_one,
 have hinv : interval_integrable (λ x:ℝ,x⁻¹) volume a 1 :=
  (continuous_on_inv₀.mono (set.subset_compl_singleton_iff.mpr hj)).interval_integrable,
 have hl := interval_integral.integral_mono_on ha.le (hf.interval_integrable _ _)
  (interval_integrable_const : interval_integrable (λ _:ℝ,(1:ℝ)) volume 0 a) hleft,
 have hr := interval_integral.integral_mono_on hb (hf.interval_integrable _ _) (hinv.const_mul a) hright,
 rw [←interval_integral.integral_add_adjacent_intervals (hf.interval_integrable 0 a)
  (hf.interval_integrable a 1)],
 calc (∫ x in (0:ℝ)..a,f x)+(∫ x in a..1,f x)
   ≤ (∫ x in (0:ℝ)..a,(1:ℝ))+(∫ x in a..1,a*x⁻¹) : add_le_add hl hr
 ... = a*(1-real.log a) : by
     rw [interval_integral.integral_const_mul,integral_inv_of_pos ha zero_lt_one,
         one_div,real.log_inv,interval_integral.integral_const];simp;ring,
 all_goals {apply_instance}
end

theorem broadened_bound (small error bound rate : ℝ) (h : small≤bound)
 (q : error≤rate) : small+error≤bound+rate := add_le_add h q

theorem circle_gap_margin (p flat error : ℝ) (hp : 0≤p)
 (h : real.sqrt p≤real.sqrt flat+error) (margin : real.sqrt flat+error≤1/10) :
 p≤1/100 :=
begin
 have k : real.sqrt p≤1/10 := h.trans margin,
 have s := pow_le_pow_of_le_left (real.sqrt_nonneg p) k 2,
 rw [real.sq_sqrt hp] at s, norm_num at s ⊢, linarith
end

theorem positive_block_cost (a b n : ℤ) (ha : 0≤a+n) (hb : 0≤b-n) :
 abs (a+n)+abs (b-n)=a+b := by rw [abs_of_nonneg ha,abs_of_nonneg hb];ring

theorem path_hopping (x d : ℝ) :
 (real.sin (x+d)+real.sin (x-d))/2=real.cos d*real.sin x :=
by rw [real.sin_add,real.sin_sub];ring

theorem path_mean (q : ℕ) (v : ℝ) (hq : 0<q) :
 (∑i:fin q,∑j:fin q,(if j=i then (1:ℝ) else v))/(q:ℝ)^2
 =1/(q:ℝ)+(1-1/(q:ℝ))*v :=
begin
 have hn : (q:ℝ)≠0 := by exact_mod_cast (ne_of_gt hq),
 have row : ∀ i:fin q,(∑j:fin q,(if j=i then (1:ℝ) else v))=(q:ℝ)*v+(1-v),
 { intro i,
   have term : ∀j:fin q,(if j=i then (1:ℝ) else v)=v+(if i=j then 1-v else 0),
   { intro j, by_cases h : j=i,
     { subst j,simp }, { simp [h,ne.symm h] } },
   simp_rw [term], rw [finset.sum_add_distrib], simp [nsmul_eq_mul] },
 simp_rw [row],simp only [finset.sum_const,finset.card_univ,fintype.card_fin,nsmul_eq_mul],
 field_simp [hn];ring
end

theorem positive_block_radial (q : ℕ) (v : ℝ) (hq : 0<q) (F : fin q→fin q→ℝ)
 (d : ∀i,F i i=1) (lo : ∀i j,0≤F i j) (hi : ∀i j,j≠i→F i j≤v) :
 1/(q:ℝ)≤(∑i:fin q,∑j:fin q,F i j)/(q:ℝ)^2 ∧
 (∑i:fin q,∑j:fin q,F i j)/(q:ℝ)^2≤1/(q:ℝ)+(1-1/(q:ℝ))*v :=
begin
 have a : (∑i:fin q,∑j:fin q,(if j=i then (1:ℝ) else 0))≤∑i:fin q,∑j:fin q,F i j,
 { apply finset.sum_le_sum, intros i h1,apply finset.sum_le_sum,intros j h2,
   by_cases h : j=i, {subst j,simp [d]}, {simp [h,lo i j]} },
 have b : (∑i:fin q,∑j:fin q,F i j)≤∑i:fin q,∑j:fin q,(if j=i then (1:ℝ) else v),
 { apply finset.sum_le_sum, intros i h1,apply finset.sum_le_sum,intros j h2,
   by_cases h : j=i, {subst j,simp [d]}, {simp [h,hi i j h]} },
 have low := div_le_div_of_le (sq_nonneg (q:ℝ)) a,
 have up := div_le_div_of_le (sq_nonneg (q:ℝ)) b,
 rw [path_mean q 0 hq] at low, rw [path_mean q v hq] at up,
 simp only [mul_zero,add_zero] at low,exact ⟨low,up⟩
end

theorem capacity_floor (q : ℕ) (hq : 0<q) (p : ℝ)
 (lo : 1/(q:ℝ)≤p) (want : p<1/100) : 100<q :=
begin
 have pos : 0<(q:ℝ) := by exact_mod_cast hq,
 have frac := (div_lt_iff pos).mp (lt_of_le_of_lt lo want),
 have lim : (100:ℝ)<(q:ℝ) := by linarith,
 exact_mod_cast lim
end

end visible_body_flux
