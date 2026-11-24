import analysis.special_functions.exp_deriv
import analysis.special_functions.exponential
import analysis.special_functions.trigonometric.arctan
import analysis.special_functions.integrals
import analysis.normed_space.exponential
import data.real.sqrt
import tactic

noncomputable theory
open_locale big_operators interval
open measure_theory

namespace tidal_receipts

theorem mode_kinetic (m R s : ℝ) : (m*R^2/5)*s^2/2=m*R^2*s^2/10 := by ring
theorem kelvin_frequency (g m R rho w : ℝ) (hr : R≠0)
 (h : m=4*real.pi*rho*R^3/3) (hw : w=4*g*m/(5*R^3)) :
 w=16*real.pi*g*rho/15 := by rw [hw,h];field_simp;ring

theorem work_exchange (I v d f fd : ℝ) :
 (-I*v*f)+(-I*d*fd)+I*(v*f+d*fd)=0 := by ring

theorem torque_exchange (x y fx fy : ℝ) : (x*fy-y*fx)+(y*fx-x*fy)=0 := by ring

theorem response_energy (I w re im h : ℝ) (hh : h≠0) (hw : w≠0) :
 (h*w)*(I/(2*h*w)*(re^2+im^2))=I*(re^2+im^2)/2 := by field_simp;ring

theorem radiation_damping (g I w c : ℝ) (hp : c≠0) (hI : I≠0) (hw : w≠0) :
 (4*g*I^2*w^6/(10*c^5))/(I*w^2/2)=4*g*I*w^4/(5*c^5) := by field_simp;ring

theorem viscous_damping (nu m R : ℝ) (hm : m≠0) (hR : R≠0) :
 (2*nu*m)/(m*R^2/5)=10*nu/R^2 := by field_simp;ring

theorem near_trace (x k0 k1 : ℝ) :
 (2*x^2*k0+2*x*k1)+(-2*x^2*k0)+(-2*x*k1)=0 := by ring
theorem spectral_components (A B X : ℝ) :
 (3*B-A-(2*A-3*B))/2+X=3*B-3*A/2+X := by ring
theorem helicity_work (a b : ℝ) : (a+b)^2-(a-b)^2=4*a*b := by ring
theorem stf_factor (c m I b : ℝ) (hm : m≠0) (hb : b≠0) :
 c*m/b*(I/(m*b^2))=c*I/b^3 := by field_simp;ring

theorem encounter_shape (u : ℝ) : 12/(1+u^2)^2-11*u^2/(1+u^2)^3=
 1/(1+u^2)^2+11/(1+u^2)^3 :=
begin have hd : 1+u^2≠0 := by positivity,field_simp;ring,end

theorem burst_integral (i2 i3 : ℝ) (h2 : i2=real.pi/2) (h3 : i3=3*real.pi/8) :
 (8/15:ℝ)*(i2+11*i3)=37*real.pi/15 := by rw [h2,h3];ring

theorem residual_displacement (x gamma : ℝ) (p : ℂ) :
 (((x:ℂ)^2-complex.I*gamma)*p)+(complex.I*gamma*p)=(x:ℂ)^2*p := by ring

theorem ring_rate (g I w c d : ℝ) (hc : c≠0) (hd : d≠0) (hw : w≠0) :
 (5:ℝ)/(4*(w*d/c))*(4*g*I*w^4/(5*c^5))=g*I*w^3/(c^4*d) := by field_simp;ring

-- Coefficient of an entire displacement in the two independent Poisson populations.
theorem conserved_difference (bp bm n a b interference : ℝ)
 (h1 : bp=(n+1)*a+n*b-interference)
 (h2 : bm=(n+1)*b+n*a-interference) : bp-bm=a-b := by rw [h1,h2];ring

theorem paired_variance (bp bm n a b interference : ℝ)
 (h1 : bp=(n+1)*a+n*b-interference)
 (h2 : bm=(n+1)*b+n*a-interference) : bp+bm=(2*n+1)*(a+b)-2*interference :=
by rw [h1,h2];ring
theorem no_pair_false_flag (n : ℕ) : (n:ℤ)-n=0 := sub_self _

theorem finite_poisson_character (a : ℝ) (z : ℂ) :
 has_sum (λ n : ℕ, (complex.exp (-(a:ℂ))*(a:ℂ)^n/(n.factorial:ℂ))*z^n)
 (complex.exp ((a:ℂ)*(z-1))) :=
begin
 have h := exp_series_div_has_sum_exp ℂ ((a:ℂ)*z),
 rw [←complex.exp_eq_exp_ℂ] at h,
 convert h.mul_left (complex.exp (-(a:ℂ))) using 1,
 {funext n,rw [mul_pow],ring},
 {rw [←complex.exp_add],congr' 1,ring},
end

theorem thermal_geometric_difference (q : ℝ) (h1 : 1-q≠0) (h2 : 1+q≠0) :
 (1-q)^2/((1-q)*(1+q))=(1-q)/(1+q) := by field_simp;ring

theorem false_boundary_gibbs (n : ℝ) (hn : 0≤n) :
 (1-n/(1+n))/(1+n/(1+n))*(1+2*n/(1+n))=(1+3*n)/((1+n)*(1+2*n)) :=
begin have h : 1+n≠0 := by linarith,
 have hk : 1+2*n≠0 := by linarith,
 have h1 : 1-n/(1+n)=1/(1+n) := by field_simp;ring,
 have h2 : 1+n/(1+n)=(1+2*n)/(1+n) := by field_simp;ring,
 have h3 : 1+2*n/(1+n)=(1+3*n)/(1+n) := by field_simp;ring,
 rw [h1,h2,h3],field_simp; try {left};ring,end

theorem paired_loss_kernel (p x : ℝ) :
 (1-p)^2+p^2+2*p*(1-p)*x=1-2*p*(1-p)*(1-x) := by ring
theorem paired_loss_sum (n z : ℝ) (hn : 0≤n) (hz : 0≤z) :
 (1-n/(1+n))/(1-n/(1+n)*(1-z))=1/(1+n*z) :=
begin have hd : 1+n≠0 := by linarith,
 have hk : 0<1+n*z := by nlinarith only [mul_nonneg hn hz],
 have hr : 1-n/(1+n)*(1-z)=(1+n*z)/(1+n) := by field_simp;ring,
 rw [hr],field_simp;ring,end
theorem discrete_laplace_root (a r : ℝ) (h : r^2=1+4*a) :
 (1+2*a-r)*(1+2*a+r)=4*a^2 := by nlinarith only [h]
theorem symmetric_sides (p01 ratio : ℝ) : p01+p01*ratio+p01*ratio=p01*(1+2*ratio) := by ring

theorem witnessed_error {ι : Type*} (s : finset ι) (weight val : ι → ℝ)
 (m : ℝ) (hm : 1<m) (hpos : ∀ i∈s, 0≤weight i)
 (hw : ∀ i∈s, val i≤1) :
 (∑ i in s,weight i)*(m-1)^2≤∑ i in s,weight i*(val i-m)^2 :=
begin
 rw [finset.sum_mul],apply finset.sum_le_sum,intros i hi,
 apply mul_le_mul_of_nonneg_left _ (hpos i hi),
 have hA : 0≤m-1 := by linarith,
 have hB : m-1≤m-val i := by linarith [hw i hi],
 have hC:=mul_self_le_mul_self hA hB,
 nlinarith only [hC],
end

theorem field_mark_energy {A : Type*} [ring A] (H P Q : A)
 (hp : P*P=P) (hq : Q*Q=Q) (ht : P+Q=1)
 (h1 : P*H=H*P) (h2 : Q*H=H*Q) : P*H*P+Q*H*Q=H :=
calc P*H*P+Q*H*Q=H*(P*P+Q*Q) : by rw [h1,h2];noncomm_ring
 ... = H : by rw [hp,hq,ht,mul_one]

theorem independent_or_shared (l a b I : ℝ) :
 (l-a-b)^2/(2*I)-(l-a)^2/(2*I)-(l-b)^2/(2*I)+l^2/(2*I)=a*b/I :=
by by_cases h:I=0;[simp [h],field_simp];ring

theorem bounded_shared_square (l a b I : ℝ) (h : 0<I) : 0≤(l-a-b)^2/(2*I) := by positivity
theorem direct_force (q r : ℝ) (hr : r≠0) :
 has_deriv_at (λ x : ℝ,q/x^2) (-(2*q/r^3)) r :=
begin convert (has_deriv_at_const r q).div ((has_deriv_at_id r).pow 2) (pow_ne_zero _ hr) using 1;simp;field_simp;ring,end
theorem inverse_radius_clock (x : ℝ) :
 has_deriv_at real.arctan (1/(1+x^2)) x :=
by simpa [one_div] using real.has_deriv_at_arctan x
theorem recoil_time (a b : ℝ) :
 (∫ x in a..b, 1/(1+x^2))=real.arctan b-real.arctan a :=
begin
 have hc : continuous (λ x : ℝ,1/(1+x^2)) := continuous_const.div
  (continuous_const.add (continuous_id.pow _)) (λ x,by positivity),
 exact interval_integral.integral_eq_sub_of_has_deriv_at (λ x hx,inverse_radius_clock x)
   (hc.interval_integrable _ _),
end

theorem spin_axis (L j m : ℝ) (h : L≠0) :
 ((L+m)*(L+m+1)-L*(L+1)-j*(j+1))/(2*L)
 =m+(m*(m+1)-j*(j+1))/(2*L) := by field_simp;ring

theorem neutral_pair_blind (l r : ℤ) : (l-1)-(r-1)=l-r := by ring
theorem charge_recoil (d k : ℤ) : (d-2*k)+2*k=d := by ring
theorem geodesic_advanced (y : ℝ) (hy : 0<y) :
 (1/(1+1/y))/(1/y)=y^2/(y+1) :=
begin have ha : y+1≠0 := by linarith,
 have hn : y≠0 := ne_of_gt hy,
 have hb : 1+1/y=(y+1)/y := by field_simp [hn];ring,
 rw [hb],field_simp [hn,ha];ring,end

theorem reach_return (Ve Vh re rb : ℝ) :
 Ve+2*(rb-re)≤Vh ↔ 2*(rb-re)≤Vh-Ve := by split;intro h;linarith

theorem radial_tide (R r t : ℝ) (h : r^3=9*R*t^2/4) (hR : R≠0) (ht : t≠0) :
 R/r^3=4/(9*t^2) := by rw [h];field_simp;ring

theorem laplace_sine_kernel (t z a : ℝ) :
 real.exp (-(a+z)*t)=real.exp (-a*t)*real.exp (-z*t) :=
by rw [←real.exp_add];congr' 1;ring

theorem crossing_kernel_order (a b z : ℝ) (ha : 0<a) (hb : a≤b) (hz : 0≤z) :
 z*real.exp (-z)/(b^2+z^2)≤z*real.exp (-z)/(a^2+z^2) :=
begin
 have hden : 0<a^2+z^2 := add_pos_of_pos_of_nonneg (pow_pos ha _) (sq_nonneg _),
 apply div_le_div_of_le_left (mul_nonneg hz (real.exp_pos _).le) hden,
 have h:=mul_self_le_mul_self ha.le hb, nlinarith only [h],
end

theorem strain_tangent (u m t : ℝ) (hu : 0<u) (hm : 0≤m) (ht : 0≤t) :
 1/(u+m)-(t-m)/(u+m)^2≤1/(u+t) :=
begin
 have h1 : 0<u+m := by linarith,have h2 : 0<u+t := by linarith,
 have e : 1/(u+t)-(1/(u+m)-(t-m)/(u+m)^2)=(t-m)^2/((u+t)*(u+m)^2) := by field_simp [ne_of_gt h1,ne_of_gt h2];ring,
 have hpos : 0≤(t-m)^2/((u+t)*(u+m)^2) := by positivity,
 linarith only [e,hpos],
end

theorem escaped_clock (X Z y : ℝ) (hX : 0<X) (hy : y=4*real.pi*X*Z) :
 Z=y/(4*real.pi*X) :=
begin apply (eq_div_iff (ne_of_gt (show 0<4*real.pi*X,from mul_pos (mul_pos (by norm_num) real.pi_pos) hX))).mpr,rw [hy],ring,end

theorem emitting_radius (w z : ℝ) (hz : w=1-z) :
 w^2=(1-z)^2 := by rw [hz]

theorem light_budget (localE z : ℝ) : z*localE+(1-z)*localE=localE := by ring

theorem split_charge (k a b : ℤ) : (k+a)+b=k+(a+b) := add_assoc _ _ _
theorem subdivision_has_history : (0:ℤ)+2+(-2)=0 ∧ (0:ℤ)+2≠0 := by norm_num
theorem shot_coefficient (i : ℝ) (h : i=3*real.pi/8) :
 (9/4:ℝ)*i=27*real.pi/32 := by rw [h];ring
theorem independent_shot (a b ma mb varA varB cross : ℝ)
 (ha : a=ma^2+varA) (hb : b=mb^2+varB) (hc : cross=ma*mb) :
 a+b+2*cross-(ma+mb)^2=varA+varB := by rw [ha,hb,hc];ring

theorem evidence_odds (p q z odds : ℝ) (hq : q≠0) (hp : p=q*odds) (hz : z=p+q) (ho : 1+odds≠0) :
 q/z=1/(1+odds) :=
begin have hz' : z=q*(1+odds) := by rw [hz,hp];ring,
 rw [hz'],apply (div_eq_div_iff (mul_ne_zero hq ho) ho).2,ring,end

theorem mirrored_raw_weight (p q : ℝ) (k m : ℕ) :
 p^(m+k)*q^m*p^0*q^k=q^(m+k)*p^m*p^k := by simp [pow_add];ring

theorem two_exit_widths (escape loss survival : ℝ) (h : escape+loss≠0) :
 escape/(escape+loss)*(1-survival)+loss/(escape+loss)*(1-survival)+survival=1 :=
 by field_simp;ring

theorem thermal_probe_determinant (a eta n : ℝ) :
 (a-1)*(eta*a+1-eta+2*n-1)-eta*(a^2-1)=2*(a-1)*(n-eta) := by ring

theorem thermal_probe_crossing (a eta n : ℝ) (h : 1<a) :
 2*(a-1)*(n-eta)<0 ↔ n<eta :=
begin have hp : 0<2*(a-1) := by linarith,
 split,{intro h0,by_contra h',have hn : 0≤n-eta := by linarith,
 exact (not_le_of_gt h0) (mul_nonneg (le_of_lt hp) hn)},
 {intro hn,exact mul_neg_of_pos_of_neg hp (sub_neg.mpr hn)},end

theorem unused_port_threshold (e w : ℝ) (he : 1<e) :
 (1-w)/(e-1)<w ↔ 1/e<w :=
begin have hp : 0<e := by linarith,
 rw [div_lt_iff (sub_pos.mpr he),div_lt_iff hp],split; intro h; nlinarith,end

theorem downstream_filter (g w n : ℝ) (hg : 0<g) :
 g*((1-w)*n)<g*w ↔ (1-w)*n<w := mul_lt_mul_left hg

-- The same factorial and normalization factors occur for reflected Poisson means.
theorem mirrored_charge_distribution (p q : ℝ) (k : ℕ) (c : ℕ → ℝ) :
 (∑' m : ℕ, c m*(p^(m+k)*q^m))*q^k=(∑' m : ℕ, c m*(q^(m+k)*p^m))*p^k :=
begin rw [←tsum_mul_right,←tsum_mul_right],apply tsum_congr,
 intro m,simp only [pow_add],ring,end

theorem crossing_integral_order (a b : ℝ) (ha : 0<a) (hab : a≤b)
 (hi : integrable_on (λ z : ℝ, z*real.exp (-z)/(a^2+z^2)) (set.Ioi 0))
 (hj : integrable_on (λ z : ℝ, z*real.exp (-z)/(b^2+z^2)) (set.Ioi 0)) :
 (∫ z in set.Ioi (0:ℝ), z*real.exp (-z)/(b^2+z^2)) ≤
 ∫ z in set.Ioi (0:ℝ), z*real.exp (-z)/(a^2+z^2) :=
begin apply integral_mono_ae hj hi,
 refine (ae_restrict_iff' (measurable_set_Ioi : measurable_set (set.Ioi (0:ℝ)))).mpr (ae_of_all _ (λ z hz, _)),
 exact crossing_kernel_order a b z ha hab (le_of_lt hz),end

theorem spherical_tidal_norm (s : ℝ) : s^2+2*(-s/2)^2=3*s^2/2 := by ring
theorem relative_oscillator_energy (omega s v e : ℝ) (h : omega≠0) :
 omega^2*((s-e)^2+(v/omega)^2)=omega^2*(s-e)^2+v^2 := by field_simp;ring
theorem five_thermal_dark_modes (n : ℝ) (h : 0≤n) :
 1/(1+n)^5+5*n/(1+n)^6=(1+6*n)/(1+n)^6 :=
begin have hd : 1+n≠0 := by linarith,field_simp;ring,end
theorem crossing_clock_change (w v : ℝ) (h : v≠0) : (w/v)*v=w := div_mul_cancel _ h
theorem paired_energy_positive (a b I : ℝ) (h : 0<I) : 0≤(a-b)^2/(2*I) := by positivity
theorem intrinsic_pair_coupling (a b I : ℝ) (h : I≠0) :
 (a-b)^2/(2*I)-a^2/(2*I)-b^2/(2*I)= -(a*b/I) := by field_simp;ring
theorem port_balance (g h d : ℝ) (hg : 0<g) (hh : 0<h) :
 (4*g*h+(g-h)^2+4*d^2)/((g+h)^2+4*d^2)=1 :=
begin have hs : 0<g+h := by linarith,have hn : (g+h)^2+4*d^2≠0 := by positivity,
 field_simp;ring,end
theorem width_on_resonance (g h : ℝ) (hg : 0<g) (hh : 0<h) :
 4*g*h/(g+h)^2=1-((g-h)/(g+h))^2 :=
begin have hn : g+h≠0 := by linarith,field_simp;ring,end
theorem resonant_complement (x : ℝ) :
 1/(1+x^4)+x^4/(1+x^4)=1 :=
begin have hd : 1+x^4≠0 := by positivity,field_simp;ring,end
theorem tail_control (x : ℝ) : 0≤x^4-x^4/(1+x^4) ∧ x^4-x^4/(1+x^4)≤x^8 :=
begin have h : 0<1+x^4 := by positivity,
 have heq : x^4-x^4/(1+x^4)=x^8/(1+x^4) := by field_simp [ne_of_gt h];ring,
 rw [heq],split,{exact div_nonneg (by positivity) h.le},
 {apply (div_le_iff h).2,have hx : 0≤x^8*x^4 := by positivity,nlinarith only [hx]},end
theorem thermal_pair_collision (t : ℝ) (ht : 0≤t) (hl : t<1) :
 (1-t)^2/(1-t^2)=(1-t)/(1+t) :=
begin have h1 : 1-t≠0 := by linarith,have h2 : 1+t≠0 := by linarith,
 have h : 1-t^2=(1-t)*(1+t) := by ring,rw [h],field_simp;ring,end
theorem collision_lower_bound {ι : Type*} [decidable_eq ι] (s : finset ι)
 (p f : ι → ℝ) (same : ι → Prop) [decidable_pred same]
 (hp : ∀ i∈s, 0≤p i) (hf : ∀ i∈s, 0≤f i) (he : ∀ i∈s, same i → f i=1) :
 (∑ i in s, (if same i then p i else 0)) ≤ ∑ i in s, p i*f i :=
begin apply finset.sum_le_sum,intros i hi,by_cases h : same i,
 {simp [h,he i hi h]},{simp [h],exact mul_nonneg (hp i hi) (hf i hi)},end
theorem correlation_mixture (locked independent w : ℝ) (h : locked=1) :
 1-((1-w)*locked+w*independent)=w*(1-independent) := by rw [h];ring
theorem spin_difference_floor (j : ℝ) :
 4*j*(j+1)-(2*j)*(2*j+1)=2*j := by ring
theorem circle_ratio (n h m R rate : ℝ) (hh : h≠0) (hm : m≠0) (hr : R≠0) (hg : rate≠0) :
 ((h*n)^2/(2*m*R^2))/(h*rate/2)=h*n^2/(m*R^2*rate) := by field_simp;ring
theorem stable_recoil_trace {A : Type*} [ring A] (b q h : A) (hb : h*b=b*h) (hq : h*q=q*h) :
 h*(b*q)=(b*q)*h := by rw [←mul_assoc,hb,mul_assoc,hq,mul_assoc]
theorem odd_transfer_has_mismatch (a b k : ℤ) (h : a+b=2*k+1) : a-b≠0 :=
begin intro hz,omega,end
theorem open_flux (x : ℝ) (h : 0≤x) : 0≤4*x/(1+x)^2 ∧ 4*x/(1+x)^2≤1 :=
begin have hn : 0<1+x := by linarith,split,{positivity},
 {apply (div_le_iff (sq_pos_of_pos hn)).2,nlinarith only [sq_nonneg (1-x)]},end
theorem closed_window (e minimum d : ℝ) (he : e<minimum) (hd : minimum≤d) : e-d<0 := by linarith
end tidal_receipts
