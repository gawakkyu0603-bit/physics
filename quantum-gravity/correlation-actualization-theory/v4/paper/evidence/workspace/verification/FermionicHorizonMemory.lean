import tactic
import analysis.special_functions.exp
import data.real.pi.bounds
import analysis.inner_product_space.basic
import analysis.special_functions.integrals

noncomputable theory
open set measure_theory
open_locale interval complex_conjugate
namespace fermionic_horizon_memory

-- The spectral weights and the cylinder Fourier multiplier are inputs from
-- the stated QFT.  These identities connect them to the retarded port.
theorem spectral_subtraction (p t : ℝ) (h : p^2+t^2 ≠ 0) :
  1 - t^2/(p^2+t^2) = p^2/(p^2+t^2) :=
by {field_simp [h];ring}

theorem static_contact (a h z l k : ℝ) (hl : l≠0) (g : a=2*z/l)
  (s : 2*h=l*k-1) : a*(1/2+h)=z*k :=
by {rw [g], field_simp [hl], linear_combination 2*z*s}

theorem angular_step (k l p v : ℝ) (hk : k≠0) :
  k*((p^2+(v*l)^2)/k)=p^2+(v*l)^2 := by {field_simp [hk];ring}

def refl (p k : ℝ) := (p-k)/(p+k)
theorem prompt_and_echo (p z q : ℝ) (hp : p≠0) (hq : q≠1)
  (hz : 1+z≠0) (hd : 1+z-(1-z)*q≠0) :
  refl p (z*p*((1+q)/(1-q))) =
    (((1-z)/(1+z))-q)/(1-((1-z)/(1+z))*q) :=
begin
  have hq' : 1-q ≠ 0 := sub_ne_zero.mpr (ne.symm hq),
  have hr : 1 - (1-z)/(1+z)*q ≠ 0,
  { intro h, field_simp [hz] at h, apply hd, linear_combination h },
  have hk : p+z*p*((1+q)/(1-q)) ≠ 0,
  { intro h, field_simp [hq'] at h, apply hd,
    have hh : p*(1+z-(1-z)*q)=0 := by linear_combination h,
    exact (mul_eq_zero.mp hh).resolve_left hp },
  unfold refl, apply (div_eq_div_iff hk hr).2, field_simp [hq',hz]; ring
end

theorem pure_delay (q : ℝ) : ((0:ℝ)-q)/(1-0*q) = -q := by simp

theorem echo_tail_energy (r t : ℝ) (h : r^2≠1)
  (geom : (1-r^2)*t=1) : r^2+(1-r^2)^2*t=1 :=
by nlinarith [congr_arg (λ x : ℝ, (1-r^2)*x) geom]

theorem thermal_reflection (a b : ℝ) (ha : 0<a) :
 ((1-a)^2+b^2)/((1+a)^2+b^2) ≥ (1-a)^2/(1+a)^2 :=
begin
  have h : 0 < (1+a)^2 := sq_pos_of_pos (by linarith),
  have h' : 0 < (1+a)^2+b^2 := by nlinarith [sq_nonneg b],
  rw [ge_iff_le,div_le_div_iff h h'],
  nlinarith [mul_nonneg ha.le (sq_nonneg b)]
end

theorem thermal_pauli (u : ℝ) (h : 0<u) :
 ((1-(u-1)/(u+1))/(1+(u-1)/(u+1)))^2=1/u^2 :=
begin
 have h1 : u+1≠0 := by linarith,
 have h2 : 1+(u-1)/(u+1)≠0,
 {intro H, field_simp at H, linarith},
 have hu : u≠0 := ne_of_gt h,
 have hh : (1-(u-1)/(u+1))/(1+(u-1)/(u+1))=1/u,
 {apply (div_eq_div_iff h2 hu).2,field_simp [h1];ring},
 rw [hh,div_pow,one_pow]
end

theorem thermal_emission (b a : ℝ) (hb : 0<b) (h1 : b<1)
  (ha : a≤1-b) : a/(1/b-1)≤b :=
begin
 have h' : 0 < 1/b-1 := by {rw [sub_pos,lt_div_iff hb],linarith},
 apply (div_le_iff h').2,
 have hb' : b*(1/b-1)=1-b := by {field_simp [ne_of_gt hb];ring},
 rwa [hb']
end

theorem incoming_clock (e k f : ℝ) (he : e+k ≠ 0) (hf : f ≠ 0)
  (shell : e^2-k^2=f) : (e-k)/f=1/(e+k) :=
by {field_simp,nlinarith}

theorem proper_clock (y : ℝ) :
 has_deriv_at (λ x : ℝ, (2/3:ℝ)*x^3) (2*y^2) y :=
begin
 convert ((has_deriv_at_pow 3 y).const_mul (2/3:ℝ)) using 1; norm_num; ring
end

def phase (y : ℝ) := -2*(y-1)
theorem phase_delay (a b d : ℝ) :
  phase b = phase a+d ↔ b=a-d/2 := by {unfold phase,split;intro h;linarith}

theorem missed_horizon (a b d : ℝ) (hab : 1≤b)
  (slow : 2*(a-1)<d) : phase b≠phase a+d :=
by {intro h, have := (phase_delay a b d).1 h,linarith}

theorem photon_sphere_too_late (y d : ℝ) (hy : y^2=3/2) (hd : real.pi≤d) :
  2*(y-1)<d := by nlinarith [real.pi_gt_three,sq_nonneg (y-5/4)]

theorem earlier_radius (y d : ℝ) (h : phase 1=phase y+d) :
  y^2=(1+d/2)^2 := by {have := (phase_delay y 1 d).1 h,congr' 1,linarith}

theorem support_window (a b d e : ℝ) (hb : 1≤b) (he : b≤1+e)
  (h : phase b=phase a+d) :
  2*(a-1-e)≤d ∧ d≤2*(a-1) :=
by {have := (phase_delay a b d).1 h,constructor;linarith}

theorem disjoint_gates (a b e d : ℝ) (h : a+e<b)
  (ha : d≤2*(a-1)) : ¬ 2*(b-1-e)≤d := by linarith

def doppler (y a s : ℝ) := a^3*(y-1)/(s*(a+1)*y^3)
theorem redshift_ratio (y a s : ℝ) (hy : 0<y) (ha : 0<a)
  (h1 : y≠1) (hs : 0<s) :
  (a^3/(a+1))/(s*(y^3/(y-1)))=doppler y a s :=
by {unfold doppler,field_simp,ring}

-- The derivative of the affine earlier radius is 1/s.  The log transfer
-- includes the Schwarzschild clock, the matter delay and both radius factors.
def log_transfer (y a s : ℝ) := 3*real.log a + real.log (y-1) -
  real.log (a+1) - 3*real.log y - real.log s

theorem transfer_deriv (y a s : ℝ) (hy : 1<y) (ha : 0<a) (hs : 0<s) :
 has_deriv_at (λ x : ℝ, log_transfer x (a+(x-y)/s) s)
 ((3/a-1/(a+1))/s+1/(y-1)-3/y) y :=
begin
 let b := (has_deriv_at_const y a).add (((has_deriv_at_id y).sub_const y).div_const s),
 have la := b.log (show a+(y-y)/s ≠ 0, by simpa using (ne_of_gt ha)),
 have lb := (b.add_const 1).log (show a+(y-y)/s+1≠0, by {simp,linarith}),
 have ly := (has_deriv_at_id y).log (ne_of_gt (by linarith : 0<y)),
 have lm := ((has_deriv_at_id y).sub_const 1).log (show y-1≠0, by linarith),
 unfold log_transfer,
 convert (((((la.const_mul 3).add lm).sub lb).sub (ly.const_mul 3)).sub_const (real.log s)) using 1;
 simp [id.def]; try {ring}; try {field_simp [ne_of_gt hs,ne_of_gt ha,show a+1≠0,by linarith]; ring}
end

def peel (y a s : ℝ) :=
  (1+(y-1)*((3/a-1/(a+1))/s-3/y))/(2*y^3)

theorem peeling (y a s : ℝ) (hy : y≠1) (h0 : y≠0) :
  (y-1)/(2*y^3)*((3/a-1/(a+1))/s+1/(y-1)-3/y) = peel y a s :=
begin
  unfold peel, have hd : y-1≠0 := sub_ne_zero.mpr hy,
  generalize hc : (3/a-1/(a+1))/s = c, field_simp [hd,h0]; ring
end
theorem hawking_endpoint (a s : ℝ) : peel 1 a s=1/2 := by {unfold peel,norm_num}

theorem mobile_tip (a b wi wm wo : ℝ) (hb : 1+b≠0)
  (in_ray : wm-wi=a-b*wm) (out_ray : wo-wm=a-b*wm) :
  wo=2*a/(1+b)+(1-b)/(1+b)*wi :=
by {field_simp,linear_combination (1-b)*in_ray+(1+b)*out_ray}

theorem tick_compression (s b a a' : ℝ) :
 (b+s*a')-(b+s*a)=s*(a'-a) := by ring

theorem energy_momentum_return (m k e : ℝ) (hm : 0<m) (hk : 0<k) (he : 0<e) :
  (m/k-m^2/(m*k+2*e))/2=e/(k^2*(1+2*e/(m*k))) :=
begin
 have h : 0<m*k+2*e := by nlinarith [mul_pos hm hk],
 have h' : 0<1+2*e/(m*k) := by positivity,
 field_simp [ne_of_gt hm,ne_of_gt hk,ne_of_gt h,ne_of_gt h'];ring
end

theorem paid_boost (m e k t : ℝ) (hm : 0<m) (he : 0<e) (hk : 0<k)
  (ht : 0<t) (quality : 2*e*(1-t)≤t*(m*k)) :
  e*(1-t)*(1-k)^2/(t*k^2)≤m*((1+k^2)/(2*k)-1) :=
begin
 have hden : 0<t*k^2 := by positivity,
 have hk' : (2:ℝ)*k ≠ 0 := by positivity,
 have hcore : (1+k^2)/(2*k)-1=(1-k)^2/(2*k),
 {apply (eq_div_iff hk').2,rw [sub_mul,div_mul_cancel _ hk'],ring},
 have h : m*((1+k^2)/(2*k)-1)=m*(1-k)^2/(2*k) := by {rw [hcore,mul_div_assoc']}, 
 rw [h,div_le_div_iff hden (by positivity : 0<2*k)],
 nlinarith [mul_nonneg (sub_nonneg.mpr quality) (mul_nonneg hk.le (sq_nonneg (1-k)))]
end

theorem timelike_retreat (r d speed : ℝ) (hr : 0<r+d)
  (timelike : 2*speed<d/(r+d)) : 2*speed*r < d*(1-2*speed) :=
by {have h := (lt_div_iff hr).1 timelike,nlinarith}

-- A null trigger from the mouth reaches a pinned tip before the later packet.
def ret (q l a i : ℝ) := q+2*l+a*(i-q)/(a+i-q)
def red (q a i : ℝ) := a/(a+i-q)

theorem ret_clock (q l a i : ℝ) (h : a+i-q ≠ 0) :
  has_deriv_at (ret q l a) ((red q a i)^2) i :=
begin
 have d := (((has_deriv_at_id i).sub_const q).const_mul a).div
   (((has_deriv_at_id i).const_add a).sub_const q) h,
 unfold ret red, convert d.const_add (q+2*l) using 1; simp [id.def]; field_simp [h];ring
end

theorem unpin_time (q l a : ℝ) : ret q l a q=q+2*l :=
by {unfold ret,simp}

theorem pulse_compression (q l a i j : ℝ) (hi : a+i-q≠0) (hj : a+j-q≠0) :
  ret q l a j-ret q l a i=(j-i)*red q a i*red q a j :=
by {unfold ret red,field_simp [hi,hj];ring}

theorem rational_null_map (q l a i : ℝ) (hi : a+i-q≠0) :
  (q+2*l+a-ret q l a i)*(a+i-q)=a^2 :=
by {unfold ret,field_simp [hi];ring}

theorem tip_work (a l i o q : ℝ) (h : o=ret q l a i) (hi : a+i-q≠0) (ha : a≠0) :
  l-(o-i)/2=a*((red q a i+1/red q a i)/2-1) :=
begin
 rw [h],unfold ret red,field_simp [hi,ha];ring
end

theorem riccati_force (m k dk tension flux : ℝ) (hk : k≠0)
  (balance : m/k^2*dk= -tension+2*flux/k^2) :
  m*dk= -tension*k^2+2*flux :=
by {field_simp [hk] at balance,linear_combination balance}

theorem impulse_integral (m tension : ℝ) (k o energy : ℝ → ℝ) (i dk do' f : ℝ)
  (hk : has_deriv_at k dk i) (ho : has_deriv_at o do' i)
  (he : has_deriv_at energy f i) (h : m*dk+tension*do'=2*f) :
  has_deriv_at (λ t, m*k t+tension*o t-2*energy t) 0 i :=
begin
 convert ((hk.const_mul m).add (ho.const_mul tension)).sub (he.const_mul 2) using 1,
 linarith
end

theorem delay_bound (m tension energy k k0 o base : ℝ) (hm : 0≤m)
  (ht : 0<tension) (hk : k0≤k)
  (budget : m*(k-k0)+tension*(o-base)=2*energy) :
  o-base≤2*energy/tension :=
by {apply (le_div_iff ht).2,nlinarith [mul_nonneg hm (sub_nonneg.mpr hk)]}

theorem return_before_cut (o base cap e t : ℝ) (ht : 0<t)
  (shift : o-base≤2*e/t) (gap : 2*e<t*(cap-base)) : o<cap :=
by {have := (div_lt_iff ht).2 (show 2*e<(cap-base)*t,by nlinarith),linarith}

theorem schwarzian_mobius (c d : ℝ) (hc : c≠0) (hd : d≠0) :
 ((6*c/d^4)/(c/d^2))-(3/2:ℝ)*((2*c/d^3)/(c/d^2))^2=0 :=
by {field_simp [hc,hd];ring}

-- Comparison with the unforced motion. H is a primitive of (k+k0)/a.
theorem integrated_nonnegative (f g : ℝ → ℝ) (a b : ℝ) (hab : a≤b)
 (hder : ∀ t∈uIcc a b, has_deriv_at f (g t) t)
 (hi : interval_integrable g volume a b) (hg : ∀ t∈Icc a b, 0≤g t) :
 f a ≤ f b :=
begin
 have eqn := interval_integral.integral_eq_sub_of_has_deriv_at hder hi,
 have pos := interval_integral.integral_mono_on hab
   (interval_integrable_const : interval_integrable (λ _:ℝ,(0:ℝ)) volume a b) hi hg,
 simp at pos, linarith
end

theorem positive_load_comparison (delta primitive h b : ℝ → ℝ) (i j : ℝ)
 (hij : i≤j) (initial : delta i=0)
 (hh : ∀ x∈uIcc i j, has_deriv_at primitive (h x) x)
 (hd : ∀ x∈uIcc i j, has_deriv_at delta (b x-h x*delta x) x)
 (source : ∀ x∈Icc i j, 0≤b x)
 (integrable : interval_integrable (λ x, real.exp (primitive x)*b x) volume i j) :
 0≤delta j :=
begin
 have prod : ∀ x∈uIcc i j, has_deriv_at (λ t, real.exp (primitive t)*delta t)
                    (real.exp (primitive x)*b x) x,
 { intros x hx, convert ((hh x hx).exp).mul (hd x hx) using 1,ring },
 have order := integrated_nonnegative _ _ i j hij prod integrable
    (λ x hx,mul_nonneg (real.exp_pos _).le (source x hx)),
 change real.exp (primitive i)*delta i ≤ real.exp (primitive j)*delta j at order,
 rw [initial,mul_zero] at order,
 exact nonneg_of_mul_nonneg_right order (real.exp_pos _)
end

theorem relative_return_order (delta g k k0 : ℝ → ℝ) (i j : ℝ) (hij : i≤j)
 (initial : delta i=0)
 (der : ∀ t∈uIcc i j, has_deriv_at delta (g t) t)
 (continuous_force : interval_integrable g volume i j)
 (rate : ∀ t∈Icc i j,g t=(k t-k0 t)*(k t+k0 t))
 (positive : ∀ t∈Icc i j, 0≤k0 t ∧ k0 t≤k t) : 0≤delta j :=
begin
 rw [←initial],
 apply integrated_nonnegative _ _ _ _ hij der continuous_force,
 intros t ht, change 0≤g t, rw [rate t ht], obtain ⟨a,b⟩ := positive t ht,
 exact mul_nonneg (sub_nonneg.mpr b) (by linarith)
end

theorem zero_schwarzian_loaded_correction (k dk ddk a b db : ℝ)
 (hk : k≠0) (ha : a≠0) (first : dk= -k^2/a+b)
 (second : ddk= -2*k*dk/a+db) :
 2*ddk/k-4*(dk/k)^2 = 2*db/k-4*b*dk/k^2 :=
begin
 rw [second],field_simp [hk,ha],
 have g : a*dk= -k^2+a*b := by {rw [first],field_simp [ha];ring},
 linear_combination -4*k^4*dk*g
end

theorem recoil_inverse (q e m : ℝ) (hq : 0<q) (he : 0<e) (hm : 0<m) :
 let Q := q+2*e, E := m^2*e/(q*(q+2*e)) in
 q*(m^2+2*E*Q)=m^2*Q ∧ e*(m^2+2*E*Q)=E*Q^2 :=
begin
 dsimp,have h : q+2*e≠0 := by linarith,
 constructor;field_simp [h, ne_of_gt hq];ring
end

theorem recoil_log_jacobian (u : ℝ) : u*u-(1-u)*(-1-u)=1 := by ring

theorem recoil_band_gap (qlo qhi ehi elo q1 q2 e1 e2 : ℝ)
 (bands : 2*(elo-ehi)>qhi-qlo) (h1 : q1≤qhi) (h2 : qlo≤q2)
 (h3 : e1≤ehi) (h4 : elo≤e2) : q1+2*e1<q2+2*e2 := by linarith

theorem clock_spread (q b m i : ℝ) (hm : m≠0) :
 (((q+b)/m)^2-((q-b)/m)^2)*i=4*q*b*i/m^2 :=
by {field_simp [hm];ring}

theorem time_and_which_energy (q b m i e eta width : ℝ) (h : 0≤q)
 (hi : 0≤i) (ht : 0≤eta)
 (time : 4*q*b*i≤m^2*width) (visibility : e≤eta*b) :
  4*q*e*i≤eta*m^2*width :=
by nlinarith [mul_nonneg ht (sub_nonneg.mpr time),
  mul_nonneg (mul_nonneg h hi) (sub_nonneg.mpr visibility)]

-- Each radiation kernel element after the mirror is traced is such an integral.
theorem disjoint_recoil_trace {α : Type*} [measurable_space α] (μ : measure α)
 (left right : set α) (a b : α → ℂ) (h : ∀ x, x∈left → x∉right)
 (ha : ∀ x, x∉left → a x=0) (hb : ∀ x, x∉right → b x=0) :
 ∫ x, a x * conj (b x) ∂μ = 0 :=
begin
 have point : ∀ x, a x * conj (b x)=0,
 {intro x,by_cases H : x∈left,
  {simp [hb x (h x H)]},
  {simp [ha x H]}},
 simp [point]
end

theorem pair_escape_cone (v x c : ℝ) (hx : 0<1-v*x) (hc : 0<1-v*c) :
 c<(v-x)/(1-v*x) ↔ x<(v-c)/(1-v*c) :=
by {rw [lt_div_iff hx,lt_div_iff hc],split;intro h;nlinarith}

theorem ray_pair_energy (m e v x : ℝ) :
 m*e*(1+v*x)/2+m*e*(1-v*x)/2=m*e := by ring

theorem halfangle_escape (v c : ℝ) (hv : 1+v≠0) (hc : 1+c≠0)
 (h : 1-v*c≠0) :
 let a := (1-c)/(1+c), b := (1-v)/(1+v) in
 (a-b)*(1-v*c)=(v-c)*(a+b) :=
by {dsimp,field_simp [hv,hc];ring}

theorem ejection_cost (f : ℝ) (hf : f≠0) :
 (1+(1-f))/f=2/f-1 := by {field_simp [hf];ring}

theorem marginal_escape_limit :
 (((27:ℝ)/4)-1)/((27:ℝ)/4+1)=23/31 := by norm_num

theorem exterior_weight (f L r : ℝ) (hf : f≠0) (hr : r≠0) :
 (f*L/r^2)/f=L/r^2 := by {field_simp [hf,hr];ring}

theorem static_zero_form (gradient weighted : ℝ) (hg : 0≤gradient)
 (hv : 0≤weighted) (h : gradient+weighted=0) : gradient=0 ∧ weighted=0 :=
by {constructor;linarith}

theorem outgoing_reference {E F ι : Type*} [normed_add_comm_group E]
 [inner_product_space ℂ E] [normed_add_comm_group F] [inner_product_space ℂ F]
 (w : E →ₗᵢ[ℂ] F) (v : ι → E) (i j : ι) :
 @inner ℂ F _ (w (v i)) (w (v j)) = @inner ℂ E _ (v i) (v j) :=
 w.inner_map_map _ _

end fermionic_horizon_memory
