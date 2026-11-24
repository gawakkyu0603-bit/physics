import tactic
import analysis.calculus.mean_value
import analysis.special_functions.integrals
import analysis.special_functions.trigonometric.inverse

noncomputable theory
open measure_theory set
open_locale interval big_operators

namespace collapse_charge_conversion

theorem pair_quantization (q p : ℤ) (outer : 2*q+2=0) (inner : 2*p-2=0) :
 q= -1 ∧ p=1 ∧ q+p=0 := by omega

theorem sphere_curvature_integral :
 (∫ t in (0:ℝ)..real.pi, real.sin t)=2 :=
begin
 rw [integral_sin],norm_num
end

theorem two_line_flux (k : ℝ) (unit : k=1 ∨ k= -1) :
 (2*real.pi)*(k/2)*(∫ t in (0:ℝ)..real.pi,real.sin t)/(2*real.pi)=k :=
by {rw [sphere_curvature_integral],field_simp [real.pi_ne_zero],ring}

theorem moving_dust_level (v mu c b : ℝ) (eqn : (2*mu-c)*v= -c*b)
 (regular : 2*mu-c≠0) : v= -c*b/(2*mu-c) :=
(eq_div_iff regular).2 (by simpa [mul_comm] using eqn)

theorem uniform_front (c b : ℝ) (hc : c≠0) :
 -c*b/(2*(3*c/2)-c)= -b/2 ∧ -c*b/(2*0-c)=b :=
begin
 have a : 2*(3*c/2)-c=2*c := by ring,
 have e : 2*(0:ℝ)-c= -c := by ring,
 rw [a,e], constructor,
 { apply (div_eq_div_iff (mul_ne_zero (by norm_num : (2:ℝ)≠0) hc) (by norm_num : (2:ℝ)≠0)).2, ring },
 { apply (div_eq_iff (neg_ne_zero.mpr hc)).2, ring }
end

theorem timelike_window (k b : ℝ) (hb : 0<b) (hk : 2<k) :
 b*(1+k)/(k-2)<1 ↔ 2+b<k*(1-b) :=
by {rw [div_lt_one (by linarith : 0<k-2)],split; intro h; nlinarith only [h]}

theorem inward_timelike (k b : ℝ) (hb : 0<b) (hk : k<2) :
 b*(1+k)/(2-k)<1 ↔ k*(1+b)<2-b :=
by {rw [div_lt_one (by linarith : 0<2-k)],split; intro h; nlinarith only [h]}

theorem front_speed_from_gradient (c b k v mu : ℝ) (hc : c≠0) (hk : 1+k≠0)
 (hf : k≠2) (hab : 2*mu/c=3/(1+k)) (hv : (2*mu-c)*v= -c*b) :
 v= -b*(1+k)/(2-k) :=
begin
 field_simp [hc,hk] at hab,
 have a : (2*mu*(1+k))*v=(3*c)*v := congr_arg (λ z:ℝ,z*v) hab,
 have b' : ((2*mu-c)*v)*(1+k)=(-c*b)*(1+k) := congr_arg (λ z:ℝ,z*(1+k)) hv,
 have e : c*((2-k)*v+b*(1+k))=0 := by nlinarith only [a,b'],
 have r := (mul_eq_zero.mp e).resolve_left hc,
 apply (eq_div_iff (show (2-k:ℝ)≠0,by intro h; apply hf; linarith)).2,
 nlinarith only [r]
end

theorem positive_reference_velocity (v s : ℝ) (hv : 0<v)
 (positive_energy : (1-v*s)^2≤1-v^2) : v*(1+s^2)≤2*s :=
begin
 have h : 0≤v*(2*s-v*(1+s^2)) := by nlinarith only [positive_energy],
 have h' : 0≤2*s-v*(1+s^2) := nonneg_of_mul_nonneg_right h hv, linarith
end

theorem sweep_seed (a r da dr : ℝ → ℝ) (t : ℝ) (ht : 0≤t)
 (hia : ∀ s,has_deriv_at a (da s) s) (hir : ∀ s,has_deriv_at r (dr s) s)
 (hc : continuous (λ s,da s*r s+a s*dr s))
 (speed : ∀ s∈Icc 0 t,da s*r s+a s*dr s≤0) :
 a t*r t≤a 0*r 0 :=
begin
 have diff : ∀ s:ℝ,has_deriv_at (λ x,a x*r x) (da s*r s+a s*dr s) s :=
 λ s,by simpa [mul_comm,add_comm,add_left_comm,add_assoc] using ((hia s).mul (hir s)),
 have e:=interval_integral.integral_eq_sub_of_has_deriv_at (λ s hs,diff s) (hc.interval_integrable 0 t),
 have g:=interval_integral.integral_mono_on ht (hc.interval_integrable 0 t)
    (show interval_integrable (λ s:ℝ,(0:ℝ)) volume 0 t,from interval_integrable_const) speed,
 rw [e] at g, simpa using (sub_nonpos.mp (by simpa using g : a t*r t-a 0*r 0≤0))
end

theorem sweeping_wall_stress (nu v h r : ℝ) (hr : r≠0) :
 (nu-nu*(1+v*h*r))/r= -nu*v*h ∧
 h*nu*v+(nu*(1+v*h*r)-nu)/r=2*nu*v*h :=
by {constructor;field_simp [hr];ring}

theorem dust_wall_flux (nu v rho G dh : ℝ) (hG : G≠0) (friedmann : dh= -4*real.pi*G*rho) :
 -nu^2*v*dh/(4*real.pi*G)=rho*nu^2*v :=
by {rw [friedmann],field_simp [hG,real.pi_ne_zero],ring}

theorem dust_clock_boundary (rho X G beta rapid : ℝ) (hG : G≠0) (ht : X≠0)
 (density : rho=1/(6*real.pi*G*X^2))
 (variation : rho*rapid=beta/(6*real.pi*G*X^2)) : rapid=beta :=
begin
 rw [density] at variation,field_simp [hG,ht,real.pi_ne_zero] at variation, exact variation
end

theorem wall_cloud_energy (m nu r z c : ℝ) (hz : z≠0) (hp : nu*z=1)
 (mass : c*r=2*m) : r*(c/z)=2*nu*m :=
begin
 rw [←mul_div_assoc],apply (div_eq_iff hz).2,
 have h := congr_arg (λ x:ℝ, (2*m)*x) hp,
 change (2*m)*(nu*z)=(2*m)*1 at h, nlinarith only [mass,h]
end

theorem static_join_pressure (s z c nu : ℝ) (hz : z≠0)
 (j : z*s=c) (offset : nu=z+s) :
 z+c/(2*z)-nu= -s/2 :=
by {rw [offset],field_simp [hz],nlinarith only [j]}

theorem gas_partition (gas tension total : ℝ) (sum : gas+tension=total)
 (pressure : gas/2-tension= -total/4) : gas=total/2 ∧ tension=total/2 := by {constructor;linarith}

theorem radial_stability (c : ℝ) (hc : 0<c) (h : c<8/9) :
 0<2*c-c^2/(4*(1-c)) :=
begin
 have hd : 0<4*(1-c) := by linarith,
 have h' : c^2/(4*(1-c))<2*c := (div_lt_iff hd).2
   (by nlinarith only [mul_pos hc (show 0<8-9*c,by linarith)]),
 linarith only [h']
end

theorem boost_tangent (beta w nu g : ℝ) (hb : 0≤beta) (hw : 0≤w) (hn : 0<nu) (hg : 0<g)
 (norm0 : nu^2=1+beta^2) (norm1 : g^2=1+w^2) :
 (beta/nu)*(w-beta)≤g-nu :=
begin
 have iden : (nu*g)^2-(1+beta*w)^2=(w-beta)^2 :=
   by {rw [mul_pow,norm0,norm1],ring},
 have comp : 1+beta*w≤nu*g,
 { by_contra hh, have t : nu*g<1+beta*w := lt_of_not_ge hh,
   have hpos : 0<1+beta*w+nu*g := by positivity,
   nlinarith only [mul_pos (sub_pos.mpr t) hpos,iden,sq_nonneg (w-beta)] },
 rw [div_mul_eq_mul_div],apply (div_le_iff hn).2,
 nlinarith only [comp,norm0]
end

theorem delayed_cloud_mismatch (beta w nu g s h : ℝ) (hb : 0≤beta) (hw : beta<w)
 (hn : 0<nu) (hg : 0<g) (hs : 0≤s) (sm : s<beta/nu) (hh : 1≤h)
 (norm0 : nu^2=1+beta^2) (norm1 : g^2=1+w^2) :
  0<g-nu-s*(w-beta*h) :=
begin
 have tangent:=boost_tangent beta w nu g hb (le_trans hb hw.le) hn hg norm0 norm1,
 have strict:=mul_pos (sub_pos.mpr sm) (sub_pos.mpr hw),
 have keep:=mul_nonneg (mul_nonneg hs hb) (sub_nonneg.mpr hh),
 nlinarith only [tangent,strict,keep]
end

-- Accreted shift charge and Misner--Sharp mass have the same derivative.
theorem swept_mass (n m : ℝ → ℝ) (flux : ℝ → ℝ) (T : ℝ)
 (hn : ∀ t,has_deriv_at n (flux t) t) (hm : ∀ t,has_deriv_at m (flux t) t)
 (reg : interval_integrable flux volume 0 T) (seed : n 0=m 0) : n T=m T :=
begin
 have a:=interval_integral.integral_eq_sub_of_has_deriv_at (λ t ht,hn t) reg,
 have b:=interval_integral.integral_eq_sub_of_has_deriv_at (λ t ht,hm t) reg,
 linarith only [a,b,seed]
end

theorem material_clock_eos (q w s nu : ℝ) :
 nu-(q*(s^2/2)-((1+s^2/2)*q-s*w-nu))=q-s*w := by ring

theorem dust_clock_fderiv (q w : ℝ → ℝ) (s nu : ℝ)
 (hq : has_deriv_at q (w s) s) (hw : has_deriv_at w (q s) s) :
 has_deriv_at (λ x,(1+x^2/2)*q x-x*w x-nu) ((s^2/2)*w s) s :=
begin
 convert (((((has_deriv_at_const s (1:ℝ)).add ((has_deriv_at_pow 2 s).div_const 2)).mul hq).sub
 ((has_deriv_at_id s).mul hw)).sub_const nu) using 1, norm_num, ring
end

theorem branching_law (q w s dq dw : ℝ) (hw : w≠0)
 (boost_norm : w*dw=q*dq) (normal : s*q= -dq+w+s*dw) :
 s*q=w ∨ dq=w :=
begin
 have h : (s*q-w)*(dq-w)=0,
 { have a : w*(s*q)=w*(-dq+w+s*dw) := congr_arg (λ z:ℝ,w*z) normal,
   have b : s*(w*dw)=s*(q*dq) := congr_arg (λ z:ℝ,s*z) boost_norm,
   nlinarith only [a,b] },
 rcases mul_eq_zero.mp h with h|h,
 {left,linarith}, {right,linarith}
end

theorem range_for_freezing (m M c R : ℝ) (hc : 0<c) (r : R=2*m/c) :
 2*M<R ↔ c*M<m :=
by {rw [r,lt_div_iff hc],split;intro h;nlinarith only [h]}

theorem rest_charge_leakage (R M N vel d : ℝ) (hr : R≠0)
 (gravity : d^2=1-2*M/R+vel^2) (stored : d^2=1-2*N/R) :
 vel^2=2*(M-N)/R :=
begin
 have h:=gravity.symm.trans stored,field_simp [hr] at h,
 apply (eq_div_iff hr).2,nlinarith only [h]
end

theorem angular_cone (c : ℝ) (hc : c<1) (large : 2/3<c) :
 1<c/(2*(1-c)) ∧ (1-c)*(c/(2*(1-c)))=c/2 :=
begin
 have hp : 0<2*(1-c) := by linarith,constructor,
 { apply (lt_div_iff hp).2,linarith },
 { field_simp [show (1-c)≠0,by linarith],ring }
end

theorem dust_recoil (q w s rho r : ℝ) (hq : q≠0) (hr : r≠0)
 (norm : q^2=1+w^2) (motion : w=q*s) :
 -r*(-w/q^2)*(4*real.pi*r*rho*q^3*w)=r*(4*real.pi*r*rho*(q^3-q)) :=
begin
 have h : w^2=q^2-1 := by linarith,
 calc -r*(-w/q^2)*(4*real.pi*r*rho*q^3*w)=4*real.pi*r^2*rho*q*w^2 :
      by {field_simp [hq],ring}
 ... = r*(4*real.pi*r*rho*(q^3-q)) : by {rw [h],ring}
end

theorem outgoing_recoil (q r flux : ℝ) (hq : q≠0) (hr : r≠0) :
 -r*(1/q)*(flux*q^4/r)= -flux*q^3 :=
by {field_simp [hq,hr],ring}

theorem null_charge_balance (charge mass luminosity clock : ℝ) (time : clock=1)
 (current : charge= -luminosity*clock) (einstein : mass= -luminosity*clock^2) :
 charge=mass := by {rw [current,einstein,time],ring}

theorem distinct_recoil_functions (q w : ℝ) (hq : 0<q) (hw : 0≤w) :
 -w/q^2<1/q :=
lt_of_le_of_lt (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hw) (sq_nonneg q)) (one_div_pos.mpr hq)

theorem intake_pins_radius (s v : ℝ) (current : s^2/2=v^2/2-(v-s)*v) : v=s :=
begin
 have zero : (v-s)^2=0 := by nlinarith only [current],
 nlinarith only [zero,sq_nonneg (v-s)]
end

theorem emitting_radial_freedom (F q m r : ℝ) (hq : q≠0) (hr : r≠0)
 (metric : F=1-2*m/r) :
 (1/q+F*q)/2+(1/q-F*q)/2=1/q ∧
 r*((1-1/q^2)/2+((1/q-F*q)/2)/q)=m ∧
 (1/q+F*q)/2+q*m/r=(q+1/q)/2 :=
begin
 rw [metric],split, {ring},split;field_simp [hq,hr];ring
end

theorem access_radius (a b d : ℝ) (rel : a=1+b*d/2) : a^2=(1+b*d/2)^2 := by rw [rel]

theorem chord_survival (s : ℝ) :
 1-3*s/4+s^3/16=(2-s)^2*(4+s)/16 := by ring

theorem chord_derivative (s : ℝ) :
 has_deriv_at (λ x:ℝ,1-3*x/4+x^3/16) (-(3*(4-s^2)/16)) s :=
begin
 convert (((has_deriv_at_const s (1:ℝ)).sub (((has_deriv_at_id s).const_mul 3).div_const 4)).add
 ((has_deriv_at_pow 3 s).div_const 16)) using 1, norm_num, ring
end

theorem mean_chord :
 (∫ x in (0:ℝ)..2,(1-3*x/4+x^3/16))=3/4 :=
begin
 have h : ∀ x:ℝ,has_deriv_at (λ y:ℝ,y-3*y^2/8+y^4/64) (1-3*x/4+x^3/16) x,
 { intro x, convert (((has_deriv_at_id x).sub (((has_deriv_at_pow 2 x).const_mul 3).div_const 8)).add
 ((has_deriv_at_pow 4 x).div_const 64)) using 1, norm_num, ring },
 have hc : continuous (λ x:ℝ,1-3*x/4+x^3/16) := by continuity,
 rw [interval_integral.integral_eq_sub_of_has_deriv_at (λ x hx,h x) (hc.interval_integrable _ _)],
 norm_num
end

-- On any two-component linear field, the parity projectors sum to the
-- identity. A minus sign in the odd sector exchanges the full input pair.
theorem algebra_exchange {E : Type*} [add_comm_group E] [module ℝ E] (x y : E) :
 (1/2:ℝ) • (x+y) - (1/2:ℝ) • (x-y)=y :=
begin
 rw [smul_add,smul_sub],
 calc (1/2:ℝ) • x + (1/2:ℝ) • y - ((1/2:ℝ) • x - (1/2:ℝ) • y)
     = (1/2:ℝ) • y + (1/2:ℝ) • y : by abel
 ... = y : by {rw [←add_smul],norm_num}
end

theorem ray_projection_energy (a b : ℝ) :
 (a^2+b^2)/2+(a^2+b^2)/2=a^2+b^2 := by ring

theorem fermi_from_ratio (n e : ℝ) (he : 0<e) (ratio : n=(1-n)*e) :
 n=1/(1+1/e) :=
begin
 have den : 1+1/e≠0 := ne_of_gt (by positivity),
 apply (eq_div_iff den).2, field_simp [ne_of_gt he], nlinarith only [ratio]
end

theorem two_sources (n : ℝ) (hn : 0<n) (ht : n<1/2) :
 n<2*n*(1-n) :=
by nlinarith only [mul_pos hn (show 0<1-2*n,by linarith)]

theorem matched_boost_weight (w : ℕ) (c : ℝ) (inside : 2/3<c) (outside : c<1)
 (rate : (w:ℝ)*c^2=1) : w=2 :=
begin
 have hc : 0<c := by linarith,
 have lo : 4/9<c^2 := by nlinarith [mul_pos (show 0<c-2/3,by linarith) (show 0<c+2/3,by linarith)],
 have hi : c^2<1 := by nlinarith [mul_pos (show 0<1-c,by linarith) (show 0<1+c,by linarith)],
 have bound : w<3,
 { by_contra h, have h3 : 3≤w := le_of_not_gt h,
   have h3' : (3:ℝ)≤(w:ℝ) := by exact_mod_cast h3,
   nlinarith only [mul_le_mul_of_nonneg_right h3' (sq_nonneg c),lo,rate] },
 interval_cases w,
 { norm_num at rate },
 { have h' : c^2=1 := by simpa only [nat.cast_one,one_mul] using rate, linarith only [h',hi] }
end

theorem transport_rate (p a p' m r : ℝ) (hp : p≠0) (hr : r≠0)
 (normal : a=p'/p^2+m/(r^2*p)) : p*a=p'/p+m/r^2 :=
by {rw [normal],field_simp [hr,hp],ring}

theorem static_clock (w m r c : ℝ) (hr : r≠0) (hm : m≠0) (hc : c=2*m/r) :
 w*m/r^2=(w*c^2)/(4*m) :=
by {rw [hc],field_simp [hr,hm],ring}

theorem transport_integrating_factor (b p j : ℝ → ℝ) (u v k : ℝ) (hp : p u≠0)
 (hb : has_deriv_at b (-2*(v/p u+k)*b u) u)
 (hd : has_deriv_at p v u) (hj : has_deriv_at j (2*k*j u) u) :
 has_deriv_at (λ t,b t*p t^2*j t) 0 u :=
begin
 convert ((hb.mul (hd.pow 2)).mul hj) using 1,
 norm_num, field_simp [hp], ring
end

theorem reciprocal_clock (b p const j : ℝ) (hc : const≠0) (hb : b≠0)
 (equation : b*p^2*j=const) : 1/b=p^2*j/const :=
by {field_simp [hc,hb],nlinarith only [equation]}

theorem finite_radius_lapse (p F R dR : ℝ → ℝ) (a b : ℝ)
 (lapse : ∀ t,p t^2=F t+2*dR t)
 (hF : interval_integrable F volume a b) (hd : continuous dR)
 (hR : ∀ t,has_deriv_at R (dR t) t) :
 (∫ t in a..b,p t^2)=(∫ t in a..b,F t)+2*(R b-R a) :=
begin
 have eq : (λ t,p t^2)=(λ t,F t+2*dR t) := funext lapse,
 rw [eq,interval_integral.integral_add hF ((hd.interval_integrable _ _).const_mul _),
    interval_integral.integral_const_mul,
    interval_integral.integral_eq_sub_of_has_deriv_at (λ t ht,hR t) (hd.interval_integrable _ _) ]
end

-- x is the time *remaining*, normalized to one at the start of the interval.
-- An endpoint with b(x)<=L*x costs logarithmically divergent integral of 1/b.
theorem terminal_log_bound (b : ℝ → ℝ) (a L : ℝ) (ha : 0<a) (le : a≤1) (hL : 0<L)
 (h : ∀ x∈Icc a 1,0<b x ∧ b x≤L*x)
 (ib : interval_integrable (λ x,1/b x) volume a 1) :
 L⁻¹*real.log (1/a)≤∫ x in a..1,1/b x :=
begin
 have nz : ∀ x∈uIcc a 1,x≠(0:ℝ) :=
 by {intros x hx,rw [uIcc_of_le le] at hx,exact (lt_of_lt_of_le ha hx.1).ne'},
 have hi : interval_integrable (λ x:ℝ,x⁻¹) volume a 1 := (continuous_on_id.inv₀ nz).interval_integrable,
 have mono:=interval_integral.integral_mono_on le (hi.const_mul L⁻¹) ib
 (show ∀ x∈Icc a 1,L⁻¹*x⁻¹≤1/b x,from
  λ x hx,begin
   convert one_div_le_one_div_of_le (h x hx).1 (h x hx).2 using 1,
   simp [one_div,mul_inv_rev, mul_comm]
  end),
 rwa [interval_integral.integral_const_mul,integral_inv_of_pos ha zero_lt_one] at mono
end

theorem terminal_impossibility (L B : ℝ) (hL : 0<L) (hB : 0≤B)
 (bounded : ∀ a : ℝ,0<a → a≤1 → L⁻¹*real.log (1/a)≤B) : false :=
begin
 let t := L*(B+1),
 have ht : 0≤t := mul_nonneg hL.le (by linarith),
 have le : real.exp (-t)≤1 := by simpa using real.exp_le_exp.mpr (neg_nonpos.mpr ht),
 have q:=bounded (real.exp (-t)) (real.exp_pos _) le,
 rw [real.exp_neg,one_div,inv_inv,real.log_exp] at q,
 change L⁻¹*(L*(B+1))≤B at q,
 rw [←mul_assoc,inv_mul_cancel hL.ne',one_mul] at q,linarith
end

theorem no_regular_terminal_gap (b : ℝ → ℝ) (L B : ℝ) (hL : 0<L) (hB : 0≤B)
 (gap : ∀ x:ℝ, 0<x → x≤1 → 0<b x ∧ b x≤L*x)
 (ib : ∀ a:ℝ, 0<a → a≤1 → interval_integrable (λ x,1/b x) volume a 1)
 (area : ∀ a:ℝ, 0<a → a≤1 → (∫ x in a..1,1/b x)≤B) : false :=
begin
 apply terminal_impossibility L B hL hB, intros a ha h1,
 exact (terminal_log_bound b a L ha h1 hL
 (λ x hx,gap x (lt_of_lt_of_le ha hx.1) hx.2) (ib a ha h1)).trans (area a ha h1)
end

-- The time variable is the remaining retarded time, with the endpoint at 0.
theorem finite_switch_distance (g : ℝ → ℝ) (x : ℝ) (hx : 0<x)
 (hg : interval_integrable g volume 0 x)
 (hs : interval_integrable (λ t,g t^2) volume 0 x) :
 (∫ t in 0..x,g t)^2 ≤ x*(∫ t in 0..x,g t^2) :=
begin
 let m := (∫ t in 0..x,g t)/x,
 have hm : (∫ t in 0..x,g t)=x*m := by {dsimp [m],field_simp [ne_of_gt hx],ring},
 have pos : 0 ≤ ∫ t in 0..x,(g t-m)^2 :=
 interval_integral.integral_nonneg hx.le (λ t ht,sq_nonneg _),
 have alg : (λ t,(g t-m)^2)=(λ t,g t^2-2*m*g t+m^2) := funext (λ t,by ring),
 rw [alg,interval_integral.integral_add (hs.sub (hg.const_mul _)) interval_integrable_const,
 interval_integral.integral_sub hs (hg.const_mul _),interval_integral.integral_const_mul,hm] at pos,
 dsimp only at pos, rw [interval_integral.integral_const] at pos,
 simp only [sub_zero,smul_eq_mul] at pos,
 have h : x*m^2 ≤ (∫ t in 0..x,g t^2) := by nlinarith only [pos],
 rw [hm],nlinarith only [mul_le_mul_of_nonneg_left h hx.le]
end

theorem clock_energy_pointwise (b d x K C : ℝ) (hk : 0≤K)
 (gap : b≤K*d^2) (energy : d^2≤x*C) : b≤(K*C)*x :=
by nlinarith only [gap,mul_le_mul_of_nonneg_left energy hk]

theorem cap_rate (m r v : ℝ) (hr : r≠0) (orbit : v=m/r) : v/r=m/r^2 :=
by {rw [orbit,div_div,pow_two]}

-- A bound on the finite-radius trajectory gives a uniform bound on the
-- integral of the reciprocal of the transported rank-two amplitude.
theorem reciprocal_area_bound (b p : ℝ → ℝ) (a t K B : ℝ) (ht : a≤t) (hk : 0≤K)
 (pointwise : ∀ u∈Icc a t,1/b u≤K*p u^2)
 (ib : interval_integrable (λ u,1/b u) volume a t)
 (ip : interval_integrable (λ u,p u^2) volume a t)
 (size : (∫ u in a..t,p u^2)≤B) :
 (∫ u in a..t,1/b u)≤K*B :=
begin
 have h:=interval_integral.integral_mono_on ht ib (ip.const_mul K) pointwise,
 rw [interval_integral.integral_const_mul] at h,
 exact h.trans (mul_le_mul_of_nonneg_left size hk)
end

theorem final_radius (m l R F : ℝ)
 (balance : F^2=R^2+2*m*l*(3/4)) : F^2=R^2+3*m*l/2 := by linarith

-- With v=u+2r the first scattering source is (du dv psi1)=-4 M f/(v-u)^3.
theorem tail_source (m f v u r : ℝ) (h : v-u=2*r) (hr : r≠0) :
 (-2*m*f/r^3)/4 = -4*m*f/(v-u)^3 :=
by {rw [h],field_simp [hr],ring}

-- The late outgoing derivative has fixed sign for an input with positive
-- integrated mass-weighted monopole amplitude on 0 <= s <= T < v.
theorem tail_lower_bound (a : ℝ → ℝ) (T v : ℝ) (ht : 0≤T) (hv : T<v)
 (ha : ∀ t∈Icc 0 T,0≤a t) (ia : interval_integrable a volume 0 T)
 (ik : interval_integrable (λ t,4*a t/(v-t)^3) volume 0 T) :
 (4/v^3)*(∫ t in 0..T,a t) ≤ ∫ t in 0..T,4*a t/(v-t)^3 :=
begin
 have vv : 0<v := lt_of_le_of_lt ht hv,
 have mono:=interval_integral.integral_mono_on ht (ia.const_mul (4/v^3)) ik
 (show ∀ t∈Icc 0 T,(4/v^3)*a t≤4*a t/(v-t)^3,from
 λ t h,begin
   have h0 : 0<v-t := sub_pos.mpr (lt_of_le_of_lt h.2 hv),
   have hb : (v-t)^3≤v^3 := pow_le_pow_of_le_left h0.le (sub_le_self _ h.1) 3,
   rw [div_mul_eq_mul_div], exact div_le_div_of_le_left (mul_nonneg (by norm_num) (ha t h))
      (pow_pos h0 3) hb
 end),
 rwa [interval_integral.integral_const_mul] at mono
end

theorem characteristic_return (D a : ℝ → ℝ) (T v incoming : ℝ) (h0 : D 0=0)
 (evolve : ∀ t,has_deriv_at D (-(4*a t/(v-t)^3)) t)
 (ik : interval_integrable (λ t,4*a t/(v-t)^3) volume 0 T)
 (regular_center : incoming = -D T) :
 incoming = ∫ t in 0..T,4*a t/(v-t)^3 :=
begin
 have eq:=interval_integral.integral_eq_sub_of_has_deriv_at (λ t ht,evolve t) ik.neg,
 rw [interval_integral.integral_neg,h0,sub_zero] at eq, rw [regular_center,←eq,neg_neg]
end

theorem phase_space_norm (v a b : ℝ) (hv : 0≤v) :
 (real.sqrt v*a)^2+(real.sqrt v*b)^2=v*(a^2+b^2) :=
by {rw [mul_pow,mul_pow,real.sq_sqrt hv],ring}

theorem contact_complement (s v : ℝ) (hs : 0≤s) (hv : 0≤v) :
 1-4*s*v/(1+s*v)^2=(1-s*v)^2/(1+s*v)^2 :=
begin
 have n : 1+s*v≠0 := ne_of_gt (by positivity),
 field_simp [n], ring
end

theorem contact_perfect (s v : ℝ) (hs : 0≤s) (hv : 0≤v)
 (p : 4*s*v/(1+s*v)^2=1) : s*v=1 :=
begin
 have h := contact_complement s v hs hv, rw [p,sub_self] at h,
 have d : (1+s*v)^2≠0 := pow_ne_zero 2 (ne_of_gt (by positivity)),
 have z : (1-s*v)^2=0 := (div_eq_zero_iff.mp h.symm).resolve_right d,
 nlinarith only [z,sq_nonneg (1-s*v)]
end

end collapse_charge_conversion
