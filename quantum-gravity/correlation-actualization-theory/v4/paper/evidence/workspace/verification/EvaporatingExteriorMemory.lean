import tactic
import analysis.special_functions.integrals
import analysis.special_functions.improper_integrals
import analysis.inner_product_space.basic

noncomputable theory
open measure_theory set filter
open_locale big_operators real topology complex_conjugate
namespace evaporating_exterior

theorem conformal_metric (m f nu z du dz : ℝ) :
 -f*(m*du)^2-2*(m*du)*(m*dz-nu*z*m*du)
 =m^2*(-(f-2*nu*z)*du^2-2*du*dz) := by ring

theorem similarity_lapse (z nu a b : ℝ) (hz : z≠0)
 (hs : 2*nu*(a+b)=1) (hp : nu*a*b=1) :
 1-2/z-2*nu*z=(-2*nu)*(z-a)*(z-b)/z :=
calc 1-2/z-2*nu*z = (z-2-2*nu*z*z)/z : by {field_simp [hz];ring}
 ... = ((-2*nu)*(z-a)*(z-b))/z : congr_arg (λ c:ℝ,c/z)
   (by linear_combination -z*hs+2*hp)

theorem boundary_oscillator (F z j : ℝ) (hz : z≠0) :
 F*(j*(j+1)/z^2+(2/z^2)/8)=F*((j+1/2)^2/z^2) :=
by {field_simp [hz];ring}

theorem wave_energy (dt dx dd xx v q : ℝ) (h : dd-xx+v*q=0) :
 dt*dd+dx*(0:ℝ)+v*q*dt-dt*xx=0 := by linear_combination dt*h

theorem endpoint_work (m k q a v flux : ℝ) (h : m*a+k*q=flux) :
 m*v*a+k*q*v=v*flux := by linear_combination v*h

theorem positive_surface (m k q p : ℝ) (hm : 0<m) (hk : 0<k)
 (h : m*p^2+k*q^2=0) : p=0 ∧ q=0 :=
begin
 have hp := mul_nonneg hm.le (sq_nonneg p),
 have hq := mul_nonneg hk.le (sq_nonneg q),
 have hp' : m*p^2=0 := by linarith,
 have hq' : k*q^2=0 := by linarith,
 exact ⟨pow_eq_zero ((mul_eq_zero.mp hp').resolve_left hm.ne'),
        pow_eq_zero ((mul_eq_zero.mp hq').resolve_left hk.ne')⟩
end

/-- The Wronskian of the actual retarded Vaidya radial equation in real and
imaginary components. a,b are the two amplitudes; p,q their radial slopes. -/
theorem radial_current_derivative (F dF a b p q pp qq g w : ℝ)
 (hr : F*pp+dF*p-2*w*q-g*a=0) (hi : F*qq+dF*q+2*w*p-g*b=0) :
 dF*(a*q-b*p)+F*(a*qq-b*pp)+2*w*(a*p+b*q)=0 :=
by linear_combination a*hi-b*hr

theorem propagated_current (f : ℝ → ℝ) (lo hi : ℝ)
 (h : ∀ x∈uIcc lo hi, has_deriv_at f 0 x) : f hi=f lo :=
begin
 have eqn := interval_integral.integral_eq_sub_of_has_deriv_at h
   (show interval_integrable (λ x:ℝ,(0:ℝ)) volume lo hi, from continuous_const.interval_integrable _ _),
 simp at eqn,linarith
end

theorem signed_wave_current (a b c d w : ℝ) :
 w*((a+c)^2+(b+d)^2)-2*w*((a+c)*c+(b+d)*d)=w*(a^2+b^2-c^2-d^2) := by ring

theorem outgoing_admittance (a b p q w : ℝ) (h : a*q-b*p=w)
 (hw : 0<w) (hz : 0<a^2+b^2) : 0<(q*a-p*b)/(a^2+b^2) :=
by {apply div_pos _ hz,linarith}

theorem no_real_surface_pole (K A B : ℝ) (h : 0<B) : 0<(K-A)^2+B^2 :=
add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos h)

theorem no_dark_boundary (q y p : ℝ) (h : q=y) (hz : y=0) (hp : p=0) :
 q=0 ∧ p=0 := ⟨h.trans hz,hp⟩

theorem flux_ratio (a b : ℂ) (h : complex.norm_sq a-complex.norm_sq b=1) :
 complex.norm_sq b<complex.norm_sq a := by linarith

theorem repair_norm (a b q : ℂ) :
 complex.norm_sq (conj a-q*conj b)-complex.norm_sq (q*a-b)
 =(complex.norm_sq a-complex.norm_sq b)*(1-complex.norm_sq q) :=
by {simp [complex.norm_sq_apply,complex.add_re,complex.sub_re,complex.mul_re,
  complex.add_im,complex.sub_im,complex.mul_im,complex.conj_re,complex.conj_im];ring}

theorem second_mode_allowed (a b q : ℂ) (hs : complex.norm_sq a-complex.norm_sq b=1)
 (hq : complex.norm_sq q<1) :
 complex.norm_sq (q*a-b)<complex.norm_sq (conj a-q*conj b) :=
begin
 have eqn := repair_norm a b q,rw [hs,one_mul] at eqn,linarith
end

theorem required_partner (a b q c : ℂ) (hc : c*(conj a-q*conj b)=q*a-b) :
 b+conj a*c=q*(a+conj b*c) := by linear_combination hc

/-- Coefficient on t=r of D_l (t+r)^(s+l), excluding the common factor 2^s. -/
def down : ℕ → ℂ → ℂ
| 0 s := 1
| (n+1) s := (s-((n:ℂ)+1))*down n s

theorem cone_shift (n : ℕ) (s : ℂ) :
 (s-(n:ℂ))*down n (s+1)=s*down n s :=
begin
 induction n with n ih,
 {simp [down]},
 {rw [down,down,nat.cast_succ],
  linear_combination (s-((n:ℂ)+1))*ih}
end

theorem ladder_on_cone (n : ℕ) (s : ℂ) :
 2*(s-(n:ℂ))*down n (s+1)-(s+(n:ℂ)+1)*down n s=down (n+1) s :=
by {rw [down],linear_combination 2*cone_shift n s}

theorem radial_intertwiner (n r f d dd ddd : ℝ) (hr : r≠0) :
 -ddd+(n+1)*(dd/r-2*d/r^2+2*f/r^3)+(n+1)*(n+2)/r^2*(d-(n+1)*f/r)
 = -ddd+n*(n+1)*(d/r^2-2*f/r^3)-(n+1)/r*(-dd+n*(n+1)*f/r^2) :=
by {field_simp [hr];ring}

noncomputable def energy_factor : ℕ → ℝ → ℝ
| 0 x := 1/2
| (n+1) x := energy_factor n x * (x^2+((n:ℝ)+3/2)^2)/(x^2+((n:ℝ)+1/2)^2)

theorem all_cone_energies (l : ℕ) (x : ℝ) :
 energy_factor l x*(x^2+1/4)=(x^2+((l:ℝ)+1/2)^2)/2 :=
begin
 induction l with n ih,
 {rw [energy_factor,nat.cast_zero],ring}, 
 {rw [energy_factor,nat.cast_succ],
  have pos : 0<x^2+((n:ℝ)+1/2)^2 := by positivity,
  calc energy_factor n x*(x^2+((n:ℝ)+3/2)^2)/(x^2+((n:ℝ)+1/2)^2)*(x^2+1/4)
    =(energy_factor n x*(x^2+1/4))*(x^2+((n:ℝ)+3/2)^2)/(x^2+((n:ℝ)+1/2)^2) : by {simp only [div_eq_mul_inv];ring}
    ... = _ : by {rw [ih],apply (div_eq_iff pos.ne').2,ring}}
end

theorem mellin_unit (x n : ℝ) :
 x^2+n^2=x^2+(-n)^2 := by ring

theorem flat_integrated (l : ℕ) (f : ℝ → ℝ) :
 (∫ x,energy_factor l x*(x^2+1/4)*f x)=
 (∫ x,(x^2+((l:ℝ)+1/2)^2)/2*f x) := by simp only [all_cone_energies]

theorem cone_null_energy (t r v q : ℝ) :
 (t^2+r^2+v*q^2)/2+t*r=((t+r)^2+v*q^2)/2 := by ring

theorem finite_clock_energy (m b : ℝ) (hm : m≠0) : (m*b)^2/m=m*b^2 :=
by {field_simp [hm];ring}

theorem stationary_regular_limit (d bound : ℝ) (hb : 0≤bound)
 (h : ∀ ε:ℝ,0<ε → |d|≤ε*bound) : d=0 :=
begin
 by_contra hn, have hp := abs_pos.mpr hn,
 have p : 0<bound+1 := by linarith,
 have eqn := h (|d|/(2*(bound+1))) (div_pos hp (by linarith)),
 have q : 0<2*(bound+1) := by linarith,
 have eqn' : |d|*(2*(bound+1))≤|d|*bound := (le_div_iff q).mp
   (by simpa [div_mul_eq_mul_div] using eqn),
 nlinarith only [eqn',hp,mul_nonneg hp.le hb]
end

theorem dilation_current_kernel (a b : ℝ) (ha : a≠0) (hb : b≠0) (hd : a^2≠b^2) :
 (a^2*b^2)/(a^2-b^2)^2=1/(a/b-b/a)^2 :=
by {field_simp [ha,hb]; ring}

theorem angular_divergence (s c f df : ℝ) :
 2*s*f*(c*f+s*df)=2*s*c*f^2+2*s^2*f*df := by ring

theorem cap_flux (J W A D : ℝ → ℝ) (lo hi : ℝ)
 (hd : ∀ t ∈ uIcc lo hi,has_deriv_at (λ x:ℝ,W x*A x) (J t+D t) t)
 (hj : interval_integrable J volume lo hi) (hc : interval_integrable D volume lo hi) :
 (∫ t in lo..hi,J t)=W hi*A hi-W lo*A lo-∫ t in lo..hi,D t :=
begin
 have h := interval_integral.integral_eq_sub_of_has_deriv_at hd (hj.add hc),
 rw [interval_integral.integral_add hj hc] at h,dsimp at h,linarith
end

theorem dipole_ratio : -(1:ℝ)/(2*(4/3))= -3/8 ∧ -(16/15)/(2*(4/3):ℝ)= -2/5 :=
by norm_num

theorem helicity_sign (s : ℝ) (h : 0<s) : -s^2/2<0 ∧ 0<s^2/2 :=
by {have p:=sq_pos_of_pos h,split;linarith}

theorem finite_record_readout {ι : Type*} (J : ι → ℝ) (h : function.injective J)
 (i j : ι) (hij : i≠j) : J i≠J j := λ eqn,hij (h eqn)

theorem parity_fourth_difference (c0 c1 c2 c3 c4 : ℝ) :
 let p := λ x:ℝ,c0+c1*x+c2*x^2+c3*x^3+c4*x^4 in
 (p 0-4*p 3+6*p 6-4*p 9+p 12)/8=243*c4 := by {dsimp;ring}

theorem four_distinct_helicities : (243:ℝ)*16/(12*11*10*9)=18/55 := by norm_num

theorem gaussian_fourth_fidelity (d : ℝ) : d^2/(16*24)=d^2/384 := by ring

/-- Differentiate the actual radial current before applying the radial ODE. -/
theorem radial_current_at (F a b p q : ℝ → ℝ) (x dF pp qq w g : ℝ)
 (hF : has_deriv_at F dF x) (ha : has_deriv_at a (p x) x)
 (hb : has_deriv_at b (q x) x) (hp : has_deriv_at p pp x) (hq : has_deriv_at q qq x)
 (hr : F x*pp+dF*p x-2*w*q x-g*a x=0) (hi : F x*qq+dF*q x+2*w*p x-g*b x=0) :
 has_deriv_at (λ z,F z*(a z*q z-b z*p z)+w*(a z*a z+b z*b z)) 0 x :=
begin
 have h := (hF.mul ((ha.mul hq).sub (hb.mul hp))).add (((ha.mul ha).add (hb.mul hb)).const_mul w),
 convert h using 1,
 linear_combination -a x*hi+b x*hr
end

/-- The inverse transform is applied only after both Plancherel equalities are
supplied. The arbitrary nonnegative spectral power may encode any wave packet. -/
theorem physical_packet_energy (n : ℕ) (density : ℝ → ℝ) (early late : ℝ)
 (h1 : late=∫ x,energy_factor n x*(x^2+1/4)*density x)
 (h2 : early=∫ x,(x^2+((n:ℝ)+1/2)^2)/2*density x) : late=early :=
 h1.trans ((flat_integrated n density).trans h2.symm)

theorem binary_angle_exception (a b e f : ℝ) (h : a≠b) :
 {x:ℝ | a*x+e=b*x+f} ⊆ ({(f-e)/(a-b)} : set ℝ) :=
begin
 intros x hx,change a*x+e=b*x+f at hx,change x=(f-e)/(a-b),
 apply (eq_div_iff (sub_ne_zero.mpr h)).2,linear_combination hx
end

theorem angles_exception_null (a b e f : ℝ) (h : a≠b) :
 (volume : measure ℝ) {x:ℝ | a*x+e=b*x+f}=0 :=
 measure_mono_null (binary_angle_exception a b e f h) (measure_singleton _)

theorem time_of_infall_difference (s₀ s₁ : ℝ) (h₀ : s₀≠0) (h₁ : s₁≠0) :
 (2/9:ℝ)*(1/s₁-1/s₀)=(2/(9*s₁)-2/(9*s₀)) := by {field_simp [h₀,h₁];ring}

theorem inverse_time_tide (s₀ t : ℝ) (h : s₀-t≠0) :
 has_deriv_at (λ u:ℝ,(2/9:ℝ)/(s₀-u)) ((2/9)/(s₀-t)^2) t :=
begin
 have d := (has_deriv_at_const t s₀).sub (has_deriv_at_id t),
 have v := (has_deriv_at_const t (2/9:ℝ)).div d h,
 convert v using 1,dsimp,ring
end

theorem finite_exposure (s₀ a b : ℝ) (h : ∀ x∈uIcc a b,s₀-x≠0)
 (hint : interval_integrable (λ x:ℝ,(2/9)/(s₀-x)^2) volume a b) :
 (∫ x in a..b,(2/9:ℝ)/(s₀-x)^2)=(2/9)/(s₀-b)-(2/9)/(s₀-a) :=
 interval_integral.integral_eq_sub_of_has_deriv_at
  (λ x hx,inverse_time_tide s₀ x (h x hx)) hint

theorem bounded_link_variance (d mean second : ℝ) (hr : second≤d*mean) :
 second-mean^2≤(d/2)^2 :=
calc second-mean^2 ≤ d*mean-mean^2 : sub_le_sub_right hr _
 ... = (d/2)^2-(mean-d/2)^2 : by ring
 ... ≤ (d/2)^2 : sub_le_self _ (sq_nonneg _)

theorem constant_phase_attainment (phase : ℝ) :
 (1+real.cos (2*phase))/2=(real.cos phase)^2 :=
by {rw [real.cos_two_mul],nlinarith only [real.sin_sq_add_cos_sq phase]}

theorem finite_discrimination (angle threshold budget m : ℝ)
 (hm : 0<m) (ha : threshold≤angle) (hb : angle≤budget/m) :
 m*threshold≤budget :=
by {have hh := (le_div_iff hm).mp (ha.trans hb),linarith only [hh,mul_comm m threshold]}

/-- Charge-controlled transport of an actual pointer, followed by inverse
transport. The flag can be smooth throughout the unoccupied interval. -/
theorem focused_pointer (χ flag : ℝ → ℂ) (b q d qmin : ℝ)
 (hb : 0≤b) (hg : d<b*qmin) (hq : qmin≤q)
 (support : ∀ x,χ x≠0 → 0≤x ∧ x≤d)
 (plateau : ∀ x,b*qmin≤x → flag x=1) :
 (λ x:ℝ,flag (x+b*q)*χ ((x+b*q)-b*q))=χ :=
begin
 funext x,rw [add_sub_cancel],
 by_cases hz:χ x=0,{rw [hz,mul_zero]},
 have h0 := (support x hz).1,
 have lhs := mul_le_mul_of_nonneg_left hq hb,
 rw [plateau (x+b*q) (by linarith),one_mul]
end

theorem empty_pointer (χ flag : ℝ → ℂ) (d : ℝ)
 (support : ∀ x,χ x≠0 → 0≤x ∧ x≤d) (plateau : ∀ x,x≤d → flag x=0) :
 (λ x:ℝ,flag x*χ x)=λ x,0 :=
begin
 funext x,by_cases hz:χ x=0,{rw [hz,mul_zero]},
 rw [plateau x (support x hz).2,zero_mul]
end

theorem two_kick_energy (p m v q : ℝ) (hm : m≠0) :
 (p+m*v*q)^2/(2*m)=p^2/(2*m)+v*q*p+m*v^2*q^2/2 :=
by {field_simp [hm];ring}

theorem bounded_displacement (d lower upper speed t b : ℝ)
 (hL : 0<lower) (hu : 0≤upper) (hb : d<b*lower) (ht : b*upper≤speed*t) :
 d*upper≤(speed*t)*lower :=
begin
 calc d*upper ≤ (b*lower)*upper : mul_le_mul_of_nonneg_right hb.le hu
 ... = (b*upper)*lower : by ring
 ... ≤ (speed*t)*lower : mul_le_mul_of_nonneg_right ht hL.le
end

noncomputable def transfer_product : ℕ → ℂ → ℂ
| 0 s := 1
| (n+1) s := -transfer_product n s*
   ((s+(((n:ℝ)+1:ℝ):ℂ))/(s-(((n:ℝ)+1:ℝ):ℂ)))

theorem norm_rational (a x k : ℝ) :
 complex.norm_sq (((⟨a,x⟩:ℂ)+(k:ℂ))/((⟨a,x⟩:ℂ)-(k:ℂ)))=
 ((a+k)^2+x^2)/((a-k)^2+x^2) :=
by {rw [complex.norm_sq_div],simp [complex.norm_sq_apply,pow_two]}

theorem actual_half_line (n : ℕ) (x : ℝ) :
 (1/2:ℝ)*complex.norm_sq (transfer_product n ⟨1/2,x⟩)=energy_factor n x :=
begin
 induction n with n ih,
 {rw [transfer_product,energy_factor],simp},
 {rw [transfer_product,complex.norm_sq_mul,complex.norm_sq_neg,norm_rational,energy_factor,←ih],
  have e₁ : (1/2+((n:ℝ)+1))^2+x^2=x^2+((n:ℝ)+3/2)^2 := by ring,
  have e₂ : (1/2-((n:ℝ)+1))^2+x^2=x^2+((n:ℝ)+1/2)^2 := by ring,
  rw [e₁,e₂],simp only [div_eq_mul_inv],ring}
end

theorem actual_imaginary_line (n : ℕ) (x : ℝ) :
 complex.norm_sq (transfer_product n ⟨0,x⟩)=1 :=
begin
 induction n with n ih,
 {rw [transfer_product],simp},
 {rw [transfer_product,complex.norm_sq_mul,complex.norm_sq_neg,norm_rational,ih,one_mul],
  have eqn : (0-((n:ℝ)+1))^2+x^2=(0+((n:ℝ)+1))^2+x^2 := by ring,
  rw [eqn],apply div_self,have hp : 0<(0+((n:ℝ)+1))^2+x^2 := by positivity,exact hp.ne'}
end

theorem actual_energy_line (l : ℕ) (x : ℝ) :
 (1/2:ℝ)*complex.norm_sq (transfer_product l ⟨1/2,x⟩)*(x^2+1/4)
 =(x^2+((l:ℝ)+1/2)^2)/2 :=
by rw [actual_half_line,all_cone_energies]

theorem bondi_balance (m p : ℝ → ℝ) (a b : ℝ)
 (hd : ∀ x∈uIcc a b,has_deriv_at m (-p x) x) (hp : interval_integrable p volume a b) :
 m a-m b=∫ x in a..b,p x :=
begin
 have h := interval_integral.integral_eq_sub_of_has_deriv_at hd hp.neg,
 rw [interval_integral.integral_neg] at h,linarith
end

theorem bondi_mass_tail (mass p : ℝ → ℝ) (u : ℝ)
 (hb : ∀ b:ℝ,mass u-mass b=∫ x in u..b,p x)
 (hm : tendsto mass at_top (𝓝 0)) (q : ℝ)
 (hq : tendsto (λ b,∫ x in u..b,p x) at_top (𝓝 q)) :
 mass u=q :=
begin
 have h := (tendsto_const_nhds : tendsto (λ b:ℝ,mass u) at_top (𝓝 (mass u))).sub hm,
 simp only [sub_zero] at h,
 have hh : (λ b:ℝ,mass u-mass b)=(λ b,∫ x in u..b,p x) := funext hb,
 rw [←hh] at hq,exact tendsto_nhds_unique h hq
end

theorem positive_late_energy (mass L eps : ℝ) (hL : 0<L) (he : eps≠0)
 (h : mass=45*eps^2/(4*L)) : 0<mass :=
by {rw [h],exact div_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero eps he)) (by linarith)}

theorem spin_flux_surface_term (A : ℝ → ℝ) (x d : ℝ) (ha : has_deriv_at A d x) :
 has_deriv_at (λ z:ℝ,real.sin z^2*A z)
 (2*real.sin x*real.cos x*A x+real.sin x^2*d) x :=
begin
 have h := ((real.has_deriv_at_sin x).pow 2).mul ha,
 convert h using 1,simp;ring
end

theorem fully_resolved_fidelity {ι : Type*} [fintype ι] (weight : ι → ℝ) (d : ℝ)
 (hd : d≠0) (s : ∑ i,weight i=d) :
 (∑ i,weight i)/d^2=1/d :=
by {rw [s],field_simp [hd];ring}

/-- In outgoing flat coordinates the mixed Einstein constraint follows from
the actual radial Maxwell equation, including the centrifugal potential. -/
theorem monopole_continuity (psi du dr dur drr angular : ℝ)
 (wave : drr-2*dur-angular*psi=0) :
 dr*dur+angular*psi*du+(2*du*dur-dur*dr-du*drr)=0 :=
by linear_combination -du*wave

theorem monopole_flux_components (a b potential : ℝ) :
 ((a^2+(b-a)^2+potential)/2-(a^2-a*b)=(b^2+potential)/2)
 ∧ ((a^2+(b-a)^2+potential)/2+(a^2+(b-a)^2-potential)/2-2*(a^2-a*b)=b^2) :=
by split;ring

theorem dipole_flux_polynomial (x : ℝ) :
 (x^3*(4-x))^2+2*x^6=18*x^6-8*x^7+x^8 := by ring

theorem dipole_bondi_integral :
 ((18*(720:ℝ)/2^7-8*5040/2^8+40320/2^9)/2=45/4)
 ∧ (-(16*(120:ℝ)/2^6-8*720/2^7+5040/2^8)= -75/16) := by norm_num

theorem vaidya_mass_continuity (f fr fu psi a b ab bb v : ℝ)
 (h : f*bb+fr*b-2*ab-v*psi=0) :
 fu*b^2/2+f*b*ab+v*psi*a+
  (2*a*ab-fr*a*b-f*ab*b-f*a*bb)=fu*b^2/2 :=
by linear_combination -a*h

theorem dust_lapse_feedback (lum r slope : ℝ) :
 (2*lum/r)*slope^2/2=lum*(slope^2/r) := by ring

theorem moving_surface_work (m R : ℝ → ℝ) (J E L b speed x : ℝ)
 (h : has_deriv_at m (-J+L*b) x) (k : has_deriv_at R speed x) :
 has_deriv_at (λ u:ℝ,m u+E*(R u-R x)) (-J+speed*E+L*b) x :=
begin
 have a := h.add ((k.sub (has_deriv_at_const x (R x))).const_mul E),
 convert a using 1,ring
end

/-- The off-diagonal entries of a two-word effect change sign under the
duality rotation. A reflection exchanges the two diagonal entries. -/
theorem two_helicity_effect (a b c d : ℂ) (hb : b= -b) (hc : c= -c) (hr : a=d) :
 a=d ∧ b=0 ∧ c=0 :=
begin
 refine ⟨hr,_,_⟩,
 {linear_combination (1/2:ℂ)*hb},
 {linear_combination (1/2:ℂ)*hc}
end

def angular_pair (a b : fin 3) : ℝ :=
 if a.val+b.val=2 then (if a.val=1 then -1 else 1) else 0

theorem dipole_one_body (i j : fin 3) :
 ∑ k:fin 3,angular_pair i k*angular_pair j k=if i.val=j.val then 1 else 0 :=
by {fin_cases i;fin_cases j;norm_num [fin.sum_univ_succ,angular_pair]}

theorem helicity_angular_reflection (m h c : ℝ) :
 (1+(-m)*(-h)*c)^2/4=(1+m*h*c)^2/4 := by ring

theorem spin_charge_reflection (m h a b : ℝ) :
 (-m)*a+(-h)*b= -(m*a+h*b) := by ring

theorem measured_singlet_example :
 ((3*(-1:ℝ)/4-27/32= -51/32) ∧ (3*(0:ℝ)/4-27/32= -27/32)
 ∧ (3*(1:ℝ)/4-27/32= -3/32)) ∧
 (((1:ℝ)/16*(9/64))/(414/1024)=1/46
 ∧ ((3:ℝ)/8*(15/32))/(414/1024)=20/46
 ∧ ((9:ℝ)/16*(25/64))/(414/1024)=25/46) := by norm_num

theorem unsigned_readout {ι : Type*} [fintype ι] (p : ι → ℝ)
 (hp : ∀ i,0≤p i) (hn : ∑ i,p i=1) :
 (1+∑ i,real.sqrt (p i*p i))/2=1 :=
begin
 have h : ∀ i,real.sqrt (p i*p i)=p i := λ i,real.sqrt_mul_self (hp i),
 simp only [h,hn],norm_num
end

end evaporating_exterior
