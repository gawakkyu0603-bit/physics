import tactic
import analysis.special_functions.integrals
import analysis.special_functions.complex.arg

noncomputable theory
open set measure_theory
open_locale big_operators real topology
namespace gravitational_charge_cycle

/-- Gaussian slab volume element and the integrated total-derivative term. -/
theorem slab_density (a k dk q scalar K2 : ℝ) :
 a*(scalar-k^2-q-2*dk+K2) =
 -2*(a*k*k+a*dk)+a*(scalar+k^2-q+K2) := by ring

theorem slab_faces (a k : ℝ → ℝ) (lo hi : ℝ) (d : ℝ → ℝ)
 (h : ∀ x ∈ uIcc lo hi, has_deriv_at (λ t,a t*k t) (d x) x)
 (hd : interval_integrable d volume lo hi) :
 (∫ x in lo..hi,d x) = a hi*k hi-a lo*k lo :=
 interval_integral.integral_eq_sub_of_has_deriv_at h hd

theorem spherical_slab (r v dv dm : ℝ) (hr : r≠0)
 (h : 2*r*v*dv=1-v^2-2*dm) :
 (2+2*v^2)-4*v*(v+r*dv)=4*dm := by linear_combination -2*h

theorem exterior_invariant (r C : ℝ) (hr : r≠0) (hC : C≠0) :
 (1-C)*36/(r^2)/(C/r^2)=36*(1-C)/C :=
 by {field_simp [hr,hC]; ring}

theorem advanced_rate (s : ℝ) (h : 0≤s) (hb : s≤1) :
 1/2≤1/(1+s) := by {apply (le_div_iff (by linarith : 0<1+s)).2,linarith}

theorem signal_advantage (s v : ℝ) (hs : 0<s) (hv : 0≤v) :
 s-1/(v+1/s)=v*s^2/(1+v*s) :=
begin
 have hk : 1+v*s≠0 := (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hv hs.le)).ne',
 have eqn : v+1/s=(1+v*s)/s := by {field_simp [hs.ne'];ring},
 rw [eqn,one_div,inv_div],field_simp [hk];ring
end

theorem time_remaining (rs a b : ℝ) (h : 0<rs) (hab : b<a) :
 0<2*rs/3*(a-b) := mul_pos (by linarith) (sub_pos.mpr hab)

/-- A negative real crossing is possible only at the middle for positive radius;
the two forms use z or exp(-i theta) z. The unused branch when y=0 is explicit. -/
theorem small_cut (y C S : ℝ) (hpp : 0≤y)
 (hroot : S=0 → C=1 ∨ (C= -1 ∧ y<1)) :
 0<1+y*C ∨ y*S≠0 :=
begin
 by_cases hy:y=0, {left,rw [hy],norm_num},
 by_cases hs:S=0,
 {left,rcases hroot hs with hc|⟨hc,hm⟩; rw [hc];linarith},
 exact or.inr (mul_ne_zero hy hs)
end

theorem large_cut (y C S : ℝ) (hy : 0≤y)
 (hroot : S=0 → C=1 ∨ (C= -1 ∧ 1<y)) :
 0<C+y ∨ -S≠0 :=
begin
 by_cases hs:S=0,
 {left,rcases hroot hs with hc|⟨hc,hm⟩;rw [hc];linarith},
 exact or.inr (neg_ne_zero.mpr hs)
end

theorem factor_phase (y C S : ℝ) (h : C^2+S^2=1) :
 C*(1+y*C)+S*(y*S)=C+y ∧ C*(y*S)-S*(1+y*C)= -S :=
 ⟨by linear_combination y*h,by ring⟩

/-- An actual continuous lift on a cut-free path. Its measured increment is the degree. -/
theorem lift_continuous (z : ℝ → ℂ) (hz : continuous z)
 (h : ∀ t,0<(z t).re ∨ (z t).im≠0) (n : ℝ) :
 continuous (λ t:ℝ,n*t+complex.arg (z t)) :=
 (continuous_const.mul continuous_id).add
 (continuous_iff_continuous_at.2 (λ t,(complex.continuous_at_arg (h t)).comp hz.continuous_at))

theorem lift_increment (z : ℝ → ℂ) (a b n s e : ℝ)
 (hs : 0≤s) (he : 0≤e) (h₁ : z a=(s:ℂ)) (h₂ : z b=(e:ℂ)) :
 (n*b+complex.arg (z b))-(n*a+complex.arg (z a))=n*(b-a) :=
 by {rw [h₁,h₂,complex.arg_of_real_of_nonneg hs,complex.arg_of_real_of_nonneg he];ring}

theorem phase_velocity (y dy C S angular : ℝ) (h : C^2+S^2=1) :
 (1+y*C)*(dy*S+y*C*angular)-y*S*(dy*C-y*S*angular)=
 dy*S+(y^2+y*C)*angular := by linear_combination y^2*angular*h

theorem impedance_norm (y C S : ℝ) (h : C^2+S^2=1) :
 (1+y*C)^2+(y*S)^2=1+2*y*C+y^2 := by linear_combination y^2*h

theorem phase_threshold (y : ℝ) : (1-y)^2=0 ↔ y=1 :=
begin split, {intro h,have h' := pow_eq_zero h,linarith},
 {rintro rfl,norm_num} end

theorem rotating_gap (scale freq : ℝ) (hf : freq≠0)
 (h : 4*scale^2=5*freq^2) : freq^2/(scale^2+freq^2)=4/9 :=
begin
 have hp : 0 < scale^2+freq^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero _ hf),
 field_simp [hp.ne'], linarith
end

/-- Finite compact support reduces the full causal periodization to a telescoping sum. -/
theorem periodized_difference (f : ℕ → ℝ) (N : ℕ) :
 ∑ j in finset.range N,(f (j+1)-f j)=f N-f 0 :=
begin induction N with N ih, {simp}, {rw [finset.sum_range_succ,ih];ring} end

theorem filtered_current (f : ℕ → ℝ) (N : ℕ) (T n : ℝ) (h : f N-f 0=2*real.pi*n) :
 ∑ j in finset.range N,(f (j+1)-f j)/T=2*real.pi*n/T :=
by rw [←finset.sum_div,periodized_difference,h]

/-- The retarded box average only needs a logarithmic derivative on its past circuit. -/
theorem delayed_slope (I : ℝ → ℝ) (omega p q T x : ℝ)
 (h : has_deriv_at I (omega-(p-q)/T) x) (phase : ℝ → ℝ)
 (hp : has_deriv_at phase omega x) :
 has_deriv_at (λ s,phase s-I s) ((p-q)/T) x :=
 by {convert hp.sub h using 1;ring}

theorem average_of_lift (F phi : ℝ→ℝ) (x T : ℝ)
 (hx : has_deriv_at F (phi x) x) (hp : has_deriv_at F (phi (x-T)) (x-T)) :
 has_deriv_at (λ t:ℝ,(F t-F (t-T))/T) ((phi x-phi (x-T))/T) x :=
begin
 have shift : has_deriv_at (λ t:ℝ,t-T) 1 x :=
 by simpa using (has_deriv_at_id x).sub (has_deriv_at_const x T),
 simpa only [mul_one,function.comp_app] using (hx.sub (hp.comp x shift)).div_const T
end

/-- Phase modulus permits converting a cut-free argument into a unitary seam. -/
theorem normalized_arg (z : ℂ) (h : z≠0) :
 complex.exp ((complex.arg z:ℂ)*complex.I)=z/(complex.abs z:ℂ) :=
begin
 apply (eq_div_iff _).2,
 {rw [mul_comm,complex.abs_mul_exp_arg_mul_I]},
 {exact_mod_cast (complex.abs.pos h).ne'}
end

theorem neutral_vector (n initialR initialL : ℤ) :
 (initialR+n)+(initialL-n)=initialR+initialL ∧
 (initialR+n)-(initialL-n)-(initialR-initialL)=2*n := ⟨by ring,by ring⟩

theorem uniform_is_minimal (g : ℝ → ℝ) (c T : ℝ)
 (hm : (∫ x in 0..T, g x)=T*c)
 (h : interval_integrable g volume 0 T)
 (hs : interval_integrable (λ x,g x^2) volume 0 T) :
 (∫ x in 0..T,(g x-c)^2)=(∫ x in 0..T,g x^2)-T*c^2 :=
begin
 have fun_eq : (λ x,(g x-c)^2)=(λ x,g x^2-(2*c)*g x+c^2) := funext (λ x,by ring),
 rw [fun_eq,interval_integral.integral_add (hs.sub (h.const_mul _)) interval_integrable_const,
     interval_integral.integral_sub hs (h.const_mul _),interval_integral.integral_const_mul,
     hm],dsimp only,rw [interval_integral.integral_const],simp only [sub_zero,smul_eq_mul],ring
end

theorem unique_box {ι : Type*} (k : ι → ℝ) (T : ℝ) (hT : T≠0)
 (h : ∀ i,T*k i=1) : ∀ i,k i=1/T :=
λ i,(eq_div_iff hT).2 (by simpa [mul_comm] using h i)

theorem sea_energy (n : ℕ) :
 2*(∑ j in finset.range n,((j:ℝ)+(1:ℝ)/2))=(n:ℝ)^2 :=
begin
 induction n with n ih,
 {simp}, {rw [finset.sum_range_succ,nat.cast_succ],linear_combination ih}
end

theorem geometric_work (x : ℝ) (hx : 1-x ≠ 0) :
 1+x/(2*(1-x))=(2-x)/(2*(1-x)) := by {field_simp [hx];ring}

theorem neutral_gap (remaining emitted gap : ℝ) (he : 0<emitted)
 (h : remaining+emitted=gap) (spectrum : remaining=0 ∨ gap≤remaining) :
 remaining=0 := spectrum.elim id (λ h',false.elim (by linarith))

theorem compressing_pressure (r e A p : ℝ) (hr : r≠0) (hA : A≠0)
 (h : -(e/r) = -p*(2*A/r)) : p=e/(2*A) :=
begin
 have eqn : e=p*(2*A) := by {field_simp [hr] at h;linarith},
 apply (eq_div_iff (mul_ne_zero (by norm_num: (2:ℝ)≠0) hA)).2,linarith
end

theorem shell_root (B D m k r : ℝ) (hr : r≠0) (hk : k≠0)
 (h : B-D=k/r^2) (g : B^2-D^2=2*m/r) :
 B=m*r/k+k/(2*r^2) :=
begin
 have h' : (B+D)*(k/r^2)=2*m/r := by {rw [←h];linear_combination g},
 field_simp [hr] at h h',field_simp [hk,hr],
 linear_combination k*h+r*h'
end

theorem stationary_shell (r m k : ℝ) (hk : k≠0) (hr : r≠0)
 (energy : m*r/k+k/(2*r^2)=1) (force : m/k-k/r^3=0) :
 r^2=3*k/2 ∧ m=4*r/9 :=
begin
 field_simp [hk,hr] at energy force,
 have h : k*(3*k-2*r^2)=0 := by linear_combination energy-2*force,
 have h' := (mul_eq_zero.mp h).resolve_left hk,
 have hj : (9*m-4*r)*r^3=0 :=
   by linear_combination 9*force+(3*k+2*r^2)*h',
 have h'' := (mul_eq_zero.mp hj).resolve_right (pow_ne_zero 3 hr),
 exact ⟨by linarith,by linarith⟩
end

theorem instability (r k : ℝ) (hr : r≠0) (h : r^2=3*k/2) :
 3*k/r^4=2/r^2 := by {field_simp [hr];linear_combination -2*r^2*h}

theorem diagonal_stress (a q b : ℂ) (h : q*a=b*a) (e : q≠b) : a=0 :=
begin
 have h' : (q-b)*a=0 := by linear_combination h,
 exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr e)
end

theorem invisible_centre (a : ℂ) (intertwines : -a=a) : a=0 := by linear_combination -(1/2:ℂ)*intertwines

theorem two_graviton_primitive (x : ℝ) :
 has_deriv_at (λ t:ℝ,t^6/6-5*t^7/7+10*t^8/8-10*t^9/9+5*t^10/10-t^11/11)
 (x^5*(1-x)^5) x :=
begin
 convert ((((((has_deriv_at_pow 6 x).div_const 6).sub
   (((has_deriv_at_pow 7 x).const_mul 5).div_const 7)).add
   (((has_deriv_at_pow 8 x).const_mul 10).div_const 8)).sub
   (((has_deriv_at_pow 9 x).const_mul 10).div_const 9)).add
   (((has_deriv_at_pow 10 x).const_mul 5).div_const 10)).sub
   ((has_deriv_at_pow 11 x).div_const 11) using 1,
 norm_num;ring
end

theorem two_graviton_normalization :
 (∫ x:ℝ in 0..1,x^5*(1-x)^5)=1/2772 :=
begin
 have v:=interval_integral.integral_eq_sub_of_has_deriv_at
  (λ x (hx:x∈uIcc (0:ℝ) 1),two_graviton_primitive x)
  (((continuous_id.pow 5).mul ((continuous_const.sub continuous_id).pow 5)).interval_integrable 0 1),
 norm_num at v ⊢,exact v
end

theorem finite_optical_depth (a r : ℝ) (hr : r≠0) :
 has_deriv_at (λ s:ℝ,-a/(2*s^2)) (a/r^3) r :=
begin
 have h := (has_deriv_at_const r (-a)).div ((has_deriv_at_pow 2 r).const_mul 2)
   (mul_ne_zero (by norm_num : (2:ℝ)≠0) (pow_ne_zero 2 hr)),
 convert h using 1, field_simp [hr];ring
end

theorem surviving_flag (depth : ℝ) : 0<real.exp (-depth) := real.exp_pos _

/-- If every one-circuit input tests only its mean, the response kernel is
constant almost everywhere. The measure here may be restricted to one circuit. -/
theorem response_unique_ae {α : Type*} [measurable_space α] (μ : measure α)
 (k : α → ℝ) (c : ℝ) (hi : integrable (λ x,(k x-c)^2) μ)
 (h : ∀ f : α→ℝ, integrable (λ x,(k x-c)*f x) μ →
    (∫ x,(k x-c)*f x ∂μ)=0) : k=ᵐ[μ] (λ x,c) :=
begin
 have test := h (λ x,k x-c) (by simpa only [pow_two] using hi),
 have hn : 0 ≤ᵐ[μ] (λ x:α,(k x-c)^2) := filter.eventually_of_forall (λ x:α,show 0≤(k x-c)^2, from sq_nonneg _),
 have z := (integral_eq_zero_iff_of_nonneg_ae hn hi).1
   (by simpa only [pow_two] using test),
 filter_upwards [z] with x hx,
 exact sub_eq_zero.mp (pow_eq_zero (show (k x-c)^2=0,from hx))
end

theorem outward_branch_budget (D m k r : ℝ) (hd : 0≤D) (hk : 0<k) (hr : 0<r)
 (h : D=m*r/k-k/(2*r^2)) : k^2≤2*m*r^3 :=
begin
 have hv : D*(2*r^2*k)=2*m*r^3-k^2 := by {rw [h];field_simp [hr.ne',hk.ne'];ring},
 have hj := mul_nonneg hd (show 0≤2*r^2*k,by positivity),linarith
end

theorem exterior_cap (k r m : ℝ) (hr : 0≤r) (h : k^2≤2*m*r^3)
 (hC : 2*m≤r) : k^2≤r^4 :=
calc k^2≤2*m*r^3 : h
 ... ≤r*r^3 : mul_le_mul_of_nonneg_right hC (pow_nonneg hr _)
 ... =r^4 : by ring

theorem cap_area (C S : ℝ) (h : C^2+S^2=1) :
 S^2≤2*(1-C) := by nlinarith [sq_nonneg (1-C)]

theorem cap_tangent (f u : ℝ) (hf : 0<f) (hu : 0<u) :
 3/(2*u)-f^2/(2*u^3)≤1/f :=
begin
 have h := mul_nonneg (sq_nonneg (f-u)) (show 0≤f+2*u,by linarith),
 have eqn : 1/f-(3/(2*u)-f^2/(2*u^3))=(f-u)^2*(f+2*u)/(2*u^3*f) :=
 by {field_simp [hf.ne',hu.ne'];ring},
 have hd := div_nonneg h (show 0≤2*u^3*f,by positivity),linarith
end

theorem cap_packing (J : ℕ) (f : fin J → ℝ) (u : ℝ) (hu : 0<u)
 (hf : ∀ i,0<f i) (hspace : ∑ i,f i^2≤4) (hmean : (J:ℝ)*u^2=4) :
 (J:ℝ)/u≤∑ i,1/f i :=
begin
 have term : ∀ i,3*u^2-f i^2≤2*u^3*(1/f i) := λ i,begin
   have eqn : 3*u^2-f i^2=(2*u^3)*(3/(2*u)-f i^2/(2*u^3)) :=
   by {field_simp [hu.ne'];ring},
   rw [eqn],exact mul_le_mul_of_nonneg_left (cap_tangent _ _ (hf i) hu) (by positivity)
 end,
 have h : (∑ i, (3*u^2-f i^2)) ≤ ∑ i,2*u^3*(1/f i) := finset.sum_le_sum (λ i hi,term i),
 have collect : (∑ i,2*u^3*(1/f i))=(2*u^3)*(∑ i,1/f i) := by rw [finset.mul_sum],
 rw [finset.sum_sub_distrib,collect,finset.sum_const,finset.card_univ,
     fintype.card_fin,nsmul_eq_mul] at h,
 apply (div_le_iff hu).2,
 apply (mul_le_mul_right (pow_pos hu 2)).1,
 nlinarith only [h,hmean,hspace]
end

theorem barotropic_rest_energy (w eta wprime : ℝ) (h : wprime= -2*(1+w)*(eta-w)) :
 -2*wprime+4*w^2+2*w=4*(1+w)*eta-2*w := by {rw [h];ring}

theorem shell_sound_response (eta : ℝ) :
 (2:ℝ)/3*(8*(1/2)^2-(4*(1+1/2)*eta-2*(1/2)))+
 (1:ℝ)/3*((4*(1+1/2)*eta-2*(1/2))+4*(1/2)+2)=3-2*eta := by ring

theorem no_causal_stall (eta : ℝ) (h : eta≤1) : 0<3-2*eta := by linarith

theorem inflow_level (k : ℤ) (h : k*1=1-(-1)) : k=2 := by linarith

theorem no_source_no_winding (k n : ℤ) (hk : k≠0) (h : k*n=0) : n=0 :=
 (mul_eq_zero.mp h).resolve_left hk

theorem dressed_flip (s : ℤ) : (-2)-2*s=0 ↔ s= -1 := by split; intro h;linarith

theorem charged_survival (rate₁ rate₂ : ℝ) :
 0<real.exp (-rate₁)*real.exp (-rate₂) := mul_pos (real.exp_pos _) (real.exp_pos _)

/-- Proper-time energy flux on a moving timelike boundary in outgoing coordinates. -/
theorem retarded_flux (mprime kprime R z : ℝ) (hz : z≠0)
 (h : kprime/R=mprime*(1/z)^2) : mprime=(kprime/R)*z^2 :=
by {rw [h];field_simp [hz];ring}

theorem moving_mass (q B v dk a : ℝ) (hv : v≠0) (hq : q≠0) (hB : B≠0)
 (h : (B-q)*dk+q*v*a/B-q*B*v+3*q^2*v/2=dk*(B-q+v)) :
 a=B*(dk/q+B-3*q/2) :=
begin
 have hv' : v*(q*a-q*B^2+3*q^2*B/2-dk*B)=0 := by
 {field_simp [hB] at h,linear_combination h/2},
 have hj := (mul_eq_zero.mp hv').resolve_left hv,
 field_simp [hq],linear_combination 2*hj
end

theorem radiating_root (B s : ℝ) :
 B-2*(B-2*s)/3-s=(B+s)/3 := by ring

theorem constant_shell_speed (B s : ℝ) :
 B*(-2*s+B-3*(2*(B-2*s)/3)/2)=0 := by ring

theorem radiating_branch_mass (B s q : ℝ) (h : q=2*(B-2*s)/3) :
 B*q-q^2/2 = 2*q*((B+s)/3) := by {rw [h];ring}

theorem positive_shell (B s : ℝ) (hB : 0<B) (hs : 0<s) (hu : 3*s^2<1)
 (h : B^2=1+s^2) : 0<2*(B-2*s)/3 :=
begin
 have hpos : 0<B+2*s := by linarith,
 have hmul : 0<(B-2*s)*(B+2*s) := by nlinarith,
 have hx : 0<B-2*s := lt_of_not_ge (λ hn,(not_le_of_gt hmul) (mul_nonpos_of_nonpos_of_nonneg hn hpos.le)),
 linarith
end

theorem radiated_mass (C s z R : ℝ) (hs : s≠0) (hz : z≠0) :
 C*s*z/2*(R/(s*z))=C*R/2 := by {field_simp [hs,hz];ring}

theorem curvature_on_tube (C R : ℝ) (hR : R≠0) :
 48*(C*R/2)^2/R^6=12*C^2/R^4 := by {field_simp [hR];ring}

theorem packed_power (X f gamma q z fill : ℝ) (hf : f≠0)
 (hl : fill≠0) (h : q*f^3=fill*X) :
 (gamma*q*z^2*X^2/f^5)*f^2=gamma*q^2*z^2*X/fill :=
begin
 field_simp [hl,hf],linear_combination -gamma*q*z^2*X*f^2*h
end

theorem finite_packing_conflict (f X q C : ℝ) (hf : 0<f)
 (hscale : X=C*f^5) (hpack : q*f^3≤4*X) : q≤4*C*f^2 :=
begin
 apply (mul_le_mul_right (pow_pos hf 3)).1,
 rw [hscale] at hpack,
 nlinarith only [hpack]
end

theorem unique_geometric_power (d : ℝ) :
 2+(2*d-5)/3=1 ↔ d=1 := by split; intro h;linarith

theorem hard_member (a b total : ℝ) (h : a+b=total) : total/2≤a ∨ total/2≤b :=
by {by_cases ha : total/2≤a,exact or.inl ha,right,linarith}

theorem cascade_multiplicity (n : ℕ) (freq : fin n→ℝ) (H : ℝ)
 (bound : ∀ i,freq i≤H) : ∑ i,freq i≤(n:ℝ)*H :=
begin
 have h: (∑ i,freq i) ≤ ∑ i:fin n,H := finset.sum_le_sum (λ i hi,bound i),
 simpa only [finset.sum_const,finset.card_univ,fintype.card_fin,nsmul_eq_mul] using h
end

end gravitational_charge_cycle
