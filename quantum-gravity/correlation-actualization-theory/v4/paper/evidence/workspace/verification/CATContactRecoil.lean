import tactic
import analysis.special_functions.trigonometric.basic
import analysis.inner_product_space.basic

namespace cat_contact_recoil
noncomputable theory
open_locale big_operators

-- Reduced inverse mass of j*w_L + d - x_L, including all three kinetic terms.
theorem normal_mass (j g : ℝ) (hj : 0 < j) (hg : 0 < g) :
 g*(j^2/((2*j+1)*j*(j+1)) + 1/(2*j+1) + 1) =
 g*(j+2)/(j+1) :=
begin
 have h₁ : 2*j+1 ≠ 0 := by linarith,
 have h₂ : j+1 ≠ 0 := by linarith,
 field_simp [h₁,h₂,ne_of_gt hj]; ring
end

theorem kinetic_split (a b c v : ℝ) (orth : b=0) :
 a+2*v*b+v^2*c=a+v^2*c := by rw [orth]; ring

theorem opposite_impulse (force : ℝ) : (-1)*force+1*force=0 := by ring

def pinch {A : Type*} [ring A] (p h : A) := p*h*p+(1-p)*h*(1-p)

theorem pinch_left {A : Type*} [ring A] (p h : A) (hp : p*p=p) :
 p*(pinch p h)=p*h*p :=
begin
 have u : p*(1-p)=0 := by rw [mul_sub,mul_one,hp,sub_self],
 unfold pinch, rw [mul_add,←mul_assoc,←mul_assoc p p h,hp,←mul_assoc p,←mul_assoc p (1-p),u,zero_mul,zero_mul,add_zero]
end

theorem pinch_right {A : Type*} [ring A] (p h : A) (hp : p*p=p) :
 (pinch p h)*p=p*h*p :=
begin
 have u : (1-p)*p=0 := by rw [sub_mul,one_mul,hp,sub_self],
 unfold pinch, rw [add_mul,mul_assoc (p*h),hp,mul_assoc ((1-p)*h),u,mul_zero,add_zero]
end

theorem transparent_iff_commutes {A : Type*} [ring A] (p h : A) (hp : p*p=p) :
 pinch p h=h ↔ p*h=h*p :=
begin
 split,
 { intro e, calc p*h=p*(pinch p h) : by rw [e]
    ... = p*h*p : pinch_left p h hp
    ... = (pinch p h)*p : (pinch_right p h hp).symm
    ... = h*p : by rw [e] },
 { intro e, have v : p*h*p=h*p := by rw [e,mul_assoc,hp],
   calc pinch p h = h - h*p-p*h + (p*h*p+p*h*p) : by {unfold pinch, noncomm_ring}
    ... = h : by {rw [v,e], abel} }
end

theorem reflected_matching {A : Type*} [ring A] (k d a r : A)
 (match_eq : k*(a-r)=d*(a+r)) :
 (k+d)*r=(k-d)*a :=
begin
 rw [mul_sub,mul_add] at match_eq, rw [add_mul,sub_mul],
 calc k*r+d*r=(k*a-(k*a-k*r))+d*r : by abel
  ... = k*a-d*a : by rw [match_eq]; abel
end

theorem common_trace {A : Type*} [ring A] (k d a r : A)
 (match_eq : (k+d)*r=(k-d)*a) : (k+d)*(a+r)=k*a+k*a :=
by rw [mul_add,match_eq,add_mul,sub_mul]; abel

theorem square_intertwines {A : Type*} [ring A] (k p : A) (h : k*p=p*k) :
 k*k*p=p*(k*k) := by rw [mul_assoc,h,←mul_assoc,h,mul_assoc]

-- Current balance follows from the same trace map on values and time derivatives.
theorem current_balance {L R : Type*} [add_comm_group L] [add_comm_group R]
 (pairL : L → L → ℝ) (pairR : R → R → ℝ) (v : L → R) (adj : R → L)
 (pairing : ∀ a b, pairR (v a) b=pairL a (adj b))
 (odd : ∀ a b, pairL a (-b)= -pairL a b)
 (a x : L) (y : R) (matching : adj y= -x) :
 pairL a x+pairR (v a) y=0 := by rw [pairing,matching,odd]; ring

theorem local_schrodinger_energy (u v ux vx ut vt uxx vxx uxt vxt inv h : ℝ)
 (real_eom : -vt= -inv*uxx+h*u) (imag_eom : ut= -inv*vxx+h*v) :
 (2*inv*(ux*uxt+vx*vxt)+2*h*(u*ut+v*vt))
  -2*inv*(ut*uxx+vt*vxx+ux*uxt+vx*vxt)=0 :=
by linear_combination (2*ut)*(-real_eom)+(2*vt)*(-imag_eom)

theorem shell_recoil (e hi hf : ℝ) : (hf-hi)+((e-hf)-(e-hi))=0 := by ring

theorem wave_flux_balance (u v a b : ℂ) :
 (star (u+v)*(v-u)).re + (star a*b).re =
  (star v*v).re-(star u*u).re+(star a*b).re :=
by {simp [complex.mul_re,complex.add_re,complex.sub_re,complex.add_im,complex.sub_im];ring}

-- At threshold, a null vector of a positive sum must satisfy each constraint.
theorem common_kernel (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
 a+b+c=0 ↔ a=0 ∧ b=0 ∧ c=0 :=
begin split, {intro h, exact ⟨by linarith,by linarith,by linarith⟩},
 {rintro ⟨rfl,rfl,rfl⟩,ring} end

theorem ground_fragmentation (q : ℝ) (lo : 0 < q) (hi : q < 1) : q*q ≠ q :=
by intro h; nlinarith [mul_pos lo (sub_pos.mpr hi)]

theorem small_transmission (k bound t : ℝ) (hk : 0 ≤ k) (hb : 0 ≤ bound)
 (hlo : -(k*bound) ≤ t) (hhi : t ≤ k*bound) : t^2 ≤ k^2*bound^2 :=
by nlinarith [mul_nonneg (sub_nonneg.mpr hhi) (show 0 ≤ k*bound+t, by linarith)]

-- The value of an isolated outgoing sheet must vanish at the contact if the
-- projected state is to obey the finite-energy form-domain trace condition.
theorem trace_after_selection {L R : Type*} [add_comm_group L] [add_comm_group R]
 (v : L →+ R) (a : R) (finite_trace : a=v 0) : a=0 := by simpa using finite_trace

def joined {M : Type*} [add_comm_group M] (p : M →+ M) (incoming written empty : M) : Prop :=
 written=p incoming ∧ empty=incoming-p incoming

theorem sharp_sheet_trace_iff {M : Type*} [add_comm_group M] (p : M →+ M) (a b c : M)
 (joint : joined p a b c) :
 (joined p (0:M) b 0 ∧ joined p a 0 c) ↔ b=0 :=
begin
 rcases joint with ⟨hb,hc⟩,
 split,
 { rintro ⟨⟨h,_⟩,_⟩, simpa using h },
 { intro h, have hp : p a=0 := hb.symm.trans h,
   unfold joined, simp [h,hp,hc] }
end

theorem vanishing_positive_form (x y : ℝ) : x^2+y^2=0 ↔ x=0 ∧ y=0 :=
begin split, {intro h, exact ⟨by nlinarith [sq_nonneg y,sq_nonneg x],by nlinarith [sq_nonneg y,sq_nonneg x]⟩},
 {rintro ⟨rfl,rfl⟩,ring} end

theorem regularized_work (f g df dg u du : ℝ) (normal : f^2+g^2=1)
 (tangent : f*df+g*dg=0) :
 (f*du+df*u)^2+(g*du+dg*u)^2-du^2=(df^2+dg^2)*u^2 :=
by linear_combination du^2*normal+2*u*du*tangent

theorem angle_cost (a d : ℝ) :
 ((real.cos a)*d)^2+((-real.sin a)*d)^2=d^2 :=
begin
 calc (real.cos a*d)^2+(-real.sin a*d)^2=(real.sin a^2+real.cos a^2)*d^2 : by ring
  ... =d^2 : by rw [real.sin_sq_add_cos_sq,one_mul]
end

theorem local_cost_bound (m a b theta : ℝ) (hm : 0<m) (hb : 0<b)
 (cs : theta^2 ≤ a*b) : theta^2/(2*m*b) ≤ a/(2*m) :=
begin
 have h₂ : 0<2*m := by linarith,
 apply (div_le_div_iff (mul_pos h₂ hb) h₂).2,
 nlinarith only [mul_le_mul_of_nonneg_right cs h₂.le]
end

theorem positive_momenta_negative_current (b k₁ k₂ : ℝ) (hb : b<1)
 (interference : k₁<b*k₂) : (1-b)*(k₁-b*k₂)<0 :=
mul_neg_of_pos_of_neg (sub_pos.mpr hb) (sub_neg.mpr interference)

-- Classical randomization of a broader variance ratio into an intermediate one.
theorem gaussian_noise_comparison (r t : ℝ) :
 t*r+(1-t)*1=1+t*(r-1) := by ring

theorem pair_tag (a b c d : ℝ) : (a*b)*(c*d)=(a*c)*(b*d) := by ring

theorem deficit_rationalization (x t : ℝ) (ht : 0 ≤ t) (h : t^2=1-x) :
 (1-t)/2=x/(2*(1+t)) :=
begin have z : 1+t≠0 := by linarith, field_simp [z]; nlinarith end

theorem finite_variance_heading (a b : ℝ) (ha : 0<a) (hb : 0<b) :
 0<(a*b) := mul_pos ha hb

theorem density_mismatch (x y d : ℝ) :
 (x+y)^2-4*x*y*d=(x-y)^2+4*x*y*(1-d) := by ring

theorem stack_mass (j k g : ℝ) (hj : 0<j) (hk : 0<k) (hg : 0<g) :
 (k*(j+1)/(g*(k+j+1)))*(g*(1/(j+1)+1/k))=1 :=
begin
 have a : j+1 ≠0 := by linarith, have b : k+j+1≠0 := by linarith,
 field_simp [a,b,ne_of_gt hk,ne_of_gt hg];ring
end

theorem reduced_mass_cap (j k g : ℝ) (hj : 0<j) (hk : 0<k) (hg : 0<g) :
 k*(j+1)/(g*(k+j+1)) ≤ (j+1)/g :=
begin
 have h : 0<k+j+1 := by linarith,
 apply (div_le_div_iff (mul_pos hg h) hg).2,
 nlinarith only [mul_nonneg (sq_nonneg (j+1)) hg.le]
end

theorem localized_adiabatic_bound (m gap width dp rms : ℝ) (hm : 0<m)
 (hg : 0<gap) (hd : 0≤dp) (hx : width≤gap) (heis : 1≤2*width*dp)
 (pr : dp≤rms) :
 1/(8*m*gap^3) ≤ rms/(4*m*gap^2) :=
begin
 have h₁ : 1≤2*gap*rms := by nlinarith [mul_nonneg (sub_nonneg.mpr hx) hd,
                                    mul_nonneg hg.le (sub_nonneg.mpr pr)],
 have pos₁ : 0<8*m*gap^3 := by positivity,
 have pos₂ : 0<4*m*gap^2 := by positivity,
 apply (div_le_div_iff pos₁ pos₂).2,
 nlinarith only [mul_le_mul_of_nonneg_left h₁ (le_of_lt pos₂)]
end

theorem resonant_rank_scaling (n g energy : ℝ) (hn : 0<n) (hg : 0<g) :
 (n/g)*(energy/(2*n))^3=energy^3/(8*g*n^2) :=
begin field_simp [ne_of_gt hn,ne_of_gt hg];ring end

theorem two_level_projector_metric (s g : ℝ) :
 (g^2)^2+(s*g)^2=g^2*(s^2+g^2) := by ring

theorem independent_holes (n : ℕ) (v : ℝ) :
 (∑ i : fin n, v^2)=(n:ℝ)*v^2 := by simp

theorem collective_power (n a : ℝ) (h : n≠0) :
 (n^2*(a/n^2)=a) ∧ (n*(a/n^2)=a/n) :=
by {split;field_simp [h];ring}

theorem comoving_extreme (j w d : ℝ) :
 j*w+(j-1)*(-w)+d=w+d := by ring

theorem adjacent_block (j z : ℝ) :
 z*(z+1)*(z-1)-(2*j)*(z-1)-(2*(j-1))*(z+1)=z^3-(4*j-1)*z+2 := by ring

theorem small_root_bracket (d z : ℝ) (hz : 0<z) (ltone : z<1)
 (high : (d-1)*z=2) : z^3-d*z+2<0 :=
begin
 have h : z^2 < 1 := by nlinarith [mul_pos (sub_pos.mpr ltone) (show 0<1+z, by linarith)],
 nlinarith [mul_pos hz (sub_pos.mpr h)]
end

theorem small_root_lower (d z : ℝ) (hz : 0<z) (low : d*z=2) :
 0<z^3-d*z+2 := by rw [low];nlinarith [pow_pos hz 3]

theorem isolated_transfer_speed (a err gap duration : ℝ)
 (he : 0≤err) (hd : err ≤ gap*duration) (ha : |a| ≤ err) :
 a^2 ≤ (gap*duration)^2 :=
begin
 have p := (abs_le.mp (le_trans ha hd)),
 nlinarith [mul_nonneg (sub_nonneg.mpr p.2) (show 0≤gap*duration+a, by linarith [p.1])]
end

end cat_contact_recoil
