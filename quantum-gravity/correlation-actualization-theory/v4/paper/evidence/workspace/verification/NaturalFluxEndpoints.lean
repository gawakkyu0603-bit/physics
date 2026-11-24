import analysis.special_functions.log.deriv
import analysis.special_functions.pow.real
import analysis.special_functions.integrals
import measure_theory.integral.bochner
import measure_theory.group.integration
import measure_theory.measure.lebesgue.basic
import analysis.special_functions.trigonometric.bounds
import tactic

noncomputable theory
open measure_theory
open_locale big_operators
namespace natural_flux_endpoints

-- Mixed transgression of the normalized M-theory cubic on three degree-four
-- factors with vanishing squares; they commute since the degrees are even.
theorem mixed_cubic {K : Type*} [comm_ring K] (a b c : K)
 (ha : a^2=0) (hb:b^2=0) (hc:c^2=0) : (a+b+c)^3=6*a*b*c :=
calc (a+b+c)^3=a^2*(a+3*b+3*c)+b^2*(b+3*a+3*c)+c^2*(c+3*a+3*b)+6*a*b*c : by ring
 ... =6*a*b*c : by rw [ha,hb,hc];ring
theorem flux_lift (a n l : ℝ) : (a-l)+(n+l)=a+n := by ring
theorem closed_pair (bulk da_dB dA_b a_dB left right : ℝ)
 (he:da_dB=0) (hl:dA_b=left) (hr:a_dB= -right) :
 bulk+da_dB+dA_b+a_dB=bulk+left-right := by rw [he,hl,hr];ring
theorem sheet_and_end (sheet left right u v : ℝ) :
 (sheet+u-v)+(left-u)-(right-v)=sheet+left-right := by ring
theorem half_source (k m : ℤ) : 2*k+m=0 ↔ m= -2*k := by split;intro h;linarith
theorem odd_source_unscreened (k s : ℤ) : 2*k+(2*s+1)≠0 :=
begin intro h,omega end
theorem doubled_screen (s : ℤ) : 2*(-s)+2*s=0 := by ring
theorem gauge_relabel (k p chi t : ℝ) : (k-p*t)+p*(chi+t)=k+p*chi := by ring
theorem connection_basis (k p chi A C : ℝ) : k*A+p*(C+chi*A)=(k+p*chi)*A+p*C := by ring
theorem shifted_flux_trace (a b y : ℝ) (ha:a≠0) (hb:b≠0) :
 (y*b/a)*(y*a/b)=y^2 := by field_simp [ha,hb];ring
theorem projectors_one_wave {K : Type*} [ring K] (P Q : K)
 (hP : P*P=1) (hQ:Q*Q=1) (h:P*Q+Q*P=0) :
 (P+Q)*(P+Q)=2 :=
begin
 rw [add_mul,mul_add,mul_add,hP,hQ],
 calc 1+P*Q+(Q*P+1) = (1+1)+(P*Q+Q*P) : by abel
 ... = 2 : by rw [h];norm_num
end

-- Both specified Page polarizations. Extra polarizations need not be half.
theorem inverse_block_det (u v s : ℝ) : -(u*v)-s^2= -(u*v+s^2) := by ring
theorem positive_dual_range (y : ℝ) (hy:0<y) :
 0< (1/2:ℝ)/(1/4+y^2) ∧ (1/2:ℝ)/(1/4+y^2)<2 :=
begin have h : 0 < 1/4+y^2 := by positivity,
 split,{exact div_pos (by norm_num) h},{rw [div_lt_iff h],nlinarith [sq_pos_of_pos hy]} end
theorem dual_half (y : ℝ) (hy:0<y) (k : ℤ)
 (h : (1/2:ℝ)/(1/4+y^2)=(k:ℝ)+1/2) :
 (k=0 ∧ y^2=3/4) ∨ (k=1 ∧ y^2=1/12) :=
begin
 rcases positive_dual_range y hy with ⟨lo,hi⟩,rw [h] at lo hi,
 have h0 : (-1:ℤ)<k := by exact_mod_cast (show (-1:ℝ)<(k:ℝ),by linarith),
 have h2 : k<(2:ℤ) := by exact_mod_cast (show (k:ℝ)<(2:ℝ),by linarith),
 have hden : (1/4+y^2:ℝ)≠0 := by positivity,
 have hh := (div_eq_iff hden).mp h,
 rcases show k=0 ∨ k=1,by omega with rfl|rfl,
 {left,refine ⟨rfl,_⟩,push_cast at hh,linear_combination (-2)*hh},
 {right,refine ⟨rfl,_⟩,push_cast at hh,linear_combination (-(2/3:ℝ))*hh}
end
theorem dual_orbit (x y : ℝ) (hx:x=1/2) (hy:y^2=1/12) :
 2-x/(x^2+y^2)=1/2 ∧ (y/(x^2+y^2))^2=3/4 :=
begin subst x,rw [hy],norm_num,field_simp; nlinarith only [hy] end
theorem other_frame : (((1:ℝ)/2)+2)/(1+4*(1/2)+4)=5/14 := by norm_num
theorem other_frame_outside : (0:ℝ)<5/14 ∧ (5:ℝ)/14<1/2 := by norm_num
theorem modular_contract (c x a : ℝ) (ha:0<a) (hx:0≤x) (hc:2≤c) :
 (x+c*a)/(1+2*c*x+c^2*a)<1/2 :=
begin have hp : 0<1+2*c*x+c^2*a := by positivity,
 rw [div_lt_iff hp], have hh : 0≤(c-2)*c*a :=
 mul_nonneg (mul_nonneg (sub_nonneg.mpr hc) (by linarith)) ha.le,
 have hh' : 0≤(c-1)*x := mul_nonneg (by linarith) hx,nlinarith end

-- A normalized, conserved oriented triangle of BPS masses.
theorem three_neutral (n m k : ℤ) : n-m=0 ∧ m-k=0 ↔ n=m ∧ m=k :=
by split;rintro ⟨a,b⟩;split;linarith
theorem neutral_counterexample (n : ℤ) : n*1+n*(-1)=0 := by ring
theorem determinant_square (x y A B : ℝ) (ha:A^2=x^2+y^2)
 (hb:B^2=(1-x)^2+y^2) :
 (A*B)^2-(x*(1-x)+y^2)^2=y^2*(2*x-1)^2 :=
by rw [mul_pow,ha,hb];ring
theorem triangle_dot (x y A B : ℝ) (ha:0≤A) (hb:0≤B)
 (sa:A^2=x^2+y^2) (sb:B^2=(1-x)^2+y^2) : x*(1-x)+y^2≤A*B :=
begin by_contra h, push_neg at h,
 have hn : 0≤A*B := mul_nonneg ha hb,
 have ht : 0<(x*(1-x)+y^2-A*B)*(x*(1-x)+y^2+A*B) :=
 mul_pos (by linarith) (by linarith),
 have hd := determinant_square x y A B sa sb,
 have hp : 0≤y^2*(2*x-1)^2 := mul_nonneg (sq_nonneg _) (sq_nonneg _),
 nlinarith only [ht,hd,hp] end
theorem triangle_midpoint (x y A B : ℝ) (ha:0≤A) (hb:0≤B)
 (sa:A^2=x^2+y^2) (sb:B^2=(1-x)^2+y^2) : 1+4*y^2≤(A+B)^2 :=
begin
 have hi : (A+B)^2-(1+4*y^2)=2*(A*B-(x*(1-x)+y^2)) := by linear_combination sa+sb,
 refine (sub_nonneg.mp (_ : 0 ≤ (A+B)^2-(1+4*y^2))),rw [hi],exact mul_nonneg (by norm_num) (sub_nonneg.mpr (triangle_dot x y A B ha hb sa sb))
end
theorem midpoint_unique (x y A B : ℝ) (hy:y≠0)
 (sa:A^2=x^2+y^2) (sb:B^2=(1-x)^2+y^2) (h:(A+B)^2=1+4*y^2) : x=1/2 :=
begin
 have he : A*B=x*(1-x)+y^2 := by linear_combination (h-sa-sb)/2,
 have d:=determinant_square x y A B sa sb,rw [he,sub_self] at d,
 have hs := (mul_eq_zero.mp d.symm).resolve_left (pow_ne_zero 2 hy),
 have hv : 2*x-1=0 := pow_eq_zero hs,linear_combination hv/2 end
theorem triangle_excess (t : ℝ) :
 (1+t)^3-27*(t-1)=(t-2)^2*(t+7) := by ring
theorem best_height (t : ℝ) (ht:1<t) :
 108 ≤ 4*(1+t)^3/(t-1) :=
begin rw [le_div_iff (sub_pos.mpr ht)],
 have hp:0≤(t-2)^2*(t+7) := mul_nonneg (sq_nonneg _) (by linarith),
 nlinarith only [hp,triangle_excess t] end
theorem best_height_unique (t : ℝ) (ht:1<t) (h:4*(1+t)^3/(t-1)=108) : t=2 :=
begin rw [div_eq_iff (ne_of_gt (sub_pos.mpr ht))] at h,
 have hz:(t-2)^2*(t+7)=0 := by nlinarith only [h,triangle_excess t],
 have hs: (t-2)^2=0 := (mul_eq_zero.mp hz).resolve_right (by linarith),
 have hh:t-2=0:=pow_eq_zero hs,linarith end
theorem height_quartic (t y : ℝ) (ht:1<t) (hy:0<y) (h:t^2=1+4*y^2) :
 (1+t)^4/y^2=4*(1+t)^3/(t-1) :=
begin field_simp [ne_of_gt hy,ne_of_gt (sub_pos.mpr ht)],
 linear_combination (1+t)^3*h end
theorem elliptic_height (t y : ℝ) (h:t^2=1+4*y^2) (ht:t=2) : y^2=3/4 :=
by subst t;nlinarith only [h]
theorem normalized_hessian (y E Q : ℝ) (hy:y^2=3/4) (hE:E≠0) (hQ:2*Q=E) :
 y^2*Q/E=3/8 :=
begin rw [hy],field_simp [hE];linarith end

theorem unit_scalar_charge (t v : ℝ) (h:t^2+v^2≠0) :
 (v*t/(t^2+v^2))^2+(v^2/(t^2+v^2)-1/2)^2=1/4 :=
by field_simp [h];ring
theorem triangle_charge (a b c : ℝ) :
 (a+b+c)^2-3*(a*b+b*c+c*a)=((a-b)^2+(b-c)^2+(c-a)^2)/2 := by ring
theorem equal_pop_charge (a b c : ℝ) :
 (a-b)^2+(b-c)^2+(c-a)^2=0 ↔ a=b ∧ b=c :=
begin split,{intro h,
 have h1:(a-b)^2=0 := by linarith only [h,sq_nonneg (a-b),sq_nonneg (b-c),sq_nonneg (c-a)],
 have h2:(b-c)^2=0 := by linarith only [h,sq_nonneg (a-b),sq_nonneg (b-c),sq_nonneg (c-a)],
 exact ⟨sub_eq_zero.mp (pow_eq_zero h1),sub_eq_zero.mp (pow_eq_zero h2)⟩},
 {rintro ⟨rfl,rfl⟩,ring} end
theorem mass_per_hubble (f H hess F : ℝ) (h:F≠0) (hf:hess=3*(3*f*(2*F)*H^2)/8) :
 hess/F=(9/4)*f*H^2 := by rw [hf];field_simp [h];ring
theorem compactness_mass (G rho L f : ℝ) :
 (3/4)*(8*real.pi*G)*(f*rho)*L^2=(9/2)*f*((4/3)*real.pi*G*rho*L^2) := by ring
theorem ppn_bound (a e : ℝ) (he:e<2) (h: -(2*a^2)/(1+a^2)≥-e) :
 a^2≤e/(2-e) :=
begin have hp:0<1+a^2 := by positivity,have hh := (le_div_iff hp).mp (show -e ≤ -(2*a^2)/(1+a^2), from h),
 rw [le_div_iff (show 0<2-e,by linarith)],linarith only [hh] end
theorem thermal_transfer {X : Type*} [measurable_space X] (μ : measure X)
 (w f g : X → ℝ) (hi : integrable (λ x,w x*f x) μ)
 (hj : integrable (λ x,w x*g x) μ) (hw : ∀ x,0≤w x) (h : ∀ x,f x≤g x) :
 ∫ x,w x*f x ∂μ ≤ ∫ x,w x*g x ∂μ :=
integral_mono hi hj (λ x,mul_le_mul_of_nonneg_left (h x) (hw x))
theorem thermal_free_energy (a b t : ℝ) (ha:0<a) (h:a≤b) (ht:0≤t) :
 -t*real.log b≤ -t*real.log a :=
mul_le_mul_of_nonpos_left ((real.log_le_log ha (lt_of_lt_of_le ha h)).mpr h) (neg_nonpos.mpr ht)

-- Dissolved electric charge, local metric readout and open string modes.
theorem opposite_halves (k : ℝ) : (k+1/2)+(-k-1+1/2)=0 := by ring
theorem recombined_mass (y : ℝ) (h:y^2=3/4) :
 (2*y)^2+((-1:ℝ)+2*(1/2))^2=3 := by linear_combination 4*h
theorem mass_of_endpoint (y : ℝ) (h:y^2=3/4) :
 y^2+((1:ℝ)/2)^2=1 ∧ y^2+((-1:ℝ)+1/2)^2=1 := by rw [h];norm_num
theorem counterplanar (n : ℤ) : n*(-1)-n*0= -n := by ring
theorem dipole_field (z a : ℝ) (h1:z-a≠0) (h2:z+a≠0) :
 1/(2*(z-a)^2)-1/(2*(z+a)^2)=2*a*z/((z-a)^2*(z+a)^2) :=
by field_simp [h1,h2];ring
theorem detector_ratio : (1/(2*(3-1/2)^2)-1/(2*(3+1/2)^2))/(4:ℝ)=12/1225 := by norm_num
theorem reading_cost (n G R t arm L : ℝ) (hl:L≠0) (hr:R≠0) (ht:t≠0) (hd:arm≠0)
 (h:16*n*G/R^2*arm*t/L^2=real.pi/2) :
 G*(n/R)/L=real.pi*R*L/(32*arm*t) :=
calc G*(n/R)/L=(16*n*G/R^2*arm*t/L^2)*(R*L/(16*arm*t)) : by field_simp [hr,hl,hd,ht];ring
 ... =real.pi*R*L/(32*arm*t) : by rw [h];field_simp [hd,ht];ring
theorem string_instability (d dc a : ℝ) (ha:0<a) :
 (d^2-dc^2)/a<0 ↔ d^2<dc^2 := by simpa only [zero_mul,sub_neg] using (div_lt_iff ha : (d^2-dc^2)/a<0 ↔ d^2-dc^2<0*a)
theorem boson_geometric (N : ℝ) (h:0≤N) : 1-1/(1+N)=N/(1+N) :=
by field_simp [show (1+N)≠0,by linarith];ring
theorem critical_pair : (1:ℝ)/(1+1)=1/2 ∧ (1:ℝ)/(1+2*1)=1/3 := by norm_num

-- Magnetic charge and the matched radial problem.
theorem monopole_phase (q n m : ℝ) (h:q=n*m/2) : 2*q=n*m := by linarith
theorem odd_spin (n m : ℤ) : (2*n+1)*(2*m+1)=2*(2*n*m+n+m)+1 := by ring
theorem radial_cancel (a n j : ℝ) :
 -(a*n)^2-(j*(j+1)-(a*n)^2)= -j*(j+1) := by ring
theorem radial_coulomb (r a n w j : ℝ) :
 w^2*r*(r+a)-(r+a)^2*n^2-(j*(j+1)-(a*n)^2)
 =(w^2-n^2)*r^2+a*(w^2-2*n^2)*r-j*(j+1) := by ring
theorem below_threshold (r a n w L : ℝ) (hr:0<r) (ha:0<a) (h:w^2<n^2) (hl:0≤L) :
 (w^2-n^2)*r^2+a*(w^2-2*n^2)*r-L<0 :=
begin have h1:0<(n^2-w^2)*r^2 := mul_pos (sub_pos.mpr h) (sq_pos_of_pos hr),
 have h2:0<(2*n^2-w^2) := by linarith only [h,sq_nonneg n],
 have h3:0<a*(2*n^2-w^2)*r := mul_pos (mul_pos ha h2) hr,linarith only [h1,h3,hl] end
theorem nut_quadratic (h s : ℝ) (hc:s^2=h^2+1) :
 ((s-h)/2)*((s-h)/2+h)=1/4 := by nlinarith only [hc]
theorem log_coordinate (r h z : ℝ) (hh:h≠0) (hz:z≠0) (hp:1+z≠0)
 (he:r=h*(1+z)) : (r-h)/r=z/(1+z) :=
by subst r;field_simp [hh,hp];ring
theorem horizon_index (w h a : ℝ) : w^2*h*(h+a)=(w*h)^2+w^2*h*a := by ring
theorem angular_exponent (k : ℕ) : 2*((k:ℝ)/2)+3/2=(k:ℝ)+3/2 := by ring
theorem near_far_normalization (w h p v c g : ℝ) (hp:p≠0) (hg:g≠0) :
 w*h^2*v*(2*c*p/g)^2/p=4*(c/g)^2*w*p*h^2*v := by field_simp [hp,hg];ring
theorem ratio_coefficient (pi s t : ℝ) (hp:pi≠0) (hs:s≠0) (ht:t≠0) :
 (pi^3/128)*(1/s)/((pi/s)/t)=pi^2*t/128 := by field_simp [hp,hs,ht];ring
theorem horizon_area (p h v : ℝ) (hp:p≠0) :
 real.pi/p^2*(4*p^2*h^2*v)=4*real.pi*h^2*v := by field_simp [hp];ring

-- Thermal horizon: number counting, including possible emission.
def gen (t b z : ℝ) : ℝ :=
 1/(1+b*(1-z))-(1-t)*(1-z)/(1+b*(1-z))^2
theorem gen_one (t b : ℝ) : gen t b 1=1 := by norm_num [gen]
theorem gen_zero (t b : ℝ) (h:0≤b) : gen t b 0=(t+b)/(1+b)^2 :=
begin have hn : 1+b≠0 := by linarith,simp only [gen,sub_zero,mul_one],field_simp [hn];ring end
theorem gen_odd (t b : ℝ) (h:0≤b) :
 (1+gen t b (-1))/2=(t+3*b+2*b^2)/(1+2*b)^2 :=
begin have hn:1+2*b≠0:=by linarith,
 simp only [gen,show (1:ℝ)-(-1)=2,by norm_num,mul_comm b 2],field_simp [hn];ring end
theorem increase_odd (t b : ℝ) (h:0≤b) :
 (t+3*b+2*b^2)/(1+2*b)^2-b/(1+2*b)=(t+2*b)/(1+2*b)^2 :=
begin field_simp [show 1+2*b≠0,by linarith];ring end
theorem one_mode_mean (t n : ℝ) : 1-((1-t)+t*n)=t*(1-n) := by ring
theorem conditional_rescale (t b u : ℝ) (hb:b≠0) (ht:t=b*u)
 (h1:1+b≠0) (h2:1+2*b≠0) (h3:u+3+2*b≠0) :
 ((t+b)/(1+b)^2)/((t+3*b+2*b^2)/(1+2*b)^2)=
 (u+1)*(1+2*b)^2/((1+b)^2*(u+3+2*b)) :=
begin rw [ht,show b*u+3*b+2*b^2=b*(u+3+2*b),by ring],
 field_simp [hb,h1,h2,h3];ring end
theorem conditional_limit {X : Type*} {l : filter X} {b u : X → ℝ}
 (hb:filter.tendsto b l (nhds 0)) (hu:filter.tendsto u l (nhds 0)) :
 filter.tendsto (λ x,(u x+1)*(1+2*b x)^2/((1+b x)^2*(u x+3+2*b x))) l (nhds (1/3)) :=
begin
 have h := ((hu.add_const 1).mul (((hb.const_mul 2).const_add 1).pow 2)).div
 ((((hb.const_add 1).pow 2).mul ((hu.add_const 3).add (hb.const_mul 2))))
 (by norm_num : (1+(0:ℝ))^2*(0+3+2*0)≠0),
 convert h using 1;norm_num
end
theorem weak_noise_linear (n : ℝ) :
 (1+n)+2*n=1+3*n := by ring
theorem source_spin_shift (j : ℝ) : (j+1/2)-j=1/2 := by ring
theorem threshold_inverse (h t : ℝ) (hs : (t-3*h)^2=1+h^2) :
 8*h^2-6*t*h+t^2-1=0 := by nlinarith only [hs]
theorem extremal_scale (a : ℝ) :
 (3:ℝ)/8*(2*a)=3*a/4 := by ring

-- The only topology assumed here is the three integrated Stokes identities.
theorem boundary_coupling {V : Type*} [add_comm_group V] (cup : V → V → ℝ)
 (hl : ∀ a b c, cup (a+b) c=cup a c+cup b c)
 (hr : ∀ a b c, cup a (b+c)=cup a b+cup a c)
 (dA dB N M : V) (left right : ℝ)
 (closed : cup dA dB = 0) (s1 : cup dA M = left) (s2 : cup N dB = -right) :
 cup (dA+N) (dB+M)=cup N M+left-right :=
begin rw [hl,hr,hr,closed,s1,s2],ring end

theorem triangle_length_range (x y A B t : ℝ) (ha:0≤A) (hb:0≤B) (ht:1<t)
 (sa:A^2=x^2+y^2) (sb:B^2=(1-x)^2+y^2) (st:t^2=1+4*y^2) : t≤A+B :=
begin
 apply (mul_self_le_mul_self_iff (show 0≤t,by linarith) (add_nonneg ha hb)).mpr,
 simpa only [←sq,st] using triangle_midpoint x y A B ha hb sa sb
end
theorem triangle_global (x y A B t : ℝ) (ha:0≤A) (hb:0≤B) (hy:0<y) (ht:1<t)
 (sa:A^2=x^2+y^2) (sb:B^2=(1-x)^2+y^2) (st:t^2=1+4*y^2) :
 108≤(1+t)^4/y^2 ∧ (1+t)^4/y^2≤(1+(A+B))^4/y^2 :=
begin split,
 {rw [height_quartic t y ht hy st],exact best_height t ht},
 {exact div_le_div_of_le (sq_nonneg y) (pow_le_pow_of_le_left (by linarith)
   (add_le_add_left (triangle_length_range x y A B t ha hb ht sa sb st) 1) 4)}
end
theorem triangle_global_equality (x y A B t : ℝ) (ha:0≤A) (hb:0≤B) (hy:0<y)
 (ht:1<t) (sa:A^2=x^2+y^2) (sb:B^2=(1-x)^2+y^2) (st:t^2=1+4*y^2)
 (h:(1+(A+B))^4/y^2=108) : x=1/2 ∧ y^2=3/4 :=
begin
 rcases triangle_global x y A B t ha hb hy ht sa sb st with ⟨h1,h2⟩,
 have hm : (1+t)^4/y^2=108 := le_antisymm (h ▸ h2) h1,
 have hq := hm.trans h.symm,
 have he : (1+t)^4=(1+(A+B))^4 := (div_left_inj' (pow_ne_zero 2 (ne_of_gt hy))).mp hq,
 have ha' : 0≤1+t := by linarith, have hb' : 0≤1+(A+B) := by linarith,
 have hl := (pow_left_inj ha' hb' (by norm_num : 0<(4:ℕ))).mp he,
 have heq : A+B=t := by linarith only [hl],
 rw [height_quartic t y ht hy st] at hm,
 exact ⟨midpoint_unique x y A B (ne_of_gt hy) sa sb (by rw [heq,st]),
   elliptic_height t y st (best_height_unique t ht hm)⟩
end

-- The determinant here is the wrapped cycle intersection in the two-torus.
theorem integral_basis (a b c d k p l s : ℤ) (h:a*d-b*c=1) :
 (a*k+b*p)*(c*l+d*s)-(c*k+d*p)*(a*l+b*s)=k*s-p*l :=
by linear_combination (k*s-p*l)*h
def parity_check (q w : bool × bool) : bool :=
 bxor (q.1 && w.2) (q.2 && w.1)
theorem basis_resolves (q s : bool × bool) :
 (∀ w, parity_check q w=parity_check s w) ↔ q=s :=
begin split,
 {rintro h,rcases q with ⟨a,b⟩,rcases s with ⟨c,d⟩,
  have h1:=h (ff,tt),have h2:=h (tt,ff),
  cases a;cases b;cases c;cases d;simp [parity_check,bxor,band] at h1 h2 ⊢;assumption},
 {rintro rfl,intro w,refl}
end
theorem dependent_reading (a b : bool × bool) :
 parity_check a b=parity_check b a :=
begin rcases a with ⟨i,j⟩,rcases b with ⟨k,l⟩,cases i;cases j;cases k;cases l;refl end
theorem self_intersection (a : bool × bool) : parity_check a a=ff :=
begin rcases a with ⟨i,j⟩,cases i;cases j;refl end
theorem indistinguishable (w q s : bool × bool) :
 parity_check q w=parity_check s w ↔
 parity_check (bxor q.1 s.1,bxor q.2 s.2) w=ff :=
begin rcases q with ⟨i,j⟩,rcases s with ⟨a,b⟩,rcases w with ⟨k,l⟩,
 cases i;cases j;cases a;cases b;cases k;cases l;dec_trivial end
theorem sufficient_partition {Q W Y : Type*} (phase : Q → W → bool) (mark : Q → Y)
 (available : set W) :
 (∀ q s,mark q=mark s → ∀ w∈available,phase q w=phase s w) ↔
 (∀ q s,mark q=mark s → (λ w : available,phase q w)=(λ w : available,phase s w)) :=
begin split,
 {intros h q s hs,funext w,exact h q s hs w.val w.property},
 {intros h q s hs w hw,have he := congr_arg (λ f : available → bool, f ⟨w,hw⟩) (h q s hs),exact he}
end
theorem single_twirl (a : ℝ) (h:a^2=1) : ((1+a)/2)^2=(1+a)/2 :=
by linear_combination h/4
theorem receiver_gram (a b : ℝ) : 0≤(a^2+b^2)/2 := by positivity
theorem rank_probability (empty a b c : ℝ) :
 empty+((a-empty)+(b-empty)+(c-empty))+(1-a-b-c+2*empty)=1 := by ring
theorem rank_entropy (empty a b c : ℝ) :
 2*empty+((a-empty)+(b-empty)+(c-empty))=a+b+c-empty := by ring
theorem balanced_receipts : ((1:ℚ)/2)^3*3-((1:ℚ)/4)^3=23/64 := by norm_num
-- Exact rank-one probability for independent categorical receipts, without
-- assigning a Poisson clock. Once a different direction arrives rank increases.
def only_direction (empty hit : ℝ) : ℕ → ℝ
| 0 := 0
| (n+1) := empty^n*hit+(empty+hit)*only_direction n
theorem rank_one_packets (empty hit : ℝ) (n : ℕ) :
 only_direction empty hit n=(empty+hit)^n-empty^n :=
begin induction n with n ih,{simp [only_direction]},
 {rw [only_direction,ih,pow_succ,pow_succ],ring} end
theorem average_gram {I : Type*} (s : finset I) (v ch : I → ℝ) :
 (∑ i in s,∑ j in s, v i*((1+ch i*ch j)/2)*v j)=
 ((∑ i in s,v i)^2+(∑ i in s,v i*ch i)^2)/2 :=
begin
 rw [eq_div_iff (by norm_num : (2:ℝ)≠0)],
 simp only [pow_two,finset.sum_mul,finset.mul_sum,←finset.sum_add_distrib],
 apply finset.sum_congr rfl,intros i hi,apply finset.sum_congr rfl,intros j hj,ring
end
-- Difference of consecutive canonical tails equals the exact number probability.
theorem infinite_tail_step (B tau L : ℝ) (hb:0<B) :
 (1+(1-tau)*L/(B*(1+B)))-(B/(1+B))*(1+(1-tau)*(L+1)/(B*(1+B)))=
 (tau+B+(1-tau)*L/B)/(1+B)^2 :=
by field_simp [ne_of_gt hb,show 1+B≠0,by linarith];ring
theorem infinite_count_positive (B tau : ℝ) (L : ℕ) (hb:0<B) (ht:0≤tau) (ht':tau≤1) :
 0<(B/(1+B))^L/(1+B)^2*(tau+B+(1-tau)*(L:ℝ)/B) :=
begin
 have h1 : 0<1+B := by linarith,
 have h2 : 0≤(1-tau)*(L:ℝ)/B :=
 div_nonneg (mul_nonneg (sub_nonneg.mpr ht') (nat.cast_nonneg L)) hb.le,
 exact mul_pos (div_pos (pow_pos (div_pos hb h1) _) (sq_pos_of_pos h1))
  (by linarith only [h2,ht,hb])
end
theorem translated_readout (g : ℝ → ℝ) (u : ℝ) (h:(∫ P,g P)=1) :
 (∫ P,g (P-u))=1 :=
begin simpa only [sub_eq_add_neg] using (integral_add_right_eq_self g (-u)).trans h end
theorem conditional_linear_risk (a V S : ℝ) (h:V+S≠0) :
 (1-a)^2*V+a^2*S=(V*S)/(V+S)+(V+S)*(a-V/(V+S))^2 :=
by field_simp [h];ring
theorem opt_variance (V S : ℝ) (h:V+S≠0) :
 (1-V/(V+S))^2*V+(V/(V+S))^2*S=V*S/(V+S) :=
by rw [conditional_linear_risk _ _ _ h];ring
theorem missed_gravity (a V S best : ℝ) (ha:0≤a) (h:best≤V*S/(V+S)) :
 (1-a)*V+a*best≤(1-a)*V+a*(V*S/(V+S)) :=
add_le_add_left (mul_le_mul_of_nonneg_left h ha) _
theorem unit_pointer_bound : ((1:ℝ)/3)*1/(1/3+1)/(1/3)=3/4 := by norm_num
-- Four-dimensional tensor reception; scale and frequency are dimensionless here.
theorem tensor_cross (w r : ℝ) (hw:w≠0) :
 5*real.pi/w^2*(4*(w*r)^6/225)=4*real.pi*r^6*w^4/45 :=
by field_simp [hw];ring
theorem circular_pattern (v : ℝ) :
 ((1+v)^4+(1-v)^4)/2=1+6*v^2+v^4 := by ring
theorem helicity_moments :
 (∫ z in (0:ℝ)..1,z^4)=1/5 ∧ (∫ z in (0:ℝ)..1,z^5)=1/6 ∧
 (∫ z in (0:ℝ)..1,z^6)=1/7 := by norm_num [integral_pow]
theorem angular_mean_variance :
 2*(5/6:ℝ)-1=2/3 ∧ 4*(5/7:ℝ)-4*(5/6:ℝ)+1=11/21 ∧
 (11/21:ℝ)-(2/3)^2=5/63 := by norm_num
theorem untagged_orientation (m : ℝ) : m/2+(-m)/2=0 := by ring
theorem prior_information (a : ℝ) :
 1/3-(a/2*(2/3)^2+a/2*(-2/3)^2+(1-a)*0^2)=1/3-4*a/9 := by ring
theorem received_odd (s t B : ℝ) (h:0≤B) :
 (1-s)*(B/(1+2*B))+s*((t+3*B+2*B^2)/(1+2*B)^2)=
 B/(1+2*B)+s*(t+2*B)/(1+2*B)^2 :=
by field_simp [show 1+2*B≠0,by linarith];ring
theorem mean_excess_gravity (s t n : ℝ) :
 (1-s)*(-t*n)+s*(t*(1-n))-(-t*n)=s*t := by ring
theorem diluted_ratio (s t b u : ℝ) (hb:b≠0) (ht:t=b*u)
 (h1:1+b≠0) (h2:1+2*b≠0) (h3:1+2*b+s*(u+2)≠0) :
 (s*(t+b)/(1+b)^2)/(b/(1+2*b)+s*(t+2*b)/(1+2*b)^2)=
 s*(u+1)*(1+2*b)^2/((1+b)^2*(1+2*b+s*(u+2))) :=
begin
 have he : b/(1+2*b)+s*(t+2*b)/(1+2*b)^2 =
 b*(1+2*b+s*(u+2))/(1+2*b)^2 := by rw [ht];field_simp [h2];ring,
 rw [he,ht],field_simp [hb,h1,h2,h3];ring
end
theorem diluted_limit {X : Type*} {l : filter X} {b u : X → ℝ} (s : ℝ) (hs:0≤s)
 (hb:filter.tendsto b l (nhds 0)) (hu:filter.tendsto u l (nhds 0)) :
 filter.tendsto (λ x,s*(u x+1)*(1+2*b x)^2/
 ((1+b x)^2*(1+2*b x+s*(u x+2)))) l (nhds (s/(1+2*s))) :=
begin
 have hn : (1+(0:ℝ))^2*(1+2*0+s*(0+2))≠0 := by nlinarith,
 have hh := (((hu.add_const 1).const_mul s).mul (((hb.const_mul 2).const_add 1).pow 2)).div
 (((hb.const_add 1).pow 2).mul (((hb.const_mul 2).const_add 1).add ((hu.add_const 2).const_mul s))) hn,
 convert hh using 1;ring_nf
end
end natural_flux_endpoints
