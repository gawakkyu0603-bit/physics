import tactic
import algebra.big_operators.order
import analysis.inner_product_space.basic
import analysis.special_functions.integrals
import measure_theory.measure.lebesgue.basic

namespace cat_compensated_yukawa
noncomputable theory
open_locale big_operators
open measure_theory filter

theorem triangle_offsets (l r p : ℝ) : (l-p)-(r-p)=l-r := by ring
theorem transverse_projector {A : Type*} [ring A] (y d : A)
 (hy : y*y=1) (anti : y*d= -(d*y)) :
 y*(1-d)*y=1+d :=
begin
 rw [mul_sub,mul_one,sub_mul,hy,anti,neg_mul,mul_assoc,hy,mul_one], abel
end
theorem spin_trace (x z y w : ℝ) :
 ((1+z)*(1+w)+(1-z)*(1-w)+2*x*y)/4=(1+x*y+z*w)/2 := by ring
theorem casimir_excess (j d M : ℝ) :
 M^2+j*(j+1)*d^2-(M^2+(j*d)^2)=j*d^2 := by ring
theorem mass_spin (L R x z y w S : ℝ) (hl : L^2=x^2+z^2)
 (hr : R^2=y^2+w^2) (hs : 2*L*R*S=L*R+x*y+z*w) :
 (L+R)^2-((x-y)^2+(z-w)^2)=4*L*R*S :=
by nlinarith only [hl,hr,hs]
theorem shell_dark (L R S : ℝ) (hl : 0<L) (hr : 0<R) (h : 4*L*R*S=0) : S=0 :=
(mul_eq_zero.mp h).resolve_left (ne_of_gt (by positivity))
theorem shell_factor (j d M W a : ℝ) (h : W^2-M^2=j*(j+1)*d^2) :
 (j+1)*((W-a*M)^2-((1-a)^2*M^2+j^2*d^2))
 =(W-M)*(W+M-2*a*M*(j+1)) := by linear_combination j*h
theorem selected_fraction (a M W j : ℝ) (hm : 0<M) (hw : M<W) (hj : 0≤j)
 (h : (W-M)*(W+M-2*a*M*(j+1))=0) : a=(W+M)/(2*(j+1)*M) :=
begin
 have e := (mul_eq_zero.mp h).resolve_left (ne_of_gt (sub_pos.mpr hw)),
 have hp : 0<2*(j+1)*M := by positivity,
 apply (eq_div_iff (ne_of_gt hp)).2, nlinarith only [e]
end
theorem shell_converse (x y : ℝ) (hx : 0≤x) (hy : 0≤y) (e : x^2=y^2) : x=y :=
begin
 have h := mul_eq_zero.mp (show (x-y)*(x+y)=0,by nlinarith only [e]),
 cases h with a b, {linarith only [a]}, {linarith only [hx,hy,b]}
end
theorem edge_weight (L R S W M : ℝ) (hL : 0<L) (hR : 0<R)
 (h : 4*L*R*S=2*L*(W-M)) : S=(W-M)/(2*R) :=
begin
 apply (eq_div_iff (show 2*R≠0,by positivity)).2,
 apply (mul_left_cancel₀ (ne_of_gt hL)), nlinarith only [h]
end
theorem general_port_bound (j s m e d : ℝ) (hs : 0≤s) (hm : 0≤m)
 (hj : 0≤j) (hgap : m≤e) (hshell : 4*e*s=j*d^2)
 (hspread : j*(j+1)*d^2≤1) : 4*(j+1)*m*s≤1 :=
begin
 have h1 := mul_le_mul_of_nonneg_right hgap hs,
 have h2 := mul_le_mul_of_nonneg_left h1 (show 0≤4*(j+1),by positivity),
 have h3 := congr_arg (λ t:ℝ,(j+1)*t) hshell,
 dsimp only at h3, nlinarith only [h2,h3,hspread]
end

theorem gauss_absorption (q a b : ℤ) : (q+1)+(a-1)-b=q+a-b := by ring
theorem gauss_emission (q a b : ℤ) : (q+1)+a-(b+1)=q+a-b := by ring
theorem fermion_compensated (l r : ℤ) : (l+1)+(r-1)=l+r := by ring
theorem grade_sum (a b : ℝ) (ha : 0≤a) (hb : 0≤b) : |a-b|≤a+b :=
by {apply abs_le.mpr, split;linarith}
theorem charge_conjugate {V : Type*} [normed_add_comm_group V]
 (C : V→V) (p n : V→V) (v : V) (hc : ∀ x, ‖C x‖=‖x‖)
 (hv : C v=v) (swap : ∀ x,C (p x)=n (C x)) : ‖p v‖^2=‖n v‖^2 :=
by rw [←hc (p v),swap,hv]
theorem identity_shift_cost (energy diag hop : ℝ) (h : energy=diag+hop) :
 diag-energy= -hop := by linarith only [h]

-- A grade projector separates the two opposite shifts. Multiplication by the
-- complex link coordinate and its conjugate is injective on wave functions.
theorem ae_multiplier {α : Type*} [measurable_space α] (μ : measure α)
 (f g : α→ℂ) (hf : ∀ᵐ x ∂μ, f x≠0) (hp : ∀ᵐ x ∂μ, f x*g x=0) :
 ∀ᵐ x ∂μ, g x=0 :=
by {filter_upwards [hf,hp] with x h1 h2, exact (mul_eq_zero.mp h2).resolve_left h1}
theorem no_live_signed_grade {V : Type*} [add_comm_group V] [module ℝ V]
 (f b z zb pr : V →ₗ[ℝ] V) (v : V) (q : ℝ) (hv : v≠0)
 (hz : function.injective z) (hzb : function.injective zb)
 (proj_f : pr (z (f v))=z (f v)) (proj_b : pr (zb (b v))=0)
 (stationary : z (f v)+zb (b v)=0) (ladder : f (b v)-b (f v)=(2*q)•v) : q=0 :=
begin
 have zero_f : z (f v)=0,
 { have h := congr_arg pr stationary, rw [map_add,proj_f,proj_b,add_zero,map_zero] at h, exact h },
 have zero_b : zb (b v)=0 := by simpa only [zero_f,zero_add] using stationary,
 have hf : f v=0 := hz (by simpa only [map_zero] using zero_f),
 have hb : b v=0 := hzb (by simpa only [map_zero] using zero_b),
 rw [hf,hb,map_zero,map_zero,sub_self] at ladder,
 have small := (smul_eq_zero.mp ladder.symm).resolve_right hv, linarith only [small]
end
theorem conserved_projector_range {V : Type*} [add_comm_group V] [module ℝ V]
 (H P : V→ₗ[ℝ] V) (v : V) (hp : P v=v) (hc : ∀ x,P (H x)=H (P x)) : P (H v)=H v :=
by rw [hc,hp]
theorem ladder_positive (f b q : ℝ) (hf : 0≤f) (hb : 0≤b) (h : f-b=2*q) :
 2*|q|≤f+b :=
begin
 rw [←abs_of_nonneg (show 0≤(2:ℝ),by norm_num),←abs_mul,←h],
 exact grade_sum f b hf hb
end
theorem oscillator_average {ι : Type*} (s : finset ι) (p n : ι→ℝ) (m : ℝ)
 (hp : ∀ i∈s,0≤p i) (hn : ∀ i∈s,m≤n i) (norm : ∑ i in s,p i=1) :
 m≤∑ i in s,p i*n i :=
begin
 calc m=(∑ i in s,p i)*m : by rw [norm,one_mul]
 ... =∑ i in s,p i*m : finset.sum_mul
 ... ≤∑ i in s,p i*n i : finset.sum_le_sum (λ i hi,mul_le_mul_of_nonneg_left (hn i hi) (hp i hi))
end
theorem radial_uncertainty (A R P : ℝ) (ha : 0<A) (hr : 0<R)
 (spectrum : ∀ k:ℝ,0<k→2*k*A≤P+k^2*R) : A^2≤P*R :=
begin
 have h := spectrum (A/R) (div_pos ha hr),
 have h2 : 2*A^2≤P*R+A^2 := calc
   2*A^2=(2*(A/R)*A)*R : by {field_simp [ne_of_gt hr];ring}
   ... ≤ (P+(A/R)^2*R)*R : mul_le_mul_of_nonneg_right h hr.le
   ... =P*R+A^2 : by {field_simp [ne_of_gt hr];ring},
 linarith only [h2]
end
theorem leakage_cost (g m R P E L : ℝ) (hg : 0≤g) (hm : 0≤m) (hr : 0≤R)
 (he : 0<E) (hk : P≤2*E) (hu : (m+1)^2≤P*R) (hl : g*m*R≤L) :
 g*m*(m+1)^2/(2*E)≤L :=
begin
 apply (div_le_iff (show 0<2*E,by positivity)).2,
 have h1 := mul_le_mul_of_nonneg_right hk hr,
 have h2 := mul_le_mul_of_nonneg_left (hu.trans h1) (mul_nonneg hg hm),
 have h3 := mul_le_mul_of_nonneg_right hl (show 0≤2*E,by positivity),
 nlinarith only [h2,h3]
end
theorem unscreened_energy (omega q E : ℝ) (h : omega*(q+1)≤E) : omega*q≤E-omega :=
by linarith only [h]
theorem weight_of_transfer (l r x y : ℝ) : l*(x+1)+r*(y-1)-(l*x+r*y)=l-r := by ring
theorem insulated_cluster (l r x y : ℝ) (h : l=r) :
 l*(x+1)+r*(y-1)=l*x+r*y := by {rw [h],ring}
theorem bare_work (v force gradient : ℝ) (equation : force= -gradient) :
 v*force+gradient*v=0 := by {rw [equation],ring}
theorem field_energy_exchange (gradient vel : ℝ) : (-gradient)*vel+gradient*vel=0 := by ring

-- Apply to same and different spin indices after rotating the right spin basis.
theorem car_bilinear {A : Type*} [ring A] (a b c d s t : A)
 (bc : b*c=s-c*b) (da : d*a=t-a*d) (ca : c*a= -(a*c)) (db : d*b= -(b*d)) :
 (a*b)*(c*d)-(c*d)*(a*b)=a*s*d-c*t*b :=
begin
 have eqn : (c*a)*(d*b)=(a*c)*(b*d) := by rw [ca,db,neg_mul_neg],
 calc (a*b)*(c*d)-(c*d)*(a*b)=a*(b*c)*d-c*(d*a)*b : by noncomm_ring
 ... =a*(s-c*b)*d-c*(t-a*d)*b : by rw [bc,da]
 ... =a*s*d-c*t*b+((c*a)*(d*b)-(a*c)*(b*d)) : by noncomm_ring
 ... =a*s*d-c*t*b : by rw [eqn,sub_self,add_zero]
end
theorem strict_positive_leakage (g m E L : ℝ) (hg : 0<g) (hm : 0<m) (he : 0<E)
 (bound : g*m*(m+1)^2/(2*E)≤L) : 0<L :=
lt_of_lt_of_le (by positivity) bound
theorem interchanging_marks (f : ℤ → ℝ) (h : ∀ i, f i=f (-i)) (i : ℤ) :
 (i:ℝ)*f i+(-i:ℤ)*f (-i)=0 := by {rw [←h i,int.cast_neg],ring}
theorem dephasing_hop {ι : Type*} (s : finset ι) (diag hop : ι→ℝ)
 (forbidden : ∀ i∈s,hop i=0) : (∑ i in s,(diag i+hop i))=∑ i in s,diag i :=
by {apply finset.sum_congr rfl, intros i hi, rw [forbidden i hi,add_zero]}
theorem conjugate_readout {V : Type*} [normed_add_comm_group V] (C P : V→V)
 (v : V) (h : ∀ x,P (C x)=P x) : P (C v)=P v := h v
theorem protected_neutral {V : Type*} [add_comm_group V] [module ℝ V]
 (a b z zb : V→ₗ[ℝ] V) (v : V) (ha : a v=0) (hb : b v=0) :
 z (a v)+zb (b v)=0 := by rw [ha,hb,map_zero,map_zero,add_zero]
theorem two_step_probability (amplitude_sq gap N g D : ℝ) (hN : 0<N) (hgap : 0<gap)
 (h : amplitude_sq=(g/(2*N*gap))*2*D) :
 amplitude_sq/4=g*D/(4*N*gap) :=
by {rw [h],field_simp [ne_of_gt hN,ne_of_gt hgap];ring}
theorem neutral_survival (v t amp : ℝ) (ha : 0≤amp) (h : amp≤|v|*t^2) :
 amp^2≤v^2*t^4 :=
begin
 have hh := pow_le_pow_of_le_left ha h 2,
 rw [mul_pow,sq_abs] at hh, nlinarith only [hh]
end


theorem link_coordinate_nonzero (μ : measure ℂ) [has_no_atoms μ] : ∀ᵐ (z : ℂ) ∂μ,z≠(0:ℂ) :=
begin
 rw [ae_iff],
 have same : {z:ℂ | ¬z≠0} = {0} := by {ext z,simp},
 rw [same,measure_singleton]
end
theorem real_singlet_conversion (lx lz rx rz : ℝ) :
 ((rx-lx)^2+(lz-rz)^2+(lz-rz)^2+(lx-rx)^2)/2=(lx-rx)^2+(lz-rz)^2 := by ring
theorem symmetric_spin_motion (x z a b d : ℝ) :
 z*b+x*d+a*x-b*z=x*a-z*b+b*z+d*x := by ring
theorem two_compensators {A : Type*} [ring A] (g x y : A)
 (up : g*x-x*g=x) (down : g*y-y*g= -y) : g*(x*y)=(x*y)*g :=
begin
 have h : g*(x*y)-(x*y)*g=(g*x-x*g)*y+x*(g*y-y*g) := by noncomm_ring,
 rw [up,down,mul_neg,add_neg_self] at h, exact sub_eq_zero.mp h
end
open_locale interval
theorem integrated_screening (v T : ℝ) :
 (∫ t in (0:ℝ)..T, (2*|v|)*t)=|v|*T^2 :=
by {rw [interval_integral.integral_const_mul,integral_id],ring}


theorem exclusive_two_axes (a b c d : ℝ) :
 (a^2+b^2)*(c^2+d^2)-(a*c+b*d)^2=(a*d-b*c)^2 := by ring
theorem conclusive_bound {V : Type*} [normed_add_comm_group V] [normed_space ℝ V]
 (K : V→ₗ[ℝ] V) (x y : V) (r : ℝ) (dark : K x=0)
 (contract : ∀ u, ‖K u‖≤‖u‖) : ‖K y‖≤‖y-r•x‖ :=
begin
 have h : K (y-r•x)=K y := by rw [map_sub,K.map_smul r x,dark,smul_zero,sub_zero],
 rw [←h], exact contract _
end


theorem absorption_storage_trade (N E W S vertex leak g A : ℝ) (hN : 0<N) (hE : 0<E)
 (hW : 0<W) (hS : 0<S) (v : 2*N*W*vertex=g*S)
 (h : g*A≤2*N*E*leak) : vertex*(W*A)≤E*S*leak :=
begin
 have h1 := mul_le_mul_of_nonneg_right h hS.le,
 have h2 := congr_arg (λ x:ℝ,x*A) v, dsimp only at h2,
 apply le_of_mul_le_mul_left _ (show 0<2*N,by positivity), nlinarith only [h1,h2]
end
theorem finite_deadline (p n N g I : ℝ) (hn : 0≤n) (hN : 0<N) (hg : 0≤g)
 (hi : 0≤I) (p_bound : p≤(real.sqrt (2*n*g/N)*I)^2) :
 p*N≤2*n*g*I^2 :=
begin
 have hnng : 0≤2*n*g/N := div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hn) hg) hN.le,
 rw [mul_pow,real.sq_sqrt hnng] at p_bound,
 have h:=mul_le_mul_of_nonneg_right p_bound hN.le,
 calc p*N≤(2*n*g/N*I^2)*N : h
 ... =2*n*g*I^2 : by {field_simp [ne_of_gt hN];ring}
end

end cat_compensated_yukawa
