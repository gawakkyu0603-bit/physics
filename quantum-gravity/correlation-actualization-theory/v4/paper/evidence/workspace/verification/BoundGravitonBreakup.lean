import analysis.special_functions.integrals
import analysis.special_functions.trigonometric.deriv
import linear_algebra.matrix.trace
import analysis.special_functions.improper_integrals
import measure_theory.function.l2_space
import tactic

noncomputable theory
open filter
namespace bound_graviton_breakup

-- Coefficients of (u+s a)(v+s b) / (d+2s q+s^2 w) through second order.
def jet0 (u v d : ℝ) := u*v/d
def jet1 (u v a b d q : ℝ) := (a*v+u*b)/d-2*q*u*v/d^2
def jet2 (u v a b d q w : ℝ) :=
 a*b/d-2*q*(a*v+u*b)/d^2+u*v*(4*q^2/d^3-w/d^2)
theorem quotient_coefficients (u v a b d q w : ℝ) (hd : d≠0) :
 d*jet0 u v d=u*v ∧
 d*jet1 u v a b d q+2*q*jet0 u v d=a*v+u*b ∧
 d*jet2 u v a b d q w+2*q*jet1 u v a b d q+w*jet0 u v d=a*b :=
by unfold jet0 jet1 jet2; split; [skip,split]; field_simp [hd]; ring

-- A directional Hessian contracted with an eigenprojector vv^T, with |k|=1.
theorem hessian_rank_one (u v a b q w : ℝ) :
 jet2 u v a b 1 q w+w*u*v=(a-2*q*u)*(b-2*q*v) :=
by unfold jet2; ring

section reflector
variables {A : Type*} [ring A]
def half_turn (p : A) := 1-(p+p)
theorem reflection_sq (p : A) (hp : p*p=p) : half_turn p * half_turn p=1 :=
by unfold half_turn; simp only [sub_mul,mul_sub,add_mul,mul_add,one_mul,mul_one,hp]; abel
theorem reflector_restores (p e : A) (hp : p*p=p) :
 half_turn p*(half_turn p*e*half_turn p)*half_turn p=e :=
by simp only [mul_assoc,reflection_sq p hp,mul_one,←mul_assoc (half_turn p) (half_turn p),one_mul]
theorem preserves_pairing (h e b : A) (hh : h*h=1)
 (tr : A → ℝ) (cyclic : ∀ x y, tr (x*y)=tr (y*x)) :
 tr ((h*b*h)*(h*e*h))=tr (b*e) :=
begin
 have merge : (h*b*h)*(h*e*h)=(h*(b*(h*h)*e))*h := by simp only [mul_assoc],
 rw [merge,hh,mul_one,cyclic,←mul_assoc,hh,one_mul]
end
end reflector

-- Multiplication by a scalar scattering phase in the direction-adapted basis.
theorem ward_channel (h e : ℝ) (hh : h*h=1) (s : ℝ) : h*(s*(h*e))=s*e :=
by calc h*(s*(h*e))=s*((h*h)*e) : by ring
    ... =s*e : by rw [hh,one_mul]

-- Joint block ranks and the coefficient of r_i r_j in the curvature coupling.
theorem relative_quadrupole (c r d s : ℝ) :
 ((c+r/2)*(d+s/2)+(c-r/2)*(d-s/2))/2=c*d+r*s/4 := by ring

theorem spectral_constant (p : ℝ) (hp : p≠0) :
 (32*p^4/105)*(16*p^2)^2/(8*(2*p)^9)=2/(105*p) :=
by field_simp [hp];ring
theorem radial_power (k : ℝ) (hk : k≠0) :
 k^8/(2*k)/k^4=k^3/2 := by field_simp [hk];ring
theorem euclidean_coefficient (s : ℝ) (hs : s≠0) :
 (2/(105*s^2))*(3*s/4)=1/(70*s) := by field_simp [hs];ring
theorem strain_coefficient (p : ℝ) (hp : p≠0) :
 2/(105*p)*(2*p)/4/2=1/210 := by field_simp [hp];ring

def cap (z : ℝ) := 1-35/16*(z-z^3+3*z^5/5-z^7/7)
theorem cap_density (z : ℝ) : has_deriv_at cap (-(35/16)*(1-z^2)^3) z :=
begin
 have d := ((((has_deriv_at_id z).sub ((has_deriv_at_id z).pow 3)).add
   ((((has_deriv_at_id z).pow 5).const_mul 3).div_const 5)).sub
   (((has_deriv_at_id z).pow 7).div_const 7)).const_mul (35/16:ℝ),
 convert (has_deriv_at_const z (1:ℝ)).sub d using 1; try {ext x}; simp [cap]; ring; tauto
end
theorem cap_ends : cap 0=1 ∧ cap 1=0 := by norm_num [cap]
theorem normalized_harmonic (s : ℝ) (hs : s^2=11) :
 (s/4)^2*(81*(1/33:ℝ)-18*(1/9:ℝ)+1)=1 :=
by calc (s/4)^2*(81*(1/33:ℝ)-18*(1/9:ℝ)+1)=s^2/11 : by ring
    ... = 1 : by rw [hs];norm_num

def cap_primitive (z : ℝ) := z*(1-z^2)^4
theorem cap_quadrupole_integrand (z : ℝ) :
 has_deriv_at cap_primitive ((1-9*z^2)*(1-z^2)^3) z :=
begin
 have h := (has_deriv_at_id z).mul
   (((has_deriv_at_const z (1:ℝ)).sub ((has_deriv_at_id z).pow 2)).pow 4),
 convert h using 1; try {ext x}; simp [cap_primitive];ring
end
theorem cap_quadrupole_endpoint : cap_primitive 1=0 := by norm_num [cap_primitive]

-- Reversible, partial and fully irreversible writes with two coarse alternatives.
def weight (x y overlap : ℝ) := x^2+y^2+2*overlap*x*y
theorem singlet_fraction (p overlap : ℝ) :
 weight p (1-p) overlap=1-2*(1-overlap)*p*(1-p) :=
by unfold weight;ring
theorem higher_channel (b overlap : ℝ) :
 weight b (-b) overlap=2*(1-overlap)*b^2 := by unfold weight;ring
theorem quadrupole_leak (c s overlap : ℝ) (hs : s^2=11) :
 weight (35*s/64*cap_primitive c) (-(35*s/64*cap_primitive c)) overlap =
 (13475/2048)*(1-overlap)*c^2*(1-c^2)^8 :=
begin
 rw [higher_channel],unfold cap_primitive,
 calc 2*(1-overlap)*(35*s/64*(c*(1-c^2)^4))^2 =
       (1225/2048)*s^2*(1-overlap)*c^2*(1-c^2)^8 : by ring
 ... = _ : by rw [hs];ring
end
theorem leak_nonzero (c overlap : ℝ) (hc : 0<c) (hc' : c<1) (hd : overlap<1) :
 0<(13475/2048:ℝ)*(1-overlap)*c^2*(1-c^2)^8 :=
begin
 have h : 0<1-c^2 := by nlinarith [mul_pos (sub_pos.mpr hc') (show 0<1+c, by linarith)],
 have h1 : 0<1-overlap := sub_pos.mpr hd,
 positivity
end
theorem fixed_angle_preserves (p overlap : ℝ) (hp : 0<p) (hpc : p<1) :
 weight p (1-p) overlap=1 ↔ overlap=1 :=
begin
 rw [singlet_fraction],split,
 { intro H,
   have zero : (1-overlap)*(p*(1-p))=0 := by nlinarith only [H],
   have pos : 0<p*(1-p) := mul_pos hp (sub_pos.mpr hpc),
   exact (sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_right (ne_of_gt pos))).symm },
 { intro H,rw [H],ring }
end
theorem bfss_phases :
 (4:ℝ)/720=1/180 ∧ (4:ℝ)*2/40320=1/5040 ∧ (1/180:ℝ)-1/5040=3/560 :=
by norm_num

-- Taking a partial trace of the two-mode rotation gives the following occupations.
theorem marginal_mode : ((0:ℝ)+1/2)/2=1/4 ∧ ((1:ℝ)+1/2)/2=3/4 := by norm_num
theorem local_full_support (m : ℕ) :
 0 < (3/4:ℝ)^m*(1/4:ℝ)^(8-m) ∧ 0 < (1/4:ℝ)^m*(3/4:ℝ)^(8-m) :=
by constructor;positivity
theorem majority_success :
 (3^8+8*3^7+28*3^6+56*3^5+70*3^4/2:ℝ)/4^8=3807/4096 := by norm_num
theorem helicity_ports :
 ((3/4:ℝ)^8=6561/65536) ∧ ((1/4:ℝ)^8=1/65536) ∧
 ((3/4:ℝ)^8/((3/4:ℝ)^8+(1/4:ℝ)^8)=6561/6562) := by norm_num
theorem port_with_loss (a b eta : ℝ) :
 eta*a+(1-eta*(a+b))/2=(1+eta*(a-b))/2 := by ring
theorem add_reverse (a b : ℝ) : a^2+b^2≤(a+b)^2 ↔ 0≤a*b :=
by constructor;intro h;nlinarith

theorem encounter_complete (a : ℝ) : real.sin a^2+real.cos a^2=1 :=
real.sin_sq_add_cos_sq a
theorem encounter_gram (a b : ℝ) :
 real.cos a*real.cos b+real.sin a*real.sin b=real.cos (a-b) := (real.cos_sub a b).symm
theorem gram_nonnegative (a b x y : ℝ) :
 0 ≤ x^2 + 2*x*y*real.cos (a-b) + y^2 :=
begin
 rw [real.cos_sub],
 have hi : x^2+y^2 = x^2*(real.sin a^2+real.cos a^2)+y^2*(real.sin b^2+real.cos b^2) :=
 by rw [real.sin_sq_add_cos_sq,real.sin_sq_add_cos_sq];ring,
 have h : x^2+2*x*y*(real.cos a*real.cos b+real.sin a*real.sin b)+y^2 =
 (x*real.cos a+y*real.cos b)^2+(x*real.sin a+y*real.sin b)^2 :=
 by linear_combination hi,
 rw [h], exact add_nonneg (sq_nonneg _) (sq_nonneg _)
end
theorem phase_coefficients : ((2*(1/180):ℝ)^2=1/8100) ∧
 2*((1/180:ℝ)-1/5040)^2=9/156800 := by norm_num
theorem distant_encounters (a b : ℝ) :
 real.cos (a+b)-real.cos a*real.cos b = -real.sin a*real.sin b :=
by rw [real.cos_add];ring
theorem common_even_factor_trivial (f : ℝ → ℝ) (zero : f 0=1)
 (even : ∀ x, f (-x)=f x) (product : ∀ x y, f (x+y)=f x*f y)
 (x : ℝ) : f x=1 :=
begin
 have pos : 0≤f x := by
   { have h := product (x/2) (x/2), rw [show x/2+x/2=x, by ring] at h,
     rw [h],exact mul_self_nonneg _ },
 have h := product x (-x),rw [add_neg_self,zero,even] at h,
 nlinarith only [h,pos]
end

open measure_theory
open_locale big_operators

theorem pair_variance {X H : Type*} [measurable_space X] (μ : measure X)
 [is_probability_measure μ] [normed_add_comm_group H] [inner_product_space ℝ H]
 [complete_space H] (r : X → H) (hr : integrable r μ) (unit : ∀ x, ‖r x‖=1) :
 (∫ x, ∫ y, ‖r x-r y‖^2 ∂μ ∂μ)/2 = 1-‖∫ x,r x ∂μ‖^2 :=
begin
 let m := ∫ x,r x ∂μ,
 have first : ∀ x, (∫ y, ‖r x-r y‖^2 ∂μ)=2-2*@inner ℝ H _ (r x) m,
 { intro x,
   have h : ∀ y, ‖r x-r y‖^2=2-2*@inner ℝ H _ (r x) (r y) :=
     λ y, by rw [norm_sub_sq_real,unit x,unit y];ring,
   simp_rw [h],
   have ha : integrable (λ y, @inner ℝ H _ (r x) (r y)) μ := hr.const_inner (r x),
   rw [integral_sub (integrable_const (2:ℝ)) (ha.const_mul (2:ℝ)),
       integral_mul_left,integral_inner hr],
   simp [m,integral_const] },
 simp_rw [first],
 have swap : ∀ x, @inner ℝ H _ (r x) m=@inner ℝ H _ m (r x) :=
  λ x, real_inner_comm _ _,
 simp_rw [swap],
 have hb : integrable (λ x, @inner ℝ H _ m (r x)) μ := hr.const_inner m,
 rw [integral_sub (integrable_const (2:ℝ)) (hb.const_mul (2:ℝ)),
     integral_mul_left,integral_inner hr],
 change ((∫ x : X, (2:ℝ) ∂μ) - 2*@inner ℝ H _ m m)/2=1-‖m‖^2,
 simp [integral_const,real_inner_self_eq_norm_sq];ring
end

theorem first_time_unit_mass : (∫ s : ℝ in set.Ioi 0,real.exp (-s))=1 :=
integral_exp_neg_Ioi_zero
theorem first_time_factor (a b : ℝ) (ha : 0<a) (hb : 0<b) :
 a*b/((a^2+b^2)/2)=2*a*b/(a^2+b^2) :=
begin
 have hn : 0<a^2+b^2 := by positivity,
 have hn' : (a^2+b^2)/2≠0 := by positivity,
 field_simp [hn',ne_of_gt hn];ring
end
theorem first_time_contraction (a b : ℝ) (ha : 0<a) (hb : 0<b) :
 2*a*b/(a^2+b^2)≤1 :=
begin
 have hn : 0<a^2+b^2 := by positivity,
 apply (div_le_iff hn).2,nlinarith only [sq_nonneg (a-b)]
end
theorem first_time_matrix : (2*28/(28^2+1):ℝ)=56/785 := by norm_num
theorem first_time_finite (v p : ℝ) : p+v*(1-p)=v+(1-v)*p := by ring
theorem conditional_weights (w a b : ℝ) (hw : 0<w) (hw' : w<1)
 (ha : 0<a) (hb : 0<b) :
 w*a/(w*a+(1-w)*b)=w ↔ a=b :=
begin
 have pos : 0 < w*a+(1-w)*b :=
   add_pos (mul_pos hw ha) (mul_pos (sub_pos.mpr hw') hb),
 rw [div_eq_iff (ne_of_gt pos)],split,
 { intro h,
   have hz : (a-b)*(w*(1-w))=0 := by linear_combination h,
   exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right
       (ne_of_gt (mul_pos hw (sub_pos.mpr hw')))) },
 { intro h,rw [h],ring }
end

theorem refine_pair (weights : finset ℕ) (p : ℕ → ℝ) (cap : ℝ)
 (nonneg : ∀ j∈weights,0≤p j) (bounded : ∀ j∈weights,p j≤cap)
 (total : ∑ j in weights,p j=1) : ∑ j in weights,(p j)^2≤cap :=
begin
 calc ∑ j in weights,(p j)^2 ≤ ∑ j in weights,cap*p j :
   finset.sum_le_sum (λ j hj,by rw [pow_two];exact mul_le_mul_of_nonneg_right (bounded j hj) (nonneg j hj))
 ... = cap : by rw [←finset.mul_sum,total,mul_one]
end

def square_primitive (z : ℝ) :=
 z-2*z^3+3*z^5-(20/7)*z^7+(5/3)*z^9-(6/11)*z^11+z^13/13
theorem square_derivative (z : ℝ) :
 has_deriv_at square_primitive ((1-z^2)^6) z :=
begin
 have h := has_deriv_at_id z,
 have d1 := h.sub ((h.pow 3).const_mul 2),
 have d2 := d1.add ((h.pow 5).const_mul 3),
 have d3 := d2.sub ((h.pow 7).const_mul (20/7:ℝ)),
 have d4 := d3.add ((h.pow 9).const_mul (5/3:ℝ)),
 have d5 := d4.sub ((h.pow 11).const_mul (6/11:ℝ)),
 have d := d5.add ((h.pow 13).div_const 13),
 convert d using 1;try {ext x};simp [square_primitive];ring
end
theorem bin_limit_constant :
 (35/16:ℝ)^2*(∫ x in (0:ℝ)..1,(1-x^2)^6)=700/429 :=
begin
 have hc : continuous (λ x:ℝ,(1-x^2)^6) := by continuity,
 rw [interval_integral.integral_eq_sub_of_has_deriv_at
    (λ x hx,square_derivative x) (hc.interval_integrable _ _)],
 norm_num [square_primitive]
end
theorem frame_normalization : (44:ℝ)*(9/8)*(2/(9*11))=1 := by norm_num
theorem damped_action (a b c d : ℝ) :
 (a^2+b^2+c^2+d^2)/2-(a*c+b*d)=((a-c)^2+(b-d)^2)/2 := by ring
theorem rank_pair_step (n rank diag : ℝ) :
 (n+rank)^2-(diag+rank^2)=n^2-diag+2*n*rank := by ring
theorem rank_bound (n diag : ℝ) (h : n≤diag) :
 n^2-diag≤n*(n-1) := by nlinarith only [h]
theorem observer_exclusive (w1 w2 eff1 eff2 : ℝ) :
 w1*eff1+w2*eff2+((1-w1-w2)+w1*(1-eff1)+w2*(1-eff2))=1 := by ring

theorem stationary_occupancy (u d : ℝ) (h : u+d≠0) :
 u*(1-u/(u+d))-d*(u/(u+d))=0 := by field_simp [h];ring
theorem identical_observers_infinite (p : ℝ) (hp : 0≤p)
 (finite_bounds : ∀ n:ℕ,(n:ℝ)*p≤1) : p=0 :=
begin
 by_contra h,
 have pos : 0<p := lt_of_le_of_ne hp (ne.symm h),
 obtain ⟨n,hn⟩ := exists_nat_gt (1/p),
 have contra := (div_lt_iff pos).1 hn,
 linarith only [finite_bounds n,contra]
end

def gaussian_kernel (D y : ℝ) := real.exp (-(y^2)/(2*D))
def layer_amplitude (D a y : ℝ) := real.exp (a*y-D*a^2)

theorem gaussian_layer_shift (D a b y : ℝ) (hd : D≠0) :
 gaussian_kernel D y*layer_amplitude D a y*layer_amplitude D b y =
 real.exp (-D*(a-b)^2/2)*gaussian_kernel D (y+(-(D*(a+b)))) :=
begin
 unfold gaussian_kernel layer_amplitude,
 rw [←real.exp_add,←real.exp_add,←real.exp_add],
 congr' 1, field_simp [hd];ring
end

theorem gaussian_layer_overlap (D a b : ℝ) (hd : D≠0) :
 (∫ y:ℝ, gaussian_kernel D y*layer_amplitude D a y*layer_amplitude D b y) =
 real.exp (-D*(a-b)^2/2)*(∫ y:ℝ, gaussian_kernel D y) :=
begin
 simp_rw [gaussian_layer_shift D a b _ hd],
 rw [integral_mul_left,integral_add_right_eq_self (gaussian_kernel D)];apply_instance
end

theorem gaussian_born_normal (D a : ℝ) (hd : D≠0) :
 (∫ y:ℝ, gaussian_kernel D y*layer_amplitude D a y*layer_amplitude D a y) =
 (∫ y:ℝ, gaussian_kernel D y) :=
by rw [gaussian_layer_overlap D a a hd];simp
theorem continuous_compose (a D E y z : ℝ) :
 layer_amplitude D a y*layer_amplitude E a z=layer_amplitude (D+E) a (y+z) :=
by unfold layer_amplitude;rw [←real.exp_add];congr' 1;ring
theorem exposure_additive (a b D E : ℝ) :
 real.exp (-(D+E)*(a-b)^2/2) =
 real.exp (-D*(a-b)^2/2)*real.exp (-E*(a-b)^2/2) :=
by rw [←real.exp_add];congr' 1;ring
theorem zero_exposure (a b : ℝ) : real.exp (-(0:ℝ)*(a-b)^2/2)=1 := by simp
theorem onset_positive (D a b : ℝ) (hd : 0<D) (hab : a≠b) :
 real.exp (-D*(a-b)^2/2)<1 :=
begin
 have h2 : 0<(a-b)^2 := sq_pos_of_ne_zero _ (sub_ne_zero.mpr hab),
 have h3 := mul_pos hd h2,
 calc real.exp (-D*(a-b)^2/2)<real.exp 0 : real.exp_lt_exp.mpr (by nlinarith only [h3])
 ... = 1 : real.exp_zero
end

-- Positive occupation of two disjoint cells below the same sharp marginal.
-- u and v are the parts in and out of the first cell, respectively.
theorem disjoint_occupation {V : Type*} [add_comm_group V] (q p d : V → ℝ)
 (pos : ∀ x,0≤q x) (left : ∀ x,q x≤p x) (right : ∀ x,q x≤d x)
 (parallelogram : ∀ u v, q (u+v)+q (u-v)=2*q u+2*q v)
 (split_cells : ∀ x,∃ u v,x=u+v ∧ d u=0 ∧ p v=0) (x : V) : q x=0 :=
begin
 obtain ⟨u,v,h,hu,hv⟩ := split_cells x,
 rw [h],have A := right u,have B := left v,rw [hu] at A,rw [hv] at B,
 linarith only [A,B,parallelogram u v,pos (u-v),pos (u+v)]
end

theorem product_weights_nonaffine : ((1/2:ℝ)*(1/2) ≠ (1*0+0*1)/2) := by norm_num

theorem two_material_references (y z s t : ℝ) (hst : s≠t)
 (hs : (y-s)^2=(z-s)^2) (ht : (y-t)^2=(z-t)^2) : y=z :=
begin
 have h : (s-t)*(y-z)=0 := by linear_combination (ht-hs)/2,
 exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hst))
end
theorem mirror_gap (y s : ℝ) : (y-s)^2-(-y-s)^2= -4*y*s := by ring
theorem equal_layer_response (a D : ℝ) : real.exp (-D*(a-a)^2/2)=1 := by simp

section recoil
variables {A : Type*} [ring A]
def comm (a b : A) := a*b-b*a
theorem comm_product (a p q : A) : comm a (p*q)=comm a p*q+p*comm a q :=
by unfold comm;noncomm_ring
theorem comm_sum (a p q : A) : comm a (p+q)=comm a p+comm a q :=
by unfold comm;noncomm_ring
theorem recoil_double_commutator (a p : A) (h : comm a (comm a p)=0) :
 comm a (comm a (p*p))=comm a p*comm a p+comm a p*comm a p :=
by rw [comm_product a p p,comm_sum,comm_product,comm_product,h];simp
end recoil

-- The arc estimate uses the integral of the squared deviation of a' from its mean.
theorem arc_gradient_budget (l : ℝ) (hl : 0<l) (a g : ℝ → ℝ) (hg : continuous g)
 (deriv : ∀ t, has_deriv_at a (g t) t) :
 (a l-a 0)^2/l ≤ ∫ u in (0:ℝ)..l,(g u)^2 :=
begin
 let d := a l-a 0,
 have fund : (∫ u in (0:ℝ)..l,g u)=d :=
 interval_integral.integral_eq_sub_of_has_deriv_at (λ x hx,deriv x) (hg.interval_integrable _ _),
 have positive : 0≤∫ u in (0:ℝ)..l,(g u-d/l)^2 :=
  interval_integral.integral_nonneg hl.le (λ x hx,sq_nonneg _),
 have expand : (λ u:ℝ,(g u-d/l)^2)=(λ u:ℝ,(g u)^2-(2*d/l)*g u+(d/l)^2) :=
  funext (λ u,by ring),
 have c : continuous (λ u:ℝ,(g u)^2-(2*d/l)*g u) :=
  (hg.pow 2).sub (continuous_const.mul hg),
 rw [expand,interval_integral.integral_add (c.interval_integrable _ _)
       (continuous_const.interval_integrable _ _),
     interval_integral.integral_sub ((hg.pow 2).interval_integrable _ _)
       ((continuous_const.mul hg).interval_integrable _ _),
     interval_integral.integral_const_mul,fund] at positive,
 simp only [interval_integral.integral_const,sub_zero,smul_eq_mul] at positive,
 have cancel : 2*d/l*d-l*(d/l)^2=d^2/l := by field_simp [ne_of_gt hl];ring,
 change d^2/l ≤ _,linarith only [positive,cancel],
 all_goals {apply_instance}
end
theorem opposite_modes_momentum (ps pr kick : ℝ) :
 (ps+kick)+(pr-kick)=ps+pr := by ring
theorem recoil_energy (p kick m : ℝ) :
 ((p+kick)^2-p^2)/(2*m)=(2*p*kick+kick^2)/(2*m) := by ring
theorem matched_exchange (a b transfer : ℝ) :
 (a+transfer)+(b-transfer)=a+b := by ring

end bound_graviton_breakup
