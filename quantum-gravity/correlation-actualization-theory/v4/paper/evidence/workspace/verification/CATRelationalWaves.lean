import tactic
import algebra.big_operators.order
import data.real.sqrt
import analysis.ODE.picard_lindelof
import data.complex.exponential
import algebra.order.chebyshev
import linear_algebra.matrix.determinant
import data.matrix.notation

/- Exact algebra of the null matrix sector, transverse metric and conditional
   readouts. Smooth operator realizations and the physical receiver identification
   are hypotheses in the companion. -/
namespace cat_relational_waves
noncomputable theory
open_locale big_operators nnreal

def bracket {A : Type*} [ring A] (a b : A) : A := a*b-b*a
theorem jacobi {A : Type*} [ring A] (u v w : A) :
 bracket u (bracket v w)-bracket v (bracket u w)=bracket (bracket u v) w :=
by {unfold bracket, noncomm_ring}
theorem equal_null_orders {A : Type*} [ring A] (u v w : A)
 (h : bracket (bracket u v) w=0) : bracket u (bracket v w)=bracket v (bracket u w) :=
sub_eq_zero.mp ((jacobi u v w).trans h)

theorem commuting_functions {A : Type*} [ring A] (f g y : A)
 (hfg : f*g=g*f) (hyf : y*f=f*y) (hyg : y*g=g*y) :
 bracket (f*y) (g*y)=0 :=
begin
 unfold bracket, apply sub_eq_zero.mpr,
 calc f*y*(g*y) = f*(y*g)*y : by simp only [mul_assoc]
 ... = f*(g*y)*y : by rw [hyg]
 ... = (f*g)*(y*y) : by simp only [mul_assoc]
 ... = (g*f)*(y*y) : by rw [hfg]
 ... = g*(f*y)*y : by simp only [mul_assoc]
 ... = g*(y*f)*y : by rw [hyf]
 ... = g*y*(f*y) : by simp only [mul_assoc]
end

theorem harmonic_double_commutator (f a : ℝ) :
 (-a + a) + (f^2*(-a)+f^2*a)=0 := by ring
def kinetic_density (s h c d : ℝ) : matrix (fin 4) (fin 4) ℝ :=
 !![0,-1,0,0; -1,h,c,d; 0,c,s,0; 0,d,0,s]
theorem density_determinant (s h c d : ℝ) :
 (kinetic_density s h c d).det= -s^2 :=
begin
 let A := kinetic_density s h c d,
 have h0 : A 0 0=0 := rfl, have h1 : A 0 1= -1 := rfl,
 have h2 : A 0 2=0 := rfl, have h3 : A 0 3=0 := rfl,
 change A.det= -s^2,
 rw [matrix.det_succ_row_zero,fin.sum_univ_four,h0,h1,h2,h3],
 simp only [mul_zero,zero_mul,add_zero,zero_add,fin.coe_one,pow_one,neg_mul_neg,one_mul],
 rw [matrix.det_fin_three],
 change (-1:ℝ)*s*s-(-1)*0*0-c*0*s+c*0*0+d*0*0-d*s*0= -s^2,
 ring
end
theorem conformal_norm (s x y : ℝ) :
 (s*x-y)^2+(x+s*y)^2=(s^2+1)*(x^2+y^2) := by ring
theorem inverse_polarization (s a b : ℝ) :
 let d := s^2+1, x := (s*a+b)/d, y := (s*b-a)/d in
 s*x-y=a ∧ x+s*y=b :=
begin
 dsimp, have hd : s^2+1 ≠ 0 := by nlinarith [sq_nonneg s],
 split; field_simp [hd]; ring
end
theorem vacuum_condition (f fp a b : ℝ) :
 2*(fp^2/(1+f^2)-(a^2+b^2)/(1+f^2)^2)=0 ↔
 a^2+b^2=(1+f^2)*fp^2 :=
begin
 have hs : 1+f^2≠0 := by nlinarith [sq_nonneg f],
 split,
 { intro h, field_simp [hs] at h, nlinarith },
 { intro h, rw [h], field_simp [hs], ring }
end
theorem affine_vacuum (s a b k : ℝ) (hs : 0<s)
 (h : k^2=((a/s)^2+(b/s)^2)/s) : a^2+b^2=s*(s*k)^2 :=
begin
 have hn := ne_of_gt hs, field_simp [hn] at h, nlinarith
end
theorem eigen_tide (r : ℝ) (h : r^2=2) :
 (1-r)*(-1-r)-1=0 := by nlinarith
theorem jacobi_area (x y z w dx dy dz dw kp kc : ℝ) :
 dx*dy+ x*(kp*y+kc*w)+dz*dw+z*(kc*y-kp*w)
 -(dy*dx+y*(kp*x+kc*z)+dw*dz+w*(kc*x-kp*z))=0 := by ring

theorem bracket_product {A : Type*} [ring A] (x y z : A) :
 bracket x (y*z)=bracket x y*z+y*bracket x z :=
by { unfold bracket, noncomm_ring }
theorem bracket_plus {A : Type*} [ring A] (x y z : A) :
 bracket x (y+z)=bracket x y+bracket x z := by {unfold bracket,noncomm_ring}
theorem bracket_minus {A : Type*} [ring A] (x y z : A) :
 bracket x (y-z)=bracket x y-bracket x z := by {unfold bracket,noncomm_ring}
@[simp] theorem bracket_self {A : Type*} [ring A] (x : A) : bracket x x=0 := sub_self _
@[simp] theorem bracket_zero {A : Type*} [ring A] (x : A) : bracket x 0=0 :=
by simp [bracket]
theorem bracket_flip {A : Type*} [ring A] (x y : A) : bracket x y= -bracket y x :=
by {unfold bracket,abel}
def lap {A : Type*} [ring A] (y z p : A) := bracket y (bracket y p)+bracket z (bracket z p)
theorem plane_harmonics {A : Type*} [ring A] (y z c : A)
 (hyz : bracket y z=c) (hyc : bracket y c=0) (hzc : bracket z c=0) :
 lap y z (y*y-z*z)=0 ∧ lap y z (y*z+z*y)=0 :=
begin
 have hzy : bracket z y= -c := (bracket_flip z y).trans (congr_arg has_neg.neg hyz),
 have neg_rule : ∀ p q : A, bracket p (-q)= -bracket p q :=
   λ p q, by simp [bracket],
 split; unfold lap;
 simp only [bracket_minus,bracket_plus,bracket_product,bracket_self,bracket_zero,
   hyz,hzy,hyc,hzc,neg_rule,zero_mul,mul_zero,zero_add,add_zero,neg_zero,neg_mul,mul_neg];
 abel
end

theorem transverse_density (s c d h : ℝ) :
 let inv_uu := c^2+d^2-s*h in
 (-1)*(inv_uu/s)-h+(c*c+d*d)/s=0 ∨ s=0 :=
begin
 dsimp, by_cases hs : s=0, { exact or.inr hs },
 left, field_simp [hs], ring
end
theorem transported_screen (a b x y : ℝ) (h : x^2+y^2=1) :
 ((x^2-y^2)*a-2*x*y*b)^2+(2*x*y*a+(x^2-y^2)*b)^2=a^2+b^2 :=
begin
 have hn : ((x^2-y^2)*a-2*x*y*b)^2+(2*x*y*a+(x^2-y^2)*b)^2 =
   (x^2+y^2)^2*(a^2+b^2) := by ring,
 rw [hn,h], ring
end
theorem inverse_speed_bound (s x y a b : ℝ)
 (ha : a=s*x-y) (hb : b=x+s*y) :
 x^2+y^2≤a^2+b^2 :=
begin
 rw [ha,hb,conformal_norm],
 nlinarith [mul_nonneg (sq_nonneg s) (add_nonneg (sq_nonneg x) (sq_nonneg y))]
end
theorem initial_margin {E : Type*} [normed_add_comm_group E]
 (start shift : E) (budget : ℝ) (hs : budget<‖start‖)
 (hd : ‖shift‖≤budget) : 0<‖start+shift‖ :=
begin
 have ht : ‖start‖≤‖start+shift‖+‖shift‖ :=
   calc ‖start‖ = ‖start+shift+ -shift‖ : by simp
   ... ≤ ‖start+shift‖+‖-shift‖ : norm_add_le _ _
   ... = _ : by rw [norm_neg],
 linarith
end

/- Closed-interval existence for the inverse polarizations. Scale the f
   coordinate by ell so that the entire time interval fits a Picard ball.
   The two transverse components live in the Euclidean complex plane. -/
def inverse_field (ell : ℝ) (drive : ℝ → ℝ → ℂ) (t : ℝ) (x : ℝ × ℂ) : ℝ × ℂ :=
 (‖x.2‖/(ell*real.sqrt (1+(ell*x.1)^2)), drive t (ell*x.1))

theorem inverse_interval (T K ell : ℝ) (x₀ : ℝ × ℂ) (drive : ℝ → ℝ → ℂ)
 (L : ℝ≥0) (hT : 0≤T) (hK : 0<K) (he : 0<ell)
 (hsize : ‖x₀.2‖+K*T≤K*ell)
 (hdrive : ∀ t ∈ set.Icc (0:ℝ) T, ∀ f, ‖drive t f‖≤K)
 (hcont : ∀ x ∈ metric.closed_ball x₀ (K*T),
    continuous_on (λ t, inverse_field ell drive t x) (set.Icc (0:ℝ) T))
 (hlip : ∀ t ∈ set.Icc (0:ℝ) T,
    lipschitz_on_with L (inverse_field ell drive t) (metric.closed_ball x₀ (K*T))) :
 ∃ x : ℝ → ℝ × ℂ, x 0=x₀ ∧ ∀ t ∈ set.Icc (0:ℝ) T,
  has_deriv_within_at x (inverse_field ell drive t (x t)) (set.Icc (0:ℝ) T) t :=
begin
 apply @exists_forall_deriv_within_Icc_eq_of_is_picard_lindelof (ℝ × ℂ) _ _ _
   (inverse_field ell drive) 0 0 T x₀ K (K*T) L,
 refine { ht₀ := ⟨le_rfl,hT⟩, hR := mul_nonneg hK.le hT, lipschitz := hlip,
   cont := hcont, norm_le := _, C_mul_le_R := _ },
 { intros t ht x hx,
   have hd : dist x.2 x₀.2≤K*T := (le_max_right _ _).trans (metric.mem_closed_ball.mp hx),
   have hm : ‖x.2‖≤‖x₀.2‖+K*T :=
     calc ‖x.2‖ = ‖(x.2-x₀.2)+x₀.2‖ : by rw [sub_add_cancel]
     ... ≤ ‖x.2-x₀.2‖+‖x₀.2‖ : norm_add_le _ _
     ... ≤ _ : by {rw [dist_eq_norm] at hd, linarith},
   have hr : 1≤real.sqrt (1+(ell*x.1)^2) :=
     calc (1:ℝ) = real.sqrt 1 : real.sqrt_one.symm
     ... ≤ _ : real.sqrt_le_sqrt (by nlinarith [sq_nonneg (ell*x.1)]),
   have hd' : 0<ell*real.sqrt (1+(ell*x.1)^2) := mul_pos he (by linarith),
   change max (‖(‖x.2‖/(ell*real.sqrt (1+(ell*x.1)^2)) : ℝ)‖) (‖drive t (ell*x.1)‖) ≤ K,
   apply max_le,
   { rw [real.norm_eq_abs,abs_of_nonneg (div_nonneg (norm_nonneg _) hd'.le)],
     apply (div_le_iff hd').mpr,
     exact (hm.trans hsize).trans (by nlinarith [mul_nonneg
       (mul_pos hK he).le (sub_nonneg.mpr hr)]) },
   { exact hdrive t ht _ } },
 { simp [max_eq_left hT] }
end

theorem tetra_second_moment (x y z : ℝ) :
 (x+y+z)^2+(x-y-z)^2+(-x+y-z)^2+(-x-y+z)^2=4*(x^2+y^2+z^2) := by ring
theorem four_site_tide (yy zz cross : ℝ) :
 ((yy+zz+2*cross)-(yy+zz-2*cross))/4=cross := by ring
theorem balanced_loss (p : ℝ) :
 (1-p)^2+p^2=1-2*p*(1-p) := by ring
theorem charge_cancellation (p r : ℝ) :
 (1-p)*(1-r)+p*(1-r)=1-r := by ring
theorem history_return (p r : ℝ) :
 ((1-p)*(1-r))^2+((1-p)*r)^2+(p*r)^2+(p*(1-r))^2
 = ((1-p)^2+p^2)*((1-r)^2+r^2) := by ring
theorem surviving_prefix {I : Type*} (s : finset I) (w : I → ℝ) (p : ℝ)
 (h : ∑ i in s, w i = 1) : ∑ i in s, p*w i = p :=
by rw [←finset.mul_sum,h,mul_one]
theorem four_receivers :
 ((1:ℝ)/16)^2+(15/16)^2=226/256 ∧
 (1+16+36+16+1:ℝ)/256=70/256 ∧ ((1:ℝ)/2)^4=1/16 := by norm_num
theorem phonon_fine (v : ℝ) : ((1-v)/2)^2+2*((1+v)/4)^2=(3-2*v+3*v^2)/8 := by ring
theorem phonon_coarse (v : ℝ) : ((1-v)/2)^2+((1+v)/2)^2=(1+v^2)/2 := by ring
theorem phonon_minimum (v : ℝ) : 1/3≤(3-2*v+3*v^2)/8 :=
by nlinarith [sq_nonneg (3*v-1)]
theorem rank_budget (q x y t : ℝ) (hx : x≤t*q) (hy : y≤1-q) :
 x+y≤1-q*(1-t) := by nlinarith
theorem rank_example (q : ℝ) (h : 4/5≤q) :
 1-q*(1-(1:ℝ)/4)≤2/5 := by linarith

def wave_drive (k : ℝ → ℂ) (t f : ℝ) : ℂ :=
 -(complex.exp (((-(f^2) : ℝ) : ℂ)*complex.I)*k t) /
   (((1+f^2 : ℝ) : ℂ)+complex.I)
theorem wave_drive_bound (k : ℝ → ℂ) (t f : ℝ) : ‖wave_drive k t f‖≤‖k t‖ :=
begin
 let z : ℂ := ((1+f^2 : ℝ) : ℂ)+complex.I,
 have hreal : z.re=1+f^2 := by simp only [z,complex.add_re,complex.of_real_re,complex.I_re,add_zero],
 have hz : 1≤‖z‖ := calc (1:ℝ) ≤ 1+f^2 : by nlinarith [sq_nonneg f]
  ... = z.re : hreal.symm
  ... ≤ complex.abs z : complex.re_le_abs _
  ... = ‖z‖ : rfl,
 have hphase : ‖complex.exp (((-(f^2) : ℝ) : ℂ)*complex.I)‖=1 :=
   complex.abs_exp_of_real_mul_I _,
 change ‖-(complex.exp (((-(f^2) : ℝ) : ℂ)*complex.I)*k t)/z‖≤‖k t‖,
 rw [norm_div,norm_neg,norm_mul,hphase,one_mul],
 exact (div_le_iff (by linarith : 0<‖z‖)).mpr
    (by nlinarith [mul_nonneg (norm_nonneg (k t)) (sub_nonneg.mpr hz)])
end

theorem singular_value_bound {I : Type*} (s : finset I) (sv : I → ℝ) :
 (∑ i in s, sv i)^2 ≤ (s.card:ℝ)*∑ i in s, (sv i)^2 :=
sq_sum_le_card_mul_sum_sq

theorem ray_jacobi (m b r rd ss cc : ℝ) (hr : r≠0) :
 (b^2/r^3-3*m*b^2/r^4)*ss+2*rd*cc*(b/r^2)
 +r*((-ss)*(b/r^2)^2+cc*(-2*b*rd/r^3)) =
 (-3*m*b^2/r^5)*(r*ss) :=
by {field_simp [hr],ring}
theorem infall_cone (w c : ℝ) (h : 1+w*c≠0) :
 (1-(c+w)/(1+w*c))/2=(1-w)*(1-c)/(2*(1+w*c)) :=
by {field_simp [h],ring}
theorem escape_rationalization (w c ep y : ℝ) (h₁ : (1-w)*(1+w)=ep)
 (h₂ : (1-c)*(1+c)=ep*y) :
 (1-w)*(1-c)*((1+w)*(1+c))=ep^2*y :=
begin
 have hx : (1-w)*(1-c)*((1+w)*(1+c))=((1-w)*(1+w))*((1-c)*(1+c)) := by ring,
 rw [hx,h₁,h₂], ring
end
theorem horizon_coefficient :
 ((27/4:ℝ)/(2*(1+1)*(1+1)*(1+1*1)))=27/64 := by norm_num
theorem radial_tide (m r : ℝ) : 3*m*(0:ℝ)^2/r^5=0 := by simp

end cat_relational_waves
