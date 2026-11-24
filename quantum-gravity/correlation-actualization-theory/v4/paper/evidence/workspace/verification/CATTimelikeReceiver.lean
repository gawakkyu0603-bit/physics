import tactic
import algebra.big_operators.order
import analysis.special_functions.pow.real
import analysis.special_functions.integrals
import analysis.inner_product_space.basic

namespace cat_timelike_receiver
noncomputable theory
open_locale big_operators

def br {A : Type*} [ring A] (x y : A) := x*y-y*x
theorem trace_double {A B : Type*} [ring A] [add_comm_group B]
 (tr : A →+ B) (cyc : ∀ x y, tr (x*y)=tr (y*x)) (x w : A) :
 tr (w*br x (br x w))= - tr (br x w *br x w) :=
begin
 let d:=br x w,
 change tr (w*(x*d-d*x))= -tr ((x*w-w*x)*d),
 calc tr (w*(x*d-d*x))=tr ((w*x)*d)-tr ((w*d)*x) : by simp [mul_sub,mul_assoc]
 ... =tr ((w*x)*d)-tr ((x*w)*d) : by rw [cyc (w*d) x,mul_assoc x w d]
 ... = -tr ((x*w-w*x)*d) : by {rw [sub_mul,map_sub],abel}
end
theorem finite_color_norms {ι : Type*} [fintype ι] (v : ι→ℝ)
 (h : ∑ i,v i^2=0) (i : ι) : v i=0 :=
begin
 have hi := finset.single_le_sum (λ j (hj : j∈finset.univ),sq_nonneg (v j)) (finset.mem_univ i),
 rw [h] at hi, change v i^2≤0 at hi,
 by_contra hn, exact (not_le.mpr (sq_pos_of_ne_zero _ hn)) hi
end
theorem null_sphere (w : ℝ) (h : 2*w^3=0) : w=0 :=
by {have hh : w^3=0 := by linarith,exact (pow_eq_zero_iff (by norm_num : 0<(3:ℕ))).mp hh}
theorem jacobi_oscillator (w : ℝ) : 2*(-w^3)+2*w^3=0 := by ring
theorem ordinary_energy (w v : ℝ) : 2*v*(-2*w^3)+4*w^3*v=0 := by ring
theorem flat_clock (s p t q : ℝ) :
 ((s-p)*(t+q)+(s+p)*(t-q))/2=s*t-p*q := by ring
theorem singlet_kernel (C u v : ℝ) :
 C^2*(u^2+v^2-2*u*v)=C^2*(u-v)^2 := by ring
theorem material_metric (c : ℝ) (h : c≠0) :
 (-c)*(1/c)*c*c= -c^2 ∧ c/(-c) = -1 ∧ c/(1/c)=c^2 ∧ c/c=1 :=
by {split, {field_simp [h];ring},split,{field_simp [h]},split;field_simp [h];ring}
theorem opposing_expansion (v c d : ℝ) (hc : c≠0) (hd : d≠0) :
 ((-(v/c^2))/(1/c))/(2*d)= -(v/c/(2*d)) :=
by {field_simp [hc,hd];ring}
theorem crossing_before (R v t T w : ℝ) (hv : 0<v) (ht : t<T) (hw : |w|≤R) :
 |w|<R+v*(T-t) := by linarith [mul_pos hv (sub_pos.mpr ht)]
theorem edge_gap (j m : ℝ) (hj : 0≤j) (hm : m≤j-1/2) :
 2*j+1/4≤(j+1/2)^2-2*j*m+j^2 :=
begin
 have hz : 0≤2*j*(j-1/2-m) := mul_nonneg (by linarith) (sub_nonneg.mpr hm),
 calc 2*j+1/4≤2*j+1/4+2*j*(j-1/2-m) : le_add_of_nonneg_right hz
 ... = (j+1/2)^2-2*j*m+j^2 : by ring
end
theorem axial_zero (j R : ℝ) : (-R)*j+j*R=0 := by ring
theorem signed_volume (w a b c : ℝ) : (w*a)*(w*b)*(w*c)=w^3*(a*b*c) := by ring
theorem turning_mode (omega k c a : ℝ) : omega^2+k^2+c^2*(a-a)^2=omega^2+k^2 := by ring
theorem clock_transfer_work (v Qp mass a acc mu h : ℝ)
 (eqn : mass*acc=h*Qp*v-2*mu*a^3) :
 mass*v*acc-h*Qp*v^2/2+2*mu*a^3*v-h*v^2*Qp/2=0 :=
begin
 calc mass*v*acc-h*Qp*v^2/2+2*mu*a^3*v-h*v^2*Qp/2 =
   v*(mass*acc-(h*Qp*v-2*mu*a^3)) : by ring
 ... = 0 : by rw [eqn,sub_self,mul_zero]
end
theorem field_work (x y p q f h v : ℝ) :
 p*(-(f^2+h*v^2)*x)+q*(-(f^2+h*v^2)*y)+f^2*(x*p+y*q)
 = - h*v^2*((2*(x*p+y*q))/2) := by ring
theorem turning_energy (mu r R f n : ℝ)
 (e : mu*R^4/2+f/2=mu*r^4/2+f*(n+1/2)) :
 mu*(R^4-r^4)/2=f*n := by linarith only [e]
theorem number_nonneg (x y p q w : ℝ) (hw : 0<w)
 (wr : y*p-x*q=1/2) :
 0≤(p^2+q^2+w^2*(x^2+y^2))/(2*w)-1/2 :=
begin
 refine sub_nonneg.mpr ((le_div_iff (show 0<2*w, by linarith)).2 _),
 have e : p^2+q^2+w^2*(x^2+y^2)=(p-w*y)^2+(q+w*x)^2+2*w*(y*p-x*q) := by ring,
 rw [e,wr], linarith only [sq_nonneg (p-w*y),sq_nonneg (q+w*x)],
 all_goals {apply_instance}
end
theorem number_strict (n p : ℝ) (hn : 0<n) (hp : 0≤p)
 (h : p^2*(1+n)=1) : p<1 :=
begin
 by_contra z, push_neg at z,
 have sq : 1≤p^2 := by nlinarith only [sq_nonneg (p-1),z],
 nlinarith only [h,sq,mul_pos hn (lt_of_lt_of_le zero_lt_one sq)]
end
theorem perpendicular_projection {A : Type*} [ring A] (s d : A) (hh : s*s=1)
 (anti : s*d= -(d*s)) : d+s*d*s=0 :=
by {rw [anti,neg_mul,mul_assoc,hh,mul_one,add_neg_self]}
theorem square_difference_bound (x y h : ℝ) (hx : |x|≤1) (hy : |y|≤1)
 (hd : |x-y|≤h) : |x^2-y^2|≤2*h :=
begin
 have ident : x^2-y^2=(x-y)*(x+y) := by ring,
 rw [ident,abs_mul], have hs : |x+y|≤2 := by linarith only [abs_add x y,hx,hy],
 calc |x-y|*|x+y|≤h*2 : mul_le_mul hd hs (abs_nonneg _) ((abs_nonneg _).trans hd)
 ... =2*h : mul_comm _ _
end
open measure_theory set
open_locale interval
theorem midpoint_error (b v k : ℝ) (hk : 0<k) (err : ℝ → ℝ)
 (he : interval_integrable err volume (-(k/2)) (k/2))
 (relation : k*(b-v)=∫ x in (-(k/2))..(k/2), err x)
 (bound : ∀ x∈Icc (-(k/2)) (k/2), |err x|≤3*x^2) : |b-v|≤k^2/4 :=
begin
 have hends : -(k/2)≤k/2 := by linarith,
 have eh : interval_integrable (λ x:ℝ,x^2) volume (-(k/2)) (k/2) :=
   (continuous_id.pow 2).interval_integrable _ _,
 have comp := interval_integral.integral_mono_on hends he.norm (eh.const_mul 3)
   (λ x hx,show ‖err x‖≤3*x^2, by simpa only [real.norm_eq_abs] using bound x hx),
 have base : ‖∫ x in (-(k/2))..(k/2),err x‖≤∫ x in (-(k/2))..(k/2), ‖err x‖ :=
   interval_integral.norm_integral_le_integral_norm hends,
 have hi : |k*(b-v)|≤∫ x in (-(k/2))..(k/2),3*x^2 :=
 by {rw [relation,←real.norm_eq_abs], exact le_trans base comp},
 have rhs : (∫ x in (-(k/2))..(k/2),(3:ℝ)*x^2)=k*(k^2/4) :=
 by {rw [interval_integral.integral_const_mul,integral_pow],norm_num,ring},
 rw [abs_mul,abs_of_pos hk,rhs] at hi, exact le_of_mul_le_mul_left hi hk
end
end cat_timelike_receiver
