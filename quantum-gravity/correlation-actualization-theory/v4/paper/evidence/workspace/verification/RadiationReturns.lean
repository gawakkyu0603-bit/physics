import tactic
import analysis.special_functions.integrals
import measure_theory.integral.bochner
import data.complex.basic
import data.nat.choose.basic

noncomputable theory
open measure_theory finset
open_locale big_operators
namespace radiation_returns

-- Opposite-port amplitudes in an arbitrary local spin frame.
-- The singlet transforms by the determinant of the spin-frame change.
theorem rotated_singlet (a b c d : ℂ) (h : a*d-b*c=1) :
 (a*b-b*a, a*d-b*c, c*b-d*a, c*d-d*c)=(0,1,-1,0) :=
by {rw [h,show a*b-b*a=0,by ring,show c*d-d*c=0,by ring,
 show c*b-d*a = -(a*d-b*c),by ring,h]}
-- Basis order ++,+-,-+,--. Both branches have the same occupied ports.
def ordered₀ (v : ℂ × ℂ × ℂ × ℂ) : ℂ × ℂ × ℂ × ℂ := (0,0,v.2.2.1,0)
def ordered₁ (v : ℂ × ℂ × ℂ × ℂ) : ℂ × ℂ × ℂ × ℂ := (0,0,v.2.1,0)
theorem singlet_branches (z : ℂ) :
 ordered₀ (0,z,-z,0) = (0,0,-z,0) ∧ ordered₁ (0,z,-z,0) = (0,0,z,0) :=
⟨rfl,rfl⟩
theorem sorter_weight (u v w y : ℂ) :
 complex.norm_sq u + complex.norm_sq v + complex.norm_sq w + complex.norm_sq y =
 complex.norm_sq w + complex.norm_sq v + (complex.norm_sq u + complex.norm_sq y) := by ring
theorem degree_at_cut (θ : ℝ) :
 has_deriv_at (λ x : ℝ, (real.cos x-1)/2) (-real.sin θ/2) θ :=
by simpa using ((real.has_deriv_at_cos θ).sub (has_deriv_at_const θ (1:ℝ))).div_const 2
theorem sphere_charge : (real.cos real.pi-1)/2 - (real.cos 0-1)/2 = (-1:ℝ) :=
by {rw [real.cos_pi,real.cos_zero], norm_num}
theorem pointwise_constraint (f : ℝ) : 2*(-f/2)+f=0 := by ring
-- Project the spatial connection in an adapted Spin(3) frame onto the minus line.
def spin_conn (a b w x y : ℂ) : ℂ × ℂ :=
 ((w*x+(a-complex.I*b)*y)/2,((a+complex.I*b)*x-w*y)/2)
theorem projected_connection (a b w y : ℂ) :
 (spin_conn a b w 0 y).2=(-w/2)*y := by {unfold spin_conn,ring}
theorem genus_charge (g : ℤ) : (2*(g-1) : ℤ) = -(2-2*g) := by ring
theorem frozen_exchange (sing trip : ℂ) :
 (sing+trip)/2-(sing-trip)/2=trip ∧
 (sing+trip)/2+(sing-trip)/2=sing := by {split;ring}

theorem thermal_defect (u : ℝ) (hu : 0<u) : 0<2*u/(1+3*u) :=
div_pos (by linarith) (by linarith)
theorem exchange_deadline (j t h : ℝ) (ht : 0<t) (hj : 0<j) :
 h/j<t ↔ h/t<j := by {rw [div_lt_iff hj,div_lt_iff ht,mul_comm]}

-- In the two equivalent total-j representations the following matrices act on
-- multiplicity only. x,y may be individual amplitudes of any entangled input.
def primary (a b : ℂ) (v : ℂ × ℂ) : ℂ × ℂ :=
 (a*(a*v.1+b*v.2),b*(a*v.1+b*v.2))
def low (v : ℂ × ℂ) : ℂ × ℂ := (v.1,0)
theorem multiplicity_projector (a b : ℂ) (h : a^2+b^2=1) (v : ℂ × ℂ) :
 primary a b (primary a b v)=primary a b v :=
begin
 apply prod.ext; dsimp [primary],
 {linear_combination (a*(a*v.1+b*v.2))*h},
 {linear_combination (b*(a*v.1+b*v.2))*h}
end
theorem commutator (a b : ℂ) (ha : a≠0) (hb : b≠0) (v : ℂ × ℂ) :
 let A:= low (primary a b v), B:=primary a b (low v) in
 ((A.1-B.1)/(a*b),(A.2-B.2)/(a*b))=(v.2,-v.1) :=
by {dsimp [primary,low],apply prod.ext,all_goals {dsimp,field_simp [ha,hb];ring}}
theorem corrected_amplitudes (a b z : ℂ) :
 low (a*z,b*z)=(a*z,0) ∧ ((a*z,b*z).2,-(0:ℂ))=(b*z,0) := by simp [low]
theorem flat_record (a b z : ℂ) (h : complex.norm_sq a+complex.norm_sq b=1) :
 (↑(complex.norm_sq a) : ℂ)*z+(↑(complex.norm_sq b) : ℂ)*z=z :=
begin
 rw [←add_mul,←complex.of_real_add,h,complex.of_real_one,one_mul]
end
theorem relative_charge (j : ℝ) : 2*(j-1/2)-2*j = -1 := by ring
theorem individual_error (j : ℝ) (h : 0<j) :
 1/(2*(2*j+1))+j/(2*j+1)^2=(4*j+1)/(2*(2*j+1)^2) :=
by {field_simp [show 2*j+1≠0,by linarith],ring}
theorem charge_coherence_gap (a b c d : ℝ) (h : a^2+b^2=1) (h' : c^2+d^2=1)
 (distinct : a≠c) : a*c+b*d<1 :=
begin
 have p : 0 < (a-c)^2+(b-d)^2 := add_pos_of_pos_of_nonneg
   (sq_pos_of_ne_zero (a-c) (sub_ne_zero.mpr distinct)) (sq_nonneg (b-d)),
 have eqn : 2*(1-(a*c+b*d))=(a-c)^2+(b-d)^2 := by linear_combination -h-h',
 rw [←eqn] at p, linarith only [p]
end
theorem spin_sign (z : ℂ) (h : -z=z) : z=0 := by linear_combination -h/2

def up : list bool → ℕ
| [] := 0
| (tt::w) := (up w).succ
| (ff::w) := up w
def down : list bool → ℕ
| [] := 0
| (tt::w) := down w
| (ff::w) := (down w).succ
def path_num : list bool → ℕ
| [] := 1
| (tt::w) := (up w).succ*path_num w
| (ff::w) := (down w).succ*path_num w
theorem word_counts (w : list bool) : up w + down w = w.length :=
begin
 induction w with h w ih, {refl}, cases h,
 {change up w + (down w).succ = w.length.succ, rw [nat.add_succ,ih]},
 {change (up w).succ + down w = w.length.succ, rw [nat.succ_add,ih]}
end
theorem word_product (w : list bool) : path_num w = (up w).factorial*(down w).factorial :=
begin
 induction w with h w ih, {refl}, cases h; simp [up,down,path_num,ih,nat.factorial_succ,nat.succ_eq_add_one];ring
end
theorem dicke_word (w : list bool) :
 (w.length.choose (up w))*path_num w=w.length.factorial :=
begin
 rw [←word_counts w,word_product],
 have h:=nat.add_choose_mul_factorial_mul_factorial (down w) (up w),
 rw [add_comm (down w) (up w)] at h,
 simpa only [mul_assoc,mul_comm (down w).factorial (up w).factorial] using h
end

-- Resonant left/right visits before and after U=c I+d S.
def left (r : ℂ) (v : ℂ × ℂ) : ℂ × ℂ := (r*v.1,v.2)
def right (r : ℂ) (v : ℂ × ℂ) : ℂ × ℂ := (v.1,r*v.2)
def move (c d : ℂ) (v : ℂ × ℂ) : ℂ × ℂ := (c*v.1+d*v.2,c*v.2+d*v.1)
theorem dark (r c d : ℂ) (v : ℂ × ℂ) :
 let A := right r (move c d (left r v)), B := left r (move c d (right r v)) in
 ((A.1-B.1)/2,(A.2-B.2)/2) =
 ((1-r^2)/2*d*v.2,-((1-r^2)/2*d)*v.1) :=
by {dsimp [left,right,move],apply prod.ext,all_goals {dsimp,ring}}
theorem bright (r c d : ℂ) (v : ℂ × ℂ) :
 let A := right r (move c d (left r v)), B := left r (move c d (right r v)) in
 ((A.1+B.1)/2,(A.2+B.2)/2) =
 (r*c*v.1+(1+r^2)/2*d*v.2,r*c*v.2+(1+r^2)/2*d*v.1) :=
by {dsimp [left,right,move],apply prod.ext,all_goals {dsimp,ring}}
theorem dark_preserves_norm (z u v : ℂ) :
 complex.norm_sq (z*v)+complex.norm_sq (-(z*u))=
 complex.norm_sq z*(complex.norm_sq u+complex.norm_sq v) :=
by {simp only [complex.norm_sq_mul,complex.norm_sq_neg],ring}
theorem one_port (s a : ℂ) (h : s+a≠0) :
 (1-((s-a)/(s+a))^2)/2=2*a*s/(s+a)^2 := by {field_simp [h],ring}

def tail_poly (x : ℝ) := x^4-2*x^3+x^2+x+1/2
theorem tail_derivative (x : ℝ) : has_deriv_at tail_poly (4*x^3-6*x^2+2*x+1) x :=
begin
 change has_deriv_at (λ u : ℝ,u^4-2*u^3+u^2+u+1/2) _ x,
 convert (((((has_deriv_at_pow 4 x).sub ((has_deriv_at_pow 3 x).const_mul 2)).add
 (has_deriv_at_pow 2 x)).add (has_deriv_at_id x)).add (has_deriv_at_const x (1/2:ℝ))) using 1,
 norm_num, ring
end
theorem finite_pulse (x : ℝ) : has_deriv_at
 (λ u : ℝ, 1/2-real.exp (-2*u)*tail_poly u)
 (2*real.exp (-2*x)*x^2*(2-x)^2) x :=
begin
 have e := ((has_deriv_at_id x).const_mul (-2:ℝ)).exp,
 convert (has_deriv_at_const x (1/2:ℝ)).sub (e.mul (tail_derivative x)) using 1,
 dsimp [tail_poly],ring
end
theorem pulse_initial : 1/2-real.exp (-2*0)*tail_poly 0=0 := by norm_num [tail_poly]

-- Isotropic dipole contraction applied to three rotational tensors.
theorem tensor_scalar (v : ℂ) : (6*v+v+3*v)/10=v := by ring
theorem tensor_vector (v : ℂ) : (6*v-v)/10=v/2 := by ring
theorem tensor_quadrupole (v : ℂ) : (6*v+v)/10=7/10*v := by ring
theorem matched_rays (u v : ℝ) : u^2+(-v)^2=u^2+v^2 := by ring
theorem n_returns (v : ℕ → ℝ) (h₀ : v 0=1)
 (hs : ∀ n, v (n+1)=7/10*v n) : ∀ n, v n=(7/10:ℝ)^n :=
begin intro n, induction n with n ih, {simp [h₀]}, rw [hs,ih,pow_succ] end
-- The phase-sensitive decoding term in a singular-vector basis.
theorem polar_bound {ι : Type*} (s : finset ι) (w c : ι → ℝ)
 (hw : ∀ i ∈ s, 0≤w i) (hc : ∀ i ∈ s, c i≤1) :
 (∑ i in s, w i*c i) ≤ ∑ i in s, w i :=
finset.sum_le_sum (λ i hi, by simpa using mul_le_mul_of_nonneg_left (hc i hi) (hw i hi))
theorem polar_attainment {ι : Type*} (s : finset ι) (w : ι → ℝ) :
 (∑ i in s,w i*1)=∑ i in s,w i := by simp
theorem renewal (t p V : ℝ) (h : V=t+(1-t)*(1-3/10*p)*V)
 (ht : 0<t) (ht' : t≤1) (hp : 0≤p) : V=t/(t+3/10*(1-t)*p) :=
begin
 have hpos : 0≤(1-t)*p := mul_nonneg (by linarith) hp,
 apply (eq_div_iff (ne_of_gt (by nlinarith : 0<t+3/10*(1-t)*p))).2,
 nlinarith only [h]
end
theorem renewal_loss (t l : ℝ) (h : t+l≠0) : 1-t/(t+l)=l/(t+l) :=
by {field_simp [h]}

-- All positive measures of pair gaps, including lines, obey the same test.
def cubic (s x : ℝ) := (max (s-x) 0)^3
theorem truncated_midpoint (z d : ℝ) (hd : 0≤d) :
 2*(max z 0)^3 ≤ (max (z+d) 0)^3+(max (z-d) 0)^3 :=
begin
 by_cases h : z≤0,
 {rw [max_eq_right h], simp only [zero_pow (dec_trivial : 0<3),mul_zero],
  exact add_nonneg (pow_nonneg (le_max_right _ _) _) (pow_nonneg (le_max_right _ _) _)},
 have hz : 0≤z := le_of_lt (lt_of_not_ge h),
 rw [max_eq_left hz,max_eq_left (add_nonneg hz hd)],
 by_cases h₂ : d≤z,
 {rw [max_eq_left (sub_nonneg.mpr h₂)],
  nlinarith only [mul_nonneg hz (sq_nonneg d)]},
 rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge h₂))],
 have k : (2*z)^3≤(z+d)^3 := pow_le_pow_of_le_left (by linarith)
   (by linarith [le_of_not_ge h₂]) 3,
 nlinarith only [k,pow_nonneg hz 3]
end
theorem kernel_mid (s x d : ℝ) (hd : 0≤d) :
 cubic s x+cubic s x≤cubic s (x-d)+cubic s (x+d) :=
begin
 unfold cubic,
 rw [show s-(x-d)=s-x+d, by ring,show s-(x+d)=s-x-d,by ring,←two_mul],
 exact truncated_midpoint (s-x) d hd
end
theorem spectrum_mid (μ : measure ℝ) (x d : ℝ) (hd : 0≤d)
 (hm : integrable (λ s,cubic s x) μ) (hl : integrable (λ s,cubic s (x-d)) μ)
 (hr : integrable (λ s,cubic s (x+d)) μ) :
 2*(∫ s,cubic s x ∂μ) ≤ (∫ s,cubic s (x-d) ∂μ)+(∫ s,cubic s (x+d) ∂μ) :=
begin
 have h := integral_mono (hm.add hm) (hl.add hr) (λ s,kernel_mid s x d hd),
 change (∫ s,cubic s x + cubic s x ∂μ) ≤
        (∫ s,cubic s (x-d)+cubic s (x+d) ∂μ) at h,
 rwa [integral_add hm hm,integral_add hl hr,←two_mul] at h
end
theorem fractional_error (a b c u v w e : ℝ)
 (hu : u≤a*(1+e)) (hv : b*(1-e)≤v) (hw : w≤c*(1+e))
 (hm : 2*v≤u+w) (hpos : 0<a+2*b+c) : (2*b-a-c)/(a+2*b+c)≤e :=
(div_le_iff hpos).mpr (by nlinarith only [hu,hv,hw,hm])

-- If reflected photons all return at the same energy, flux counts net injection.
theorem escaped_balance (stock source escape : ℕ → ℝ)
 (step : ∀ j, stock (j+1)=stock j+source j-escape j) (n : ℕ) :
 stock n + (∑ j in range n, escape j)=stock 0+(∑ j in range n, source j) :=
begin
 induction n with n ih, {simp}, rw [step, sum_range_succ,sum_range_succ], linarith
end
theorem stationary_emission (n s t k : ℝ) (h : s-t*k*n=0) : t*k*n=s := by linarith
theorem trapped_tail (r : ℝ) (h : 0<r) (n : ℕ) : 0<r^n := pow_pos h n

-- Integral inverse on finite intervals, including the endpoint term.
open_locale interval
open set
def inverse_primitive (x : ℝ) (f g h k : ℝ → ℝ) (s : ℝ) : ℝ :=
 (s-x)^3*k s-3*(s-x)^2*h s+6*(s-x)*g s-6*f s
theorem inverse_derivative (x s : ℝ) (f g h k l : ℝ → ℝ)
 (hf : has_deriv_at f (g s) s) (hg : has_deriv_at g (h s) s)
 (hh : has_deriv_at h (k s) s) (hk : has_deriv_at k (l s) s) :
 has_deriv_at (inverse_primitive x f g h k) ((s-x)^3*l s) s :=
begin
 have d : has_deriv_at (λ u:ℝ,u-x) 1 s := by simpa using
 (has_deriv_at_id s).sub (has_deriv_at_const s x),
 have p := (((((d.pow 3).mul hk).sub (((d.pow 2).const_mul 3).mul hh)).add
 ((d.const_mul 6).mul hg)).sub (hf.const_mul 6)),
 convert p using 1, norm_num, ring
end
theorem inverse_integral (x y : ℝ) (f g h k l : ℝ → ℝ)
 (hf : ∀ s ∈ uIcc x y, has_deriv_at f (g s) s)
 (hg : ∀ s ∈ uIcc x y, has_deriv_at g (h s) s)
 (hh : ∀ s ∈ uIcc x y, has_deriv_at h (k s) s)
 (hk : ∀ s ∈ uIcc x y, has_deriv_at k (l s) s)
 (hi : interval_integrable (λ s,(s-x)^3*l s) volume x y) :
 (∫ s in x..y,(s-x)^3*l s)=inverse_primitive x f g h k y+6*f x :=
begin
 have p := interval_integral.integral_eq_sub_of_has_deriv_at
 (λ s (hs:s∈uIcc x y),inverse_derivative x s f g h k l (hf s hs) (hg s hs) (hh s hs) (hk s hs)) hi,
 rw [p], unfold inverse_primitive,ring
end

theorem gap_lambda (q z : ℝ) :
 ((1-q)^2-(1-q)^2*z)*((1+q)^2-(1-q)^2*z)=
 (1-q)^2*(1-z)*((1+q)^2-(1-q)^2*z) := by ring
theorem pair_beta : (1:ℝ)/4-3/5+3/6-1/7=1/140 := by norm_num
theorem fourth_derivative_soft : (4:ℝ)*5*6*7/6=140 := by norm_num
theorem cutoff_number : (140:ℝ)/4*(1/8-3/9+3/10-1/11)=7/264 := by norm_num
theorem cutoff_energy : (140:ℝ)/5*(1/9-3/10+3/11-1/12)=7/495 := by norm_num
end radiation_returns
