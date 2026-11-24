import data.mv_polynomial.pderiv
import data.mv_polynomial.comm_ring
import analysis.special_functions.log.basic
import data.complex.basic
import linear_algebra.finite_dimensional
import tactic

noncomputable theory
open_locale big_operators
open mv_polynomial
namespace cat_projective_radius

-- Fixed-number bosons in the polynomial representation. 0,1 are ket
-- coordinates and 2,3 are independent bra coordinates. Spectator coordinates
-- do not occur in the mode. No cutoff n is fixed in these identities.
abbreviation P := mv_polynomial ℕ ℂ
abbreviation Der := derivation ℂ P P
def ii : P := C complex.I
def z : P := X 0+ii*X 1
def w : P := X 2+ii*X 3
def dx (i : ℕ) : Der := pderiv i
def dxn : Der := dx 0+ii • dx 1
def dyn : Der := dx 2+ii • dx 3
def number : Der :=
  (X 0:P) • dx 0+(X 1:P) • dx 1+(X 2:P) • dx 2+(X 3:P) • dx 3
def rotation : Der :=
  ii • ((X 0:P) • dx 1-(X 1:P) • dx 0+(X 2:P) • dx 3-(X 3:P) • dx 2)
def mode (n : ℕ) : P := z^n*w^n

lemma ii_sq : ii*ii=-1 :=
by { unfold ii, rw [← map_mul,complex.I_mul_I], simp }

meta def coord := `[simp [dxn,dyn,number,rotation,dx,z,w,ii,pderiv_mul,
  derivation.add_apply,derivation.sub_apply,derivation.smul_apply,smul_eq_mul,
  pi.single_apply, ←map_mul,complex.I_mul_I]; try { ring }]

lemma dxn_z : dxn z=0 := by coord
lemma dxn_w : dxn w=0 := by coord
lemma dyn_z : dyn z=0 := by coord
lemma dyn_w : dyn w=0 := by coord
lemma number_z : number z=z := by coord
lemma number_w : number w=w := by coord
lemma dz0 : dx 0 z=1 := by coord
lemma dz1 : dx 1 z=ii := by coord
lemma dz2 : dx 2 z=0 := by coord
lemma dz3 : dx 3 z=0 := by coord
lemma dw0 : dx 0 w=0 := by coord
lemma dw1 : dx 1 w=0 := by coord
lemma dw2 : dx 2 w=1 := by coord
lemma dw3 : dx 3 w=ii := by coord
lemma rotation_apply (h : P) : rotation h =
  ii*((X 0:P)*dx 1 h-X 1*dx 0 h+X 2*dx 3 h-X 3*dx 2 h) :=
by simp only [rotation,derivation.smul_apply,derivation.add_apply,derivation.sub_apply,smul_eq_mul]
lemma square_rotation (a b : P) : ii*(a*ii-b)= -(a+ii*b) :=
by { rw [mul_sub,mul_left_comm ii a ii,ii_sq,mul_neg_one],ring }
lemma rotation_z : rotation z= -z :=
by simpa only [rotation_apply,dz0,dz1,dz2,dz3,mul_one,mul_zero,add_zero,sub_zero]
   using (show ii*((X 0:P)*ii-X 1)= -z, from square_rotation _ _)
lemma rotation_w : rotation w= -w :=
by simpa only [rotation_apply,dw0,dw1,dw2,dw3,mul_one,mul_zero,sub_zero,zero_add]
   using (show ii*((X 2:P)*ii-X 3)= -w, from square_rotation _ _)

lemma product_deriv (d : Der) (p q : P) : d (p*q) = d p*q+p*d q :=
by { rw [d.leibniz], simp only [smul_eq_mul], ring }

lemma homogeneous_power (d : Der) (v k : P) (h : d v=k*v) (n : ℕ) :
 d (v^n)=(n:P)*k*v^n :=
begin
  induction n with n ih,
  { simp },
  rw [pow_succ,product_deriv,ih,h,nat.cast_succ], ring
end

lemma on_kernel (d : Der) (a b : P) (ha : d z=a*z) (hb : d w=b*w) (n : ℕ) :
 d (mode n)=(n:P)*(a+b)*mode n :=
by { unfold mode, rw [product_deriv,homogeneous_power d z a ha,
  homogeneous_power d w b hb], ring }

theorem transverse_ket (n : ℕ) : dxn (mode n)=0 :=
by simpa using on_kernel dxn 0 0 (by simp [dxn_z]) (by simp [dxn_w]) n
theorem transverse_bra (n : ℕ) : dyn (mode n)=0 :=
by simpa using on_kernel dyn 0 0 (by simp [dyn_z]) (by simp [dyn_w]) n
theorem oscillator_number (n : ℕ) : number (mode n)=2*(n:P)*mode n :=
by { rw [on_kernel number 1 1 (by simp [number_z]) (by simp [number_w])], ring }
theorem contracted_flux (n : ℕ) : rotation (mode n)= -(2*(n:P)*mode n) :=
by { rw [on_kernel rotation (-1) (-1) (by simp [rotation_z]) (by simp [rotation_w])], ring }
theorem transverse_vector_pole (n : ℕ) :
  number (mode n)+2*rotation (mode n)= -(2*(n:P))*mode n :=
by { rw [oscillator_number,contracted_flux], ring }

theorem transfer_from_null_derivatives (a b c d u : P)
  (h₀ : a+ii*b=0) (h₁ : c+ii*d=0)
  (link : u=a*c+b*d) : u=0 :=
begin
  have h₂ : a= -(ii*b) := eq_neg_of_add_eq_zero_left h₀,
  have h₃ : c= -(ii*d) := eq_neg_of_add_eq_zero_left h₁,
  rw [link,h₂,h₃], linear_combination b*d*ii_sq
end

theorem lower_block_zero (n : ℕ) :
 dx 0 (z^n)*dx 2 (w^n)+dx 1 (z^n)*dx 3 (w^n)=0 :=
begin
  have hx : dxn (z^n)=0 := by
    simpa using homogeneous_power dxn z 0 (by simp [dxn_z]) n,
  have hy : dyn (w^n)=0 := by
    simpa using homogeneous_power dyn w 0 (by simp [dyn_w]) n,
  exact transfer_from_null_derivatives _ _ _ _ _ hx hy rfl
end

def test_point (i : ℕ) : ℂ := if i=0 ∨ i=2 then 1 else 0
theorem mode_is_nonzero (n : ℕ) : mode n≠0 :=
begin
  have h : eval test_point (mode n)=1 := by norm_num [mode,z,w,ii,test_point],
  intro hn, simpa [hn] using h
end

theorem physical_negative (n t : ℝ) (hn : 0<n) (ht : 0<t) : -(2*n)*t^2<0 :=
by nlinarith [mul_pos hn (sq_pos_of_pos ht)]
theorem uniform_gap (n t gap : ℝ) : 0≤ -(2*n)*t^2+gap ↔ 2*n*t^2≤gap :=
by { split; intro h; nlinarith }
theorem common_real_plane_dimension {V : Type*} [add_comm_group V] [module ℂ V]
  [finite_dimensional ℂ V] (E F : submodule ℂ V)
  (axes : finite_dimensional.finrank ℂ V≤6)
  (hE : finite_dimensional.finrank ℂ E=4) (hF : finite_dimensional.finrank ℂ F=4) :
  2≤finite_dimensional.finrank ℂ ↥(E⊓F) :=
begin
  have hd := E.finrank_sup_add_finrank_inf_eq F,
  have hu := (E⊔F).finrank_le,
  rw [hE,hF] at hd,
  by_contra hn,
  have small : finite_dimensional.finrank ℂ ↥(E⊓F)≤1 := nat.le_of_lt_succ (lt_of_not_ge hn),
  have too_small := add_le_add (le_trans hu axes) small,
  rw [hd] at too_small, norm_num at too_small
end
theorem vector_scale_polarization (p q : ℝ) (h : p=2*q) : q+p=3*q := by linarith

theorem pole_determinant (n h l : ℝ) :
  (n+h/2)*(n+h/2+3)-(n-l)*(n+h+l+3)=(2*l+h)*(2*l+h+6)/4 := by ring
theorem even_pole (x y l : ℝ) (root : l*(x+y-l)=x*y) :
  (x-l)*(y-l)=0 := by nlinarith
theorem pole_relative_error (s r : ℝ) (hs : s+r≠0) :
  2*s/(s+r)-1=(s-r)/(s+r) := by { field_simp [hs], ring }
theorem odd_gap (n h j v : ℝ) (hn : 0≤n) (hh : 0≤h) (hj : 0≤j) (le : j≤n)
  (hv : 0≤v) (sqv : v^2=(n-j)*(n+h-j)) :
  3/2≤(2*n+h+3)/2-v :=
begin
  have aux : 0≤n+h/2-j := by linarith,
  have ub : v≤n+h/2-j,
  { by_contra cc, push_neg at cc, nlinarith [mul_pos (sub_pos.mpr cc)
      (show 0<v+(n+h/2-j), by linarith),sq_nonneg h] },
  linarith
end

def ent (x : ℝ) := x*real.log x
lemma ent_tangent (x y : ℝ) (hx : 0≤x) (hy : 0<y) :
  0≤ent x-ent y-(real.log y+1)*(x-y) :=
begin
  rcases eq_or_lt_of_le hx with h|h,
  { rw [←h], unfold ent, nlinarith },
  have t := real.log_le_sub_one_of_pos (div_pos hy h),
  rw [real.log_div (ne_of_gt hy) (ne_of_gt h)] at t,
  have tt := mul_le_mul_of_nonneg_left t h.le,
  have clear : x*(y/x-1)=y-x := by { field_simp [ne_of_gt h],ring },
  rw [clear] at tt, unfold ent, nlinarith
end

theorem spin_spectral_positivity {ι : Type*} (s : finset ι) (w x : ι → ℝ) (y : ℝ)
  (hy : 0<y) (hw : ∀ i∈s, 0≤w i) (hx : ∀ i∈s, 0≤x i)
  (mean : ∑ i in s, w i*(x i-y)=0) :
  0≤∑ i in s,w i*(ent (x i)-ent y) :=
begin
  have aux := finset.sum_nonneg (λ i hi, mul_nonneg (hw i hi) (ent_tangent (x i) y (hx i hi) hy)),
  have eq : (∑ i in s,w i*(ent (x i)-ent y-(real.log y+1)*(x i-y))) =
    (∑ i in s,w i*(ent (x i)-ent y))-(real.log y+1)*∑ i in s,w i*(x i-y),
  { rw [finset.mul_sum, ←finset.sum_sub_distrib],
    apply finset.sum_congr rfl, intros, ring },
  simpa [eq,mean] using aux
end
theorem ent_scaling (x t : ℝ) (hx : 0≤x) (ht : 0<t) :
 ent (t*x)=t*ent x+t*real.log t*x :=
begin
  rcases eq_or_lt_of_le hx with h|h,
  { rw [←h], simp [ent] },
  rw [ent,real.log_mul (ne_of_gt ht) (ne_of_gt h)], unfold ent, ring
end
theorem spectral_scale_cancellation (s u v t k : ℝ) (equal_trace : u=v) :
  t*s+t*k*(u-v)=t*s := by rw [equal_trace,sub_self,mul_zero,add_zero]
theorem integrated_tail (q m : ℝ) (hq : q≠0) (h : q+m≠0) :
 (q/(q+m))^2-1+2*m/q=m^2*(3*q+2*m)/(q*(q+m)^2) :=
by { field_simp [hq,h],ring }
theorem stationary_scale (a b r : ℝ) (hb : b≠0) (eq : 2*b*r^2=a) :
  12*b*r^2-2*a=4*a := by linarith
theorem matter_neutrality (t m f : ℝ) (ht : t≠0) (hf : f≠0) :
 (t*m)^2/(t^2*f)=m^2/f := by { field_simp [ht,hf],ring }
theorem thresholds (b0 b1 b2 b3 : ℝ) :
 (b0-b1)+(b1-b2)+(b2-b3)=b0-b3 := by ring
theorem probe_force (f : ℝ) :
 2*(((-9*f/2+3*(1-f)/2)^2/(63/2))+((-6*f/7+2*(1-f)/7)^2/(6/7)))=
 (4*f-1)^2/3 := by ring
theorem flux_hessian : (18:ℝ)*21^2-42*9^2=4536 ∧
  -(48:ℝ)*(2/7)^2+6*(16/7)^2=192/7 := by norm_num
theorem ads_masses : (4536:ℝ)/(8*(63/2))=18 ∧ (192/7:ℝ)/(8*(6/7))=4 := by norm_num

theorem closed_metric_radius (f v t : ℝ) (hf : f≠0) (ht : t≠0) :
  v*t^4/(f*t^2)^2=v/f^2 := by { field_simp [hf,ht],ring }
theorem eliminate_external_curvature (f fp v vp R : ℝ)
  (einstein : f*R=4*v) (scalar : fp*R=2*vp) : f*vp-2*v*fp=0 :=
by linear_combination (fp*einstein-f*scalar)/2
theorem homogeneous_stationarity (f v t : ℝ) :
  (f*t^2)*(4*v*t^3)-2*(v*t^4)*(2*f*t)=0 := by ring

theorem torus_shape_energy (p q A B : ℝ) (hA : A≠0) (hB : B≠0) :
 p^2*B/A+q^2*A/B-2*p*q=(p*B-q*A)^2/(A*B) := by { field_simp [hA,hB],ring }
theorem selfdual_energy_excess (plus minus : ℝ) :
 (plus^2+minus^2)/2-(plus^2-minus^2)/2=minus^2 := by ring
theorem equal_flux_minimum (b s n m : ℝ)
  (hb : 0≤b) (hn : 0≤n) (hm : 0≤m) :
  s^2 ≤ s^2+(2*n+1)*b+(2*m+1)*b-2*b :=
by nlinarith [mul_nonneg hb hn,mul_nonneg hb hm]
theorem static_supertrace (x y : ℝ) :
  4+2*(2*x^2-1)+2*(2*y^2-1)-8*x*y=4*(x-y)^2 := by ring
theorem balanced_heat_kernel (c s e : ℝ) (id : c^2-s^2=1) (hs : s≠0) :
 (c^2-1)*e/(4*s^2)=e/4 :=
by { field_simp [hs],linear_combination 4*e*id }
theorem finite_band_second_difference (e : ℝ) : 1-2*e+e^2=(1-e)^2 := by ring
theorem separation_response (x a : ℝ) (hx : 0<x) (ha : 0<a) :
 (1/x-2/(x+a)+1/(x+2*a))/2=a^2/(x*(x+a)*(x+2*a)) :=
by { field_simp [ne_of_gt hx,show x+a≠0,by positivity,show x+2*a≠0,by positivity],ring }
theorem band_at_coincidence (a : ℝ) (ha : 0<a) :
 (ent 0-2*ent a+ent (2*a))/2=a*real.log 2 :=
by { simp [ent,real.log_mul (show (2:ℝ)≠0,by norm_num) (ne_of_gt ha)],ring }
theorem cutoff_force (eta k : ℝ) (hk : k≠0) :
  2*((1-eta)/k)^2=2*(1-eta)^2/k^2 := by { rw [div_pow,mul_div_assoc] }
theorem charged_product_gap (l r d : ℝ) (hd : 1/2≤d) (hl : d≤l) (hr : d≤r) :
  2*d^2≤l*(l-1)+r*(r+1) :=
begin
  nlinarith [mul_nonneg (sub_nonneg.mpr hl) (show 0≤l+d-1,by linarith),
    mul_nonneg (sub_nonneg.mpr hr) (show 0≤r+d+1,by linarith)]
end
theorem shape_exclusion (b c p q : ℝ) (hb : 0<b) (hc : 0≤c)
  (hp : p<0) (hq : q<0) : b*p+c*q<0 :=
add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg hb hp) (mul_nonpos_of_nonneg_of_nonpos hc hq.le)
end cat_projective_radius
