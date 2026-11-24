import analysis.inner_product_space.basic
import analysis.special_functions.exp_deriv
import analysis.calculus.deriv.inv
import data.complex.basic
import tactic

noncomputable theory
open_locale big_operators
namespace falling_multipoles

-- Cauchy--Schwarz for the donor tag and the sum of both receiving tags.
theorem common_tag {E : Type*} [normed_add_comm_group E] [inner_product_space ℝ E]
 (d a b : E) (c z : ℝ) (hd : ⟪d,d⟫_ℝ=1) (ha : ⟪a,a⟫_ℝ=1)
 (hb : ⟪b,b⟫_ℝ=1) (h1 : ⟪d,a⟫_ℝ=c) (h2 : ⟪d,b⟫_ℝ=c)
 (h3 : ⟪a,b⟫_ℝ=z) : 2*c^2≤1+z :=
begin
 have h4 : ⟪a,d⟫_ℝ=c := by rw [real_inner_comm,h1],
 have h5 : ⟪b,d⟫_ℝ=c := by rw [real_inner_comm,h2],
 have h6 : ⟪b,a⟫_ℝ=z := by rw [real_inner_comm,h3],
 have h : 0≤⟪a+b-(2*c) • d,a+b-(2*c) • d⟫_ℝ := real_inner_self_nonneg,
 simp only [inner_sub_left,inner_sub_right,inner_add_left,inner_add_right,
   real_inner_smul_left,real_inner_smul_right,hd,ha,hb,h1,h2,h3,h4,h5,h6] at h,
 nlinarith,
end

theorem gram_det (z c : ℝ) :
 (1-z*z)-c*(c-z*c)+c*(c*z-c)=(1-z)*(1+z-2*c^2) := by ring

theorem envelope_square (u z : ℝ) :
 (1+u)^2-4*u*(1+z)*(1-u*z)=(2*u*z-(1-u))^2 := by ring

theorem endpoint_max (u z : ℝ) (hu : 0≤u) (hl : 0≤z) (hr : z≤1) (hc : 3*u≤1) :
 (1+z)*(1-u*z)/2≤1-u :=
begin
 have h : 0≤1-2*u-u*z := by nlinarith [mul_nonneg hu (sub_nonneg.mpr hr)],
 nlinarith [mul_nonneg (sub_nonneg.mpr hr) h],
end

theorem pair_gain (c z : ℝ) (hs : 2*c^2≤1+z) (hz : z≤1) :
 2*(c^2*(1-z))≤1-z*z := by nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hz)]

theorem common_dark {E : Type*} [add_comm_group E] (p q : E) (h : p=q) : p-q=0 := sub_eq_zero.mpr h
theorem orthogonal_positive_sum {ι : Type*} (s : finset ι) (w : ι → ℝ) (h : ∀ i∈s,0≤w i)
 (hz : ∑ i in s, w i=0) (j : ι) (hj : j∈s) : w j=0 :=
begin
 have hh : w j≤∑ i in s,w i := finset.single_le_sum h hj,
 linarith [h j hj],
end

theorem projection_contrast (raw cut p : ℝ) : (1-p)*raw+p*cut=raw+p*(cut-raw) := by ring
theorem comparable_recoil (v t : ℝ) (hv : 0≤v) (h : v≤1) (ht : t≤1) :
 1-v^3*t≤3*(1-v*t) :=
begin
 have h2 : 0≤2-v-v^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr h) (show 0≤1+v,by linarith)],
 have h3 : 0≤3*v-v^3 := by nlinarith [mul_nonneg hv h2],
 nlinarith [mul_nonneg (sub_nonneg.mpr ht) h3,
   mul_nonneg (sq_nonneg (1-v)) (show 0≤2+v,by linarith)],
end

theorem polar_filter (x a b : ℝ) (ha : a=((1+x)/2)^2) (hb : b=((1-x)/2)^2) :
 a-b=x ∧ a+b=(1+x*x)/2 ∧ (a+b)^2-(a-b)^2=4*a*b :=
by subst a;subst b;split;[ring,split];ring

def w0 (x : ℝ) := 15/16*(1-x^2)^2
def w1 (x : ℝ) := 5/8*(1-x^4)
def w2 (x : ℝ) := 5/32*(1+6*x^2+x^4)
def f0 (x : ℝ) := 15/16*(x-2*x^3/3+x^5/5)
def f1 (x : ℝ) := 5/8*(x-x^5/5)
def f2 (x : ℝ) := 5/32*(x+2*x^3+x^5/5)

theorem density_zero (x : ℝ) : has_deriv_at f0 (w0 x) x :=
begin
 unfold f0 w0,
 convert (((has_deriv_at_id x).sub (((has_deriv_at_pow 3 x).const_mul 2).div_const 3)).add
   ((has_deriv_at_pow 5 x).div_const 5)).const_mul (15/16) using 1; simp;try {left};ring,
end

theorem density_one (x : ℝ) : has_deriv_at f1 (w1 x) x :=
begin
 unfold f1 w1,
 convert ((has_deriv_at_id x).sub ((has_deriv_at_pow 5 x).div_const 5)).const_mul (5/8) using 1;simp;try {left};ring,
end

theorem density_two (x : ℝ) : has_deriv_at f2 (w2 x) x :=
begin
 unfold f2 w2,
 convert (((has_deriv_at_id x).add ((has_deriv_at_pow 3 x).const_mul 2)).add
   ((has_deriv_at_pow 5 x).div_const 5)).const_mul (5/32) using 1;simp;try {left};ring,
end

theorem normalized : f0 1-f0 (-1)=1 ∧ f1 1-f1 (-1)=1 ∧ f2 1-f2 (-1)=1 := by norm_num [f0,f1,f2]
theorem cap_order (u : ℝ) (hl : 0≤u) (hr : u≤1) :
 (f0 1-f0 u ≤ f1 1-f1 u) ∧ (f1 1-f1 u ≤ f2 1-f2 u) :=
begin
 have h : 0≤1-u^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hr) (show 0≤1+u,by linarith)],
 unfold f0 f1 f2,
 split,
 { nlinarith [mul_nonneg hl (sq_nonneg (1-u^2))] },
 { nlinarith [mul_nonneg (mul_nonneg hl h) (show 0≤3+u^2,by nlinarith [sq_nonneg u])] },
end

theorem aperture (d : ℝ) : f0 1-f0 (1-d)=15/16*d^3*(4/3-d+d^2/5) ∧
 5/12*(1-(1-d)^3)=5/4*d*(1-d+d^2/3) :=
by unfold f0;split;ring

theorem aberration (v m : ℝ) (h : 1+v*m≠0) :
 1-(m+v)/(1+v*m)=(1-v)*(1-m)/(1+v*m) := by field_simp;ring
theorem critical_ray (r : ℝ) (h : r≠0) :
 1-27*(r-1)/(4*r^3)=(3/2-r)^2*(r+3)/r^3 := by field_simp;ring
theorem narrow_cap_coeff : ((1:ℝ)/2)*(27/8)/2=27/32 := by norm_num
theorem raw_moment : 5/32*((2:ℝ)/3+12/5+2/7)=11/21 := by norm_num
theorem energy_shell (M m : ℝ) (h : M≠0) :
 (M-(M^2-m^2)/(2*M))^2-((M^2-m^2)/(2*M))^2=m^2 := by field_simp;ring
theorem frequency_gate (v u y : ℝ) (hv : 0≤v) (hu : u≤1) (hy : 1-v*u≤y) :
 1-v≤y := by nlinarith [mul_nonneg hv (sub_nonneg.mpr hu)]

theorem axial_fifth (z : ℝ) (h : z≠0) :
 has_deriv_at (λ r : ℝ,r⁻¹^5*6) (-30/z^6) z :=
begin
 have g := ((has_deriv_at_inv h).pow 5).mul_const (6:ℝ),
 convert g using 1; simp [id];field_simp;ring,
end
theorem octupole_exchange (G o q a : ℝ) (h : a≠0) :
 (G*o*q)*(30/a^6)/(6*2)=(5/2)*G*o*q/a^6 := by ring
theorem tide_shifts : (-(504:ℝ)*(-2/7)*(1+1/8)=162) ∧
 ((3:ℝ)/64*(2/5-2/7)=3/560) ∧ ((12:ℝ)-3*2^2=0) := by norm_num
theorem flyby_primitive (s : ℝ) :
 has_deriv_at (λ x : ℝ,2*(x+4*x^3/3+6*x^5/5+4*x^7/7+x^9/9)) (2*(1+s^2)^4) s :=
begin
 convert (((((has_deriv_at_id s).add (((has_deriv_at_pow 3 s).const_mul 4).div_const 3)).add
    (((has_deriv_at_pow 5 s).const_mul 6).div_const 5)).add
    (((has_deriv_at_pow 7 s).const_mul 4).div_const 7)).add
    ((has_deriv_at_pow 9 s).div_const 9)).const_mul 2 using 1;simp;ring,
end
theorem flyby_value : 2*((1:ℝ)+4/3+6/5+4/7+1/9)=2656/315 := by norm_num
theorem angular_population (a b da db q r w : ℝ)
 (h1 : da= -q*a/2-w*b) (h2 : db=w*a-r*b/2) :
 2*a*da+2*b*db= -q*a^2-r*b^2 := by rw [h1,h2];ring

theorem full_population (x y u v dx dy du dv a b w e : ℝ)
 (h1 : dx= -a*x/2+w*v) (h2 : dy= -a*y/2-w*u)
 (h3 : du= -b*u/2+e*v+w*y) (h4 : dv= -b*v/2-e*u-w*x) :
 2*(x*dx+y*dy+u*du+v*dv)= -a*(x^2+y^2)-b*(u^2+v^2) := by rw [h1,h2,h3,h4];ring

theorem pulsar_loss (a b z : ℝ) (hn : a+b=1) :
 1-(a^2+b^2+2*z*a*b)=2*a*b*(1-z) :=
begin have h : (a+b)^2=1 := by rw [hn];norm_num, nlinarith, end

theorem port_balance (k : ℝ) (h : k+2≠0) :
 ((2-k)/(k+2))^2+8*k/(k+2)^2=1 := by field_simp;ring
theorem one_return (b d z : ℝ) :
 ((1+z)*b+(1-z)*d)/2+((1-z)*b+(1+z)*d)/2=b+d := by ring
theorem returns (s : ℕ → ℝ) (z : ℝ) (h0 : s 0=1) (h : ∀ n,s (n+1)=s n*((1+z)/2)) :
 ∀ n,s n=((1+z)/2)^n :=
begin intro n,induction n with n ih, {simpa using h0}, {rw [h,ih,pow_succ];ring}, end
theorem port_limit (k : ℝ) (h : k+2≠0) :
 1/2-4*k/(k+2)^2=(k-2)^2/(2*(k+2)^2) := by field_simp;ring
theorem lens_same_valence : ((4:ℕ)*2=8) ∧ ((2:ℕ)*2+2*2=8) := by norm_num
theorem frequencies (n k : ℝ) (h : k≠0) : (2*n)/(2*k)=n/k := by field_simp;ring
theorem odd_strength (a b : ℝ) : (a*b-b*a)^2=0 := by ring
theorem refinement (a b : ℝ) : (a+b)^2-(a^2+b^2)=2*a*b := by ring

theorem thermal_choi (t w : ℝ) (ht : 0≤t) :
 (1-(1+2*w)/(1+2*t))/4=(t-w)/(2*(1+2*t)) :=
begin have hh : 1+2*t≠0 := by linarith,field_simp;ring,end
theorem coherent_count (c x y n : ℝ) (hn : n+1≠0) (hxy : x+y=n+1) :
 x*(1-c^2)/(n+1)+(1+(c-1)*x/(n+1))^2+(c-1)^2*x*y/(n+1)^2=1 :=
begin have hy : y=n+1-x := by linarith, rw [hy],field_simp;ring,end
theorem thermal_weights (t : ℝ) (h : 1-t≠0) :
 1/(1-t)^3+3*t/(1-t)^4=(1+2*t)/(1-t)^4 :=
by field_simp;ring

end falling_multipoles
