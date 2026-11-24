import analysis.inner_product_space.basic
import tactic

open_locale big_operators
namespace cat_flux_completion

-- The bulk charges are in the Douglas--Taylor convention, including the images.
theorem tadpole_polynomial (x y z : ℝ) :
 (2+3*y*z+6*x*z-x*y)+(y*z+x*y)+2*(1+x*y)+
 (4+4*y*z+2*x*z+6*x*y)=8*(1+y*z+x*z+x*y) := by ring

theorem odd_flux_kernel (a b c d : ℤ)
 (ha : 3*a-2*b-c+6*d=0) (hb : -a-c=0) (hc : b-c=0) :
 a = -c ∧ b=c ∧ d=c := ⟨by linarith,by linarith,by linarith⟩

theorem calibrated_shape (x y z : ℝ) (hx : 0<x) (hy : 0<y)
 (a : -2*x-y+6*z-3*x*y*z=0) (b : -y+x*y*z=0) (c : x-y=0) :
 x=1 ∧ y=1 ∧ z=1 :=
begin
 have eqy : y=x := by linarith,
 have prod : y*(x*z-1)=0 := by nlinarith,
 have xz : x*z=1 := by linarith [eq_zero_of_ne_zero_of_mul_left_eq_zero (ne_of_gt hy) prod],
 have yprod : x*y*z=y := by nlinarith [congr_arg (λ w : ℝ, w*y) xz],
 have eqz : z=x := by linarith,
 have xsq : x*x=1 := by simpa [eqz] using xz,
 have root : (x-1)*(x+1)=0 := by nlinarith,
 cases mul_eq_zero.mp root with h h,
 { exact ⟨by linarith,by linarith,by linarith⟩ },
 { exfalso, linarith }
end

theorem positive_shape (x y z : ℝ) (v : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) :
 0<(-5*x-4*y+3*z)^2/10+(x+z)^2/2+(x-y)^2 :=
begin
 by_contra h, push_neg at h,
 have h1 : (-5*x-4*y+3*z)^2=0 := by nlinarith [sq_nonneg (-5*x-4*y+3*z),
    sq_nonneg (x+z),sq_nonneg (x-y)],
 have h2 : (x+z)^2=0 := by nlinarith [sq_nonneg (x+z),sq_nonneg (x-y)],
 have h3 : (x-y)^2=0 := by nlinarith [sq_nonneg (x-y)],
 have a := pow_eq_zero h1,
 have b := pow_eq_zero h2,
 have c := pow_eq_zero h3,
 rcases v with v|v|v; apply v; linarith
end

theorem recombination (t z : ℝ) :
 (-2*t-t+6*z-3*t*t*z)+(-t+t*t*z)=2*((3-t^2)*z-2*t) := by ring

-- Values of the different positive flux energies at a proposed critical point.
theorem filled_dilaton (h f l : ℝ) (hh : 0≤h) (hf : 0≤f) (hl : 0≤l)
 (nz : 0<h ∨ 0<f ∨ 0<l) : 0<2*h+4*f+3*l :=
by rcases nz with p|p|p; linarith

theorem scaling (h a b c d l r : ℝ) :
 -9*(h+a)-11*b-13*c-15*d-9*l-7*r =
 -9*(h+a+b+c+d+l+r)-(2*b+4*c+6*d)+2*r := by ring

theorem directional_second (h a b c d l r : ℝ)
 (crit : -9*(h+a)-11*b-13*c-15*d-9*l-7*r=0) :
 81*(h+a)+121*b+169*c+225*d+81*l+49*r = 22*b+52*c+90*d-14*r := by linarith

theorem small_vacuum_bound (v b c d : ℝ) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d)
 (crit : 9*v= -(2*b+4*c+6*d)) :
 v≤0 ∧ 99*(-v)≤22*b+52*c+90*d ∧ 22*b+52*c+90*d≤135*(-v) :=
⟨by linarith,by linarith,by linarith⟩

theorem curvature_bound (v b c d r : ℝ) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d)
 (crit : 9*v=2*r-(2*b+4*c+6*d)) :
 8*r-99*v≤22*b+52*c+90*d-14*r ∧ 22*b+52*c+90*d-14*r≤16*r-135*v :=
⟨by linarith,by linarith⟩

theorem minkowski (h a b c d l : ℝ) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d)
 (vac : h+a+b+c+d+l=0) (dir : 2*b+4*c+6*d=0)
 (dil : 2*h+4*(a+b+c+d)+3*l=0) :
 b=0 ∧ c=0 ∧ d=0 ∧ h=a ∧ l= -2*h :=
⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

-- Cutoff inequality in a mass eigenbasis, using nonnegative mass squared.
theorem spectral_cut {ι : Type*} (s : finset ι) (m w : ι → ℝ) (k : ℝ)
 (hm : ∀i,0≤m i) (hw : ∀i,0≤w i) :
 k*(∑ i in s.filter (λ i,k<m i),w i) ≤ ∑ i in s,m i*w i :=
begin
 classical,
 rw [finset.mul_sum],
 calc ∑ i in s.filter (λ i,k<m i), k*w i ≤ ∑ i in s.filter (λ i,k<m i), m i*w i :
      finset.sum_le_sum (λ i hi, mul_le_mul_of_nonneg_right
        (le_of_lt (finset.mem_filter.mp hi).2) (hw i))
  ... ≤ ∑ i in s,m i*w i : finset.sum_le_sum_of_subset_of_nonneg (finset.filter_subset _ _)
        (λ i hi hn, mul_nonneg (hm i) (hw i))
end

theorem observable_projection {E : Type*} [normed_add_comm_group E] [inner_product_space ℝ E] (g t u v : E)
 (split : t=u+v) (low : ℝ) (l : abs (inner g u) ≤ low) :
 abs (inner g t)-‖g‖*‖v‖≤low :=
begin
 rw [split, inner_add_right],
 have a : abs ((inner g u : ℝ)+inner g v) ≤ abs (inner g u : ℝ)+abs (inner g v : ℝ) :=
   abs_add _ _,
 exact sub_le_iff_le_add.mpr (le_trans a (add_le_add l (abs_real_inner_le_norm g v)))
end

theorem tangent_metric_and_charge :
 (3/2:ℝ)+2*3^2=39/2 ∧ (3:ℝ)^2/(39/2)=6/13 ∧ (135:ℝ)/(39/2)=90/13 := by norm_num

theorem required_mass (slope allowed norm mass cutoff : ℝ)
 (hc : 0<cutoff) (hn : 0<norm) (proj : slope ≤ allowed+norm*(mass/cutoff)) :
 cutoff*(slope-allowed)/norm ≤ mass :=
begin
 apply (div_le_iff hn).2,
 have h := mul_le_mul_of_nonneg_right proj (le_of_lt hc),
 field_simp [ne_of_gt hc] at h,
 nlinarith
end

-- Two pairs of sources with the same cross-term at the reference point.
theorem two_squares (a b c d e : ℝ) (p : a*b=e) (q : c*d=e) :
 (a-b)^2+(c-d)^2=a^2+b^2+c^2+d^2-4*e := by nlinarith

theorem only_common_zero (u d : ℝ) (a : d= -3*u) (b : d= -u) :
 u=0 ∧ d=0 := ⟨by nlinarith only [a,b],by nlinarith only [a,b]⟩

theorem curved_mass (u d : ℝ) : 20*u^2+16*u*d+4*d^2 =
 2*(d+3*u)^2+2*(d+u)^2 := by ring

theorem curved_characteristic (m : ℝ) :
 (20-3*m/2)*(4-2*m)-8^2=3*m^2-46*m+16 := by ring

-- x and y coordinates of the cross bracket of two cycle tangents.
theorem subgroup_condition (a b c d e f : ℝ) :
 a*(c*f+d*e)-b*(-c*e+d*f)=b*c*e+a*d*e+a*c*f-b*d*f := by ring

-- Basis order z1,z2,z3,bar(z1),bar(z2),bar(z3); overall bracket scale omitted.
def bracket_coeff (a b c : ℝ) : ℕ → ℕ → ℕ → ℝ
| 1 2 3 := a    | 2 1 3 := -a   | 4 5 0 := a    | 5 4 0 := -a
| 2 0 4 := b    | 0 2 4 := -b   | 5 3 1 := b    | 3 5 1 := -b
| 0 1 5 := c    | 1 0 5 := -c   | 3 4 2 := c    | 4 3 2 := -c
| _ _ _ := 0

def twice (f : ℕ → ℕ → ℕ → ℝ) (i j k l : ℕ) :=
 ([0,1,2,3,4,5].map (λ n, f i j n * f n k l)).sum
def jac (f : ℕ → ℕ → ℕ → ℝ) (i j k l : ℕ) :=
 twice f i j k l + twice f j k i l + twice f k i j l

theorem jacobi_components (a b c : ℝ) :
 jac (bracket_coeff a b c) 1 2 4 2=a*c ∧ jac (bracket_coeff a b c) 2 0 5 0=b*a ∧
 jac (bracket_coeff a b c) 0 1 3 1=c*b := by simp [jac,twice,bracket_coeff]

-- [z_j,z_k] = k_i bar(z_i) up to a common normalization.
-- The Jacobi identity for (z_j,z_k,bar(z_j)) tests k_i*k_k.
theorem compatible_twists (a b c : ℝ) (h : a*b=0) (i : b*c=0) (j : c*a=0) :
 (a=0 ∧ b=0) ∨ (b=0 ∧ c=0) ∨ (c=0 ∧ a=0) :=
begin
 rcases mul_eq_zero.mp h with h|h,
 { rcases mul_eq_zero.mp i with q|q, exact or.inl ⟨h,q⟩,
   exact or.inr (or.inr ⟨q,h⟩) },
 { rcases mul_eq_zero.mp j with q|q, exact or.inr (or.inl ⟨h,q⟩),
   exact or.inl ⟨q,h⟩ }
end

theorem nil_scaling (a b c : ℝ) :
 -9*a-12*b-15*c= -9*(a+b+c)-3*b-6*c := by ring

theorem nil_curvature_bounds (a b c : ℝ) (hb : 0≤b) (hc : 0≤c)
 (crit : -9*a-12*b-15*c=0) :
 a+b+c≤0 ∧ 108*(-(a+b+c))≤81*a+144*b+225*c ∧
 81*a+144*b+225*c≤135*(-(a+b+c)) := ⟨by linarith,by linarith,by linarith⟩

theorem nil_tangent (s : ℝ) :
 -3*s+3*s=0 ∧ -3*s+s-4*(-s/2)=0 ∧
 (3/2:ℝ)+18+3/4=81/4 ∧ (3:ℝ)^2/(81/4)=4/9 :=
 ⟨by ring,by ring,by norm_num,by norm_num⟩

-- Symmetric-trace matching and the centered uniform moments E[s^2], E[s^4].
theorem disk_coefficients (a b : ℝ) (step : 4*b= -1) (cal : 4*a+2*b=0) :
 a=1/8 ∧ b= -1/4 := ⟨by linarith,by linarith⟩

theorem centered_covariance (x y d e : ℝ) :
 ((x*y)^2+(x^2*e^2+y^2*d^2+4*x*y*d*e)/12+d^2*e^2/80
   -(x^2+d^2/12)*(y^2+e^2/12))/2 =
 x*y*d*e/6+d^2*e^2/360 := by ring

theorem mirror_symtrace_gap : (1/5:ℝ)-7/45=2/45 := by norm_num

-- Cosine and sine coefficients at the right endpoint of a matrix-valued strip.
theorem right_endpoint {E : Type*} [add_comm_group E] [module ℝ E]
 (x a b ba : E) (c s : ℝ) :
 (-s) • x + c • a - (c • b + s • ba) =
 c • (a-b)-s • (x+ba) := by simp only [smul_sub,smul_add,neg_smul]; abel

end cat_flux_completion
