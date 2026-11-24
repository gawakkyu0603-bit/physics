import analysis.special_functions.log.basic
import analysis.special_functions.trigonometric.deriv
import data.complex.exponential_bounds
import measure_theory.integral.bochner
import linear_algebra.matrix.trace
import tactic

noncomputable theory
open_locale big_operators
open measure_theory
namespace cat_magnetic_orbifold

-- Real and imaginary coordinates can be treated independently in these identities.
theorem rank_defect (a b c : ℝ) :
  (a+b+c)^2-3*(a^2+b^2+c^2) = -((a-b)^2+(b-c)^2+(c-a)^2) := by ring

theorem ranks_equal (a b c : ℝ) :
  (a+b+c)^2=3*(a^2+b^2+c^2) ↔ a=b ∧ b=c :=
begin
  split,
  { intro h, have H := rank_defect a b c,
    have p : (a-b)^2=0 := by nlinarith [sq_nonneg (a-b),sq_nonneg (b-c),sq_nonneg (c-a)],
    have q : (b-c)^2=0 := by nlinarith [sq_nonneg (a-b),sq_nonneg (b-c),sq_nonneg (c-a)],
    exact ⟨by nlinarith [sq_eq_zero_iff.mp p],by nlinarith [sq_eq_zero_iff.mp q]⟩ },
  { rintro ⟨rfl,rfl⟩, ring }
end

theorem trace_moment (a b c g y : ℝ) :
 (2*g+y/2)*(a^2+b^2+c^2)+(y-2*g)*(a*b+b*c+c*a) =
 g*((a-b)^2+(b-c)^2+(c-a)^2)+y*(a+b+c)^2/2 := by ring

theorem regular_antipodes_moment (g y : ℝ) :
 (6*(4*y)+12*(8*g)+24*(4*g-y))/4-6*(8*g)=0 := by ring

theorem finite_shape_energy (g y u c trvar trmean : ℝ)
  (hv : u=trvar+trmean) :
 y*(u-c/2)+g*c/2-y*trmean = y*trvar+(g-y)*c/2 := by {rw [hv],ring}

theorem shape_bound (g y variance comm : ℝ)
  (hy : 0≤y) (hg : y≤g) (hv : 0≤variance) (hc : 0≤comm) :
 0≤y*variance+(g-y)*comm/2 :=
 add_nonneg (mul_nonneg hy hv) (div_nonneg (mul_nonneg (sub_nonneg.mpr hg) hc) (by norm_num))

-- Cyclicity is proved for actual square complex matrices, including nonnormal ones.
theorem square_trace {ι : Type*} [fintype ι] [decidable_eq ι] (a b : matrix ι ι ℂ) :
 matrix.trace ((a*b-b*a)*(a*b-b*a)) =
 2*(matrix.trace ((b*a)*(b*a))-matrix.trace ((b*b)*(a*a))) :=
begin
  have h1 : matrix.trace ((a*b)*(a*b))=matrix.trace ((b*a)*(b*a)),
  { calc matrix.trace ((a*b)*(a*b)) = matrix.trace (a*(b*(a*b))) : by rw [mul_assoc]
    ... = matrix.trace ((b*(a*b))*a) : matrix.trace_mul_comm _ _
    ... = _ : by simp only [mul_assoc] },
  have h2 : matrix.trace ((a*b)*(b*a))=matrix.trace ((b*b)*(a*a)),
  { calc matrix.trace ((a*b)*(b*a)) = matrix.trace (a*(b*(b*a))) : by rw [mul_assoc]
    ... = matrix.trace ((b*(b*a))*a) : matrix.trace_mul_comm _ _
    ... = _ : by simp only [mul_assoc] },
  have h3 : matrix.trace ((b*a)*(a*b))=matrix.trace ((a*b)*(b*a)) :=
    matrix.trace_mul_comm (b*a) (a*b),
  simp only [sub_mul,mul_sub,matrix.trace_sub], rw [h1,h3,h2], ring
end

def wave (x k d b : ℝ) := (x-k)*(x-k-d)-b*x

theorem grand_wave (x k d b : ℝ) :
 wave x k d b=x^2-(2*k+d+b)*x+k*(k+d) := by {unfold wave,ring}
theorem shape_band (k : ℝ) (hk : 0<k) (hu : k<1) :
 wave 0 k (-1) 4<0 := by {rw [grand_wave],nlinarith [mul_pos hk (sub_pos.mpr hu)]}
theorem fastest_shape (k : ℝ) :
 wave (-(1/16)) k (-1) 4=(k-7/16)^2 := by {unfold wave,ring}
theorem common_static (k u : ℝ) : wave 0 k (2*u) (4*u)=k*(k+2*u) :=
 by { unfold wave,ring }
theorem charged_poles (x k m w : ℝ) :
 (x-k-m)*(x-k-m+2*w)-4*w*(x-m)=(x-k-m-w)^2-w^2-4*w*k :=
 by ring
theorem charged_gap (k w : ℝ) : (k+5*w/4)^2-(w^2+4*w*k)=(k-3*w/4)^2 := by ring
theorem sound_ratio (w s : ℝ) : 3*(2*w^2*s^2)=2*w^2*s^2+(2*w*s)^2 := by ring

theorem radial_balance (l f o : ℝ) : l*f^3-f*o^2=f*(l*f^2-o^2) := by ring
theorem positive_charge_well (l f v : ℝ) (hf : f≠0) :
 l*f^4/4+l*v^6/(2*f^2)-3*l*v^4/4 =
 l*(f^2-v^2)^2*(f^2+2*v^2)/(4*f^2) := by {field_simp [hf],ring}
theorem static_charge_pole (l f s z o : ℝ) (circ : o^2=l*f^2) :
 (3*l*f^2*s^2+l*f^3*z)-(s^2+f*z)*o^2=2*o^2*s^2 :=
 by {rw [circ],ring}
theorem density_force (p s f l : ℝ) (hf : f≠0) :
 4*(3*l*f^4/4)*(2*p^2*s^2/f^2) = 3*p^2*(2*l*f^2*s^2) :=
 by {field_simp [hf],ring}
theorem tracking_redshift (a b u v : ℝ) (h : a*u=b*v) (hne : b*v≠0) :
 a*u/(b*v)=1 := by {rw [h],exact div_self hne}

def ent (x : ℝ) := x*real.log x
lemma chord (x u : ℝ) (hx : 0≤x) (hu : 0<u) (hle : x≤u) : ent x≤x*real.log u :=
begin
  rcases eq_or_lt_of_le hx with rfl|h,
  { simp [ent] },
  exact mul_le_mul_of_nonneg_left ((real.log_le_log h hu).mpr hle) h.le
end

theorem endpoint_spectrum {ι : Type*} (s : finset ι) (x : ι → ℝ) (u w count : ℝ)
 (hu : 0<u) (hw : 0≤w) (hx : ∀i∈s, 0≤x i ∧ x i≤u)
 (matched : w*(∑i in s,x i)=count*u) :
 w*(∑i in s,ent (x i))-count*ent u≤0 :=
begin
  have t : (∑i in s,ent (x i))≤∑i in s,(x i)*real.log u :=
    finset.sum_le_sum (λ i hi, chord (x i) u (hx i hi).1 hu (hx i hi).2),
  rw [←finset.sum_mul] at t,
  have b := mul_le_mul_of_nonneg_left t hw,
  rw [←mul_assoc, matched] at b,
  change w*(∑i in s,ent (x i))-count*(u*real.log u)≤0,
  rw [←mul_assoc count u (real.log u)], linarith only [b]
end

-- Quadratic form on the difference of two point measures. The Gaussian feature
-- representation is the standard Fourier transform of the planar heat kernel.
theorem signed_heat (a b energy : ℝ) (gram : 2*a-2*b=energy) (pos : 0≤energy) :
 b-a≤0 := by linarith
theorem spectral_heat_sign {X : Type*} [measurable_space X] (μ : measure X)
  (c s weight : X → ℝ) (hw : ∀x,0≤weight x) :
  0 ≤ ∫ x, weight x * ((c x)^2+(s x)^2) ∂μ :=
 integral_nonneg (λ x, mul_nonneg (hw x) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
theorem coulomb_response_sign (intra inter : ℝ)
 (cpd : 0≤intra+intra-inter-inter) : inter-intra≤0 := by linarith

theorem paired_direction (q y g d : ℝ) :
 y*(d/2)+g*(2*(q^2-d))/2=g*q^2+(y/2-g)*d := by ring

theorem projected_counts (v ch : ℝ) : (v+ch)/4-v=(ch-3*v)/4 := by ring
theorem coulomb_trace (r t : ℝ) :
 2*(r^2+t^2)-2*(2*r*t) = 2*(r-t)^2 := by ring
theorem newton_exclusion (m a missing : ℝ) (ha : a≤0) (hm : m=missing+a) (h : 0<m) :
 -a<missing := by linarith

lemma positive_tangent (a z : ℝ) (ha : 0<a) (hz : 0<z) :
 0≤ent a-ent z-(1+real.log z)*(a-z) :=
begin
  have h := real.log_le_sub_one_of_pos (div_pos hz ha),
  rw [real.log_div (ne_of_gt hz) (ne_of_gt ha)] at h,
  have hh := mul_le_mul_of_nonneg_left h ha.le,
  have he : a*(z/a-1)=z-a := by {field_simp [ne_of_gt ha],ring},
  rw [he] at hh, unfold ent, nlinarith
end

lemma middle_chord (x : ℝ) (hx : 0≤x) (hu : x≤1/3) :
 ent (1-2*x)≤ -x*real.log 3 :=
begin
  have hz : 0<1-2*x := by linarith,
  have a := mul_nonneg (show 0≤3*x, by linarith)
    (positive_tangent (1/3) (1-2*x) (by norm_num) hz),
  have b := mul_nonneg (show 0≤1-3*x, by linarith)
    (positive_tangent 1 (1-2*x) (by norm_num) hz),
  have he : ent (1/3) = -(real.log 3)/3 := by {simp [ent,div_eq_mul_inv],ring},
  have h1 : ent 1=0 := by simp [ent],
  rw [he] at a, rw [h1] at b, nlinarith only [a,b]
end

lemma reciprocal_pair_bound (h x : ℝ) (hh : 1≤h) (hs : h+h⁻¹=2+x) :
 2*(ent h+ent h⁻¹)≤x^2+4*x :=
begin
  have hp : 0<h := by linarith,
  have hn := ne_of_gt hp,
  have hi : h*h⁻¹=1 := mul_inv_cancel hn,
  have hi1 : h⁻¹≤1 := inv_le_one hh,
  have hd : 0≤h-h⁻¹ := by linarith,
  have bound := real.self_le_sinh_iff.mpr (real.log_nonneg hh),
  rw [real.sinh_eq,real.exp_neg,real.exp_log hp] at bound,
  have prod := mul_nonneg hd (show 0≤h-h⁻¹-2*real.log h, by linarith),
  have sq : (h+h⁻¹)^2=(2+x)^2 := congr_arg (λ t : ℝ,t^2) hs,
  unfold ent, rw [real.log_inv], nlinarith only [prod,sq,hi]
end

theorem nonpositive_cycle_when_gaussian_stable (x h : ℝ) (hx : 0≤x) (hu : x≤1/3)
  (hh : 1≤h) (hs : h+h⁻¹=2+x) :
 2*ent x+4*ent (1-2*x)+ent (4*x)+2*(ent h+ent h⁻¹)≤ -x/3 :=
begin
  have hlog : 1≤real.log 3 :=
    (real.le_log_iff_exp_le (by norm_num : (0:ℝ)<3)).mpr (real.exp_one_lt_d9.le.trans (by norm_num)),
  have small := chord x (1/3) hx (by norm_num) hu,
  have eq : real.log (1/3) = -real.log 3 := by simp,
  rw [eq] at small,
  have four := chord (4*x) (4/3) (by linarith) (by norm_num) (by linarith),
  have log4 := real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4/3),
  have a := mul_le_mul_of_nonneg_left hlog hx,
  have b := mul_le_mul_of_nonneg_left log4 (show 0≤4*x,by linarith),
  have c := mul_nonneg hx (show 0≤1/3-x,by linarith),
  nlinarith only [small,four,middle_chord x hx hu,reciprocal_pair_bound h x hh hs,a,b,c]
end

theorem cyclic_pair_tachyon (m y : ℝ) (hm : 0<m) (hy : 0≤y) :
  m^2-y*m<0 ↔ m^2<y^2 :=
begin
  have p : 0<m+y := by linarith,
  split,
  { intro h, have d : m<y := by {by_contra c,push_neg at c,nlinarith [mul_nonneg hm.le (sub_nonneg.mpr c)]},
    nlinarith [mul_pos (sub_pos.mpr d) p] },
  { intro h, have d : m<y := by {by_contra c,push_neg at c,nlinarith [mul_nonneg (sub_nonneg.mpr c) p.le]},
    nlinarith [mul_pos hm (sub_pos.mpr d)] }
end

lemma log_small (x : ℝ) (hx : 0<x) (hu : x≤27/80) : real.log x ≤ -1 :=
begin
  rw [real.log_le_iff_le_exp hx,real.exp_neg,inv_eq_one_div,le_div_iff (real.exp_pos 1)],
  have t := mul_le_mul_of_nonneg_right hu (real.exp_pos 1).le,
  nlinarith only [t,real.exp_one_lt_d9]
end

lemma extended_middle_chord (x : ℝ) (hx : 0≤x) (hu : x≤27/80) :
 ent (1-2*x)≤ -(26/27)*x :=
begin
  have hz : 0<1-2*x := by linarith,
  have wa : 0≤(80/27)*x := by linarith,
  have a := mul_nonneg wa (positive_tangent (13/40) (1-2*x) (by norm_num) hz),
  have b := mul_nonneg (show 0≤1-(80/27)*x,by linarith)
    (positive_tangent 1 (1-2*x) (by norm_num) hz),
  have top : ent (13/40)≤ -(13/40) :=
    by {unfold ent, linarith only [log_small (13/40) (by norm_num) (by norm_num)]},
  have c := mul_le_mul_of_nonneg_left top wa,
  have h1 : ent 1=0 := by simp [ent],
  rw [h1] at b, nlinarith only [a,b,c]
end

theorem cycle_negative_margin (x h : ℝ) (hx : 0≤x) (hu : x≤27/80)
 (hh : 1≤h) (hs : h+h⁻¹=2+x) :
 2*ent x+4*ent (1-2*x)+ent (4*x)+2*(ent h+ent h⁻¹)≤ -x/10 :=
begin
  have one := chord x (27/80) hx (by norm_num) hu,
  have a := mul_le_mul_of_nonneg_left (log_small (27/80) (by norm_num) le_rfl) hx,
  have four := chord (4*x) (27/20) (by linarith) (by norm_num) (by linarith),
  have b := mul_le_mul_of_nonneg_left (real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<27/20))
    (show 0≤4*x,by linarith),
  have c := mul_nonneg hx (show 0≤27/80-x,by linarith),
  have e1 : ent x≤ -x := by simpa using one.trans a,
  have e4 := four.trans b,
  have e2 := extended_middle_chord x hx hu,
  have e3 := reciprocal_pair_bound h x hh hs,
  have power : x^2≤(27/80)*x := by nlinarith only [c],
  have total := add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left e1
    (show (0:ℝ)≤2,by norm_num)) (mul_le_mul_of_nonneg_left e2 (show (0:ℝ)≤4,by norm_num))) e4) e3,
  refine total.trans _,
  linarith only [hx,power]
end

theorem finite_tachyon_margin (x m y : ℝ) (hx : 27/80<x) (hu : x≤4/9)
 (hm : 0≤m) (hy : 0≤y) (ms : m^2=1-2*x) (ys : y^2=x) :
 1/240<m*y-m^2 :=
begin
  have ml : m^2≤y^2 := by {rw [ms,ys],linarith only [hx]},
  have ul : y^2≤(2*m)^2 := by {rw [ys,mul_pow,ms],linarith only [hu]},
  have l : m≤y := by simpa only [abs_of_nonneg hm,abs_of_nonneg hy] using (sq_le_sq.mp ml),
  have hm2 : 0≤2*m := mul_nonneg (by norm_num) hm,
  have u : y≤2*m := by simpa only [abs_of_nonneg hy,abs_of_nonneg hm2] using (sq_le_sq.mp ul),
  have pos := mul_nonneg (sub_nonneg.mpr u) (sub_nonneg.mpr l),
  have id : (2*m-y)*(y-m)=3*(m*y-m^2)-(y^2-m^2) := by ring,
  rw [id,ys,ms] at pos, rw [ms], linarith only [hx,pos]
end

end cat_magnetic_orbifold
