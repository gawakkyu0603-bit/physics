import analysis.inner_product_space.basic
import analysis.calculus.mean_value
import analysis.special_functions.trigonometric.arctan_deriv
import data.list.sublists
import tactic

open_locale big_operators
open_locale topology
open filter
namespace cat_charge_orientation

-- A four-form component and its complementary component are one complex
-- coordinate. Use the representative which contains index zero.
def halves : list (list ℕ) :=
 (([1,2,3,4,5,6,7] : list ℕ).sublists_len 3).map (list.cons 0)

def sees (a b : ℕ) (s : list ℕ) : ℕ := if a ∈ s ↔ b ∈ s then 1 else 0
def shared (s : list ℕ) : ℕ := sees 0 1 s + 2*sees 0 2 s + 4*sees 0 3 s
def cycle (s : list ℕ) : ℕ := sees 0 1 s + 2*sees 0 2 s + 4*sees 1 2 s
def histogram (sets : list (list ℕ)) (f : list ℕ → ℕ) : list ℕ :=
 (list.range 8).map (λ n, (sets.map f).count n)
def oddsets := halves.filter (λ s, (s.filter (λ i, i<4)).length % 2 = 1)

theorem coordinate_counts : halves.length = 35 ∧ oddsets.length = 16 := by dec_trivial
theorem shared_spectrum : histogram halves shared = [4,6,6,4,6,4,4,1] := by dec_trivial
theorem cycle_spectrum : histogram halves cycle = [0,10,10,0,10,0,0,5] := by dec_trivial
theorem rr_shared_spectrum : histogram oddsets shared = [4,0,0,4,0,4,4,0] := by dec_trivial
theorem rr_cycle_spectrum : histogram oddsets cycle = [0,4,4,0,4,0,0,4] := by dec_trivial
theorem opposite_signs (s : list ℕ) (hs : s ∈ oddsets) :
 sees 0 1 s + sees 2 3 s = 1 ∧ sees 0 2 s + sees 1 3 s = 1 ∧
 sees 0 3 s + sees 1 2 s = 1 :=
begin
 have h : ∀ s ∈ oddsets, sees 0 1 s + sees 2 3 s = 1 ∧
   sees 0 2 s + sees 1 3 s = 1 ∧ sees 0 3 s + sees 1 2 s = 1 := by dec_trivial,
 exact h s hs
end

-- The real form of the four-form generator is symmetric. Its second
-- iteration in the isolated occupied plane is a sum of squares.
theorem charge_second_order {ι : Type*} [fintype ι] (g : ι → ι → ℝ)
 (symm : ∀ i j, g i j = g j i) (p : ι) :
 (∑j, g p j*g j p) = ∑j, (g j p)^2 :=
finset.sum_congr rfl (λ j hj, by rw [symm p j, sq])

-- Two-block singular-value estimate: a cross block of order t^2 cannot
-- change the second-order coefficient of the isolated leading skew plane.
theorem block_rayleigh (u d b x y : ℝ) (gap : 0<u-d) :
 u*x^2+2*b*x*y+d*y^2 ≤ (u+b^2/(u-d))*(x^2+y^2) :=
begin
 have pos : 0 ≤ (b*x-(u-d)*y)^2 + b^2*y^2 :=
   add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _)),
 apply (le_of_mul_le_mul_right _ gap),
 field_simp [ne_of_gt gap], nlinarith
end

theorem fourth_order (m u d b t c : ℝ) (gap : 1/2≤u-d)
 (cross : 0≤b) (h : b≤c*t^2) (lower : u≤m) (upper : m≤u+b^2/(u-d)) :
 0≤m-u ∧ m-u≤2*c^2*t^4 :=
begin
 have gap_pos : 0<u-d := by linarith,
 have bnd : b^2 ≤ (c*t^2)^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr h)
   (show 0≤c*t^2+b, by linarith)],
 have g : b^2/(u-d) ≤ 2*b^2,
 { apply (div_le_iff gap_pos).2, nlinarith [mul_nonneg (sq_nonneg b)
   (show 0≤2*(u-d)-1, by linarith)] },
 exact ⟨by linarith,by nlinarith⟩
end

theorem restoring_bound {ι : Type*} [fintype ι] (w v : ι → ℝ) (m : ℝ)
 (hw : ∀j, m ≤ w j) : m*(∑j, (v j)^2) ≤ ∑j, w j*(v j)^2 :=
begin
 rw [finset.mul_sum], exact finset.sum_le_sum
   (λ j hj, mul_le_mul_of_nonneg_right (hw j) (sq_nonneg _))
end

def iter {E : Type*} (T : E → E) (v : E) : ℕ → E
| 0 := v
| (n+1) := T (iter n)

theorem flat_all_orders {E : Type*} [has_zero E] (T : E → E) (v : E)
 (hz : T 0=0) (h : T v=0) : ∀ n, iter T v (n+1)=0
| 0 := h
| (n+1) := by {change T (iter T v (n+1))=0, rw [flat_all_orders n,hz]}

-- A two-colouring would be necessary for each occupied plane to have one
-- index in each of two SU(4) factors.
theorem cycle_cannot_split (a b c : bool) : ¬ (a≠b ∧ b≠c ∧ c≠a) :=
by {cases a; cases b; cases c; dec_trivial}

theorem primitive_invariant : (2:ℤ)*2-0^2 = 4 := by norm_num
theorem first_jacobi_coefficient : (1:ℤ)*(-2)+(-2)*4+1*(-2) = -12 := by norm_num

-- Determinant and second elementary symmetric polynomial of a real symmetric
-- three by three matrix in upper-triangular order (a,b,c,d,e,f).
def det3 (a b c d e f : ℤ) := a*d*f+2*b*c*e-a*e^2-d*c^2-f*b^2
def second (a b c d e f : ℤ) := a*d+a*f+d*f-b^2-c^2-e^2

theorem two_fluxes : det3 0 (-1) 0 0 0 0=0 ∧ second 0 (-1) 0 0 0 0 = -1 ∧
 det3 0 0 0 (-1) 0 1=0 ∧ second 0 0 0 (-1) 0 1 = -1 ∧
 det3 0 1 0 (-1) 0 1 = -1 := by norm_num [det3,second]
theorem third_flux : det3 0 1 0 2 0 (-1)=1 ∧ second 0 1 0 2 0 (-1) = -3 :=
by norm_num [det3,second]
theorem same_phase (x : ℝ) : (1+x^2)>0 := by positivity
theorem coprime_stacks (a b : ℝ) (degree_zero : a+b=0) (offdiag : -a=0) :
 a=0 ∧ b=0 := ⟨by linarith,by linarith⟩
theorem copied_stack (a b c : ℝ) (degree_zero : a+b+c=0) (offdiag : -a-c=0) :
 b=0 ∧ c = -a := ⟨by linarith,by linarith⟩

-- With y=(I-F)x and Oy=(I+F)x, skewness gives Cayley orthogonality.
theorem cayley_isometry {E : Type*} [normed_add_comm_group E] [inner_product_space ℝ E]
 (x fx : E) (h : (inner x fx : ℝ)=0) : ‖x+fx‖^2 = ‖x-fx‖^2 :=
by rw [norm_add_sq_real,norm_sub_sq_real,h]; ring
theorem coupling_length (rotation_column_sq : fin 6 → ℝ)
 (h : ∀i, rotation_column_sq i=1) :
 (1:ℝ)/2+ (∑i, rotation_column_sq i)/4=2 :=
by simp [h]; norm_num
theorem universal_coupling : (1:ℝ)/2+1/6=2/3 := by norm_num
theorem radial_factor (r : ℝ) (h : r≠0) :
 (r^6+r^2)/r^3 = r^3+1/r :=
by {field_simp [h], ring}

theorem calibration_gap (a b t : ℝ) (ht : t^2=a^2+b^2) :
 (t-a)*(t+a)=b^2 := by nlinarith
theorem double_zero (r : ℝ) : (r^4-1)^2=(r-1)^2*(r^3+r^2+r+1)^2 := by ring
theorem radial_coefficient : (4:ℝ)^2/(4+4)=2 := by norm_num
theorem disk_mass_ratio : (2:ℝ)*2/6/4=1/6 := by norm_num

-- With three eigenvalues of one sign and elementary symmetric polynomials
-- tr=det, the real calibration is negative.
theorem same_sign_wrong_phase (a b c : ℝ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
 (h : a+b+c=a*b*c) : 1-(a*b+a*c+b*c)<0 :=
begin
 have hab : 1<a*b,
 { by_contra hle, push_neg at hle,
   have aux := mul_le_mul_of_nonneg_right hle hc.le, nlinarith },
 nlinarith [mul_pos ha hc,mul_pos hb hc]
end
theorem mirror_tachyon (a b c : ℝ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
 (aligned : c-a-b=a*b*c) :
 a+b<c ∧ 2*(a+b+c)-4*c = -2*(c-a-b) ∧ -2*(c-a-b)<0 :=
begin
 have pos := mul_pos (mul_pos ha hb) hc,
 exact ⟨by linarith,by ring,by linarith⟩
end

-- A smooth, plane-wise frequency rule preserving the signed calibration
-- in a neighbourhood of each flux has its entire response fixed.
theorem angle_rule_unique (f : ℝ → ℝ) (diff : differentiable ℝ f) (at_zero : f 0=0)
 (slope : has_deriv_at f 1 0)
 (law : ∀ a : ℝ, (λ b : ℝ, f ((a+b)/(1-a*b))) =ᶠ[𝓝 0] (λ b, f a+f b)) :
 f = real.arctan :=
begin
 have df : ∀ a : ℝ, deriv f a = 1/(1+a^2),
 { intro a,
   have hn : has_deriv_at (λ b : ℝ, a+b) 1 0 := (has_deriv_at_id (0:ℝ)).const_add a,
   have hd : has_deriv_at (λ b : ℝ, 1-a*b) (-a) 0 :=
     by simpa using (((has_deriv_at_id (0:ℝ)).const_mul a).const_sub 1),
   have hq : has_deriv_at (λ b : ℝ, (a+b)/(1-a*b)) (1+a^2) 0,
   { convert hn.div hd (by simp : 1-a*0≠0) using 1, simp, ring },
   have hf : has_deriv_at f (deriv f a) ((a+0)/(1-a*0)) := by simpa using (diff a).has_deriv_at,
   have left : has_deriv_at (f ∘ (λ b : ℝ, (a+b)/(1-a*b)))
     (deriv f a*(1+a^2)) 0 := by {apply has_deriv_at.comp 0 _ hq, exact hf},
   have right : has_deriv_at (λ b : ℝ, f ((a+b)/(1-a*b))) 1 0 :=
     (slope.const_add (f a)).congr_of_eventually_eq (law a),
   apply (eq_div_iff (by positivity : (1+a^2:ℝ)≠0)).2,
   exact left.unique right },
 have zero : ∀ a : ℝ, deriv (λ x, f x-real.arctan x) a=0,
 { intro a, exact ((diff a).has_deriv_at.sub (real.has_deriv_at_arctan a)).deriv.trans
     (by rw [df,sub_self]) },
 funext a,
 have same := is_const_of_deriv_eq_zero (diff.sub real.differentiable_arctan) zero a 0,
 change f a-real.arctan a = f 0-real.arctan 0 at same,
 rw [at_zero,real.arctan_zero] at same, linarith
end
end cat_charge_orientation
