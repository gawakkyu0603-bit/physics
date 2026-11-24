import tactic
import analysis.special_functions.trigonometric.basic
import analysis.calculus.deriv.mul
import analysis.special_functions.integrals
import data.matrix.rank
import analysis.inner_product_space.basic

noncomputable theory
namespace cat_bounce_records
open set measure_theory
open_locale interval filter

open_locale matrix real_inner_product_space
open finite_dimensional

theorem torque_cancels (kin ab ba : ℝ) (symmetric_force : ab=ba) :
 (kin-ab)-(kin-ba)=0 := by linarith

theorem inertial_floor {H : Type*} [normed_add_comm_group H] [inner_product_space ℝ H]
 (x v : H) (e : ℝ) (he : 0<e) (kinetic : ‖v‖^2 ≤ 2*e) :
 (⟪x,v⟫_ℝ)^2/(2*e) ≤ ‖x‖^2 :=
begin
 have cs:=abs_real_inner_le_norm x v,
 have h1:=mul_self_le_mul_self (abs_nonneg (⟪x,v⟫_ℝ)) cs,
 have h2:=mul_le_mul_of_nonneg_left kinetic (sq_nonneg ‖x‖),
 rw [← sq, sq_abs, ← sq, mul_pow] at h1,
 apply (div_le_iff (by linarith : 0<2*e)).2, linarith
end

theorem rank_defect {ι κ : Type*} [fintype ι] [fintype κ]
 (a b : matrix ι κ ℝ) : (a-b).rank≤a.rank+b.rank :=
begin
 let p:=a.mul_vec_lin.range, let q:=b.mul_vec_lin.range,
 have h : (a-b).mul_vec_lin.range ≤ p⊔q,
 {rintros _ ⟨v,rfl⟩,
  rw [matrix.mul_vec_lin_apply,matrix.sub_mul_vec],
  exact submodule.sub_mem _ ((le_sup_left : p≤p⊔q) ⟨v,rfl⟩)
                             ((le_sup_right : q≤p⊔q) ⟨v,rfl⟩)},
 exact (submodule.finrank_mono h).trans (submodule.finrank_add_le_finrank_add_finrank p q)
end

theorem angular_rank {ι κ : Type*} [fintype ι] [fintype κ]
 (x v : matrix ι κ ℝ) : (x ⬝ vᵀ-v ⬝ xᵀ).rank ≤ x.rank+x.rank :=
begin
 have h:=rank_defect (x ⬝ vᵀ) (v ⬝ xᵀ),
 have r:=matrix.rank_mul_le_right v xᵀ,
 rw [matrix.rank_transpose] at r,
 exact h.trans (add_le_add (matrix.rank_mul_le_left x vᵀ) r)
end

theorem surviving_three_directions {ι κ : Type*} [fintype ι] [fintype κ]
 (x v : matrix ι κ ℝ) (six : 6≤(x ⬝ vᵀ-v ⬝ xᵀ).rank) : 3≤x.rank :=
by have h:=le_trans six (angular_rank x v); omega

-- The half-difference and half-sum of the two transverse axis lengths.
theorem port_distances (a b x y : ℝ)
 (left : a^2=(1+x)^2+y^2) (right : b^2=(1-x)^2+y^2) :
 ((a-b)/2)*((a+b)/2)=x ∧ ((a-b)/2)^2+((a+b)/2)^2=1+x^2+y^2 :=
begin
 split,
 {calc ((a-b)/2)*((a+b)/2) = (a^2-b^2)/4 : by ring
     ... = x : by rw [left,right]; ring},
 {calc ((a-b)/2)^2+((a+b)/2)^2 = (a^2+b^2)/2 : by ring
     ... = 1+x^2+y^2 : by rw [left,right]; ring}
end

theorem port_sign (r e x y s : ℝ) (focus : r*e=x)
 (axes : r^2+e^2=1+x^2+y^2) (exterior : s<e^2) :
 s<r^2 ↔ s*y^2 < (x^2-s)*(1-s) :=
begin
 have ident : (r^2-s)*(e^2-s)=(x^2-s)*(1-s)-s*y^2,
 {calc (r^2-s)*(e^2-s) = (r*e)^2-s*(r^2+e^2)+s^2 : by ring
    ... = _ : by rw [focus,axes]; ring},
 have pos := sub_pos.2 exterior,
 split,
 {intro h, have h' := mul_pos (sub_pos.2 h) pos, rw [ident] at h', linarith},
 {intro h, by_contra hn,
  have nonpos := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (le_of_not_gt hn)) pos.le,
  rw [ident] at nonpos, linarith}
end

theorem port_outer_axis (a b x y s : ℝ) (ha : 0≤a) (hb : 0≤b)
 (left : a^2=(1+x)^2+y^2) (right : b^2=(1-x)^2+y^2) (hs : s<1/2) :
 s<((a+b)/2)^2 :=
begin
 have h : ((a+b)/2)^2=(1+x^2+y^2+a*b)/2 :=
   calc ((a+b)/2)^2 = (a^2+b^2+2*a*b)/4 : by ring
      ... = (1+x^2+y^2+a*b)/2 : by rw [left,right]; ring,
 rw [h], linarith only [hs,mul_nonneg ha hb,sq_nonneg x,sq_nonneg y]
end

theorem port_inversion (x y s : ℝ) :
 (s*(-y)^2 < ((-x)^2-s)*(1-s)) ↔ (s*y^2 < (x^2-s)*(1-s)) :=
by simp

theorem two_port_return (p : ℝ) :
 1-(p^2+(1-p)^2)=2*p*(1-p) := by ring

section born_return
open_locale complex_inner_product_space
theorem initial_state_test {H : Type*} [normed_add_comm_group H] [inner_product_space ℂ H]
 (x y : H) (p : ℝ) (orth : ⟪x,y⟫_ℂ=0)
 (first_weight : ‖⟪x,x⟫_ℂ‖=p) (second_weight : ‖⟪y,y⟫_ℂ‖=1-p) :
 ‖⟪x+y,x⟫_ℂ‖^2+‖⟪x+y,y⟫_ℂ‖^2=p^2+(1-p)^2 :=
begin
 have reverse : ⟪y,x⟫_ℂ=0 := inner_eq_zero_symm.1 orth,
 simp only [inner_add_left,orth,reverse,zero_add,add_zero,first_weight,second_weight]
end
end born_return

-- The history probability space may be nonatomic; every hypothesis concerns one observer.
theorem empty_contact_floor {α : Type*} [measurable_space α]
 (μ : measure α) [is_probability_measure μ] (empty : set α) (q : α → ℝ)
 (he : measurable_set empty) (hq : integrable q μ)
 (positive : ∀ x,0≤q x) (kept : ∀ x∈empty, q x=1) :
 (μ empty).to_real ≤ ∫ x, q x ∂μ :=
begin
 rw [← measure_theory.integral_indicator_one he],
 apply measure_theory.integral_mono_ae ((integrable_const (1:ℝ)).indicator he) hq,
 apply filter.eventually_of_forall,
 intro x, by_cases hx : x∈empty,
 {simp [set.indicator_of_mem hx,kept x hx]},
 {simpa [set.indicator_of_not_mem hx] using positive x}
end

theorem closure_support {α : Type*} [measurable_space α]
 (μ : measure α) (q : α → ℝ) (hq : integrable q μ) (positive : ∀ x,0≤q x) :
 (∫ x, q x ∂μ)=0 ↔ q =ᵐ[μ] 0 :=
measure_theory.integral_eq_zero_iff_of_nonneg_ae (filter.eventually_of_forall positive) hq

theorem far_single_quantum (detected pin : ℝ) (total : detected≤1)
 (only_far_can_close : 1-detected/5≤pin) : 4/5≤pin := by linarith

-- Apply with the two maps equal to the positive square roots of I-M_A and M_B.
theorem common_preparation {H K J : Type*} [normed_add_comm_group K] [normed_add_comm_group J]
 (a : H → K) (b : H → J) (psi : H) :
 ‖a psi‖^2+‖b psi‖^2=0 ↔ a psi=0 ∧ b psi=0 :=
begin
 split,
 {intro h,
  have ha : ‖a psi‖^2=0 := by linarith only [h,sq_nonneg ‖a psi‖,sq_nonneg ‖b psi‖],
  have hb : ‖b psi‖^2=0 := by linarith only [h,sq_nonneg ‖a psi‖,sq_nonneg ‖b psi‖],
  exact ⟨norm_eq_zero.1 (pow_eq_zero ha),norm_eq_zero.1 (pow_eq_zero hb)⟩},
 {rintro ⟨ha,hb⟩, simp [ha,hb]}
end

theorem feedback_gap (pA pB gap eps : ℝ)
 (floor : gap≤1-pA+pB) (kept : 1-eps≤pA) (closed : pB≤eps) :
 gap≤2*eps := by linarith

-- The matrix background in units in which its largest radius is one.
theorem radial_energy (a b v w c d : ℝ)
 (energy : c = v^2+w^2+(a^2+b^2)^2) (rotation : d=(a*w-b*v)^2) :
 (2*(a*v+b*w))^2 = -4*(a^2+b^2)^3+4*c*(a^2+b^2)-4*d :=
by rw [energy,rotation]; ring

theorem radial_acceleration (a b v w : ℝ) :
 2*(v^2+w^2+a*(-2*(a^2+b^2)*a)+b*(-2*(a^2+b^2)*b)) =
 2*(v^2+w^2+(a^2+b^2)^2)-6*(a^2+b^2)^2 := by ring

theorem turning_roots (x d : ℝ) :
 -4*x^3+4*(1+d)*x-4*d = -4*(x-1)*(x^2+x-d) := by ring

theorem third_harmonic (x : ℝ → ℝ) (x' : ℝ → ℝ) (t c : ℝ)
 (dx : has_deriv_at x (x' t) t) :
 has_deriv_at (λ s, 2*c-6*(x s)^2) (-12*x t*x' t) t :=
begin
 convert (has_deriv_at_const t (2*c)).sub ((dx.pow 2).const_mul 6) using 1,
 norm_num, ring
end

theorem null_at_turn (h : ℝ) (hh : h ≠ 0) :
 -(2*(2-h^2))/(h^2*h) = -2*(2-h^2)/h^3 := by rw [pow_succ h 2]; ring

theorem defocus (h : ℝ) (hh : 0<h) (hr : h^2<2) :
 -2*(2-h^2)/h^3 < 0 :=
div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) (sub_pos.2 hr)) (pow_pos hh _)

theorem optical_period (expansion curvature : ℝ → ℝ) (a b : ℝ)
 (periodic : expansion b=expansion a) (he : continuous expansion) (hc : continuous curvature)
 (ray : ∀ t, has_deriv_at expansion (-(1/2)*(expansion t)^2-curvature t) t) :
 (∫ t in a..b, curvature t) = -(1/2)*(∫ t in a..b,(expansion t)^2) :=
begin
 have h1 : continuous (λ t:ℝ,-(1/2)*(expansion t)^2) := continuous_const.mul (he.pow 2),
 have i1 : interval_integrable (λ t:ℝ,-(1/2)*(expansion t)^2) volume a b :=
   h1.interval_integrable a b,
 have i2 : interval_integrable curvature volume a b := hc.interval_integrable a b,
 have h:=interval_integral.integral_eq_sub_of_has_deriv_at (λ t ht,ray t)
      (i1.sub i2),
 rw [interval_integral.integral_sub i1 i2,
     interval_integral.integral_const_mul,periodic,sub_self] at h, linarith
end

theorem optical_period_negative (f : ℝ → ℝ) (a b : ℝ) (hab : a<b)
 (hf : continuous f) (hn : ∃t∈Icc a b, f t≠0) :
 -(1/2:ℝ)*(∫ t in a..b,(f t)^2)<0 :=
begin
 obtain ⟨t,ht,hn⟩:=hn,
 have h:=interval_integral.integral_lt_integral_of_continuous_on_of_le_of_exists_lt hab
   (continuous_const.continuous_on : continuous_on (λ x:ℝ,(0:ℝ)) (Icc a b))
   ((hf.pow 2).continuous_on) (λ x hx,sq_nonneg (f x)) ⟨t,ht,sq_pos_of_ne_zero _ hn⟩,
 simp at h, linarith
end

theorem radial_null_fastest (light axial : ℝ → ℝ) (a b : ℝ) (hab : a<b)
 (hl : continuous light) (hv : continuous axial)
 (speed : ∀t∈Ioc a b,axial t ≤light t) (slow : ∃t∈Icc a b,axial t<light t) :
 (∫ t in a..b,axial t)<∫ t in a..b,light t :=
interval_integral.integral_lt_integral_of_continuous_on_of_le_of_exists_lt hab
 hv.continuous_on hl.continuous_on speed slow

theorem flrw_boundary_derivative (a h : ℝ → ℝ) (u dh : ℝ) (ha : a u≠0)
 (expands : has_deriv_at a (h u*a u) u) (hh : has_deriv_at h dh u) :
 has_deriv_at (λ t,h t/a t) (dh/a u-(h u)^2/a u) u :=
begin
 convert (hh.div expands ha) using 1, field_simp [ha], ring
end

theorem flrw_budget (p spatial kinetic first last : ℝ)
 (hp : 0<p) (hk : spatial≤0) (hkin : 0≤kinetic) (h1 : first<0) (h2 : 0<last) :
 2*p*(spatial-kinetic-(last-first))<0 :=
mul_neg_of_pos_of_neg (by linarith) (by linarith)

-- Band edges of -d²/dt² - 30x.  The sign convention is det(0-H).
def cubic (x c d : ℝ) := -4*x^3+4*c*x-4*d
def cubic' (x c : ℝ) := -12*x^2+4*c
def det3 (a b c d e f g h i : ℝ) := a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

theorem cube_division (x r c d : ℝ) (root : d=c*r-r^3) :
 cubic x c d=(x-r)*(-4)*(x*x+x*r+r*r-c) := by rw [root]; unfold cubic; ring

-- Conjugation by sqrt(x-r), after the root polynomial is divided out.
theorem root_block (x r c d : ℝ) :
 let f := cubic x c d, v := -10*x^2-4*r*x+6*c-4*r^2, u := 28*x-r in
 u= -r+28*x ∧ v+u*x=6*c-4*r^2-5*r*x+18*x^2 ∧
 2*f+v*(2*x)+u*x^2= -8*d+(20*c-8*r^2)*x-9*r*x^2 :=
by dsimp [cubic]; split; {try {split}; ring}

theorem triple_root_block (x c : ℝ) :
 3*cubic' x c/2+18*x*x=6*c ∧ (0:ℝ)*0-18*(6*c)= -108*c :=
by unfold cubic'; split; ring

theorem root_determinant (r c d : ℝ) (hr : d=c*r-r^3) :
 det3 (-r) (6*c-4*r^2) (-8*d) 28 (-5*r) (20*c-8*r^2) 0 18 (-9*r)
 =135*(5*c*r-21*d) := by rw [hr]; unfold det3; ring

theorem viete_product (a b e c d u w : ℝ) (hs : a+b+e=0)
 (hp : a*b+a*e+b*e= -c) (ht : a*b*e= -d) :
 (u*a-w)*(u*b-w)*(u*e-w)= -w^3+c*w*u^2-d*u^3 :=
begin
 calc (u*a-w)*(u*b-w)*(u*e-w) =
    u^3*(a*b*e)-u^2*w*(a*b+a*e+b*e)+u*w^2*(a+b+e)-w^3 : by ring
 ... = _ : by rw [ht,hp,hs]; ring
end

theorem edge_product (c d : ℝ) :
 -(21*d)^3+c*(21*d)*(5*c)^2-d*(5*c)^3=d*(400*c^3-9261*d^2) := by ring

theorem sharp_factor (d : ℝ) :
 400*(1+d)^3-9261*d^2=(5-16*d)*(80+496*d-25*d^2) := by ring

theorem other_roots (d : ℝ) (hd : 0≤d) (h : d≤2) : 0<80+496*d-25*d^2 :=
by nlinarith only [hd,mul_nonneg hd (sub_nonneg.mpr h)]

-- Real Lamé band classification is the cited spectral input.
theorem fifth_gap (d q : ℝ) (hd : 0<d) (h : d<2) (gap : Prop)
 (bands : gap ↔ q<0)
 (edges : q= -(108:ℝ)*135^3*(1+d)*d*(5-16*d)*(80+496*d-25*d^2)) :
 gap ↔ d<5/16 :=
begin
 have hpos : 0 < (108:ℝ)*135^3*(1+d)*d*(80+496*d-25*d^2) :=
   mul_pos (mul_pos (mul_pos (by norm_num) (by linarith)) hd) (other_roots d hd.le h.le),
 have scaled : q= -((108:ℝ)*135^3*(1+d)*d*(80+496*d-25*d^2))*(5-16*d) :=
   by rw [edges]; ring,
 rw [bands,scaled,neg_mul,neg_lt_zero], split,
 {intro t, have h' := pos_of_mul_pos_right t hpos.le, linarith},
 {intro t, exact mul_pos hpos (by linarith)}
end

theorem critical_example : (0:ℝ)<(1/2)^2 ∧ (1/2:ℝ)^2<5/16 ∧
 5/16<(3/4:ℝ)^2 ∧ (3/4:ℝ)^2<2 := by norm_num

def blockdet (r c d : ℝ) :=
 det3 (-r) (6*c-4*r^2) (-8*d) 28 (-5*r) (20*c-8*r^2) 0 18 (-9*r)

theorem band_from_restricted_operators (r s t c d : ℝ) (hc : c=1+d)
 (hd : 0<d) (upper : d<2) (rr : d=c*r-r^3) (rs : d=c*s-s^3) (rt : d=c*t-t^3)
 (roots₁ : r+s+t=0) (roots₂ : r*s+r*t+s*t= -c) (roots₃ : r*s*t= -d)
 (gap : Prop) (spectral : gap ↔ (-108*c)*blockdet r c d*blockdet s c d*blockdet t c d<0) :
 gap ↔ d<5/16 :=
begin
 apply fifth_gap d _ hd upper gap spectral,
 unfold blockdet,
 rw [root_determinant _ _ _ rr, root_determinant _ _ _ rs, root_determinant _ _ _ rt],
 have prod := viete_product r s t c d (5*c) (21*d) roots₁ roots₂ roots₃,
 rw [edge_product] at prod,
 calc -108*c*(135*(5*c*r-21*d))*(135*(5*c*s-21*d))*(135*(5*c*t-21*d))
     = -108*135^3*c*((5*c*r-21*d)*(5*c*s-21*d)*(5*c*t-21*d)) : by ring
 ... = _ : by rw [prod,hc,sharp_factor]; ring
end

-- Symplectic transfer and the occupation in the same endpoint oscillator.
theorem occupation_nonnegative (a b c d : ℝ) (wronskian : a*d-b*c=1) :
 0≤(a^2+b^2+c^2+d^2-2)/4 :=
by nlinarith only [wronskian,sq_nonneg (a-d),sq_nonneg (b+c)]

theorem occupation_squares (a b c d : ℝ) (wronskian : a*d-b*c=1) :
 (a^2+b^2+c^2+d^2-2)/4=((a-d)^2+(b+c)^2)/4 :=
by nlinarith only [wronskian]

theorem remove_background (a g u v re im : ℝ) (hg : g≠0) :
 a-2*(re*u+im*v)+g*(u^2+v^2) =
 (a-(re^2+im^2)/g)+g*((u-re/g)^2+(v-im/g)^2) :=
by field_simp [hg]; ring

theorem optimum_background (a g u v re im : ℝ) (hg : 0<g) :
 a-(re^2+im^2)/g ≤ a-2*(re*u+im*v)+g*(u^2+v^2) :=
begin
 rw [remove_background a g u v re im hg.ne'],
 linarith only [mul_nonneg hg.le (add_nonneg (sq_nonneg (u-re/g)) (sq_nonneg (v-im/g)))]
end

-- One-way null travel and the reflection of a marked transverse screen.
def optical (x y a b : ℝ) := ((x+y)^2*a+(x-y)^2*b)/2
theorem radar_reflection (x y a b : ℝ) :
 optical x y a b-optical x y b a=2*x*y*(a-b) := by unfold optical; ring

theorem radar_axes (x a b : ℝ) :
 optical x 0 a b=optical x 0 b a ∧ optical 0 x a b=optical 0 x b a :=
by unfold optical; split; ring

theorem diagonal_separates (x a b : ℝ) (hx : x≠0) (hab : a≠b) :
 optical x x a b ≠ optical x x b a :=
begin
 intro he, have h:=radar_reflection x x a b, rw [he,sub_self] at h,
 exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hx) hx)
   (sub_ne_zero.mpr hab)) h.symm
end

theorem same_return (f g : ℝ → ℝ) (u v : ℝ)
 (same : ∀ t, f t=g t) (fu : f u=0) (gv : g v=0)
 (unique : ∀ a b, g a=0 → g b=0 → a=b) : u=v :=
unique u v ((same u).symm.trans fu) gv

theorem common_clock_error (a b s δ : ℝ) (ha : |a-s|≤δ) (hb : |b-s|≤δ) :
 |a-b|/2≤δ :=
begin
 have eq : a-b=(a-s)+(s-b) := by ring,
 rw [eq], have h:=abs_add (a-s) (s-b), rw [abs_sub_comm s b] at h, linarith
end

theorem marked_continuation {α : Type*} (record : α → ℝ) (a b : α)
 (d : record a ≠ record b) : a ≠ b := λ e, d (congr_arg record e)

-- Compensated D0 transfer and the two magnetic endpoint charges.
theorem relative_flux (l r q : ℤ) : ((l+q)-(r-q))-(l-r)=2*q ∧
 (l+q)+(r-q)=l+r := by split; ring

theorem equal_gaps_signed (p : ℝ) :
 (1*p)-(-1*p)=2*p ∧ |(1:ℝ)|*p=|(-1:ℝ)|*p := by norm_num; ring

theorem clifford_gap {R : Type*} [ring R] (a b : R) (anti : a*b+b*a=0) :
 (a+b)*(a+b)=a*a+b*b :=
by simp only [add_mul,mul_add]; rw [show a*a+b*a+(a*b+b*b)=a*a+(a*b+b*a)+b*b, by abel,anti]; simp

theorem paired_bulk (low plus minus : ℝ) (paired : plus=minus) :
 (low+plus)-minus=low := by linarith

theorem landau_sum (p r tail : ℝ) (hr : r≠1) (h : (1-r)*tail=p*r) :
 p+2*tail=p*(1+r)/(1-r) :=
by apply (eq_div_iff (sub_ne_zero.mpr (ne.symm hr))).2; nlinarith only [h]

theorem excited_tower (p r : ℝ) (h0 : 0≤r) (h1 : r<1) :
 p+2*p*r*(∑' n : ℕ,r^n)=p*(1+r)/(1-r) :=
by rw [tsum_geometric_of_lt_1 h0 h1]; field_simp [ne_of_gt (sub_pos.mpr h1)]; ring

theorem spectral_resolution (b x y : ℝ) (gap : y^2=b^2+2*x) (h : y+b≠0) :
 y-b=2*x/(y+b) := by apply (eq_div_iff h).2; nlinarith only [gap]

def cost (p : ℝ) := p*(1+p^2)/(1-p^2)
def slope (a : ℝ) := 2*(1+a^2)/(1-a^2)^2-1

theorem stable_vector_tradeoff (p t : ℝ) (hp : 0≤p) (hpt : p≤t)
 (ht : t<1) : cost p ≤ p*(1+t^2)/(1-t^2) :=
begin
 have h0 : 0≤t := le_trans hp hpt,
 have dt : 0<1-t^2 := by nlinarith only [mul_pos (sub_pos.mpr ht) (show 0<1+t,by linarith)],
 have d : p^2≤t^2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hpt) (add_nonneg h0 hp)],
 have dp : 0<1-p^2 := by linarith,
 unfold cost, apply (div_le_div_iff dp dt).2,
 nlinarith only [mul_nonneg hp (sub_nonneg.mpr d)]
end

theorem convex_cost (a x : ℝ) (da : 1-a^2≠0) (dx : 1-x^2≠0) :
 cost x-cost a-slope a*(x-a) =
 2*(x-a)^2*((1+a^2)*x+2*a)/((1-x^2)*(1-a^2)^2) :=
by unfold cost slope; field_simp [da,dx]; ring

theorem cost_tangent (a x : ℝ) (ha : 0≤a) (ha' : a<1) (hx : 0≤x) (hx' : x<1) :
 cost a+slope a*(x-a) ≤ cost x :=
begin
 have pos : ∀z:ℝ, 0≤z → z<1 → 0<1-z^2 :=
 by {intros z h h', nlinarith only [mul_pos (sub_pos.mpr h') (show 0<1+z,by linarith)]},
 have i:=convex_cost a x (pos a ha ha').ne' (pos x hx hx').ne',
 have up : 0≤2*(x-a)^2*((1+a^2)*x+2*a) := by positivity,
 have down : 0≤(1-x^2)*(1-a^2)^2 := mul_nonneg (pos x hx hx').le (sq_nonneg _),
 linarith only [i,div_nonneg up down]
end

open_locale big_operators
theorem mixed_cost {ι : Type*} (s : finset ι) (w p n : ι → ℝ) (a : ℝ)
 (hw : ∀ i∈s, 0≤w i) (norm : ∑ i in s,w i=1) (mean : ∑ i in s,w i*p i=a)
 (ha : 0≤a) (ha' : a<1) (hp : ∀ i∈s,0≤p i ∧ p i<1) (stable : ∀ i∈s,cost (p i)≤n i) :
 cost a ≤ ∑ i in s,w i*n i :=
begin
 have h : (∑ i in s,w i*(cost a+slope a*(p i-a)))≤∑ i in s,w i*n i :=
   finset.sum_le_sum (λ (i : ι) (hi : i∈s),mul_le_mul_of_nonneg_left
   (le_trans (@cost_tangent a (p i) ha ha' (hp i hi).1 (hp i hi).2) (stable i hi)) (hw i hi)),
 have term : ∀ i,w i*(cost a+slope a*(p i-a))=
   w i*cost a+(w i*p i)*slope a-w i*(slope a*a) := λ i,by ring,
 simp_rw [term] at h,
 rw [finset.sum_sub_distrib,finset.sum_add_distrib,← finset.sum_mul,← finset.sum_mul,
     ← finset.sum_mul,norm,mean] at h, linarith
end

theorem fraction_bound (p f n : ℝ) (hp : 0<p) (hu : p<1) (hf : 0≤f)
 (rate : f*n=p) (h : cost p≤n) : p^2*(1+f)≤1-f :=
begin
 have den : 0<1-p^2 := by nlinarith only [mul_pos (sub_pos.mpr hu) (show 0<1+p,by linarith)],
 have a:=mul_le_mul_of_nonneg_left ((div_le_iff den).1 h) hf,
 have b : p*(f*(1+p^2))≤p*(1-p^2),
 {calc p*(f*(1+p^2)) = f*(p*(1+p^2)) : by ring
   ... ≤ f*(n*(1-p^2)) : a
   ... = (f*n)*(1-p^2) : by ring
   ... = p*(1-p^2) : by rw [rate]},
 have u := (mul_le_mul_left hp).1 b, nlinarith only [u]
end

theorem wilson_change (f m q : ℝ) :
 2*real.pi*f*(m+2*q)-2*real.pi*f*m=4*real.pi*f*q := by ring

theorem dark_probability (t : ℝ) :
 ((1-real.cos (2*t))^2+(real.sin (2*t))^2)/4=(real.sin t)^2 :=
begin
 have h:=real.sin_sq_add_cos_sq (2*t), have h':=real.sin_sq_add_cos_sq t,
 rw [real.cos_two_mul] at *, nlinarith only [h,h']
end

theorem quarter_area (q : ℝ) : 4*real.pi*(1/4)*q=real.pi*q := by ring

theorem square_loop_time (length speed : ℝ) (l : 0≤length) (v : 0<speed)
 (bound : speed≤1) : 2*length≤2*length/speed :=
by apply (le_div_iff v).2; nlinarith only [mul_nonneg l (sub_nonneg.mpr bound)]

end cat_bounce_records
