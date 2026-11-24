import analysis.special_functions.sqrt
import analysis.calculus.deriv.inv
import algebra.big_operators.basic
import analysis.special_functions.trigonometric.deriv
import tactic

noncomputable theory
namespace overlapping_contacts

theorem shell_root (m p h s : ℝ) (hm : 0 < m) (hs : 0 ≤ s)
 (root : s^2 = m^2+h*p^2) :
 2*m*(p^2/(m+s))+h*(p^2/(m+s))^2=p^2 :=
begin
 have den : m+s ≠ 0 := ne_of_gt (by linarith),
 field_simp [den], linear_combination -(m+s)*p^2*root
end

theorem pole_free_root (s t : ℝ) (hs : 0 ≤ s) (h : 0 < t) (root : s^2=1+4*t) :
 2/(1+s) = 1-t*(2/(1+s))^2 :=
begin have hn : 1+s ≠ 0 := ne_of_gt (by linarith), field_simp [hn], nlinarith end

theorem calibration_coefficients (u v w z : ℝ) (h₁ : u=1) (h₂ : v=2*u)
 (h₃ : w=2*v+u*u) (h₄ : z=2*w+2*u*v) : v=2 ∧ w=5 ∧ z=14 :=
by subst u; subst v; subst w; subst z; norm_num

theorem catalan_positive_cone (u v : ℝ) (hu : 0 ≤ u) (hv : u ≤ v) :
 real.sqrt u ≤ real.sqrt v := real.sqrt_le_sqrt hv

theorem mixed_phase_sign (a b x y : ℝ) (ha : 0<a) (hb : 0<b) (hx : 0<x)
 (hy : x<y) : a/(y+b) < a/(x+b) :=
(div_lt_div_left ha (by linarith : 0<y+b) (by linarith : 0<x+b)).2 (by linarith)

theorem energy_strictly_decreases (p m u v : ℝ) (hp : p≠0) (hm : 0<m) (hu : 0≤u) (hv : u<v) :
 p^2/(m+v) < p^2/(m+u) :=
(div_lt_div_left (sq_pos_of_ne_zero p hp) (by linarith : 0<m+v) (by linarith : 0<m+u)).2 (by linarith)

-- A path takes an edge of strictly positive weight at each step.
section graph
variables {V : Type*} (w : V → V → ℝ)
def twins : Prop := ∀ i j, 0<w i j → ∀ k, k≠i → k≠j → w i k=w j k
inductive walk (s : V) : V → Prop
| here : walk s
| step : ∀ {i j}, walk i → 0<w i j → walk j
variables (sym : ∀ i j, w i j=w j i) (diag : ∀ i, w i i=0) (law : twins w)
include sym law
theorem adjacent_edge_weights {i j k : V} (hj : 0<w i j) (hk : 0<w i k)
 (hji : j≠i) (hki : k≠i) : w i j = w i k :=
begin
 by_cases h : j=k, { rw [h] },
 have a := law i k hk j hji h,
 have b := law i j hj k hki (ne.symm h),
 exact a.trans ((sym k j).trans b.symm)
end

include diag
theorem uniform_component_row {s n j : V} (hn : 0<w s n) (path : walk w s j) :
 j=s ∨ w s j=w s n :=
begin
 have ns : n≠s := λ e, by { subst n, rw [diag s] at hn, exact (lt_irrefl _ hn) },
 induction path with i j path edge ih,
 { exact or.inl rfl },
 by_cases js : j=s, {exact or.inl js}, right,
 rcases ih with is|prev,
 { subst i, exact adjacent_edge_weights w sym law edge hn js ns },
 by_cases is : i=s,
 { subst i, exact adjacent_edge_weights w sym law edge hn js ns },
 have h := law i j edge s (ne.symm is) (ne.symm js),
 calc w s j=w j s : sym _ _
 ... = w i s : h.symm
 ... = w s i : sym _ _
 ... = w s n : prev
end

omit diag law sym
theorem finite_row_budget (c M : ℝ) (hc : 0<c) : ¬ (∀ n : ℕ, (n:ℝ)*c ≤ M) :=
begin
 intro all, obtain ⟨n,hn⟩:=exists_nat_gt (M/c),
 have gt : M < (n:ℝ)*c := (div_lt_iff hc).mp hn, exact (not_lt_of_ge (all n)) gt
end
end graph

theorem swap_commutes_iff {R : Type*} [ring R] (u x : R) (hu : u*u=1) :
 u*x=x*u ↔ u*x*u=x :=
begin split,
 {intro h, rw [h,mul_assoc,hu,mul_one]},
 {intro h, calc u*x=(u*x)*(u*u) : by rw [hu,mul_one]
 ... = (u*x*u)*u : by rw [mul_assoc (u*x) u u]
 ... = x*u : by rw [h]}
end

theorem transposition_entries {V : Type*} (w : V → V → ℝ) (perm : V → V)
 (i j : V) (pi : perm i=j) (pj : perm j=i) (fixed : ∀ k, k≠i → k≠j → perm k=k)
 (sym : ∀ x y, w x y=w y x) (diag : ∀ x, w x x=0)
 (twin : ∀ k, k≠i → k≠j → w i k=w j k) :
 ∀ x y, w (perm x) (perm y)=w x y :=
begin
 have ri : ∀ y, w (perm i) (perm y)=w i y,
 { intro y, rw [pi], by_cases hi : y=i, {subst y, rw [pi,diag,diag]},
   by_cases hj : y=j, {subst y, rw [pj,sym]}, rw [fixed y hi hj], exact (twin y hi hj).symm },
 have rj : ∀ y, w (perm j) (perm y)=w j y,
 { intro y, rw [pj], by_cases hi : y=i, {subst y, rw [pi,sym]},
   by_cases hj : y=j, {subst y, rw [pj,diag,diag]}, rw [fixed y hi hj], exact twin y hi hj },
 intros x y, by_cases xi : x=i, {subst x, exact ri y},
 by_cases xj : x=j, {subst x, exact rj y},
 by_cases yi : y=i, {subst y, exact (sym _ _).trans ((ri x).trans (sym _ _))},
 by_cases yj : y=j, {subst y, exact (sym _ _).trans ((rj x).trans (sym _ _))},
 rw [fixed x xi xj, fixed y yi yj]
end

theorem triangle_spectrum (a b c t : ℝ) :
 (a+(b+c)/4-t)*(3*(b+c)/4-t)-3*(b-c)^2/16 =
 t^2-(a+b+c)*t+3*(a*b+b*c+c*a)/4 := by ring

theorem discriminant (a b c : ℝ) :
 (a+b+c)^2-3*(a*b+b*c+c*a) = a^2+b^2+c^2-a*b-b*c-c*a := by ring

theorem cyclic_strength (a b c d : ℝ) (hd : d≠0)
 (width : d^2=a^2+b^2+c^2-a*b-b*c-c*a) :
 3*((b-c)^2+(c-a)^2+(a-b)^2)/(16*d^2)=3/8 :=
begin field_simp [hd], nlinarith end

theorem projective_offdiagonal (u v x y l h : ℝ)
 (orth : u^2+v^2=1) (gen : (h-l)*u*v=x) (basis : y=(u*v)^2)
 : (h-l)^2*y=x^2 := by rw [basis,←gen]; ring

theorem derivative_annihilates_common_profile (a b c s t : ℝ) :
 (b-c)*(s*a+t)+(c-a)*(s*b+t)+(a-b)*(s*c+t)=0 := by ring

theorem commuting_shapes (a b c u v w : ℝ) (ab : a≠b)
 (h : (b-c)*u+(c-a)*v+(a-b)*w=0) :
 ∃ s t : ℝ, u=s*a+t ∧ v=s*b+t ∧ w=s*c+t :=
begin
 have den : a-b≠0 := sub_ne_zero.mpr ab,
 refine ⟨(u-v)/(a-b), u-(u-v)/(a-b)*a, by ring, _, _⟩;
 field_simp [den]; nlinarith
end

theorem divided_difference (eh el hi lo q amp : ℝ) (d : hi≠lo)
 (response : amp*(hi-lo)=(eh-el)*q) : amp=((eh-el)/(hi-lo))*q :=
begin field_simp [sub_ne_zero.mpr d], nlinarith end

theorem factor_turnover (u v : ℝ) :
 (v-1)*u*(u+1)-(u-1)*v*(v+1)=(v-u)*(2-(u-1)*(v-1)) := by ring

theorem single_turnover {u₁ u₂ v₁ v₂ : ℝ}
 (a : 1<u₁) (b : u₁<u₂) (c : 1<v₁) (d : v₁<v₂) :
 (u₁-1)*(v₁-1)<(u₂-1)*(v₂-1) :=
mul_lt_mul (by linarith) (by linarith) (by linarith) (by linarith)

-- Product rules in any commuting spatial coordinate system, one term per contracted index.
theorem flux_divergence (ht lx lxt l ht_xx j jx ht_x lxx : ℝ)
 (wave : lxt = lxx*ht) (sign : ht_xx=jx) :
 lxt+j*lx+(-ht_x*lx-ht*lxx+lx*ht_x+l*ht_xx-lx*j-l*jx)=0 :=
by rw [wave,sign]; ring

theorem stress_divergence (hij lj hi ljj lij hj li hjj : ℝ) :
 hij*lj+hi*ljj+lij*hj+li*hjj-(hij*lj+hj*lij)=hi*ljj+li*hjj := by ring

theorem fourier_branch (m e x p : ℝ) (h : p^2=2*m*e+x*e^2) :
 -e^2*x-2*m*e+p^2=0 := by linarith

theorem grav_angular_strength (g Ω y d : ℝ) :
 (2*g/5)*Ω^5*(y*d)^2= (2*g/5)*Ω^5*y^2*d^2 := by ring

theorem on_shell_recoil (M m : ℝ) (hm : M≠0) :
 M^2-2*M*((M^2-m^2)/(2*M))=m^2 := by field_simp [hm]; ring

-- Integrated cold two-mode balance, conditional on positive decay of both modes.
theorem receiver_dwell (k g δ x y a b : ℝ) (hk : k≠0) (hg : g≠0)
 (pop : 2*g*b=1) (loss : k*y=1)
 (real_part : k*a= -2*δ*b) (imag_part : g*(x-y)=k*b/2-δ*a) :
 x+y=2/k+(δ^2+k^2/4)/(k*g^2) :=
begin
 have byv : b=1/(2*g) := (eq_div_iff (mul_ne_zero (by norm_num) hg)).2 (by nlinarith),
 have yy : y=1/k := (eq_div_iff hk).2 (by nlinarith),
 have aa : a=(-2*δ*b)/k := (eq_div_iff hk).2 (by nlinarith),
 have xx : x=y+(k*b/2-δ*a)/g,
 { have u : x-y=(k*b/2-δ*a)/g := (eq_div_iff hg).2 (by nlinarith), linarith },
 rw [xx,aa,byv,yy], field_simp [hk,hg], ring
end

theorem cumulative_gravitational_branch (kg k y : ℝ) (hk : k≠0) (h : k*y=1) :
 kg*y=kg/k := by field_simp [hk]; linear_combination kg*h

theorem gram_two_modes (a b c d : ℝ) :
 (a^2+c^2)*(b^2+d^2)-(a*b+c*d)^2=(a*d-b*c)^2 := by ring

theorem no_pure_cross_mediator (aa bb ab : ℝ)
 (positive : ab^2≤aa*bb) (dark : aa=0 ∨ bb=0) : ab=0 :=
begin rcases dark with h|h; rw [h] at positive; nlinarith [sq_nonneg ab] end

theorem indefinite_cross (s : ℝ) (h : s≠0) :
 (0:ℝ)*0-s^2<0 := by nlinarith [sq_pos_of_ne_zero s h]

theorem exact_parallel_projection {R : Type*} [ring R] (p d : R)
 (idempotent : p*p=p) (tangent : p*d+d*p=d) :
 d+(p*d-d*p)*p-p*(p*d-d*p)=0 :=
begin
 have dp2 : d*p*p=d*p := by rw [mul_assoc,idempotent],
 have p2d : p*(p*d)=p*d := by rw [←mul_assoc,idempotent],
 have inner : p*d*p=0,
 { calc p*d*p=(p*d+d*p)*p-d*p : by rw [add_mul,dp2]; abel
   ... = 0 : by rw [tangent,sub_self] },
 rw [sub_mul,mul_sub,dp2,p2d,←mul_assoc p d p,inner],
 calc d+(0-d*p)-(p*d-0)=d-(p*d+d*p) : by abel
 ... = 0 : by rw [tangent,sub_self]
end

theorem parallel_ambiguity {R : Type*} [ring R] (p a b d : R)
 (a_ok : d+a*p-p*a=0) (b_ok : d+b*p-p*b=0) :
 (a-b)*p=p*(a-b) :=
begin
 apply sub_eq_zero.mp,
 calc (a-b)*p-p*(a-b)=(d+a*p-p*a)-(d+b*p-p*b) : by noncomm_ring
 ... = 0 : by rw [a_ok,b_ok,sub_self]
end

theorem mark_common_commutant (hx hy a b : ℂ) (h : hx≠hy)
 (offdiag₁ : hx*a=a*hy) (offdiag₂ : hx*b=b*hy) : a=0 ∧ b=0 :=
begin
 have d : hx-hy≠0 := sub_ne_zero.mpr h,
 have z₁ : (hx-hy)*a=0 := by linear_combination offdiag₁,
 have z₂ : (hx-hy)*b=0 := by linear_combination offdiag₂,
 exact ⟨(mul_eq_zero.mp z₁).resolve_left d,(mul_eq_zero.mp z₂).resolve_left d⟩
end

theorem common_diagonals_equal (u v b : ℂ) (noalign : b≠0) (commutes : u*b=b*v) : u=v :=
begin
 have h : (u-v)*b=0 := by linear_combination commutes,
 exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right noalign)
end

theorem first_jet (g value : ℝ) (on_all : ∀ v d : ℝ, value*v+2*g*d=0) : g=0 :=
by have h:=on_all 0 1; linarith

theorem least_distorting_connection (gap k d z : ℝ) (hk : 0<k) :
 let c := gap^2+k^2, f := gap^2/c in
 gap^2*(d-z)^2+k^2*z^2 - (gap^2*(d-f*d)^2+k^2*(f*d)^2)=c*(z-f*d)^2 :=
begin
 dsimp, have n : gap^2+k^2≠0 := ne_of_gt (by nlinarith [sq_nonneg gap, sq_pos_of_ne_zero k (ne_of_gt hk)]),
 field_simp [n]; ring
end

theorem strict_cost_at_other_point (c z d : ℝ) (hc : 0<c) (hne : z≠d) :
 0<c*(z-d)^2 := mul_pos hc (sq_pos_of_ne_zero _ (sub_ne_zero.mpr hne))

theorem regular_fraction (gap k : ℝ) (hk : 0<k) :
 1-gap^2/(gap^2+k^2)=k^2/(gap^2+k^2) :=
begin
 have n : gap^2+k^2≠0 := ne_of_gt (by nlinarith [sq_nonneg gap,sq_pos_of_ne_zero k (ne_of_gt hk)]),
 field_simp [n]; ring
end

theorem half_trace_line (f r : ℝ) (h : r=1-f) :
 real.cos (real.pi*f)= -real.cos (real.pi*r) :=
begin rw [h, mul_sub,mul_one,real.cos_sub,real.cos_pi,real.sin_pi], ring end

theorem divergent_exact_connection (r M : ℝ) (hr : 0<r) (hm : 2*r*M<1) :
 M<1/(2*r) := (lt_div_iff (by linarith : 0<2*r)).2 (by nlinarith)

theorem weak_regularization (g k r L : ℝ) (hk : 0<k) (hr : 0<r)
 (h : g^2≤L*r^2) :
 g^2/((g^2+k^2)*r) ≤ (L*r)/(k^2) :=
begin
 have kpos : 0<k^2 := sq_pos_of_ne_zero k (ne_of_gt hk),
 have gr : 0<(g^2+k^2)*r := mul_pos (by nlinarith [sq_nonneg g]) hr,
 have Lpos : 0≤L := nonneg_of_mul_nonneg_left
   (le_trans (sq_nonneg _) h) (sq_pos_of_ne_zero _ (ne_of_gt hr)),
 apply (div_le_div_iff gr kpos).2,
 nlinarith only [mul_le_mul_of_nonneg_right h kpos.le,
   mul_nonneg (mul_nonneg Lpos (sq_nonneg r)) (sq_nonneg g)]
end

theorem improved_noether_product (Cdiv C dh field derivative : ℝ) :
 Cdiv*dh+C*derivative-(field*dh+C*derivative)= -(field-Cdiv)*dh := by ring

theorem positive_residue_min (a b c : ℝ) (ha : 0≤a) (hb : 0≤b) (hc : c^2≤a*b) :
 2*|c|≤a+b :=
begin by_cases sign : 0≤c,
 {rw [abs_of_nonneg sign], nlinarith [sq_nonneg (a-b)]},
 {rw [abs_of_neg (lt_of_not_ge sign)], nlinarith [sq_nonneg (a-b)]}
end

theorem saturating_residues (a b c : ℝ) (h : c^2≤a*b) (tr : a+b=2*c) :
 a=c ∧ b=c :=
begin
 have v : b=2*c-a := by linarith,
 by_cases ac : a=c, {exact ⟨ac,by linarith⟩},
 rw [v] at h, exfalso, nlinarith [sq_pos_of_ne_zero (a-c) (sub_ne_zero.mpr ac)]
end

def rad (a s : ℝ) := real.sqrt (1+a*s)
def threshold (a b s : ℝ) := (rad a s-1)*(rad b s-1)

theorem rad_increases (a : ℝ) (ha : 0<a) {x y : ℝ} (hx : 0≤x) (hxy : x<y) :
 rad a x < rad a y :=
real.sqrt_lt_sqrt (by nlinarith [mul_nonneg ha.le hx]) (by nlinarith [mul_lt_mul_of_pos_left hxy ha])

theorem threshold_increases (a b : ℝ) (ha : 0<a) (hb : 0<b) {x y : ℝ}
 (hx : 0≤x) (hxy : x<y) : threshold a b x < threshold a b y :=
begin
 have ax : 1≤rad a x := by {have h:=real.sqrt_le_sqrt (show (1:ℝ)≤1+a*x, by nlinarith [mul_nonneg ha.le hx]),
   simpa [rad] using h},
 have byy : 1<rad b y := by {have h:=rad_increases b hb (le_refl (0:ℝ)) (lt_of_le_of_lt hx hxy),
   simpa [rad] using h},
 have u:=rad_increases a ha hx hxy, have v:=rad_increases b hb hx hxy,
 unfold threshold,
 calc (rad a x-1)*(rad b x-1)≤(rad a x-1)*(rad b y-1) :
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
 ... < (rad a y-1)*(rad b y-1) : mul_lt_mul_of_pos_right (by linarith) (by linarith)
end

theorem unique_threshold (a b : ℝ) (ha : 0<a) (hb : 0<b) :
 ∃! s : ℝ, 0≤s ∧ threshold a b s=2 :=
begin
 let top := max (8/a) (8/b),
 have ta : 8/a≤top := le_max_left _ _,
 have tb : 8/b≤top := le_max_right _ _,
 have ta' := (div_le_iff ha).mp ta, have tb' := (div_le_iff hb).mp tb,
 have tp : 0≤top := le_trans (div_nonneg (by norm_num) ha.le) ta,
 have ra : 3≤rad a top := by {unfold rad, nlinarith [real.sq_sqrt (show 0≤1+a*top, by nlinarith),real.sqrt_nonneg (1+a*top)]},
 have rb : 3≤rad b top := by {unfold rad, nlinarith [real.sq_sqrt (show 0≤1+b*top, by nlinarith),real.sqrt_nonneg (1+b*top)]},
 have large : 2≤threshold a b top := by {unfold threshold,
   nlinarith [mul_nonneg (sub_nonneg.mpr ra) (sub_nonneg.mpr rb)]},
 have small : threshold a b 0=0 := by simp [threshold,rad],
 have ct : continuous (threshold a b) :=
 begin
   change continuous (λ s:ℝ, (real.sqrt (1+a*s)-1)*(real.sqrt (1+b*s)-1)),
   apply continuous.mul; apply continuous.sub; try {exact continuous_const};
   apply real.continuous_sqrt.comp; apply continuous.add; try {exact continuous_const};
   exact continuous_const.mul continuous_id
 end,
 obtain ⟨s,hs,eq⟩:=intermediate_value_Icc tp ct.continuous_on
   (show (2:ℝ)∈set.Icc (threshold a b 0) (threshold a b top), by rw [small]; exact ⟨by norm_num,large⟩),
 refine ⟨s,⟨hs.1,eq⟩,_⟩, rintros y ⟨hy,ey⟩,
 rcases lt_trichotomy y s with l|l|l,
 {have bad:=threshold_increases a b ha hb hy l, rw [ey,eq] at bad, exact (lt_irrefl _ bad).elim},
 {exact l},
 {have bad:=threshold_increases a b ha hb hs.1 l, rw [ey,eq] at bad, exact (lt_irrefl _ bad).elim}
end

def energy_ratio (a s : ℝ) := 2/(1+rad a s)
def slope (u : ℝ) := (u-1)/(u*(u+1))

theorem actual_derivative (a s : ℝ) (ha : 0<a) (hs : 0<s) :
 has_deriv_at (energy_ratio a) (-(slope (rad a s))/s) s :=
begin
 have pos : 0<1+a*s := by nlinarith [mul_pos ha hs],
 have d0 : has_deriv_at (λ t:ℝ,1+a*t) a s,
 { convert ((has_deriv_at_id s).const_mul a).const_add 1 using 1; ring },
 have d1 := d0.sqrt (ne_of_gt pos),
 have hp : 0<real.sqrt (1+a*s) := real.sqrt_pos.mpr pos,
 have hn : 1+real.sqrt (1+a*s)≠0 := ne_of_gt (by linarith),
 have h := (has_deriv_at_const s (2:ℝ)).div (d1.const_add 1) hn,
 convert h using 1,
 have algebra : ∀ (u:ℝ), 0<u → u^2=1+a*s →
   -((u-1)/(u*(u+1)))/s=(0*(1+u)-2*(a/(2*u)))/(1+u)^2,
 { intros u up sq,
   have aa : a=(u-1)*(u+1)/s := (eq_div_iff (ne_of_gt hs)).2 (by nlinarith),
   have n1 : (1+u)≠0 := ne_of_gt (by linarith),
   have n2 : (u+1)≠0 := ne_of_gt (by linarith),
   rw [aa], field_simp [ne_of_gt hs,ne_of_gt up,n1,n2]; ring },
 exact algebra _ hp (real.sq_sqrt pos.le)
end

theorem peak_derivative_sign (u v : ℝ) (hu : 1≤u) (hv : u<v) :
 0<slope v-slope u ↔ (u-1)*(v-1)<2 :=
begin
 have p : 0<u*(u+1) := mul_pos (by linarith) (by linarith),
 have q : 0<v*(v+1) := mul_pos (by linarith) (by linarith),
 rw [sub_pos, slope, slope, div_lt_div_iff p q],
 have s := factor_turnover u v,
 constructor,
 { intro h, have top : 0<(v-u)*(2-(u-1)*(v-1)) := by nlinarith only [s,h],
   have e := pos_of_mul_pos_right top (sub_nonneg.mpr hv.le), linarith },
 { intro h, have e := mul_pos (sub_pos.mpr hv) (sub_pos.mpr h), nlinarith only [e,s] }
end

theorem loop_trig_solution (f θ : ℝ) :
 has_deriv_at (λ t:ℝ, real.cos (f*t/2)) (-(f/2)*real.sin (f*θ/2)) θ ∧
 has_deriv_at (λ t:ℝ, real.sin (f*t/2)) ((f/2)*real.cos (f*θ/2)) θ :=
begin
 have inner := ((has_deriv_at_id θ).const_mul f).div_const 2,
 split, {convert inner.cos using 1; ring}, {convert inner.sin using 1; ring}
end

theorem generic_wave_balance (velocity h dt velocity_dt gradient laplacian flux_div : ℝ)
 (eom : h*velocity_dt+dt*velocity=laplacian)
 (flux : flux_div= -2*velocity*laplacian-2*gradient) :
 2*velocity*h*velocity_dt+dt*velocity^2+2*gradient+flux_div= -dt*velocity^2 :=
by rw [flux]; linear_combination 2*velocity*eom

theorem covariance_filter (d k : ℝ) (hk : 0<k) :
 (k/(k^2+d^2))*k=1-d^2/(d^2+k^2) :=
by rw [regular_fraction d k hk,add_comm]; ring

end overlapping_contacts
