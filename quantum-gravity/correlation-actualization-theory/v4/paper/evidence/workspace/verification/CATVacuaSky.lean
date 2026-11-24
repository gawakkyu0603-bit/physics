import tactic
import analysis.normed_space.basic
import analysis.inner_product_space.basic
import data.fintype.card
import data.nat.choose.basic
import analysis.calculus.inverse

noncomputable theory
open_locale big_operators
namespace cat_vacua_sky

-- Density sqrt(|g|) with the sphere volume element factored out.
theorem probe_metric (v r : ℝ) (hv : v≠0) (hr : r≠0) :
 (v*r^2)/(-(v*r^2))= -1 ∧ (v*r^2)/(r^2/v)=v^2 ∧ (v*r^2)/v=r^2 :=
by split; try {split}; field_simp [hv,hr]; ring

theorem determinant_density (v r : ℝ) :
 (-(v*r^2))*(r^2/v)*v^2= -(v*r^2)^2 :=
by by_cases hv:v=0; [simp [hv], field_simp [hv]]; ring

theorem turning_curvature (h : ℝ) : 2+2*(h^2-2)=2*h^2-2 := by ring

theorem curvature_injective (h k : ℝ) (hh : 0<h) (hk : 0<k)
 (same : 2*h^2-2=2*k^2-2) : h=k :=
begin
 have z : (h-k)*(h+k)=0 := by nlinarith only [same],
 exact sub_eq_zero.mp ((mul_eq_zero.mp z).resolve_right (ne_of_gt (add_pos hh hk)))
end

-- Holonomies of each inverted translation in a one-dimensional unitary character.
theorem sign_holonomy (z : ℂ) : z^2=1 ↔ z=1 ∨ z= -1 :=
begin
 split,
 {intro h, have p : (z-1)*(z+1)=0 := by linear_combination h,
  rcases mul_eq_zero.mp p with a|a,
  {exact or.inl (sub_eq_zero.mp a)}, {right, linear_combination a}},
 {rintro (rfl|rfl); norm_num}
end

theorem glide_generator (coordinate w : ℤ) : coordinate=2*w ↔ coordinate-2*w=0 :=
by exact sub_eq_zero.symm

theorem sign_components : fintype.card (fin 4 → bool)=16 := by norm_num [fintype.card_fun]

-- The covering-space flux periods are even. In the unit orthonormal cube
-- N_flux=4*norm2, so an O3 charge of 16 leaves exactly this norm budget.
theorem tadpole_budget (s d : ℤ) (charge : 2*s+d=16) : 0≤d ↔ s≤8 := by omega

-- Partition all configurations by the number (0,1,2) of coordinates of size two.
theorem covering_isd_count :
 (∑ k in finset.range 9, nat.choose 20 k * 2^k) +
 40*(∑ k in finset.range 5, nat.choose 19 k * 2^k) +4*nat.choose 20 2=48055489 :=
by norm_num [finset.sum_range_succ, nat.choose_eq_desc_factorial_div_factorial,
             nat.desc_factorial, nat.factorial]

structure jet :=
(a b c d e : ℕ)
def conv (x y : jet) : jet :=
 ⟨x.a*y.a,x.a*y.b+x.b*y.a,x.a*y.c+x.b*y.b+x.c*y.a,
 x.a*y.d+x.b*y.c+x.c*y.b+x.d*y.a,
 x.a*y.e+x.b*y.d+x.c*y.c+x.d*y.b+x.e*y.a⟩

-- Coefficients up through squared norm eight. Terms at odd norms vanish.
theorem primitive_coefficients :
 let a : jet := ⟨1,12,6,24,12⟩, b : jet := ⟨1,2,0,0,2⟩,
     b2 := conv b b, b3 := conv b b2, x := conv (conv a a) (conv b3 b3) in
 x.a=1 ∧ x.b=36 ∧ x.c=504 ∧ x.d=3664 ∧ x.e=16392 ∧
 x.a+x.b+x.c+x.d+x.e=20597 := by norm_num [conv]

theorem orbit_total : (1+2+9+27+76 : ℕ)=115 := by norm_num

-- W along a line in the period matrix and axiodilaton is at most quartic.
theorem quartic_difference (a b c d e : ℂ) :
 let p := λ t : ℂ, a+b*t+c*t^2+d*t^3+e*t^4 in
 -p (-2)+16*p (-1)-30*p 0+16*p 1-p 2=24*c := by dsimp; ring

theorem isolated_flux_critical_point {E : Type*} [normed_add_comm_group E]
 [normed_space ℂ E] [complete_space E] (f : E → E) (a : E) (H : E ≃L[ℂ] E)
 (slope : has_strict_fderiv_at f (H : E →L[ℂ] E) a) (critical : f a=0) :
 ∃s : set E, is_open s ∧ a∈s ∧ ∀x∈s, f x=0 → x=a :=
begin
 let g := slope.to_local_homeomorph f,
 have ha : a ∈ g.source := slope.mem_to_local_homeomorph_source,
 refine ⟨g.source,g.open_source,ha,_⟩,
 intros x hx hz,
 exact g.inj_on hx ha (show f x=f a, by rw [hz,critical])
end

theorem flux_full_rank_total : (1+7+41 : ℕ)=49 := by norm_num

-- If every physical output intertwines a conserved spectral projector, an
-- eigenvector in its one-dimensional range can only acquire a scalar.
theorem isolated_ground_preserved {V : Type*} [add_comm_group V] [module ℂ V]
 (P K : V →ₗ[ℂ] V) (v : V) (fixed : P v=v)
 (intertwines : ∀w, P (K w)=K (P w))
 (simple : ∀w, P w=w → ∃c : ℂ, w=c • v) : ∃c : ℂ, K v=c • v :=
simple (K v) (by rw [intertwines,fixed])

theorem two_charge_stationary (a b : ℂ) :
 ‖a‖*‖b‖=0 ↔ a=0 ∨ b=0 := by simp only [mul_eq_zero,norm_eq_zero]

-- Orthogonal components of the actual branch after the two successive
-- projectors. No commutation between the vacuum and contact projectors.
theorem contact_and_write_budget {H : Type*} [normed_add_comm_group H] [inner_product_space ℂ H]
 (v pass sent stay drift : H) (first : v=pass+sent) (second : pass=stay+drift)
 (orth1 : @inner ℂ H _ pass sent=0) (orth2 : @inner ℂ H _ stay drift=0) :
 ‖v‖^2-‖stay‖^2=‖sent‖^2+‖drift‖^2 :=
begin
 have p := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero pass sent orth1,
 have q := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero stay drift orth2,
 rw [←first] at p, rw [←second] at q, linarith
end

theorem contact_zero_cost {ι : Type*} (s : finset ι) (cost : ι → ℝ)
 (hn : ∀i∈s, 0≤cost i) :
 (∑ i in s, cost i)=0 ↔ ∀i∈s, cost i=0 :=
finset.sum_eq_zero_iff_of_nonneg hn

-- Propagating a value around each closed path must return it to itself.
theorem triangle_consistency {X : Type*} (a b c : X → X) (x : X) :
 (∃y z, y=a x ∧ z=b y ∧ x=c z) ↔ c (b (a x))=x :=
begin
 split,
 {rintro ⟨y,z,hy,hz,hx⟩, rw [hy] at hz, rw [hz] at hx, exact hx.symm},
 {intro h, exact ⟨a x,b (a x),rfl,rfl,h.symm⟩}
end

theorem one_contact_reflection (x y : ℂ) :
 (x,-y)=(x,y) ↔ y=0 :=
begin
 split, {intro h, have t : -y=y := congr_arg prod.snd h, linear_combination -(1/2:ℂ)*t},
 {rintro rfl, simp}
end

theorem two_contact_reflections (x y : ℂ) :
 ((x,-y)=(x,y) ∧ (-x,y)=(x,y)) ↔ x=0 ∧ y=0 :=
begin
 split,
 {rintro ⟨a,b⟩, refine ⟨_,(one_contact_reflection x y).mp a⟩,
  have t : -x=x := congr_arg prod.fst b, linear_combination -(1/2:ℂ)*t},
 {rintro ⟨rfl,rfl⟩, simp}
end

theorem uniform_ground (x y : ℤ) : x^2+y^2=0 ↔ x=0 ∧ y=0 :=
begin
 split, {intro h, constructor,
  {exact pow_eq_zero (show x^2=0, by linarith only [h,sq_nonneg y,sq_nonneg x])},
  {exact pow_eq_zero (show y^2=0, by linarith only [h,sq_nonneg x,sq_nonneg y])}},
 {rintro ⟨rfl,rfl⟩,norm_num}
end

theorem harmonic_weights (p e n : ℝ) (total : p+e+n=1) (hp : 0≤p) (he : 0≤e)
 (hn : 0≤n) : 0≤p ∧ p≤p+e ∧ p+e≤1 ∧ (p+e)-p=e ∧ 1-(p+e)=n :=
by repeat {split}; linarith

theorem harmonic_energy (n p : ℝ) : n+n-2*n*p=2*n*(1-p) := by ring

theorem relative_flux_distance (g p rg rp : ℝ) (h : rg^2*g=1) (j : rp^2*p=1)
 (nonzero : rp≠0) (gpos : g≠0) : (rg/rp)^2=p/g :=
begin
 rw [div_pow],
 apply (div_eq_div_iff (pow_ne_zero 2 nonzero) gpos).2,
 rw [h,mul_comm p,j]
end

-- On an open ball inside the physical preparation space, exact zero defect
-- forces the entire linear defect amplitude to vanish, even for noncommuting observers.
theorem robust_zero {H K : Type*} [normed_add_comm_group H] [normed_space ℝ H]
 [normed_add_comm_group K] [normed_space ℝ K] (f : H →ₗ[ℝ] K)
 (v : H) (r : ℝ) (hr : 0<r) (empty : ∀w, ‖w-v‖<r → f w=0) : ∀x, f x=0 :=
begin
 intro x, have base : f v=0 := empty v (by simpa using hr),
 let t:=r/(2*(1+‖x‖)),
 have den : 0<2*(1+‖x‖) := by nlinarith [norm_nonneg x],
 have ht: 0<t := div_pos hr den,
 have prod : t*(2*(1+‖x‖))=r := div_mul_cancel _ den.ne',
 have small : ‖(v+t • x)-v‖<r,
 {rw [add_sub_cancel',norm_smul,real.norm_eq_abs,abs_of_pos ht],
  nlinarith only [prod,ht,mul_nonneg ht.le (norm_nonneg x)]},
 have z:=empty (v+t • x) small, rw [map_add,map_smul,base,zero_add] at z,
 exact (smul_eq_zero.mp z).resolve_left ht.ne'
end

theorem phase_independent_error {H K : Type*} [add_comm_group H] [module ℝ H]
 [normed_add_comm_group K] [normed_space ℝ K] (f : H →ₗ[ℝ] K)
 (v e : H) (a b : ℝ) (clear : f v=0) :
 ‖f (a • v+b • e)‖^2=b^2*‖f e‖^2 :=
by rw [map_add,map_smul,map_smul,clear,smul_zero,zero_add,norm_smul,mul_pow,real.norm_eq_abs,sq_abs]

theorem helicity_gram (u v : ℝ) :
 (u+v)^2-(v-u)^2=4*u*v := by ring

theorem two_graviton_rank (c : ℝ) (lo : -1<c) (hi : c<1) :
 0 < ((1-c)^4+(1+c)^4)^2-((1+c)^4-(1-c)^4)^2 :=
begin
 rw [helicity_gram],
 exact mul_pos (mul_pos (by norm_num) (pow_pos (sub_pos.mpr hi) _)) (pow_pos (by linarith) _)
end

theorem angular_overlap_numerator (c : ℝ) :
 (1+c)^4-(1-c)^4=8*c*(1+c^2) := by ring

theorem right_angle_and_collinear :
 ((1+(0:ℝ))^4-(1-0)^4)=0 ∧ ((1+(-1:ℝ))^4)=0 ∧ ((1-(1:ℝ))^4)=0 := by norm_num

theorem recoiling_mass_shell (M m w c : ℝ)
 (conserve : (M-2*w)^2=m^2+2*w^2*(1+c)) :
 2*(1-c)*w^2-4*M*w+(M^2-m^2)=0 := by nlinarith only [conserve]

end cat_vacua_sky
