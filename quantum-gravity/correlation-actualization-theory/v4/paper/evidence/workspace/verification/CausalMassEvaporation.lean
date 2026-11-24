import tactic
import analysis.inner_product_space.basic
import analysis.special_functions.improper_integrals
import measure_theory.function.ae_eq_of_integral
import measure_theory.integral.fund_thm_calculus

noncomputable theory
open measure_theory set filter
open_locale big_operators topology

namespace causal_mass_evaporation

/-- The two charges in this section are joint spectral values. The radial
channel requires an actual positive inward receipt on the observer's carrier. -/
def radial (g c : ℝ) : ℝ := if 0 < c ∧ g = c then 1 else 0

theorem exterior_empty_carrier (g : ℝ) : radial g 0 = 0 := by simp [radial]

theorem comoving_open (q : ℝ) (hq : 0 < q) : radial q q = 1 := by simp [radial,hq]

theorem different_charge_closed (g c : ℝ) (h : g ≠ c) : radial g c = 0 := by simp [radial,h]

/-- Orthogonal complement of all carrier time-translation differences.
This is independent of gaps, discretization and any readout duration. -/
theorem invisible_to_carrier {H : Type*} [normed_add_comm_group H] [inner_product_space ℂ H]
    (U : ℝ → H → H) (unitary : ∀ (t:ℝ) (y x:H), @inner ℂ H _ y (U t x) = @inner ℂ H _ (U (-t) y) x)
    (y : H) :
    (∀ (t:ℝ) (x:H), @inner ℂ H _ y (U t x-x)=0) ↔ ∀ t:ℝ, U t y=y :=
begin
 split,
 {intros h t, apply @ext_inner_right ℂ, intro x,
  have eqn := h (-t) x, rw [inner_sub_right,unitary,neg_neg,sub_eq_zero] at eqn, exact eqn},
 {intros h t x,rw [inner_sub_right,unitary,h,sub_self]}
end

theorem conservative_vertex (g c z : ℝ) :
  (radial g c*z)^2+((1-radial g c)*z)^2=z^2 :=
by {unfold radial, split_ifs; ring}

/-- With the outside carrier absent, an arbitrary distribution of geometric
charges, including an atom at zero, has zero inward weight. -/
theorem arbitrary_exterior {α : Type*} [measurable_space α] (μ : measure α)
    (charge density : α → ℝ) : (∫ x, radial (charge x) 0*density x ∂μ)=0 :=
by simp [exterior_empty_carrier]

def formed (w : ℕ → Prop) (n : ℕ) : Prop := ∃ k, k ≤ n ∧ w k

theorem no_interior_before (w : ℕ → Prop) (n : ℕ) (h : ∀ k ≤ n, ¬w k) :
  ¬formed w n := λ ⟨k,hk,hw⟩, h k hk hw

theorem future_first (w : ℕ → Prop) (n : ℕ) (h : ∀ k ≤ n, ¬w k) (hw : w (n+1)) :
  ¬formed w n ∧ formed w (n+1) := ⟨no_interior_before _ _ h,⟨_,le_refl _,hw⟩⟩

theorem past_prefix (w v : ℕ → Prop) (n : ℕ) (h : ∀ k ≤ n, w k ↔ v k) :
  formed w n ↔ formed v n :=
⟨λ ⟨k,hk,hw⟩, ⟨k,hk,(h k hk).mp hw⟩, λ ⟨k,hk,hv⟩, ⟨k,hk,(h k hk).mpr hv⟩⟩

theorem separated_vacuum {H : Type*} [normed_add_comm_group H]
  (K : H → H) (vac : H) (hs : K vac = 0 → ∀ x, K x = 0)
  (hz : ‖K vac‖^2 = 0) : ∀ x, K x = 0 :=
hs (norm_eq_zero.mp (pow_eq_zero hz))

theorem spherical_charge (r g c m f : ℝ) (hg : g ≠ 0) (hc : c ≠ 0) (hr : r ≠ 0)
    (h : f = 1-2*g*m/(c^2*r)) : r*c^2*(1-f)/(2*g)=m :=
by {rw [h], field_simp; ring}

theorem dust_time (s v t : ℝ) (hv : 0 < v) (h : s=3*v*t/2) : t=2*s/(3*v) :=
by {rw [h], field_simp [hv.ne']; ring}

theorem mass_plateau (r a b : ℝ) (ha : a ≠ b) (hr : r ≠ 0) :
    (b/r^3-a/r^3)*r^3=b-a :=
by {field_simp; ring}

theorem brown_york_gap (k lo hi delta : ℝ) (hs : lo+hi ≠ 0)
  (h : k*(lo^2-hi^2)=2*delta) : k*(lo-hi)=2*delta/(lo+hi) :=
by {apply (eq_div_iff hs).mpr, nlinarith only [h]}

/-- Product rule for the area of a twist-free affine null pencil. F is the
Einstein null source including its conversion factor, and s is shear squared. -/
theorem null_pencil (A θ : ℝ → ℝ) (t s F : ℝ)
  (ha : has_deriv_at A (A t*θ t) t)
  (hθ : has_deriv_at θ (-(θ t)^2/2-s-F) t) :
  has_deriv_at (λ u:ℝ,A u*θ u) (A t*((θ t)^2/2-s)-A t*F) t :=
by {convert ha.mul hθ using 1; ring}

theorem received_null_flux (A θ s F : ℝ → ℝ) (lo hi : ℝ)
  (ha : ∀ t ∈ uIcc lo hi, has_deriv_at A (A t*θ t) t)
  (hθ : ∀ t ∈ uIcc lo hi, has_deriv_at θ (-(θ t)^2/2-s t-F t) t)
  (hi1 : interval_integrable (λ u:ℝ,A u*((θ u)^2/2-s u)) volume lo hi)
  (hi2 : interval_integrable (λ u:ℝ,A u*F u) volume lo hi) :
  (∫ u in lo..hi,A u*F u)=A lo*θ lo-A hi*θ hi+
    ∫ u in lo..hi,A u*((θ u)^2/2-s u) :=
begin
 have eqn := interval_integral.integral_eq_sub_of_has_deriv_at
   (λ (x:ℝ) (hx:x∈uIcc lo hi), @null_pencil A θ x (s x) (F x) (ha x hx) (hθ x hx)) (hi1.sub hi2),
 rw [interval_integral.integral_sub hi1 hi2] at eqn,
 dsimp only at eqn,
 linarith
end

theorem finite_front_cone (angle time d b : ℝ) (ha : angle≤time)
  (ht : time≤d/b) : angle≤d/b := le_trans ha ht

theorem launch_sufficient (d b lag travel front : ℝ) (hb : 0<b)
  (h1 : travel ≤ d/(1+b)) (h2 : d ≤ front)
  (h3 : lag < d*b/(1+b)) : lag+travel<front :=
begin
  have pos : 0<1+b := by linarith,
  have eqn : d*b/(1+b)+d/(1+b)=d := by {field_simp [pos.ne']; ring},
  linarith
end

theorem launch_necessary (d b lag travel front : ℝ) (h1 : d/2 ≤ travel)
  (h2 : front ≤ d/b) (h3 : lag+travel<front) : lag<d/b-d/2 := by linarith

def exchange (A y x : ℝ) : ℝ := y*(A*y+2*x)

theorem coherent_difference (X j : ℝ) : (X+j)^2-X^2=j^2+2*j*X := by ring

theorem exchange_zero_fibre (A y : ℝ) (hy : y ≠ 0) :
    {x : ℝ | exchange A y x=0} = {-(A*y)/2} :=
begin
 ext x, simp only [set.mem_set_of_eq,set.mem_singleton_iff,exchange,mul_eq_zero],
 split,
 {intro h, have h' := h.resolve_left hy,linarith},
 {intro h,right,linarith}
end

/-- The quadrature on each nonempty material fibre may have a different
atomless law. No assumption of independence between field and matter. -/
theorem vacuum_fibre_only (A : ℝ) (ν : measure ℝ) (μ : ℝ → measure ℝ)
    (hμ : ∀ y x : ℝ, μ y {x}=0) :
  (∫⁻ y, μ y {x : ℝ | exchange A y x=0} ∂ν)
    =∫⁻ y, (if y=0 then μ y univ else 0) ∂ν :=
begin
 apply lintegral_congr, intro y, by_cases h : y=0,
 {subst y, simp [exchange]},
 {rw [if_neg h,exchange_zero_fibre _ _ h,hμ]}
end

/-- Dipole squared projected electric field, after isotropic angular averaging:
trace = 2, and the component along the chosen light direction is (3+z^2)/5. -/
theorem even_quartic_mean (a b d : ℝ) :
 (∫ u in (-1:ℝ)..1, a+b*u^2+d*u^4)/2 = a+b/3+d/5 :=
begin
 have hd : ∀ c:ℝ, has_deriv_at (λ u:ℝ, a*u+b*(u^3/3)+d*(u^5/5)) (a+b*c^2+d*c^4) c,
 {intro c, convert (((has_deriv_at_id c).const_mul a).add
  (((has_deriv_at_pow 3 c).div_const 3).const_mul b)).add
  (((has_deriv_at_pow 5 c).div_const 5).const_mul d) using 1;norm_num;ring},
 rw [interval_integral.integral_eq_sub_of_has_deriv_at (λ t ht,hd t)
    (show interval_integrable (λ u:ℝ,a+b*u^2+d*u^4) volume (-1) 1,
     from (show continuous (λ u:ℝ,a+b*u^2+d*u^4),by continuity).interval_integrable _ _)];ring
end

theorem dipole_sphere (z : ℝ) :
 (∫ u in (-1:ℝ)..1, 1-z^2+(3-9*u^2)*(z^2*u^2+(1-z^2)*(1-u^2)/2)+6*z^2*u^2)/2=(7-z^2)/5 :=
begin
 have h : (λ u:ℝ, 1-z^2+(3-9*u^2)*(z^2*u^2+(1-z^2)*(1-u^2)/2)+6*z^2*u^2)=
          (λ u:ℝ,5*(1-z^2)/2+(15*z^2-6)*u^2+((9-27*z^2)/2)*u^4) := funext (λ u,by ring),
 rw [h,even_quartic_mean]; ring
end

theorem vacuum_pair_angle :
  (∫ u in (-1:ℝ)..1, (1-u^2)^2)/2=8/15 :=
begin
 have h : (λ u:ℝ,(1-u^2)^2)=(λ u:ℝ,1+(-2)*u^2+1*u^4) := funext (λ u,by ring),
 rw [h,even_quartic_mean];norm_num
end

theorem neutral_orientation (z : ℝ) (h : |z|≤1) :
  2-(3+z^2)/5=(7-z^2)/5 ∧ 6/5≤(7-z^2)/5 ∧ (7-z^2)/5≤7/5 :=
begin
 have b := abs_le.mp h,
 have pos := mul_nonneg (sub_nonneg.mpr b.2) (show 0≤1+z,by linarith [b.1]),
 split,{ring},split; nlinarith [sq_nonneg z]
end

theorem flatten_small_window (x eps : ℝ) (he : 0≤eps) :
    |(if |x|≤eps then (0:ℝ) else x)-x|≤eps :=
by {split_ifs with h; simp [h,he]}

def spin_det (d a b x z : ℝ) : ℝ := (d+2*a*x)*(d-2*a*x)-(2*b*z)^2

theorem spin_conic_roots (d a b x z w : ℝ) (hb : b≠0)
   (hz : spin_det d a b x z=0) (hw : spin_det d a b x w=0) : z=w ∨ z= -w :=
begin
 unfold spin_det at hz hw,
 have eqn : (4*b^2)*((z-w)*(z+w))=0 := by nlinarith only [hz,hw],
 have nonzero : (4:ℝ)*b^2≠0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hb),
 rcases mul_eq_zero.mp ((mul_eq_zero.mp eqn).resolve_left nonzero) with h|h,
 {exact or.inl (sub_eq_zero.mp h)}, {right,linarith}
end

theorem spin_source_kernel (d a b x : ℝ) (hb : b≠0) (μ : measure ℝ)
    (atomless : ∀ z:ℝ, μ {z}=0) : μ {z:ℝ | spin_det d a b x z=0}=0 :=
begin
 by_cases exists_root : ∃ z:ℝ, spin_det d a b x z=0,
 {rcases exists_root with ⟨w,hw⟩,
  have hs : {z:ℝ | spin_det d a b x z=0} ⊆ ({w}:set ℝ) ∪ {-w} :=
   λ z hz, by simpa only [set.mem_union,set.mem_singleton_iff] using spin_conic_roots d a b x z w hb hz hw,
  have he : μ (({w}:set ℝ) ∪ {-w}) ≤ μ {w}+μ {-w} := measure_union_le _ _,
  rw [atomless,atomless,zero_add] at he,
  exact measure_mono_null hs (le_antisymm he (zero_le _))},
 {have hn : {z:ℝ | spin_det d a b x z=0}=∅ :=
   set.eq_empty_iff_forall_not_mem.mpr (λ z hz,exists_root ⟨z,hz⟩),
  rw [hn,measure_empty]}
end

theorem inactive_exchange (A x : ℝ) : exchange A 0 x=0 := by simp [exchange]

theorem pair_angle_moment : (1:ℝ)-2/3+1/5=8/15 := by norm_num

theorem optical_energy_ratio (m p factor : ℝ) (hm : m≠0) (hf : factor≠0) :
  (p^2/(factor*m))/m=(p/m)^2/factor := by {field_simp [hm,hf];ring_nf;simp}

theorem meter_center (v lo hi : ℝ) (h : lo ≤ v) (h' : v ≤ hi) :
    |v-(lo+hi)/2| ≤ (hi-lo)/2 :=
by {apply abs_le.mpr, split; linarith}

theorem irrep_off_diagonal (m n a : ℂ) (h : m ≠ n) (hz : m*a=n*a) : a=0 :=
begin
 have eqn : (m-n)*a=0 := by rw [sub_mul,hz,sub_self],
 exact (mul_eq_zero.mp eqn).resolve_left (sub_ne_zero.mpr h)
end

theorem irrep_ladder (a c : ℕ → ℂ) (n : ℕ) (hc : ∀ k<n,c k≠0)
  (h : ∀ k<n,c k*a (k+1)=c k*a k) : ∀ m ≤ n, a m=a 0 :=
begin
 intro m, induction m with m ih, {intro hm, refl},
 intro hm, have step : m<n := nat.lt_of_succ_le hm,
 exact (mul_left_cancel₀ (hc m step) (h m step)).trans (ih (le_of_lt step))
end

/-- Triangle inequality in the environment of any trace-preserving recovery.
The vectors are its diagonal amplitudes, of norm at most one. -/
theorem flagged_bound {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
    {ι : Type*} (s : finset ι) (w : ι → ℝ) (v : ι → E) (hw : ∀ i∈s, 0≤w i)
    (hv : ∀ i∈s, ‖v i‖ ≤ 1) : ‖∑ i in s, w i • v i‖ ≤ ∑ i in s, w i :=
begin
  apply le_trans (norm_sum_le _ _),
  apply finset.sum_le_sum, intros i hi, rw [norm_smul,real.norm_eq_abs,abs_of_nonneg (hw i hi)],
  simpa using mul_le_mul_of_nonneg_left (hv i hi) (hw i hi)
end

theorem polar_center (a b : ℝ) :
  (∫ u in a..b, 3*u^2/2)=(b^3-a^3)/2 :=
begin
 have hd : ∀ c:ℝ, has_deriv_at (λ u:ℝ,u^3/2) (3*c^2/2) c,
 {intro c, convert (has_deriv_at_pow 3 c).div_const 2 using 1; norm_num},
 rw [interval_integral.integral_eq_sub_of_has_deriv_at (λ c hc,hd c)
  (show interval_integrable (λ u:ℝ,3*u^2/2) volume a b,
   from (show continuous (λ u:ℝ,3*u^2/2),by continuity).interval_integrable _ _)]; ring
end

theorem polar_side (a b : ℝ) :
  (∫ u in a..b, 3*(1-u^2)/4)=3*(b-a)/4-(b^3-a^3)/4 :=
begin
 have hd : ∀ c:ℝ, has_deriv_at (λ u:ℝ,(3*u-u^3)/4) (3*(1-c^2)/4) c,
 {intro c, convert (((has_deriv_at_id c).const_mul 3).sub (has_deriv_at_pow 3 c)).div_const 4 using 1;
  norm_num; ring},
 rw [interval_integral.integral_eq_sub_of_has_deriv_at (λ c hc,hd c)
  (show interval_integrable (λ u:ℝ,3*(1-u^2)/4) volume a b,
   from (show continuous (λ u:ℝ,3*(1-u^2)/4),by continuity).interval_integrable _ _)]; ring
end

theorem polar_overlap_integral : (∫ u in (0:ℝ)..1, real.sqrt (1-u^2)*(2*u))=2/3 :=
begin
 have hd : ∀ x ∈ uIcc (0:ℝ) 1, has_deriv_at (λ t:ℝ,t^2) (2*x) x :=
  λ x hx,by {convert has_deriv_at_pow 2 x using 1;norm_num},
 have sub := interval_integral.integral_comp_mul_deriv hd
   (show continuous (λ x:ℝ,2*x),by continuity).continuous_on
   (show continuous (λ x:ℝ,real.sqrt (1-x)),from real.continuous_sqrt.comp (continuous_const.sub continuous_id)),
 have change : (∫ u in (0:ℝ)..1, real.sqrt (1-u^2)*(2*u))=∫ z in (0:ℝ)..1,real.sqrt z :=
   by simpa [function.comp,interval_integral.integral_comp_sub_left] using sub,
 rw [change], simp_rw [real.sqrt_eq_rpow],
 rw [integral_rpow (or.inl (by norm_num : (-1:ℝ)<1/2))],
 norm_num [real.zero_rpow]
end

/-- Emission histories can be composed without measuring the reference. -/
theorem scale_on_chain {E F G : Type*} [has_inner ℂ E] [has_inner ℂ F] [has_inner ℂ G]
  (V : E → F) (W : F → G) (p q : ℂ)
  (hv : ∀ x y, @inner ℂ F _ (V x) (V y)=p*@inner ℂ E _ x y)
  (hw : ∀ x y, @inner ℂ G _ (W x) (W y)=q*@inner ℂ F _ x y) (x y : E) :
    @inner ℂ G _ (W (V x)) (W (V y))=(q*p)*@inner ℂ E _ x y :=
by rw [hw,hv,mul_assoc]

theorem exp_waiting (a : ℝ) (ha : 0<a) :
    (∫ t in Ioi (0:ℝ), real.exp (-(a*t)))=a⁻¹ :=
begin
 have h := integral_comp_mul_left_Ioi (λ t:ℝ, real.exp (-t)) 0 ha,
 simpa [abs_of_pos (inv_pos.mpr ha),smul_eq_mul,integral_exp_neg_Ioi_zero] using h
end

theorem waiting_overlap (a b : ℝ) (ha : 0<a) (hb : 0<b) :
  (∫ t in Ioi (0:ℝ), real.sqrt (a*b)*real.exp (-(((a+b)/2)*t)))
       = 2*real.sqrt (a*b)/(a+b) :=
begin
 have h : 0 < (a+b)/2 := by linarith,
 rw [integral_mul_left,exp_waiting _ h], field_simp [h.ne', (add_pos ha hb).ne']; ring
end

theorem equal_width_only (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    2*real.sqrt (a*b)/(a+b)=1 ↔ a=b :=
begin
 have hs : 0 < a+b := by linarith,
 have sq := real.sq_sqrt (mul_pos ha hb).le,
 split,
 {intro h, have h' := (div_eq_iff hs.ne').mp h,
  rw [one_mul] at h',
  have hsq : (2*real.sqrt (a*b))^2=(a+b)^2 := congr_arg (λ x:ℝ,x^2) h',
  have hh : (a-b)^2=0 := by nlinarith only [sq,hsq],
  linarith [pow_eq_zero hh]},
 {intro h, subst b, rw [←pow_two,real.sqrt_sq_eq_abs,abs_of_pos ha],
  apply (div_eq_iff hs.ne').mpr, ring}
end

/-- Norm transfer for any continuous input density, with no restriction to
a finite angular or radial basis. Time here increases from the final end. -/
theorem smooth_area_transfer (x dx ρ : ℝ → ℝ) (a b : ℝ)
    (hd : ∀ t ∈ uIcc a b, has_deriv_at x (dx t) t)
    (hc : continuous_on dx (uIcc a b)) (hρ : continuous ρ) :
    (∫ t in a..b, (ρ ∘ x) t*dx t)=∫ w in x a..x b, ρ w :=
interval_integral.integral_comp_mul_deriv hd hc hρ

theorem cubic_transfer (ρ : ℝ → ℝ) (hρ : continuous ρ) :
  (∫ t in (0:ℝ)..1, ρ (t^3)*(3*t^2))=∫ z in (0:ℝ)..1, ρ z :=
begin
 have hd : ∀ t ∈ uIcc (0:ℝ) 1, has_deriv_at (λ y:ℝ,y^3) (3*t^2) t :=
 λ t ht, by {convert has_deriv_at_pow 3 t using 1; norm_num},
 simpa [function.comp] using smooth_area_transfer (λ t:ℝ,t^3) (λ t:ℝ,3*t^2) ρ 0 1 hd
   (show continuous (λ t:ℝ,3*t^2),by continuity).continuous_on hρ
end

/-- Cross term in the energy of a time-limited packet. Integral of z^-2,
after z=sqrt(x), exhibits the divergence at the Hawking endpoint. -/
theorem exterior_energy_kernel (u U : ℝ) (hu : u<U) :
  (∫ v in Ioi U, (v-u)⁻¹^2)=(U-u)⁻¹ :=
begin
 have hd : ∀ (v:ℝ), v∈Ici U → has_deriv_at (λ w:ℝ,-(w-u)⁻¹) ((v-u)⁻¹^2) v,
 {intros v hv, have h : v-u≠0 := (sub_pos.mpr (lt_of_lt_of_le hu hv)).ne',
  convert (((has_deriv_at_id v).sub_const u).inv h).neg using 1; simp [pow_two,one_div,div_eq_mul_inv]},
 have ht : tendsto (λ v:ℝ,v-u) at_top at_top :=
   by simpa [sub_eq_add_neg] using tendsto_at_top_add_const_right at_top (-u) (tendsto_id : tendsto id at_top at_top),
 have hg : tendsto (λ v:ℝ,-(v-u)⁻¹) at_top (𝓝 (0:ℝ)) :=
   by simpa [function.comp_app] using (tendsto_inv_at_top_zero.comp ht).neg,
 have h := integral_Ioi_of_has_deriv_at_of_nonneg' hd (λ v hv,sq_nonneg _) hg,
 simpa using h
end

theorem cutoff_energy (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    (∫ z in a..b, z⁻¹^2)=a⁻¹-b⁻¹ :=
begin
 have hh : ∀ (z:ℝ), z ∈ uIcc a b → z≠0 :=
  λ z hz, (lt_of_lt_of_le ha ((by rwa [uIcc_of_le hab] at hz : z∈Icc a b).1)).ne',
 have hd : ∀ z ∈ uIcc a b, has_deriv_at (λ u:ℝ,-u⁻¹) (z⁻¹^2) z,
 {intros z hz, convert (has_deriv_at_inv (hh z hz)).neg using 1; simp [pow_two]},
 have hc : continuous_on (λ z:ℝ,z⁻¹^2) (uIcc a b) :=
   (continuous_on_inv₀.mono (λ z hz,hh z hz)).pow 2,
 rw [interval_integral.integral_eq_sub_of_has_deriv_at hd hc.interval_integrable],ring
end

theorem cubic_energy_example :
  (∫ y in (0:ℝ)..1,9*(1-4*y^3)^2)=81/7 :=
begin
 have hd : ∀ c:ℝ, has_deriv_at (λ y:ℝ,9*(y-2*y^4+16*y^7/7)) (9*(1-4*c^3)^2) c,
 {intro c, convert (((has_deriv_at_id c).sub ((has_deriv_at_pow 4 c).const_mul 2)).add
                    (((has_deriv_at_pow 7 c).const_mul 16).div_const 7)).const_mul 9 using 1;
  norm_num; ring},
 rw [interval_integral.integral_eq_sub_of_has_deriv_at (λ t ht,hd t)
  (show interval_integrable (λ y:ℝ,9*(1-4*y^3)^2) volume 0 1,
  from (show continuous (λ y:ℝ,9*(1-4*y^3)^2),by continuity).interval_integrable _ _)];norm_num
end

end causal_mass_evaporation
