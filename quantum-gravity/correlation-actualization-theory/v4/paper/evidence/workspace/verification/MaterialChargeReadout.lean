import tactic
import data.complex.basic
import analysis.inner_product_space.basic
import analysis.specific_limits.basic
import algebra.geom_sum

noncomputable theory
open filter finset
open_locale big_operators
namespace material_charge_readout

-- Finite material charges and the exact two-site interchange.
theorem swap_sector {α : Type*} (a b : α) (h : a ≠ b) :
 (a,b) ≠ (b,a) := λ e, h (congr_arg prod.fst e)

theorem swap_load (a b : ℝ) (e : ℝ → ℝ) : e a + e b = e b + e a := add_comm _ _
theorem anchor_mixture (a b c d : ℝ) :
 a*c+b*d-(a*d+b*c)=(a-b)*(c-d) := by ring
theorem swap_plus_minus (x y : ℝ) :
 ((x+y)/2-(x-y)/2,(x+y)/2+(x-y)/2)=(y,x) := by {apply prod.ext, all_goals {dsimp,ring}}
theorem charge_sum (q₁ q₂ : ℤ) : q₁+q₂=q₂+q₁ := add_comm _ _
-- Jacobi equation in X=sqrt(r/r_i): X²h''-2Xh'-4h=0.
-- h=(X^4+4/X)/5; both initial conditions are in the following statements.
theorem jacobi_equation (x : ℝ) (hx : x ≠ 0) :
 x^2*((12*x^2+8/x^3)/5)-2*x*((4*x^3-4/x^2)/5)-4*((x^4+4/x)/5)=0 :=
by {field_simp [hx],ring}
theorem jacobi_initial : (((1:ℝ)^4+4/1)/5,(4*(1:ℝ)^3-4/1^2)/5)=(1,0) := by norm_num
theorem elastic_envelope (Y a b : ℝ) (h : Y≤a+b*Y) (hb : b<1) :
 Y≤a/(1-b) := (le_div_iff (by linarith : 0<1-b)).2 (by nlinarith)

-- Four-momentum after removing one null quantum in the parent rest frame.
theorem recoil_mass (m w : ℝ) : (m-w)^2-w^2=m^2-2*m*w := by ring
theorem recoil_fraction (m x : ℝ) : m^2-2*m*(m*x/2)=m^2*(1-x) := by ring
theorem entropy_cost (m x j : ℝ) :
 4*(m^2*(1-j*x)-m^2)= -4*m^2*j*x := by ring
theorem fourth_mass_drift (x m : ℝ) :
 m^4-(m^2*(1-x))^2=m^4*(2*x-x^2) := by ring
theorem finite_rare_bound (u d b k : ℝ) (hd : 0<d) (h : d*u≤b)
 (hb : b≤k) : u≤k/d := (le_div_iff hd).2 (by linarith [mul_comm d u])
-- Bellman supersolution for any finite horizon and any distribution of the next mass.
theorem rare_induction (mark stay future moment v C δ : ℝ)
 (hs : 0≤stay) (hc : 0≤C) (hf : future≤C*moment)
 (hd : stay*moment≤(1-δ)*v) (hb : mark≤C*δ*v) :
 mark+stay*future≤C*v :=
begin
 have h₁ := mul_le_mul_of_nonneg_left hf hs,
 have h₂ := mul_le_mul_of_nonneg_left hd hc,
 nlinarith only [hb,h₁,h₂]
end
theorem finite_horizon_majorant {ι : Type*} (P : ℕ → ι → ℝ) (V : ι → ℝ)
 (h₀ : ∀ i, P 0 i≤V i)
 (step : ∀ n, (∀ i, P n i≤V i) → ∀ i, P (n+1) i≤V i) :
 ∀ n i, P n i≤V i := by {intro n,induction n with n ih,exact h₀,exact step n ih}

-- Helicity contractions in the pair rest frame for h_i = ±1.
theorem same_helicity (h : ℝ) (hh : h^2=1) :
 1-h*h=0 ∧ 1+h*h=2 := by {split; nlinarith}
theorem opposite_helicity (h : ℝ) (hh : h^2=1) :
 1-h*(-h)=2 ∧ 1+h*(-h)=0 := by {split; nlinarith}
theorem lambda_factor (q y : ℝ) :
 (1-q^2-y)^2-4*q^2*y=((1-q)^2-y)*((1+q)^2-y) := by ring
theorem pair_energy (q y d : ℝ) :
 (1-q^2+y+d)/4+(1-q^2+y-d)/4+(1+q^2-y)/2=1 := by ring
theorem daughter_mass (q y : ℝ) :
 ((1+q^2-y)/2)^2-((1-q^2-y)^2-4*q^2*y)/4=q^2 := by ring
theorem angular_mean : (1:ℝ)-2/3+1/5=8/15 := by norm_num
theorem widths (a b m : ℝ) (ha : a≠0) (hm : m≠0) :
 b*m^9/(a*m^3)=(b/a)*m^6 := by {field_simp [ha,hm],ring}
theorem continuation_complement (b : ℝ) (hb : 0≤b) :
 b/(1+b)+1/(1+b)=1 := by {field_simp [show 1+b≠0,by linarith],ring}
theorem continuation_bound (b : ℝ) (hb : 0≤b) : b/(1+b)≤b :=
(div_le_iff (by linarith : 0<1+b)).2 (by nlinarith [sq_nonneg b])
theorem odds_contract (q m b : ℝ) : b*(q*m)^6=q^6*(b*m^6) := by ring
theorem survival_step (s b : ℝ) (hs : 0≤s) (hb : 0≤b) :
 s*(b/(1+b))≤s*b := mul_le_mul_of_nonneg_left (continuation_bound b hb) hs

-- A tail of survival weights dominated by a contracting geometric sequence.
theorem tail_bound (a : ℕ → ℝ) (r : ℝ) (hr : 0≤r)
 (step : ∀ n, a (n+1)≤r*a n) : ∀ n, a n≤a 0*r^n :=
begin
 intro n, induction n with n ih, {simp},
 calc a (n+1) ≤ r*a n : step n
 ... ≤ r*(a 0*r^n) : mul_le_mul_of_nonneg_left ih hr
 ... = a 0*r^(n+1) : by {rw [pow_succ],ring}
end
theorem tail_vanishes (a : ℕ → ℝ) (r : ℝ) (hr : 0≤r) (hlt : r<1)
 (hp : ∀ n, 0≤a n) (step : ∀ n, a (n+1)≤r*a n) :
 tendsto a at_top (nhds 0) :=
begin
 have h := (tendsto_const_nhds : tendsto (λ n:ℕ, a 0) at_top (nhds (a 0))).mul
   (tendsto_pow_at_top_nhds_0_of_lt_1 hr hlt),
 rw [mul_zero] at h,
 exact squeeze_zero hp (tail_bound a r hr step) h
end
theorem tail_summable (a : ℕ → ℝ) (r : ℝ) (hr : 0≤r) (hlt : r<1)
 (hp : ∀ n, 0≤a n) (step : ∀ n, a (n+1)≤r*a n) : summable a :=
summable_of_nonneg_of_le hp (tail_bound a r hr step)
 ((summable_geometric_of_lt_1 hr hlt).mul_left (a 0))
theorem weighted_step (q a b w : ℝ) (hq : 0<q) (hw : w≠0) :
 (a*b/(1+b))/(w*q^4)=(a/w)*(b/((1+b)*q^4)) :=
by {by_cases hb : 1+b=0,{rw [hb],simp},field_simp [hw,ne_of_gt hq,hb],left,ring}
theorem eventual_wait_ratio (b Q : ℝ) (hb : 0≤b) (hQ : 0<Q) (h : b≤Q/2) :
 b/((1+b)*Q)≤1/2 :=
(div_le_iff (mul_pos (by linarith) hQ)).2 (by nlinarith [mul_nonneg hb hQ.le])

-- Error correction with a never-read code and an uncontrolled history.
-- A radiation parity isometry relates the signs and their charge sectors are orthogonal.
theorem hidden_gram {ι H : Type*} (p : H → H → ℂ) (a : ι → H) (flip : H → H)
 (iso : ∀ x y, p (flip x) (flip y)=p x y)
 (orth : ∀ i j, p (a i) (flip (a j))=0)
 (rev : ∀ i j, p (flip (a i)) (a j)=0) (i j : ι) :
 p (a i) (a j)=p (flip (a i)) (flip (a j)) ∧
 p (a i) (flip (a j))=0 ∧ p (flip (a i)) (a j)=0 :=
⟨(iso _ _).symm,orth _ _,rev _ _⟩
theorem parity_overlap (x y : ℂ) : (x+y)+(x-y)=2*x := by ring
-- Relative parallel transport on any chain of sites is an endpoint operation.
theorem connection_join {G : Type*} [group G] (u v w : G) :
 (w*v⁻¹)*(v*u⁻¹)=w*u⁻¹ := by simp [mul_assoc]
theorem conjugate_exchange {G : Type*} [group G] (u h k : G) :
 (u*h*u⁻¹)*(u*k*u⁻¹)=u*(h*k)*u⁻¹ := by simp [mul_assoc]

-- The small-gauge action uses Stokes for the bulk increment; the edge is oriented.
theorem switching_gauge (bulk edge variation edge_shift : ℝ)
 (stokes : variation=edge_shift) :
 (bulk+variation)-(edge+edge_shift)=bulk-edge := by linarith
theorem sphere_charge (charge euler : ℤ) (sphere : euler=2)
 (constraint : 2*charge+euler=0) : charge= -1 := by omega

-- Actual two-width survival recurrence. The weight t^{-n} can include recoil
-- and the scaling of the proper lifetime of each daughter.
theorem endpoint_weight_summable (B h t : ℝ) (hb : 0≤B) (hh : 0≤h)
 (hh1 : h<1) (ht : 0<t) (s : ℕ → ℝ) (hs : ∀ n, 0≤s n)
 (law : ∀ n, s (n+1)=s n*((B*h^n)/(1+B*h^n))) :
 summable (λ n, s n/t^n) :=
begin
 have lim := (tendsto_const_nhds : tendsto (λ n:ℕ, B) at_top (nhds B)).mul
   (tendsto_pow_at_top_nhds_0_of_lt_1 hh hh1),
 rw [mul_zero] at lim,
 have small : ∀ᶠ n:ℕ in at_top, B*h^n<t/2 :=
   lim.eventually (gt_mem_nhds (show (0:ℝ)<t/2,by linarith)),
 obtain ⟨N,hN⟩ := eventually_at_top.1 small,
 apply (summable_nat_add_iff N).1,
 apply tail_summable _ (1/2:ℝ) (by norm_num) (by norm_num),
 { intro n, exact div_nonneg (hs _) (pow_nonneg ht.le _) },
 { intro n,
   change s (n+1+N)/t^(n+1+N) ≤ 1/2*(s (n+N)/t^(n+N)),
   rw [show n+1+N=n+N+1,by omega,law,pow_succ],
   have hn : 0≤B*h^(n+N) := mul_nonneg hb (pow_nonneg hh _),
   have hsmall := (hN (n+N) (by omega)).le,
   have ht' : 0<t^(n+N) := pow_pos ht _,
   have ratio : B*h^(n+N)/(1+B*h^(n+N)) ≤ t/2 :=
       le_trans (continuation_bound _ hn) hsmall,
   apply (div_le_iff (mul_pos ht ht')).2,
   have prod := mul_le_mul_of_nonneg_left ratio (hs (n+N)),
   calc s (n+N)*(B*h^(n+N)/(1+B*h^(n+N))) ≤ s (n+N)*(t/2) : prod
   ... = 1/2*(s (n+N)/t^(n+N))*(t*t^(n+N)) :
       by {field_simp [ne_of_gt ht'],ring} },
 all_goals { apply_instance }
end

theorem endpoint_survival_zero (B h : ℝ) (hb : 0≤B) (hh : 0≤h) (hlt : h<1)
 (s : ℕ → ℝ) (hs : ∀ n, 0≤s n)
 (law : ∀ n, s (n+1)=s n*((B*h^n)/(1+B*h^n))) :
 tendsto s at_top (nhds 0) :=
begin
 have hsum := endpoint_weight_summable B h 1 hb hh hlt zero_lt_one s hs law,
 simp only [one_pow,div_one] at hsum,
 exact hsum.tendsto_at_top_zero
end
theorem register_odds (a b m : ℝ) (ha : a≠0) (hm : m≠0) :
 b*m^9/(a*m^5)=(b/a)*m^4 := by {field_simp [ha,hm],ring}
theorem choose_pair {ι : Type*} (r : ι → ℝ) (a i : ι) (d : ℝ)
 (hd : 0<d) (truth : r a=0) (separated : ∀ j, j≠a → d≤r j)
 (best : r i≤r a) : i=a :=
begin by_contra h,have h₁ := separated i h,rw [truth] at best,linarith end
theorem pairing_tolerance (right wrong noise gap : ℝ) (hr : right≤noise)
 (hw : gap-noise≤wrong) (hg : 2*noise<gap) : right<wrong := by linarith
-- Infinite-species interpretation at a fixed photon collision energy.
theorem unsuppressed_bulk_tail (w : ℕ → ℝ) (d : ℝ) (hd : 0<d)
 (h : ∀ n, d≤w n) : ¬ summable w :=
begin
 intro hsum,
 have hs := hsum.tendsto_at_top_zero,
 have hle : d≤(0:ℝ) := ge_of_tendsto' hs h,
 linarith
end
theorem tapered_bulk_tail (w : ℕ → ℝ) (B r : ℝ) (hr : 0≤r) (hr1 : r<1)
 (posw : ∀ n, 0≤w n) (bound : ∀ n, w n≤B*r^n) : summable w :=
 summable_of_nonneg_of_le posw bound ((summable_geometric_of_lt_1 hr hr1).mul_left B)
section radiation_decoder
open_locale complex_inner_product_space
variables {H K : Type*} [normed_add_comm_group H] [inner_product_space ℂ H]
 [normed_add_comm_group K] [inner_product_space ℂ K]
variables (positive negative : H →ₗᵢ[ℂ] K)
 (sectors : ∀ x y, ⟪positive x,negative y⟫=0)
include sectors

-- The common space H may contain arbitrary coherent history and reference vectors.
theorem decoder_preserves_gram (u v u' v' : H) :
 ⟪positive u+negative v,positive u'+negative v'⟫=⟪u,u'⟫+⟪v,v'⟫ :=
begin
 have rev : ⟪negative v,positive u'⟫=0 := inner_eq_zero_symm.1 (sectors u' v),
 simp only [inner_add_left,inner_add_right,linear_isometry.inner_map_map,sectors,rev,
            add_zero,zero_add]
end

theorem decoder_unique_on_range (u v u' v' : H)
 (same : positive u+negative v=positive u'+negative v') : u=u' ∧ v=v' :=
begin
 have hp : ∀ x : H, ⟪x,u⟫=⟪x,u'⟫,
 { intro x, have h := congr_arg (λ k:K, ⟪positive x,k⟫) same,
   simpa only [inner_add_right,linear_isometry.inner_map_map,sectors,add_zero] using h },
 have hn : ∀ x : H, ⟪x,v⟫=⟪x,v'⟫,
 { intro x, have rev : ∀ y : H, ⟪negative x,positive y⟫=0 := λ y, inner_eq_zero_symm.1 (sectors y x),
   have h := congr_arg (λ k:K, ⟪negative x,k⟫) same,
   simpa only [inner_add_right,linear_isometry.inner_map_map,rev,zero_add] using h },
 have hu : ⟪u-u',u-u'⟫=0 := by rw [inner_sub_right,hp (u-u'),sub_self],
 have hv : ⟪v-v',v-v'⟫=0 := by rw [inner_sub_right,hn (v-v'),sub_self],
 exact ⟨sub_eq_zero.mp (inner_self_eq_zero.mp hu),sub_eq_zero.mp (inner_self_eq_zero.mp hv)⟩
end
end radiation_decoder
end material_charge_readout
