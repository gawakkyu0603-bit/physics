import analysis.special_functions.integrals
import algebra.geom_sum
import tactic

noncomputable theory
open_locale big_operators interval
open measure_theory

namespace continuum_layer_interface

theorem refinement (u v w θ phi : ℝ) :
 (u+v)*w*(1-real.cos (θ-phi)) =
 u*w*(1-real.cos (θ-phi))+v*w*(1-real.cos (θ-phi)) := by ring

-- Two independent actual populations. c and s stand for cos(j theta) and sin(j theta).
theorem population_moment {α β : Type*} [measurable_space α] [measurable_space β]
 (μ : measure α) (ν : measure β) [is_probability_measure μ] [is_probability_measure ν]
 (c s : α→ℝ) (d t : β→ℝ) (hc : integrable c μ) (hs : integrable s μ)
 (hd : integrable d ν) (ht : integrable t ν) :
 (∫ x, (∫ y, 1-(c x*d y+s x*t y) ∂ν) ∂μ) =
 1-((∫ x, c x ∂μ)*(∫ y,d y ∂ν)+(∫ x,s x ∂μ)*(∫ y,t y ∂ν)) :=
begin
 have inner : ∀ x, (∫ y, 1-(c x*d y+s x*t y) ∂ν) =
    1-(c x*(∫ y,d y ∂ν)+s x*(∫ y,t y ∂ν)),
 { intro x, have h : integrable (λ y, c x*d y+s x*t y) ν := (hd.const_mul (c x)).add (ht.const_mul (s x)),
   rw [integral_sub (integrable_const (1:ℝ)) h, integral_add (hd.const_mul (c x)) (ht.const_mul (s x)), integral_mul_left, integral_mul_left],simp },
 simp_rw [inner],
 let D:= ∫y,d y ∂ν, let T:= ∫y,t y ∂ν,
 change (∫x,1-(c x*D+s x*T) ∂μ)=1-((∫x,c x ∂μ)*D+(∫x,s x ∂μ)*T),
 have hh : integrable (λ x,c x*D+s x*T) μ := (hc.mul_const D).add (hs.mul_const T),
 rw [integral_sub (integrable_const (1:ℝ)) hh,integral_add (hc.mul_const D) (hs.mul_const T),integral_mul_right,integral_mul_right],simp
end

theorem thin_integral_bound {α : Type*} [measurable_space α]
 (μ : measure α) (f g : α→ℝ) (hf : integrable f μ) (hg : integrable g μ)
 (h : ∀x, f x ≤ g x) : (∫x, f x ∂μ) ≤ ∫x,g x ∂μ := integral_mono hf hg h

theorem all_harmonics (J D : ℕ→ℝ) (σ : ℝ)
 (hJ : ∀ n, 0 ≤ J n) (hD : ∀ n, D n ≤ σ^2*(n:ℝ)^2)
 (hs : summable (λ n,J n*D n)) (ht : summable (λ n,J n*(n:ℝ)^2)) :
 (∑' n,J n*D n) ≤ σ^2 * ∑' n,J n*(n:ℝ)^2 :=
begin
 rw [←tsum_mul_left],
 apply tsum_le_tsum _ hs (ht.mul_left _),
 intro n, calc J n*D n ≤ J n*(σ^2*(n:ℝ)^2) : mul_le_mul_of_nonneg_left (hD n) (hJ n)
 ... = σ^2*(J n*(n:ℝ)^2) : by ring
end

theorem thick_harmonic (x : ℕ→ℝ) (hs : summable x) (hp : ∀ n,0≤x n) :
 x 1≤∑' n,x n := le_tsum hs 1 (λ n hn,hp n)

theorem strict_band (a b lo hi e : ℝ) (ha : a<lo) (hb : hi<b)
 (h1 : lo≤e) (h2 : e≤hi) : a<e ∧ e<b := ⟨lt_of_lt_of_le ha h1,lt_of_le_of_lt h2 hb⟩

theorem visibility_bound (a b : ℝ) : 2*a*b≤a^2+b^2 := by nlinarith [sq_nonneg (a-b)]

theorem variance_estimator (r n : ℝ) (hr : r≠0) (hn : n≠0) :
 (1-(r/2)^2)/((r/2)^2*n)=(4/r^2-1)/n := by field_simp;ring

theorem all_chords (z : ℂ) (hz : ‖z‖=1) (n : ℕ) :
 ‖z^n-1‖≤(n:ℝ)*‖z-1‖ :=
begin
 induction n with n hn,
 { simp },
 { have eq : z^(n+1)-1=z^n*(z-1)+(z^n-1) := by rw [pow_succ];ring,
   calc ‖z^(n+1)-1‖ ≤ ‖z^n*(z-1)‖+‖z^n-1‖ : by rw [eq];apply norm_add_le
   ... ≤ ‖z^n*(z-1)‖+(n:ℝ)*‖z-1‖ : add_le_add_left hn _
   ... = ((n+1:ℕ):ℝ)*‖z-1‖ : by rw [norm_mul,norm_pow,hz,one_pow,one_mul,nat.cast_add,nat.cast_one];ring }
end

theorem shifted_second {α : Type*} [measurable_space α] (μ : measure α)
 [is_probability_measure μ] (x : α→ℝ) (a : ℝ) (hx : integrable x μ)
 (hxx : integrable (λ i,x i^2) μ) (h0 : (∫ i,x i ∂μ)=0) :
 (∫ i,(x i+a)^2 ∂μ)=(∫ i,x i^2 ∂μ)+a^2 :=
begin
 have expand : ∀i,(x i+a)^2=(x i^2+(2*a)*x i)+a^2 := λ i,by ring,
 simp_rw [expand],
 have hsum : integrable (λ i,x i^2+(2*a)*x i) μ := hxx.add (hx.const_mul (2*a)),
 rw [integral_add hsum (integrable_const (a^2)),integral_add hxx (hx.const_mul (2*a)),integral_mul_left,h0],
 simp
end

theorem bad_tail_point (x a g : ℝ) (ha : 0≤a) (hg : 0≤g) :
 (if g≤x then (g+a)^2 else 0) ≤ (x+a)^2 :=
begin split_ifs with h,
 { exact pow_le_pow_of_le_left (add_nonneg hg ha) (add_le_add_right h _) _ },
 { exact sq_nonneg _ }
end

theorem square_chord (x : ℝ) : 1-real.cos (2*x) ≤ 4*(1-real.cos x) :=
begin rw [real.cos_two_mul], nlinarith [sq_nonneg (1-real.cos x)] end

theorem uncertainty_to_tail (p E m : ℝ) (hE : 0<E) (h : p*E≤m) : p≤m/E :=
(le_div_iff hE).mpr h

theorem receiver_to_tail (p strength e information : ℝ)
 (hs : 0<strength) (he : e<strength) (h : p*(1-e/strength)≤information) :
 p≤information/(1-e/strength) :=
(le_div_iff (sub_pos.mpr ((div_lt_one hs).mpr he))).mpr h

theorem cantelli (p gap variance : ℝ) (hg : 0<gap) (hv : 0≤variance)
 (second : p*(gap+variance/gap)^2 ≤ variance+(variance/gap)^2) :
 p≤variance/(variance+gap^2) :=
begin
 have h1 : 0<variance+gap^2 := add_pos_of_nonneg_of_pos hv (sq_pos_of_pos hg),
 apply (le_div_iff h1).mpr,
 have ht : p*(variance+gap^2)^2 ≤ variance*(variance+gap^2) :=
 begin
   field_simp [ne_of_gt hg] at second,
   have s2 := (div_le_div_right (sq_pos_of_pos hg)).mp second,
   nlinarith only [s2]
 end,
 exact (le_of_mul_le_mul_right (show p*(variance+gap^2)*(variance+gap^2)≤variance*(variance+gap^2),
 by simpa [pow_two,mul_assoc] using ht) h1)
end

theorem two_channel_work (m w h v : ℝ) :
 m*v^4/8*(h*w-h*w*real.cos v)=(m*v^4*h*w/8)*(1-real.cos v) := by ring

theorem trapped_speed (r R beta mass G speed : ℝ) (hr : 0<r)
 (ht : beta*(R-r)≤2*G*mass-r) (hs : 2*G*mass/r-1≤speed^2) :
 beta*(R-r)/r≤speed^2 :=
begin apply (div_le_iff hr).mpr,
 have b : (2*G*mass/r-1)*r≤speed^2*r := mul_le_mul_of_nonneg_right hs hr.le,
 field_simp [ne_of_gt hr] at b, linarith
end

theorem transformed_proper_time (R beta : ℝ) :
 (2*R/real.sqrt beta)*(∫ t in (0:ℝ)..real.pi/2,real.sin t^2)=
 real.pi*R/(2*real.sqrt beta) :=
begin rw [integral_sin_sq,real.sin_pi_div_two,real.cos_pi_div_two,real.sin_zero,real.cos_zero],
 simp [div_eq_mul_inv,mul_inv_rev]; ring end

theorem curvature_hazard (R K : ℝ) (hr : R≠0) :
 R*(12/R^4)*K=12*K/R^3 := by field_simp;ring

-- The map ins replaces bit i in a four-bit word by u, filling the other
-- three bits, in order, with k. Squares and cross-products reduce to counts.
def mask (j : bool) (n : ℕ) : ℕ :=
 if j then (if n=5 ∨ n=10 then 1 else 0)
 else (if n=3 ∨ n=6 ∨ n=12 ∨ n=9 then 1 else 0)
def ins (i u k : ℕ) : ℕ := k % (2^i)+u*2^i+(k/(2^i))*2^(i+1)

theorem code_partial_counts : ∀ (i : fin 4) (u v : fin 2) (j l : bool),
 (∑ k in finset.range 8, mask j (ins i u k)*mask l (ins i v k)) =
 if j=l ∧ u=v then (if j then 1 else 2) else 0 :=
by exact dec_trivial

theorem code_partial_state (a b : ℝ) (ha : 4*a^2=1) (hb : 2*b^2=1)
 (i : fin 4) (u v : fin 2) (j l : bool) :
 (if j then b else a)*(if l then b else a)*
 ((∑ k in finset.range 8, mask j (ins i u k)*mask l (ins i v k) : ℕ):ℝ)
 = if j=l ∧ u=v then 1/2 else 0 :=
begin
 rw [code_partial_counts], by_cases h : j=l ∧ u=v,
 { rw [if_pos h,if_pos h,h.1], cases l; norm_num; nlinarith },
 { rw [if_neg h,if_neg h], simp }
end

theorem quartet_lower (p : ℝ) (h1 : (1:ℝ)/10≤p) (h2 : p≤9/10) :
 486/10000 ≤ 6*p^2*(1-p)^2 :=
begin
 have h : (9:ℝ)/100≤p*(1-p) := by nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)],
 have hh := mul_self_le_mul_self (show (0:ℝ)≤9/100, by norm_num) h,
 nlinarith only [hh]
end

theorem horizon_gravitons (m r omega mass : ℝ) (ho : omega≠0) (hr : r≠0) (hm : mass≠0) :
 ((16/45:ℝ)*mass^6*(18*m^2*omega^2/(r*mass)^6))*(2*real.pi/omega)/(2*omega)
 = 32*real.pi*m^2/(5*r^6) := by field_simp;ring

theorem kerr_radius_bound (r a : ℝ) (hr : 0<r) :
 real.sqrt (r^2+a^2)≤r+a^2/(2*r) :=
begin
 have h : 0≤r+a^2/(2*r) := by positivity,
 apply (real.sqrt_le_left h).mpr,
 have eq : (r+a^2/(2*r))^2 = r^2+a^2+(a^2/(2*r))^2 := by field_simp [ne_of_gt hr];ring,
 rw [eq],nlinarith [sq_nonneg (a^2/(2*r))]
end

theorem dark_port (a : ℝ) : (a-a)^2=0 := by ring
theorem surviving_sector :
 (26/65:ℝ)*(18/26)=18/65 ∧ 2*(18/65:ℝ)=36/65 ∧
 (36/65:ℝ)+(29/65)=1 := by norm_num

theorem full_flag_capacity (dims old logic k : ℕ) (h : 0<old*logic) :
 old*logic*k≤dims ↔ k≤dims/(old*logic) :=
by rw [nat.le_div_iff_mul_le h, mul_comm k]

theorem one_quiet_flag (k : ℝ) (hk : k≠0) : 1/k+(k-1)/k=1 :=
by field_simp;ring

theorem spherical_entropy (g M d : ℝ) :
 4*real.pi*g*(M+d)^2-4*real.pi*g*M^2=8*real.pi*g*M*d+4*real.pi*g*d^2 := by ring

theorem spare_entropy_bound (R e E radius logical : ℝ) (h : logical≤2*real.pi*E*radius) :
 2*real.pi*E*(2*e*R-radius)≤4*real.pi*R*e*E-logical := by linarith only [h]

theorem simplex_quiet_tail (a : ℝ) (k : ℕ) (h : a≠1) :
 (1-a)^(k+1)/(1-a)=(1-a)^k :=
by rw [pow_succ]; field_simp [sub_ne_zero.mpr (ne.symm h)]; ring

theorem one_pair_fusion (n : ℝ) (hn : 1≤n) :
 1≤(4*n+2)/(2*(n+2)) ∧ (4*n+2)/(2*(n+2))<2 :=
begin have hp : 0<2*(n+2) := by linarith,split,
 {apply (le_div_iff hp).mpr,linarith},{apply (div_lt_iff hp).mpr,linarith} end

theorem two_pair_fusion (n : ℝ) (hn : 9≤n) :
 3≤((4*n+2)*(4*n+6))/(4*(n+2)*(n+3)) ∧
 ((4*n+2)*(4*n+6))/(4*(n+2)*(n+3))<4 :=
begin
 have hp : 0<4*(n+2)*(n+3) := mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith),
 split,
 {apply (le_div_iff hp).mpr,nlinarith [mul_nonneg (show 0≤n-9,by linarith) (show 0≤n+2,by linarith)]},
 {apply (div_lt_iff hp).mpr,nlinarith}
end

theorem level_two_all (s : ℕ) (old : ℝ) (hp : old≠0) :
 ((2:ℝ)^s*old)/((2:ℝ)^s*old)=1 := div_self (mul_ne_zero (pow_ne_zero s (by norm_num)) hp)

end continuum_layer_interface
