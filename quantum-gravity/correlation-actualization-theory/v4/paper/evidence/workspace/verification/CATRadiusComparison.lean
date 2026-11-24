import analysis.special_functions.pow.real
import tactic

open_locale big_operators
namespace cat_radius_comparison

-- The two rows of the real magnetic block, with the common scale removed.
theorem magnetic_norm (a b x y : ℝ) :
 (-a*x+b*y)^2+(b*x+a*y)^2 = (a^2+b^2)*(x^2+y^2) := by ring

theorem vector_spin_character (lo mid hi : ℝ) :
 2*lo+4*mid+2*hi = (4*lo+8*mid+4*hi)/2 := by ring

theorem sector_floor (mu2 b n1 n2 : ℝ) (hb : 0≤b) (h1 : 0≤n1) (h2 : 0≤n2) :
 mu2 ≤ mu2+2*b*(n1+n2+1)-2*b :=
by nlinarith [mul_nonneg hb h1, mul_nonneg hb h2]

theorem base_casimir_homogeneity (l m t h w : ℝ) (hl : 0<l) (hm : 0<m)
 (ht : 0<t) (hw : 0<l^2*h+m^2*w) :
 ((t*l)*(t*m))^2/((t*l)^2*h+(t*m)^2*w)^4 =
 (l*m)^2/(l^2*h+m^2*w)^4/t^4 :=
begin
 have eq : (t*l)^2*h+(t*m)^2*w = t^2*(l^2*h+m^2*w) := by ring,
 rw [eq], have tt := ne_of_gt ht, have ww := ne_of_gt hw,
 field_simp; ring
end

-- Energy contributions already include their scale factors at the tested point.
theorem three_weights (a b c : ℝ) :
 81*a+144*b+225*c+24*(-9*a-12*b-15*c)+135*(a+b+c) = -9*b := by ring

theorem stationary_curvature (a b c : ℝ) (hb : 0≤b)
 (stat : -9*a-12*b-15*c=0) :
 81*a+144*b+225*c ≤ -135*(a+b+c) := by linarith [three_weights a b c]

theorem dilaton_curvature (h l q : ℝ) (stat : 2*h+3*l+4*q=0) :
 4*h+9*l+16*q = -4*h-3*l := by linarith

theorem filled_dilaton (h l q : ℝ) (hh : 0<h) (hl : 0≤l)
 (stat : 2*h+3*l+4*q=0) : 4*h+9*l+16*q<0 :=
by linarith [dilaton_curvature h l q stat]

theorem central_second_sign (k z p : ℝ) (hk : k≠0) (hz : 0<z) (hp : 0<p) :
 0<12*k^2*z/p^5 := by positivity

-- Remainder of the rational summand in the Mittag-Leffler expansion.
theorem central_remainder (v : ℝ) (hv : 0≤v) :
 (1-v)/(1+v)^2 =
 1-3*v+5*v^2-7*v^3+9*v^4-v^5*(9/(1+v)+2/(1+v)^2) :=
begin
 have h : 1+v≠0 := by linarith,
 field_simp [h]; ring
end

theorem response_factors (x r : ℝ) (hx : 0≤x) (hx' : x≤1)
 (hr : 1≤r) (hr' : r≤2) : 0≤r*x ∧ r*x≤2 ∧ 0≤r*x*(1-x) ∧ r*x*(1-x)≤2 :=
begin
 have r0 : 0≤r := by linarith,
 have a := mul_nonneg r0 hx,
 have b : r*x≤2 := le_trans (by simpa using mul_le_mul_of_nonneg_left hx' r0) hr',
 have c := mul_nonneg a (show 0≤1-x, by linarith),
 have d : r*x*(1-x)≤r*x := by
   simpa using mul_le_mul_of_nonneg_left (show 1-x≤1, by linarith) a,
 exact ⟨a,b,c,le_trans d b⟩
end

theorem remainder_response (a b : ℝ) (ha : 0≤a) (ha' : a≤2)
 (hb : 0≤b) (hb' : b≤2) :
 0 ≤ 4*((5-a)^2-b-1) ∧ 4*((5-a)^2-b-1) ≤ 96 :=
begin
 have lo := pow_le_pow_of_le_left (show (0:ℝ)≤3, by norm_num)
    (show 3≤5-a, by linarith) 2,
 have hi := pow_le_pow_of_le_left (show 0≤5-a, by linarith)
    (show 5-a≤5, by linarith) 2,
 split; linarith only [lo,hi,hb,hb']
end

noncomputable def tail_estimate (e : ℝ) : ℝ :=
 (9/4:ℝ)*(32*(6/675:ℝ)*e^6+60*(2/10395:ℝ)*15480*e^8+
 96*44*5040*192/(3:ℝ)^12*e^10)

theorem tail_small (e : ℝ) (he : 0≤e) (h : e≤1/4) :
 tail_estimate e < 432/(4:ℝ)^7 :=
begin
 have a := pow_le_pow_of_le_left he h 6,
 have b := pow_le_pow_of_le_left he h 8,
 have c := pow_le_pow_of_le_left he h 10,
 unfold tail_estimate, norm_num at a b c ⊢, linarith
end

theorem central_ray_test (e response leading remainder : ℝ) (he : 0≤e) (h : e≤1/4)
 (split : response = leading + remainder)
 (lower : leading ≤ -(432/(4:ℝ)^7)) (bound : remainder ≤ tail_estimate e) :
 response<0 := by linarith [tail_small e he h]

-- Every row of the mismatch operator may have its own positive response.
theorem common_kernel {ι : Type*} (s : finset ι) (w t : ι → ℝ)
 (pos : ∀ i ∈ s, 0<w i) :
 (∑ i in s, w i*(t i)^2)=0 ↔ ∀ i ∈ s, t i=0 :=
begin
 classical,
 have nn : ∀ i ∈ s, 0≤w i*(t i)^2 :=
   λ i h, mul_nonneg (le_of_lt (pos i h)) (sq_nonneg _),
 split,
 { intros eq i hi,
   have h := finset.single_le_sum nn hi,
   rw [eq] at h,
   have he : w i*(t i)^2=0 := le_antisymm h (nn i hi),
   exact pow_eq_zero ((mul_eq_zero.mp he).resolve_left (ne_of_gt (pos i hi))) },
 { intro allzero, exact finset.sum_eq_zero (λ i hi, by rw [allzero i hi]; ring) }
end

theorem common_shift (a b q : ℝ) : (a+q)-(b+q)=a-b := by ring

theorem real_readout {ι : Type*} (s : finset ι) (k v : ι → ℝ) (f df : ℝ)
 (norm : (∑ i in s, (k i)^2)=1) (tangent : (∑ i in s, k i*v i)=0) :
 (∑ i in s, (v i*f+k i*df)^2) = f^2*(∑ i in s, (v i)^2)+df^2 :=
begin
 classical,
 calc
  (∑ i in s, (v i*f+k i*df)^2) =
   ∑ i in s, (f^2*(v i)^2+ (2*f*df)*(k i*v i)+df^2*(k i)^2) :
   finset.sum_congr rfl (λ i hi, by ring)
  ... = _ : by simp only [finset.sum_add_distrib, ← finset.mul_sum, norm, tangent]; ring
end

-- For a complex multiplier k=x+i*y, k'=u+i*v, psi=f+i*g,
-- psi'=d+i*e. The antisymmetric cross term is the phase-induced recoil.
theorem complex_readout_row (x y u v f g d e : ℝ) :
 (u*f-v*g+x*d-y*e)^2+(v*f+u*g+y*d+x*e)^2 =
 (u^2+v^2)*(f^2+g^2)+(x^2+y^2)*(d^2+e^2)
 +2*(x*u+y*v)*(f*d+g*e)+2*(x*v-y*u)*(f*e-g*d) := by ring

theorem completed_momentum (f g d e a noise : ℝ) :
 (e+a*f)^2+(-d+a*g)^2+(noise-a^2)*(f^2+g^2) =
 d^2+e^2+2*a*(f*e-g*d)+noise*(f^2+g^2) := by ring

section charge
variables {R : Type*} [ring R]

theorem missing_interference (p e : R) :
 p*e*p + (1-p)*e*(1-p) - e =
 -(p*e*(1-p)+(1-p)*e*p) := by noncomm_ring

theorem unaffected_radius (p e : R) (proj : p*p=p) (comm : p*e=e*p) :
 p*e*p + (1-p)*e*(1-p) = e :=
begin
 have h : p*e*p = e*p := by rw [comm, mul_assoc, proj],
 calc p*e*p+(1-p)*e*(1-p) = e-p*e-e*p+(p*e*p+p*e*p) : by noncomm_ring
 ... = e : by rw [h, comm]; noncomm_ring
end
end charge

theorem crossing_force (energy prob : ℝ) :
 (1-prob)*(3*energy) + prob*(15*energy/4)-3*energy = 3*prob*energy/4 := by ring

theorem both_point_out (energy prob : ℝ) (h : 0<energy) (p : 0≤prob) :
 0 < 3*energy+3*prob*energy/4 := by nlinarith [mul_nonneg p (le_of_lt h)]

-- E^2 is the sum of pieces of weights -6 and -15/2 in the Einstein frame.
theorem all_rest_modes (x y energy force : ℝ) (hx : 0≤x) (hy : 0≤y)
 (positive : 0<energy) (mass : energy^2=x+y)
 (slope : 2*energy*force=6*x+15*y/2) :
 3*energy ≤ force ∧ force ≤ 15*energy/4 :=
begin
 split,
 { apply le_of_not_gt, intro bad,
   have q := mul_lt_mul_of_pos_left bad positive,
   nlinarith only [q,mass,slope,hy] },
 { apply le_of_not_gt, intro bad,
   have q := mul_lt_mul_of_pos_left bad positive,
   nlinarith only [q,mass,slope,hx] }
end

theorem positive_loads {ι : Type*} (s : finset ι) (w e f : ι → ℝ)
 (hw : ∀ i ∈ s, 0≤w i)
 (hf : ∀ i ∈ s, 3*e i≤f i ∧ f i≤15*e i/4) :
 3*(∑ i in s, w i*e i) ≤ (∑ i in s, w i*f i) ∧
 (∑ i in s, w i*f i) ≤ (15/4:ℝ)*(∑ i in s, w i*e i) :=
begin
 classical,
 split,
 { rw [finset.mul_sum], apply finset.sum_le_sum, intros i hi,
   calc 3*(w i*e i) = w i*(3*e i) : by ring
   ... ≤ w i*f i : mul_le_mul_of_nonneg_left (hf i hi).1 (hw i hi) },
 { rw [finset.mul_sum], apply finset.sum_le_sum, intros i hi,
   calc w i*f i ≤ w i*(15*e i/4) : mul_le_mul_of_nonneg_left (hf i hi).2 (hw i hi)
   ... = (15/4:ℝ)*(w i*e i) : by ring }
end

theorem routing_bound (p e f g : ℝ) (hp : 0≤p) (f0 : 3*e≤f) (f1 : f≤15*e/4)
 (g0 : 3*e≤g) (g1 : g≤15*e/4) : |p*(g-f)| ≤ 3*p*e/4 :=
begin
 rw [abs_le], split,
 { have q := mul_le_mul_of_nonneg_left (show -(3*e/4)≤g-f, by linarith) hp,
   nlinarith only [q] },
 { have q := mul_le_mul_of_nonneg_left (show g-f≤3*e/4, by linarith) hp,
   nlinarith only [q] }
end

end cat_radius_comparison
