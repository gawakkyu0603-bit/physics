import tactic
import analysis.special_functions.integrals
import topology.algebra.order.intermediate_value

/- A normalized matrix sphere in the marginal dust clock s. The Volterra
   equality below follows from the radial differential equation. Closure is
   conditional on an actual received, uncompensated charge on the tested port. -/
namespace cat_falling_fermi_edge
noncomputable theory
open set measure_theory
open_locale interval

def b (s : ℝ) := 2*s-s^2
def h (s : ℝ) := 3*s*(1-s)
def kernel (s r : ℝ) := 18*s*(r-s)*r^3

theorem tidal_advantage (s : ℝ) :
 h s - b s*(1-s^3) = s*(1-s)^3*(1+s) :=
by {unfold h b, ring}

theorem strict_advantage (s : ℝ) (hs : 0<s) (hs' : s<1) :
 b s*(1-s^3)<h s :=
begin
 have hpos : 0<s*(1-s)^3*(1+s) :=
 mul_pos (mul_pos hs (pow_pos (sub_pos.mpr hs') 3)) (by linarith),
 linarith [tidal_advantage s]
end

theorem radial_clock_equation (s y yp ypp : ℝ) :
 s^2*(2*yp+s*ypp)-2*s*(y+s*yp)+2*(s*y)=s^3*ypp := by ring

theorem green_bound (s r : ℝ) (hs : 0≤s) (hsr : s≤r) :
 0≤kernel s r ∧ kernel s r≤6*r^2*(r^3-s^3) :=
begin
 have hr : 0≤r := le_trans hs hsr,
 have hd := pow_nonneg (sub_nonneg.mpr hsr) 3,
 split,
 { unfold kernel, exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs) (sub_nonneg.mpr hsr)) (pow_nonneg hr 3) },
 { unfold kernel, nlinarith [mul_nonneg (sq_nonneg r) hd] }
end

def volterra (R : ℝ → ℝ) (e : ℝ) :=
 ∀ s ∈ Icc (1/3:ℝ) 1,
   b s-R s = ∫ r in s..1, kernel s r*e*(R r)^3

theorem ode_gives_volterra (Y V : ℝ → ℝ) (e : ℝ) (hc : continuous Y)
 (hy : ∀ r ∈ Icc (1/3:ℝ) 1, has_deriv_at Y (V r) r)
 (hv : ∀ r ∈ Icc (1/3:ℝ) 1,
   has_deriv_at V (-18*e*r^3*(r*Y r)^3) r)
 (hi : Y 1=1) (hv1 : V 1= -1) :
 volterra (λ r, r*Y r) e :=
begin
 intros s hs,
 have hint : interval_integrable (λ r:ℝ, kernel s r*e*(r*Y r)^3) volume s 1,
 { apply continuous.interval_integrable, unfold kernel, continuity },
 have dh : ∀ r ∈ Icc s 1, has_deriv_at
   (λ z:ℝ, s*(Y z-(z-s)*V z)) (kernel s r*e*(r*Y r)^3) r,
 { intros r hr, have hm : r ∈ Icc (1/3:ℝ) 1 := ⟨le_trans hs.1 hr.1,hr.2⟩,
   convert ((hy r hm).sub (((has_deriv_at_id r).sub_const s).mul (hv r hm))).const_mul s using 1,
   unfold kernel, simp only [id.def], ring },
 have he := interval_integral.integral_eq_sub_of_has_deriv_at_of_le hs.2 (has_deriv_at.continuous_on dh)
   (λ r hr, dh r (mem_Icc_of_Ioo hr)) hint,
 rw [he], dsimp only, rw [hi,hv1], unfold b, ring
end

theorem envelope_integral (s e : ℝ) (hs : s≤1) :
 (∫ r in s..1, (6*r^2*(r^3-s^3))*e) = e*(1-s^3)^2 :=
begin
 have dh : ∀ r:ℝ, has_deriv_at (λ z:ℝ, e*(z^3-s^3)^2)
     (6*r^2*(r^3-s^3)*e) r,
 { intro r, convert ((((has_deriv_at_id r).pow 3).sub_const (s^3)).pow 2).const_mul e using 1,
   simp [id.def], ring },
 rw [interval_integral.integral_eq_sub_of_has_deriv_at (λ r hr, dh r)
   (continuous.interval_integrable (by continuity) s 1)], ring
end

theorem b_range (s : ℝ) (hs : s ∈ Icc (1/3:ℝ) 1) :
 1/2≤b s ∧ b s≤1 :=
begin
 cases hs with hl hu, unfold b,
 split; nlinarith [mul_nonneg (sub_nonneg.mpr hl) (by linarith : 0≤5/3-s),sq_nonneg (1-s)]
end

theorem local_bounds (R : ℝ → ℝ) (e s : ℝ) (hc : continuous R)
 (law : volterra R e) (he : 0≤e) (hs : s ∈ Icc (1/3:ℝ) 1)
 (pos : ∀ r ∈ Icc s 1, 0≤R r) :
 0≤b s-R s ∧ b s-R s≤e*(1-s^3)^2 :=
begin
 have lower : ∀ v ∈ Icc s 1, 0≤b v-R v,
 { intros v hv,
   rw [law v ⟨le_trans hs.1 hv.1,hv.2⟩],
   apply interval_integral.integral_nonneg hv.2,
   intros r hr, have hp := pos r ⟨le_trans hv.1 hr.1,hr.2⟩,
   exact mul_nonneg (mul_nonneg (green_bound v r (by linarith [hs.1,hv.1]) hr.1).1 he)
      (pow_nonneg hp 3) },
 refine ⟨lower s ⟨le_rfl,hs.2⟩,_⟩,
 rw [law s hs, ←envelope_integral s e hs.2],
 apply interval_integral.integral_mono_on hs.2,
 { apply continuous.interval_integrable, unfold kernel, continuity },
 { apply continuous.interval_integrable, continuity },
 { intros r hr, have hp := pos r hr,
   have hru := (b_range r ⟨le_trans hs.1 hr.1,hr.2⟩).2,
   have hval : R r≤1 := by linarith [lower r hr],
   have hcube : (R r)^3≤1 := by simpa using pow_le_pow_of_le_left hp hval 3,
   have hg := green_bound s r (by linarith [hs.1]) hr.1,
   calc kernel s r*e*(R r)^3 ≤ kernel s r*e*1 :
      mul_le_mul_of_nonneg_left hcube (mul_nonneg hg.1 he)
   ... ≤ 6*r^2*(r^3-s^3)*e : by simpa only [mul_one] using mul_le_mul_of_nonneg_right hg.2 he }
end

theorem positive_from_last_zero (R : ℝ → ℝ) (hc : continuous R) (hend : 0<R 1)
 (test : ∀ (s : ℝ), s ∈ Icc (1/3:ℝ) 1 → (∀ r ∈ Icc s 1, 0≤R r) → 0<R s) :
 ∀ s ∈ Icc (1/3:ℝ) 1, 0<R s :=
begin
 intros s hs, by_contra hn, push_neg at hn,
 obtain ⟨z,hz,hzero⟩ := intermediate_value_Icc hs.2 hc.continuous_on
    (show (0:ℝ) ∈ Icc (R s) (R 1), from ⟨hn,le_of_lt hend⟩),
 let Z := Icc (1/3:ℝ) 1 ∩ R ⁻¹' ({0}:set ℝ),
 have compactZ : is_compact Z := is_compact_Icc.inter_right (is_closed_singleton.preimage hc),
 have nonemptyZ : Z.nonempty := ⟨z,⟨⟨hs.1.trans hz.1,hz.2⟩,hzero⟩⟩,
 obtain ⟨m,hm,hmax⟩ := compactZ.exists_forall_ge nonemptyZ (continuous_id.continuous_on : continuous_on (id : ℝ → ℝ) Z),
 have hm0 : R m=0 := hm.2,
 have posm := test m hm.1 _,
 { linarith },
 intros r hr, by_contra hnegative, push_neg at hnegative,
 obtain ⟨w,hw,hzw⟩ := intermediate_value_Icc hr.2 hc.continuous_on
   (show (0:ℝ) ∈ Icc (R r) (R 1), from ⟨le_of_lt hnegative,le_of_lt hend⟩),
 have hm' : w≤m := hmax w ⟨⟨hm.1.1.trans (hr.1.trans hw.1),hw.2⟩,hzw⟩,
 have hrm : r=m := le_antisymm (hw.1.trans hm') hr.1,
 rw [hrm,hm0] at hnegative, linarith
end

theorem sphere_bounds (R : ℝ → ℝ) (e : ℝ) (hc : continuous R) (R1 : R 1=1)
 (law : volterra R e) (he : 0≤e) (hsmall : e≤1/64) :
 ∀ s ∈ Icc (1/3:ℝ) 1,
 0<R s ∧ 0≤b s-R s ∧ b s-R s≤e*(1-s^3)^2 :=
begin
 have pos := positive_from_last_zero R hc (by rw [R1]; norm_num) _,
 { intros s hs, exact ⟨pos s hs,local_bounds R e s hc law he hs
     (λ r hr, le_of_lt (pos r ⟨hs.1.trans hr.1,hr.2⟩))⟩ },
 intros s hs hprev, have bd := local_bounds R e s hc law he hs hprev,
 have s0 : 0≤s := by linarith [hs.1],
 have powup : s^3≤1 := by simpa using pow_le_pow_of_le_left s0 hs.2 3,
 have tpos := sub_nonneg.mpr powup,
 have tup : (1-s^3)^2≤1 := by simpa using
   pow_le_pow_of_le_left tpos (show 1-s^3≤1, by linarith [pow_nonneg s0 3]) 2,
 have err := mul_le_mul_of_nonneg_left tup he,
 linarith [(b_range s hs).1,bd.2]
end

def point (s d v : ℝ) := (1+d)*b s-v*h s

theorem speed_window_crossing (R : ℝ → ℝ) (e v : ℝ) (hc : continuous R)
 (R1 : R 1=1) (law : volterra R e) (he : 0≤e) (hsmall : e≤1/256)
 (hv : 1/4+(49/48)*e<v) :
 ∃ s ∈ Ioo (1/2:ℝ) 1, R s=point s (1/4) v :=
begin
 have hb := (sphere_bounds R e hc R1 law he (by linarith : e≤1/64) (1/2) (by norm_num)).2.2,
 norm_num [b] at hb,
 let f := λ s:ℝ, point s (1/4) v-R s,
 have hf : continuous f := by {dsimp [f,point,b,h], continuity},
 have hl : f (1/2)<0 := by {dsimp [f,point,b,h], norm_num, linarith},
 have hu : 0<f 1 := by {dsimp [f,point,b,h], rw [R1], norm_num},
 obtain ⟨s,hs,hh⟩ := intermediate_value_Icc (show (1/2:ℝ)≤1, by norm_num)
   hf.continuous_on (show (0:ℝ) ∈ Icc (f (1/2)) (f 1), from ⟨hl.le,hu.le⟩),
 refine ⟨s,⟨lt_of_le_of_ne hs.1 _,lt_of_le_of_ne hs.2 _⟩,_⟩,
 { intro hn, rw [←hn] at hh, linarith },
 { intro hn, rw [hn] at hh, linarith },
 { exact (sub_eq_zero.mp hh).symm }
end

theorem finite_rank_speed (e : ℝ) (he : e≤1/256) :
 1/4+(49/48)*e<(33/128:ℝ) ∧ (33/128:ℝ)<27/104 := by {split; linarith}

theorem flat_energy (R V e : ℝ) (he : 0<e) (conserved : V^2+e*R^4=e) : R≤1 :=
begin
 by_contra hf, push_neg at hf,
 have h4 : (1:ℝ)^4<R^4 := pow_lt_pow_of_lt_left hf (by norm_num) (by norm_num),
 norm_num at h4,
 nlinarith [mul_pos he (sub_pos.mpr h4), sq_nonneg V]
end
theorem flat_exclusion (R v t : ℝ) (hr : R≤1) (hv : 0≤v) (hv' : v<27/104)
 (ht : t≤26/27) : R < 1+1/4-v*t :=
begin
 have hb := mul_le_mul_of_nonneg_left ht hv,
 linarith
end
theorem comoving_exclusion (R s d : ℝ) (hr : R≤b s)
 (hb : 0<b s) (hd : 0<d) : R<point s d 0 :=
by {unfold point, nlinarith [mul_pos hd hb]}
theorem relative_wronskian (R x v w k e : ℝ) :
 ((-k*R-2*e*R^3)*x+v*w)-(v*w+R*(-k*x))= -2*e*R^3*x := by ring
theorem wronskian_positive (R x W : ℝ → ℝ) (e t : ℝ)
 (hcR : continuous R) (hcx : continuous x) (he : 0≤e) (hE : e≤1/256)
 (ht : 0≤t) (hT : t≤26/27) (hw0 : 1/4≤W 0)
 (hR : ∀ z ∈ Icc 0 t, 0≤R z ∧ R z≤1)
 (hx : ∀ z ∈ Icc 0 t, 0≤x z ∧ x z≤5/4)
 (dh : ∀ z ∈ Icc 0 t, has_deriv_at W (-2*e*(R z)^3*x z) z) : 0<W t :=
begin
 have hint : interval_integrable (λ z, -2*e*(R z)^3*x z) volume 0 t :=
   continuous.interval_integrable (by continuity) _ _,
 have heq := interval_integral.integral_eq_sub_of_has_deriv_at_of_le ht
   (has_deriv_at.continuous_on dh) (λ z hz, dh z (mem_Icc_of_Ioo hz)) hint,
 have lower := interval_integral.integral_mono_on ht
   (continuous_const.interval_integrable 0 t :
    interval_integrable (λ _:ℝ, -(5/2)*e) volume 0 t) hint _,
 { rw [heq] at lower,
   change (∫ u in (0:ℝ)..t, (-(5/2)*e:ℝ)) ≤ W t-W 0 at lower,
   rw [interval_integral.integral_const,sub_zero,smul_eq_mul] at lower,
   have hz := mul_le_mul_of_nonneg_left hT he,
   nlinarith },
 intros z hz, have hr := hR z hz, have hxz := hx z hz,
 have hcub : (R z)^3≤1 := by simpa using pow_le_pow_of_le_left hr.1 hr.2 3,
 have prod := mul_le_mul_of_nonneg_right hcub hxz.1,
 have prod' : (R z)^3*x z≤5/4 := by linarith [hxz.2],
 nlinarith [mul_le_mul_of_nonneg_left prod' he]
end

theorem one_crossing_ratio (R x V w : ℝ → ℝ) (T : ℝ)
 (hr : ∀ z ∈ Icc 0 T, has_deriv_at R (V z) z)
 (hx : ∀ z ∈ Icc 0 T, has_deriv_at x (w z) z)
 (hp : ∀ z ∈ Icc 0 T, 0<x z)
 (hW : ∀ z ∈ Icc 0 T, 0<V z*x z-R z*w z) :
 strict_mono_on (λ z,R z/x z) (Icc 0 T) :=
begin
 have dh : ∀ z ∈ Icc 0 T, has_deriv_at (λ a,R a/x a)
   ((V z*x z-R z*w z)/(x z)^2) z :=
   λ z hz, (hr z hz).div (hx z hz) (ne_of_gt (hp z hz)),
 apply (convex_Icc (0:ℝ) T).strict_mono_on_of_deriv_pos (has_deriv_at.continuous_on dh),
 intros z hz, have h := interior_subset hz, rw [(dh z h).deriv],
 exact div_pos (hW z h) (pow_pos (hp z h) 2)
end

theorem exposure_margin (s : ℝ) (hs : 1/2<s) : 1<2*(3*s-1) := by linarith

theorem edge_commutator {A : Type*} [ring A] (P D C L : A)
 (hl : P*D=L*P) (hr : D*P=P*L) (hcomm : L*(P*C*P)=(P*C*P)*L) :
 P*(D*C-C*D)*P=0 :=
begin
 calc P*(D*C-C*D)*P = (P*D)*C*P-P*C*(D*P) : by noncomm_ring
 ... = L*(P*C*P)-(P*C*P)*L : by rw [hl,hr]; noncomm_ring
 ... = 0 : sub_eq_zero.mpr hcomm
end

theorem casimir_upper (j : ℝ) (hj : 0≤j) :
 ((j+1)*(j+2)-j*(j+1)-2)/2=j ∧
 (j*(j+1)-j*(j+1)-2)/2≤j ∧
 ((j-1)*j-j*(j+1)-2)/2≤j := by {split, ring, constructor; nlinarith}
theorem hessian_lower (j a x k m c : ℝ) (ha : 0≤a) (hx : 0≤x)
 (hm : m≤j) (hc : c≤j) :
 (x-a*j)^2-a^2*j+k ≤ a^2*j*(j+1)+x^2-2*a*x*m-2*a^2*c+k :=
by nlinarith [mul_nonneg (mul_nonneg ha hx) (sub_nonneg.mpr hm),
              mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hc)]
theorem gapped_boson (gap R2 Jinv k : ℝ) (hu : R2≤1) (hj : 0≤Jinv)
 (hk : 2/9≤k) : 2/9-Jinv ≤ gap^2-R2*Jinv+k :=
by nlinarith [sq_nonneg gap,mul_nonneg (sub_nonneg.mpr hu) hj]
def thermal (x : ℝ) := 1+16*x+36*x^2+16*x^3+x^4
theorem neutral_counts : (nat.choose 4 0)^2=1 ∧ (nat.choose 4 1)^2=16 ∧
 (nat.choose 4 2)^2=36 ∧ (nat.choose 4 3)^2=16 ∧ (nat.choose 4 4)^2=1 := by dec_trivial
theorem thermal_miss_positive (x : ℝ) (hx : 0<x) : 0<1/thermal x :=
by {unfold thermal, positivity}
theorem infinite_temperature : 1/thermal 1=(1/70:ℝ) := by norm_num [thermal]
theorem protected_pair_energy (gap k : ℝ) : k*gap+k*gap=2*k*gap := by ring
end cat_falling_fermi_edge
