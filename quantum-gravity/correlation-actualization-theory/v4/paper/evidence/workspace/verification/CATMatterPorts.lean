import tactic
import data.real.sqrt
import analysis.special_functions.trigonometric.basic
import analysis.special_functions.integrals

/- Algebra used in the finite-time material-port argument. All physical
   hypotheses, including occupancy, have to be furnished by the preparation. -/
namespace cat_matter_ports
noncomputable theory

theorem heron_gram (a b c : ℝ) :
 (a+b+c)*(-a+b+c)*(a-b+c)*(a+b-c) =
 (a^2+b^2+c^2)^2-2*(a^4+b^4+c^4) := by ring

theorem purity_criterion (a b c : ℝ) (hc : 0<c) (hcb : c≤b) (hba : b≤a) :
 2*(a^4+b^4+c^4)<(a^2+b^2+c^2)^2 ↔ a<b+c :=
begin
 have hp : 0<a+b+c := by linarith,
 have hq : 0<a-b+c := by linarith,
 have hr : 0<a+b-c := by linarith,
 have hs : 0<(a+b+c)*(a-b+c)*(a+b-c) := mul_pos (mul_pos hp hq) hr,
 have hx : (a^2+b^2+c^2)^2-2*(a^4+b^4+c^4) =
      ((a+b+c)*(a-b+c)*(a+b-c))*(-a+b+c) := by ring,
 split,
 { intro h, have hz : 0<((a+b+c)*(a-b+c)*(a+b-c))*(-a+b+c) := by linarith [hx],
   by_contra hh, push_neg at hh,
   have bad := mul_nonpos_of_nonneg_of_nonpos hs.le (show -a+b+c≤0,by linarith), linarith },
 { intro h, have hz := mul_pos hs (show 0 < -a+b+c, by linarith), linarith [hx] }
end

theorem bell_blocks (a b c r x : ℝ) :
 ((a-r-x)*(a+r-x)-(b-c)^2)*((-a-r-x)*(-a+r-x)-(b+c)^2)
 = ((a-x)^2-r^2-(b-c)^2)*((-a-x)^2-r^2-(b+c)^2) := by ring

theorem focal_parities (a b c r : ℝ) (hr : r^2=a^2-b^2) (hc : 0<c) (hb : c≤b) :
 0<a^2-r^2-(b-c)^2 ∧ a^2-r^2-(b+c)^2<0 :=
begin
 rw [hr], constructor,
 { nlinarith [mul_pos hc (show 0<2*b-c, by linarith)] },
 { nlinarith [mul_pos hc (show 0<2*b+c, by linarith)] }
end

theorem positive_even_gap (a b c x : ℝ) (ha : 0<a) (hb : c≤b) (hc : 0<c)
 (hx : 0≤x) (h : x^2=a^2-2*b*c+c^2) : b*c/(2*a)≤a-x :=
begin
 have hbc : c*c≤b*c := mul_le_mul_of_nonneg_right hb hc.le,
 have hle : x≤a := by {by_contra hz,push_neg at hz,
    nlinarith [mul_pos (sub_pos.mpr hz) (show 0<x+a,by linarith),mul_pos hc (show 0<2*b-c,by linarith)]},
 apply (div_le_iff (show 0<2*a,by linarith)).2,
 nlinarith [sq_nonneg (a-x)]
end

theorem positive_odd_gap (a b c x : ℝ) (ha : 0<a) (hc : 0<c) (hcb : c≤b) (hba : b≤a)
 (hx : 0≤x) (h : x^2=a^2+2*b*c+c^2) : b*c/(2*a)≤x-a :=
begin
 have hle : a≤x := by {by_contra hz,push_neg at hz,
   nlinarith [mul_pos (sub_pos.mpr hz) (show 0<a+x,by linarith),mul_pos hc (show 0<b,by linarith),sq_nonneg c]},
 have hhi : x≤a+c := by {by_contra hz,push_neg at hz,
   nlinarith [mul_pos (sub_pos.mpr hz) (show 0<x+(a+c),by linarith),mul_le_mul_of_nonneg_right hba hc.le]},
 apply (div_le_iff (show 0<2*a,by linarith)).2,
 have hp : 0 ≤ (x-a)*(3*a-x) := mul_nonneg (sub_nonneg.mpr hle) (by linarith),
 nlinarith [hp,sq_nonneg c]
end

theorem spectral_margin (gap error mesh : ℝ) (h : error+mesh<gap) :
 0<gap-error-mesh := by linarith
theorem nonlinear_bounds (k v T w : ℝ) :
 k*v*T^3/6+v*w*T^5/5=v*T*(k*T^2/6+w*T^4/5) := by ring
theorem pauli_double_comm {R : Type*} [ring R] (s t : R)
 (hs : s*s=1) (ht : s*t= -(t*s)) : s*(s*t-t*s)-(s*t-t*s)*s=4*t :=
begin
 have hr : s*t*s= -t := by rw [ht,neg_mul,mul_assoc,hs,mul_one],
 calc s*(s*t-t*s)-(s*t-t*s)*s = (s*s)*t+t*(s*s)-2*(s*t*s) : by noncomm_ring
 ... = 4*t : by {rw [hr,hs,one_mul,mul_one],noncomm_ring}
end
theorem commuting_triples {R : Type*} [ring R] (x y : R) (h : x*y=y*x) :
 x*(x*y-y*x)-(x*y-y*x)*x=0 := by simp [h]

def d00 (s : ℝ) := -1/s^2+2/s
def d01 (s : ℝ) := 3*s^2-3*s
def d10 (s : ℝ) := 2/(3*s^2)-2/(3*s)
def d11 (s : ℝ) := 2*s-s^2
theorem ricci_determinant (s : ℝ) (hs : s≠0) :
 d00 s*d11 s-d01 s*d10 s=1 :=
by { unfold d00 d01 d10 d11, field_simp [hs]; ring }
theorem ricci_relative_trace (s : ℝ) (hs : s≠0) :
 d00 s+d11 s+(1-s^3)*d10 s=2-(s+1/s-2)^2/3 :=
by { unfold d00 d10 d11, field_simp [hs]; ring }
theorem at_six : 2-((6:ℝ)+1/6-2)^2/3= -409/108 := by norm_num
theorem trace_threshold (a : ℝ) : 2-a^2/3 < -2 ↔ 12<a^2 := by split; intro h; linarith
theorem ricci_powers : ((2:ℝ)/3)*(2/3-1)= -2/9 ∧
 ((1:ℝ)/3)*(1/3-1)= -2/9 := by norm_num

theorem chord_acceptance (mu y d : ℝ) (hy : 0<y) :
 1+y^2-2*y*mu<d^2 ↔ (1+y^2-d^2)/(2*y)<mu :=
begin rw [div_lt_iff (show 0<2*y,by linarith)], split; intro h; nlinarith end
theorem cap_area : (1-((1+(4/5:ℝ)^2-(2/5)^2)/(2*(4/5))))/2=3/80 := by norm_num
theorem cap_count (n : ℕ) (h : 80≤3*n) : 27≤n := by omega
theorem retarded_times (son soff chord dwell : ℝ) :
 1+dwell<son-chord/2 ∧ soff-chord/2<1 ↔
 2*(soff-1)<chord ∧ chord<2*(son-1-dwell) := by split; rintro ⟨a,b⟩; constructor; linarith
theorem robust_annulus (lo hi y delta d : ℝ) (h : y*delta<(hi-lo)/2)
 (hlo : (hi+lo)/2-y*delta≤d) (hhi : d≤(hi+lo)/2+y*delta) : lo<d ∧ d<hi :=
by constructor; linarith
theorem net_error (p q c : ℝ) (hp : 0≤p*q) (hu : p*q≤1) (hc : c≤1) :
 p*q*(1-c)≤1-c := by nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hc)]
theorem general_area (lo hi y : ℝ) (hy : y≠0) :
 ((1+y^2-lo^2)/(2*y)-(1+y^2-hi^2)/(2*y))/2=(hi^2-lo^2)/(4*y) :=
by {field_simp [hy]; ring}
theorem meshed_preparation (s1 s2 s3 t h e : ℝ) (g : h+e<t*s2*s3/(2*s1)) :
 0<t*s2*s3/(2*s1)-h-e := by linarith
theorem in_out_threshold (s d : ℝ) : 1<s-d/2 ↔ d<2*(s-1) :=
by split; intro h; linarith
theorem inclusive_weight {R : Type*} [monoid R] (z w U V U' V' : R)
 (hU : U'*U=1) (hV : V'*V=1) : (z*U'*V')*(V*U*w) = z*w :=
begin
 calc (z*U'*V')*(V*U*w) = z*(U'*(V'*V)*U)*w : by simp only [mul_assoc]
 ... = z*w : by rw [hV,mul_one,hU,mul_one]
end
theorem mixing_overlap (p q r a : ℝ) (he : 2-2*a≤r^2) (hr : r^2≤2)
 (ha : a^2≤p) (h : q=(1-r^2/2)^2) : q≤p :=
begin
 have hn : 0≤a-(1-r^2/2) := by linarith,
 have hs : 0≤a+(1-r^2/2) := by linarith,
 rw [h], calc (1-r^2/2)^2 ≤ a^2 : by {rw [pow_two (1-r^2/2),pow_two a], exact mul_self_le_mul_self (show 0≤1-r^2/2,by linarith) (show 1-r^2/2≤a,by linarith)}
 ... ≤ p : ha
end
theorem taylor_residual_bound (E R L t2 : ℝ) (h : 2*E≤t2*(R+L*E))
 (hL : 0<2-L*t2) : E≤R*t2/(2-L*t2) :=
by {rw [le_div_iff hL], nlinarith only [h]}

theorem signed_spin_contrast (b x : ℝ) :
 b*((1+x)/2)^2-b*((1-x)/2)^2=b*x := by ring
theorem unsigned_average (b x : ℝ) : (b*x+b*(-x))/2=0 := by ring
theorem tag_success (b : ℝ) : (1+b/2)/2=1/2+b/4 := by ring
theorem radial_hemi_mean : (∫ x in (0:ℝ)..1, x) = 1/2 :=
by { rw [integral_id], norm_num }
theorem six_axis_bias (b : ℝ) (hb : 0≤b) :
 (abs b+abs (-b)+0+0+0+0)/6=b/3 := by {rw [abs_neg, abs_of_nonneg hb], ring}

/-- Any charge event is a physical test on the receiver when the source is fixed.
    Rotating both preparations preserves probabilities for a scalar event. -/
def reference_distance {R : Type*} (tests : set (R → ℝ)) (r r' : R) : ℝ :=
 Sup ((λ f : R → ℝ, abs (f r-f r')) '' tests)

theorem rotational_reference_bound {S R Z : Type*} (p : S → R → Z → ℝ)
 (s s' : S) (r r' : R) (tests : set (R → ℝ))
 (unit_range : ∀ (f : R → ℝ), f ∈ tests → ∀ (t : R), 0 ≤ f t ∧ f t ≤ 1)
 (physical : ∀ z, (λ t, p s t z) ∈ tests)
 (covariant : ∀ z, p s' r z = p s r' z) (z : Z) :
 abs (p s r z-p s' r z) ≤ reference_distance tests r r' :=
begin
 rw [covariant z], unfold reference_distance,
 apply le_cSup,
 { use (1:ℝ), rintro x ⟨f,hf,rfl⟩,
   rcases unit_range f hf r with ⟨h0,h1⟩,
   rcases unit_range f hf r' with ⟨k0,k1⟩,
   exact abs_le.mpr ⟨by linarith, by linarith⟩ },
 { exact ⟨(λ t, p s t z),physical z,rfl⟩ }
end

theorem antipodal_charge (b f : ℝ) :
 f*b-(1-f)*b=b*(2*f-1) := by ring

def qqdiag (a b c : ℝ) : ℝ × ℝ × ℝ :=
 ((9*a+3*b-12*c)/6,(3*a+9*b-12*c)/6,(-12*a-12*b+24*c)/6)
theorem tensor_diagonal_modes (a b c : ℝ) :
 qqdiag a b c = ((a-b)/2-(2*c-a-b),-(a-b)/2-(2*c-a-b),2*(2*c-a-b)) :=
by {unfold qqdiag, congr' 1, ring, congr' 1; ring}
theorem tensor_transverse (x y : ℝ) : 3*(x+y)/6=(x+y)/2 := by ring
theorem tensor_mixed (x y : ℝ) : -12*(x+y)/6= -4*((x+y)/2) := by ring
theorem antisymmetric_dark (q x : ℝ) : q*(x+(-x))=0 := by ring
theorem antiparallel_tensor : qqdiag (1/2) (1/2) 0 = (1,1,-2) := by norm_num [qqdiag]
theorem weak_opposite : (1:ℝ)^2+1^2+(-2)^2=6 := by norm_num
theorem antiparallel_weight (c s : ℝ) (h : 6*c^2=1) :
 c^2*s^2=s^2/6 := by rw [show c^2=1/6,by linarith]; ring
theorem inclusive_polarization (p m z same opposite middle : ℝ) :
 (p*same+m*opposite+z*middle)-(m*same+p*opposite+z*middle)
 =(p-m)*(same-opposite) := by ring
theorem dark_weight_bound (p bright : ℝ) (hu : bright≤1)
 (h : p=bright/2) : p≤1/2 := by linarith
theorem contrast_crosses (a b : ℝ) (p q : ℝ → ℝ) (hab : a≤b)
 (hp : continuous_on p (set.Icc a b)) (hq : continuous_on q (set.Icc a b))
 (lo : p a<q a) (hi : q b<p b) :
 ∃ t ∈ set.Icc a b, p t=q t :=
begin
 have z : (0:ℝ) ∈ set.Icc ((p-q) a) ((p-q) b) :=
     ⟨sub_nonpos.mpr lo.le,sub_nonneg.mpr hi.le⟩,
 obtain ⟨t, ht, he⟩ := intermediate_value_Icc hab (hp.sub hq) z,
 exact ⟨t,ht,sub_eq_zero.mp he⟩
end

def first_lobe_factor (c : ℝ) : ℝ := 2*c*(4*c^2-1)*(4*c^2-3)
theorem six_sine_factor (x : ℝ) :
 real.sin (6*x)=real.sin x*first_lobe_factor (real.cos x) :=
begin
 have hs : real.sin x ^ 2 = 1-real.cos x ^ 2 := by linarith [real.sin_sq_add_cos_sq x],
 have h3 : real.sin (3*x) = real.sin x*(4*real.cos x^2-1),
 { rw [real.sin_three_mul,show real.sin x^3=real.sin x*real.sin x^2,by ring,hs], ring },
 rw [show 6*x=2*(3*x),by ring,real.sin_two_mul,h3,real.cos_three_mul],
 unfold first_lobe_factor, ring
end
theorem first_lobe_strict (c d : ℝ) (hc : 0<c) (cd : c<d) (h : 3<4*c^2) :
 first_lobe_factor c < first_lobe_factor d :=
begin
 have hsq : c^2<d^2 := by nlinarith [mul_pos (sub_pos.mpr cd) (show 0<d+c,by linarith)],
 have h1 : 0<4*c^2-1 := by linarith,
 have h2 : 0<4*c^2-3 := by linarith,
 have h3 : 0<2*d := by linarith,
 unfold first_lobe_factor,
 calc 2*c*(4*c^2-1)*(4*c^2-3) < 2*d*(4*c^2-1)*(4*c^2-3) :
        mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right (by linarith) h1) h2
 ... < 2*d*(4*d^2-1)*(4*c^2-3) :
        mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left (by linarith) h3) h2
 ... < 2*d*(4*d^2-1)*(4*d^2-3) :
        mul_lt_mul_of_pos_left (by linarith) (mul_pos h3 (by linarith))
end

end cat_matter_ports
