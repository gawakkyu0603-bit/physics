import tactic
import analysis.calculus.mean_value
import analysis.calculus.deriv.inv
import analysis.calculus.deriv.pow
import analysis.special_functions.trigonometric.basic
import data.complex.basic
import data.polynomial.ring_division
import measure_theory.integral.interval_integral

noncomputable theory
open_locale big_operators
namespace compact_matrix_radiation

-- Angular averages for a trace-free quadrupole in three spatial dimensions.
theorem polarization_weights :
 (7/15-(1/2)*(2/15):ℚ)=2/5 ∧
 ((1/2-1/8)*(2/15):ℚ)=1/20 ∧
 (2*(1/3-2/15):ℚ)=2/5 ∧ ((1+1/8)*(2/15):ℚ)=3/20 :=
by norm_num
theorem lifted_norm (tt mixed longitudinal : ℝ) (h : tt+2*mixed+longitudinal=1) :
 tt+mixed+mixed+longitudinal=1 := by linarith
theorem trace_lift (t u : ℝ) (h : t+u=0) : (t+u)^2=0 := by rw [h]; norm_num
theorem plane_tensor_power (I w : ℝ) :
 ((2*w)^6*I^2/2)/5=(32/5)*I^2*w^6 := by ring
theorem dipole_acceleration (u v w : ℝ) :
 (u^2+v^2+w^2)^2+4*(u^2*v^2+v^2*w^2+w^2*u^2)=
 u^4+v^4+w^4+6*(u^2*v^2+v^2*w^2+w^2*u^2) := by ring
theorem equal_dipole (w : ℝ) :
 (w^2+w^2+w^2)^2+4*(w^2*w^2+w^2*w^2+w^2*w^2)=21*w^4 := by ring
theorem threeform_norm (g I w : ℝ) :
 4*g*(I^2*w^2/2)*21*w^4=42*g*I^2*w^6 := by ring
theorem dipole_bands : ((1:ℚ)^4*3/4+3^4/4)=21 := by norm_num
theorem boson_balance (g I w : ℝ) :
 3*(16*g*I^2*w^6)+42*g*I^2*w^6=90*g*I^2*w^6 := by ring
theorem tensor_share : (32/5/90:ℚ)=16/225 := by norm_num
theorem bosonic_split :
 (32/5+4/5+32/5+12/5+32+28+14:ℚ)=90 := by norm_num
theorem threeform_branch : ((2/3:ℚ)*42=28) ∧ ((1/3:ℚ)*42=14) := by norm_num
theorem plane_virial (I w : ℝ) : 3*I*w^2/2+3*I*w^2/4=9*I*w^2/4 := by ring
theorem three_spin_chirp (a b c l m n : ℝ)
 (h1 : l=2*a+(b+c)/2) (h2 : m=2*b+(a+c)/2) (h3 : n=2*c+(a+b)/2) :
 (b+c)/2=(-l+2*m+2*n)/9 := by linarith
theorem selective_branches :
 (1/9:ℚ)>0 ∧ ((9/8-2*(5/2)-2*(5/2))/9:ℚ)= -71/72 ∧
 ((5/2-2*(5/2)-2*(5/2))/9:ℚ)= -5/6 := by norm_num
theorem radiation_chirp (I w g dw : ℝ) (hi : I≠0) (hw : w≠0)
 (balance : 9*I*w*dw= -90*g*I^2*w^6) : dw= -10*g*I*w^5 :=
begin
 apply (mul_left_cancel₀ (show 9*I*w≠0, by norm_num [hi,hw])),
 calc (9*I*w)*dw= -90*g*I^2*w^6 : balance
 ... =(9*I*w)*(-10*g*I*w^5) : by ring
end
theorem initial_all_scaled : ((-10:ℚ)*5/32)= -25/16 := by norm_num
theorem tensor_spindown (x b : ℝ) (hb : b≠0) (h : x+2≠0) (hb6 : b^6*(1+x)=2) :
 (b^3*(1-x/(2*(1+x))))*(-4*x^2/(2+x)) = -x^2*b^9 :=
begin
 have hp : 1+x≠0 := by {intro k,rw [k,mul_zero] at hb6,norm_num at hb6},
 have hp2 : 2+x≠0 := by simpa [add_comm] using h,
 field_simp [hp,hp2],
 linear_combination (-2*b^3*x^2*(x+2))*hb6
end
theorem secular_clock (a w : ℝ) (ha : a≠0) (hw : w≠0) :
 (-(6:ℝ)/(60*a*w^7))*w= -(5:ℝ)/(50*a*w^6) :=
by {field_simp [ha,hw],ring}
theorem weak_crossing_coefficient (g I w r : ℝ) (hg : g≠0) (hi : I≠0)
 (hw : w≠0) (hr : r≠0) :
 (3/(8*w^2))*(8*g*I*w^4/r)^2*real.pi/(10*g*I*w^5)=
 (12*real.pi/5)*g*(I*w)/r^2 :=
by {field_simp [hg,hi,hw,hr],ring}
theorem positive_chirp_energy (I w g : ℝ) (hi : 0<I) (hw : 0<w) (hg : 0<g) :
 0<90*g*I^2*w^6 := by positivity
theorem inclination (c : ℝ) :
 ((1+c^2)/2)^2-c^2=(1-c^2)^2/4 := by ring
theorem signed_record (a b : ℝ) (hn : a^2+b^2≠0) :
 (a^2+b^2)/2*(1-(a^2-b^2)/(a^2+b^2))=b^2 :=
by {field_simp [hn],ring}
theorem helicity_erasures (eta : ℝ) : (4*(1-eta)+2*eta)/4=1-eta/2 := by ring
theorem helicity_two_changes_sign (a b : ℝ) : (a+b)^2-(a-b)^2=4*a*b := by ring
theorem exactly_zero_at_equator : ((0:ℝ)^2)=0 := by norm_num
theorem probability_union (p q : ℝ) : 1-(1-p)*(1-q)=p+q-p*q := by ring
theorem collection_upper (C g J M r m : ℝ) (hg : 0<g) (hr : 0<r) (hm : 0<m)
 (hj : 0≤J) (h : 2*g*M*m/r≤C) :
 M*(12*real.pi/5*g*J/r^2)≤6*real.pi/5*C*J/(m*r) :=
begin
 have cut : M ≤ C*r/(2*g*m) :=
   (le_div_iff (by positivity : 0<2*g*m)).2 (by linarith only [(div_le_iff hr).1 h]),
 have hpi : 0 < real.pi := real.pi_pos,
 have p : 0≤12*real.pi/5*g*J/r^2 := by positivity,
 refine le_trans (mul_le_mul_of_nonneg_right cut p) (le_of_eq _),
 field_simp [ne_of_gt hg,ne_of_gt hr,ne_of_gt hm],ring
end

-- Four-dimensional radial tests. E is the constant affine null energy.
theorem radial_null_sign (E R Rpp : ℝ) (he : E≠0) (hr : 0<R) (hpp : 0<Rpp) :
 -2*E^2*Rpp/R<0 :=
by {apply div_neg_of_neg_of_pos _ hr,have h := mul_pos (sq_pos_of_ne_zero _ he) hpp,linarith}
theorem funnel_positive (Q r : ℝ) (hq : Q≠0) (hr : 0<r) :
 0<3*Q^2*r^2/(r^4+Q^2)^2 := by positivity
theorem four_charge_variance (a b c d : ℝ) :
 (a^2+b^2+c^2+d^2)/4-((a+b+c+d)/4)^2=
 ((a-b)^2+(a-c)^2+(a-d)^2+(b-c)^2+(b-d)^2+(c-d)^2)/16 := by ring
theorem four_charge_concave (a b c d : ℝ) :
 ((a+b+c+d)/4)^2-(a^2+b^2+c^2+d^2)/4≤0 :=
begin
 have h:=four_charge_variance a b c d,
 linarith [sq_nonneg (a-b),sq_nonneg (a-c),sq_nonneg (a-d),sq_nonneg (b-c),
           sq_nonneg (b-d),sq_nonneg (c-d)]
end
theorem neutral_potential (s r : ℝ) (hr : r≠0) :
 (1-s/r)*(1/r^2-3*s/r^3)+(-1/r+3*s/(2*r^2))^2+
 2*(1-s/r)/r*(-1/r+3*s/(2*r^2))-2*(1-s/r)/r^2 =
 -2/r^2+9*s^2/(4*r^4) :=
by {field_simp [hr],ring}
theorem horizon_offset (s : ℝ) (hs : s≠0) :
 -2/s^2+9*s^2/(4*s^4)=(1/(2*s))^2 := by {field_simp [hs],ring}
theorem unequal_endpoint (k origin : ℝ) (hk : 0<k) :
 origin+k^2≠origin :=
by {have ht:=sq_pos_of_pos hk,linarith}
theorem family_mass_coefficient (r fp fpp V s t : ℝ) (hr : r≠0) (hst : s≠t)
 (hs : V=(1-s/r)*fpp+s*fp/r^2) (ht : V=(1-t/r)*fpp+t*fp/r^2) :
 fp=r*fpp :=
begin
 have hh : r*((s-t)*(fp-r*fpp))=0,
 {field_simp [hr] at hs ht,linear_combination ht-hs},
 have h := (mul_eq_zero.mp hh).resolve_left hr,
 have y:fp-r*fpp=0 := (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hst),
 linarith
end
theorem two_derivative_target (r fp fpp V s Z : ℝ) (hr : r≠0)
 (hc : fp=r*fpp) (hs : V=(1-s/r)*fpp+s*fp/r^2) (hz : Z=fpp) :
 V=Z :=
by {rw [hs,hz,hc],field_simp [hr],ring}
theorem candidate_reproduces (r s c : ℝ) (hr : r≠0) :
 (1-s/r)*(2*c)+s*(2*c*r)/r^2=2*c := by {field_simp [hr],ring}
theorem flux_exchange (F rho x a : ℝ) (h : F=rho*x+a) : F-a=rho*x :=
by linarith

-- For a finite Kraus family, an input of zero total weight has no hidden output.
theorem each_zero_of_zero_weight {ι : Type*} [fintype ι] (w : ι → ℝ)
 (hw : ∀ i, 0 ≤ w i) (hz : ∑ i, w i = 0) (i : ι) : w i = 0 :=
begin
 classical,
 exact (finset.sum_eq_zero_iff_of_nonneg (λ j hj, hw j)).mp hz i (finset.mem_univ i)
end

-- If every input pure state on a charge sector survives its given port isometry,
-- the range-one condition on the chosen basis column and on each pair sum gives
-- these two amplitude relations for each Kraus matrix after pulling the port back.
theorem minimally_disturbing_matrix {ι : Type*} [decidable_eq ι]
 (r : ι) (M : ι → ι → ℂ)
 (basis_column : ∀ j, ∃ b : ℂ, ∀ k, M k j = if k=j then b else 0)
 (pair_sum : ∀ i j, i≠j → ∃ b : ℂ, M i i+M i j=b ∧ M j i+M j j=b) :
 ∃ b : ℂ, ∀ i j, M i j=if i=j then b else 0 :=
begin
 have off : ∀ i j, i≠j → M i j=0,
 { intros i j hij, rcases basis_column j with ⟨c,hc⟩, simpa [hij] using hc i },
 refine ⟨M r r, _⟩,
 intros i j, by_cases h : i=j,
 { subst j, simp only [if_pos rfl], by_cases hr : i=r,
   { rw [hr] },
   { rcases pair_sum i r hr with ⟨c,hi,hj⟩,
     rw [off i r hr,add_zero] at hi,
     rw [off r i (ne.symm hr),zero_add] at hj, exact hi.trans hj.symm } },
 { simp only [if_neg h], exact off i j h }
end

theorem scalar_family_channel {ι : Type*} [fintype ι] (w : ι → ℂ) (x : ℂ)
 (h : ∑ i, w i = 1) : ∑ i, w i*x=x :=
by rw [←finset.sum_mul,h,one_mul]

-- A pure column direction for each Kraus matrix follows by testing total support
-- on any linear functional that annihilates the target pure vector.
theorem pure_output_support {ι : Type*} [fintype ι] (amplitude : ι → ℂ)
 (h : ∑ i, complex.norm_sq (amplitude i)=0) (i : ι) : amplitude i=0 :=
begin
 have hi := each_zero_of_zero_weight (λ j, complex.norm_sq (amplitude j)) (λ j, complex.norm_sq_nonneg (amplitude j)) h i,
 exact complex.norm_sq_eq_zero.mp hi
end

theorem rest_mass_recoil (m gap energy : ℝ) (hm : m≠0)
 (shell : (m+energy)^2-energy^2=(m+gap)^2) :
 energy=gap+gap^2/(2*m) :=
by {field_simp [hm],nlinarith only [shell]}

theorem remote_receipt_sum {ι : Type*} [fintype ι] (p : ι → ℂ) (x : ℂ)
 (hn : ∑ i,p i=1) : ∑ i,p i*x=x := scalar_family_channel p x hn

theorem readable_sign_bound (p quiet yes fidelity : ℝ)
 (hp : 0≤p) (hq : p≤1) (hqf : quiet≤1) (hy : yes≤1/2)
 (mix : fidelity=(1-p)*quiet+p*yes) : fidelity≤1-p/2 :=
begin
 have h1 := mul_le_mul_of_nonneg_left hqf (sub_nonneg.mpr hq),
 have h2 := mul_le_mul_of_nonneg_left hy hp, linarith
end

theorem degeneracy_and_scalar_bound (a b s : ℝ) (ha : a=s) (hb : b=s) : a=b :=
ha.trans hb.symm

-- E is the pullback of the interior effect and the last summand its mean on the
-- positive remainder, in the eigenbasis of E (valid also for noncommuting inputs).
theorem support_floor {ι : Type*} [fintype ι] (e a b : ι → ℝ) (β : ℝ)
 (he : ∀ i, 0≤e i) (hd : ∀ i, β*a i≤b i) :
 β*(∑ i,e i*a i) ≤ ∑ i,e i*b i :=
begin
 classical, rw [finset.mul_sum],
 apply finset.sum_le_sum, intros i hi,
 calc β*(e i*a i)=e i*(β*a i) : by ring
 ... ≤e i*b i : mul_le_mul_of_nonneg_left (hd i) (he i)
end

theorem exact_route_support {ι : Type*} [fintype ι] (e a b : ι → ℝ)
 (he : ∀ i, 0≤e i ∧ e i≤1) (ha : ∀ i, 0≤a i) (hb : ∀ i, 0≤b i)
 (pass : ∑ i,(1-e i)*a i=0) (stop : ∑ i,e i*b i=0) (i : ι) : a i*b i=0 :=
begin
 have x := each_zero_of_zero_weight (λ j, (1-e j)*a j) (λ j, mul_nonneg (sub_nonneg.mpr (he j).2) (ha j)) pass i,
 have y := each_zero_of_zero_weight (λ j, e j*b j) (λ j, mul_nonneg (he j).1 (hb j)) stop i,
 change (1-e i)*a i=0 at x,
 change e i*b i=0 at y,
 rcases mul_eq_zero.mp x with hx|hx,
 { have hz : e i=1 := by linarith, rw [hz,one_mul] at y, rw [y,mul_zero] },
 { rw [hx,zero_mul] }
end

theorem matched_ratio (d : ℝ) (k : ℕ) (hd : d≠0) :
 (1/d)^k*(1/d)^k=(1/d^2)^k :=
by {rw [←mul_pow],congr' 1,field_simp [hd],ring}

theorem ten_pairs : ((1/2:ℚ)^10)=1/1024 := by norm_num
-- A finite pure output is on its assigned input ray exactly when its two-by-two
-- row minors against that ray have zero squared norm. Positivity precludes
-- cancellation between Kraus outcomes.
def unit_column {ι : Type*} [decidable_eq ι] (j : ι) (k : ι) : ℂ :=
if k=j then 1 else 0

theorem pure_instrument_kraus_scalar {ι κ : Type*} [decidable_eq ι] [fintype κ]
 (r : ι) (K : κ → ((ι → ℂ) →ₗ[ℂ] (ι → ℂ)))
 (pure : ∀ (v : ι → ℂ) i j, ∑ t, complex.norm_sq
    (v i*K t v j - v j*K t v i) = 0) (t : κ) :
 ∃ b : ℂ, ∀ i j, K t (unit_column j) i=if i=j then b else 0 :=
begin
 have minor : ∀ (v : ι → ℂ) i j, v i*K t v j-v j*K t v i=0,
 { intros v i j, exact @pure_output_support κ _ (λ s : κ, v i*K s v j-v j*K s v i) (pure v i j) t },
 have off : ∀ i j, i≠j → K t (unit_column j) i=0,
 { intros i j hij, have h:=minor (unit_column j) j i,
   simpa [unit_column,hij] using h },
 apply minimally_disturbing_matrix r (λ i j, K t (unit_column j) i),
 { intro j, refine ⟨K t (unit_column j) j, _⟩,
   intro i, by_cases h : i=j,
   { subst i, simp }, { simpa [h] using (off i j h) } },
 { intros i j hij,
   have h:=minor (unit_column i+unit_column j) i j,
   rw [linear_map.map_add] at h,
   simp only [pi.add_apply] at h,
   have vi : unit_column i i + unit_column j i=1 := by simp [unit_column,hij],
   have vj : unit_column i j + unit_column j j=1 := by simp [unit_column,ne.symm hij],
   rw [vi,vj,one_mul,one_mul,sub_eq_zero] at h,
   exact ⟨_,rfl,h⟩ }
end

-- Partial trace for an arbitrary entangled input. i,j label the local
-- subsystem. C is the contraction of the Kraus family, summed over the
-- outcomes and local final states. x contains arbitrary remote matrix entries.
theorem local_channel_remote_entry {ι : Type*} [fintype ι] [decidable_eq ι]
 (C x : ι → ι → ℂ) (complete : ∀ i j, C i j=if i=j then 1 else 0) :
 (∑ i, ∑ j, C i j*x i j) = ∑ i,x i i :=
begin
 classical,
 apply finset.sum_congr rfl, intros i hi,
 calc (∑ j, C i j*x i j) = ∑ j, if i=j then x i j else 0 :
   finset.sum_congr rfl (λ j hj, by { rw [complete], split_ifs; simp })
 ... = x i i : by simp
end

-- Integrate F'=r F'' on each positive compact interval. hF is the ordinary
-- derivative of F, hP the derivative of its first derivative P.
theorem area_action_on_interval (F P D : ℝ → ℝ) (a b : ℝ) (ha : 0<a)
 (hF : ∀ x ∈ set.Icc a b, has_deriv_at F (P x) x)
 (hP : ∀ x ∈ set.Icc a b, has_deriv_at P (D x) x)
 (eqn : ∀ x ∈ set.Icc a b, P x=x*D x) :
 ∃ c d : ℝ, ∀ x ∈ set.Icc a b, F x=c*x^2+d :=
begin
 let k : ℝ := P a/a,
 have hn : ∀ (x : ℝ), x ∈ set.Icc a b → x≠0 :=
   λ x hx, ne_of_gt (lt_of_lt_of_le ha hx.1),
 have div_rule : ∀ x ∈ set.Icc a b, has_deriv_at (λ y, P y/y) 0 x,
 { intros x hx, have hd := (hP x hx).div (has_deriv_at_id x) (hn x hx),
   change has_deriv_at (λ y, P y/y) ((D x*x-P x*1)/x^2) x at hd,
   convert hd using 1, rw [eqn x hx], ring },
 have radius_constant : ∀ x ∈ set.Icc a b, P x/x=k,
 { apply eq_of_has_deriv_right_eq (λ x hx, (div_rule x (set.mem_Icc_of_Ico hx)).has_deriv_within_at)
          (λ x hx, (has_deriv_at_const x k).has_deriv_within_at),
   { exact λ x hx, (div_rule x hx).continuous_at.continuous_within_at },
   { exact continuous_const.continuous_on },
   { refl } },
 let d : ℝ := F a-k/2*a^2,
 have poly : ∀ x, has_deriv_at (λ y:ℝ, k/2*y^2+d) (k*x) x,
 { intro x, have hd := ((has_deriv_at_pow 2 x).const_mul (k/2)).add_const d,
   convert hd using 1; simp; ring },
 refine ⟨k/2,d,_⟩,
 apply eq_of_has_deriv_right_eq (λ x hx, (hF x (set.mem_Icc_of_Ico hx)).has_deriv_within_at),
 { intros x hx, have hi := set.mem_Icc_of_Ico hx,
   have hh := (div_eq_iff (hn x hi)).mp (radius_constant x hi),
   change has_deriv_within_at (λ y:ℝ, k/2*y^2+d) (P x) (set.Ici x) x,
   rw [hh], exact (poly x).has_deriv_within_at },
 { exact λ x hx, (hF x hx).continuous_at.continuous_within_at },
 { exact λ x hx, (poly x).continuous_at.continuous_within_at },
 { dsimp [d],ring }
end

-- Finite-clock trace factors and the spacelike duality are separate limits.
theorem clock_commutator_entry (k l h : ℤ) (a : ℂ) (hkl : k-l=h) :
 (k:ℂ)*a-a*(l:ℂ)=(h:ℂ)*a :=
by {subst h,push_cast,ring}

theorem clock_sample (K : ℝ) (hK : K≠0) :
 (5/8)*(1-1/K)+(1/8)*(1-2/K)=3/4-7/(8*K) :=
by {field_simp [hK],ring}

theorem dual_charge_norm (l r g m n : ℝ) (hl : l≠0) (hr : r≠0) (hg : g≠0) :
 (m/r)^2+(n/(g*l))^2=((l^2/r)/l^2)^2*(m^2+n^2/(g*l/r)^2) :=
by {field_simp [hl,hr,hg],ring}

theorem material_charge_pairing (a b c d p q m n : ℤ) (det : a*d-b*c=1) :
 (a*p+b*q)*(c*m+d*n)-(c*p+d*q)*(a*m+b*n)=p*n-q*m :=
by {linear_combination (p*n-q*m)*det}

theorem primitive_bilinear_readout (a b c d : ℤ)
 (rotate : a=d ∧ b= -c) (shear : a+b=b) :
 a=0 ∧ d=0 ∧ c= -b :=
by {rcases rotate with ⟨h1,h2⟩,repeat {split};linarith}

-- Any parametrized arc containing infinitely many distinct complex points
-- has a strictly positive number-band Born weight for a nonzero polynomial.
theorem circle_arc_has_weight (p : polynomial ℂ) (hp : p≠0) (z : ℝ → ℂ)
 (a b : ℝ) (hab : a<b) (hinf : (z '' set.Icc a b).infinite)
 (cont : continuous_on (λ x, complex.norm_sq (p.eval (z x))) (set.Icc a b)) :
 0 < ∫ x in a..b, complex.norm_sq (p.eval (z x)) :=
begin
 have hw : ∃ x ∈ set.Icc a b, p.eval (z x)≠0,
 { by_contra h, push_neg at h, apply hp,
   apply polynomial.eq_zero_of_infinite_is_root,
   refine set.infinite.mono _ hinf, rintro y ⟨x,hx,rfl⟩, exact h x hx },
 obtain ⟨x,hx,hn⟩ := hw,
 have good : 0<complex.norm_sq (p.eval (z x)) :=
   lt_of_le_of_ne (complex.norm_sq_nonneg _) (ne.symm (mt complex.norm_sq_eq_zero.mp hn)),
 have cmp := interval_integral.integral_lt_integral_of_continuous_on_of_le_of_exists_lt hab
  (show continuous_on (λ t:ℝ, (0:ℝ)) (set.Icc a b), from continuous_const.continuous_on)
  cont (λ t ht, complex.norm_sq_nonneg _) ⟨x,hx,good⟩,
 simpa using cmp
end

theorem visibility_conservative (v ideal p : ℝ) (hideal : ideal≤1) (hp : p≤1)
 (h : v=ideal*(1-p)) : p≤1-v :=
by {have w:=mul_le_mul_of_nonneg_right hideal (sub_nonneg.mpr hp),linarith}

end compact_matrix_radiation
