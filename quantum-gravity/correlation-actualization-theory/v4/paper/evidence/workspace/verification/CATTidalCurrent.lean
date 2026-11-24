import analysis.special_functions.integrals
import analysis.calculus.mean_value
import analysis.inner_product_space.basic
import tactic

noncomputable theory
open measure_theory set
open_locale big_operators
namespace cat_tidal_current

-- Subselecting a history can never populate a different conserved flux.
theorem history_in_flux {ι V : Type*} (P : V → V) (K : ι → V → V)
 (comm : ∀ i v, P (K i v)=K i (P v)) (ops : list ι) (v : V) (sharp : P v=v) :
 P (ops.foldl (λ w i, K i w) v)=ops.foldl (λ w i, K i w) v :=
begin
 induction ops with i rest ih generalizing v, {exact sharp},
 exact ih (K i v) (by rw [comm,sharp])
end

theorem repeated_geometry {ι V : Type*} [nonempty ι] (shape : V → Prop) (v : V) :
 (∀ i : ι, shape v) ↔ shape v :=
⟨λ h, h (classical.choice (by apply_instance : nonempty ι)), λ h i,h⟩

theorem common_scale {ι V : Type*} (eligible : ι → V → Prop) (v : V)
 (all : ∀ i,eligible i v) {κ : Type*} (tuple : κ → ι) : ∀ j,eligible (tuple j) v :=
λ j,all (tuple j)

-- All suffixes whose member fluxes allow a specified common subspace.
theorem containing_tuple_count {A : Type*} [fintype A] (m : ℕ) (allow : A → Prop)
 [decidable_pred allow] :
 fintype.card (fin m → {a : A // allow a}) = fintype.card {a : A // allow a}^m :=
by simp [fintype.card_fun]

theorem incidence_subtraction {A : Type*} (eligible : finset A) (strict : A → Prop)
 [decidable_pred strict] :
 (eligible.filter (not ∘ strict)).card = eligible.card-(eligible.filter strict).card :=
begin
 have h : (eligible.filter strict).card+(eligible.filter (not ∘ strict)).card=eligible.card :=
   finset.filter_card_add_filter_neg_card_eq_card strict,
 omega
end

-- The integer weights come from the external enumeration of rational kernels.
-- Each additional marked layer multiplies the contribution of a support by its size.
def shape_tuples (n : ℕ) : ℤ :=
 1440*4^n+96*8^n+96*12^n-12*64^n+12*80^n-2*672^n+3*1840^n

theorem anchored_to_unanchored (m : ℕ) : shape_tuples (m+1) =
 5760*4^m+768*8^m+1152*12^m-768*64^m+960*80^m-1344*672^m+5520*1840^m :=
by simp only [shape_tuples,pow_succ]; ring

theorem three_layer_shapes : shape_tuples 3=18084888576 := by norm_num [shape_tuples]

theorem two_flux_witness {F V : Type*} (allowed : F → V → Prop) (scale : V → Prop)
 (f g : F) (shared : ∀ v : V, allowed f v → allowed g v → scale v)
 {I : Type*} (tuple : I → F) (i j : I) (hi : tuple i=f) (hj : tuple j=g)
 (v : V) (all : ∀ k, allowed (tuple k) v) : scale v :=
shared v (by simpa [hi] using all i) (by simpa [hj] using all j)

theorem missing_flux_bound (prob : ℕ → ℝ) (c : ℝ) (hc : 0≤c) (start : prob 0≤1)
 (step : ∀ n, prob (n+1)≤c*prob n) : ∀ n,prob n≤c^n
| 0 := by simpa using start
| (n+1) := by simpa [pow_succ,mul_comm] using
 ((step n).trans (mul_le_mul_of_nonneg_left (missing_flux_bound n) hc))

-- Pair the two opposite longitudinal momenta before integrating the filled sea.
theorem paired_velocity (p d r v parallel perpendicular : ℝ) (hr : r≠0) :
 v*((p*parallel-d*perpendicular)/r)+v*((-p*parallel-d*perpendicular)/r)
 =(-v*d/r^2)*(2*r*perpendicular) := by field_simp [hr]; ring

theorem finite_time_transport (spin rate : ℝ → ℝ) (a b factor : ℝ)
 (hd : ∀ t ∈ uIcc a b, has_deriv_at spin (rate t) t)
 (int : interval_integrable rate volume a b) :
 (∫ t in a..b, factor*rate t)=factor*(spin b-spin a) :=
by rw [interval_integral.integral_const_mul,interval_integral.integral_eq_sub_of_has_deriv_at hd int]

theorem massive_pair_zero (forward backward : ℝ) (rev : backward= -forward) :
 forward+backward=0 := by rw [rev,add_neg_self]

theorem sweep_integrand (p d e : ℝ) (h : p^2+d^2≠0) :
 (-d/(2*(p^2+d^2)))*((2*e-1)-1) = d*(1-e)/(p^2+d^2) :=
by field_simp [h]; ring

-- The two extremal lines plus the triplet's central line have zero
-- summed first-order splitting. The singlet is stationary to first order.
theorem tracefree_multiplet {V : Type*} [add_comm_group V] [module ℝ V]
 (a b : V) (tr : a+(2:ℝ) • b=0) (L S : V →ₗ[ℝ] ℝ) :
 2*L ((1/2:ℝ) • a)+L ((-1/2:ℝ) • a+b)+S ((-1/2:ℝ) • a-b)=0 :=
begin
 have eqL := congr_arg L tr, have eqS := congr_arg S tr,
 simp only [map_add,L.map_smul,S.map_smul,map_zero,smul_eq_mul] at eqL eqS,
 simp only [map_add,map_sub,L.map_smul,S.map_smul,smul_eq_mul], linarith
end

theorem trace_shape_equation (elastic f a b u v force : ℝ)
 (rad : u=4*force-2*elastic*f^2*(a+2*b))
 (perp : v= -2*force-2*elastic*f^2*(a+2*b)) :
 u+2*v= -6*elastic*f^2*(a+2*b) := by rw [rad,perp]; ring

theorem edge_recurrence (mass spacing : ℝ) (h : spacing≠0) (n : ℕ) :
 (mass+1/spacing)*(1+spacing*mass)^n-(1+spacing*mass)^(n+1)/spacing=0 :=
by rw [pow_succ]; field_simp [h]; ring

theorem localized_ratio (h m : ℝ) (hh : 0<h) :
 |1+h*m|<1 ↔ -2/h<m ∧ m<0 :=
begin
 rw [abs_lt,div_lt_iff hh],
 split,
 {rintro ⟨left,right⟩, split,
  {nlinarith only [left]}, apply (mul_lt_mul_left hh).1, rw [mul_zero], linarith},
 {rintro ⟨left,right⟩, have hn:=mul_neg_of_pos_of_neg hh right,
  split; nlinarith only [left,hn]}
end

theorem bound_weight (weight : ℝ) (h : 0≤weight) :
 0≤1-real.exp (-weight) ∧ 1-real.exp (-weight)<1 :=
begin
 have le := real.exp_le_exp.mpr (show -weight≤0, by linarith),
 rw [real.exp_zero] at le, exact ⟨by linarith,by linarith [real.exp_pos (-weight)]⟩
end

-- Wick determinant of the two commuting spectral occupations of a Slater state.
theorem compensated_pair (upper lower coherence2 both : ℝ)
 (wick : both=upper*lower-coherence2) :
 upper-both=upper*(1-lower)+coherence2 := by rw [wick]; ring

theorem frozen_read_conserves {A : Type*} [ring A] (P H : A)
 (project : P*P=P) (comm : P*H=H*P) :
 P*H*P+(1-P)*H*(1-P)=H :=
begin
 have v : P*H*P=H*P := by rw [comm,mul_assoc,project],
 calc P*H*P+(1-P)*H*(1-P)= H-P*H-H*P+P*H*P+P*H*P : by noncomm_ring
 ... = H : by rw [v,comm]; noncomm_ring
end

theorem sharp_boundary_work (left right bond : ℝ) :
 (left+right)-(left+right+2*bond)= -2*bond := by ring

theorem cut_continuity (left right flux : ℝ) :
 (left-flux)+(right+flux)=left+right := by ring

theorem gauss_link (electric : ℕ → ℤ) (density : ℕ → ℤ)
 (zero : electric 0=0) (gauss : ∀ k, electric (k+1)=electric k+density k) (n : ℕ) :
 electric n=∑ k in finset.range n,density k :=
begin
 induction n with n ih, {simpa using zero},
 rw [gauss,ih,finset.sum_range_succ]
end

theorem electric_envelope (q b : ℝ) (lo : -b≤q) (hi : q≤b) : q^2≤b^2 :=
by nlinarith only [mul_nonneg (sub_nonneg.mpr hi) (show 0≤b+q,by linarith)]

theorem positive_transfer_with_recoil (baseline actual error floor : ℝ)
 (bound : |actual-baseline|≤error) (margin : floor+error<baseline) : floor<actual :=
by have h : - (actual-baseline)≤error := (neg_le_abs_self _).trans bound; linarith

theorem finite_coupling_window {H : Type*} [normed_add_comm_group H] [normed_space ℝ H]
 (evolution derivative : ℝ → H) (t b : ℝ) (ht : 0≤t)
 (hd : ∀ s∈Icc 0 t, has_deriv_at evolution (derivative s) s)
 (bound : ∀ s∈Ico 0 t, norm (derivative s)≤b) :
 norm (evolution t-evolution 0) ≤ t*b :=
begin
 have h:=norm_image_sub_le_of_norm_deriv_le_segment' (λ s hs,(hd s hs).has_deriv_within_at)
   bound t (set.right_mem_Icc.mpr ht),
 simpa only [sub_zero,mul_comm] using h
end

-- Bhattacharyya overlap tensorizes for independent records, whether or not
-- the label of an individual copy is subsequently discarded.
theorem copy_overlap {ι κ : Type*} [fintype ι] [fintype κ] (a : ι→ℝ) (b : κ→ℝ) :
 (∑ i,∑ j,a i*b j)=(∑ i,a i)*(∑ j,b j) := by rw [finset.sum_mul]; simp only [finset.mul_sum]

theorem shared_output {ι : Type*} [fintype ι] (p q : ι→ℝ) (k : ι)
 (hp : ∀ i,0≤p i) (hq : ∀ i,0≤q i) (pk : 0<p k) (qk : 0<q k) :
 0<∑ i,min (p i) (q i) :=
begin
 exact lt_of_lt_of_le (lt_min pk qk)
   (finset.single_le_sum (λ i hi, le_min (hp i) (hq i)) (finset.mem_univ k))
end

theorem binary_contact_interval (a b c d : ℝ)
 (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d) (total : a+b+c+d=1) :
 |(b+d)-(c+d)|≤b+c ∧ b+c≤min ((b+d)+(c+d)) (2-(b+d)-(c+d)) :=
begin
 split, {rw [abs_le], split; linarith}, exact le_min (by linarith) (by linarith)
end

theorem born_flag {V : Type*} (norm2 : V→ℝ) (K : V→V) (v : V) (p : ℝ)
 (on_code : ∀ w, norm2 (K w)=p*norm2 w) (normalized : norm2 v=1) :
 norm2 (K v)=p := by rw [on_code,normalized,mul_one]

-- Apply this to the linear map taking a Hamiltonian to its commutator
-- with a fixed readout. Commuting at two masses implies commuting at all.
theorem affine_meter {V W : Type*} [add_comm_group V] [module ℝ V]
 [add_comm_group W] [module ℝ W] (L : V →ₗ[ℝ] W) (h v : V) (a b : ℝ)
 (different : a≠b) (x : L (h+a • v)=0) (y : L (h+b • v)=0) (t : ℝ) :
 L (h+t • v)=0 :=
begin
 simp only [map_add,L.map_smul] at x y ⊢,
 have eq : a • L v=b • L v := add_left_cancel (x.trans y.symm),
 have hsub : (a-b) • L v=0 := by rw [sub_smul,eq,sub_self],
 have van := (smul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr different),
 simpa [van] using x
end

theorem common_phase_arc {ι : Type*} [fintype ι] (w angle : ι → ℝ) (lower : ℝ)
 (positive : ∀ i,0≤w i) (total : ∑ i,w i=1) (arc : ∀ i,lower≤real.cos (angle i)) :
 lower≤∑ i,w i*real.cos (angle i) :=
calc lower=(∑ i,w i)*lower : by rw [total,one_mul]
 ... = ∑ i,w i*lower : by rw [finset.sum_mul]
 ... ≤ ∑ i,w i*real.cos (angle i) :
  finset.sum_le_sum (λ i hi, mul_le_mul_of_nonneg_left (arc i) (positive i))

-- An effect commuting with both magnetic translations of a flux-two torus.
theorem magnetic_code (a b c d : ℂ) (clock_b : b= -b) (clock_c : c= -c)
 (shift : a=d) : a=d ∧ b=0 ∧ c=0 :=
begin
 refine ⟨shift,_,_⟩,
 {linear_combination (1/2:ℂ)*clock_b},
 {linear_combination (1/2:ℂ)*clock_c}
end

theorem graviton_band (E hbar omega scale mean p : ℝ) (h : 0<hbar*omega)
 (energy : mean*(hbar*omega)≤E) (model : E≤scale)
 (mark : p≤mean) : p≤scale/(hbar*omega) :=
mark.trans ((le_div_iff h).2 (energy.trans model))

theorem scale_cancels (G mass central factor c hbar cutoff : ℝ)
 (hg : G≠0) (hc : central≠0) (hv : c≠0) (hh : hbar≠0) (hw : cutoff≠0) :
 (factor*mass^2*c^2/central)/(hbar*(cutoff*c^3/(G*central)))
 =factor/cutoff*(G*mass^2/(hbar*c)) := by field_simp [hg,hc,hv,hh,hw]; ring

end cat_tidal_current
