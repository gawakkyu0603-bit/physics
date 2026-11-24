import tactic
import data.complex.basic
import measure_theory.integral.lebesgue

noncomputable theory
open_locale big_operators ennreal
open measure_theory filter
namespace layer_matrix_parent

-- Unpaired eigenvalues and the determinant of each paired Pauli block.
theorem paired_det (r a j m : ℝ) :
 (a*m-r)*(r-a*(m+1))-a^2*(j-m)*(j+m+1) =
 -(r-a*(m+1/2))^2-a^2*(j*(j+1)-(m+1/2)^2) := by ring
theorem paired_gap (j m : ℝ) (lower : -j≤m) (upper : m+1≤j) :
 0 < j*(j+1)-(m+1/2)^2 :=
begin
 have p : 0 ≤ (j-m-1)*(j+m) := mul_nonneg (by linarith) (by linarith),
 have eqn : j*(j+1)-(m+1/2)^2=(j-m-1)*(j+m)+2*j-1/4 := by ring,
 rw [eqn],linarith
end
theorem paired_negative (r a j m : ℝ) (ap : 0<a) (lo : -j≤m) (hi : m+1≤j) :
 (a*m-r)*(r-a*(m+1))-a^2*(j-m)*(j+m+1)<0 :=
begin
 rw [paired_det], have hp:=mul_pos (sq_pos_of_pos ap) (paired_gap j m lo hi),
 linarith [sq_nonneg (r-a*(m+1/2))]
end
theorem unpaired_inside (a j r : ℝ) (inside : r<a*j) (rad : 0≤r) :
 0<a*j-r ∧ 0<a*j+r := by constructor; linarith
theorem unpaired_outside (a j r : ℝ) (aj : 0≤a*j) (outside : a*j<r) :
 a*j-r<0 ∧ 0<a*j+r := by constructor; linarith
theorem full_spinor_cancel (t : ℤ) : 4*t+4*(-t)=0 := by ring
theorem paired_index (t : ℚ) : (4*t-4*(-t))/16=t/2 := by ring
theorem transverse_gap (b e : ℝ) (hb : 0<b) : 0<e^2+b^2 :=
by nlinarith [sq_pos_of_pos hb,sq_nonneg e]
theorem sphere_first_integral (a v d : ℝ) (hd : d= -2*a^3) :
 2*v*d+4*a^3*v=0 := by rw [hd]; ring
theorem charge_shift (q c s : ℤ) : (q+s)+(c-s)=q+c := by ring

-- The occupied wall multiplies wavefunctions and their covariant derivative
-- by the same isometry; hence their inner-product pairing is unchanged.
theorem matched_flux {X : Type*} (pair : X → X → ℂ) (T : X → X)
 (iso : ∀ a b, pair (T a) (T b)=pair a b) (u du : X) :
 pair (T u) (T du)=pair u du := iso u du
theorem swap_even (u v : ℂ) : (u+v)/2-(u-v)/2=v := by ring
theorem swap_odd (u v : ℂ) : (u+v)/2+(u-v)/2=u := by ring
theorem spectator_gap (a b c : ℝ) : (a+b)-(a+c)=b-c := by ring

-- Matrix element of the full Hamiltonian in energy eigenbases, for each
-- occupied term. Complex amplitudes may interfere at the same total energy.
theorem recoil_intertwines (before after packet gap : ℝ) (x : ℂ)
 (h : before-after=gap) :
 ((after+(packet+gap):ℝ):ℂ)*x=x*((before+packet:ℝ):ℂ) :=
begin
 have t : after+(packet+gap)=before+packet := by linarith,
 rw [t,mul_comm]
end

theorem energy_sum {ι : Type*} (s : finset ι) (u v : ℂ) (x : ι → ℂ)
 (h : ∀ i∈s, u*x i=x i*v) :
 u*(∑ i in s,x i)=(∑ i in s,x i)*v :=
by {rw [finset.mul_sum,finset.sum_mul],exact finset.sum_congr rfl h}

-- Intertwining entries vanish between unequal total energies. Arbitrary
-- spectral functions, in particular every energy projector, then intertwine.
theorem every_energy_projector (a b : ℝ) (x : ℂ)
 (supported : a≠b → x=0) (f : ℝ → ℂ) : f a*x=x*f b :=
begin
 by_cases h:a=b,
 {rw [h,mul_comm]},
 {rw [supported h,mul_zero,zero_mul]}
end
theorem complete_energy_instrument {R ι : Type*} [ring R] (s : finset ι)
 (bra ket out : ι → R) (input : R) (complete : (∑ i in s,bra i*ket i)=1)
 (h : ∀ i∈s, out i*ket i=ket i*input) :
 (∑ i in s,bra i*out i*ket i)=input :=
calc
 (∑ i in s,bra i*out i*ket i) = ∑ i in s,(bra i*ket i)*input :
   finset.sum_congr rfl (λ i hi, by rw [mul_assoc,h i hi,mul_assoc])
 ... = (∑ i in s,bra i*ket i)*input : by rw [finset.sum_mul]
 ... = input : by rw [complete,one_mul]

theorem quiet_and_write (dt rate : ℝ) : (1-dt*rate)+dt*rate=1 := by ring
theorem energy_distribution (p x y : ℝ) (out : x=y) :
 (1-p)*x+p*y=x := by rw [←out]; ring
theorem two_receipts {X : Type*} (U V : X→X) (Ui Vi : X→X)
 (hu : ∀ x, Ui (U x)=x) (hv : ∀ x, Vi (V x)=x) (x : X) :
 Ui (Vi (V (U x)))=x := by rw [hv,hu]
theorem physical_decoding {X : Type*} :
 ∀ l : list ((X → X) × (X → X)),
 (∀ (p : (X→X)×(X→X)), p∈l → ∀ x, p.2 (p.1 x)=x) →
 ∀ x, l.foldr (λ (p : (X→X)×(X→X)) v, p.2 v) (l.foldl (λ v (p : (X→X)×(X→X)), p.1 v) x)=x :=
begin
 intro l,induction l with p l ih,
 {intros h x,refl},
 {intros h x, change p.2 (l.foldr _ (l.foldl _ (p.1 x)))=x,
  have ht : ∀ q∈l, ∀ u, (q : (X→X)×(X→X)).2 (q.1 u)=u :=
     λ q hq, h q (list.mem_cons_of_mem _ hq),
  rw [ih ht],exact h p (list.mem_cons_self _ _) x}
end
theorem hidden_record_fidelity (p : ℝ) : (p+(1-p))/2=(1:ℝ)/2 := by ring
theorem independent_receipts {X Y : Type*} (f : X→X) (g : Y→Y) (u : X×Y) :
 prod.map f id (prod.map id g u)=prod.map id g (prod.map f id u) := by cases u; refl
-- A positive exceptional subpopulation suffices to destroy a shared zero
-- mode when the failed constraint is injective. Zero-weight parts do not.
theorem shared_zero {ι : Type*} (s : finset ι) (w loss : ι → ℝ)
 (hw : ∀ i∈s, 0<w i) (hl : ∀ i∈s, 0≤loss i) :
 (∑ i in s, w i*loss i)=0 ↔ ∀ i∈s, loss i=0 :=
begin
 rw [finset.sum_eq_zero_iff_of_nonneg (λ i hi, mul_nonneg (le_of_lt (hw i hi)) (hl i hi))],
 split,
 {intros h i hi, exact (mul_eq_zero.mp (h i hi)).resolve_left (ne_of_gt (hw i hi))},
 {intros h i hi,change w i*loss i=0,rw [h i hi,mul_zero]}
end
theorem continuum_shared_zero {X : Type*} [measurable_space X]
 (μ : measure X) (loss : X→ℝ≥0∞) (h : measurable loss) :
 (∫⁻ x, loss x ∂μ)=0 ↔ loss =ᵐ[μ] 0 := lintegral_eq_zero_iff h
theorem contact_refinement (u v loss : ℝ) : (u+v)*loss=u*loss+v*loss := by ring
theorem two_ports (a b : ℝ) (p : ℝ) (h : p=0 ∨ p=1) :
 (p*a+(1-p)*b)^2+(p*b+(1-p)*a)^2=a^2+b^2 :=
by {cases h with h h; rw [h]; ring}
theorem permanent_transfer_no_balance (weight p : ℝ) (hw : 0<weight) (hp : 0<p)
 (other : ℝ) : weight*p≠other*0 :=
by {rw [mul_zero],exact ne_of_gt (mul_pos hw hp)}
theorem four_flux_square (a : ℝ) (h : a^2=3) : (-a)^2=3 := by rw [←h]; ring
theorem neutral_string_radius (r m a b c M : ℝ)
 (hr : r*m=1) (prod : a*b*c*m=1/64) (ha : a≠0) (hb : b≠0) (hc : c≠0) :
 64*r*(M/(8*a))*(M/(8*b))*(M/(8*c))=8*M^3 :=
begin
 field_simp [ha,hb,hc],
 have e : (a*b*c*m)*r = (1/64)*r := by rw [prod],
 have h : r=64*(a*b*c) := calc
   r = 64*((1/64)*r) : by ring
   ... = 64*((a*b*c*m)*r) : by rw [e]
   ... = 64*((a*b*c)*(r*m)) : by ring
   ... = 64*(a*b*c) : by rw [hr,mul_one],
 rw [h],ring
end
theorem continuum_density (a : ℝ) (ha : a≠0) : a^2 * (1/a^2)=1 :=
by field_simp [ha]
theorem sphere_multiplicity_sum : ∀ n : ℕ, (∑ l in finset.range n, (2*l+1))=n^2 :=
begin
 intro n,induction n with n ih,
 {simp},
 {rw [finset.sum_range_succ,ih],simp only [nat.succ_eq_add_one],ring}
end
theorem base_curvature (a v : ℝ) (ha : a≠0) :
 ((-2*a^3)*a-v^2)/a^4 = -(2+v^2/a^4) :=
by {field_simp [ha],ring}
theorem angular_stress (a v : ℝ) (ha : 0<a) : 1<2+v^2/a^4 :=
by linarith [div_nonneg (sq_nonneg v) (le_of_lt (pow_pos ha 4))]
theorem equal_radius_resonance (a w Omega : ℝ) (ha : 0≤w) (ho : 0≤Omega)
 (hw : w^2=2*a^2) (hO : Omega^2=2*a^2) : 2*w=2*Omega :=
begin
 have e : (w-Omega)*(w+Omega)=0 := by nlinarith only [hw,hO],
 rcases mul_eq_zero.mp e with h|h; linarith
end
theorem six_tidal_channels (amp w : ℝ) (hw : w≠0) :
 6*(amp^2/(8*w^2))=3*amp^2/(4*w^2) :=
by {field_simp [hw],ring}
theorem symplectic_bogoliubov (a b c d : ℝ) (h : a*d-b*c=1) :
 ((a+d)^2+(b-c)^2)/4-((a-d)^2+(b+c)^2)/4=1 := by linarith only
 [show ((a+d)^2+(b-c)^2)/4-((a-d)^2+(b+c)^2)/4=a*d-b*c, by ring,h]
theorem rotating_force (a J2 : ℝ) (ha : a≠0) (h : J2=2*a^6) :
 J2/a^3-2*a^3=0 := by {rw [h],field_simp [ha],ring}
theorem rotating_curvature (a J2 : ℝ) (ha : a≠0) (h : J2=2*a^6) :
 J2/a^6-2=0 := by {rw [h],field_simp [ha];ring}
theorem product_einstein (k s : ℝ) :
 k-(2*k+2*s)/2= -s ∧ s-(2*k+2*s)/2= -k := by constructor;ring
theorem rotating_curvature_general (a v J : ℝ) (ha : a≠0) :
 ((J^2/a^3-2*a^3)*a-v^2)/a^4=J^2/a^6-2-v^2/a^4 :=
by {field_simp [ha],ring}
theorem dominant_window (x u : ℝ) : (-1≤x-2-u ∧ x-2-u≤1) ↔
 (1+u≤x ∧ x≤3+u) := by constructor; rintro ⟨h,k⟩; constructor; linarith
theorem string_tension_target (G n t : ℝ) (h : G*(n*t)=1/2) :
 2*G*n*t=1 := by linarith only [show G*n*t=1/2, by simpa only [mul_assoc] using h]
theorem even_average {X : Type*} [add_comm_group X] [module ℝ X]
 (f : X →ₗ[ℝ] X) (x : X) (h : f (f x)=x) :
 f ((1/2:ℝ) • (x+f x))=(1/2:ℝ) • (x+f x) :=
by rw [linear_map.map_smul,linear_map.map_add,h,add_comm]
theorem preserved_average {X : Type*} [add_comm_group X] [module ℝ X]
 (f g : X →ₗ[ℝ] X) (x : X) (h : f x=x) (hg : f (g x)=g (f x)) :
 f ((1/2:ℝ) • (x+g x))=(1/2:ℝ) • (x+g x) :=
by rw [linear_map.map_smul,linear_map.map_add,hg,h]
theorem clifford_conjugations_commute {R : Type*} [ring R] (a b c d x : R)
 (h : a*b= -(b*a)) (k : d*c= -(c*d)) :
 a*(b*x*d)*c=b*(a*x*c)*d :=
calc
 a*(b*x*d)*c = (a*b)*x*(d*c) : by simp only [mul_assoc]
 ... = (b*a)*x*(c*d) : by rw [h,k,neg_mul,neg_mul_neg]
 ... = b*(a*x*c)*d : by simp only [mul_assoc]

theorem wall_deposit_norm (p q : ℝ) (h : p+q=1) : 1-(p+q)=0 :=
by rw [h,sub_self]
theorem consume_precursor (u z : ℤ) : (u-1)+(z+1)=u+z := by ring
theorem polarization_rate : ((1:ℚ)/256)^2=1/65536 := by norm_num
theorem frozen_temperature (y : ℝ) : (1-y)^2*(1-4*y)=1-6*y+9*y^2-4*y^3 := by ring
theorem two_pair_survival (u : ℝ) : (4*u-u^4)/3=u^4+4*(u-u^4)/3 := by ring
theorem two_pair_probability (u : ℝ) (hp : 0≤u) (hq : u≤1) :
 0≤1-(4*u-u^4)/3 :=
begin
 have he : 3-4*u+u^4=(1-u)^2*(u^2+2*u+3) := by ring,
 have h := mul_nonneg (sq_nonneg (1-u)) (show 0≤u^2+2*u+3, by nlinarith [sq_nonneg u]),
 linarith
end

end layer_matrix_parent
