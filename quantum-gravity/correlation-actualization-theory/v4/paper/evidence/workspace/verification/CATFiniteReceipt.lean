import tactic
import analysis.special_functions.exp_deriv
import measure_theory.integral.bochner
import analysis.inner_product_space.basic

noncomputable theory
open set measure_theory
open_locale real_inner_product_space complex_inner_product_space complex_conjugate big_operators
namespace cat_finite_receipt

-- v is the norm squared of an arbitrary homogeneous material solution.
-- A is the integrated upper coupling rate. The input is the passive energy balance.
theorem integrated_floor (v A : ℝ → ℝ) (c : ℝ → ℝ) (t₀ t₁ : ℝ) (ht : t₀≤t₁)
 (initial : A t₀=0) (hd : ∀ t, has_deriv_at A (c t) t)
 (hv : ∀ t, ∃ d, has_deriv_at v d t ∧ -(c t)*v t≤d) :
 real.exp (-(A t₁))*v t₀ ≤ v t₁ :=
begin
 let f : ℝ → ℝ := λ t,real.exp (A t)*v t,
 have df : ∀ t, ∃ d, has_deriv_at f d t ∧ 0≤d,
 {intro t, obtain ⟨d,h,lower⟩:=hv t,
  refine ⟨_,((hd t).exp).mul h,_⟩,
  have := mul_nonneg (real.exp_pos (A t)).le (show 0≤c t*v t+d,by linarith), nlinarith only [this]},
 have mono : monotone f := monotone_of_deriv_nonneg
     (λ t,(df t).some_spec.1.differentiable_at)
     (λ t, by {rw [(df t).some_spec.1.deriv], exact (df t).some_spec.2}),
 have b:=mono ht, change real.exp (A t₀)*v t₀ ≤ real.exp (A t₁)*v t₁ at b,
 rw [initial,real.exp_zero,one_mul] at b,
 have h:=mul_le_mul_of_nonneg_left b (real.exp_pos (-(A t₁))).le,
 rwa [←mul_assoc,←real.exp_add,neg_add_self,real.exp_zero,one_mul] at h
end

-- Evaluate the output row on the direction parallel to the captured vector.
-- Valid in any finite complex output dimension; no common basis for successive absorbers.
theorem passive_row (v k overlap eta : ℝ) (row : v^2+k^2=1) (floor : eta≤v^2)
 (cauchy : |overlap|≤|k|) : eta≤1-overlap^2 :=
begin
 have h:=mul_self_le_mul_self (abs_nonneg overlap) cauchy,
 rw [←sq,←sq,sq_abs,sq_abs] at h, linarith
end

theorem one_quantum_escape {H K : Type*} [normed_add_comm_group H] [inner_product_space ℂ H]
 [normed_add_comm_group K] [inner_product_space ℂ K]
 (forward : H → K) (back : K → H) (memory : K → K) (eta : ℝ)
 (row : ∀u : K, ‖memory u‖^2+‖back u‖^2=‖u‖^2)
 (lower : ∀u : K, eta*‖u‖^2≤‖memory u‖^2)
 (dual : ∀v u, ⟪forward v,u⟫_ℂ=⟪v,back u⟫_ℂ)
 (v : H) (unit : ‖v‖=1) (rate : eta≤1) : eta≤1-‖forward v‖^2 :=
begin
 let u := forward v,
 by_cases zero : u=0,
 {change eta≤1-‖u‖^2, simpa [zero] using rate},
 have hnorm : 0<‖u‖ := norm_pos_iff.mpr zero,
 have cs := norm_inner_le_norm v (back u),
 rw [unit,one_mul,←dual] at cs, change ‖⟪u,u⟫_ℂ‖≤‖back u‖ at cs,
 rw [inner_self_eq_norm_sq_to_K, norm_pow, complex.norm_real, real.norm_eq_abs,
     abs_of_nonneg (norm_nonneg u)] at cs,
 have cs2 := mul_self_le_mul_self (sq_nonneg ‖u‖) cs,
 have c : (‖u‖^2)*(‖u‖^2)≤(1-eta)*(‖u‖^2) :=
   by nlinarith only [cs2,row u,lower u],
 have b:=(mul_le_mul_right (pow_pos hnorm 2)).1 c,
 change eta≤1-‖u‖^2, linarith
end

-- Eigenvalues of the no-capture operator in the tensor power of the one-particle space.
theorem fock_floor (eta : ℝ) (positive : 0≤eta) : ∀ l : list ℝ,
 (∀ x∈l,eta≤x) → eta^l.length ≤ l.prod
| [] h := by simp
| (x::xs) h := begin
  have head := h x (list.mem_cons_self _ _),
  have tail := fock_floor xs (λ a ha, h _ (list.mem_cons_of_mem x ha)),
  have p := mul_le_mul head tail (pow_nonneg positive _) (le_trans positive head),
  simpa [pow_succ, mul_comm] using p
end

def floors (c : ℕ → ℝ) : ℕ → ℝ
| 0 := 1
| (n+1) := c n * floors n

theorem composed_floor (c m : ℕ → ℝ) (positive : ∀ n, 0≤c n)
 (init : 1≤m 0) (step : ∀n, c n*m n≤m (n+1)) : ∀n, floors c n≤m n
| 0 := init
| (n+1) := le_trans (mul_le_mul_of_nonneg_left (composed_floor n) (positive n)) (step n)

theorem exponential_tangent (x a : ℝ) :
 real.exp a+(real.exp a)*(x-a)≤real.exp x :=
begin
 have h:=mul_le_mul_of_nonneg_left (real.add_one_le_exp (x-a)) (real.exp_pos a).le,
 rw [←real.exp_add,show a+(x-a)=x,by ring] at h,
 linarith
end

section average
variables {α : Type*} [measurable_space α] (μ : measure α) [is_probability_measure μ]

theorem affine_average (X : α → ℝ) (m offset slope : ℝ) (hX : integrable X μ)
 (hm : (∫ x, X x ∂μ)=m) :
 (∫ x, offset+slope*(X x-m) ∂μ)=offset :=
begin
 have sub_int : integrable (λ x, X x-m) μ := hX.sub (integrable_const m),
 have prod_int : integrable (λ x,slope*(X x-m)) μ := sub_int.const_mul slope,
 rw [integral_add (integrable_const offset) prod_int,
 integral_mul_left, integral_sub hX (integrable_const _),hm],
 simp
end

theorem finite_mean_escape (X : α → ℝ) (A mean : ℝ) (hX : integrable X μ)
 (hm : (∫ x, X x ∂μ)=mean) (hi : integrable (λ x,real.exp (-A*X x)) μ) :
 real.exp (-A*mean) ≤ ∫ x,real.exp (-A*X x) ∂μ :=
begin
 let q:=real.exp (-A*mean),
 have h := affine_average μ X mean q (q*(-A)) hX hm,
 change q ≤ _, rw [←h],
 apply integral_mono_ae ((integrable_const _).add ((hX.sub (integrable_const _)).const_mul _)) hi,
 apply filter.eventually_of_forall, intro x,
 calc q+q*(-A)*(X x-mean) = q+q*((-A*X x)-(-A*mean)) : by ring
 ... ≤ real.exp (-A*X x) : exponential_tangent _ _
end

theorem reciprocal_tangent (x m : ℝ) (hx : 0≤x) (hm : 0≤m) :
 1/(1+m)+(-(1/(1+m)^2))*(x-m) ≤ 1/(1+x) :=
begin
 have dm : 0<1+m := by linarith, have dx : 0<1+x := by linarith,
 have e : 1/(1+x)-(1/(1+m)+(-(1/(1+m)^2))*(x-m))
            = (x-m)^2/((1+x)*(1+m)^2) := by field_simp [dx.ne',dm.ne']; ring,
 linarith only [e, div_nonneg (sq_nonneg (x-m)) (mul_nonneg dx.le (sq_nonneg (1+m)))]
end

-- Applies directly to the joint probability of elastic mode and Laplace frequency.
theorem retarded_compliance (X : α → ℝ) (m : ℝ) (positive : ∀x,0≤X x)
 (hm : 0≤m) (hX : integrable X μ) (mean : (∫ x, X x ∂μ)=m)
 (hi : integrable (λ x,1/(1+X x)) μ) : 1/(1+m)≤∫ x,1/(1+X x) ∂μ :=
begin
 have h:=affine_average μ X m (1/(1+m)) (-(1/(1+m)^2)) hX mean,
 rw [←h], apply integral_mono_ae
 ((integrable_const _).add ((hX.sub (integrable_const _)).const_mul _)) hi,
 exact filter.eventually_of_forall (λx,reciprocal_tangent _ _ (positive x) hm)
end
end average

-- Five Frobenius-unit trace-free quadrupoles, after squaring their gradients/2m.
theorem quadrupole_strength (x y z : ℝ) :
 (x^2+y^2)/2+(x^2+y^2+4*z^2)/6+
 (x^2+y^2)/2+(x^2+z^2)/2+(y^2+z^2)/2=(5/3)*(x^2+y^2+z^2) := by ring

theorem spectral_cutoff (ω Ω strength : ℝ) (hn : 0≤ω) (cutoff : ω≤Ω)
 (weight : 0≤strength) : ω^5*strength≤Ω^4*(ω*strength) :=
begin
 have h:=pow_le_pow_of_le_left hn cutoff 4,
 have g:=mul_le_mul_of_nonneg_right h (mul_nonneg hn weight),
 calc ω^5*strength = ω^4*(ω*strength) : by ring
 ... ≤ Ω^4*(ω*strength) : g
end

theorem radiative_factor : (2/5:ℝ)*(10/3)=4/3 := by norm_num

-- Coordinate double commutator with the kinetic term, via the two product rules.
-- q, dq, ddq and v, dv, ddv are value and first two derivatives on the common core.
theorem kinetic_commutator (q dq ddq v dv ddv : ℝ) :
 -2*q*(ddq*v+2*dq*dv+q*ddv)+q^2*ddv+
 ((2*dq^2+2*q*ddq)*v+4*q*dq*dv+q^2*ddv)=2*dq^2*v := by ring

-- Navier bulk force and both independent surface tractions for the cubic displacement.
theorem free_surface_coefficients :
 let a : ℝ := 7/33, b : ℝ := -3/22, c : ℝ := 2/33 in
 -18*b-24*c=1 ∧ a+2*b+c=0 ∧ 4*b+9*c=0 := by norm_num

theorem elastic_moments :
 let a : ℝ := 7/33, b : ℝ := -3/22, c : ℝ := 2/33 in
 a/5+b/7+2*c/35=61/2310 ∧
 a^2/5+2*a*b/7+b^2/9+4*a*c/35+4*b*c/45+2*c^2/45=145/39204 := by norm_num

-- Fourier-Laplace response of one oscillator on one exponential load.
theorem exponential_drive (ω u f s : ℝ) (h : ω^2+u^2≠0) :
 (u^2+ω^2)*(-f*real.exp (-u*s)/(ω^2+u^2))= -f*real.exp (-u*s) :=
by field_simp [h]; ring

-- The Laplace time variable decreases along free fall. Two proper-time derivatives
-- give the same second derivative as two s derivatives.
theorem exponential_solution (ω u f s : ℝ) (h : ω^2+u^2≠0) :
 let a := -f/(ω^2+u^2), q := λ t : ℝ, a*real.exp (-u*t),
     v := λ t : ℝ, -u*q t in
 has_deriv_at q (v s) s ∧ has_deriv_at v (-f*real.exp (-u*s)-ω^2*q s) s :=
begin
 dsimp only,
 have heat := (((has_deriv_at_id s).const_mul (-u)).exp).const_mul (-f/(ω^2+u^2)),
 have d : has_deriv_at (λt:ℝ,(-f/(ω^2+u^2))*real.exp (-u*t))
     (-u*((-f/(ω^2+u^2))*real.exp (-u*s))) s,
 {convert heat using 1, dsimp, ring},
 split, {exact d},
 convert d.const_mul (-u) using 1, field_simp [h]; ring
end

theorem phase_kernel (ω u : ℝ) (hω : 0<ω) :
 (ω/(u^2+ω^2))^2+(u/(u^2+ω^2))^2 ≤ 1/ω^2 :=
begin
 have d : 0<u^2+ω^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hω _),
 have e : (ω/(u^2+ω^2))^2+(u/(u^2+ω^2))^2=1/(u^2+ω^2) :=
   by field_simp [d.ne']; ring,
 rw [e], apply one_div_le_one_div_of_le (pow_pos hω _), linarith only [sq_nonneg u]
end

theorem amplitude_floor {H : Type*} [normed_add_comm_group H] [inner_product_space ℝ H]
 (x a : H) (weight : ℝ) (hw : ‖x‖^2≤weight) :
 ⟪x,a⟫_ℝ^2≤weight*‖a‖^2 :=
begin
 have h:=mul_self_le_mul_self (abs_nonneg (⟪x,a⟫_ℝ)) (abs_real_inner_le_norm x a),
 rw [←sq,sq_abs,←sq,mul_pow] at h,
 exact h.trans (mul_le_mul_of_nonneg_right hw (sq_nonneg _))
end

-- Parity relates the two physical code branches. The ordinary source tags retained
-- at output give orthogonality; equal outcome probabilities alone are insufficient.
theorem flag_isometry {H : Type*} [normed_add_comm_group H] [inner_product_space ℂ H]
 (u v : H) (p : ℂ) (hu : ⟪u,u⟫_ℂ=p) (hv : ⟪v,v⟫_ℂ=p)
 (orth : ⟪u,v⟫_ℂ=0) (a b c d : ℂ) :
 ⟪a • u+b • v,c • u+d • v⟫_ℂ=p*(conj a*c+conj b*d) :=
begin
 have reverse:=inner_eq_zero_symm.1 orth,
 simp only [inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,
            hu,hv,orth,reverse,mul_zero,zero_add,add_zero],
 ring
end

theorem shear_even (s t : ℝ) : (t < abs s) ↔ (t < abs (-s)) := by rw [abs_neg]

-- The square of the classical fidelity after grouping the records into two
-- decisions; a,c are the first conditional square roots and b,d the second.
theorem signed_fidelity_budget (a b c d e : ℝ)
 (pa : a^2+c^2=1) (pb : b^2+d^2=1) (err : 2*e=c^2+b^2) :
 (a*b+c*d)^2 ≤ 4*e*(1-e) :=
begin
 have alt : 2*(1-e)=a^2+d^2 := by linarith,
 have h : 4*e*(1-e)-(a*b+c*d)^2=(a*c-b*d)^2,
 {calc 4*e*(1-e)-(a*b+c*d)^2
      = (2*e)*(2*(1-e))-(a*b+c*d)^2 : by ring
  ... = _ : by rw [err,alt]; ring},
 linarith only [h,sq_nonneg (a*c-b*d)]
end

end cat_finite_receipt
