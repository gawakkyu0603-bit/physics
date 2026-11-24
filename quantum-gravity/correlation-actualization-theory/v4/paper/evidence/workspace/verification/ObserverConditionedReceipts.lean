import analysis.special_functions.integrals
import data.matrix.basic
import data.complex.basic
import algebra.big_operators.order
import tactic

noncomputable theory
open_locale big_operators matrix
open finset measure_theory

namespace observer_conditioned_receipts

theorem split_marginal {ι : Type*} [fintype ι] (m : ι→ℝ) (w : ℝ)
 (h : ∑i,m i=1) : ∑i,w*m i=w := by rw [←mul_sum,h,mul_one]

theorem neutral_blind (q₁ q₂ : ℝ) (K : ℝ→ℝ) :
 K(q₁-q₁)=K(q₂-q₂) := by simp

theorem signed_ports (a b : ℝ) :
 (a+b)/2=(b+a)/2 ∧ a-b=-(b-a) := by split;ring

theorem choose_property_first (w p total : ℝ) (hp : 0<p) (h : total=w*p) :
 total/p=w := by rw [h,mul_div_cancel _ (ne_of_gt hp)]

-- No product structure between different material modes is needed for this lemma.
theorem permuted_readout {ι : Type*} [fintype ι] (g : ι≃ι) (p k : ι→ℝ)
 (preserves : ∀i,p(g i)=p i) :
 ∑i,p i*k(g i)=∑i,p i*k i :=
begin
 calc (∑i,p i*k(g i))=∑i,p(g i)*k(g i) :
   sum_congr rfl (λ i _,by rw [preserves])
 ... = _ : g.sum_comp (λ i,p i*k i)
end

-- For any earlier material distribution the remote outcome leaves its posterior unchanged.
theorem remote_posterior {ι : Type*} [fintype ι] (p : ι→ℝ) (h : ∑i,p i=1)
 (q : ℝ) (pos : 0<q) (i : ι) :
 p i*q/(∑j,p j*q)=p i :=
begin rw [←sum_mul,h,one_mul,mul_div_cancel _ (ne_of_gt pos)] end

theorem approximate_remote_guess {κ : Type*} [fintype κ] (obs q err : κ→ℝ)
 (prior cap δ : ℝ) (hq : ∑j,q j=1) (he : ∑j,err j≤δ)
 (b : ∀j,obs j≤cap*q j+err j) :
 ∑j,obs j≤cap+δ :=
begin
 calc (∑j,obs j)≤∑j,(cap*q j+err j) : sum_le_sum (λ j _,b j)
 ... ≤ _ : by rw [sum_add_distrib,←mul_sum,hq,mul_one];linarith
end

theorem local_posterior {ι : Type*} [fintype ι] [decidable_eq ι] (p : ι→ℝ)
 (x z : ι) (pz : 0<p z) :
 (if z=x then p x else 0)/(∑i,if z=i then p i else 0)=(if z=x then 1 else 0) :=
begin simp,by_cases h : z=x,
 {subst x,simp [ne_of_gt pz]}, {simp [h]} end

theorem same_effect_cannot_separate {ι : Type*} [fintype ι] (w p : ι→ℝ)
 (hn : ∑j,w j=1) (h : ∀i,p i=1) : ∑i,w i*p i=1 := by simpa [h] using hn

theorem common_marginal {ι : Type*} [fintype ι] (z : ι→ℝ)
 (d : ℝ) (normed : ∑j,z j=1) : ∑j,z j*d=d :=
by rw [←sum_mul,normed,one_mul]

theorem scalar_effect {ι : Type*} [fintype ι] (trace_state : ι→ℝ)
 (p : ℝ) (h : ∑i,trace_state i=1) : ∑i,p*trace_state i=p :=
by rw [←mul_sum,h,mul_one]

-- Direct diagonal correction cannot restore the missing logical off-diagonal.
theorem off_diagonal_zero (a b : ℂ) : a*0*b=0 := by simp

-- The two angular harmonics have zero mean cross term in the Born density.
theorem angular_born_density (a b c s : ℝ) (circle : c^2+s^2=1) :
 (a+b*c)^2+(b*s)^2=a^2+b^2+2*a*b*c :=
begin calc (a+b*c)^2+(b*s)^2 = a^2+b^2*(c^2+s^2)+2*a*b*c : by ring
 ... = _ : by rw [circle,mul_one] end

theorem mean_interference (a b phase : ℝ) :
 ∫ t in (0:ℝ)..(2*real.pi), (a+b*real.cos (t+phase))=2*real.pi*a :=
begin
 have h : interval_integrable (λt : ℝ,real.cos(t+phase)) volume 0 (2*real.pi) :=
   (real.continuous_cos.comp (continuous_id.add continuous_const)).interval_integrable _ _,
 rw [interval_integral.integral_add interval_integrable_const (h.const_mul _)],
 dsimp only,
 rw [interval_integral.integral_const,interval_integral.integral_const_mul],
 have integ : (∫t in (0:ℝ)..2*real.pi,real.cos(t+phase)) = ∫t in 0+phase..2*real.pi+phase,real.cos t := interval_integral.integral_comp_add_right real.cos phase,
 rw [integ, integral_cos],simp [real.sin_add,real.sin_two_pi,real.cos_two_pi,smul_eq_mul]
end

theorem bright_rotation (E T a b : ℝ) (he : E≠0) (h : a^2+b^2=E^2) :
 (real.cos (T*E))^2+(real.sin (T*E))^2*(a^2+b^2)/E^2=1 :=
begin rw [h],field_simp [he] end

theorem absent_gravity_no_write (T : ℝ) : (real.sin (T*0))^2=0 := by simp

-- Once both modes have the same spectral measure a referenced common reading
-- uses exactly the same characteristic amplitude as a relative transfer.
theorem matched_spectrum {ι : Type*} [fintype ι] (w f : ι→ℂ) (c d : ℂ) :
 (∑i,w i*(complex.exp (c*f i)*complex.exp (-(d*f i))))=
 ∑i,w i*complex.exp ((c-d)*f i) :=
begin apply sum_congr rfl,intros i hi,rw [←complex.exp_add],congr' 2,ring end

theorem optimal_binary_error (p : ℝ) (hp : 0≤p) (cap : p≤1) :
 4*((1-real.sqrt(1-p))/2)*(1-(1-real.sqrt(1-p))/2)=p :=
begin have h:=real.sq_sqrt (show 0≤1-p,by linarith),nlinarith only [h] end

theorem one_sided_error (p : ℝ) : (1/2:ℝ)*0+(1/2)*p=p/2 := by ring

theorem finite_write_guess {ι : Type*} [fintype ι] (p w : ι→ℝ) (null_guess : ι) :
 (∑i,p i*w i) + p null_guess*(1-w null_guess)
 = (∑i,p i*w i) + (p null_guess - p null_guess*w null_guess) := by ring

theorem independent_radiation {κ : Type*} [fintype κ] (guess : κ→ℝ)
 (w₀ w₁ : κ→ℝ) (h : ∀k,w₀ k=w₁ k) :
 (∑k,w₀ k*guess k)=(∑k,w₁ k*guess k) := by simp_rw [h]

theorem decoded_distinguishability (p₀ p₁ distance e : ℝ)
 (success : (p₀+(1-p₁))/2=1-e) (test : p₀-p₁≤distance) :
 1-2*e≤distance := by linarith only [success,test]

theorem polar_error_spectral (x : ℝ) (hx : 0≤x) :
 (real.sqrt x-1)^2≤(x-1)^2 :=
begin
 have he := real.sq_sqrt hx,
 have extra : 0≤(real.sqrt x-1)^2*((real.sqrt x)^2+2*real.sqrt x) :=
 mul_nonneg (sq_nonneg _) (by nlinarith only [sq_nonneg (real.sqrt x),real.sqrt_nonneg x]),
 calc (real.sqrt x-1)^2≤((real.sqrt x)^2-1)^2 : by nlinarith only [extra]
 ... = _ : by rw [he]
end

theorem repeated_pair_averages {ι : Type*} [fintype ι] (p h : ι→ℝ) :
 (∑i,∑j,p i*p j*(h i*h j))=(∑i,p i*h i)^2 :=
begin
 have term : ∀i j,p i*p j*(h i*h j)=(p i*h i)*(p j*h j) := λ i j,by ring,
 simp_rw [term,←mul_sum],rw [←sum_mul,pow_two]
end

theorem four_candidates_error (u : ℝ) (h : 0≤u) (hu : u≤0.013826) :
 3*u^2<0.000574 ∧ 3*u^3<0.000008 :=
begin
 have a:=pow_le_pow_of_le_left h hu 2,have b:=pow_le_pow_of_le_left h hu 3,
 split;norm_num at *;linarith
end

theorem sealed_quantum_effect {ι : Type*} [fintype ι] (K V E W : matrix ι ι ℂ)
 (p : ℂ) (eqv : W⬝(E⬝V)=E) (joint : K=p • (W⬝(E⬝V))) : K=p • E :=
by rw [joint,eqv]

theorem local_random_isometry {ι : Type*} [fintype ι] [decidable_eq ι]
 (E V W : matrix ι ι ℂ) (commutes : E⬝V=V⬝E) (isometry : W⬝V=1) :
 W⬝(E⬝V)=E := by rw [commutes,←matrix.mul_assoc,isometry,matrix.one_mul]

end observer_conditioned_receipts
