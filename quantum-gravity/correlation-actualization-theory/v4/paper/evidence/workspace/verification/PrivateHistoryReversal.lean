import analysis.special_functions.trigonometric.bounds
import data.complex.basic
import measure_theory.integral.bochner
import algebra.big_operators.order
import tactic

noncomputable theory
open_locale big_operators complex_conjugate
open finset

namespace private_history_reversal

-- The inverse row is the conjugate of the incident column, at any dimension.
theorem group_amplitude {ι : Type*} (s : finset ι) (u : ι→ℂ) :
 (∑i in s, conj (u i)*u i) = ((∑i in s,complex.norm_sq (u i)):ℝ) :=
begin
 rw [complex.of_real_sum],apply sum_congr rfl,intros i hi,
 rw [mul_comm,complex.mul_conj]
end

theorem group_echo {κ ι : Type*} [fintype κ] (blocks : κ→finset ι) (u : ι→ℂ) :
 (∑j, complex.norm_sq (∑i in blocks j,conj (u i)*u i))=
 ∑j,(∑i in blocks j, complex.norm_sq (u i))^2 :=
begin simp_rw [group_amplitude,complex.norm_sq_of_real,pow_two] end

theorem merged_events (a b : ℝ) (ha : 0≤a) (hb : 0≤b) :
 a^2+b^2≤(a+b)^2 := by nlinarith only [mul_nonneg ha hb]

theorem blank_echo_moments {ι : Type*} [fintype ι]
 (w p : ι→ℝ) (hw : ∀i,0≤w i) (mass : ∑i,w i=1)
 (hp : ∀i,0≤p i) (cap : ∀i,p i≤1) :
 (∑i,w i*p i)^2 ≤ ∑i,w i*(p i)^2 ∧
 (∑i,w i*(p i)^2) ≤ ∑i,w i*p i :=
begin
 let m := ∑i,w i*p i,
 have term : ∀i,w i*(p i-m)^2=w i*p i^2-(2*m)*(w i*p i)+m^2*w i :=
 λ i,by ring,
 have h : 0≤∑i,w i*(p i-m)^2 := sum_nonneg (λ i _,mul_nonneg (hw i) (sq_nonneg _)),
 simp_rw [term] at h,
 rw [sum_add_distrib,sum_sub_distrib,←mul_sum,←mul_sum,mass,mul_one] at h,
 change 0≤(∑i,w i*p i^2)-2*m*m+m^2 at h,
 split,
 {change m^2≤_,nlinarith only [h]},
 {apply sum_le_sum,intros i hi,apply mul_le_mul_of_nonneg_left _ (hw i),
  nlinarith only [mul_nonneg (hp i) (sub_nonneg.mpr (cap i))]}
end

theorem retained_witness (p efficiency false_alarm distance : ℝ)
 (h : efficiency*(1-p)-false_alarm≤distance)
 (bound : p≤1/100) (eff : 0≤efficiency) :
 efficiency*(99/100)-false_alarm≤distance :=
by nlinarith only [h,mul_nonneg eff (sub_nonneg.mpr bound)]

-- A trace-preserving continuation gives a stochastic row on each actual prefix.
theorem prefix_marginal {ι κ : Type*} [fintype κ] (w : ι→ℝ) (P : ι→κ→ℝ)
 (row : ∀i,∑j,P i j=1) (i : ι) : ∑j,w i*P i j=w i :=
by rw [←mul_sum,row,mul_one]

theorem changed_proxy (x : bool) : bnot x ≠ x := by cases x; simp

theorem unknown_logical_coherence (p vis : ℝ) (cap : p<1/100)
 (h : vis^2≤p) : vis<1/10 :=
begin by_contra no,have ge : 1/10≤vis := le_of_not_gt no,
 have k:=mul_nonneg (sub_nonneg.mpr ge) (show 0≤vis+1/10,by linarith only [ge]),
 nlinarith only [k,cap,h] end

theorem distinguishing_mark_bound (old fresh common : ℝ) (h : 0≤old)
 (f : 0≤fresh) (h0 : old=1) (hc : common^2≤old*fresh) :
 common^2≤fresh := by simpa [h0] using hc

theorem uniform_visits (s : ℕ→ℝ) (r : ℝ) (hr : 0≤r)
 (init : s 0≤1) (step : ∀k,s (k+1)≤r*s k) (k : ℕ) :
 s k≤r^k :=
begin induction k with n ih, {simpa using init},
 rw [pow_succ],exact le_trans (step n) (mul_le_mul_of_nonneg_left ih hr) end

theorem exits_telescope (s : ℕ→ℝ) (k : ℕ) :
 (∑n in range k,(s n-s(n+1)))+s k=s 0 :=
begin induction k with n ih, {simp},rw [sum_range_succ],linarith only [ih] end

theorem persistent_atom (w p : ℝ) (hw : 0≤w) (hp : p=1) (k : ℕ) :
 w*p^k=w := by simp [hp]

theorem bernoulli_defect (p : ℝ) (hp : 0≤p) (cap : p≤1) (k : ℕ) :
 1-(k:ℝ)*(1-p)≤p^k :=
begin
 induction k with n ih, {simp}, rw [pow_succ],push_cast,
 have g := mul_le_mul_of_nonneg_left ih hp,
 have rhs := mul_nonneg (show 0≤(n:ℝ),by positivity) (sq_nonneg (1-p)),
 nlinarith only [g,rhs]
end

theorem slow_survivors (p : ℝ) (hp : 0≤p) (cap : p≤1)
 (k : ℕ) (near_zero : (k:ℝ)*(1-p)≤1/2) : (1/2:ℝ)≤p^k :=
by linarith only [bernoulli_defect p hp cap k,near_zero]

theorem narrow_charges {ι : Type*} (s : finset ι) (w p : ι→ℝ)
 (hw : ∀i∈s,0≤w i) (hp : ∀i∈s,0≤p i) (cap : ∀i∈s,p i≤1)
 (k : ℕ) (condition : ∀i∈s,(k:ℝ)*(1-p i)≤1/2) :
 (∑i in s,w i)/2 ≤ ∑i in s,w i*(p i)^k :=
begin rw [sum_div],apply sum_le_sum,intros i hi,
 have h:=mul_le_mul_of_nonneg_left (slow_survivors (p i) (hp i hi) (cap i hi) k (condition i hi)) (hw i hi),
 linarith only [h] end

theorem spectral_variance {ι : Type*} [fintype ι] (w f : ι→ℝ) (mass : ∑i,w i=1) :
 (∑i,∑j,w i*w j*(f i-f j)^2)=
 2*((∑i,w i*(f i)^2)-(∑i,w i*f i)^2) :=
begin
 have term : ∀i j,w i*w j*(f i-f j)^2 =
   (w i*f i^2)*w j + w i*(w j*f j^2) - (2*(w i*f i))*(w j*f j) := λ i j,by ring,
 simp_rw [term,sum_sub_distrib,sum_add_distrib,←mul_sum],
 simp [mass,←sum_mul,←mul_sum],ring
end

theorem sin_square_bound (x : ℝ) : (real.sin x)^2≤x^2 :=
begin
 have poscase : ∀y : ℝ,0≤y→(real.sin y)^2≤y^2,
 {intros y hy, by_cases h1 : 1≤y,
  {have s:=real.sin_sq_add_cos_sq y,
   nlinarith only [s,sq_nonneg (real.cos y),mul_nonneg (sub_nonneg.mpr h1)
      (show 0≤y+1,by linarith only [hy])]},
  {rcases eq_or_lt_of_le hy with h|hp,
   {rw [←h],simp},
   {have hsin := real.sin_nonneg_of_nonneg_of_le_pi hy (le_trans (le_of_not_ge h1) (by linarith only [real.two_le_pi])),
    exact pow_le_pow_of_le_left hsin (real.sin_lt hp).le 2}}},
 by_cases h : 0≤x, {exact poscase x h},
 have hneg:=poscase (-x) (by linarith), simpa [real.sin_neg] using hneg
end

theorem cos_defect (x : ℝ) : 1-real.cos x ≤ x^2/2 :=
begin
 have c:=real.cos_two_mul (x/2),
 rw [show 2*(x/2)=x,by ring] at c,
 calc 1-real.cos x=2*(real.sin (x/2))^2 : by linarith only [c,real.sin_sq_add_cos_sq (x/2)]
 ... ≤ 2*(x/2)^2 : mul_le_mul_of_nonneg_left (sin_square_bound (x/2)) (by norm_num)
 ... = _ : by ring
end

theorem continuum_narrow_bound {α : Type*} [measurable_space α]
 (μ : measure_theory.measure α) (s : set α) (p : α→ℝ) (k : ℕ)
 (h₁ : measure_theory.integrable (s.indicator (λa:α,(1/2:ℝ))) μ)
 (h₂ : measure_theory.integrable (λa,(p a)^k) μ)
 (hp : ∀a,0≤p a) (cap : ∀a,p a≤1)
 (near : ∀a∈s,(k:ℝ)*(1-p a)≤1/2) :
 (∫a,s.indicator (λa:α,(1/2:ℝ)) a ∂μ)≤∫a,(p a)^k ∂μ :=
begin
 apply measure_theory.integral_mono h₁ h₂,intro a,
 by_cases ha : a∈s,
 {rw [set.indicator_of_mem ha],exact slow_survivors (p a) (hp a) (cap a) k (near a ha)},
 {rw [set.indicator_of_not_mem ha],exact pow_nonneg (hp a) _}
end

end private_history_reversal
