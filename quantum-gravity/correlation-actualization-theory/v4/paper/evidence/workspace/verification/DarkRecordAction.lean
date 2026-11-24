import analysis.special_functions.integrals
import analysis.calculus.deriv.slope
import measure_theory.integral.bochner
import tactic

noncomputable theory
open filter measure_theory
open_locale topology
namespace dark_record_action

def mode (j : ℕ) (x : ℝ) : ℝ := 1-real.cos ((j:ℝ)*x)
def quad (j : ℕ) : ℝ := (j:ℝ)^2
def coeff (j : ℕ) : ℝ := quad j*(quad j-1)/12

lemma convex_seq (f : ℕ→ℝ) (z : f 0=0) (one : 0≤f 1)
 (h : ∀n,0≤f(n+2)-2*f(n+1)+f n) (n : ℕ) : 0≤f n :=
begin
 have aux : ∀i:ℕ, 0≤f i ∧ 0≤f(i+1)-f i,
 {intro i,induction i with i ih,
  {rw [z],simp [one]},
  {change 0≤f (i+1) ∧ 0≤f(i+2)-f(i+1),
   specialize h i,split;linarith [ih.1,ih.2]}},
 exact (aux n).1
end

lemma mode_step (n : ℕ) (x : ℝ) :
 mode (n+2) x-2*mode (n+1) x+mode n x=2*mode 1 x*(1-mode (n+1) x) :=
begin
 let a : ℝ := ((n:ℝ)+1)*x,
 have h : ((n+2:ℕ):ℝ)*x=a+x, {dsimp [a],push_cast,ring},
 have h' : (n:ℝ)*x=a-x, {dsimp [a],ring},
 have h'' : ((n+1:ℕ):ℝ)*x=a, {dsimp [a],push_cast},
 unfold mode,rw [h,h'',h',real.cos_add,real.cos_sub],norm_num,ring
end

def deficit (j : ℕ) (x : ℝ) := quad j*mode 1 x-mode j x

lemma quad_step (n : ℕ) : quad(n+2)-2*quad(n+1)+quad n=2 :=
by {unfold quad,push_cast,ring}

lemma coeff_step (n : ℕ) : coeff(n+2)-2*coeff(n+1)+coeff n=quad(n+1) :=
by {unfold coeff quad,push_cast,ring}

lemma mode_nonneg (j : ℕ) (x : ℝ) : 0≤mode j x :=
sub_nonneg.mpr (real.cos_le_one _)

lemma deficit_step (n : ℕ) (x : ℝ) :
 deficit(n+2) x-2*deficit(n+1) x+deficit n x=2*mode 1 x*mode(n+1) x :=
begin unfold deficit,linear_combination (mode 1 x)*quad_step n-mode_step n x end

lemma deficit_nonneg (j : ℕ) (x : ℝ) : 0≤deficit j x :=
begin
 apply convex_seq (λi,deficit i x),
 {simp [deficit,quad,mode]}, {simp [deficit,quad,mode]},
 {intro n,change 0≤deficit(n+2) x-2*deficit(n+1) x+deficit n x,
  rw [deficit_step],exact mul_nonneg (mul_nonneg (by norm_num) (mode_nonneg 1 x)) (mode_nonneg _ x)}
end

lemma gap_two (x : ℝ) : 4*mode 1 x-mode 2 x=2*(mode 1 x)^2 :=
begin have h:=mode_step 0 x,simp [mode] at h ⊢,linarith end

theorem pointwise_rigidity (j : ℕ) (x : ℝ) :
 0≤deficit j x ∧ deficit j x≤coeff j*(4*mode 1 x-mode 2 x) :=
begin
 refine ⟨deficit_nonneg j x,_⟩,rw [gap_two],
 suffices bound : 0≤coeff j*(2*(mode 1 x)^2)-deficit j x, by linarith,
 apply convex_seq (λi,coeff i*(2*(mode 1 x)^2)-deficit i x),
 {simp [coeff,deficit,quad,mode]}, {simp [coeff,deficit,quad,mode]},
 {intro n, change 0≤(coeff(n+2)*(2*mode 1 x^2)-deficit(n+2) x)-
       2*(coeff(n+1)*(2*mode 1 x^2)-deficit(n+1) x)+(coeff n*(2*mode 1 x^2)-deficit n x),
  have h : (coeff(n+2)*(2*mode 1 x^2)-deficit(n+2) x)-
       2*(coeff(n+1)*(2*mode 1 x^2)-deficit(n+1) x)+(coeff n*(2*mode 1 x^2)-deficit n x)
        =2*mode 1 x*deficit(n+1) x,
  {change _ = 2*mode 1 x*(quad(n+1)*mode 1 x-mode(n+1) x),
   linear_combination (2*mode 1 x^2)*coeff_step n-deficit_step n x},
  rw [h],exact mul_nonneg (mul_nonneg (by norm_num) (mode_nonneg 1 x)) (deficit_nonneg _ x)}
end

def moment (μ : measure ℝ) (i : ℕ) : ℝ := ∫ x,mode i x ∂μ

theorem integrated_bounds (μ : measure ℝ) (hi : ∀i,integrable (mode i) μ) (j : ℕ) :
 0≤quad j*moment μ 1-moment μ j ∧
 quad j*moment μ 1-moment μ j≤coeff j*(4*moment μ 1-moment μ 2) :=
begin
 have hd : integrable (λx,quad j*mode 1 x-mode j x) μ := ((hi 1).const_mul _).sub (hi j),
 have ht : integrable (λx,(4:ℝ)*mode 1 x-mode 2 x) μ := ((hi 1).const_mul _).sub (hi 2),
 have lo := integral_nonneg (λx,(pointwise_rigidity j x).1),
 have up := integral_mono hd (ht.const_mul (coeff j)) (λx,(pointwise_rigidity j x).2),
 change 0≤∫ x,(quad j*mode 1 x-mode j x) ∂μ at lo,
 change (∫ x,(quad j*mode 1 x-mode j x) ∂μ)≤∫ x,coeff j*(4*mode 1 x-mode 2 x) ∂μ at up,
 unfold moment,
 rw [integral_sub ((hi 1).const_mul _) (hi j),integral_mul_left] at lo up,
 rw [integral_mul_left,integral_sub ((hi 1).const_mul _) (hi 2),integral_mul_left] at up,
 exact ⟨lo,up⟩
end

theorem generator_bounds (law : ℕ→measure ℝ) (vol : ℕ→ℝ) (ψ : ℕ→ℝ)
 (hv : ∀i,0<vol i) (hi : ∀i j,integrable (mode j) (law i))
 (slope : ∀j,tendsto (λi,moment (law i) j / vol i) at_top (nhds (ψ j))) (j : ℕ) :
 0≤quad j*ψ 1-ψ j ∧ quad j*ψ 1-ψ j≤coeff j*(4*ψ 1-ψ 2) :=
begin
 have cw : ∀k:ℝ,tendsto (λi:ℕ,k) at_top (nhds k) := λk,tendsto_const_nhds,
 have lhs := ((cw (quad j)).mul (slope 1)).sub (slope j),
 have rhs := (cw (coeff j)).mul (((cw 4).mul (slope 1)).sub (slope 2)),
 split,
 {apply le_of_tendsto_of_tendsto' tendsto_const_nhds lhs,intro i,
  have h:=div_nonneg (integrated_bounds (law i) (hi i) j).1 (le_of_lt (hv i)),
  dsimp,convert h using 1; ring},
 {apply le_of_tendsto_of_tendsto' lhs rhs,intro i,
  have h:=div_le_div_of_le (le_of_lt (hv i)) (integrated_bounds (law i) (hi i) j).2,
  dsimp,convert h using 1; ring}
end

theorem two_modes_fix_all (ψ : ℕ→ℝ)
 (est : ∀j,0≤quad j*ψ 1-ψ j ∧ quad j*ψ 1-ψ j≤coeff j*(4*ψ 1-ψ 2))
 (second : ψ 2=4*ψ 1) (j : ℕ) : ψ j=quad j*ψ 1 :=
begin have h:=est j,rw [second,sub_self,mul_zero] at h,linarith [h.1,h.2] end

theorem lapse_sound (x : ℝ) (hx : 1≤x) :
 -(2*x*(x+9))/(3*(1+x)*(3+x)) ≤ -(2/3:ℝ) :=
begin
 have hd : 0<3*(1+x)*(3+x) := by positivity,
 apply (div_le_iff hd).2,nlinarith
end

theorem no_positive_vacuum (F G D R : ℝ) (f : 0<F) (g : 0≤G) (dust : 0≤D)
 (stationary : -21*F-15*G+9*R-3/2*D=0) : F+G-R<0 := by linarith

theorem volume_window (F C R : ℝ) (f : 0<F)
 (stationary : -21*F+9*R+18*C=0) :
 (0<F-C-R ∧ 0<441*F-81*R-324*C) ↔ (4*F/3<C ∧ C<14*F/9) :=
by {split;intro h;cases h;split;linarith}

theorem stationary_elimination (F G D R W W1 W2 : ℝ)
 (h : -21*F-15*G+9*R-3*D/2+W1=0) :
 9*(F+G-R+W)= -12*F-6*G-3*D/2+W1+9*W ∧
 441*F+225*G-81*R+9*D/4+W2=252*F+90*G-45*D/4+W2+9*W1 :=
by {split;linarith}

theorem fold_and_zero (C A z s : ℝ)
 (hz : A*z=3*C/4) (hs : A*s=9*C/14) :
 A*z^7-C*z^6+C*z^3/4*z^3=0 ∧
 7*A*s^4-6*C*s^3+3*(C*s^3/2)=0 :=
by {split,linear_combination z^6*hz,linear_combination 7*s^3*hs}

theorem flux_balance (a k n : ℝ) : a*(k+n)^2-a*k^2=a*(2*k*n+n^2) := by ring

theorem matrix_barrier (res A : ℝ) (h : 0≤res) (a : 0≤A) :
 2*A≤A*(2+res) := by nlinarith [mul_nonneg a h]

theorem cosine_parity_counterexample :
 (1:ℝ) = 1/2*1^2+1/4*2 ∧ (2:ℝ) = 1/2*2^2 ∧ (5:ℝ) = 1/2*3^2+1/4*2 := by norm_num

theorem ruler_degeneracy (l h r : ℝ) (hl : l≠0) : (l*h)*(r/l)=h*r := by {field_simp,ring}

theorem relative_tolerance (q gap base eps loss : ℝ) (hq : 0<q) (hb : 0<base)
 (h : loss ≤ q*(q-1)*gap/12) (tol : (q-1)*gap≤12*eps*base) :
 loss/(q*base)≤eps :=
begin apply (div_le_iff (mul_pos hq hb)).2,
 have aux:=mul_le_mul_of_nonneg_left tol (le_of_lt hq),nlinarith end

theorem radial_fold_ratio (C B ym ys am ass km ks : ℝ) (hc : 0<C) (hm : 0<ym)
 (a : 0<am) (hmk : 0<km) (hs : 0<ys)
 (b1 : 4*B=C*ym^3) (b2 : 2*B=C*ys^3)
 (y0 : 4*(am*km^2)*ym=3*C) (y1 : 14*(ass*ks^2)*ys=9*C)
 (same : ass=am) :
 ym^3=2*ys^3 ∧ 7*ks^2*ys=6*km^2*ym :=
begin subst ass,split,
 {apply (mul_left_cancel₀ (ne_of_gt hc)),linear_combination (2*b2-b1)},
 {apply (mul_left_cancel₀ (ne_of_gt a)),linear_combination y1/2-3*y0/2}
end

theorem fit_all_charges (k lo hi M : ℝ) (left : lo<k-M) (right : k+M<hi) :
 2*M<hi-lo := by linarith

theorem fold_density_root (A k y C B : ℝ) :
 7*A*k^2*y^6-6*C*y^5+3*B*y^2=y^2*(7*A*k^2*y^4-6*C*y^3+3*B) := by ring

theorem same_record_no_witness (a b : ℝ) (h : a=b) : |a-b|=0 := by simp [h]

theorem flux_energy_cap (E k mean variance hop J : ℝ) (e : E*(2*k*mean+variance)+hop=0)
 (h : |hop|≤J) : |E*(2*k*mean+variance)|≤J :=
begin have q : E*(2*k*mean+variance) = -hop := by linarith,rw [q,abs_neg],exact h end

theorem fourth_circle (a : ℝ) :
 (∫ x in (0:ℝ)..(2*real.pi), (a^2*(real.cos x)^2+a^4*(real.sin x)^4))=
        (2*real.pi)*(a^2/2+3*a^4/8) :=
begin
 have hc : interval_integrable (λx:ℝ,a^2*(real.cos x)^2) volume 0 (2*real.pi) :=
     (continuous_const.mul (real.continuous_cos.pow 2)).interval_integrable _ _,
 have hs : interval_integrable (λx:ℝ,a^4*(real.sin x)^4) volume 0 (2*real.pi) :=
     (continuous_const.mul (real.continuous_sin.pow 4)).interval_integrable _ _,
 rw [interval_integral.integral_add hc hs], dsimp only,
 have fourth : (∫ x in (0:ℝ)..(2*real.pi),real.sin x ^ (2+2:ℕ))=3*real.pi/4,
 {rw [integral_sin_pow,integral_sin_sq],norm_num [real.sin_two_pi,real.cos_two_pi],ring},
 rw [interval_integral.integral_const_mul,interval_integral.integral_const_mul,integral_cos_sq,fourth],
 simp [real.sin_two_pi,real.cos_two_pi],ring
end

theorem squared_norm_envelope (a b : ℝ) (ha : 0≤a) (hb : 0≤b) :
 a^2+b^2≤(a+b)^2 := by nlinarith [mul_nonneg ha hb]

theorem volume_slope (b : ℝ) (v : ℕ→ℝ) (hp : ∀i,0<v i)
 (hz : tendsto v at_top (nhds 0)) :
 tendsto (λi,(1-real.exp (v i*(-b)))/v i) at_top (nhds b) :=
begin
 have hf : has_deriv_at (λx:ℝ,1-real.exp (x*(-b))) b 0,
 {simpa using ((((has_deriv_at_id (0:ℝ)).mul_const (-b)).exp).const_sub 1)},
 rw [has_deriv_at_iff_tendsto_slope,slope_fun_def_field] at hf,
 have off : tendsto v at_top (nhds_within (0:ℝ) ({0}:set ℝ)ᶜ),
 {apply tendsto_nhds_within_of_tendsto_nhds_of_eventually_within v hz,
  exact eventually_of_forall (λi,show v i≠0,from ne_of_gt (hp i))},
 simpa [function.comp] using hf.comp off
end

theorem calibrated_flux_law (μ : ℕ→measure ℝ) (v : ℕ→ℝ) (ψ : ℕ→ℝ)
 (hp : ∀i,0<v i) (hz : tendsto v at_top (nhds 0))
 (hi : ∀i j,integrable (mode j) (μ i))
 (law : ∀i j,moment (μ i) j=1-real.exp (v i*(-ψ j)))
 (second : ψ 2=4*ψ 1) (j : ℕ) : ψ j=quad j*ψ 1 :=
begin
 apply two_modes_fix_all ψ _ second,
 apply generator_bounds μ v ψ hp hi,
 intro k,simpa only [law] using volume_slope (ψ k) v hp hz
end

theorem heat_character_glue (s t b : ℝ) (n : ℕ) :
 real.exp (-s*b*quad n)*real.exp (-t*b*quad n)=real.exp (-(s+t)*b*quad n) :=
by {rw [←real.exp_add],congr' 1,ring}

theorem joint_charges (m q E u : ℝ) :
 (m+1)+(q-1)=m+q ∧ u*(m+1)^2+(E-u*(2*m+1))=u*m^2+E := by {split;ring}

theorem energy_shell (u M k : ℝ) : u*((k+M)^2-k^2)=u*(2*k*M+M^2) := by ring

theorem interval_packet (W δ : ℝ) (w : 0<W) (d : 0≤δ) :
 max 0 (min W (W+δ)-max 0 δ)/W=max 0 (1-δ/W) :=
begin
 have m : min W (W+δ)=W := min_eq_left (by linarith),
 rw [m,max_eq_right d],by_cases h : δ≤W,
 {have z : 0≤1-δ/W := sub_nonneg.mpr ((div_le_one w).2 h),
  rw [max_eq_right (sub_nonneg.mpr h),max_eq_right z,sub_div,div_self w.ne']},
 {have z : 1-δ/W≤0 := sub_nonpos.mpr ((one_le_div w).2 (le_of_not_ge h)),
  have z' : W-δ≤0 := by linarith,
  rw [max_eq_left z',max_eq_left z,zero_div]}
end

theorem coherence_window (W delta : ℝ) (h : 0<W) :
 (99/100:ℝ)≤1-delta/W ↔ 100*delta≤W :=
begin have equiv : delta/W≤1/100 ↔ delta≤(1/100)*W := div_le_iff h,
 split; intro hi,
 {have hb : delta/W≤1/100 := by linarith, have hh := equiv.1 hb, linarith},
 {have hh : delta≤(1/100)*W := by linarith, have hb:=equiv.2 hh,linarith}
end

theorem membrane_calibration (MP Z e σ : ℝ) (z : 0<Z) (p : MP≠0)
 (norm : 2*Z*σ^2=MP^2*e^2) : e^2/(2*Z)=σ^2/MP^2 :=
by {apply (div_eq_div_iff (by positivity : 2*Z≠0) (pow_ne_zero 2 p)).2,linarith}

theorem wall_radius_squared (inside outside f wall R : ℝ)
 (i : inside^2=1-(f-wall)*R^2) (o : outside^2=1-f*R^2)
 (h : inside-outside=R) (r : R≠0) :
 4=R^2*(4*f+(wall-1)^2) :=
begin
 have sum0 : R*(inside+outside)=R*(wall*R),
 {linear_combination (inside+outside)*(-h)+i-o},
 have sm := mul_left_cancel₀ r sum0,
 have p : 2*outside=R*(wall-1) := by linarith [sm,h],
 linear_combination (-4)*o+(2*outside+R*(wall-1))*p
end

theorem window_polynomial (v : ℝ) (p : 0≤v) : 1+8*v≤(1+4*v)*(1+v)^4 :=
begin
 have h : (1+4*v)*(1+v)^4-(1+8*v)=v^2*(22+28*v+17*v^2+4*v^3) := by ring,
 have pos : 0≤v^2*(22+28*v+17*v^2+4*v^3) := by positivity,linarith
end

theorem radius_margin (r v : ℝ) (hr : 1≤r) (p : 0≤v)
 (law : r^6*(1+v)^4=1+8*v) : 2*(r-1)≤4*v/3 :=
begin
 have b : r^6≤1+4*v,
 {by_contra neg,push_neg at neg,
  have h:=mul_lt_mul_of_pos_right neg (show 0<(1+v)^4,by positivity),
  linarith [window_polynomial v p]},
 have t : 0≤r-1 := by linarith,
 have expn : r^6-(1+6*(r-1))=(r-1)^2*(15+20*(r-1)+15*(r-1)^2+6*(r-1)^3+(r-1)^4) := by ring,
 have pos : 0≤(r-1)^2*(15+20*(r-1)+15*(r-1)^2+6*(r-1)^3+(r-1)^4) := by positivity,
 linarith
end

theorem wall_three_term_identity (r v y : ℝ) (hy : 0<y)
 (charge : r^2*y*(1+v)=1) (curv : y^3*(1+8*v)=1+v) :
 r^6*(1+v)^4=1+8*v :=
begin
 have c : (r^2*y*(1+v))^3=1 := by rw [charge,one_pow],
 apply mul_left_cancel₀ (show y^3≠0,from pow_ne_zero 3 hy.ne'),
 linear_combination (1+v)*c-curv
end

theorem wall_factor (k : ℝ) (h : 1≤k) :
 0<(8*k-7)^2/(48*k^2) ∧ (8*k-7)^2/(48*k^2)<4/3 :=
begin have dk : 0<48*k^2 := by positivity,split,
 {apply div_pos _ dk,have t : 0<8*k-7 := by linarith,positivity},
 {apply (div_lt_iff dk).2,nlinarith} end

theorem stable_local_bubble (κ M g η f : ℝ) (kpos : 0<κ) (mpos : 0<M)
 (e : 2*M<κ*η) (he : 0<η) (hf : 0<f) (cap : f≤4/3)
 (radius : g=η/(η+f)) : 3*M/(2*κ+3*M)<g :=
begin rw [radius],apply (div_lt_div_iff (show 0<2*κ+3*M,by positivity) (add_pos he hf)).2,
 have lim:=mul_le_mul_of_nonneg_left cap (show 0≤3*M,by positivity),
 nlinarith only [e,lim]
end

theorem local_budget_rank (k m eps : ℝ) (hk : 0<k) (hm : 0<m) (he : 0<eps)
 (bound : 3*m/(2*k+3*m)<eps^2) : (3*m/2)*(1/eps^2-1)<k :=
begin
 have h:=(div_lt_iff (show 0<2*k+3*m,by positivity)).1 bound,
 have eqn : (3*m/2)*(1/eps^2-1)=((3*m/2)*(1-eps^2))/eps^2 :=
     by {field_simp [he.ne'];ring},
 rw [eqn],apply (div_lt_iff (show 0<eps^2,by positivity)).2,nlinarith only [h]
end

end dark_record_action
