import tactic
import topology.algebra.order.intermediate_value
import analysis.special_functions.sqrt

noncomputable theory
namespace cat_compact_interior
open set

-- The normalized derivative of the on-shell total action under a singlet
-- symplectic variation.  T is the base trace, p one angular pressure.
theorem ward_density (r P k p T : ℝ) (hr : r≠0) (hP : P≠0) (hk : k≠0) :
  2*k*r^2*P*((P/r^2+r^2/P)/(2*k)+p-T/2)
  = r^4+P^2+k*r^2*P*(2*p-T) :=
by { field_simp [hr,hP,hk], ring }

theorem kinetic_trace (e m p t : ℝ) (shell : e^2=m^2+p^2+t^2) :
  e^2-p^2+t^2=m^2+2*t^2 := by linarith

theorem positive_load_bound (r P k D C : ℝ) (hP : 0≤P) (hk : 0≤k)
  (hd : 0≤D) (law : r^4+P^2+k*r^2*P*D=C) : r^4≤C :=
by { have h := mul_nonneg (mul_nonneg (mul_nonneg hk (sq_nonneg r)) hP) hd,
     linarith [sq_nonneg P] }

theorem negative_load_threshold (r P k D C : ℝ)
  (law : r^4+P^2+k*r^2*P*D=C) :
  4*(r^4-C) ≤ (k*r^2*D)^2 :=
by { nlinarith only [sq_nonneg (2*P+k*r^2*D), law] }

theorem dust_cone_threshold (y d : ℝ) (hd : d≠0) :
 (y^2)^4 + (2*y^7/d)^2 + d*y*(2*y^7/d) = 3*y^8+4*y^14/d^2 :=
by { field_simp [hd], ring }

-- The real-spin algebra in the two independent representations.
theorem angular_casimir (p q s t u v : ℝ) :
  (p*s+q*t)^2+(p*t-q*s)^2=(p^2+q^2)*(s^2+t^2) := by ring

theorem spin_energy_derivative (p q s t : ℝ) :
 2*s*(-2*(p^2+q^2)*p)+2*t*(-2*(p^2+q^2)*q)
   +2*(p^2+q^2)*(2*p*s+2*q*t)=0 := by ring

theorem conserved_angular_momentum (a b : ℝ) :
 a*(-2*(a^2+b^2)*b)-b*(-2*(a^2+b^2)*a)=0 := by ring

theorem compact_energy_derivative (p v : ℝ) :
 2*v*(-2*p^3)+4*p^3*v=0 := by ring

theorem pauli_energy_derivative (a b c u v w : ℝ) :
 2*u*(-a*(b^2+c^2))+2*v*(-b*(a^2+c^2))+2*w*(-c*(a^2+b^2))
 +2*a*u*(b^2+c^2)+2*b*v*(a^2+c^2)+2*c*w*(a^2+b^2)=0 := by ring

theorem exterior_data (x : ℝ) (hx : x≠0) :
 ((1+x^2)/(2*x))^2-((1-x^2)/(2*x))^2=1 ∧
 ((1+x^2)/(2*x))^2+((1-x^2)/(2*x))^2=(1+x^4)/(2*x^2) :=
by { split; field_simp [hx]; ring }

theorem zero_share_gap (x : ℝ) (hx : 0<x) :
 x-((1-x^2)/(2*x))/((1+x^4)/(2*x^2))=x^3*(1+x^2)/(1+x^4) :=
begin
 have hp : 0 < 1+x^4 := by positivity,
 field_simp [ne_of_gt hx,ne_of_gt hp], ring
end

theorem gap_positive (x : ℝ) (hx : 0<x) : 0<x^3*(1+x^2)/(1+x^4) :=
by positivity

-- All three independent constraints on the initial radius and its two derivatives.
theorem matched_radial_data (F l m x S D z e s : ℝ)
 (share : F^2*(l^2+m^2)=1-S) (hyp : m^2-l^2=1)
 (gap : D=x-F^2*l) (root : s^2=S) (hs : S≠0)
 (velocity : e*F*z^3*s=D)
 (acceleration : 3*S*z^2=2*D^2/S-(4*x^2-1)-F^2*(4*l^2-1)) :
 F^2*(l^2+m^2)+S=1 ∧ F^2*l+e*F*z^3*s=x ∧
 -(F^2*(3*l^2+m^2-2)+3*S*z^2-2*(e*F*z^3)^2)=4*x^2-1 :=
begin
 have hD : D^2=(e*F*z^3)^2*S := by rw [←velocity, ←root]; ring,
 have hd : D^2/S=(e*F*z^3)^2 := (div_eq_iff hs).2 hD,
 rw [mul_div_assoc, hd] at acceleration,
 refine ⟨by linarith, by linarith, _⟩,
 have h := congr_arg (λ u : ℝ, F^2*u) hyp,
 dsimp at h, nlinarith only [h,acceleration]
end

-- Continuous parametrization without singular denominators at S=0. W=S*z.
theorem rescaled_match (S D B z : ℝ) (hs : S≠0)
 (h : 3*S*z^2=2*D^2/S-B) : 3*(S*z)^2=2*D^2-S*B :=
begin
 field_simp [hs] at h, nlinarith only [h]
end

theorem small_spin_values (upper : ℝ) (hu : 0≤upper) (f : ℝ→ℝ)
 (hf : continuous_on f (Icc 0 upper)) (hf0 : f 0=0)
 (ratio : ℝ) (hp : 0<ratio) (hq : ratio≤f upper) :
 ∃ s ∈ Icc 0 upper, 0<s ∧ f s=ratio :=
begin
 have mem : ratio ∈ Icc (f 0) (f upper) := ⟨by simpa [hf0] using hp.le,hq⟩,
 obtain ⟨s,hs,he⟩ := intermediate_value_Icc hu hf mem,
 refine ⟨s,hs,_,he⟩,
 by_contra hn, have : s=0 := le_antisymm (le_of_not_gt hn) hs.1,
 rw [this,hf0] at he, linarith
end

-- For the actual polynomials of the joining problem, every sufficiently
-- small positive representation ratio is attained at a physical 0<S<1.
theorem attainable_ratios (x l K : ℝ) (hK : 0<K) (hD : 0<x-l/K) :
 let F : ℝ→ℝ := λ s, real.sqrt ((1-s)/K),
     D : ℝ→ℝ := λ s, x-((1-s)/K)*l,
     W : ℝ→ℝ := λ s, real.sqrt ((2*(D s)^2-s*(4*x^2-1+((1-s)/K)*(4*l^2-1)))/3) in
 ∃ emax>0, ∀ e, 0<e → e≤emax →
 ∃ s : ℝ, 0<s ∧ s<1 ∧ 0<D s ∧ 0<W s ∧
  D s*s^2*real.sqrt s/(F s*(W s)^3)=e :=
begin
 dsimp only,
 let F : ℝ→ℝ := λ s, real.sqrt ((1-s)/K),
 let D : ℝ→ℝ := λ s, x-((1-s)/K)*l,
 let W : ℝ→ℝ := λ s, real.sqrt ((2*(D s)^2-s*(4*x^2-1+((1-s)/K)*(4*l^2-1)))/3),
 let g : ℝ→ℝ := λ s, D s*s^2*real.sqrt s/(F s*(W s)^3),
 have cF : continuous F := by { dsimp [F], continuity },
 have cD : continuous D := by { dsimp [D], continuity },
 have cW : continuous W := by { dsimp [W,D], continuity },
 have pD : 0<D 0 := by { dsimp [D], simp only [sub_zero,one_div,div_eq_mul_inv] at *, simpa [mul_comm] using hD },
 have pF : 0<F 0 := by { dsimp [F], rw [real.sqrt_pos], simp [hK] },
 have pW : 0<W 0 := by { change 0<real.sqrt ((2*(D 0)^2-0*_)/3), rw [real.sqrt_pos], simp only [zero_mul,sub_zero], positivity },
 have hnear : {s : ℝ | 0<F s ∧ 0<D s ∧ 0<W s} ∈ nhds (0:ℝ) :=
  (continuous_at_const.eventually_lt cF.continuous_at pF).and
   ((continuous_at_const.eventually_lt cD.continuous_at pD).and
    (continuous_at_const.eventually_lt cW.continuous_at pW)),
 obtain ⟨r,hr,hh⟩ := metric.mem_nhds_iff.mp hnear,
 let b : ℝ := min (r/2) (1/2),
 have hb : 0<b := lt_min (by linarith) (by norm_num),
 have hb1 : b<1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num),
 have pos : ∀ s ∈ Icc 0 b, 0<F s ∧ 0<D s ∧ 0<W s :=
 begin
  intros s hs, apply hh, rw [metric.mem_ball,real.dist_eq,sub_zero,abs_of_nonneg hs.1],
  exact lt_of_le_of_lt (hs.2.trans (min_le_left _ _)) (by linarith),
 end,
 have cg : continuous_on g (Icc 0 b) :=
   (((cD.mul (continuous_id.pow 2)).mul real.continuous_sqrt).continuous_on).div
    ((cF.mul (cW.pow 3)).continuous_on)
    (λ s hs, mul_ne_zero (ne_of_gt (pos s hs).1) (pow_ne_zero _ (ne_of_gt (pos s hs).2.2))),
 have g0 : g 0=0 := by simp [g],
 have pb := pos b (right_mem_Icc.2 hb.le),
 have gb : 0<g b := div_pos ((mul_pos (mul_pos pb.2.1 (sq_pos_of_pos hb)) (real.sqrt_pos.2 hb)))
                                (mul_pos pb.1 (pow_pos pb.2.2 _)),
 refine ⟨g b,gb,λ e he heb,_⟩,
 obtain ⟨s,hs,hp,hv⟩ := small_spin_values b hb.le g cg g0 e he heb,
 exact ⟨s,hp,lt_of_le_of_lt hs.2 hb1,(pos s hs).2.1,(pos s hs).2.2,hv⟩
end

theorem matrix_and_schwarzschild_jerks (a da mu L : ℝ) (ha : a≠0)
 (hj : L^2=mu^2*a^4) :
 (-3*L^2/a^4-6*a^2)*da - (mu^2-6*a^2)*da = -4*mu^2*da :=
by { rw [hj], field_simp [ha], ring }

-- Inverting the continuous ratio gives exactly the z and compact velocity
-- needed by matched_radial_data, including the second derivative.
theorem reconstruct_compact (S D B W F e : ℝ)
 (hs : 0<S) (hw : 0<W) (hf : 0<F) (wlaw : 3*W^2=2*D^2-S*B)
 (ratio : e=D*S^2*real.sqrt S/(F*W^3)) :
 e*F*(W/S)^3*real.sqrt S=D ∧ 3*S*(W/S)^2=2*D^2/S-B :=
begin
 have h0 := real.sq_sqrt hs.le,
 split,
 { rw [ratio], field_simp [ne_of_gt hw,ne_of_gt hf,ne_of_gt hs],
   ring_nf at *, simp only [h0]; ring },
 { field_simp [ne_of_gt hs], nlinarith only [wlaw] }
end

theorem finite_spins_below (c e : ℝ) (hc : 0<c) (he : 0<e) :
 ∃ j : ℕ, 0<c/real.sqrt ((j:ℝ)*((j:ℝ)+1)) ∧ c/real.sqrt ((j:ℝ)*((j:ℝ)+1))<e :=
begin
 obtain ⟨j,hj⟩ := exists_nat_gt (c/e),
 have cj : 0<(j:ℝ) := lt_trans (div_pos hc he) hj,
 have cr : 0<(j:ℝ)*((j:ℝ)+1) := by positivity,
 have sq := real.sq_sqrt cr.le,
 have rt := real.sqrt_pos.2 cr,
 have le : (j:ℝ)≤real.sqrt ((j:ℝ)*((j:ℝ)+1)) := by nlinarith,
 refine ⟨j,div_pos hc rt,(div_lt_iff rt).2 _⟩,
 have h := (div_lt_iff he).1 hj, nlinarith only [h,mul_le_mul_of_nonneg_left le he.le]
end

theorem orthonormal_curvature_match (B R dB dR ddB ddR B' R' dB' dR' ddB' ddR' : ℝ)
 (hB : B=B') (hR : R=R') (hb : dB=dB') (hr : dR=dR') (hbb : ddB=ddB') (hrr : ddR=ddR') :
 (-ddB/B,-ddR/R,(dB/B)*(dR/R),1/R^2+(dR/R)^2)=
 (-ddB'/B',-ddR'/R',(dB'/B')*(dR'/R'),1/R'^2+(dR'/R')^2) :=
by rw [hB,hR,hb,hr,hbb,hrr]

theorem area_floor (a r L v eta w E M : ℝ) (ha : 0<a) (hM : 0<M)
 (upper : a^2≤M) (rad : r^4=v^2+L^2/a^2+eta^2*w^2)
 (energy : E=v^2+L^2/a^2+a^4) : L^2/M≤r^4 ∧ a^4≤E :=
begin
 have hdiv := div_le_div_of_le_left (sq_nonneg L) (sq_pos_of_pos ha) upper,
 have hn : 0≤L^2/a^2 := div_nonneg (sq_nonneg _) (sq_nonneg _),
 have hh := mul_nonneg (sq_nonneg eta) (sq_nonneg w),
 split; nlinarith only [rad,energy,hdiv,hh,sq_nonneg v,hn],
end

theorem compact_conservation (r a b E W eta d : ℝ) (rad : r^4=d+eta^2*(W-b^4))
 (ext : E=d+a^4) : r^4+a^4+eta^2*b^4=E+eta^2*W :=
by { rw [rad,ext], ring }

theorem deep_radius_bound (S w s : ℝ) (hS : 0≤S) :
  1-S ≤ 1-S+S*(w/s)^2 := by linarith [mul_nonneg hS (sq_nonneg (w/s))]

theorem deep_turn (S s : ℝ) : 1-S+S*((0:ℝ)/s)^2=1-S := by simp

theorem deep_strict_floor (S : ℝ) (hs : S<1/2) : (1:ℝ)/2<1-S := by linarith

theorem external_straight_line (v : ℝ) :
 (1-v/2)^2+(v/2)^2 = ((v-1)^2+1)/2 := by ring

theorem gram_clock_rate (u v du dv L : ℝ) (hl : u*dv-v*du=L) :
 (u*dv-v*du)/(u^2+v^2)=L/(u^2+v^2) := by rw [hl]

theorem real_kernel (C l a b : ℝ) :
 C^2*(a^2+b^2)-2*(C^2-l/2)*a*b=C^2*(a-b)^2+l*a*b := by ring

theorem regular_oscillator_wronskian (a b p q f : ℝ) :
 p*q+a*(-f*b)-q*p-b*(-f*a)=0 := by ring

-- In the reduced quantization, A=Var(w), V=<p^2>, K=sqrt(2<E>).
-- Robertson and the energy moment bound A≤K are the input quantum facts.
theorem quantum_area_floor (A V K e s S : ℝ) (hV : 0≤V) (hK : 0<K) (hS : 0≤S)
 (energy : A≤K) (uncertainty : e^2≤4*A*V) :
 1-S+S*((e^2/(4*K))/s^2)≤1-S+S*(V/s^2) :=
begin
 have h := mul_le_mul_of_nonneg_right energy hV,
 have bound : e^2/(4*K)≤V := (div_le_iff (by linarith : 0<4*K)).2 (by nlinarith only [h,uncertainty]),
 have q := mul_le_mul_of_nonneg_left (div_le_div_of_le (sq_nonneg s) bound) hS,
 linarith only [q]
end

theorem swap_double_commutator {M : Type*} [ring M] (p y : M) (h : p*p=1) :
 p*(p*y-y*p)-(p*y-y*p)*p=(y-p*y*p)+(y-p*y*p) :=
begin
 have h₁ : p*(p*y)=y := by rw [←mul_assoc,h,one_mul],
 have h₂ : y*p*p=y := by rw [mul_assoc,h,mul_one],
 simp only [mul_sub,sub_mul], rw [h₁,h₂,←mul_assoc p y p], abel
end

theorem mixed_colour_energy (a b g da db dg : ℝ) :
 3*da*(-8*a^3-2*g^2*(a-b))+3*db*(-8*b^3+2*g^2*(a-b))
 +(3/4)*dg*(-8*(a-b)^2*g)+24*(a^3*da+b^3*db)
 +6*g*dg*(a-b)^2+6*g^2*(a-b)*(da-db)=0 := by ring

theorem mixed_seed_starts (a g : ℝ) (ha : 0<a) (hg : 0<g) :
 0 < -8*(0:ℝ)^3+2*g^2*(a-0) := by { simp, positivity }

theorem compact_pulse_peak (c m : ℝ) (hc : c≠0) (hm : m≠0) :
 3*(8/(3*(m/c)^2))^2/c^2=64*c^2/(3*m^4) :=
by { field_simp [hc,hm], ring }

theorem compact_pulse_rank_bound (j : ℝ) (hj : 0<j) :
 64*j*(j+1)/(3*(2*j+1)^4) ≤ 4/(3*(j*(j+1))) :=
begin
 have h : 0<j*(j+1) := by positivity,
 have h₁ : 0<(2*j+1)^4 := by positivity,
 apply (div_le_div_iff (by linarith : 0<3*(2*j+1)^4) (by linarith : 0<3*(j*(j+1)))).2,
 nlinarith [sq_nonneg j]
end

end cat_compact_interior
