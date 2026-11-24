import tactic
import data.real.sqrt
import data.complex.basic

/- Finite algebra behind the CAT calculations, with physical input explicit. -/
namespace cat_relational_collapse
noncomputable theory

theorem vector_spinor_count (d : ℕ) (h : d = 2 + 16 / 2) : d = 10 := h
theorem scalar_alternative : 4 - 2 + 6 = (8:ℕ) := rfl
theorem anomaly_count (d : ℝ) (h : d + d/2 - 26 + 11 = 0) : d=10 := by linarith
theorem dust_weyl (g m r density pi0 : ℝ) (h : m/r^3=4*pi0*density/3) :
  g*m/r^3-4*pi0*g*density/3=0 := by { rw [mul_div_assoc, h], ring }

def a (s : ℝ) := (1/s^4+4*s)/5
def b (s : ℝ) := 3*(s^4-1/s)/5
def c (s : ℝ) := 4*(s-1/s^4)/15
def d (s : ℝ) := (4/s+s^4)/5
theorem jacobi_det (s : ℝ) (hs : s ≠ 0) : a s*d s-b s*c s=1 :=
by { unfold a b c d, field_simp [hs]; ring }
theorem relative_trace (s : ℝ) (hs : s ≠ 0) :
  a s+d s+(1-s^3)*c s =
  2-(s+1/s-2)^2*((s+1/s)^2+4*(s+1/s)+8)/15 :=
by { unfold a c d, field_simp [hs]; ring }
theorem trace_at_four : a 4+d 4+(1-(4:ℝ)^3)*c 4= -32086/2560 :=
by { unfold a c d, norm_num }
theorem roots_negative (x y : ℝ) (hp : x*y=1) (ht : x+y<0) : x<0 ∧ y<0 :=
begin
  have hn : ¬ (0 ≤ x ∧ 0 ≤ y) := by { rintro ⟨hx,hy⟩, linarith },
  rcases lt_trichotomy x 0 with hx|hx|hx,
  { refine ⟨hx, _⟩, by_contra hy, push_neg at hy, nlinarith [mul_nonpos_of_nonpos_of_nonneg (le_of_lt hx) hy] },
  { rw [hx,zero_mul] at hp, norm_num at hp },
  { have hy : y<0 := by { by_contra hh, push_neg at hh, exact hn ⟨le_of_lt hx,hh⟩ },
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (le_of_lt hx) (le_of_lt hy)] }
end
theorem real_roots (t : ℝ) (ht : t < -2) :
  ∃ x y : ℝ, x+y=t ∧ x*y=1 ∧ x<0 ∧ y<0 :=
begin
  have hp : 0 ≤ t^2-4 := by nlinarith [mul_nonneg (le_of_lt (show 0 < -t-2, by linarith)) (show 0 ≤ -t+2, by linarith)],
  let x := (t+real.sqrt (t^2-4))/2,
  let y := (t-real.sqrt (t^2-4))/2,
  have hs : x+y=t := by { dsimp [x,y], ring },
  have hm : x*y=1 := by { dsimp [x,y], nlinarith [real.sq_sqrt hp] },
  exact ⟨x,y,hs,hm,roots_negative x y hm (by linarith)⟩
end
theorem signed_readout (u v ell k x p scale : ℝ) (hs : scale<0)
  (hi : 0<ell*x+k*p) (h1 : u=scale*ell) (h2 : v=scale*k) :
  u*x+v*p<0 :=
by { rw [h1,h2], calc scale*ell*x+scale*k*p = scale*(ell*x+k*p) : by ring
   ... < 0 : mul_neg_of_neg_of_pos hs hi }
theorem flux_transfer (q c k : ℤ) : (q+k)+(c-k)=q+c := by ring

/- For any pair of spinor magnetic basis states, this is the scalar action
   of a commuting block. The intertwiners for larger j use Schur's lemma. -/
theorem spin_half_commutant (a b c d : ℂ)
  (hz1 : b = -b) (hz2 : c = -c) (hx : a=d) : b=0 ∧ c=0 ∧ a=d :=
begin
  have two : (2:ℂ) ≠ 0 := by norm_num,
  have hb : (2:ℂ)*b=0 := by linear_combination hz1,
  have hc : (2:ℂ)*c=0 := by linear_combination hz2,
  exact ⟨(mul_eq_zero.mp hb).resolve_left two,(mul_eq_zero.mp hc).resolve_left two,hx⟩
end
theorem fidelity_bounds (p r s : ℝ) (hp : 0≤p) (hs : 0≤s) (hu : s≤1)
  (h : r^2=1-s^2) : p*r^2/4 ≤ p*(1-s)/2 ∧ p*(1-s)/2 ≤ p*r^2/2 :=
begin
  have a : 0≤p*(1-s)^2 := mul_nonneg hp (sq_nonneg _),
  have b : 0≤p*(s*(1-s)) := mul_nonneg hp (mul_nonneg hs (by linarith)),
  rw [h], constructor; nlinarith
end
theorem bell_return (p : ℝ) : 1-(p^2+(1-p)^2)=2*p*(1-p) := by ring
theorem balanced_peak (p : ℝ) : 2*p*(1-p)≤1/2 := calc 2*p*(1-p) = 1/2 - 2*(p-1/2)^2 : by ring
 ... ≤ 1/2 : sub_le_self _ (mul_nonneg (by norm_num) (sq_nonneg _))
theorem angular_return (c : ℝ) :
 ((1+c)/2)^2+((1-c)/2)^2=(1+c^2)/2 := by ring

/- Finite Neumann sum of a nilpotent linear update on an additive group. -/
def accumulate {V : Type*} [add_comm_group V] (f : V →+ V) (x : V) : ℕ → V
| 0 := 0
| (n+1) := x+f (accumulate n)
theorem history_remainder {V : Type*} [add_comm_group V] (f : V →+ V) (x : V) (n : ℕ) :
  accumulate f x (n+1)-accumulate f x n = (f^[n]) x :=
begin
  induction n with n ih,
  { simp [accumulate] },
  { change (x+f (accumulate f x (n+1))) - (x+f (accumulate f x n)) = _,
    rw [add_sub_add_left_eq_sub, ← f.map_sub, ih, function.iterate_succ_apply'] }
end
theorem history_fixed {V : Type*} [add_comm_group V] (f : V →+ V) (x : V) (n : ℕ)
  (hn : (f^[n]) x=0) : accumulate f x n=x+f (accumulate f x n) :=
begin
  have h := history_remainder f x n,
  rw [hn, sub_eq_zero] at h, exact h.symm
end
theorem unique_history {V : Type*} [add_comm_group V] (f : V →+ V) (x a b : V)
  (ha : a=x+f a) (hb : b=x+f b) (n : ℕ) (hn : (f^[n]) (a-b)=0) : a=b :=
begin
  have h : f (a-b)=a-b := by { rw [f.map_sub], conv_rhs {rw [ha,hb]}, abel },
  have rec : ∀ m : ℕ, (f^[m]) (a-b)=a-b,
  { intro m, induction m with m ih, {refl}, {rw [function.iterate_succ_apply', ih, h]} },
  rw [rec] at hn, exact sub_eq_zero.mp hn
end
theorem central_double_comm {R : Type*} [ring R] (x y z w : R)
  (inner : y*z-z*y=w) (central : x*w=w*x) : x*(y*z-z*y)-(y*z-z*y)*x=0 :=
by rw [inner,central,sub_self]
theorem lorentz_cone (e m u v w z : ℝ) :
 -(e*v)^2+(-e*u)^2+(m*z)^2+(-m*w)^2 =
 e^2*u^2-e^2*v^2+m^2*w^2+m^2*z^2 := by ring

/- Matrix-element consequences of intertwining the magnetic and raising
   generators on one fixed irreducible multiplet. -/
theorem distinct_weights_zero (m n x : ℂ) (hd : m≠n) (hz : m*x=n*x) : x=0 :=
begin
  have h : (m-n)*x=0 := by { rw [sub_mul,hz,sub_self] },
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hd)
end
theorem equal_adjacent (w x y : ℂ) (hw : w≠0) (h : w*x=w*y) : x=y :=
(mul_left_cancel₀ hw h)
theorem constant_multiplet {α : Type*} (diag : ℕ → α) (n : ℕ)
  (step : ∀ k<n, diag (k+1)=diag k) : diag n=diag 0 :=
begin
  induction n with n ih, {refl},
  exact (step n (nat.lt_succ_self n)).trans (ih (λ k hk, step k (nat.lt_succ_of_lt hk)))
end
theorem clifford_flip {V : Type*} [add_comm_group V] [module ℂ V]
  (A B : V →ₗ[ℂ] V) (v : V) (s : ℂ)
  (ev : A v=s • v) (h : A (B v) = -B (A v)) : A (B v)=(-s) • (B v) :=
by { rw [h,ev,B.map_smul,neg_smul] }
theorem sign_sector_dimension (r : ℕ) (hr : 0<r) : 16 < 2^5*r :=
by { change 16 < 32*r, nlinarith }
theorem mode_sign_bound (k : ℝ) (h : 0<k) (r s : ℝ) (hneg : r<0)
  (value : s=r*k) : s<0 := by {rw [value], exact mul_neg_of_neg_of_pos hneg h}
theorem causal_integrand (s : ℝ) (h : s+1≠0) :
  s^3/(s+1)=s^2-s+1-1/(s+1) := by { field_simp [h], ring }
theorem clock_lapse (x : ℝ) (h : 1+x ≠ 0) (k : 1-x≠0) :
 (1-x)/(1-x^2)=1/(1+x) :=
begin
  have fac : 1-x^2=(1-x)*(1+x) := by ring,
  rw [fac], field_simp [h,k]
end

theorem charge_effect {R : Type*} [monoid R] (dU dP dB B P U : R)
  (iso : dB * B = 1) (proj : dP*P = P) :
 (dU*dP*dB)*(B*P*U)=dU*P*U :=
begin
  calc (dU*dP*dB)*(B*P*U) = dU*((dP*(dB*B))*P)*U : by simp only [mul_assoc]
  ... = dU*P*U : by rw [iso,mul_one,proj]
end
theorem rotor_axial_integrals :
 (3:ℝ)/5-1/3=4/15 ∧ (1:ℝ)/5-1/3= -2/15 ∧
 (-(3:ℝ)/4)*(2-4/3+2/5)=-(4:ℝ)/5 := by norm_num
theorem rotor_exchange_factor :
 (-(1:ℝ)/4)*6*(4/25)= -(6:ℝ)/25 := by norm_num
theorem axial_charge_values (v : ℝ) (h : v=1/2) :
 (1-v^4=15/16) ∧ (1-v=1/2) ∧ ((1-v^4)-(1-v)=7/16) :=
by {rw [h], norm_num}
theorem axial_bias_pair : (((15:ℝ)/16-1/2)/(15/16+1/2)=7/23) ∧
 (((1:ℝ)/2-1/16)/(1/2+1/16)=7/9) := by norm_num
theorem sign_dark (m : ℤ) (h : m= -1) : m-2 < -1 := by linarith
theorem polar_overlap (p q a b c d : ℝ)
 (hp : a^2+b^2=1) (hq : c^2+d^2=1) (h1 : p=a*c) (h2 : q=b*d) :
 ((a+c)^2+(b+d)^2)/4=(1+p+q)/2 := by { rw [h1,h2], nlinarith }

end cat_relational_collapse
