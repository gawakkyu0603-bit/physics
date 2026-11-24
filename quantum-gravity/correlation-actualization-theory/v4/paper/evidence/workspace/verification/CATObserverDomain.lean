import data.complex.basic
import algebra.big_operators.basic
import tactic

noncomputable theory
open_locale big_operators
namespace cat_observer_domain

-- Physical inputs: the contracted metric is mostly plus and the probe index is spacelike.
theorem two_index_orders (k g : ℝ) (hg : g ≠ 0) :
 (k+k)/(4*g^2)=k/(2*g^2) := by field_simp; ring

theorem scalar_clock_factor (v : ℂ) : -(-complex.I*v)^2=v^2 :=
calc -(-complex.I*v)^2 = -(complex.I*complex.I)*v^2 : by ring
 ... = v^2 : by rw [complex.I_mul_I]; ring

theorem symbol_factor (u v : ℂ) :
 (complex.I*u)*(complex.I*v)=-(u*v) :=
calc (complex.I*u)*(complex.I*v)=(complex.I*complex.I)*(u*v) : by ring
 ... = -(u*v) : by rw [complex.I_mul_I]; ring

-- Each value can itself be a matrix or the value of a history operation on a state.
theorem partition_total {Z R M : Type*} [fintype Z] [fintype R] [decidable_eq R]
 [add_comm_monoid M] (read : Z → R) (v : Z → M) :
 (∑ r : R, ∑ z : Z, if read z = r then v z else 0) = ∑ z : Z, v z :=
by classical; rw [finset.sum_comm]; simp

-- The second operation and weights may depend on the first contact's actual outcome.
theorem adaptive_total {Z W : Type*} [fintype Z] [fintype W]
 (a : Z → ℝ) (b : Z → W → ℝ) (ha : ∑ z, a z = 1)
 (hb : ∀ z, ∑ w, b z w = 1) : (∑ z, ∑ w, a z * b z w) = 1 :=
by simp_rw [← finset.mul_sum, hb, mul_one]; exact ha

theorem selected_dimensions :
 2 * max (1+(0:ℤ)) 0 = 2 ∧ 2 * max (1+(-1:ℤ)) 0 = 0 := by norm_num

theorem overlap_pullback {S P Q E : Type*} (s : S) (v : S → P) (w : S → Q)
 (a : P → E) (b : Q → E) (transport : ∀ x, a (v x) = b (w x)) :
 a (v s) = b (w s) := transport s

-- For local factors the maps commute for each retained outcome.
theorem independent_contacts {A B : Type*} (f : A → A) (g : B → B) (x : A × B) :
 prod.map f id (prod.map id g x) = prod.map id g (prod.map f id x) :=
by cases x; refl

-- One Kraus term at each contact, with adjoints kd and ld. Local tensor factors
-- supply both commutation hypotheses, for arbitrary (also entangled) input r.
theorem labelled_kraus_swap {M : Type*} [semigroup M] (k l kd ld r : M)
 (forward : k*l=l*k) (backward : ld*kd=kd*ld) :
 k*(l*r*ld)*kd = l*(k*r*kd)*ld :=
calc k*(l*r*ld)*kd = (k*l)*(r*(ld*kd)) : by simp only [mul_assoc]
 ... = (l*k)*(r*(kd*ld)) : by rw [forward, backward]
 ... = l*(k*r*kd)*ld : by simp only [mul_assoc]

theorem order_witness : (1:ℚ)*(1/2) = 1/2 ∧ (1/2:ℚ)*(1/2) = 1/4 ∧ (1/2:ℚ) ≠ 1/4 :=
by norm_num

-- In the return basis the I/X randomization changes the sign of the off-diagonal element.
theorem twirl_off_diagonal (u : ℂ) : (u+(-u))/2=0 := by ring

theorem false_return_reset (p : ℝ) : (1-p/2)*1+(p/2)*1=1 := by ring

theorem readout_upper (p pl a b e : ℝ) (hp : pl ≤ p) (hp0 : 0 ≤ p)
 (hp2 : p ≤ 2) (ha : a ≤ 1) (hb : b ≤ e) (he : e ≤ 1) :
 (1-p/2)*a+(p/2)*b ≤ 1-pl/2*(1-e) :=
begin
 have h₁ : 0 ≤ 1-p/2 := by linarith only [hp2],
 have h₂ : 0 ≤ p/2 := by linarith only [hp0],
 have h₃ : pl/2 ≤ p/2 := by linarith only [hp],
 calc (1-p/2)*a+(p/2)*b ≤ (1-p/2)*1+(p/2)*e :
         add_le_add (mul_le_mul_of_nonneg_left ha h₁) (mul_le_mul_of_nonneg_left hb h₂)
      ... = 1-p/2*(1-e) : by ring
      ... ≤ 1-pl/2*(1-e) : sub_le_sub_left (mul_le_mul_of_nonneg_right h₃ (sub_nonneg.mpr he)) _
end

end cat_observer_domain

