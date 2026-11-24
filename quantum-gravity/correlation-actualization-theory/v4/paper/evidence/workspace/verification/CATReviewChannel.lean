import data.complex.basic
import algebra.big_operators.basic
import tactic

noncomputable theory
open_locale big_operators
open finset
namespace cat_review_channel

-- k is the traced velocity square and b the traced double spatial contraction.
theorem lorentz_clock (k b a : ℝ) :
 a * ((2*k+b)/4) = a*(k/2+b/4) := by ring

theorem time_commutator_factor (v : ℂ) : -2*(-complex.I*v)^2=2*v^2 :=
calc -2*(-complex.I*v)^2 = (-2*(complex.I*complex.I))*v^2 : by ring
 ... = 2*v^2 : by rw [complex.I_mul_I]; ring

theorem euclidean_and_hamiltonian (k v : ℝ) (hk : 0 ≤ k) (hv : 0 ≤ v) :
 0 ≤ k+v ∧ -( -k-v) = k+v := ⟨add_nonneg hk hv,by ring⟩

theorem cayley_weights (g : ℝ) :
 ((1-g^2)/(1+g^2))^2+(2*g/(1+g^2))^2=1 :=
begin
 have h : 1+g^2≠0 := by nlinarith [sq_nonneg g],
 field_simp [h], ring
end

theorem absorber_shell (m w : ℝ) : (m+w)^2-w^2=m^2+2*m*w := by ring
theorem compensated_port (q c : ℤ) : (q+1)+(c-1)=q+c := by ring
theorem routing_recoil (p e f : ℝ) : p+(-p)=(-p)+p ∧ e+f=f+e :=
 ⟨add_comm _ _,add_comm _ _⟩

theorem middle_characteristic (y l : ℝ) :
 (-1-y-l)*(-1+y-l)-4=(l+1)^2-(y^2+4) := by ring

-- Includes any remote observable commuting with the two local Kraus factors.
theorem remote_fixed {R : Type*} [ring R] (a b c d o : R)
 (hc : o*c=c*o) (hd : o*d=d*o) (complete : a*c+b*d=1) :
 a*(o*c)+b*(o*d)=o :=
by rw [hc,hd,←mul_assoc,←mul_assoc,←add_mul,complete,one_mul]

def trial (p : ℝ) (v : bool) : ℝ := if v=tt then p else 1-p
def dark (v : bool) : ℝ := if v=ff then 1 else 0
def law (r p : ℝ) (an am bn bm : bool) : ℝ :=
 trial p an*trial p bn*(r*trial p am*dark bm+(1-r)*dark am*trial p bm)

theorem joint (r p : ℝ) : law r p tt tt tt ff=r*p^3 :=
by {simp [law,trial,dark], ring}
theorem b_closed (r p : ℝ) :
 law r p tt tt tt ff+law r p tt ff tt ff+
 law r p ff tt tt ff+law r p ff ff tt ff=r*p+(1-r)*p*(1-p) :=
by {simp [law,trial,dark], ring}
theorem b_wrong_sign (r p : ℝ) :
 law r p tt tt ff tt+law r p tt ff ff tt+
 law r p ff tt ff tt+law r p ff ff ff tt=(1-r)*p*(1-p) :=
by {simp [law,trial,dark], ring}

theorem closure_deficit (r p : ℝ) :
 1-(r*p+(1-r)*p*(1-p))=(1-p)+(1-r)*p^2 := by ring

theorem certain_two_pulse_closure (r p : ℝ) (hr : r ≤ 1) (hp : p ≤ 1) :
 r*p+(1-r)*p*(1-p)=1 ↔ p=1 ∧ r=1 :=
begin
 split,
 { intro h,
   have z : (1-p)+(1-r)*p^2=0 := by rw [←closure_deficit,h,sub_self],
   have hmul : 0 ≤ (1-r)*p^2 := mul_nonneg (sub_nonneg.mpr hr) (sq_nonneg p),
   have h1 : p=1 := by linarith,
   refine ⟨h1,_⟩,
   simpa [h1] using h },
 { rintro ⟨rfl,rfl⟩, norm_num }
end

theorem normalized (r p : ℝ) :
 ∑ an : bool, ∑ am : bool, ∑ bn : bool, ∑ bm : bool, law r p an am bn bm=1 :=
by {simp [fintype.sum_bool,law,trial,dark],ring}

-- Matrix entries of the weighted injection into orthogonal carrier and logical labels.
theorem carrier_gram {ι : Type*} [fintype ι] [decidable_eq ι]
 (x y : (fin 3) × ι) (w v : ℂ) :
 (∑ t : (fin 3) × ι, (if t=x then w else 0)*(if t=y then v else 0))
 = if x=y then w*v else 0 :=
begin
 classical,
 rw [finset.sum_eq_single x],
 {by_cases h : x=y; simp [h]},
 {intros b hb hbx, simp [hbx]},
 {intro h, exact (h (finset.mem_univ x)).elim}
end

theorem emitted_weights (a b : ℝ) : a+(1-a)*b+(1-a)*(1-b)=1 := by ring
theorem erasure_cross_not_scalar (c : ℂ) :
 (λ i j : bool, if i=ff ∧ j=tt then (1:ℂ) else 0) ≠
 (λ i j : bool, if i=j then c else 0) :=
begin
 intro h,
 have h' := congr_fun (congr_fun h ff) tt,
 simpa using h'
end
theorem erased_bell_overlap (u v : ℝ) (normal : u+v=1) :
 (u+v)/4=(1:ℝ)/4 := by rw [normal]
theorem flagged_fidelity (s : ℝ) : s+(1-s)/4=(1+3*s)/4 := by ring

theorem logical_return (p : ℝ) : (1-p)+(p/2)/2+(p/2)/2=1-p/2 := by ring
theorem all_registers_return (p : ℝ) :
 (1-p)^2+(p/2)^2+(p/2)^2=(1-p)^2+p^2/2 := by ring

theorem calibration_lower (p c d : ℝ) (hd : d<1)
 (bound : c≤p+(1-p)*d) : (c-d)/(1-d)≤p :=
begin
 apply (div_le_iff (sub_pos.mpr hd)).2,
 nlinarith
end
end cat_review_channel

