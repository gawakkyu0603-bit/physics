import tactic
import measure_theory.integral.fund_thm_calculus

noncomputable theory
open_locale interval big_operators
open measure_theory set

namespace cat_einstein_sectors

-- R_0z0z=A, R_0y0y=T, R_zyzy=C, R_yxyx=D in a (-+++) frame.
theorem einstein_contraction (a t c d : ℝ) :
 let r0:=a+2*t, rz:=-a+2*c, ry:=-t+c+d,
     scal:=-r0+rz+2*ry in
 r0+scal/2=d+2*c ∧ rz-scal/2=2*t-d ∧ ry-scal/2=a+t-c :=
by { dsimp, split, ring, split; ring }

theorem radial_null_projection (B R b r rr : ℝ) (hB : B≠0) (hR : R≠0) :
 R/B*((1+r^2)/R^2+2*(b/B)*(r/R)+(-2*rr/R-(1+r^2)/R^2))
 = -2*((rr*B-r*b)/B^2) :=
by {field_simp [hB,hR],ring}

theorem negative_at_turn (R rr : ℝ) (hR : 0<R) (hr : 0<rr) : -2*rr/R<0 :=
by { apply div_neg_of_neg_of_pos _ hR, linarith }

theorem lambda_cannot_restore_NEC (g0 gz lam k rho p : ℝ) (hk : 0≤k)
 (e0 : g0-lam=k*rho) (ez : gz+lam=k*p) (nec : 0≤rho+p) :
 0≤g0+gz :=
by { have h := mul_nonneg hk nec, nlinarith only [h,e0,ez] }

theorem fixed_null_integral (Rvel C : ℝ→ℝ) (a b : ℝ)
 (hd : ∀ x ∈ uIcc a b, has_deriv_at (λ t, -2*Rvel t) (C x) x)
 (hi : interval_integrable C volume a b) (ha : Rvel a = -1) (hb : Rvel b=0) :
 (∫ t in a..b, C t)=-2 :=
by {rw [interval_integral.integral_eq_sub_of_has_deriv_at hd hi],dsimp,rw [ha,hb],norm_num}

theorem mass_derivative (R r rr : ℝ) :
 r*(1+r^2)+R*(2*r*rr)=r*(1+r^2+2*R*rr) := by ring

theorem pure_lambda_product_impossible (u L : ℝ) (hu : 0<u) :
 ¬(u-L=0 ∧ (0:ℝ)+L=0) := by { rintro ⟨h₀,h₁⟩,linarith }

theorem electromagnetic_product (u : ℝ) :
 u-u/2=u/2 ∧ -u+u/2= -u/2 ∧ 0+u/2=u/2 := by {split,ring,split;ring}

theorem pp_is_vacuum (a b s v : ℝ) (hs : s≠0) (mat : a^2+b^2=s*v^2) :
 2*((a^2+b^2)/s^2-v^2/s)=0 := by {rw [mat],field_simp [hs],ring}

theorem conserved_label {K : Type*} [field K] (ei ef amplitude : K)
 (different : ef≠ei) (transport : ef*amplitude=ei*amplitude) : amplitude=0 :=
begin
 have h : (ef-ei)*amplitude=0 := by rw [sub_mul,transport,sub_self],
 exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr different)
end

theorem block_diagonal_record {M : Type*} [ring M] (old future k : M)
 (orthogonal : future*old=0) (no_mix : future*k=k*future) : future*k*old=0 :=
by rw [no_mix,mul_assoc,orthogonal,mul_zero]

theorem uncertain_observer (w c : ℝ) (hc : c≠0) :
 w*c/(w*c+(1-w)*c)=w :=
by { have h : w*c+(1-w)*c=c := by ring, rw [h],field_simp [hc] }

theorem definite_local_reading (w a : ℝ) (hw : w≠0) (ha : a≠0) :
 w*a/(w*a+(1-w)*0)=1 := by simp [mul_ne_zero hw ha]

theorem tilted_leaf_symbol (l u v y z : ℝ) :
 -((l*v)^2)+v^2+(-u)^2+z^2+(-y)^2 = u^2+(1-l^2)*v^2+y^2+z^2 := by ring

theorem positive_target_symbol (a b c d q : ℝ) (hq : 0≤q) :
 0≤q*(a^2+b^2+c^2+d^2) := by positivity

theorem critical_tilt (l : ℝ) (hl : 0≤l) : 1-l^2=0 ↔ l=1 :=
by {split, intro h, nlinarith, rintro rfl, norm_num}

theorem vector_only_count (D : ℤ) (count : D-2=8) : D=10 := by linarith

-- The explicit homotopy retracting the homogeneous product's two contractible axes.
def retract {S : Type*} (s : ℝ) (x : (ℝ×ℝ)×S) : (ℝ×ℝ)×S :=
 ((s*x.1.1,s*x.1.2),x.2)

theorem continuous_retract {S : Type*} [topological_space S] :
 continuous (λ p : ℝ×((ℝ×ℝ)×S), retract p.1 p.2) :=
 ((continuous_fst.mul continuous_snd.fst.fst).prod_mk
  (continuous_fst.mul continuous_snd.fst.snd)).prod_mk continuous_snd.snd

theorem ends_of_retract {S : Type*} (x : (ℝ×ℝ)×S) :
 retract 1 x=x ∧ retract 0 x=((0,0),x.2) :=
by {rcases x with ⟨⟨a,b⟩,y⟩, simp [retract]}

theorem keeps_sphere {S : Type*} (s : ℝ) (y : S) :
 retract s ((0,0),y)=((0,0),y) := by simp [retract]

theorem all_translations_force_full_domain {V : Type*} [add_comm_group V]
 (U : set V) (occupied : U.nonempty) (complete : ∀ p∈U, ∀ v : V, p+v∈U) :
 U=set.univ :=
begin
 obtain ⟨p,hp⟩ := occupied,
 apply set.eq_univ_of_forall, intro q,
 have h := complete p hp (q-p), simpa [sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using h
end

theorem central_bracket_solves_parent {M : Type*} [ring M] (a b c d : M)
 (inner : a*b-b*a=c) (central : d*c=c*d) :
 d*(a*b-b*a)-(a*b-b*a)*d=0 := by rw [inner,central,sub_self]

end cat_einstein_sectors
