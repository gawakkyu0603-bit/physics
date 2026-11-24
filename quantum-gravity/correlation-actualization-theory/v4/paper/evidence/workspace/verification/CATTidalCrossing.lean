import tactic
import analysis.inner_product_space.basic

noncomputable theory
namespace cat_tidal_crossing

-- Primitivity is linear in the real Kähler two-form when both fluxes are fixed.
theorem common_scale {V W : Type*} [add_comm_group V] [module ℝ V]
 [add_comm_group W] [module ℝ W] (L : V →ₗ[ℝ] W) (k : V)
 (hk : L k=0) (a : ℝ) : L (a • k)=0 := by rw [map_smul,hk,smul_zero]

-- A charge-neutral contact cannot take the state into an orthogonal flux sector.
theorem flux_preserved {V : Type*} [add_comm_group V] [module ℂ V]
 (K P Q : V →ₗ[ℂ] V) (v : V) (in_P : P v=v)
 (neutral : ∀ w, P (K w)=K (P w)) (apart : ∀ w, Q (P w)=0) : Q (K v)=0 :=
begin
 have kept : P (K v)=K v := by rw [neutral,in_P],
 exact (congr_arg Q kept).symm.trans (apart (K v))
end

theorem two_shape_gram (p q r : ℝ) (hp : 0<p) (det : 0<p*r-q^2)
 (u v : ℝ) (a : p*u+q*v=0) (b : q*u+r*v=0) : u=0 ∧ v=0 :=
begin
 have h : (p*r-q^2)*v=0 := by linear_combination p*b-q*a,
 have hv := (mul_eq_zero.mp h).resolve_left det.ne',
 rw [hv,mul_zero,add_zero] at a,
 exact ⟨(mul_eq_zero.mp a).resolve_left hp.ne', hv⟩
end

-- DBI plus the calibrated C4 potential on a static BPS D3.
theorem static_probe (h : ℝ) : (1 / h)*((1:ℝ)-real.sqrt 1)=0 := by simp

theorem probe_rationalized (h v z : ℝ) (hh : h≠0) (hz : z^2=1-h*v^2)
 (s : 1+z≠0) : (1-z)/h=v^2/(1+z) :=
begin
 apply (div_eq_div_iff hh s).2, nlinarith only [hz]
end

-- The point-probe operator on a commuting colour eigenvalue is a traceless
-- two-by-two Pauli matrix whose two eigenvalues have opposite signs.
theorem commuting_characteristic (l x y z : ℝ) :
 (z-l)*(-z-l)-(x^2+y^2)=l^2-(x^2+y^2+z^2) := by ring

-- y=(s/s0)^(1/3); differentiation in x=s/s0 is (3*y^2)^(-1) d/dy.
theorem radial_jacobi (y : ℝ) (hy : y≠0) :
 ((4+16/y^5)/15)/(3*y^2)=4*((y^4+4/y)/5)/(9*(y^3)^2) :=
by field_simp [hy]; ring

theorem transverse_jacobi (y : ℝ) (hy : y≠0) :
 ((-4/y^3+2/y^2)/3)/(3*y^2)= -2*(2*y-y^2)/(9*(y^3)^2) :=
by field_simp [hy]; ring

theorem radius_initial : (((1:ℝ)^4+4/1)/5)=1 ∧ 2*(1:ℝ)-1^2=1 := by norm_num

theorem centre_threshold_polynomial (y n : ℝ) (hy : y≠0) :
 5*y*((y^4+4/y)/5-n*(2*y-y^2))=y^5+5*n*y^3-10*n*y^2+4 :=
by field_simp [hy]; ring

theorem axial_characteristic (a k d u l : ℝ) :
 (a*(k-1/2)-d-l)*(-a*(k+1/2)+d-l)-u^2=
 (l+a/2)^2-((a*k-d)^2+u^2) := by ring

-- For a>0 the upper eigenvalue is negative exactly when the squared
-- off-centre displacement and transverse coupling fit in this interval.
theorem active_interval (a b n k eta : ℝ) (ha : 0<a) :
 a^2*(k-eta)^2+b^2*((n/2)^2-k^2)<(a/2)^2 ↔
 4*(k-eta)^2+(b/a)^2*(n^2-4*k^2)<1 :=
begin
 have hi : (0:ℝ)<a^2 := sq_pos_of_pos ha,
 have hx : (4*(k-eta)^2+(b/a)^2*(n^2-4*k^2))*a^2 =
    4*(a^2*(k-eta)^2+b^2*((n/2)^2-k^2)) := by field_simp [ha.ne'];ring,
 have h4 : (0:ℝ)<4 := by norm_num,
 have hs : 4*(a/2)^2=a^2 := by ring,
 split,
 {intro h, apply (mul_lt_mul_right hi).1, rw [hx,one_mul],
  exact lt_of_lt_of_eq ((mul_lt_mul_left h4).2 h) hs},
 {intro h, have hh:= (mul_lt_mul_right hi).2 h,
  rw [hx,one_mul] at hh, exact (mul_lt_mul_left h4).1 (lt_of_lt_of_eq hh hs.symm)}
end

theorem half_integer_obstruction (a u : ℝ) (hu : 0<u^2) (k : ℝ)
 (hk : (1/2:ℝ)^2 ≤ k^2) : (a/2)^2 < (a*k)^2+u^2 :=
begin
 have h:=mul_le_mul_of_nonneg_left hk (sq_nonneg a),
 calc (a/2)^2 = a^2*(1/2)^2 : by ring
 ... ≤ a^2*k^2 : h
 ... = (a*k)^2 : by ring
 ... < (a*k)^2+u^2 : lt_add_of_pos_right _ hu
end

theorem extremal_width (n k : ℝ) (n2 : 0≤n-2) (l : -(n-2)/2≤k)
 (u : k≤(n-2)/2) : 4*(n-1) ≤ n^2-4*k^2 :=
begin
 have t := mul_nonneg (sub_nonneg.mpr u) (sub_nonneg.mpr l),
 nlinarith only [t]
end

theorem central_eigenline (a b n : ℝ) : -a/2+b*n/2=(n*b-a)/2 := by ring

theorem particle_hole_cost (a b n : ℝ) :
 4*((a-n*b)/2)+4*((a-n*b)/2)=4*(a-n*b) := by ring

-- A commuting in-plane vertex has zero matrix element between opposite
-- chirality eigenvectors. The fourth ordinary Clifford direction exchanges them.
theorem opposite_chiral_matrix_element (z : ℂ) (h : z= -z) : z=0 :=
by linear_combination (1/2:ℂ)*h

theorem transverse_partner {V : Type*} [add_comm_group V] [module ℂ V]
 (D G : V →ₗ[ℂ] V) (v : V) (l : ℂ) (e : D v=l • v)
 (anticomm : D (G v)= -G (D v)) : D (G v)=(-l) • G v :=
by rw [anticomm,e,map_smul,neg_smul]

-- Heron's product for singular values of a real three-colour preparation.
theorem triangle_discriminant (a b c : ℝ) :
 2*(a^4+b^4+c^4)-(a^2+b^2+c^2)^2=
 (a+b+c)*(a-b-c)*(a+b-c)*(a-b+c) := by ring

theorem shape_quadratic (u v w z h r t : ℝ) :
 2*(u^2+v^2+(t*r)^2+2*w^2+2*t*z^2+2*t*h^2)-(u+v+t*r)^2=
 r^2*t^2+(4*(z^2+h^2)-2*r*(u+v))*t+(u-v)^2+4*w^2 := by ring

open_locale big_operators

-- Components of (|p><q|-|q><p|) R (|q><p|-|p><q|).
-- Summing the ordered pairs counts each physical antisymmetric direction twice.
def wedge_density (p q i j : fin 4) (R : fin 4 → fin 4 → ℂ) : ℂ :=
 (if p=i then (if p=j then R q q else 0) else 0)
 -(if p=i then (if q=j then R q p else 0) else 0)
 -(if q=i then (if p=j then R p q else 0) else 0)
 +(if q=i then (if q=j then R p p else 0) else 0)

theorem core_channel (i j : fin 4) (R : fin 4 → fin 4 → ℂ) :
 (∑ p : fin 4, ∑ q : fin 4, wedge_density p q i j R)/6 =
 ((if i=j then ∑ q : fin 4, R q q else 0)-R j i)/3 :=
begin
 classical,
 simp only [wedge_density,finset.sum_add_distrib,finset.sum_sub_distrib,
            finset.sum_ite_irrel,finset.sum_const_zero],
 simp,
 split_ifs; ring
end

-- Four flavor directions, one of which is excluded by antisymmetry.
theorem normalized_emission (a b c d : ℝ) :
 ((b+c+d)+(a+c+d)+(a+b+d)+(a+b+c))/3=a+b+c+d := by ring

theorem complementary_binary_distances :
 ((1/3:ℝ)+1/3)/2=1/3 ∧ (4*(1/3:ℝ))/2=2/3 ∧
 (1+(2/3:ℝ))/2=5/6 := by norm_num

theorem four_empty (p : ℝ) :
 (1-p)*(1-p)*(1-p)*(1-p)=(1-p)^4 := by ring

end cat_tidal_crossing
