import tactic
import analysis.calculus.deriv.pow
import analysis.calculus.deriv.inv
import analysis.special_functions.trigonometric.deriv
import topology.instances.real
import measure_theory.integral.fund_thm_calculus

noncomputable theory
open set finset
open_locale big_operators interval
open measure_theory

namespace cat_oriented_bounce

-- Signed north-edge numerator j a² - d x, before division by positive a.
theorem edge_derivative (j t : ℝ) (a d x : ℝ → ℝ) (ar dr xr : ℝ)
 (ha : has_deriv_at a ar t) (hd : has_deriv_at d dr t) (hx : has_deriv_at x xr t) :
 has_deriv_at (λ s, j*(a s)^2-d s*x s) (j*(2*a t*ar)-(dr*x t+d t*xr)) t :=
begin
 convert ((ha.pow 2).const_mul j).sub (hd.mul hx) using 1, simp
end

theorem edge_acceleration (j t : ℝ) (a d x ar dr xr : ℝ → ℝ) (aa dd xx : ℝ)
 (ha : has_deriv_at a (ar t) t) (hd : has_deriv_at d (dr t) t)
 (hx : has_deriv_at x (xr t) t) (h1 : has_deriv_at ar aa t)
 (h2 : has_deriv_at dr dd t) (h3 : has_deriv_at xr xx t) :
 has_deriv_at (λ s, j*(2*a s*ar s)-(dr s*x s+d s*xr s))
 (2*j*((ar t)^2+a t*aa)-(dd*x t+2*dr t*xr t+d t*xx)) t :=
begin
 convert ((((ha.const_mul 2).mul h1).const_mul j).sub ((h2.mul hx).add (hd.mul h3))) using 1, ring
end

theorem polar_jet (j v : ℝ) :
 j*(2*1*0)-(v*1+j*0) = -v ∧
 2*j*((0:ℝ)^2+1*(-7/4))-(0*1+2*v*0+j*(-2))= -3*j/2 :=
by {split; ring}

theorem grazing (t j remainder : ℝ) (hj : 0<j) (ht : t≠0)
 (hr : |remainder| ≤ j/4) : t^2*(-3*j/4+remainder)<0 :=
begin
 apply mul_neg_of_pos_of_neg (sq_pos_of_ne_zero _ ht),
 have h := (abs_le.mp hr).2, linarith
end

theorem transverse_sign (t v r : ℝ) (hv : 0<v) (hr : |r|≤v/2) (ht : t≠0) :
 (t*(-v+r))*t<0 :=
begin
 have q : -v+r<0 := by linarith [(abs_le.mp hr).2],
 calc (t*(-v+r))*t = t^2*(-v+r) : by ring
 ... < 0 : mul_neg_of_pos_of_neg (sq_pos_of_ne_zero _ ht) q
end

theorem paired_contacts (g : ℝ → ℝ) (T d : ℝ) (ht : 0<T)
 (hg : continuous g) (he : g (-T)=g T) (h0 : d<g 0) (hT : g T<d) :
 (∃ s ∈ Ioo (-T) 0, g s=d) ∧ (∃ s ∈ Ioo 0 T, g s=d) :=
begin
 obtain ⟨u,hu,eu⟩ := intermediate_value_Icc (show -T≤0, by linarith) hg.continuous_on
   (show d∈Icc (g (-T)) (g 0), from ⟨by linarith, h0.le⟩),
 obtain ⟨v,hv,ev⟩ := intermediate_value_Icc' ht.le hg.continuous_on
   (show d∈Icc (g T) (g 0), from ⟨hT.le,h0.le⟩),
 refine ⟨⟨u,⟨lt_of_le_of_ne hu.1 _,lt_of_le_of_ne hu.2 _⟩,eu⟩,
         ⟨v,⟨lt_of_le_of_ne hv.1 _,lt_of_le_of_ne hv.2 _⟩,ev⟩⟩;
 intro bad; subst_vars; linarith
end

theorem transverse_gap (energy ell perpendicular : ℝ)
 (h : energy^2=ell^2+perpendicular^2) (contact : ell=0) :
 |energy|=|perpendicular| :=
by { rw [←sq_eq_sq_iff_abs_eq_abs], rw [h,contact], ring }

theorem outer_radius (s : ℝ) (h : 0 ≤ (5/4:ℝ)*s-s^3-1/4) : s≤1 :=
begin
 by_contra small, push_neg at small,
 have p : 0 < (s-1)*(s^2+s-1/4) :=
  mul_pos (by linarith) (by nlinarith [sq_nonneg s]),
 nlinarith only [p,h]
end

theorem threshold_derivative_bound (t minus_xp factor other : ℝ)
 (ht : 0≤t) (hx : 2*(3/4:ℝ)^3*t≤minus_xp)
 (hf : (8/9:ℝ)≤factor) (hy : other≤2*t/3) :
 -minus_xp*factor+other ≤ -t/12 :=
begin
 have hx0 : 0≤2*(3/4:ℝ)^3*t := by positivity,
 have bound := mul_le_mul hx hf (by norm_num : 0≤(8/9:ℝ)) (le_trans hx0 hx),
 calc -minus_xp*factor+other = -(minus_xp*factor)+other : by ring
 ... ≤ -(2*(3/4:ℝ)^3*t*(8/9))+2*t/3 : add_le_add (neg_le_neg bound) hy
 ... = -t/12 : by ring
end

-- Riemann entries X=R0101, Y=R0202, Z=R1212, W=R2323.
theorem electric_weyl (X Y Z W : ℝ) :
 X+(-X+2*Z)/2-(X+2*Y)/2-(-2*X-4*Y+4*Z+2*W)/6=(X-Y+Z-W)/3 := by ring

theorem bounce_invariants (h : ℝ) (hn : h≠0) :
 let rr := (2-h^2)/h^3, bb := (h^2-2)/h-rr in
 bb+2*rr=(2-h^2)*(1-h^2)/h^3 ∧
 -bb+rr-1/h=(4-h^2-h^4)/h^3 :=
by {dsimp, split; field_simp [hn]; ring}

theorem simultaneous_range (h : ℝ) (hp : 0<h) (b : 0<2-h^2)
 (v : 0 < (2-h^2)*(1-h^2)/h^3) : h^2<1 :=
begin
 have hh : 0<h^3 := pow_pos hp _,
 have p := (div_pos_iff.mp v).resolve_right (by rintro ⟨_,q⟩; linarith),
 rcases (mul_pos_iff.mp p.1) with ⟨_,q⟩ | ⟨q,_⟩; linarith
end

theorem nonzero_weyl (h : ℝ) (hp : 0<h) (h1 : h^2<1) :
 0 < (4-h^2-h^4)/(3*h^3) :=
begin
 have hh : h^4<1 := by nlinarith [mul_pos (sub_pos.mpr h1) (show 0<1+h^2, by positivity)],
 exact div_pos (by linarith) (by positivity)
end

theorem example_invariants :
 let h : ℝ := 1/2 in (2-h^2)*(1-h^2)/h^3=21/2 ∧
 4*((4-h^2-h^4)/h^3)^2/3=3481/3 := by norm_num

theorem tidal_work (mu m e x y vx vy d vd : ℝ) :
 mu*(vx*(-2*(x^2+y^2)*x-e*x)+vy*(-2*(x^2+y^2)*y+e*y)
     +2*(x^2+y^2)*(x*vx+y*vy))+m*vd*(-e*d) =
  -e*(mu*(x*vx-y*vy)+m*d*vd) := by ring

theorem equal_common_acceleration (e x y : ℝ) : -e*x-(-e*y) = -e*(x-y) := by ring

theorem perpendicular_compression {A : Type*} [ring A] (p d z : A)
 (left : p*z=p) (right : z*p=p) (anti : z*d= -(d*z)) :
 p*d*p = -(p*d*p) :=
begin
 calc p*d*p = (p*z)*d*p : by rw [left]
 ... = p*(z*d)*p : by rw [mul_assoc p z d]
 ... = -(p*d*(z*p)) : by {rw [anti], noncomm_ring}
 ... = -(p*d*p) : by rw [right]
end

theorem conserving_vertex {A : Type*} [ring A] (n create annihilate : A)
 (hc : n*create=create*n+create) (ha : n*annihilate=annihilate*n-annihilate) :
 n*(create*annihilate)=(create*annihilate)*n :=
begin
 rw [←mul_assoc,hc,add_mul,mul_assoc create n annihilate,ha], noncomm_ring
end

theorem closed_side (f df : ℝ → ℝ) (a b : ℝ) (per : f b=f a)
 (hd : ∀ x ∈ uIcc a b, has_deriv_at f (df x) x)
 (hi : interval_integrable df volume a b) : (∫ x in a..b, df x)=0 :=
by rw [interval_integral.integral_eq_sub_of_has_deriv_at hd hi,per,sub_self]

theorem slab_flux (flux : ℝ → ℝ) (a b : ℝ)
 (bianchi : ∀ t ∈ uIcc a b, has_deriv_at flux 0 t) : flux b=flux a :=
begin
 have e := interval_integral.integral_eq_sub_of_has_deriv_at bianchi
   (show interval_integrable (λ t : ℝ, (0:ℝ)) volume a b, from continuous_const.interval_integrable _ _),
 simp at e, linarith
end

theorem bridge_shell (j M w a : ℝ)
 (balance : 2*(j+1)*a*M=w+M)
 (nonzero : j≠0) (nj : j+1≠0) :
 (w-a*M)^2-((1-a)^2*M^2+j^2*((w^2-M^2)/(j*(j+1))))=0 :=
begin
 field_simp [nonzero,nj], linear_combination -j*(w-M)*balance
end

theorem counted_total (l r n : ℤ) : (l+n)+(r-n)=l+r := by ring
theorem independent_flux (phi0 phi1 q : ℤ) (same : phi0=phi1)
 (charged : q≠0) : q≠phi1-phi0 := by {rw [same,sub_self],exact charged}
theorem dressed_flux (n r k : ℤ) : (n+k)-(r+k)=n-r := by ring
theorem lock_gap (k g : ℝ) (hk : k≠0) (hg : 0<g) : 0 < |k|*g :=
mul_pos (abs_pos.mpr hk) hg

-- Real coefficients of the spatial difference equation's even time derivatives.
def impulse (c : ℝ) : ℕ → ℤ → ℝ
| 0 z := if z=0 then 1 else 0
| (r+1) z := c*(impulse r (z-1)-2*impulse r z+impulse r (z+1))

theorem impulse_support (c : ℝ) (r : ℕ) :
 ∀ z : ℤ, (r:ℤ)<z → impulse c r z=0 :=
begin
 induction r with r ih,
 { intros z hz, have nz : z≠0 := by {intro h, subst z, norm_num at hz}, simp [impulse,nz] },
 { intros z hz, rw [nat.cast_succ] at hz, simp only [impulse],
   rw [ih (z-1) (by linarith), ih z (by linarith), ih (z+1) (by linarith)], ring }
end

theorem impulse_frontier (c : ℝ) (r : ℕ) : impulse c r r=c^r :=
begin
 induction r with r ih,
 { simp [impulse] },
 { rw [nat.cast_succ], simp only [impulse],
   rw [show (r:ℤ)+1-1=r, by ring, ih, impulse_support c r ((r:ℤ)+1) (by linarith),
       impulse_support c r ((r:ℤ)+1+1) (by linarith),pow_succ], ring }
end

theorem ordinary_cone_error (signal noise : ℝ) (hn : 0<noise) (eps : ℝ)
 (bound : |signal|≤eps*noise) : |signal|/noise≤eps := (div_le_iff hn).mpr bound

theorem contour_exponent (n x s : ℝ) (hs : 0<s) (h : x*real.sinh s<n*s) :
 real.exp (-2*n*s+2*x*real.sinh s)<1 :=
by { apply real.exp_lt_one_iff.mpr, linarith }

theorem two_path_probability (s c overlap : ℝ) :
 (s*c)^2+(s*c)^2+2*overlap*(s*c)*(s*c)=2*s^2*c^2*(1+overlap) := by ring

theorem intermediate_resolving_changes (s c : ℝ) (hs : s≠0) (hc : c≠0) :
 2*s^2*c^2<4*s^2*c^2 :=
by { nlinarith only [mul_pos (sq_pos_of_ne_zero _ hs) (sq_pos_of_ne_zero _ hc)] }

theorem population_step (p hop : ℝ) :
 1-2*((1-p)*hop+p*(1-hop))=(1-2*p)*(1-2*hop) := by ring

theorem vacuum_one_derivative (p0 e p1 : ℝ) :
 has_deriv_at (λ s : ℝ, (p0+2*e*s+p1*s^2)/(1+s^2)) (2*e) 0 :=
begin
 have hs := has_deriv_at_id (0:ℝ),
 have hn := ((has_deriv_at_const (0:ℝ) p0).add (hs.const_mul (2*e))).add
     ((hs.pow 2).const_mul p1),
 have hd := (has_deriv_at_const (0:ℝ) (1:ℝ)).add (hs.pow 2),
 convert hn.div hd (by norm_num : (1:ℝ)+(0:ℝ)^2≠0) using 1; norm_num
end

theorem vacuum_one_bound (p0 p1 e rate : ℝ) (positive : e^2≤p0*p1)
 (coherent : rate=2*e) : rate^2≤4*p0*p1 := by {rw [coherent], nlinarith only [positive]}

theorem population_repeated (p : ℕ → ℝ) (d : ℝ) (h0 : p 0=0)
 (hstep : ∀ n, 1-2*p(n+1)=(1-2*p n)*d) (k : ℕ) : 1-2*p k=d^k :=
begin
 induction k with k ih, {simp [h0]}, {rw [hstep,ih,pow_succ],ring}
end

theorem final_mark_preserves_weight (p norm : ℝ) (hn : norm=1) : p*norm=p := by simp [hn]

theorem marginal_without_arrival {ι : Type*} [fintype ι] (prob : ι → ℝ) (b : ℝ)
 (h : ∑ i, prob i=1) : ∑ i, prob i*b=b := by rw [←finset.sum_mul,h,one_mul]

theorem midpoint_accuracy (a b c e : ℝ) (h1 : |a-c|≤e) (h2 : |b-c|≤e) : |a-b|≤2*e :=
begin
 have t := abs_add (a-c) (c-b), rw [show a-c+(c-b)=a-b, by ring, abs_sub_comm c b] at t,
 linarith
end

end cat_oriented_bounce
