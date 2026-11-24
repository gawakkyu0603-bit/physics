import analysis.special_functions.japanese_bracket
import analysis.special_functions.trigonometric.arctan_deriv
import analysis.special_functions.log.deriv
import analysis.inner_product_space.basic
import analysis.calculus.deriv.pow
import analysis.calculus.deriv.inv
import analysis.special_functions.trigonometric.deriv
import measure_theory.integral.fund_thm_calculus
import tactic

noncomputable theory
open measure_theory
open_locale complex_conjugate
namespace causal_gravity_receiver

-- Receiver amplitudes on the converted block, including coherences with an arbitrary spectator.
theorem born_pullback {R : Type*} [ring R] (vh v p q : R) (complete : p+q=1) :
 vh*p*v+vh*q*v=vh*v :=
by rw [←add_mul,←mul_add,complete,mul_one]

theorem conjugate_generator {R : Type*} [ring R] (u ud du dud h dh : R)
 (unit : ud*u=1) (comm : h*u=u*h) (comm' : ud*h=h*ud)
 (stationary : dh*u+h*du=du*h+u*dh) :
 ud*dh*u-dh=(ud*du)*h-h*(ud*du) :=
begin
 have a : ud*(dh*u+h*du) = ud*(du*h+u*dh) := congr_arg _ stationary,
 rw [mul_add,mul_add,←mul_assoc ud u dh,unit,one_mul,←mul_assoc ud h du,comm',
     mul_assoc h ud du,←mul_assoc ud du h,←mul_assoc ud dh u] at a,
 calc ud*dh*u-dh=(ud*dh*u+h*(ud*du))-(h*(ud*du)+dh) : by abel
 ... = (ud*du)*h-h*(ud*du) : by rw [a]; abel
end

theorem offdiagonal_response (u v : ℝ) (dh c : ℂ) (neq : u≠v) :
 dh+((1-c)/((u:ℂ)-v)*dh)*((v:ℂ)-u)=c*dh :=
begin
 have n : (u:ℂ)-(v:ℂ)≠0 := sub_ne_zero.mpr (by exact_mod_cast neq),
 field_simp [n]; ring
end

theorem covariant_curvature_of_two_delays {R : Type*} [ring R] (x y a b : R) :
 (x+a)*(y+b)-(y+b)*(x+a)-2*(x*y-y*x+a*b-b*a)
 = -((x-a)*(y-b)-(y-b)*(x-a)) := by noncomm_ring

-- The four Laplace equations are integrations of the two populations and the complex coherence.
theorem laplace_clock (s k g d x y a b : ℂ) (p₁ : s*x-1= -2*g*b)
 (p₂ : (s+k)*y=2*g*b) (realpart : (s+k/2)*a= -d*b)
 (imagpart : (s+k/2)*b=g*(x-y)+d*a) :
 (s*(s+k)*((s+k/2)^2+d^2)+4*g^2*(s+k/2)^2)*y=2*g^2*(s+k/2) :=
begin
 have coh : ((s+k/2)^2+d^2)*b=(s+k/2)*g*(x-y) :=
   by linear_combination (s+k/2)*imagpart + d*realpart,
 linear_combination (2*g*s)*coh + ((s+k/2)^2+d^2)*s*p₂ +
   (2*g^2*(s+k/2))*p₁ + (2*g^2*(s+k/2))*p₂
end

theorem normalized_at_zero (k g d : ℝ) (hk : k≠0) (hg : g≠0) :
 (2*k*g^2*(k/2))/(4*g^2*(k/2)^2)=1 :=
by field_simp [hk,hg];ring

theorem on_resonance_factor (k u n : ℝ) :
 (2*k*u-3*k*n^2/2)^2+(n^3-(4*u+k^2/2)*n)^2=
 (k^2+4*n^2)*(4*u^2-2*n^2*u+n^2*(k^2+n^2)/4) := by ring

theorem clock_strength_minimum (u r : ℝ) (hu : 0<u) :
 u+r^2/u-2*r=(u-r)^2/u :=
by field_simp [ne_of_gt hu];ring

theorem clock_threshold (k n t : ℝ) (hk : 0<k) (hn : 0<n) (ht : 0<t)
 (sq : t^2=k^2+n^2) :
 (1+4*n^2/k^2)*(n*t/2-n^2/2)=n*(k^2+4*n^2)/(2*(t+n)) :=
begin
 have s : t+n≠0 := ne_of_gt (by linarith),
 have diff : t-n=k^2/(t+n) := (eq_div_iff s).2 (by nlinarith),
 rw [show n*t/2-n^2/2=n/2*(t-n), by ring,diff],
 field_simp [s,ne_of_gt hk]; ring
end

theorem weak_cannot_clock (k n t : ℝ) (hk : 0<k) (hn : 0<n) (ht : 0<t)
 (sq : t^2=k^2+n^2) : n^2<n*(k^2+4*n^2)/(2*(t+n)) :=
begin
 have tn : n<t := by nlinarith [sq_pos_of_ne_zero k (ne_of_gt hk)],
 apply (lt_div_iff (by linarith : 0<2*(t+n))).2,
 calc n^2*(2*(t+n))<n^2*(2*(t+n))+n*(t-n)^2 :
   lt_add_of_pos_right _ (mul_pos hn (sq_pos_of_ne_zero _ (ne_of_gt (sub_pos.mpr tn))))
 ... = n*(k^2+4*n^2) : by linear_combination n*sq
end

theorem support_norm (L x y t v : ℝ) (hL : 0<L) (hv : 0≤v)
 (h : L^2=x^2+y^2) (root : v^2=(x+t)^2+y^2) :
 L^2+t*x≤L*v :=
begin
 have sq : (L*v)^2-(L^2+t*x)^2=(t*y)^2 :=
 by linear_combination L^2*root + (t^2-L^2)*h,
 have pos := mul_nonneg hL.le hv, by_contra no,
 have gt : L*v<L^2+t*x := lt_of_not_ge no,
 have squares : (L*v)^2<(L^2+t*x)^2 := pow_lt_pow_of_lt_left gt pos (by norm_num),
 linarith only [sq,squares,sq_nonneg (t*y)]
end

theorem detuning_slope (r t : ℝ) (ht : 4*t=r^2-1) :
 r*(t-1)+3*t+1=(r-1)*(r^2+4*r-1)/4 :=
by linear_combination (r+3)/4*ht

theorem positive_detuning_slope (r : ℝ) (hr : 1<r) :
 0<(r-1)*(r^2+4*r-1)/4 :=
by exact div_pos (mul_pos (sub_pos.mpr hr) (by nlinarith [sq_nonneg r])) (by norm_num : (0:ℝ)<4)

theorem detuning_minimum (k n t L x Q v d : ℝ) (pos : 0<Q) (dt : 0≤d)
 (supp : L^2+d*x≤L*v) (slope : 0≤Q*x+t) :
 Q*L^2≤Q*L*v+t*d :=
by nlinarith only [mul_le_mul_of_nonneg_left supp pos.le,mul_nonneg dt slope]

theorem even_zero (g n k : ℝ) (h : 4*g^2=3*n^2) :
 2*k*g^2-3*k*n^2/2=0 := by linear_combination (k/2)*h

theorem odd_at_even_zero (n k : ℝ) (hn : n≠0) (hk : 0<k) :
 (3*k*n^2/2)/(n*(2*n^2+k^2/2))=3*k*n/(4*n^2+k^2) :=
begin
 have v : 2*n^2+k^2/2≠0 := ne_of_gt (by nlinarith [sq_nonneg n,sq_pos_of_ne_zero k (ne_of_gt hk)]),
 have w : 4*n^2+k^2≠0 := ne_of_gt (by nlinarith [sq_nonneg n,sq_pos_of_ne_zero k (ne_of_gt hk)]),
 apply (div_eq_div_iff (mul_ne_zero hn v) w).2, ring
end

theorem twolevel_generator (a b : ℝ) : (a^2+b^2)/4=(a/2)^2+(b/2)^2 := by ring
theorem phase_sensitive_loop (f : ℝ) :
 -real.cos (real.pi*f) = real.cos (real.pi*(1-f)) :=
by rw [mul_sub,mul_one,real.cos_sub,real.cos_pi,real.sin_pi]; ring

theorem double_clock_convolution (a b s : ℂ) (ab : a≠b) (da : a+s≠0) (db : b+s≠0) :
 a*b/(b-a)*(1/(a+s)-1/(b+s))=a*b/((a+s)*(b+s)) :=
by field_simp [da,db,sub_ne_zero.mpr (ne.symm ab)];ring

theorem survival_weights (a b : ℝ) (ha : 0<a) (hb : 0<b) :
 (a+b)/(a*b)=1/a+1/b := by field_simp [ne_of_gt ha,ne_of_gt hb];ring

theorem hydrogen_gap :
 ((1/(3:ℚ)^2-1/4^2)/2=7/288) ∧ ((1/(1:ℚ)^2-1/3^2)/2=4/9) := by norm_num

theorem lower_grav_width :
 (4/75:ℚ)*(4/9)^5*(98415/32768)=1/360 := by norm_num

theorem spin2_sum (u : ℝ) :
 (5/2)*(((1+u)/2)^4+((1-u)/2)^4)=5*(1+6*u^2+u^4)/16 := by ring

theorem scalar_fusion (s : ℝ) :
 (5/4)*(s^2/5)=s^2/4 := by ring

theorem flip_error (same both e₁ e₂ : ℝ) :
 same*((1-e₁)*(1-e₂)+e₁*e₂)+(both-same)*(e₁*(1-e₂)+(1-e₁)*e₂)=
 (1-2*(e₁+e₂-2*e₁*e₂))*same+(e₁+e₂-2*e₁*e₂)*both := by ring

-- x=(1-cos(theta_1))/2 and y=(1-cos(theta_2))/2 are uniform in their caps.
def angular (x y : ℝ) :=
 let u:=x+y-2*x*y, v:=4*x*(1-x)*y*(1-y) in (5/2)*(u^4+3*u^2*v+3*v^2/8)
def cap (x y : ℝ) :=
 (x*y^5+x^5*y)/2+5*(x^2*y^4+x^4*y^2)+10*x^3*y^3
 -5*(x^2*y^5+x^5*y^2)-25*(x^3*y^4+x^4*y^3)
 +15*(x^3*y^5+x^5*y^3)+(75/2)*x^4*y^4
 -(35/2)*(x^4*y^5+x^5*y^4)+7*x^5*y^5

theorem cap_exchange (x y : ℝ) : cap x y=cap y x := by unfold cap;ring
theorem cap_zero (x : ℝ) : cap x 0=0 := by simp [cap]
theorem cap_diagonal (p : ℝ) :
 cap p p=p^6*(21-60*p+135*p^2/2-35*p^3+7*p^4) := by unfold cap;ring
theorem cap_full_sky : cap 1 1=1/2 := by norm_num [cap]

def cap_y (x y : ℝ) :=
 (5*x*y^4+x^5)/2+5*(4*x^2*y^3+2*x^4*y)+30*x^3*y^2
 -5*(5*x^2*y^4+2*x^5*y)-25*(4*x^3*y^3+3*x^4*y^2)
 +15*(5*x^3*y^4+3*x^5*y^2)+150*x^4*y^3
 -(35/2)*(5*x^4*y^4+4*x^5*y^3)+35*x^5*y^4

-- Differentiation of this finite polynomial is checked by the kernel term by term.
abbreviation monom := ℝ × ℕ × ℕ
def poly (cs : list monom) (x y : ℝ) : ℝ :=
 (cs.map (λ c : monom, c.1*x^c.2.1*y^c.2.2)).sum
def py (cs : list monom) : list monom :=
 cs.map (λ c : monom, (c.1*(c.2.2:ℝ),c.2.1,c.2.2-1))
def px (cs : list monom) : list monom :=
 cs.map (λ c : monom, (c.1*(c.2.1:ℝ),c.2.1-1,c.2.2))
def coeffs : list monom :=
 [(1/2,1,5),(1/2,5,1),(5,2,4),(5,4,2),(10,3,3),(-5,2,5),(-5,5,2),
  (-25,3,4),(-25,4,3),(15,3,5),(15,5,3),(75/2,4,4),(-35/2,4,5),(-35/2,5,4),(7,5,5)]

theorem poly_dy (cs : list monom) (x y : ℝ) :
 has_deriv_at (poly cs x) (poly (py cs) x y) y :=
begin
 induction cs with t tail ih, {exact has_deriv_at_const y (0:ℝ)},
 rcases t with ⟨c,i,j⟩,
 have h := ((((has_deriv_at_id y).pow j).const_mul (c*x^i))).add ih,
 convert h using 1,
 {funext z, simp only [poly,list.map_cons,list.sum_cons,id.def]},
 {simp only [poly,py,list.map_cons,list.sum_cons,id.def,mul_one]; ring}
end
theorem poly_dx (cs : list monom) (x y : ℝ) :
 has_deriv_at (λ u,poly cs u y) (poly (px cs) x y) x :=
begin
 induction cs with t tail ih, {exact has_deriv_at_const x (0:ℝ)},
 rcases t with ⟨c,i,j⟩,
 have h := (((((has_deriv_at_id x).pow i).const_mul c).mul_const (y^j))).add ih,
 convert h using 1,
 {funext z, simp only [poly,list.map_cons,list.sum_cons,id.def]},
 {simp only [poly,px,list.map_cons,list.sum_cons,id.def,mul_one]; ring}
end

theorem cap_as_poly (x y : ℝ) : cap x y=poly coeffs x y :=
by norm_num [cap,poly,coeffs];ring
theorem dy_as_poly (x y : ℝ) : cap_y x y=poly (py coeffs) x y :=
by norm_num [cap_y,poly,py,coeffs];ring
theorem mixed_as_poly (x y : ℝ) : angular x y=poly (px (py coeffs)) x y :=
by norm_num [angular,poly,px,py,coeffs];ring

theorem cap_partial_y (x y : ℝ) : has_deriv_at (cap x) (cap_y x y) y :=
begin
 have forms : cap x=poly coeffs x := funext (cap_as_poly x),
 rw [forms,dy_as_poly], exact poly_dy coeffs x y
end
theorem cap_mixed (x y : ℝ) : has_deriv_at (λ u,cap_y u y) (angular x y) x :=
begin
 have forms : (λ u, cap_y u y)=(λ u,poly (py coeffs) u y) := funext (λ u, dy_as_poly u y),
 rw [forms,mixed_as_poly], exact poly_dx (py coeffs) x y
end

theorem cap_as_integral (p q : ℝ) :
 (∫ y in (0:ℝ)..q, ∫ x in (0:ℝ)..p, angular x y)=cap p q :=
begin
 have ii : ∀ y, (∫ x in (0:ℝ)..p, angular x y)=cap_y p y,
 {intro y, have hc : continuous (λ x, angular x y) := by {unfold angular,continuity},
   have k:=interval_integral.integral_eq_sub_of_has_deriv_at
      (λ x hx,cap_mixed x y) (hc.interval_integrable 0 p),
   simpa [cap_y] using k },
 simp_rw [ii],
 have c : continuous (cap_y p) := by {change continuous (λ y, cap_y p y), unfold cap_y,continuity},
 have k:=interval_integral.integral_eq_sub_of_has_deriv_at
      (λ y hy,cap_partial_y p y) (c.interval_integrable 0 q),
 simpa [cap_zero] using k
end

theorem slow_last_line : (5/2:ℚ)*(1/55+2/9+4/7+2/5+1/15)=2215/693 := by norm_num

theorem open_matrix_radial (d L : ℝ) (hd : 0<d) (hL : 0<L) :
 (4*d/(L*(L+2)))/(d/2)=8/(L*(L+2)) :=
by have hn : L+2≠0 := ne_of_gt (by linarith); field_simp [ne_of_gt hL,ne_of_gt hd,hn];ring

def angular_primitive (a b c d θ : ℝ) := real.sin θ *
 (a+b*real.cos θ+c*(real.cos θ)^2+d*(real.cos θ)^3)
theorem azimuth_primitive (a b c d θ : ℝ) :
 has_deriv_at (angular_primitive a b c d)
  (a*real.cos θ+b*(2*(real.cos θ)^2-1)+c*(3*(real.cos θ)^3-2*real.cos θ)+
   d*(4*(real.cos θ)^4-3*(real.cos θ)^2)) θ :=
begin
 have dc:= real.has_deriv_at_cos θ,
 have deriv := (real.has_deriv_at_sin θ).mul
  ((((has_deriv_at_const θ a).add (dc.const_mul b)).add ((dc.pow 2).const_mul c)).add
  ((dc.pow 3).const_mul d)),
 have algebra : ∀ x y : ℝ, y^2+x^2=1 →
   a*x+b*(2*x^2-1)+c*(3*x^3-2*x)+d*(4*x^4-3*x^2)=
   x*(a+b*x+c*x^2+d*x^3)+y*(-b*y-2*c*x*y-3*d*x^2*y),
 {intros x y sq, linear_combination (b+2*c*x+3*d*x^2)*sq},
 convert deriv using 1,
 rw [algebra _ _ (real.sin_sq_add_cos_sq θ)],
 norm_num; ring; try {left;refl}
end
theorem azimuth_average (u v : ℝ) :
 (∫ t in (0:ℝ)..(2*real.pi), (u-v*real.cos t)^4)=
  2*real.pi*(u^4+3*u^2*v^2+3*v^4/8) :=
begin
 let a := -4*u^3*v-8*u*v^3/3, let b:=3*u^2*v^2+3*v^4/8,
 let c:= -4*u*v^3/3, let d:=v^4/4, let avg:=u^4+3*u^2*v^2+3*v^4/8,
 let prim:=λ t:ℝ,avg*t+angular_primitive a b c d t,
 have h : ∀ t, has_deriv_at prim ((u-v*real.cos t)^4) t,
 { intro t, have z:=((has_deriv_at_id t).const_mul avg).add (azimuth_primitive a b c d t),
   convert z using 1, dsimp [a,b,c,d,avg], ring },
 have cont : continuous (λ t:ℝ,(u-v*real.cos t)^4) := by continuity,
 have k:=interval_integral.integral_eq_sub_of_has_deriv_at (λ x hx,h x)
  (cont.interval_integrable 0 (2*real.pi)),
 rw [k], dsimp only [prim,angular_primitive],
 rw [real.sin_two_pi,real.sin_zero], dsimp only [avg], ring
end

theorem two_caps_leading (x y s : ℝ) :
 let lead := x*y^5/2+5*x^2*y^4+10*x^3*y^3+5*x^4*y^2+x^5*y/2 in
 cap (s*x) (s*y)-s^6*lead=s^7*
 (-5*(x^2*y^5+x^5*y^2)-25*(x^3*y^4+x^4*y^3)+s*(15*(x^3*y^5+x^5*y^3)+75*x^4*y^4/2)
  -s^2*35*(x^4*y^5+x^5*y^4)/2+s^3*7*x^5*y^5) := by dsimp [cap];ring

theorem cap_boost (v z : ℝ) (n : 1+v*z≠0) :
 (1-(z+v)/(1+v*z))/2=(1-v)*(1-z)/(2*(1+v*z)) := by field_simp [n];ring

theorem ordinary_line_normalization (q : ℝ) (h : 0<q) :
 let d:=q+2, t:=(q+2)*(q+1)/2-1, D:=(q+2)*(q+3)/2-1 in
 q*(q+1)/2-1+q/d+(1+2*q/d+3*q^2/(d*(d+2)))/(q+1)^2=t^2/D :=
begin
 dsimp, have a:q+2≠0:=ne_of_gt (by linarith),have b:q+2+2≠0:=ne_of_gt (by linarith),
 have c:q+1≠0:=ne_of_gt (by linarith),
 have e: (q+2)*(q+3)/2-1 ≠ 0 :=ne_of_gt (by nlinarith [sq_nonneg q]),
 apply (eq_div_iff e).2, field_simp [a,b,c];ring
end

def parallel_enhancement (d : ℚ) := (d*(d+1)/2-1)/(d*(d-1)/2-1)
theorem tensor_dimensions :
 parallel_enhancement 3=5/2 ∧ parallel_enhancement 9=44/35 ∧ parallel_enhancement 10=27/22 :=
by norm_num [parallel_enhancement]


theorem oscillator_second_derivative (L i : ℝ) :
 has_deriv_at (λ x : ℝ,4*x*(L+x^2)) (4*(L+i^2)+8*i^2) i :=
begin
 have h := ((has_deriv_at_id i).const_mul 4).mul (((has_deriv_at_id i).pow 2).const_add L),
 convert h using 1; dsimp; norm_num; ring
end

theorem bmn_color_contraction (trT quad r : ℝ) (tracefree : trT=0) :
 8*quad+4*trT*r=8*quad := by rw [tracefree];ring
theorem bmn_norm (L : ℝ) : 4*(L+2)*(2*L)=8*L*(L+2) :=by ring
theorem bmn_examples : (8/(9*(9+2)):ℚ)=8/99 ∧ (8/(24*(24+2)):ℚ)=1/78 := by norm_num

-- Factorial moments for the Coulomb quadrupoles, after the standard gamma integral.
def coulomb_moment (a : ℚ) (n : ℕ) : ℚ := (n.factorial:ℚ)/a^(n+1)
theorem cascade_radial_integrals :
 let u:=coulomb_moment (7/12), v:=coulomb_moment (4/3) in
 (1/(256*2430):ℚ)*(4/9*(4*u 6-3*u 7+u 8/2-u 9/48))^2 =
  3462669979122401280/1628413597910449 ∧
 (4/2430:ℚ)*(4/9*v 6)^2=98415/32768 :=
by norm_num [coulomb_moment,nat.factorial]

-- Purity in every input ray fixes a common scalar even on a degenerate sector.
theorem scalar_on_fixed_rays {V : Type*} [add_comm_group V] [module ℂ V]
 (K : V →ₗ[ℂ] V) (f : V →ₗ[ℂ] ℂ) (u : V) (hu : f u=1)
 (ray : ∀ v : V, ∃ a : ℂ, K v=a • v) :
 ∃ a : ℂ, ∀ v : V, K v=a • v :=
begin
 obtain ⟨a,au⟩:=ray u, refine ⟨a,_⟩,
 have ker : ∀ w : V, f w=0 → K w=a • w,
 { intros w hw, obtain ⟨b,bw⟩:=ray w, obtain ⟨c,cs⟩:=ray (w+u),
   rw [map_add,bw,au,smul_add] at cs,
   have z := congr_arg (λ v:V, f v) cs,
   simp [hw,hu] at z, rw [←z] at cs,
   calc K w=b • w : bw
   ... =a • w : add_right_cancel cs },
 intro v, let w:=v-(f v) • u,
 have fw : f w=0 := by simp [w,hu],
 have decomp : v=w+(f v) • u := by simp [w],
 calc K v=K (w+(f v) • u) : congr_arg K decomp
 ... =a • w+(f v) • (a • u) : by rw [map_add,ker w fw,K.map_smul,au]
 ... =a • (w+(f v) • u) : by simp only [smul_add,←mul_smul]; rw [mul_comm (f v) a]
 ... =a • v : congr_arg _ decomp.symm
end

-- A missed outcome has one amplitude vector for each parity. The record may be arbitrarily large.
theorem missed_pointer_overlap {H : Type*} [normed_add_comm_group H] [inner_product_space ℂ H]
 (a b : H) (q₁ q₂ : ℝ) (ha : ‖a‖^2=1-q₁) (hb : ‖b‖^2=1-q₂) :
 ‖(inner a b : ℂ)‖^2 ≤ (1-q₁)*(1-q₂) :=
begin
 have h : ‖(inner a b : ℂ)‖≤‖a‖*‖b‖ := norm_inner_le_norm a b,
 calc ‖(inner a b : ℂ)‖^2 ≤ (‖a‖*‖b‖)^2 : pow_le_pow_of_le_left (norm_nonneg _) h 2
 ... = (1-q₁)*(1-q₂) : by rw [mul_pow,ha,hb]
end

-- Half-sum and half-difference readout in the order and parity bases.
theorem parity_readout (z : ℂ) :
 (1/2:ℝ)-(z*(1/2:ℂ)).re=(1-z.re)/2 ∧
 (1/2:ℝ)+(z*(complex.I/2)).re=(1-z.im)/2 ∧
 (1/2:ℝ)-(z*(complex.I/2)).re=(1+z.im)/2 :=
begin
 have h : (1/2:ℂ)=((1/2:ℝ):ℂ) := by norm_num,
 have h' : complex.I/2=complex.I*((1/2:ℝ):ℂ) := by rw [←h];ring,
 rw [h,h'], simp only [complex.mul_re,complex.mul_im,complex.of_real_re,
 complex.of_real_im,complex.I_re,complex.I_im], split; try {split};ring
end

theorem orbital_disk (z : ℂ) (T D q₁ q₂ : ℝ) (ht : 1-2*T=z.re) (hd : D=|z.im|)
 (miss : ‖z‖^2≤(1-q₁)*(1-q₂)) : (1-2*T)^2+D^2≤(1-q₁)*(1-q₂) :=
begin
 rw [ht,hd,sq_abs], rw [complex.norm_eq_abs,complex.sq_abs,complex.norm_sq_apply] at miss,
 nlinarith [miss]
end

theorem label_exchange_floor (q T D : ℝ) (hq : q≤1)
 (disk : (1-2*T)^2+D^2≤(1-q)^2) : q/2≤T ∧ T≤1-q/2 :=
begin
 have h : (1-2*T)^2≤(1-q)^2 := by nlinarith [sq_nonneg D],
 have h₁ : 1-2*T≤1-q,
 { by_contra hh, have hp:0<(1-2*T)-(1-q):=by linarith [lt_of_not_ge hh],
   have hs:0<(1-2*T)+(1-q):=by linarith, nlinarith [mul_pos hp hs] },
 have h₂ : -(1-q)≤1-2*T,
 { by_contra hh, have hp:0< -(1-2*T)-(1-q):=by linarith [lt_of_not_ge hh],
   have hs:0< -(1-2*T)+(1-q):=by linarith, nlinarith [mul_pos hp hs] },
 constructor;linarith
end

theorem zero_transfer (x y : ℝ) (disk : x^2+y^2≤1) (none : (1-x)/2=0) :
 x=1 ∧ y=0 :=
begin
 have h:x=1:=by linarith, rw [h] at disk,
 refine ⟨h,_⟩, by_contra hne, nlinarith [sq_pos_of_ne_zero y hne]
end

theorem saturated_gravity_trigger (q c s : ℝ) (circle : c^2+s^2=1) :
 (1-2*((1-(1-q)*c)/2))^2+((1-q)*s)^2=(1-q)^2 :=
by linear_combination (1-q)^2*circle

-- Accessible outgoing waves can have norms less than one. Their missing norm never counts as a mark.
theorem collected_gram (a b s q d : ℝ) (hq₁ : q≤a) (hq₂ : q≤b)
 (miss : s^2≤(a-q)*(b-q)) (hd : 0≤d) (root : d^2=(a-b)^2+4*s^2) :
 q≤(a+b-d)/2 :=
begin
 by_contra hq, have h : a+b-2*q<d := by linarith [lt_of_not_ge hq],
 have hpos : 0≤a+b-2*q := by linarith,
 have h2 := pow_lt_pow_of_lt_left h hpos (by norm_num : 0<(2:ℕ)),
 nlinarith [h2]
end

theorem collected_optimum_attained (a b s d : ℝ) (root : d^2=(a-b)^2+4*s^2) :
 (a-(a+b-d)/2)*(b-(a+b-d)/2)=s^2 :=
by linear_combination root/4

theorem stationary_overlap_zero {α : Type*} [measurable_space α] {μ : measure_theory.measure α} (p e : α → ℝ)
 (h : ∀ᵐ x ∂μ, 0<p x) (hz : ∀ᵐ x ∂μ, e x*p x=0) : ∀ᵐ x ∂μ, e x=0 :=
begin
 filter_upwards [h,hz] with x positive disabled,
 exact (mul_eq_zero.mp disabled).resolve_right (ne_of_gt positive)
end

theorem stationary_read_of_zero_error {α : Type*} [measurable_space α] {μ : measure_theory.measure α}
 (p e : α → ℝ) (h : ∀ᵐ x ∂μ, 0<p x) (he : ∀ x, 0≤e x)
 (hint : integrable (λ x,e x*p x) μ) (no_error : (∫ x, e x*p x ∂μ)=0) :
 ∀ᵐ x ∂μ,e x=0 :=
begin
 apply stationary_overlap_zero p e h,
 apply (integral_eq_zero_iff_of_nonneg_ae _ hint).mp no_error,
 filter_upwards [h] with x positive, exact mul_nonneg (he x) positive.le
end

theorem clock_fibre_gram (a b c d : ℂ) :
 complex.norm_sq a*complex.norm_sq d+complex.norm_sq b*complex.norm_sq c-
 (2*(a*d*(conj (b*c))).re)=complex.norm_sq (a*d-b*c) :=
by simp [complex.norm_sq_apply,complex.mul_re,complex.mul_im,complex.conj_re,
 complex.conj_im,complex.sub_re,complex.sub_im];ring

theorem two_lorentz_poles (e u v g : ℂ) :
 (e-v)*(e-g-u)-(e-u)*(e-g-v)=g*(v-u) := by ring

theorem feasible_gram_mixture {V : Type*} (G₁ G₂ D₁ D₂ : V → ℝ) (w : ℝ)
 (hw : 0≤w) (hu : w≤1) (h₁ : ∀ x, D₁ x≤G₁ x) (h₂ : ∀ x, D₂ x≤G₂ x) :
 ∀ x, w*D₁ x+(1-w)*D₂ x≤w*G₁ x+(1-w)*G₂ x :=
λ x, add_le_add (mul_le_mul_of_nonneg_left (h₁ x) hw)
                (mul_le_mul_of_nonneg_left (h₂ x) (sub_nonneg.mpr hu))

theorem ambiguous_sum (r u s : ℝ) (hr : 0≤r) (hu : 0≤u) (hs : 0≤s)
 (bound : s^2≤r*u) : 2*s≤r+u :=
begin
 by_contra no, have h:r+u<2*s:=lt_of_not_ge no,
 have h₂: (r+u)^2<(2*s)^2 := pow_lt_pow_of_lt_left h (add_nonneg hr hu) (by norm_num),
 nlinarith [sq_nonneg (r-u)]
end

theorem asymmetric_failure_minimum (r u b s : ℝ) (hb : 0<b) (hu : 0≤u)
 (ur : u≤b) (bs : b<s) (miss : s^2≤r*u) : b+s^2/b≤r+u :=
begin
 have rb : b≤r,
 {by_contra no, have lt:r<b:=lt_of_not_ge no,
  have m:=mul_le_mul_of_nonneg_right (le_of_lt lt) hu,
  have m':=mul_le_mul_of_nonneg_left ur hb.le,
  nlinarith [mul_pos (sub_pos.mpr bs) (show 0<s+b,by linarith)]},
 have t:s^2/b≤(r+u)-b := (div_le_iff hb).2
  (by nlinarith [mul_nonneg (sub_nonneg.mpr ur) (sub_nonneg.mpr rb)]),
 linarith
end

theorem asymmetric_failure_attained (b s : ℝ) (hb : b≠0) : b*(s^2/b)=s^2 :=
by field_simp [hb];ring

theorem weak_line_density (a u v : ℝ) (ha : a≠0) (hu : 0<u) (hv : 0<v) :
 (a^4/(u^2*v^2))/(2*(a^2*(1/u+1/v)))=a^2/(2*u*v*(u+v)) :=
begin
 have sum : 1/u+1/v=(u+v)/(u*v) := by field_simp [ne_of_gt hu,ne_of_gt hv];ring,
 rw [sum],field_simp [ha,ne_of_gt hu,ne_of_gt hv,ne_of_gt (add_pos hu hv)];ring
end

theorem lorentz_partial_fraction (x b c : ℝ) :
 let u:=x^2+2*c*x+b^2, v:=x^2-2*c*x+b^2, d:=x^2+b^2 in
 8*c^2*b^4=2*b^2*u*v+(2*c*x+4*c^2-b^2)*d*v+(-2*c*x+4*c^2-b^2)*d*u :=
by dsimp;ring

def line_primitive (a c g k x : ℝ) :=
 g/2*real.log ((x+c)^2+a^2)+k/a*real.arctan ((x+c)/a)
theorem line_primitive_derivative (a c g k x : ℝ) (ha : 0<a) :
 has_deriv_at (line_primitive a c g k) ((g*(x+c)+k)/((x+c)^2+a^2)) x :=
begin
 have z : (x+c)^2+a^2≠0 := ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero a (ne_of_gt ha))),
 have dx:= (has_deriv_at_id x).add_const c,
 have logd:=(((dx.pow 2).add_const (a^2)).log z).const_mul (g/2),
 have atan:=((dx.div_const a).arctan).const_mul (k/a),
 have den:1+((x+c)/a)^2=((x+c)^2+a^2)/a^2 := by field_simp [ne_of_gt ha];ring,
 have frac:1/(1+((x+c)/a)^2)=a^2/((x+c)^2+a^2) := by rw [den];simp [div_eq_mul_inv,mul_comm],
 convert logd.add atan using 1,
 dsimp only [id.def], rw [frac],
 norm_num, field_simp [ne_of_gt ha,z];ring
end

theorem line_primitive_integral (a c g k l r : ℝ) (ha : 0<a) :
 (∫ x in l..r, (g*(x+c)+k)/((x+c)^2+a^2)) =
 line_primitive a c g k r-line_primitive a c g k l :=
begin
 have nn : ∀ x:ℝ, (x+c)^2+a^2≠0 := λ x, ne_of_gt
  (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero a (ne_of_gt ha))),
 have cont : continuous (λ x:ℝ,(g*(x+c)+k)/((x+c)^2+a^2)) :=
  ((continuous_const.mul (continuous_id.add continuous_const)).add continuous_const).div
  (((continuous_id.add continuous_const).pow 2).add continuous_const) nn,
 exact interval_integral.integral_eq_sub_of_has_deriv_at
  (λ x hx,line_primitive_derivative a c g k x ha) (cont.interval_integrable l r)
end

theorem line_residue (a b c : ℝ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
 (root : b^2=a^2+c^2) :
 1/(8*c^2*b^2)/b+2*((4*c^2-b^2)/(16*c^2*b^4)-1/(8*b^4))/a =
 (2*a+b)/(8*a*b^4*(a+b)) :=
begin
 have sub : c^2=b^2-a^2 := by linarith,
 have nb : b^2-a^2≠0 := sub ▸ pow_ne_zero 2 (ne_of_gt hc),
 rw [sub],field_simp [ne_of_gt ha,ne_of_gt hb,nb,ne_of_gt (add_pos ha hb)];ring
end

def clock_fraction (t : ℝ) := (t-1)*(t+2)/t^4

theorem clock_fraction_from_integral (a t c : ℝ) (ha : 0<a) (ht : 1≤t)
 (root : c^2=a^2*(t^2-1)) :
 (2*c)^2*(2*a+a*t)/(32*(a*t)^4*(a+a*t)) =
 (1/(2*(2*a)^2))*clock_fraction t :=
begin
 unfold clock_fraction,
 have pos : 0<t:=by linarith,
 have hsum : 0<a+a*t := add_pos ha (mul_pos ha pos),
 rw [show (2*c)^2=4*c^2, by ring,root],
 field_simp [ne_of_gt ha,ne_of_gt pos,ne_of_gt hsum];ring
end

theorem best_material_gap (r : ℝ) (h : r=(real.sqrt 73-3)/4) :
 1<r ∧ 2*r^2+3*r=8 :=
begin
 have sq := real.sq_sqrt (show (0:ℝ)≤73, by norm_num),
 have pos:=real.sqrt_nonneg (73:ℝ),
 have more : 7<real.sqrt (73:ℝ) := by nlinarith,
 rw [h], constructor, {linarith}, {linear_combination sq/8}
end

theorem gap_maximizes_clock (r t : ℝ) (hr : 1<r) (ht : 1≤t)
 (root : 2*r^2+3*r=8) : clock_fraction t≤clock_fraction r :=
begin
 have tp : 0<t:=by linarith, have rp:0<r:=by linarith,
 have co : 0<(r-1)*(r+2) := mul_pos (sub_pos.mpr hr) (by linarith),
 have poly : ((r-1)*(r+2))*t^4-((t-1)*(t+2))*r^4 =
 (t-r)^2*((r-1)*(r+2)*t^2+2*r*(r-1)*(r+2)*t+2*r^2) :=
 by linear_combination (r^2*t^2-r^3*t)*root,
 have pp:0≤(r-1)*(r+2)*t^2+2*r*((r-1)*(r+2))*t+2*r^2 := by positivity,
 unfold clock_fraction, apply (div_le_div_iff (pow_pos tp _) (pow_pos rp _)).2,
 nlinarith only [poly,mul_nonneg (sq_nonneg (t-r)) pp]
end

-- Continuum readout with no external time reference.
theorem causal_collection_order {V : Type*} (near far unit : V → ℝ) (q : ℝ)
 (contraction : ∀ x, far x≤near x) (read : ∀ x,q*unit x≤far x) :
 ∀ x,q*unit x≤near x := λ x, (read x).trans (contraction x)

def ordered_yield (m M s : ℝ) : ℝ :=
 if s≤m then (m+M-2*s)/2 else (m*M-s^2)/(2*m)

theorem spectrum_sandwich (m M s : ℝ) (hm : 0<m) (hs : 0<s) (ord : m≤M)
 (pos : s^2≤m*M) :
 (m*M-s^2)/(2*m)≤ordered_yield m M s ∧
 ordered_yield m M s≤(m*M-s^2)/(2*min s m) :=
begin
 by_cases h : s≤m,
 {rw [ordered_yield,if_pos h,min_eq_left h],constructor,
  {apply (div_le_iff (by linarith : 0<2*m)).2, nlinarith [sq_nonneg (m-s)]},
  {apply (le_div_iff (by linarith : 0<2*s)).2,
   nlinarith [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (h.trans ord))]}},
 {rw [ordered_yield,if_neg h,min_eq_right (le_of_not_ge h)],exact ⟨le_rfl,le_rfl⟩}
end

theorem spectrum_domination (m M s : ℝ) (hm : 0<m) (hs : 0≤s) (ord : m≤M)
 (pos : s^2≤m*M) : ordered_yield m M s≤(m*M-s^2)/m :=
begin
 by_cases h:s≤m,
 {rw [ordered_yield,if_pos h],apply (le_div_iff hm).2,
  nlinarith [mul_nonneg hm.le (sub_nonneg.mpr ord),mul_nonneg hs (sub_nonneg.mpr h)]},
 {rw [ordered_yield,if_neg h],exact div_le_div_of_le_left (sub_nonneg.mpr pos) hm (by linarith)}
end

open filter
open_locale topology
theorem weak_spectral_limit (m M s delta : ℕ → ℝ) (A K : ℝ)
 (a : 0<A) (mpos : ∀ n,0<m n) (spos : ∀ n,0<s n) (ord : ∀ n,m n≤M n)
 (gram : ∀ n,(s n)^2≤m n*M n) (hm : tendsto m at_top (𝓝 A))
 (hs : tendsto s at_top (𝓝 A))
 (det : tendsto (λ n,(m n*M n-(s n)^2)/(delta n)^2) at_top (𝓝 K)) :
 tendsto (λ n,ordered_yield (m n) (M n) (s n)/(delta n)^2) at_top (𝓝 (K/(2*A))) :=
begin
 have small : tendsto (λ n,min (s n) (m n)) at_top (𝓝 A) :=
  by simpa only [min_self] using hs.min hm,
 have nzero : (2:ℝ)*A≠0 := mul_ne_zero (by norm_num) (ne_of_gt a),
 have t₁ : tendsto (λ n:ℕ,(2:ℝ)*m n) at_top (𝓝 (2*A)) :=
  (tendsto_const_nhds : tendsto (λ _:ℕ,(2:ℝ)) at_top (𝓝 2)).mul hm,
 have t₂ : tendsto (λ n:ℕ,(2:ℝ)*min (s n) (m n)) at_top (𝓝 (2*A)) :=
  (tendsto_const_nhds : tendsto (λ _:ℕ,(2:ℝ)) at_top (𝓝 2)).mul small,
 have low : tendsto (λ n:ℕ,(m n*M n-(s n)^2)/(delta n)^2/(2*m n)) at_top (𝓝 (K/(2*A))) :=
  filter.tendsto.div det t₁ nzero,
 have hi : tendsto (λ n:ℕ,(m n*M n-(s n)^2)/(delta n)^2/(2*min (s n) (m n))) at_top (𝓝 (K/(2*A))) :=
  filter.tendsto.div det t₂ nzero,
 apply tendsto_of_tendsto_of_tendsto_of_le_of_le low hi,
 {intro n,change (m n*M n-(s n)^2)/(delta n)^2/(2*m n)≤_,
  rw [div_right_comm],exact div_le_div_of_le_of_nonneg
   (spectrum_sandwich _ _ _ (mpos n) (spos n) (ord n) (gram n)).1 (sq_nonneg _)},
 {intro n,change _≤(m n*M n-(s n)^2)/(delta n)^2/(2*min (s n) (m n)),
  rw [div_right_comm (m n*M n-(s n)^2)],exact div_le_div_of_le_of_nonneg
   (spectrum_sandwich _ _ _ (mpos n) (spos n) (ord n) (gram n)).2 (sq_nonneg _)}
end

theorem pole_denominator_control (x v a C : ℝ) (a0 : 0<a) (bound : v^2≤C^2) :
 (1+x^2)*a^2≤(2*a^2+1+2*C^2)*((x-v)^2+a^2) ∧
 (x-v)^2+a^2≤(2+2*C^2+a^2)*(1+x^2) :=
begin
 have small : x^2≤2*(x-v)^2+2*C^2 := by nlinarith [sq_nonneg (x-2*v)],
 have large : (x-v)^2≤2*x^2+2*C^2 := by nlinarith [sq_nonneg (x+v)],
 constructor,
 {nlinarith only [mul_le_mul_of_nonneg_right small (sq_nonneg a),
   mul_nonneg (show 0≤1+2*C^2,by positivity) (sq_nonneg (x-v))]},
 {nlinarith [mul_nonneg (show 0≤2*C^2+a^2,by positivity) (sq_nonneg x)]}
end

theorem integrated_spectral_limit (F : ℕ → ℝ → ℝ) (limit : ℝ → ℝ) (C : ℝ)
 (meas : ∀ n,ae_strongly_measurable (F n) volume)
 (bound : ∀ n,∀ x,‖F n x‖≤C*((1+‖x‖^2)^(-(6:ℝ)/2)))
 (point : ∀ x,tendsto (λ n,F n x) at_top (𝓝 (limit x))) :
 tendsto (λ n,∫ x,F n x) at_top (𝓝 (∫ x,limit x)) :=
begin
 have dim : (finite_dimensional.finrank ℝ ℝ:ℝ)<6 := by simp [finite_dimensional.finrank_self];norm_num,
 have integr : integrable (λ x:ℝ,(1+‖x‖^2)^(-(6:ℝ)/2)) :=
  integrable_rpow_neg_one_add_norm_sq dim,
 exact tendsto_integral_of_dominated_convergence _ meas (integr.const_mul C)
  (λ n,eventually_of_forall (bound n)) (eventually_of_forall point)
end

end causal_gravity_receiver
