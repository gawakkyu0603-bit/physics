import analysis.special_functions.gamma.basic
import analysis.special_functions.trigonometric.bounds
import measure_theory.constructions.prod.integral
import analysis.special_functions.improper_integrals
import analysis.special_functions.integrals
import analysis.special_functions.trigonometric.deriv
import measure_theory.integral.integral_eq_improper
import analysis.special_functions.exp
import analysis.special_functions.exponential
import tactic

noncomputable theory
open_locale big_operators topology
open filter measure_theory finset
namespace matrix_layer_work

-- xi indexes genuine simultaneous constituents of one matrix configuration.
theorem ordered_differences {ι : Type*} (s : finset ι) (u v : ι → ℝ) :
 (∑ i in s, ∑ j in s, (u i-u j)*(v i-v j)) =
  2*(s.card:ℝ)*(∑ i in s, u i*v i)-2*(∑ i in s,u i)*(∑ j in s,v j) :=
begin
 classical,
 simp_rw [show ∀ i j,(u i-u j)*(v i-v j)=u i*v i-u i*v j-u j*v i+u j*v j,
           from λ i j,by ring],
 simp only [sum_add_distrib,sum_sub_distrib,←mul_sum,←sum_mul,sum_const,nsmul_eq_mul],
 ring
end

theorem diagonal_removal {ι : Type*} [decidable_eq ι] (s : finset ι) (u v : ι → ℝ) :
 (∑ i in s,u i)*(∑ j in s,v j) =
 (∑ i in s,u i*v i)+(∑ i in s,∑ j in s.erase i,u i*v j) :=
begin
 rw [sum_mul,←sum_add_distrib],
 apply sum_congr rfl,intros i hi,
 rw [mul_sum,add_comm, sum_erase_add _ _ hi]
end

theorem traceremoval (n c diag prod pair : ℝ) (hn : n≠0)
 (h : n^2*prod=n*diag+n*(n-1)*pair) :
 c/(2*n)*(diag-prod)=c*(n-1)/(2*n^2)*(diag-pair) :=
begin
 have hc := congr_arg (λ a:ℝ,c*a) h,
 dsimp at hc,field_simp [hn],nlinarith only [hc]
end

theorem reconstruct (n c diag work pair : ℝ) (hn : n≠0) (hn1 : n-1≠0) (hc : c≠0)
 (hm : work=c*(n-1)/(2*n^2)*(diag-pair)) :
 pair=diag-2*n^2*work/(c*(n-1)) :=
by rw [hm];field_simp [hn,hn1,hc];ring

theorem constant_cancellation (uv u v a b : ℝ) :
 (uv-a*v-b*u+a*b)-(u-a)*(v-b)=uv-u*v := by ring

theorem centered_marginals (uv joint u v a b : ℝ) :
 (uv-a*v-b*u+a*b)-(joint-a*v-b*u+a*b)=uv-joint := by ring

theorem recoil_pair (n m e s : ℝ) (hn : n-1≠0) (he : e≠0) (h : m=e*(1-s)) :
 (n*s-1)/(n-1)=1-n/(n-1)*(m/e) :=
by rw [h];field_simp [hn,he];ring

theorem rank_two_work (k phi : ℝ) :
 k^2/4*(1-(1+phi)/2)=k^2*(1-phi)/8 := by ring

theorem circle_opens (g l n : ℝ) : (g*l)*l*n^2=g*(n*l)^2 := by ring

theorem angular_four (x y z : ℝ) :
 3*(x^2+y^2+z^2)+2*(x*y+y*z+z*x)=3*(x+y+z)^2-4*(x*y+y*z+z*x) := by ring

theorem angular_six (x y z : ℝ) :
 15*(x^3+y^3+z^3)+9*(x^2*(y+z)+y^2*(x+z)+z^2*(x+y))+6*x*y*z =
 15*(x+y+z)^3-36*(x+y+z)*(x*y+y*z+z*x)+24*x*y*z := by ring

theorem quartic_trace (q v : ℝ) : 3*(8*q)-4*(4*v)=24*q-16*v := by ring
theorem sextic_trace (q v d : ℝ) : 15*(32*q)-36*(8*v)+24*(8*d)=480*q-288*v+192*d := by ring
theorem lowest_work (t : ℝ) : (2*t/9)/16=t/72 := by ring
theorem two_body_moment (k m2 m4 m6 : ℝ) :
 k^2/8*(m2*k^2/2-m4*k^4/24+m6*k^6/720) =
 m2*k^4/16-m4*k^6/192+m6*k^8/5760 := by ring

def angular_primitive (x : ℝ) := x^10/10-x^12/4+3*x^14/14-x^16/16
theorem angular_derivative (x : ℝ) : has_deriv_at angular_primitive (x^9*(1-x^2)^3) x :=
begin
 have h := (((((has_deriv_at_id x).pow 10).div_const 10).sub
   (((has_deriv_at_id x).pow 12).div_const 4)).add
   ((((has_deriv_at_id x).pow 14).const_mul 3).div_const 14)).sub
   (((has_deriv_at_id x).pow 16).div_const 16),
 convert h using 1; try {ext t}; simp [angular_primitive];ring
end
theorem sphere_ninth :
 (35/16:ℝ)*(∫ x in (0:ℝ)..1,x^9*(1-x^2)^3)=1/256 :=
begin
 have ct : continuous (λ x:ℝ,x^9*(1-x^2)^3) := by continuity,
 rw [interval_integral.integral_eq_sub_of_has_deriv_at (λ x hx,angular_derivative x)
      (ct.interval_integrable 0 1)],
 norm_num [angular_primitive],all_goals {apply_instance}
end
theorem projected_tail : (60480:ℝ)*(1/256)/9=105/4 := by norm_num
theorem laplace_remainder (t : ℝ) (h : t≠0) :
 1/t-1/t^3+1/t^5-1/t^7+1/t^9-t/(1+t^2)=1/(t^9*(1+t^2)) :=
begin have hp : 1+t^2≠0 := by positivity,
 field_simp [h,hp];ring end
theorem laplace_weight (t : ℝ) (h : t≠0) :
 t^9*(1/(t^9*(1+t^2)))=1/(1+t^2) :=
begin have hp : 1+t^2≠0 := by positivity,
 field_simp [h,hp];ring end
theorem tail_constant (p : ℝ) : 9*(105/4:ℝ)*p/(2*362880)=p/3072 := by ring
theorem tail_to_work (p : ℝ) : (p/3072)/8=p/24576 := by ring

-- The physical premise here is the asymptotic radial density and conditional
-- alignment of the large matrix singular value. The limiting integration is
-- over a specified real measure, and measurability and domination are explicit.
theorem integrate_tail_limit {ι : Type*} {l : filter ι} [l.is_countably_generated]
 (μ : measure ℝ) (H : ι → ℝ → ℝ) (kernel bound : ℝ → ℝ) (C : ℝ)
 (hM : ∀ᶠ i in l, ae_strongly_measurable (λ u,kernel u*H i u) μ)
 (hB : ∀ᶠ i in l,∀ᵐ u ∂μ, ‖kernel u*H i u‖≤bound u) (hI : integrable bound μ)
 (hL : ∀ᵐ u ∂μ,tendsto (λ i,H i u) l (𝓝 (C/u^9))) :
 tendsto (λ i, ∫ u,kernel u*H i u ∂μ) l (𝓝 (C*∫ u,kernel u/u^9 ∂μ)) :=
begin
 have hh : ∀ᵐ u ∂μ, tendsto (λ i,kernel u*H i u) l (𝓝 (C*(kernel u/u^9))),
 { filter_upwards [hL] with u hu,
   convert (tendsto_const_nhds.mul hu : tendsto _ l (𝓝 (kernel u*(C/u^9)))) using 1;ring },
 have h := tendsto_integral_filter_of_dominated_convergence bound hM hB hI hh,
 simpa only [integral_mul_left] using h
end

-- Physical mode amplitudes can be signed. A positive output band makes their
-- dot product the Hellinger affinity; different phases can obscure information.
def kplus (a : ℝ) := (real.cos a+real.sin a)/real.sqrt 2
def kminus (a : ℝ) := (real.cos a-real.sin a)/real.sqrt 2
theorem root_two_sq : (real.sqrt 2)^2=2 := real.sq_sqrt (by norm_num)
theorem material_overlap (a b : ℝ) :
 kplus a*kplus b+kminus a*kminus b=real.cos (a-b) :=
begin
 have hh : real.sqrt 2≠0 := ne_of_gt (real.sqrt_pos.2 (by norm_num)),
 unfold kplus kminus,rw [real.cos_sub],field_simp [hh],
 nlinarith only [root_two_sq,show (real.cos a*real.cos b+real.sin a*real.sin b)*
 ((real.sqrt 2)^2-2)=0, by rw [root_two_sq];ring]
end
theorem material_complete (a : ℝ) : kplus a*kplus a+kminus a*kminus a=1 :=
by rw [material_overlap,sub_self,real.cos_zero]
theorem derivative_norm (c s : ℝ) (hn : c^2+s^2=1) :
 ((c-s)^2+(-s-c)^2)/2=1 := by nlinarith only [hn]
theorem material_no_drift (c s : ℝ) : (c+s)*(c-s)+(c-s)*(-s-c)=0 := by ring
theorem affinity_gap (a b c d : ℝ) (h : a^2+b^2=1) (g : c^2+d^2=1) :
 1-(a*c+b*d)=((a-c)^2+(b-d)^2)/2 := by nlinarith only [h,g]
theorem poisson_partition (a b x y : ℝ) :
 real.exp (-(a*(1-x)+b*(1-y)))=real.exp (-a*(1-x))*real.exp (-b*(1-y)) :=
by rw [←real.exp_add];congr' 1;ring
theorem strict_onset (exposure : ℝ) (h : 0<exposure) : real.exp (-exposure)<1 :=
by rw [←real.exp_zero];exact real.exp_lt_exp.mpr (neg_lt_zero.mpr h)
theorem no_source (b : ℝ) : real.exp (-(0:ℝ)*(1-b))=1 := by simp

theorem width_partition (r s second meanSq : ℝ) :
 r^2*(1-meanSq)=r^2*((1-s)+(s-second)+(second-meanSq)) := by ring
theorem average_posterior (m z b : ℝ) (hp : 1+m≠0) (hm : 1-m≠0) :
 (1+m)/2*(z+b/(1+m))+(1-m)/2*(z-b/(1-m))=z :=
by field_simp [hp,hm];ring
theorem mean_square_narrowing (m b : ℝ) (hp : 1+m≠0) (hm : 1-m≠0) :
 (1+m)/2*(b/(1+m))^2+(1-m)/2*(-b/(1-m))^2=b^2/(1-m^2) :=
begin
 have h : 1-m^2=(1+m)*(1-m) := by ring,
 rw [h],field_simp [hp,hm];ring
end
theorem complex_narrowing (m a b : ℝ) (hp : 1+m≠0) (hm : 1-m≠0) :
 ((1+m)/2*(a/(1+m))^2+(1-m)/2*(-a/(1-m))^2)+
 ((1+m)/2*(b/(1+m))^2+(1-m)/2*(-b/(1-m))^2)=(a^2+b^2)/(1-m^2) :=
by rw [mean_square_narrowing m a hp hm,mean_square_narrowing m b hp hm];ring
theorem parity_width (t : ℝ) :
 1/4-((1+t)/2)*((1-t)/2)=t^2/4 := by ring
theorem triple_width (a b c : ℝ) : ((4:ℝ)/27*a*b*c)^2/4=4/729*(a*b*c)^2 := by ring
theorem triple_phase : (2*(2/6:ℝ)*(2/6)*(2/6))/4=1/54 := by norm_num
theorem mixed_parity : (2:ℝ)^3*(1/54)=4/27 := by norm_num
def gaps : list ℕ → list ℕ
| [] := []
| (a::s) := (s.map (λ b,b-a))++gaps s
def hist (s : list ℕ) := (list.range 18).map (λ k,(gaps s).count k)
theorem homometric_distance_list :
 hist [0,1,4,10,12,17]=hist [0,1,8,11,13,17] := rfl


-- The absence of a direct vertex is an off-shell statement at fixed metric.
theorem no_direct_source {M G B : Type*} (sm : M → G → ℝ) (sb : B → G → ℝ)
 (m m' : M) (b b' : B) (g : G) :
 ((sm m g+sb b g)-(sm m g+sb b' g))-
 ((sm m' g+sb b g)-(sm m' g+sb b' g))=0 := by ring
theorem fixed_metric_factors (a b c d : ℝ) :
 (a*b)*(c*d)=(a*d)*(c*b) := by ring
theorem charge_balance (p k n : ℤ) : (p-n)+(k+n)=p+k := by ring
theorem no_constant_source (g : ℝ) : g-(g+g)/2=0 := by ring
theorem opposite_sources (x y : ℝ) :
 x-(x+y)/2= -(y-(x+y)/2) := by ring
theorem same_class_zero_charge (a b c m : ℝ) (hb : b=a) (hc : c=a) :
 b-(m*b+(1-m)*c)=0 := by rw [hb,hc];ring
theorem whitney_cross (a b p q : ℝ) :
 ((p+q+a*b)-(a+b)^2/4)/48-(p-a^2/4)/48-(q-b^2/4)/48=a*b/96 := by ring
theorem k3_reduction (g : ℝ) : g*(-48)/96= -g/2 := by ring

def radial_field (m d k r : ℝ) := 4*k*d/m^2*(1/r+m/r^2+(4*m^2/3)/r^3)
def radial_slope (m d k r : ℝ) := -(4*k*d/m^2)*(1/r^2+2*m/r^3+4*m^2/r^4)
def radial_flux (m d k r : ℝ) := 32*k*m*d*(1/r^3-1/(2*m)^3)
theorem radial_gradient (m d k r : ℝ) (hr : r≠0) :
 has_deriv_at (radial_field m d k) (radial_slope m d k r) r :=
begin
 have h := ((((has_deriv_at_const r (1:ℝ)).div (has_deriv_at_id r) hr).add
    ((has_deriv_at_const r m).div ((has_deriv_at_id r).pow 2) (pow_ne_zero _ hr))).add
    ((has_deriv_at_const r (4*m^2/3)).div ((has_deriv_at_id r).pow 3) (pow_ne_zero _ hr))).const_mul (4*k*d/m^2),
 convert h using 1,
 simp [radial_slope],
 by_cases hm : m=0,
 { subst m,simp },
 { field_simp [hr,hm];ring }
end
theorem metric_flux (m d k r : ℝ) (hm : m≠0) (hr : r≠0) :
 r^2*(1-2*m/r)*radial_slope m d k r=radial_flux m d k r :=
by unfold radial_slope radial_flux;field_simp [hm,hr];ring
theorem schwarzschild_equation (m d k r : ℝ) (hr : r≠0) :
 has_deriv_at (radial_flux m d k) (-96*k*m*d/r^4) r :=
begin
 have h := (((has_deriv_at_const r (1:ℝ)).div ((has_deriv_at_id r).pow 3)
       (pow_ne_zero _ hr)).sub_const (1/(2*m)^3)).const_mul (32*k*m*d),
 convert h using 1,
 simp,field_simp [hr];ring
end
theorem regular_horizon (m d k : ℝ) (hm : m≠0) :
 radial_flux m d k (2*m)=0 ∧ radial_field m d k (2*m)=4*k*d/m^2*(11/(12*m)) :=
by unfold radial_field radial_flux;split;[simp,field_simp [hm]];ring
theorem odd_mass (m d k r : ℝ) : radial_field m (-d) k r= -radial_field m d k r :=
by unfold radial_field;ring
theorem euler_difference (m d r : ℝ) :
 48*(m+d)^2/r^6-(48*(m+d)^2/r^6+48*(m-d)^2/r^6)/2=96*m*d/r^6 := by ring
theorem mixed_curvature (m d h r : ℝ) :
 96*(m+h)*d/r^6-96*m*d/r^6=96*d*h/r^6 := by ring
theorem blind_common_count (c d : ℝ) : (c*(-d)*(-d))^2=c^2*d^4 := by ring
theorem closed_ordinary_channel (x new : ℝ) (h : x+new^2=x) : new=0 := by nlinarith

theorem relaxed_energy (w g q x : ℝ) (hw : w≠0) :
 w*x^2+2*g*q*x=w*(x+g*q/w)^2-(g*q)^2/w := by field_simp [hw];ring
theorem exchange_energy (w u v : ℝ) :
 -(u+v)^2/w-(-u^2/w)-(-v^2/w)= -2*u*v/w := by ring
theorem coherent_displacement_distance (a c s : ℝ) (h : c^2+s^2=1) :
 ((a*(1-c))^2+(a*s)^2)/2=a^2*(1-c) :=
begin have hh := congr_arg (λ x:ℝ,a^2*x) h,dsimp at hh,nlinarith only [hh] end
theorem spectral_kernel (t w : ℝ) (ht : t≠0) (h : t^2+w^2≠0) :
 t*(1/t-t/(t^2+w^2))=w^2/(t^2+w^2) := by field_simp [ht,h];ring
theorem elementary_area (a b w : ℝ) (hw : w≠0) :
 (∫ u in a..b, w^2/(u^2+w^2))=w*(real.arctan (b/w)-real.arctan (a/w)) :=
begin
 have der : ∀ x:ℝ, has_deriv_at (λ t:ℝ,w*real.arctan (t/w)) (w^2/(x^2+w^2)) x,
 { intro x,have h := (((has_deriv_at_id x).div_const w).arctan).const_mul w,
   convert h using 1;try {ext y};simp,
   have hp : x^2+w^2≠0 := ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero _ hw)),
   have hq : 1+(x/w)^2≠0 := by positivity,
   have hp' : w^2+x^2≠0 := by simpa [add_comm] using hp,
   field_simp [hw,hp,hq]; try {field_simp [hw,hp,hp']};ring },
 have ct : continuous (λ x:ℝ,w^2/(x^2+w^2)) :=
  continuous_const.div (by continuity) (λ x,ne_of_gt
     (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero _ hw))),
 rw [interval_integral.integral_eq_sub_of_has_deriv_at (λ x hx,der x) (ct.interval_integrable a b)],
 ring,all_goals {apply_instance}
end
theorem discrete_spectral_budget {ι : Type*} (s : finset ι) (weights area energy : ι → ℝ)
 (h : ∀ j∈s,area j=real.pi/2*energy j) :
 (∑ j in s,weights j*area j)=real.pi/2*∑ j in s,weights j*energy j :=
begin rw [mul_sum],apply sum_congr rfl,intros j hj,rw [h j hj],ring end
theorem spectral_budget_measure {ι : Type*} [measurable_space ι] (μ : measure ι)
 (strength work : ι → ℝ) (h : ∀ᵐ j ∂μ,strength j=real.pi/2*work j) :
 (∫ j,strength j ∂μ)=real.pi/2*∫ j,work j ∂μ :=
by rw [integral_congr_ae h,integral_mul_left]
theorem passive_budget (m a b : ℝ) (hm : 0≤m) (h : a+b≤1) : a*m+b*m≤m :=
by nlinarith only [mul_nonneg (sub_nonneg.mpr h) hm]
theorem temperature_free_ratio (w g : ℝ) (hw : w≠0) :
 g^2/w^2*(real.pi*w/2)=real.pi/2*(g^2/w) := by field_simp [hw];ring
theorem poisson_single_cell (n v : ℝ) :
 real.exp (-n)*real.exp (n*v)=real.exp (-(n*(1-v))) :=
by rw [←real.exp_add];congr' 1;ring
theorem emission_finiteness (n : ℕ) (c : ℝ) :
 (∑ i in range n,c)=(n:ℝ)*c := by simp
theorem dark_born_counts (i a : ℝ) : (0:ℝ)*i^2=(0:ℝ)*a^2 := by simp


def legendre_two (x : ℝ) := (3*x^2-1)/2
def sphere_second_primitive (x : ℝ) := (9*x^5/5-2*x^3+x)/4
theorem sphere_second_derivative (x : ℝ) :
 has_deriv_at sphere_second_primitive ((legendre_two x)^2) x :=
begin
 have h := ((((((has_deriv_at_id x).pow 5).const_mul 9).div_const 5).sub
              (((has_deriv_at_id x).pow 3).const_mul 2)).add (has_deriv_at_id x)).div_const 4,
 convert h using 1; try {ext y};simp [legendre_two,sphere_second_primitive];ring
end
theorem sphere_legendre_norm :
 (∫ x in (-1:ℝ)..1,(legendre_two x)^2)/2=1/5 :=
begin
 have ct : continuous (λ x:ℝ,(legendre_two x)^2) := by {unfold legendre_two,continuity},
 rw [interval_integral.integral_eq_sub_of_has_deriv_at (λ x hx,sphere_second_derivative x)
      (ct.interval_integrable (-1) 1)],
 norm_num [sphere_second_primitive],all_goals {apply_instance}
end
theorem contrast_curvature (e y : ℝ) : ((1+6*e*y)-(1-6*e*y))/2=6*e*y := by ring
theorem continuum_source (e : ℝ) : 4*(6*e)*(1/5:ℝ)=24*e/5 := by ring
theorem product_euler_charge {ι κ : Type*} (a : finset ι) (b : finset κ) (u : ι → ℝ)
 (v : κ → ℝ) : (∑ i in a, ∑ j in b,u i*v j)=(∑ i in a,u i)*(∑ j in b,v j) :=
by simp_rw [←mul_sum];rw [←sum_mul]
theorem conformal_mode_refinement {l : filter ℕ} (a b : ℕ → ℝ) (x y : ℝ)
 (ha : tendsto a l (𝓝 x)) (hb : tendsto b l (𝓝 y)) :
 tendsto (λ n,a n*b n) l (𝓝 (x*y)) := ha.mul hb
theorem curvature_rescaling (lambda z a : ℝ) (ha : a≠0) (hz : z≠0) :
 (lambda/a)^2/(z/a^2)=lambda^2/z := by field_simp [ha,hz];ring


section spectral_integral
open set
@[reducible] def μp : measure ℝ := volume.restrict (Ioi (0:ℝ))

theorem arctan_infinity : tendsto real.arctan at_top (𝓝 (real.pi/2)) :=
begin
 have inc : strict_mono real.arctan := strict_mono_of_deriv_pos
  (λ x,by rw [(real.has_deriv_at_arctan x).deriv];positivity),
 apply tendsto_order.2,split,
 { intros a ha, let b := max 0 a,
   have hb : b<real.pi/2 := max_lt (by linarith [real.pi_pos]) ha,
   have h0 : -(real.pi/2)<b := lt_of_lt_of_le (by linarith [real.pi_pos]) (le_max_left _ _),
   filter_upwards [eventually_gt_at_top (real.tan b)] with x hx,
   have hb' := inc hx, rw [real.arctan_tan h0 hb] at hb', exact lt_of_le_of_lt (le_max_right 0 a) hb' },
 { intros a ha,exact eventually_of_forall (λ x,(real.arctan_lt_pi_div_two x).trans ha) },all_goals {apply_instance}
end

def unit_laplace_primitive (v t : ℝ) :=
 real.exp (-v*t)*(-1+(v^2*real.cos t-v*real.sin t)/(v^2+1))
theorem unit_laplace_derivative (v t : ℝ) :
 has_deriv_at (unit_laplace_primitive v) (v*real.exp (-v*t)*(1-real.cos t)) t :=
begin
 have h := (((has_deriv_at_id t).const_mul (-v)).exp).mul
  ((has_deriv_at_const t (-1:ℝ)).add ((((real.has_deriv_at_cos t).const_mul (v^2)).sub
    ((real.has_deriv_at_sin t).const_mul v)).div_const (v^2+1))),
 convert h using 1,
 have hp : v^2+1≠0 := by positivity,
 simp,field_simp [hp];ring
end

theorem unit_laplace_decay (v : ℝ) (hv : 0<v) :
 tendsto (unit_laplace_primitive v) at_top (𝓝 0) :=
begin
 have he : tendsto (λ t:ℝ,real.exp (-v*t)) at_top (𝓝 0) := by
  simpa [function.comp,neg_mul] using
   real.tendsto_exp_neg_at_top_nhds_0.comp (tendsto_id.const_mul_at_top' hv),
 let c := 1+(v^2+v)/(v^2+1),
 have hp : 0<v^2+1 := by positivity,
 have bound : ∀ t:ℝ, |(-1+(v^2*real.cos t-v*real.sin t)/(v^2+1))|≤c,
 { intro t,have hc := abs_le.mp (real.abs_cos_le_one t),have hs := abs_le.mp (real.abs_sin_le_one t),
   have high : (v^2*real.cos t-v*real.sin t)/(v^2+1)≤(v^2+v)/(v^2+1) :=
     (div_le_div_right hp).2 (by nlinarith only [mul_nonneg (sq_nonneg v) (sub_nonneg.mpr hc.2),
                                               mul_nonneg hv.le (sub_nonneg.mpr hs.1)]),
   have low : -(v^2+v)/(v^2+1)≤(v^2*real.cos t-v*real.sin t)/(v^2+1) :=
     (div_le_div_right hp).2 (by nlinarith only [mul_nonneg (sq_nonneg v) (sub_nonneg.mpr hc.1),
                                               mul_nonneg hv.le (sub_nonneg.mpr hs.2)]),
   apply abs_le.2,dsimp [c],rw [neg_div] at low,split;linarith },
 rw [tendsto_zero_iff_norm_tendsto_zero],
 change tendsto (λ t:ℝ,|unit_laplace_primitive v t|) at_top (𝓝 0),
 refine @squeeze_zero ℝ (λ t,|unit_laplace_primitive v t|) (λ t,real.exp (-v*t)*c) at_top
    (λ t,abs_nonneg _) _ (by simpa using he.mul_const c),
 intro t,change |real.exp (-v*t)*_|≤_,rw [abs_mul,abs_of_pos (real.exp_pos _)],
 exact mul_le_mul_of_nonneg_left (bound t) (real.exp_pos _).le
end

def laplace_kernel (u t : ℝ) := u*real.exp (-u*t)*(1-real.cos t)
theorem laplace_section (u : ℝ) (hu : 0<u) :
 integrable (laplace_kernel u) μp ∧
 (∫ t,laplace_kernel u t ∂μp)=1/(1+u^2) :=
begin
 have d : ∀ t∈Ici (0:ℝ), has_deriv_at (unit_laplace_primitive u) (laplace_kernel u t) t :=
  λ t ht,unit_laplace_derivative u t,
 have pos : ∀ t∈Ioi (0:ℝ),0≤laplace_kernel u t :=
  λ t ht,mul_nonneg (mul_nonneg hu.le (real.exp_pos _).le) (sub_nonneg.mpr (real.cos_le_one _)),
 have hs := unit_laplace_decay u hu,
 refine ⟨integrable_on_Ioi_deriv_of_nonneg' d pos hs,_⟩,
 unfold μp,rw [integral_Ioi_of_has_deriv_at_of_nonneg' d pos hs],simp [unit_laplace_primitive],
 have hp : 1+u^2≠0 := by positivity,have hq : u^2+1≠0 := by positivity,
 field_simp [hp,hq];ring
end

theorem first_laplace_moment (t : ℝ) (ht : 0<t) :
 (∫ u, u*real.exp (-t*u) ∂μp)=1/t^2 :=
begin
 let f : ℝ → ℝ := λ u,-(t*u+1)*real.exp (-t*u)/t^2,
 have d : ∀ u∈Ici (0:ℝ),has_deriv_at f (u*real.exp (-t*u)) u,
 { intros u hu,have h := (((((has_deriv_at_id u).const_mul t).add_const 1).neg.mul
                 (((has_deriv_at_id u).const_mul (-t)).exp)).div_const (t^2)),
   convert h using 1,simp,field_simp [ht.ne'];ring },
 have zero := real.tendsto_exp_neg_at_top_nhds_0.comp (tendsto_id.const_mul_at_top' ht),
 have one := (real.tendsto_pow_mul_exp_neg_at_top_nhds_0 1).comp (tendsto_id.const_mul_at_top' ht),
 have lim : tendsto f at_top (𝓝 0),
 { convert (((one.add zero).neg).div_const (t^2)) using 1,
   { ext x,dsimp [f,function.comp],simp only [pow_one,←neg_mul];ring },
   { simp } },
 unfold μp,rw [integral_Ioi_of_has_deriv_at_of_nonneg' d (λ x hx,mul_nonneg (le_of_lt hx) (real.exp_pos _).le) lim],
 simp [f],field_simp [ht.ne'];ring
end

theorem unit_dirichlet_area :
 (∫ t,(1-real.cos t)/t^2 ∂μp)=real.pi/2 :=
begin
 letI : sigma_finite μp := by {unfold μp,apply_instance},
 have good : ∀ᵐ x:ℝ ∂μp,0<x := ae_restrict_mem measurable_set_Ioi,
 have dp : ∀ x∈Ici (0:ℝ),has_deriv_at real.arctan (1/(1+x^2)) x :=
  λ x hx, real.has_deriv_at_arctan x,
 have dn : ∀ x∈Ioi (0:ℝ),0≤(1:ℝ)/(1+x^2) := λ x hx, by positivity,
 have hi := integrable_on_Ioi_deriv_of_nonneg' dp dn arctan_infinity,
 have area := integral_Ioi_of_has_deriv_at_of_nonneg' dp dn arctan_infinity,
 have hprod : integrable (function.uncurry laplace_kernel) (μp.prod μp),
 { have ct : ae_strongly_measurable (function.uncurry laplace_kernel) (μp.prod μp) :=
    (show continuous (function.uncurry laplace_kernel),
            by {unfold function.uncurry laplace_kernel,continuity}).ae_strongly_measurable,
   refine (integrable_prod_iff ct).2 ⟨_,_⟩,
     { filter_upwards [good] with x hx,exact (laplace_section x hx).1 },
     { apply hi.congr,filter_upwards [good] with x hx,
       have eqn := (laplace_section x hx).2,rw [←eqn],apply integral_congr_ae,
       exact eventually_of_forall (λ y,(real.norm_of_nonneg (mul_nonneg (mul_nonneg hx.le
         (real.exp_pos _).le) (sub_nonneg.mpr (real.cos_le_one y)))).symm) } },
 have first : ∀ᵐ t:ℝ ∂μp,(∫ u,laplace_kernel u t ∂μp)=(1-real.cos t)/t^2,
 { filter_upwards [good] with t ht,
   unfold laplace_kernel,rw [integral_mul_right],
   have e : (λ u:ℝ,u*real.exp (-u*t))=(λ u:ℝ,u*real.exp (-t*u)) :=
    funext (λ u,by rw [neg_mul,neg_mul,mul_comm u t]),
   rw [e,first_laplace_moment t ht],ring },
 rw [←integral_congr_ae first,←integral_integral_swap hprod],
 have second : ∀ᵐ u:ℝ ∂μp,(∫ t,laplace_kernel u t ∂μp)=1/(1+u^2) :=
  good.mono (λ u hu,(laplace_section u hu).2),
 rw [integral_congr_ae second],simpa using area
end

theorem oscillator_area (w : ℝ) (hw : 0<w) :
 (∫ t, (1-real.cos (w*t))/t^2 ∂μp)=real.pi*w/2 :=
begin
 have h := integral_comp_mul_left_Ioi (λ x:ℝ,(1-real.cos x)/x^2) 0 hw,
 simp only [mul_zero] at h,
 have eqn : (λ t:ℝ,(1-real.cos (w*t))/t^2)=
       (λ t:ℝ,w^2*((1-real.cos (w*t))/(w*t)^2)) :=
  funext (λ t,by {rw [mul_pow],by_cases ht:t=0,{simp [ht]},{field_simp [ht,hw.ne'];ring}}),
 rw [eqn,integral_mul_left],unfold μp,rw [h],
 change w^2*(|w⁻¹| • (∫ t,(1-real.cos t)/t^2 ∂μp))=_,rw [abs_of_pos (inv_pos.mpr hw)],rw [unit_dirichlet_area,smul_eq_mul],field_simp [hw.ne'];ring
end
end spectral_integral


section conditional_measure
open set
theorem spectral_information_bound (D G E : ℝ → ℝ) (μ : measure ℝ)
 (id : integrable D μ) (ig : integrable G μ)
 (accessible : ∀ᵐ t ∂μ, G t≤D t)
 (work : (∫ t,D t ∂μ)=real.pi/2*(∫ w,E w)) :
 (∫ t,G t ∂μ)≤real.pi/2*(∫ w,E w) :=
by rw [←work];exact integral_mono_ae ig id accessible

-- Actual finite-mode work integral; no fitted Dirichlet integral is assumed.
theorem finite_pulse_integral {ι : Type*} (s : finset ι) (g w : ι → ℝ)
 (pos : ∀ i∈s,0<w i)
 (finite : ∀ i∈s,integrable (λ t:ℝ,(g i)^2/(w i)^2*((1-real.cos (w i*t))/t^2)) μp) :
 (∫ t, ∑ i in s,(g i)^2/(w i)^2*((1-real.cos (w i*t))/t^2) ∂μp)=
 real.pi/2*∑ i in s,(g i)^2/w i :=
begin
 rw [integral_finset_sum s finite,mul_sum], apply sum_congr rfl,intros i hi,
 rw [integral_mul_left,oscillator_area _ (pos i hi)],
 field_simp [(pos i hi).ne'];ring
end
theorem poisson_complete_exposure (n v : ℝ) :
 (∑' k:ℕ, real.exp (-n)*((n*v)^k/(nat.factorial k:ℝ)))=
 real.exp (-(n*(1-v))) :=
begin
 rw [tsum_mul_left,←poisson_single_cell],
 congr' 1,rw [real.exp_eq_exp_ℝ],exact (exp_series_div_has_sum_exp ℝ (n*v)).tsum_eq
end
theorem gram_dark_mode (a b : ℝ) : (a*b+b*(-a))^2=0 := by ring
theorem two_amplitudes_gram (a b c d : ℝ) :
 (a^2+c^2)*(b^2+d^2)-(a*b+c*d)^2=(a*d-b*c)^2 := by ring
end conditional_measure


section cosine_bounds
-- R_i are successive zero-based antiderivatives of 1-cos. Their signs give
-- global Taylor brackets, including at wave numbers beyond a Taylor radius.
def rem0 (x : ℝ) := 1-real.cos x
def rem1 (x : ℝ) := x-real.sin x
theorem rem0_nonneg (x : ℝ) (hx : 0≤x) : 0≤rem0 x := sub_nonneg.mpr (real.cos_le_one x)
theorem rem1_deriv (x : ℝ) : has_deriv_at rem1 (rem0 x) x :=
 (has_deriv_at_id x).sub (real.has_deriv_at_sin x)
theorem primitive_positive (f g : ℝ → ℝ) (d : ∀ x,has_deriv_at f (g x) x)
 (h0 : f 0=0) (hg : ∀ x,0≤x→0≤g x) (x : ℝ) (hx : 0≤x) : 0≤f x :=
begin
 have df : differentiable ℝ f := λ t,(d t).differentiable_at,
 have m := (convex_Ici (0:ℝ)).monotone_on_of_deriv_nonneg df.continuous.continuous_on
   df.differentiable_on (λ t ht,by {rw [(d t).deriv],exact hg t (interior_subset ht)}),
 have step := m (show (0:ℝ)∈set.Ici (0:ℝ), from le_rfl) hx hx,simpa [h0] using step
end
theorem rem1_nonneg (x : ℝ) (hx : 0≤x) : 0≤rem1 x :=
 primitive_positive _ _ rem1_deriv (by simp [rem1]) rem0_nonneg x hx

def rem2 (x : ℝ) := x^2/2-rem0 x
theorem rem2_deriv (x : ℝ) : has_deriv_at rem2 (rem1 x) x :=
begin
 have h := (((has_deriv_at_id x).pow 2).div_const 2).sub ((has_deriv_at_const x (1:ℝ)).sub (real.has_deriv_at_cos x)),
 convert h using 1,simp [rem1];ring
end
theorem rem2_nonneg (x : ℝ) (hx : 0≤x) : 0≤rem2 x :=
 primitive_positive _ _ rem2_deriv (by norm_num [rem2,rem0]) rem1_nonneg x hx

def rem3 (x : ℝ) := x^3/6-rem1 x
theorem rem3_deriv (x : ℝ) : has_deriv_at rem3 (rem2 x) x :=
begin
 have h := (((has_deriv_at_id x).pow 3).div_const 6).sub (rem1_deriv x),
 convert h using 1,simp [rem2];ring
end
theorem rem3_nonneg (x : ℝ) (hx : 0≤x) : 0≤rem3 x :=
 primitive_positive _ _ rem3_deriv (by norm_num [rem3,rem1]) rem2_nonneg x hx

def rem4 (x : ℝ) := x^4/24-rem2 x
theorem rem4_deriv (x : ℝ) : has_deriv_at rem4 (rem3 x) x :=
begin
 have h := (((has_deriv_at_id x).pow 4).div_const 24).sub (rem2_deriv x),
 convert h using 1,simp [rem3];ring
end
theorem rem4_nonneg (x : ℝ) (hx : 0≤x) : 0≤rem4 x :=
 primitive_positive _ _ rem4_deriv (by norm_num [rem4,rem2,rem0]) rem3_nonneg x hx

def rem5 (x : ℝ) := x^5/120-rem3 x
theorem rem5_deriv (x : ℝ) : has_deriv_at rem5 (rem4 x) x :=
begin
 have h := (((has_deriv_at_id x).pow 5).div_const 120).sub (rem3_deriv x),
 convert h using 1,simp [rem4];ring
end
theorem rem5_nonneg (x : ℝ) (hx : 0≤x) : 0≤rem5 x :=
 primitive_positive _ _ rem5_deriv (by norm_num [rem5,rem3,rem1]) rem4_nonneg x hx

def rem6 (x : ℝ) := x^6/720-rem4 x
theorem rem6_deriv (x : ℝ) : has_deriv_at rem6 (rem5 x) x :=
begin
 have h := (((has_deriv_at_id x).pow 6).div_const 720).sub (rem4_deriv x),
 convert h using 1,simp [rem5];ring
end
theorem rem6_nonneg (x : ℝ) (hx : 0≤x) : 0≤rem6 x :=
 primitive_positive _ _ rem6_deriv (by norm_num [rem6,rem4,rem2,rem0]) rem5_nonneg x hx

def rem7 (x : ℝ) := x^7/5040-rem5 x
theorem rem7_deriv (x : ℝ) : has_deriv_at rem7 (rem6 x) x :=
begin
 have h := (((has_deriv_at_id x).pow 7).div_const 5040).sub (rem5_deriv x),
 convert h using 1,simp [rem6];ring
end
theorem rem7_nonneg (x : ℝ) (hx : 0≤x) : 0≤rem7 x :=
 primitive_positive _ _ rem7_deriv (by norm_num [rem7,rem5,rem3,rem1]) rem6_nonneg x hx

def rem8 (x : ℝ) := x^8/40320-rem6 x
theorem rem8_deriv (x : ℝ) : has_deriv_at rem8 (rem7 x) x :=
begin
 have h := (((has_deriv_at_id x).pow 8).div_const 40320).sub (rem6_deriv x),
 convert h using 1,simp [rem7];ring
end
theorem rem8_nonneg (x : ℝ) (hx : 0≤x) : 0≤rem8 x :=
 primitive_positive _ _ rem8_deriv (by norm_num [rem8,rem6,rem4,rem2,rem0]) rem7_nonneg x hx

theorem cosine_brackets (t : ℝ) (ht : 0≤t) :
 t^2/2-t^4/24≤1-real.cos t ∧ 1-real.cos t≤t^2/2-t^4/24+t^6/720 :=
begin
 have a := rem4_nonneg t ht, have b := rem6_nonneg t ht,
 unfold rem6 rem4 rem2 rem0 at *,split;linarith
end
theorem eighth_remainder (t : ℝ) :
 rem8 t=1-t^2/2+t^4/24-t^6/720+t^8/40320-real.cos t :=
by unfold rem8 rem6 rem4 rem2 rem0;ring
end cosine_bounds


section moment_kernel
open set
def weighted (n : ℕ) (t : ℝ) (g : ℝ → ℝ) :=
 ∫ x in (0:ℝ)..1, (1-x)^n*g (t*x)

theorem lower_power (n : ℕ) (t : ℝ) (f g : ℝ → ℝ)
 (der : ∀ x,has_deriv_at f (g x) x) (cg : continuous g) (zero : f 0=0) :
 t*weighted (n+1) t g=((n:ℝ)+1)*weighted n t f :=
begin
 have cf : continuous f := continuous_iff_continuous_at.2 (λ x,(der x).continuous_at),
 let u : ℝ → ℝ := λ x,(1-x)^(n+1)*f (t*x),
 have d : ∀ x:ℝ,has_deriv_at u
     (t*((1-x)^(n+1)*g (t*x))-((n:ℝ)+1)*((1-x)^n*f (t*x))) x,
 { intro x,have h := ((((has_deriv_at_const x (1:ℝ)).sub (has_deriv_at_id x)).pow (n+1))).mul
      ((der (t*x)).comp x ((has_deriv_at_id x).const_mul t)),
   convert h using 1,simp;ring },
 have c1 : continuous (λ x:ℝ,t*((1-x)^(n+1)*g (t*x))) := by continuity,
 have c2 : continuous (λ x:ℝ,((n:ℝ)+1)*((1-x)^n*f (t*x))) := by continuity,
 have h := interval_integral.integral_eq_sub_of_has_deriv_at (λ x hx,d x)
                 ((c1.sub c2).interval_integrable (0:ℝ) 1),
 rw [interval_integral.integral_sub (c1.interval_integrable _ _) (c2.interval_integrable _ _),
     interval_integral.integral_const_mul,interval_integral.integral_const_mul] at h,
 simp [u,zero] at h,unfold weighted,linarith only [h],all_goals {apply_instance}
end
theorem zero_power (t : ℝ) (f g : ℝ → ℝ) (der : ∀ x,has_deriv_at f (g x) x)
 (cg : continuous g) (zero : f 0=0) : t*weighted 0 t g=f t :=
begin
 have d : ∀ x:ℝ,has_deriv_at (λ y:ℝ,f(t*y)) (t*g (t*x)) x :=
   λ x,by {convert (der (t*x)).comp x ((has_deriv_at_id x).const_mul t) using 1,simp;ring},
 have ct : continuous (λ x:ℝ,t*g (t*x)) := by continuity,
 have h := interval_integral.integral_eq_sub_of_has_deriv_at (λ x hx,d x) (ct.interval_integrable (0:ℝ) 1),
 rw [interval_integral.integral_const_mul] at h,unfold weighted,simp [zero] at *,exact h,
 all_goals {apply_instance}
end
lemma rem0_cont : continuous rem0 := continuous_const.sub real.continuous_cos
lemma rem0_at_zero : rem0 0=0 := by norm_num [rem0]
lemma rem1_cont : continuous rem1 := continuous_iff_continuous_at.2 (λ x,(rem1_deriv x).continuous_at)
lemma rem1_at_zero : rem1 0=0 := by norm_num [rem1]
lemma rem2_cont : continuous rem2 := continuous_iff_continuous_at.2 (λ x,(rem2_deriv x).continuous_at)
lemma rem2_at_zero : rem2 0=0 := by norm_num [rem2,rem0]
lemma rem3_cont : continuous rem3 := continuous_iff_continuous_at.2 (λ x,(rem3_deriv x).continuous_at)
lemma rem3_at_zero : rem3 0=0 := by norm_num [rem3,rem1]
lemma rem4_cont : continuous rem4 := continuous_iff_continuous_at.2 (λ x,(rem4_deriv x).continuous_at)
lemma rem4_at_zero : rem4 0=0 := by norm_num [rem4,rem2,rem0]
lemma rem5_cont : continuous rem5 := continuous_iff_continuous_at.2 (λ x,(rem5_deriv x).continuous_at)
lemma rem5_at_zero : rem5 0=0 := by norm_num [rem5,rem3,rem1]
lemma rem6_cont : continuous rem6 := continuous_iff_continuous_at.2 (λ x,(rem6_deriv x).continuous_at)
lemma rem6_at_zero : rem6 0=0 := by norm_num [rem6,rem4,rem2,rem0]
lemma rem7_cont : continuous rem7 := continuous_iff_continuous_at.2 (λ x,(rem7_deriv x).continuous_at)
lemma rem7_at_zero : rem7 0=0 := by norm_num [rem7,rem5,rem3,rem1]
lemma rem8_cont : continuous rem8 := continuous_iff_continuous_at.2 (λ x,(rem8_deriv x).continuous_at)
lemma rem8_at_zero : rem8 0=0 := by norm_num [rem8,rem6,rem4,rem2,rem0]
theorem remainder7_kernel (t : ℝ) : t^7*weighted 6 t rem0=720*rem7 t :=
begin
 have h6 := lower_power 5 t _ _ rem1_deriv rem0_cont rem1_at_zero,
 have h5 := lower_power 4 t _ _ rem2_deriv rem1_cont rem2_at_zero,
 have h4 := lower_power 3 t _ _ rem3_deriv rem2_cont rem3_at_zero,
 have h3 := lower_power 2 t _ _ rem4_deriv rem3_cont rem4_at_zero,
 have h2 := lower_power 1 t _ _ rem5_deriv rem4_cont rem5_at_zero,
 have h1 := lower_power 0 t _ _ rem6_deriv rem5_cont rem6_at_zero,
 have h0 := zero_power t _ _ rem7_deriv rem6_cont rem7_at_zero,
 norm_num at h1 h2 h3 h4 h5 h6,
 linear_combination 1*t^6*h6+6*t^5*h5+30*t^4*h4+120*t^3*h3+360*t^2*h2+720*t^1*h1+720*t^0*h0
end
theorem remainder8_kernel (t : ℝ) : t^8*weighted 7 t rem0=5040*rem8 t :=
begin
 have h7 := lower_power 6 t _ _ rem1_deriv rem0_cont rem1_at_zero,
 have h6 := lower_power 5 t _ _ rem2_deriv rem1_cont rem2_at_zero,
 have h5 := lower_power 4 t _ _ rem3_deriv rem2_cont rem3_at_zero,
 have h4 := lower_power 3 t _ _ rem4_deriv rem3_cont rem4_at_zero,
 have h3 := lower_power 2 t _ _ rem5_deriv rem4_cont rem5_at_zero,
 have h2 := lower_power 1 t _ _ rem6_deriv rem5_cont rem6_at_zero,
 have h1 := lower_power 0 t _ _ rem7_deriv rem6_cont rem7_at_zero,
 have h0 := zero_power t _ _ rem8_deriv rem7_cont rem8_at_zero,
 norm_num at h1 h2 h3 h4 h5 h6 h7,
 linear_combination 1*t^7*h7+7*t^6*h6+42*t^5*h5+210*t^4*h4+840*t^3*h3+2520*t^2*h2+5040*t^1*h1+5040*t^0*h0
end

def weighted_kernel (n : ℕ) (s t : ℝ) := (1-s)^n*((1-real.cos (s*t))/t^2)

lemma weighted_beta (n : ℕ) : (∫ x in (0:ℝ)..1,(1-x)^n*x)=1/(((n:ℝ)+1)*((n:ℝ)+2)) :=
begin
 let f : ℝ → ℝ := λ x,-((1-x)^(n+1))/((n:ℝ)+1)+(1-x)^(n+2)/((n:ℝ)+2),
 have d : ∀ x:ℝ,has_deriv_at f ((1-x)^n*x) x,
 { intro x,have dx := (has_deriv_at_const x (1:ℝ)).sub (has_deriv_at_id x),
   have h := (((dx.pow (n+1)).neg).div_const ((n:ℝ)+1)).add ((dx.pow (n+2)).div_const ((n:ℝ)+2)),
   convert h using 1,
   have h1 : ((n:ℝ)+1)≠0 := by positivity,have h2 : ((n:ℝ)+2)≠0 := by positivity,
   simp [pow_succ],field_simp [h1,h2];ring },
 have ct : continuous (λ x:ℝ,(1-x)^n*x) := by continuity,
 rw [interval_integral.integral_eq_sub_of_has_deriv_at (λ x hx,d x) (ct.interval_integrable (0:ℝ) 1)],
 have h1 : ((n:ℝ)+1)≠0 := by positivity,have h2 : ((n:ℝ)+2)≠0 := by positivity,
 simp [f,pow_succ],field_simp [h1,h2];ring,all_goals {apply_instance}
end

theorem weighted_kernel_integral (n : ℕ) :
 (∫ t,(∫ s in (0:ℝ)..1,weighted_kernel n s t) ∂μp)=
       real.pi/2/(((n:ℝ)+1)*((n:ℝ)+2)) :=
begin
 let ν : measure ℝ := volume.restrict (Ioc (0:ℝ) 1),
 letI : sigma_finite μp := by {unfold μp,apply_instance},
 letI : sigma_finite ν := by {dsimp [ν],apply_instance},
 have good : ∀ᵐ s:ℝ ∂ν,s∈Ioc (0:ℝ) 1 := ae_restrict_mem measurable_set_Ioc,
 have inn : ∀ s∈Ioc (0:ℝ) 1,(∫ t,weighted_kernel n s t ∂μp)=(real.pi/2)*((1-s)^n*s),
 { intros s hs,unfold weighted_kernel,rw [integral_mul_left,oscillator_area s hs.1],ring },
 have innI : ∀ s∈Ioc (0:ℝ) 1, integrable (weighted_kernel n s) μp,
 { intros s hs,apply integrable.const_mul,
   by_contra h,have z := integral_undef h,rw [oscillator_area s hs.1] at z,
   exact (ne_of_gt (div_pos (mul_pos real.pi_pos hs.1) (by norm_num : (0:ℝ)<2))) z },
 have integral_signed : ∀ s∈Ioc (0:ℝ) 1,(∫ t,‖weighted_kernel n s t‖ ∂μp)=(real.pi/2)*((1-s)^n*s),
 { intros s hs,rw [←inn s hs],apply integral_congr_ae,refine eventually_of_forall (λ t,_),
   apply real.norm_of_nonneg, exact mul_nonneg (pow_nonneg (sub_nonneg.mpr hs.2) _)
     (div_nonneg (sub_nonneg.mpr (real.cos_le_one _)) (sq_nonneg _)) },
 have ct : continuous (λ s:ℝ,real.pi/2*((1-s)^n*s)) := by continuity,
 have ip : integrable (function.uncurry (weighted_kernel n)) (ν.prod μp),
 { have ms : measurable (function.uncurry (weighted_kernel n)) :=
   by {unfold function.uncurry weighted_kernel,measurability},
   refine (integrable_prod_iff ms.ae_strongly_measurable).2 ⟨good.mono innI,_⟩,
   have h := (ct.interval_integrable (0:ℝ) 1).1,
   exact h.congr (good.mono (λ s hs,(integral_signed s hs).symm)),all_goals {apply_instance} },
 simp_rw [interval_integral.integral_of_le (zero_le_one: (0:ℝ)≤1)],
 change (∫ t,(∫ s,weighted_kernel n s t ∂ν) ∂μp)=_,
 rw [←integral_integral_swap ip,integral_congr_ae (good.mono inn),integral_mul_left],
 have hh := weighted_beta n,rw [interval_integral.integral_of_le (zero_le_one:(0:ℝ)≤1)] at hh,
 dsimp [ν],rw [hh],ring
end
theorem moment_kernel7 : (∫ t, rem7 t/t^9 ∂μp)=real.pi/(2*40320) :=
begin
 have good : ∀ᵐ t:ℝ ∂μp,0<t := ae_restrict_mem measurable_set_Ioi,
 have point : ∀ᵐ t:ℝ ∂μp,rem7 t/t^9=(1/720:ℝ)*(∫ s in (0:ℝ)..1,weighted_kernel 6 s t),
 { filter_upwards [good] with t ht,
   have convert_k : (λ s:ℝ,weighted_kernel 6 s t)=(λ s:ℝ,((1-s)^6*rem0 (t*s))/t^2) :=
     funext (λ s,by {unfold weighted_kernel rem0,rw [mul_comm s t],ring}),
   rw [convert_k,interval_integral.integral_div],have eqn := remainder7_kernel t,unfold weighted at eqn,
   field_simp [ht.ne'];linear_combination -t^2*eqn },
 rw [integral_congr_ae point,integral_mul_left,weighted_kernel_integral],norm_num;ring
end
theorem moment_kernel8 : (∫ t, rem8 t/t^10 ∂μp)=real.pi/(2*362880) :=
begin
 have good : ∀ᵐ t:ℝ ∂μp,0<t := ae_restrict_mem measurable_set_Ioi,
 have point : ∀ᵐ t:ℝ ∂μp,rem8 t/t^10=(1/5040:ℝ)*(∫ s in (0:ℝ)..1,weighted_kernel 7 s t),
 { filter_upwards [good] with t ht,
   have convert_k : (λ s:ℝ,weighted_kernel 7 s t)=(λ s:ℝ,((1-s)^7*rem0 (t*s))/t^2) :=
     funext (λ s,by {unfold weighted_kernel rem0,rw [mul_comm s t],ring}),
   rw [convert_k,interval_integral.integral_div],have eqn := remainder8_kernel t,unfold weighted at eqn,
   field_simp [ht.ne'];linear_combination -t^2*eqn },
 rw [integral_congr_ae point,integral_mul_left,weighted_kernel_integral],norm_num;ring
end
end moment_kernel


theorem null_emission (e f c : ℝ) (he : 0<e) (hf : 0<f) (h : 2*e*f*(1-c)=0) :
 c=1 ∧ (2*e*f*(1-c))^2=0 :=
begin have hp : 2*e*f≠0 := by positivity,
 have hc := (mul_eq_zero.mp h).resolve_left hp,split;[linarith only [hc],simp [h]] end
theorem weak_curvature_projector (c d : ℝ) :
 (c+d)^2-((c+d)^2+(c-d)^2)/2=2*c*d := by ring


-- Source physics enters through the projected survival tail. The singular
-- Fourier coefficient below follows for any measurable tail with this limit.
theorem bfss_survival_fourier (S : ℝ → ℝ) (sm : measurable S) (K : ℝ)
 (sp : ∀ x,0<x→0≤S x) (bound : ∀ x,0<x→x^9*S x≤K)
 (tail : tendsto (λ x:ℝ,x^9*S x) at_top (𝓝 (105/4:ℝ))) :
 tendsto (λ r:ℝ,∫ u,rem7 u*(r^9*S (u*r)) ∂μp) at_top (𝓝 (real.pi/3072)) :=
begin
 have good : ∀ᵐ u:ℝ ∂μp,0<u := ae_restrict_mem measurable_set_Ioi,
 have ui : integrable (λ u:ℝ,rem7 u/u^9) μp,
 { by_contra h,have a:=integral_undef h,rw [moment_kernel7] at a,
   exact (ne_of_gt (div_pos real.pi_pos (by norm_num : (0:ℝ)<2*40320))) a },
 have hm : ∀ r:ℝ,measurable (λ u:ℝ,rem7 u*(r^9*S (u*r))) :=
   λ r, rem7_cont.measurable.mul (measurable_const.mul (sm.comp (measurable_id.mul_const r))),
 have domination : ∀ᶠ r:ℝ in at_top,∀ᵐ u:ℝ ∂μp,
   ‖rem7 u*(r^9*S (u*r))‖≤K*(rem7 u/u^9),
 { filter_upwards [eventually_gt_at_top (0:ℝ)] with r hr,filter_upwards [good] with u hu,
   have b := bound (u*r) (mul_pos hu hr),rw [mul_pow] at b,
   have t : r^9*S (u*r)≤K/u^9 := (le_div_iff (pow_pos hu 9)).2 (by nlinarith only [b]),
   rw [real.norm_of_nonneg (mul_nonneg (rem7_nonneg u hu.le) (mul_nonneg (pow_pos hr 9).le
        (sp _ (mul_pos hu hr))))],
   calc rem7 u*(r^9*S (u*r)) ≤ rem7 u*(K/u^9) : mul_le_mul_of_nonneg_left t (rem7_nonneg u hu.le)
   ... = _ : by ring },
 have limit : ∀ᵐ u:ℝ ∂μp,tendsto (λ r:ℝ,r^9*S (u*r)) at_top (𝓝 ((105/4:ℝ)/u^9)),
 { filter_upwards [good] with u hu,
   have h := (tail.comp (tendsto_id.const_mul_at_top' hu)).div_const (u^9),
   convert h using 1,ext r,dsimp [function.comp],rw [mul_pow],field_simp [hu.ne'];ring },
 have ans := integrate_tail_limit μp (λ r u:ℝ,r^9*S (u*r)) rem7
    (λ u:ℝ,K*(rem7 u/u^9)) (105/4) (eventually_of_forall (λ r,(hm r).ae_strongly_measurable))
    domination (ui.const_mul K) limit,
 rw [moment_kernel7] at ans,convert ans using 1;congr' 1;ring
end


-- A loss probability in a centered gravitational channel obstructs exact
-- cancellation in the coherent metric supported on the layer complement.
theorem layer_port_amplitude {E : Type*} [add_comm_group E] [module ℝ E]
 (e d : E) (c s : ℝ) :
 s • (c • e)-c • (s • d)=(s*c) • (e-d) :=
by rw [smul_smul,smul_smul,smul_sub,mul_comm c s]

theorem port_probability (w : ℝ) (hw : 0≤w) (hq : w≤1) :
 (real.sqrt w*real.sqrt (1-w))^2=w*(1-w) :=
by rw [mul_pow,real.sq_sqrt hw,real.sq_sqrt (sub_nonneg.mpr hq)]

theorem layer_feedback_bound {E : Type*} [normed_add_comm_group E]
 (e d : E) (w p : ℝ) (hw : 0≤w) (hq : w≤1) (hp : 0≤p)
 (ordinary : ‖e‖=1) (passive : ‖d‖^2+p≤1) :
 w*(1-w)*(1-real.sqrt (1-p))^2 ≤ w*(1-w)*‖e-d‖^2 :=
begin
 have hsq : ‖d‖^2≤1-p := by linarith,
 have hs : 0≤1-p := le_trans (sq_nonneg _) hsq,
 have hd : ‖d‖≤real.sqrt (1-p) :=
  by nlinarith only [hsq,real.sq_sqrt hs,real.sqrt_nonneg (1-p),norm_nonneg d],
 have h1 : real.sqrt (1-p)≤1 :=
  by nlinarith only [real.sq_sqrt hs,hp,real.sqrt_nonneg (1-p)],
 have hl := norm_sub_norm_le e d,
 rw [ordinary] at hl,
 have hdiff : 1-real.sqrt (1-p)≤‖e-d‖ := by linarith,
 apply mul_le_mul_of_nonneg_left _ (mul_nonneg hw (sub_nonneg.mpr hq)),
 nlinarith only [mul_nonneg (sub_nonneg.mpr hdiff)
        (add_nonneg (norm_nonneg (e-d)) (sub_nonneg.mpr h1))]
end

theorem hidden_channel_strict (p : ℝ) (hp : 0<p) (hq : p≤1) :
 0<1-real.sqrt (1-p) :=
begin have h := real.sq_sqrt (sub_nonneg.mpr hq),
 nlinarith only [h,hp,real.sqrt_nonneg (1-p)] end

theorem axial_deformed_entry (x l : ℝ) :
 (1-2*x)*(l*x^2-6*x^3)+(1-2*x)*(-x^2+4*x^3)-((1-2*x)*x)^2=
 (1-2*x)*(l-2)*x^2 := by ring

theorem axial_deformed_determinant (f x l a k : ℝ) (hk : k^2=l*(l-2)) :
 (f*(l-2)*x^2)*(f*(l*x^2+2*x^3+a^2*l*x^8))-(f*a*k*x^5)^2=
 f^2*(l-2)*x^2*(l*x^2+2*x^3) :=
by have h:=congr_arg (λ z:ℝ,f^2*a^2*x^10*z) hk;dsimp at h;nlinarith only [h]

theorem axial_positive_energy (a b c u v : ℝ) (ha : 0<a) (hdet : 0≤a*b-c^2) :
 0≤a*u^2+2*c*u*v+b*v^2 :=
begin
 have h:=add_nonneg (sq_nonneg (a*u+c*v)) (mul_nonneg hdet (sq_nonneg v)),
 have prod : 0≤a*(a*u^2+2*c*u*v+b*v^2) := by nlinarith only [h],
 exact nonneg_of_mul_nonneg_right prod ha
end

-- The common and contrast input have the same single-packet occupations.
theorem one_quantum_contrast (x y : ℝ) :
 (x^2+y^2-2*x*y)/2=(x-y)^2/2 := by ring
theorem matter_exchange_selection (i f : ℝ) (t : ℝ) (hi : i^2=1) (hf : f^2=1) :
 (t+i*f*t)^2+(t-i*f*t)^2=4*t^2 :=
begin
 have h : (i*f)^2=1 := by rw [mul_pow,hi,hf,mul_one],
 calc (t+i*f*t)^2+(t-i*f*t)^2=2*t^2+2*t^2*(i*f)^2 : by ring
 ... = _ : by rw [h];ring
end


-- Local Noether balances for the real and imaginary parts separately.
-- u,v are the fields; t,h are time derivatives, x,y the radial derivatives.
theorem radial_energy_exchange (u v t h x y ut vt ux vx tx hx a b c : ℝ)
 (hu : ut=ux-a*u-c*v) (hv : vt=vx-b*v-c*u) :
 (t*ut+x*tx+a*u*t-(tx*x+t*ux) = -c*v*t) ∧
 (h*vt+y*hx+b*v*h-(hx*y+h*vx) = -c*u*h) ∧
 ((-c*v*t)+(-c*u*h)+c*(t*v+u*h)=0) :=
begin rw [hu,hv],split,{ring},split;ring end

theorem radial_momentum_exchange (u v t h x y ut vt ux vx tx hx a b c ap bp cp : ℝ)
 (hu : ut=ux-a*u-c*v) (hv : vt=vx-b*v-c*u) :
 -(ut*x+t*tx+vt*y+h*hx)+(t*tx+h*hx+x*ux+y*vx)
 -(a*u*x+b*v*y+c*(x*v+u*y))-(ap*u^2+bp*v^2+2*cp*u*v)/2
 = -(ap*u^2+bp*v^2+2*cp*u*v)/2 :=
by rw [hu,hv];ring


theorem common_after_layer_mark (w chi : ℝ) :
 w*(1-w)+(1-w)*w-2*w*(1-w)*chi=2*w*(1-w)*(1-chi) := by ring

theorem protected_common_mark (w chi p : ℝ) (hw : 0<w) (hq : w<1) (hp : 0<p)
 (h : 2*w*(1-w)*(1-chi)*p=0) : chi=1 :=
begin
 have hne : 2*w*(1-w)*p≠0 := ne_of_gt
 (mul_pos (mul_pos (mul_pos (by norm_num) hw) (sub_pos.mpr hq)) hp),
 have h' : 2*w*(1-w)*p*(1-chi)=0 := by nlinarith only [h],
 have := (mul_eq_zero.mp h').resolve_left hne,linarith
end


theorem normalized_feedback_floor (w p : ℝ) (hw : 0≤w) (hq : w≤1)
 (hp : 0≤p) (hr : p≤1) :
 w*(1-w)*p^2/4 ≤ w*(1-w)*(1-real.sqrt (1-p))^2 :=
begin
 have hs:=real.sq_sqrt (sub_nonneg.mpr hr),
 have hl : p/2 ≤ 1-real.sqrt (1-p) :=
  by nlinarith only [hs,sq_nonneg (1-real.sqrt (1-p))],
 have nn : 0≤p/2 := by linarith,
 have hsq : (p/2)^2≤(1-real.sqrt (1-p))^2 :=
  pow_le_pow_of_le_left nn hl 2,
 calc w*(1-w)*p^2/4 = w*(1-w)*(p/2)^2 : by ring
 ... ≤ _ : mul_le_mul_of_nonneg_left hsq (mul_nonneg hw (sub_nonneg.mpr hq))
end


-- Comparisons in the gravitational principal symbol and direct contact action.
theorem angular_characteristic_polynomial (t x : ℝ) :
 (1-t)*(1+x^2-t)-x^2=t^2-(2+x^2)*t+1 := by ring

theorem angular_speed_pair (u v t : ℝ) (h : u^2=1+v^2) :
 (t-(u+v)^2)*(t-(u-v)^2)=t^2-(2+4*v^2)*t+1 :=
begin
 have ht : (u+v)^2+(u-v)^2=2+4*v^2 := by nlinarith only [h],
 have hp : (u+v)*(u-v)=1 := by nlinarith only [h],
 calc (t-(u+v)^2)*(t-(u-v)^2)
     =t^2-((u+v)^2+(u-v)^2)*t+((u+v)*(u-v))^2 : by ring
 ... = _ : by rw [ht,hp];ring
end
theorem faster_characteristic (u v : ℝ) (hu : 0≤u) (hv : 0<v) (h : u^2=1+v^2) :
 1<u+v ∧ 0<u-v ∧ u-v<1 :=
begin
 have one : 1≤u := by nlinarith only [h,hu,sq_nonneg v],
 have hi : 1<u+v := by linarith,
 have pos : 0<u-v := by nlinarith only [h,hu,hv],
 have prod : (u+v)*(u-v)=1 := by nlinarith only [h],
 have hh:=mul_lt_mul_of_pos_right hi pos,
 rw [one_mul,prod] at hh,exact ⟨hi,pos,hh⟩
end

theorem direct_weyl_starts_quartic (s x y : ℝ) :
 ((s*x)^2-(s*y)^2)^2=s^4*(x^2-y^2)^2 := by ring
theorem direct_magnitude_energy (k s d : ℝ) :
 k*((s+d)^2-(s-d)^2)^2/8=2*k*s^2*d^2 := by ring
theorem direct_magnitude_sign (s : ℝ) : (s^2-(-s)^2)^2=0 := by ring
theorem positive_sigma_kinetic (f m d : ℝ) (hf : 0<f) :
 0<1/f+3*m^2/2*(d/f)^2 :=
add_pos_of_pos_of_nonneg (div_pos zero_lt_one hf) (by positivity)
theorem scalarized_hessian (ms g l s : ℝ) :
 (2*(l+2*ms*g^2)*s^2)*ms-(-2*ms*g*s)^2=2*ms*l*s^2 := by ring
theorem mediated_curvature_seed (s d g : ℝ) :
 g*((s+d)^2-(s-d)^2)/2=2*g*s*d := by ring
theorem matter_weak_vacuum (xi m : ℝ) (hm : m≠0) :
 1+xi*0^2/m^2=1 ∧ xi*(0:ℝ)=0 := by norm_num
theorem exterior_log_flux (c x : ℝ) (hx : x≠0) (hf : 1-2*c/x≠0) :
 has_deriv_at (λ r:ℝ, real.log (1-2*c/r)) (2*c/(x^2*(1-2*c/x))) x :=
begin
 have h := ((has_deriv_at_const x (1:ℝ)).sub
   ((has_deriv_at_const x (2*c)).div (has_deriv_at_id x) hx)).log hf,
 convert h using 1,
 simp [div_mul_eq_div_div, neg_div]
end
theorem stellar_surface_match (c y : ℝ) (hy : y≠0) :
 (2*c/y)*y=2*c := by field_simp [hy]
theorem first_newtonian_mode :
 real.cos (real.pi/2)=0 ∧ (real.pi/2)^2/6=real.pi^2/24 :=
⟨real.cos_pi_div_two, by ring⟩

theorem contact_rate (q y : ℝ) :
 (((q-y)^2-(-q-y)^2)^2)/2=8*q^2*y^2 := by ring
theorem additive_rate (q y : ℝ) : ((q-y)-(-q-y))^2/2=2*q^2 := by ring
theorem equal_curvature_moments (s : ℝ) (hs : s^2=2) :
 (s/4+(-s)/4=0) ∧ (s^2/4+(-s)^2/4=1) :=
begin split,{ring},nlinarith only [hs] end
theorem eliminated_contact_rate (u : ℝ) :
 (1+real.exp (-(2*u)))/2-real.exp (-u)=(1-real.exp (-u))^2/2 :=
begin rw [show -(2*u)=-u+-u, by ring, real.exp_add],ring end
theorem contact_half_retention : (1+(1/2:ℝ)^2)/2=5/8 := by norm_num

theorem absence_of_earlier_mode (k : ℝ) (hk : 0<k) (hc : k<real.pi/2) :
 0<real.cos k :=
real.cos_pos_of_mem_Ioo ⟨by linarith [real.pi_pos],hc⟩

-- Two distances to distinct anchors fix a spectral column up to one orientation.
theorem equal_gap_columns {T : Type*} (p q : T → ℝ) (o e : T)
 (hne : p e - p o ≠ 0)
 (h : ∀ i j, (q i-q j)^2=(p i-p j)^2) :
 (∀ i, q i-q o=p i-p o) ∨ (∀ i, q i-q o= -(p i-p o)) :=
begin
 have hz : ((q e-q o)-(p e-p o))*((q e-q o)+(p e-p o))=0 :=
   by nlinarith only [h e o],
 rcases mul_eq_zero.mp hz with hs | hs,
 { left,intro i,
   have hr : q e=q o+(p e-p o) := by linarith only [hs],
   have h2 := h i e,rw [hr] at h2,
   have hz : (p e-p o)*((q i-q o)-(p i-p o))=0 :=
     by nlinarith only [h2,h i o],
   exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hne) },
 { right,intro i,
   have hr : q e=q o-(p e-p o) := by linarith only [hs],
   have h2 := h i e,rw [hr] at h2,
   have hz : (p e-p o)*((q i-q o)+(p i-p o))=0 :=
     by nlinarith only [h2,h i o],
   have hh := (mul_eq_zero.mp hz).resolve_left hne,
   linarith only [hh] }
end

theorem constant_gap_column {T : Type*} (p q : T → ℝ) (o : T)
 (hp : ∀ i,p i=p o) (h : ∀ i,(q i-q o)^2=(p i-p o)^2) :
 ∀ i,q i=q o :=
begin intro i,have hg:=h i,rw [hp i,sub_self,zero_pow (by norm_num : 0<2)] at hg,
 nlinarith only [hg] end

theorem equal_gap_suffices (s a b t : ℝ) (hs : s^2=1) :
 ((s*a+t)-(s*b+t))^2=(a-b)^2 :=
by rw [show (s*a+t)-(s*b+t)=s*(a-b), by ring,mul_pow,hs,one_mul]

theorem paired_phase_gap (z t : ℝ) :
 (real.cos z-real.cos t)^2+(real.sin z-real.sin t)^2 =
 2*(1-real.cos (z-t)) :=
by rw [real.cos_sub]; nlinarith only [real.sin_sq_add_cos_sq z, real.sin_sq_add_cos_sq t]

theorem phase_gap_partner_cancels (k x w y : ℝ) :
 (real.cos (k*(x-y))-real.cos (k*(w-y)))^2+
 (real.sin (k*(x-y))-real.sin (k*(w-y)))^2 = 2*(1-real.cos (k*(x-w))) :=
by rw [paired_phase_gap,show k*(x-y)-k*(w-y)=k*(x-w), by ring]

-- Hessian of the explicitly normalized pair potential at a zero probe amplitude.
theorem probe_direct_potential (k x s : ℝ) :
 k*(x^2-s^2)^2/8=k*s^4/8-k*s^2*x^2/4+k*x^4/8 := by ring

theorem probe_partner_curvature (m xi r k s : ℝ) :
 4*((m^2-xi*r)/4-k*s^2/4)=m^2-xi*r-k*s^2 := by ring

theorem partner_shift_negative (top bottom : ℝ) (ht : 0<top) (hb : 0<bottom) :
 -(top/bottom)<0 := neg_lt_zero.mpr (div_pos ht hb)

-- The derivative of the energy contains the varying mode twice and the explicit load.
-- The weak eigen-equation on that mode variation cancels its contribution.
theorem ritz_slope_identity (a b : ℝ → ℝ) (e d v n lam : ℝ)
 (hn : b e ≠ 0) (ha : has_deriv_at a (2*v-n) e) (hb : has_deriv_at b (2*d) e)
 (hr : a e=lam*b e) (hw : v=lam*d) :
 has_deriv_at (λ t,a t/b t) (-(n/b e)) e :=
begin
 have calc_der := ha.div hb hn,
 convert calc_der using 1,rw [hr,hw],field_simp [hn],ring
end

-- A marginal on the left sums the diagonal partner blocks of the joint state.
theorem marginal_dephasing_iff {T : Type*} [fintype T] (weights : T → ℝ) (c : ℝ) :
 (∀ block : T → ℝ, (∑ i,weights i*block i)=c*(∑ i,block i)) ↔
 (∀ i, weights i=c) :=
begin
 classical,split,
 { intros h j,have hh := h (λ i, if i=j then 1 else 0),
   have hs : finset.filter (λ x : T,x=j) finset.univ={j} := by ext i;simp,
   simpa [mul_ite,hs] using hh },
 { intros h b,simp_rw [h],rw [finset.mul_sum] }
end

theorem homogeneous_probe_stability (m k v : ℝ) :
 (∀ p : ℝ, 0≤p^2+m^2-2*k*v) ↔ 2*k*v≤m^2 :=
begin split,{intro h,have h0:=h 0,norm_num at h0,linarith},
 intros h p, nlinarith only [h,sq_nonneg p] end

theorem zero_mass_vacuum (k v : ℝ) (hk : 0<k) (hv : 0≤v)
 (h : 2*k*v≤(0:ℝ)^2) : v=0 :=
begin have hp : 0<2*k := mul_pos (by norm_num) hk,
 by_contra hn,have hpos := mul_pos hp (lt_of_le_of_ne hv (ne.symm hn)),
 nlinarith only [hpos,h] end

-- Each component of a simultaneous contact is a covector density in common readings.
theorem displacement_ibp (q dq e de val dv d src : ℝ) :
 -(dq*e+q*de)*val-d*src*e =
 (q*dv-d*src)*e-(dq*e*val+q*de*val+q*e*dv) := by ring

theorem integrated_displacement {s : ℝ → ℝ} (u v : ℝ) (g : ℝ → ℝ)
 (h : ∀ x ∈ set.uIcc u v, has_deriv_at s (g x) x)
 (hin : interval_integrable g volume u v) (bound : s v=s u) :
 (∫ x in u..v, g x)=0 :=
begin rw [interval_integral.integral_eq_sub_of_has_deriv_at h hin,bound,sub_self] end

theorem sum_exchange_covectors {T : Type*} [fintype T] (q force : T → ℝ) :
 (∑ i, (q i*(∑ j,force j)-(∑ j,q j)*force i))=0 :=
begin rw [sum_sub_distrib,←sum_mul,←mul_sum,sub_self] end

theorem direct_equal_volume_constraint (k a b da db : ℝ)
 (hk : k≠0) (hd : a^2-b^2≠0)
 (no_carrier : (k/2*(a^2-b^2)*(a*da-b*db))/2-k/2*(a^2-b^2)*a*da=0) :
 a*da+b*db=0 :=
begin
 have hz : (k*(a^2-b^2))*(a*da+b*db)=0 :=
   calc (k*(a^2-b^2))*(a*da+b*db)
     = (-4)*((k/2*(a^2-b^2)*(a*da-b*db))/2-k/2*(a^2-b^2)*a*da) : by ring
   ... = 0 : by rw [no_carrier,mul_zero],
 exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero hk hd)
end

theorem empty_probe_partner_force (q k b db : ℝ) (hq : q≠0) (hk : k≠0) (hb : b≠0)
 (fixed_maps : q*(k/2*b^3*db)=0) : db=0 :=
begin
 have hz : (q*k*b^3)*db=0 := by nlinarith only [fixed_maps],
 exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (mul_ne_zero hq hk) (pow_ne_zero 3 hb))
end

theorem reference_stress_balance (q dv d src grad e : ℝ)
 (reference_eom : e=q*dv-d*src) :
 ((d*src-q*dv)*grad)+e*grad=0 := by rw [reference_eom];ring


-- A continuum of occupied layers, living clocks, and the ordinary material receiver.
theorem live_variance (p s : ℝ) :
 (1-p)*(0-p*s^2)^2+p*(s^2-p*s^2)^2=p*(1-p)*s^4 := by ring

theorem complementary_energy (p k s : ℝ) :
 k/2*p*(1-p)*s^4=k/2*(1-p)*(1-(1-p))*s^4 := by ring

theorem active_force_difference (p k s : ℝ) :
 2*k*s*(s^2-p*s^2)-2*k*s*(s^2-(1-p)*s^2)=2*k*s^3*(1-2*p) := by ring

theorem clock_charge_conservation {I : Type*} [fintype I] (q d e : I → ℝ) (v : ℝ)
 (hv : (∑ i,q i)*v=∑ i,d i) (he : ∀ i,e i= -q i*v+d i) :
 ∑ i,e i=0 :=
begin simp_rw [he],rw [sum_add_distrib,←sum_mul,sum_neg_distrib,neg_mul,hv,neg_add_self] end

theorem live_energy_continuity (v u l force slope : ℝ) (hu : u≠0) :
 v*(-l*force)+u*(-slope+l*force*v/u)+u*slope=0 := by field_simp [hu];ring

theorem live_constraint_preserved (f fd fdd h hd w ed : ℝ)
 (energy : ed= -3*h*w+3*fd*(hd+2*h^2))
 (gravity : 2*f*hd+w+fdd-h*fd=0) :
 3*fd*h^2+6*f*h*hd+3*hd*fd+3*h*fdd-ed=0 :=
begin rw [energy],calc
  3*fd*h^2+6*f*h*hd+3*hd*fd+3*h*fdd-(-3*h*w+3*fd*(hd+2*h^2))
    =3*h*(2*f*hd+w+fdd-h*fd) : by ring
  ... = 0 : by rw [gravity,mul_zero]
end

theorem screened_force (f fp force dv dh : ℝ) (hf : 0<f)
 (scalar : dv= -force+3*fp*dh) (gravity : -2*f*dh=fp*dv) :
 dv= -(2*f/(2*f+3*fp^2))*force :=
begin
 have hn : 2*f+3*fp^2≠0 := ne_of_gt (by nlinarith only [hf,sq_nonneg fp]),
 field_simp [hn],
 have h1 := congr_arg (λ t:ℝ,2*f*t) scalar,
 have h2 := congr_arg (λ t:ℝ,3*fp*t) gravity,
 dsimp at h1 h2,nlinarith only [h1,h2]
end

theorem live_potential_second (k p s chi : ℝ) :
 2*k*p*(1-p)*s^3*(-chi*(2*k*s^3*(1-2*p))) =
 -4*chi*k^2*p*(1-p)*(1-2*p)*s^6 := by ring

theorem recoil_curvature_second (m r force u clock : ℝ)
 (trace : m*r=4*force-2*u*clock) (recoil : u*clock= -force) :
 m*r=6*force := by linarith only [trace,recoil]

theorem two_curvature_preparations (a : ℝ) :
 81*(a*(1/3)*(1-1/3)*(1-2/3)) =
 64*(a*(1/4)*(1-1/4)*(1-2/4)) := by ring

theorem active_fourth_power_jet (s v : ℝ → ℝ) (t a : ℝ)
 (hs : has_deriv_at s (v t) t) (hv : has_deriv_at v a t) (rest : v t=0) :
 has_deriv_at (λ z, 4*s z^3*v z) (4*s t^3*a) t :=
begin have d := (((hs.pow 3).const_mul 4).mul hv),
 simpa only [rest,mul_zero,zero_mul,zero_add] using d end

theorem flat_null_sphere (h r : ℝ) (hr : 0<r) (hh : h < -(1/r)) :
 2*(h+1/r)<0 ∧ 2*(h-1/r)<0 :=
by have hp:=div_pos zero_lt_one hr;split;linarith

theorem flat_slice_constraints (r f b y yp hr ht src : ℝ)
 (hy : y=ht^2) (ham : f*(ht^2+2*hr*ht)=src)
 (momentum : 2*ht*(b*hr-ht)=r*yp) :
 f*(r*yp+(2+b)*y)=b*src :=
begin rw [←momentum,hy,←ham],ring end

theorem flat_slice_integrating_factor (r f root fp b y yp src : ℝ)
 (hn : root≠0) (hf : root^2=f) (hb : 2*f*b=2*f+r*fp)
 (ode : f*(r*yp+(2+b)*y)=b*src) :
 2*root*(3*r^2*root*y+r^3*(fp/(2*root))*y+r^3*root*yp)=2*r^2*b*src :=
begin
 have h1:=congr_arg (λ z:ℝ,2*r^2*z) ode,
 have h2:=congr_arg (λ z:ℝ,r^2*y*z) hb,
 dsimp at h1 h2,
 calc 2*root*(3*r^2*root*y+r^3*(fp/(2*root))*y+r^3*root*yp)
   =6*r^2*root^2*y+r^3*fp*y+2*r^3*root^2*yp : by field_simp [hn];ring
 ... =2*r^2*b*src : by rw [hf];nlinarith only [h1,h2]
end

theorem tidal_integrated_jet (r t : ℝ) :
 (r/12)*(t^3/3)/2=r*t^3/72 := by ring

theorem radial_gamma_area (n : ℕ) :
 (∫ x in set.Ioi (0:ℝ), real.exp (-x)*x^n)=(n.factorial:ℝ) :=
begin
 have hg := real.Gamma_eq_integral (show 0<(n:ℝ)+1, by positivity),
 rw [real.Gamma_nat_eq_factorial,add_sub_cancel] at hg,
 simpa only [real.rpow_nat_cast] using hg.symm
end

theorem ground_radial_variance :
 (nat.factorial 6:ℝ)/2^5-((nat.factorial 4:ℝ)/2^3)^2=27/2 :=
by norm_num [nat.factorial]

theorem radial_excited_matrix (r : ℝ) (hs : r^2=2) (hn : r≠0) :
 (2*24/(3/2:ℝ)^5-120/(3/2:ℝ)^6)/r= -512*r/243 :=
by field_simp [hn]; nlinarith only [hs]

theorem two_s_share (r : ℝ) (hs : r^2=2) :
 (-512*r/243)^2/(27/2)=1048576/1594323 :=
by field_simp; nlinarith only [hs]

theorem all_channel_coefficient (m a r t : ℝ) :
 (m*r*t^3/72)^2*(27*a^4/2)=m^2*r^2*t^6*a^4/384 := by ring

-- The signed amplitude of a physical overlap and both failure probabilities are nonnegative.
theorem mean_failure_ge_overlap (s u v : ℝ) (hu : 0≤u) (hv : 0≤v)
 (h : s^2≤u*v) : s≤(u+v)/2 :=
begin
 have pos : 0≤(u+v)/2 := by linarith,
 have identity : ((u+v)/2)^2=u*v+(u-v)^2/4 := by ring,
 have sq : s^2≤((u+v)/2)^2 := by rw [identity];linarith only [h,sq_nonneg (u-v)],
 by_contra bad,have hp := mul_pos (sub_pos.mpr (lt_of_not_ge bad)) 
   (show 0<s+(u+v)/2, by linarith only [pos,lt_of_not_ge bad]),
 have hi : s^2-((u+v)/2)^2 = (s-(u+v)/2)*(s+(u+v)/2) := by ring,
 linarith only [sq,hp,hi]
end

theorem fidelity_first_nonzero (s : ℝ) (hn : 1+s≠0) :
 1-s=(1-s^2)/(1+s) := by field_simp [hn];ring

theorem circle_packet_normalization (len quart norm k : ℝ) (hl : len≠0) :
 k/2*((len^2*quart)/len-(len*norm/len)^2)
 = (k*len)*quart/2-k*norm^2/2 := by field_simp [hl];ring

theorem disjoint_mixed_contact (k a b c d : ℝ) :
 4*((k/2)*(a+b-(c+d)^2)-(k/2)*(a-c^2)-(k/2)*(b-d^2))= -4*k*c*d := by ring

theorem circle_localized_vertex (g length : ℝ) (hl : length≠0) :
 (-4*(g/length))*length = -4*g := by field_simp [hl]

theorem packet_strength_floor (w moment k : ℝ) (hw : 0<w) (hk : 0≤k)
 (h : 0≤w^2*moment-w) :
 12*k*(1/w-1)≤12*k*(moment-1) :=
begin refine mul_le_mul_of_nonneg_left _ (show (0:ℝ)≤12*k, by linarith),
 have h' : w*(w*moment-1)≥0 := by nlinarith only [h],
 have value:=nonneg_of_mul_nonneg_right h' hw,
 have lower : 1/w≤moment := (div_le_iff hw).2 (by nlinarith only [value]),
 linarith only [lower]
end

theorem normalized_matrix_shape : (∫ t in (-1:ℝ)..1,(1-t^2)^2)=16/15 :=
begin
 let prim : ℝ → ℝ := λ t,t-2*t^3/3+t^5/5,
 have hd : ∀ t,has_deriv_at prim ((1-t^2)^2) t :=
 λ t,by { have d := ((has_deriv_at_id t).sub ((((has_deriv_at_id t).pow 3).const_mul 2).div_const 3)).add
       (((has_deriv_at_id t).pow 5).div_const 5),convert d using 1,norm_num [id,prim];ring },
 have hi : continuous (λ t:ℝ,(1-t^2)^2) := by continuity,
 rw [interval_integral.integral_eq_sub_of_has_deriv_at (λ t ht,hd t) (hi.interval_integrable _ _)],
 norm_num [prim]
end


theorem shell_mass_match (small large norm : ℝ) (hn : norm≠0) :
 small+(large-small)/norm*norm=large := by field_simp [hn];ring

theorem posterior_width_one (d f : ℝ) (hd : d^2=1-f^2) :
 ((1+d)/2)*(1-(1+d)/2)=f^2/4 :=
 calc ((1+d)/2)*(1-(1+d)/2)=(1-d^2)/4 : by ring
 ... = f^2/4 : by rw [hd];ring

theorem captured_width_step (eta f v : ℝ) :
 (1-eta)*v+eta*(f^2*v)=(1-eta+eta*f^2)*v := by ring

theorem packet_variance_source {T : Type*} [measurable_space T] (μ : measure T)
 (g : T → ℝ) (w : ℝ)
 (hg : integrable g μ) (h2 : integrable (λ x,g x^2) μ)
 (hc : integrable (λ _ : T,(1:ℝ)) μ)
 (mass : (∫ x,g x ∂μ)=1) (size : (∫ x:T,(1:ℝ) ∂μ)=w) :
 0≤w^2*(∫ x,g x^2 ∂μ)-w :=
begin
 have eqp : (λ x:T,(w*g x-1)^2)=(λ x,w^2*g x^2-(2*w)*g x+1) := funext (λ x,by ring),
 have pos : 0≤∫ x,(w*g x-1)^2 ∂μ := integral_nonneg (λ x,sq_nonneg _),
 have hs : integrable (λ x:T,w^2*g x^2-(2*w)*g x) μ := (h2.const_mul (w^2)).sub (hg.const_mul (2*w)),
 have h2m : integrable (λ x:T,w^2*g x^2) μ := h2.const_mul _,
 have hgm : integrable (λ x:T,(2*w)*g x) μ := hg.const_mul _,
 rw [eqp,integral_add hs hc,integral_sub h2m hgm,
     integral_mul_left,integral_mul_left,mass,size] at pos,
 linarith only [pos]
end

theorem linear_rate_excluded_at_time (a c t : ℝ) (ht : 0<t) (h : c*t^5<a) :
 ¬ a*t≤c*t^6 :=
begin have hh:=mul_lt_mul_of_pos_right h ht,
 have eqn : c*t^5*t=c*t^6 := by ring,linarith only [hh,eqn] end

-- p and q label eigenvalues of the same swap on the ket and bra.
theorem single_dark_symbol (a b : ℝ) (dark : a+b=0) : (a-b)^2=4*b^2 :=
by rw [show a= -b, by linarith only [dark]];ring

theorem scattering_parity_block (d e p q : ℝ) :
 (d+e*p)*(d+e*q)-((d+e*p)^2+(d+e*q)^2)/2= -e^2*(p-q)^2/2 := by ring

theorem shifted_parity_block (e p q : ℝ) :
 (e*(1-p))*(e*(1-q))-((e*(1-p))^2+(e*(1-q))^2)/2= -e^2*(p-q)^2/2 := by ring

theorem elastic_total_energy_swap (a b : ℝ) : a+b=b+a := add_comm _ _

theorem mixed_click_calibration (ab aa bb : ℝ) :
 2*((1-ab)/2)-(1-aa)/2-(1-bb)/2=(aa+bb-2*ab)/2 := by ring

theorem finite_exposure_effects (c b : ℝ) (hc : c^2+b^2=1) :
 c^2+b^2=1 ∧ (1:ℝ)*c+0*b=c := by simp [hc]

theorem dark_hemisphere_integral :
 (∫ x in (0:ℝ)..(1/2),(1-x)⁻¹^2)=1 :=
begin
 let f : ℝ → ℝ := λ x,(1-x)⁻¹,
 have nozero : ∀ (x:ℝ), x ∈ set.uIcc (0:ℝ) (1/2) → 1-x≠0 :=
 λ x hx,by { rw [set.uIcc_of_le (by norm_num : (0:ℝ)≤1/2)] at hx,linarith [hx.2] },
 have d : ∀ x ∈ set.uIcc (0:ℝ) (1/2),has_deriv_at f ((1-x)⁻¹^2) x :=
 λ x hx,by { have h:=((has_deriv_at_id x).const_sub 1).inv (nozero x hx),
   convert h using 1,dsimp [id],rw [inv_pow],field_simp [nozero x hx] },
 have hi : continuous_on (λ x:ℝ,(1-x)⁻¹^2) (set.uIcc 0 (1/2)) :=
 ((continuous_const.sub continuous_id).continuous_on.inv₀ nozero).pow 2,
 rw [interval_integral.integral_eq_sub_of_has_deriv_at d (hi.interval_integrable)],
 norm_num [f]
end

theorem born_exchange_fraction (x a : ℝ) (hx : x≠0) (hu : 1-x≠0) :
 (a/x)*(a/(1-x))=a*(a/x+a/(1-x)) := by { field_simp [hx,hu]; try { ring }; simp }

theorem angular_difference_rationalized (a x e s : ℝ) (hs : s^2=1-2*e*x*(1-x))
 (hx : x≠0) (hu : 1-x≠0) (hp : 1+s≠0) :
 ((a/(x*(1-x)))*(1-s))^2/2=2*a^2*e^2/(1+s)^2 :=
begin
 have fact : (1-s)*(1+s)=2*e*x*(1-x) := by nlinarith only [hs],
 have eqn : (a/(x*(1-x)))*(1-s)=2*a*e/(1+s) :=
 by { field_simp [hx,hu,hp],
      linear_combination a*fact },
 rw [eqn],field_simp [hp],ring
end

theorem gravity_record_powers (b t : ℝ) : (b*t^6)^2=b^2*t^12 := by ring


-- Algebraic identities also apply to bounded operators on an infinite-dimensional space.
theorem swap_involution_from_projection {R : Type*} [ring R] (p : R) (hp : p*p=p) :
 (1-(p+p))*(1-(p+p))=1 :=
by { simp only [sub_mul,mul_sub,add_mul,mul_add,mul_one,one_mul,hp]; abel }

theorem dark_generator_operator {R : Type*} [ring R] (p r : R) :
 (1-(p+p))*r*(1-(p+p))-r =
 (p*r*p+p*r*p+p*r*p+p*r*p)-(p*r+p*r+r*p+r*p) :=
by { simp only [sub_mul,mul_sub,add_mul,mul_add,mul_one,one_mul]; abel }

theorem nondemolition_spectral_effect {R : Type*} [ring R] (p h : R)
 (hp : p*p=p) (comm : p*h=h*p) :
 p*h*p+(1-p)*h*(1-p)=h :=
begin
 have ph : p*h*p=h*p := by rw [comm,mul_assoc,hp],
 have hp2 : h*p*p=h*p := by rw [mul_assoc,hp],
 simp only [sub_mul,mul_sub,mul_one,one_mul,ph,comm,hp2],abel
end

-- Absolute entries of a positive effect obey this two-by-two minor inequality.
theorem faithful_silent_effect {T : Type*} [fintype T] (w diag : T → ℝ) (amp : T → T → ℝ)
 (hw : ∀ i,0<w i) (hd : ∀ i,0≤diag i)
 (minor : ∀ i j,amp i j^2≤diag i*diag j)
 (silent : (∑ i,w i*diag i)=0) : ∀ i j,amp i j=0 :=
begin
 classical,
 have all : ∀ i,diag i=0 := λ i,by {
   have h : w i*diag i≤∑ j,w j*diag j :=
    single_le_sum (λ j hj,mul_nonneg (hw j).le (hd j)) (mem_univ i),
   rw [silent] at h,
   by_contra hn, exact (not_lt_of_ge h) (mul_pos (hw i) (lt_of_le_of_ne (hd i) (ne.symm hn))) },
 intros i j,have h := minor i j,rw [all i,zero_mul] at h,
 by_contra hn,exact (not_lt_of_ge h) (sq_pos_of_ne_zero (amp i j) hn)
end


theorem longitudinal_green_normalization :
 (∫ x in (0:ℝ)..real.pi,real.sin x^6)=5*real.pi/16 :=
begin
 have h:=integral_sin_pow_even 3,
 norm_num [finset.prod_range_succ] at h,
 convert h using 1;ring
end

theorem reduced_green_constant :
 (3/(2*real.pi^5))*(5*real.pi/16)=15/(32*real.pi^4) :=
by field_simp [real.pi_ne_zero];ring

theorem finite_line_derivative (f : ℝ → ℝ) (d r m : ℝ) (hr : r≠0)
 (hf : has_deriv_at f m (d/r)) :
 has_deriv_at (λ x:ℝ,f (d/x)/x^7) (-(7*f (d/r)+(d/r)*m)/r^8) r :=
begin
 have hq := (has_deriv_at_const r d).div (has_deriv_at_id r) hr,
 have h := (hf.comp r hq).div ((has_deriv_at_id r).pow 7) (pow_ne_zero 7 hr),
 convert h using 1,dsimp [id],field_simp [hr],ring
end

theorem finite_line_integral_lower (f : ℝ → ℝ) (q : ℝ) (hq : 0<q)
 (hc : continuous_on f (set.Icc 0 q))
 (hm : strict_anti_on f (set.Icc 0 q)) :
 q*f q<(∫ x in (0:ℝ)..q,f x) :=
begin
 have h0 : (0:ℝ)∈set.Icc 0 q:=⟨le_rfl,hq.le⟩,
 have h1 : q∈set.Icc 0 q:=⟨hq.le,le_rfl⟩,
 have h : (∫ x in (0:ℝ)..q,f q)<(∫ x in (0:ℝ)..q,f x) :=
 begin
  apply interval_integral.integral_lt_integral_of_continuous_on_of_le_of_exists_lt hq continuous_on_const hc,
  { intros x hx,exact hm.antitone_on ⟨hx.1.le,hx.2⟩ h1 hx.2 },
  { exact ⟨0,h0,hm h0 h1 hq⟩ }
 end,
 simpa [interval_integral.integral_const] using h
end

theorem finite_line_log_bounds (mass edge : ℝ) (he : 0<edge) (hm : edge<mass) :
 7 < 7+edge/mass ∧ 7+edge/mass<8 :=
begin
 have hp : 0<mass := lt_trans he hm,
 have l := div_pos he hp,have u : edge/mass<1 := (div_lt_one hp).2 hm,
 split;linarith
end


-- A Duhamel source with a quadratic onset gives a cubic vector amplitude, with norm control.
theorem tidal_banach_remainder {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
 [complete_space E] (source : ℝ → E) (v : E) (t eta : ℝ) (ht : 0≤t) (he : 0≤eta)
 (hi : interval_integrable source volume 0 t)
 (modulus : ∀ x ∈ set.Icc (0:ℝ) t, ‖source x-x^2 • v‖≤eta*x^2) :
 ‖(∫ x in (0:ℝ)..t,source x)-(t^3/3) • v‖≤eta*t^3 :=
begin
 have hc : continuous (λ x:ℝ,x^2 • v) := (continuous_id.pow 2).smul continuous_const,
 have hpoly : (∫ x in (0:ℝ)..t,x^2)=t^3/3 := by rw [integral_pow];norm_num,
 rw [←hpoly,←interval_integral.integral_smul_const,
     ←interval_integral.integral_sub hi (hc.interval_integrable _ _)],
 have hb : ∀ x ∈ set.uIoc (0:ℝ) t, ‖source x-x^2 • v‖≤eta*t^2 := λ x hx,by {
    rw [set.uIoc_of_le ht] at hx,
    exact le_trans (modulus x ⟨hx.1.le,hx.2⟩)
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left hx.1.le hx.2 2) he) },
 calc ‖(∫ x in (0:ℝ)..t,source x-x^2 • v)‖ ≤ (eta*t^2)*abs (t-0) :
    interval_integral.norm_integral_le_of_norm_le_const hb
 ... = eta*t^3 : by rw [sub_zero,abs_of_nonneg ht];ring
end

theorem orbital_area_uniform (e h s : ℝ) (he : 0≤e) (hh : 0≤h) (hu : h≤1/4)
 (hs : 0≤s) (square : s^2=1-2*e*h) :
 0≤2/(1+s)^2-1/2 ∧ 2/(1+s)^2-1/2≤e :=
begin
 have fac : (1-s)*(1+s)=2*e*h := by nlinarith only [square],
 have eh : 0≤2*e*h := mul_nonneg (by linarith only [he]) hh,
 have plus : 0<1+s := by linarith only [hs],
 have product : 0≤(1-s)*(1+s) := by rw [fac];exact eh,
 have ds : 0≤1-s := nonneg_of_mul_nonneg_left product plus,
 have diff : 1-s≤e/2 := by {
   have a:=mul_nonneg ds hs,
   have b:=mul_le_mul_of_nonneg_left hu (show 0≤2*e, by linarith only [he]),
   nlinarith only [fac,a,b] },
 have den : 0<(1+s)^2 := pow_pos plus 2,
 have dd : 1≤(1+s)^2 := by nlinarith only [hs,sq_nonneg s],
 have eprod:=mul_le_mul_of_nonneg_left dd he,
 have identity : 4-(1+s)^2=(1-s)*(3+s) := by ring,
 have num:=mul_le_mul_of_nonneg_left (show 3+s≤4,by linarith only [ds]) ds,
 have low:=mul_nonneg ds (show 0≤3+s,by linarith only [hs]),
 split,
 { have rr : (1:ℝ)/2≤2/(1+s)^2 := (le_div_iff den).2 (by nlinarith only [identity,low]),
   linarith only [rr] },
 { have rr : 2/(1+s)^2≤e+1/2 := (div_le_iff den).2 (by nlinarith only [num,identity,diff,eprod]),
   linarith only [rr] }
end

-- Radiation outside a material contact and the work of a direct gravitational contrast.
theorem mediated_square (s z g b x : ℝ) (hp : s+z≠0) :
 (s+z)*b^2/2+g*b*x =
 (s+z)*(b+g*x/(s+z))^2/2-g^2*x^2/(2*(s+z)) :=
by field_simp [hp];ring

theorem work_resolvent_step (s a b p : ℝ) (ha : s+a≠0) (hb : s+b≠0)
 (hd : b-a≠0) (hp : p≠0) :
 (1/((s+b)*p)-1/((s+a)*p))/(b-a)= -(1/((s+a)*(s+b)*p)) :=
by field_simp [ha,hb,hd,hp];ring

theorem work_affine_drop (c k a b : ℝ) (hn : b-a≠0) :
 ((c+k*b)-(c+k*a))/(b-a)=k := by field_simp [hn];ring

theorem work_moment_recovery (s x y t : ℝ) :
 (s+y)*t-y*t=s*t ∧
 (s+x)*(s+y)*t-(x+y)*((s+y)*t-y*t)-x*y*t=s^2*t :=
by split;ring

theorem work_variance_integral (μ : measure ℝ) [is_finite_measure μ] (m : ℝ)
 (h₁ : integrable (λ x : ℝ,x) μ) (h₂ : integrable (λ x : ℝ,x^2) μ) :
 (∫ x,(x-m)^2 ∂μ)=(∫ x : ℝ,x^2 ∂μ)-2*m*(∫ x : ℝ,x ∂μ)+
                     m^2*(∫ x : ℝ,(1:ℝ) ∂μ) :=
begin
 have h₀ : integrable (λ x : ℝ,(1:ℝ)) μ := integrable_const _,
 have hp : ∀ x : ℝ,(x-m)^2=x^2-(2*m)*x+m^2*(1:ℝ) := λ x,by ring,
 simp_rw [hp],
 have ha := integral_add (h₂.sub (h₁.const_mul (2*m))) (h₀.const_mul (m^2)),
 have hb := integral_sub h₂ (h₁.const_mul (2*m)),
 simp only [pi.sub_apply] at ha,
 rw [ha,hb,integral_mul_left,integral_mul_left]
end

theorem work_support_single_mass (μ : measure ℝ) (m : ℝ)
 (hi : integrable (λ x:ℝ,(x-m)^2) μ) :
 (∫ x,(x-m)^2 ∂μ)=0 ↔ ∀ᵐ x ∂μ,x=m :=
begin
 have hp : 0 ≤ᵐ[μ] (λ x:ℝ,(x-m)^2) := filter.eventually_of_forall (λ x:ℝ,sq_nonneg (x-m)),
 rw [integral_eq_zero_iff_of_nonneg_ae hp hi],
 split,
 { intro h,filter_upwards [h] with x hx,change (x-m)^2=0 at hx,exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx) },
 { intro h,filter_upwards [h] with x hx,change (x-m)^2=0,rw [hx,sub_self],norm_num }
end

theorem work_rank_determinant (m₀ m₁ m₂ : ℝ) (h : m₀ ≠ 0) :
 m₀*(m₂-2*(m₁/m₀)*m₁+(m₁/m₀)^2*m₀)=m₀*m₂-m₁^2 :=
by field_simp [h];ring

theorem compact_tanh_coefficients (a b c d : ℝ)
 (ha : 3*a= -1) (hb : 5*b= -2*a) (hc : 7*c= -(2*b+a^2))
 (hd : 9*d= -(2*c+2*a*b)) :
 a= -1/3 ∧ b=2/15 ∧ c= -17/315 ∧ d=62/2835 :=
begin
 have a' : a= -1/3 := by linarith,
 have b' : b=2/15 := by linarith,
 rw [a',b'] at hc hd,norm_num at hc,
 have c' : c= -17/315 := by linarith only [hc],
 rw [c'] at hd,norm_num at hd,exact ⟨a',b',c',by linarith only [hd]⟩
end

theorem compact_contact_variance (g l : ℝ) (hg : g≠0) (hl : l≠0) :
 ((2/15)*g^2*l^5)*((62/2835)*g^2*l^9)/(((17/315)*g^2*l^7)^2)-1=(1:ℝ)/867 :=
by field_simp [hg,hl];ring

theorem current_axis_distance {ι : Type*} (s : finset ι) (u v : ι → ℝ)
 (hu : (∑ i in s,u i^2)=1) (hv : (∑ i in s,v i^2)=1) :
 (∑ i in s,∑ j in s,(u i*u j-v i*v j)^2)=2*(1-(∑ i in s,u i*v i)^2) :=
begin
 classical,
 simp_rw [show ∀ i j,(u i*u j-v i*v j)^2=u i^2*u j^2-(2*(u i*v i))*(u j*v j)+v i^2*v j^2,
    from λ i j,by ring],
 simp only [sum_add_distrib,sum_sub_distrib,←mul_sum,←sum_mul,hu,hv],ring
end

theorem strictly_positive_moment_energy {E : Type*} [has_zero E] (F : E → ℕ → ℝ)
 (separates : ∀ x,(∀ j,F x j=0) → x=0) (w : ℕ → ℝ) (hw : ∀ j,0<w j)
 {x : E} (hx : x≠0) (hs : summable (λ j,w j*(F x j)^2)) :
 0 < ∑' j,w j*(F x j)^2 :=
begin
 classical,
 have hn : ¬∀ j,F x j=0 := λ h,hx (separates x h),
 push_neg at hn,obtain ⟨j,hj⟩:=hn,
 exact lt_of_lt_of_le (mul_pos (hw j) (sq_pos_of_ne_zero _ hj))
   (le_tsum hs j (λ i hi,mul_nonneg (hw i).le (sq_nonneg _)))
end

theorem soft_screen_averages (a : ℝ) :
 1-2*(1:ℝ)/3+(1/2)*(2/15)=2/5 ∧
 1-2*a/3+(2/3)*(2*a^2/15)=1-2*a/3+4*a^2/45 ∧
 (1-2/3+(4:ℝ)/45)/(2/5)=19/18 := by refine ⟨_,_,_⟩;ring

theorem soft_circle_integral :
 (∫ x in (0:ℝ)..real.pi,real.sin x^2-(2/3)*real.sin x^4+(4/45)*real.sin x^6)
 =5*real.pi/18 :=
begin
 have ha:=integral_sin_pow_even 1,have hb:=integral_sin_pow_even 2,have hc:=integral_sin_pow_even 3,
 norm_num [finset.prod_range_succ] at ha hb hc,
 have ia : interval_integrable (λ x:ℝ,real.sin x^2) volume 0 real.pi :=
     (real.continuous_sin.pow 2).interval_integrable _ _,
 have ib : interval_integrable (λ x:ℝ,(2/3)*real.sin x^4) volume 0 real.pi :=
     (continuous_const.mul (real.continuous_sin.pow 4)).interval_integrable _ _,
 have ic : interval_integrable (λ x:ℝ,(4/45)*real.sin x^6) volume 0 real.pi :=
     (continuous_const.mul (real.continuous_sin.pow 6)).interval_integrable _ _,
 rw [interval_integral.integral_add (ia.sub ib) ic,interval_integral.integral_sub ia ib,
     interval_integral.integral_const_mul,interval_integral.integral_const_mul,hb,hc],
 rw [integral_sin_sq],simp only [real.sin_zero,real.sin_pi,zero_mul,sub_zero,zero_sub,zero_add],ring
end

theorem compact_band_primitive (s : ℝ) :
 (19/45)*(s^2)+(26/45)*s^2*(1-s^2)-(4/45)*s^4*(1-s^2)=
 s^2*(1-2*s^2/3+4*s^4/45) := by ring

theorem scattering_ports_positive (u w v : ℝ) (hv : 0<1-v^2) (hn : u≠0 ∨ w≠0) :
 0<u^2+2*v*u*w+w^2 :=
begin
 have eqn : u^2+2*v*u*w+w^2=(u+v*w)^2+(1-v^2)*w^2 := by ring,
 rw [eqn],by_cases hw : w=0,
 { rw [hw],simp,exact sq_pos_of_ne_zero _ (hn.resolve_right (not_not_intro hw)) },
 { exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hv (sq_pos_of_ne_zero _ hw)) }
end

theorem ports_conditioning (e : ℝ) (he : e ≠ 4) :
 (e/4)/((1-e/2)+e/4)=e/(4-e) :=
begin
 have h : 4-e≠0 := λ h,he (by linarith),
 rw [show (1-e/2)+e/4=(4-e)/4,by ring,div_div_div_cancel_right _ (by norm_num : (4:ℝ)≠0)]
end

theorem port_likelihood_polynomial (v l : ℝ) :
 4*((144/169-l/2)*(25/169-l/2)-(60*v/169-l*v/2)^2)=
 (1-v^2)*l^2-2*(1-(120/169)*v^2)*l+(120/169)^2*(1-v^2) := by ring

theorem port_fidelity_rationalization (q v b d : ℝ) :
 ((1-v^2)+q*(1-b)*v^2)^2-
 (1-v^2)*((1-v^2)+2*q*(1-b)*v^2-q^2*((1-b)^2*v^2+d^2))=
 q^2*((1-b)^2*v^2+(1-v^2)*d^2) := by ring

theorem rotor_parity_protection {R : Type*} [ring R] (p l a b : R)
 (hl : p*l=l*p) (ha : p*a=a) (hb : b*p=0) : b*l*a=0 :=
calc b*l*a = b*(l*(p*a)) : by rw [ha,mul_assoc]
 ... = (b*p)*l*a : by simp only [←mul_assoc,←hl]
 ... = 0 : by rw [hb,zero_mul,zero_mul]

theorem rotor_angular_integrals :
 (∫ x in (-1:ℝ)..1,(15*x^6-14*x^4+3*x^2)/4)=6/35 ∧
 (∫ x in (-1:ℝ)..1,(9*x^4-6*x^2+1)/12)=2/15 :=
begin
 have i2 : interval_integrable (λ x:ℝ,x^2) volume (-1) 1 := (continuous_id.pow 2).interval_integrable _ _,
 have i4 : interval_integrable (λ x:ℝ,x^4) volume (-1) 1 := (continuous_id.pow 4).interval_integrable _ _,
 have i6 : interval_integrable (λ x:ℝ,x^6) volume (-1) 1 := (continuous_id.pow 6).interval_integrable _ _,
 have one : interval_integrable (λ x:ℝ,(1:ℝ)) volume (-1) 1 := continuous_const.interval_integrable _ _,
 split,
 { rw [interval_integral.integral_div,interval_integral.integral_add ((i6.const_mul 15).sub (i4.const_mul 14)) (i2.const_mul 3),
       interval_integral.integral_sub (i6.const_mul 15) (i4.const_mul 14)],
   simp only [interval_integral.integral_const_mul,integral_pow],norm_num },
 { rw [interval_integral.integral_div,interval_integral.integral_add ((i4.const_mul 9).sub (i2.const_mul 6)) one,
       interval_integral.integral_sub (i4.const_mul 9) (i2.const_mul 6)],
   simp only [interval_integral.integral_const_mul,interval_integral.integral_const,integral_pow],norm_num }
end

theorem rotor_gravity_width (g h c w : ℝ) (hh : h≠0) (hc : c≠0) (hw : w≠0) :
 2*g*w^5/(5*h*c^5)*(5*h/w)^2*(6/35)=(12/7)*g*h*w^3/c^5 ∧
 (6/35 : ℝ)/(2/15)*(5/3)^5=3125/189 :=
by split;field_simp [hh,hc,hw];ring

theorem mass_shell_lines (a b : ℝ) (ha : a≠0) (hb : b≠0) :
 let e := (a^2-b^2)/(2*a), u := (a^2-b^2)/(2*b) in
 (a-e)^2=b^2+e^2 ∧ (b+u)^2=a^2+u^2 ∧ u=(a/b)*e :=
by dsimp;refine ⟨_,_,_⟩;field_simp [ha,hb];ring

theorem rotor_thermal_balance :
 (7/3:ℝ)*real.exp(-real.log(7/3))=1 :=
by rw [real.exp_neg,real.exp_log (by norm_num : (0:ℝ)<7/3)];norm_num

theorem identical_material_channel (a b mark : ℝ) (ha : 0<a) (hb : 0<b) :
 a*mark=0 ↔ b*mark=0 :=
by simp [ha.ne',hb.ne']

theorem fixed_radiation_fidelity_order (v b d : ℝ) (hd : 0<1-v^2) :
 tendsto (λ q : ℝ,((1-b)^2*v^2+d^2*(1-v^2))/
 (2*((1-v^2)+q*(1-b)*v^2+real.sqrt ((1-v^2)*((1-v^2)+2*q*(1-b)*v^2-q^2*((1-b)^2*v^2+d^2))))))
 (𝓝 0) (𝓝 ((d^2+(1-b)^2*v^2/(1-v^2))/4)) :=
begin
 let den : ℝ → ℝ := λ q,2*((1-v^2)+q*(1-b)*v^2+
    real.sqrt ((1-v^2)*((1-v^2)+2*q*(1-b)*v^2-q^2*((1-b)^2*v^2+d^2)))),
 have cont : continuous den := by dsimp only [den];continuity,
 have d0 : den 0=4*(1-v^2) := by {
  dsimp [den],simp only [zero_mul,mul_zero,zero_pow (by norm_num : (0:ℕ)<2),add_zero,sub_zero],
  rw [←sq,real.sqrt_sq hd.le],ring },
 have hn : den 0 ≠ 0 := by rw [d0]; exact mul_ne_zero (by norm_num) hd.ne',
 have ht := (tendsto_const_nhds : tendsto (λ q:ℝ,(1-b)^2*v^2+d^2*(1-v^2)) (𝓝 0)
             (𝓝 ((1-b)^2*v^2+d^2*(1-v^2)))).div (cont.tendsto 0) hn,
 rw [d0] at ht,
 convert ht using 2;try {field_simp [hd.ne'];ring}
end

theorem tidal_power_composition {α : Type*} {l : filter α} (q t w : α → ℝ) (k c : ℝ)
 (hq : tendsto (λ i,q i/(t i)^6) l (𝓝 k))
 (hw : tendsto (λ i,w i/(q i)^2) l (𝓝 c))
 (hn : ∀ i,q i≠0) (ht : ∀ i,t i≠0) :
 tendsto (λ i,w i/(t i)^12) l (𝓝 (c*k^2)) :=
begin
 have hh:=hw.mul (hq.pow 2),
 convert hh using 1,funext i,field_simp [hn i,ht i],try {left},ring
end

theorem crossover_square_root (a q k t : ℝ) (hq : 0≤q) :
 real.sqrt ((q*a)*(q*a+2*q*k-q^2*t))=q*real.sqrt (a*(a+2*k-q*t)) :=
begin
 rw [show q*a*(q*a+2*q*k-q^2*t)=q^2*(a*(a+2*k-q*t)),by ring,
     real.sqrt_mul (sq_nonneg q),real.sqrt_sq hq]
end

theorem compact_limit_separation {α : Type*} {l : filter α} (step logratio err : α → ℝ) (z : ℝ)
 (hs : tendsto step l (𝓝 0)) (hr : tendsto logratio l (𝓝 z)) (he : tendsto err l (𝓝 0)) :
 tendsto (λ i,(5/36)*(1-step i)+19/(90*real.pi)*logratio i+err i)
 l (𝓝 (5/36+19*z/(90*real.pi))) :=
begin
 have h1 : tendsto (λ i:α,(1:ℝ)) l (𝓝 1) := tendsto_const_nhds,
 have h5 : tendsto (λ i:α,(5/36:ℝ)) l (𝓝 (5/36)) := tendsto_const_nhds,
 have h19 : tendsto (λ i:α,(19/(90*real.pi))) l (𝓝 (19/(90*real.pi))) := tendsto_const_nhds,
 have h := ((h5.mul (h1.sub hs)).add (h19.mul hr)).add he,
 change tendsto (λ i,(5/36)*(1-step i)+19/(90*real.pi)*logratio i+err i) _ _,
 convert h using 2;ring
end

theorem ring_characteristic (r : ℝ) (h : r≠0) (n : ℕ) :
 (r+r⁻¹)*r^(n+1)-r^n-r^(n+2)=0 :=
by simp only [pow_succ];field_simp [h];ring

theorem ring_green_coefficients (p : ℝ) :
 let b₁ := -2*p/3, b₂ := 6*p^2/5, b₃ := -20*p^3/7, b₄ := 70*p^4/9,
     c₁ := b₁-1/3, c₂ := b₂-b₁+2/15,
     c₃ := b₃-(b₂+b₁^2)+(2/15)*5*b₁-17/315,
     c₄ := b₄-(3*b₃+6*b₁*b₂+b₁^3)/3+
                (2/15)*(5*b₂+10*b₁^2)-(17/315)*7*b₁+62/2835 in
 c₂-2*p*c₁+6*p^2=(2+20*p+128*p^2)/15 ∧
 c₃-2*p*c₂+6*p^2*c₁-20*p^3= -(17+224*p+1568*p^2+9216*p^3)/315 ∧
 c₄-2*p*c₃+6*p^2*c₂-20*p^3*c₁+70*p^4=
 (62+1020*p+8736*p^2+52480*p^3+294912*p^4)/2835 :=
by dsimp;refine ⟨_,_,_⟩;ring

theorem ring_variance_factor (p : ℝ) :
 ((2+20*p+128*p^2)/15)*((62+1020*p+8736*p^2+52480*p^3+294912*p^4)/2835)
 -((17+224*p+1568*p^2+9216*p^3)/315)^2 =
 ((1-4*p)*(1-16*p)*(1+132*p+12768*p^2+71168*p^3+147456*p^4))/297675 :=
by ring

theorem ring_nonzero_variance (p : ℝ) (hp : 0≤p) (h : p<1/16) :
 0<(1-4*p)*(1-16*p)*(1+132*p+12768*p^2+71168*p^3+147456*p^4) :=
begin
 have h4 : 0<1-4*p := by linarith, have h16 : 0<1-16*p := by linarith,
 apply mul_pos (mul_pos h4 h16),positivity
end

theorem ring_first_correction :
 ((2/15:ℝ)*(62/2835)/((-17/315)^2))*
 ((4/3)/(2/15)+(68/189)/(62/2835)-2*((-32/45)/(-17/315)))=1456/14739 :=
by norm_num

theorem equal_covariant_mark_gain (g e p dt : ℝ) :
 g*p*dt+e*p*dt=(g+e)*p*dt := by ring

theorem matrix_link_components (ar ai br bi : ℝ) :
 ((ar+br)/2)^2+((ai+bi)/2)^2+((ar-br)/2)^2+((ai-bi)/2)^2=
 (ar^2+ai^2+br^2+bi^2)/2 := by ring

theorem matrix_gauge_odd_linear {E : Type*} [add_comm_group E] [module ℝ E]
 (j : E →ₗ[ℝ] ℝ) (T : E → E) (inv : ∀ u,j (T u)=j u) (v : E) (flip : T v= -v) :
 j v=0 :=
begin have h:=inv v,rw [flip,map_neg] at h,linarith end

theorem matrix_neutral_pair_phases (a b z d : ℂ) (ha : a≠0) (hb : b≠0) :
 (a*d/b)*(b*z/a)=d*z := by field_simp [ha,hb];ring

theorem matrix_odd_pair_weight (a b : ℝ) (ha : a^2=1) (hb : b^2=1) :
 (a-b)^2=2*(1-a*b) := by nlinarith only [ha,hb]

theorem matrix_bubble_moment_2 :
 (∫ x in (0:ℝ)..1,(x*(1-x))^2/2)=1/60 :=
begin
 have deriv : ∀ x : ℝ,has_deriv_at (λ t:ℝ,(1/6:ℝ)*t^3+(-1/4:ℝ)*t^4+(1/10:ℝ)*t^5) ((x*(1-x))^2/2) x := λ x,by {
    have hh := (((((has_deriv_at_id x).pow 3).const_mul (1/6:ℝ)).add (((has_deriv_at_id x).pow 4).const_mul (-1/4:ℝ))).add (((has_deriv_at_id x).pow 5).const_mul (1/10:ℝ))),convert hh using 1;norm_num [id];ring },
 have hc : continuous (λ x:ℝ,(x*(1-x))^2/2) := by continuity,
 rw [interval_integral.integral_eq_sub_of_has_deriv_at (λ x hx,deriv x) (hc.interval_integrable _ _)],norm_num
end

theorem matrix_bubble_moment_3 :
 (∫ x in (0:ℝ)..1,(x*(1-x))^3/3)=1/420 :=
begin
 have deriv : ∀ x : ℝ,has_deriv_at (λ t:ℝ,(1/12:ℝ)*t^4+(-1/5:ℝ)*t^5+(1/6:ℝ)*t^6+(-1/21:ℝ)*t^7) ((x*(1-x))^3/3) x := λ x,by {
    have hh := ((((((has_deriv_at_id x).pow 4).const_mul (1/12:ℝ)).add (((has_deriv_at_id x).pow 5).const_mul (-1/5:ℝ))).add (((has_deriv_at_id x).pow 6).const_mul (1/6:ℝ))).add (((has_deriv_at_id x).pow 7).const_mul (-1/21:ℝ))),convert hh using 1;norm_num [id];ring },
 have hc : continuous (λ x:ℝ,(x*(1-x))^3/3) := by continuity,
 rw [interval_integral.integral_eq_sub_of_has_deriv_at (λ x hx,deriv x) (hc.interval_integrable _ _)],norm_num
end

theorem matrix_bubble_moment_4 :
 (∫ x in (0:ℝ)..1,(x*(1-x))^4/4)=1/2520 :=
begin
 have deriv : ∀ x : ℝ,has_deriv_at (λ t:ℝ,(1/20:ℝ)*t^5+(-1/6:ℝ)*t^6+(3/14:ℝ)*t^7+(-1/8:ℝ)*t^8+(1/36:ℝ)*t^9) ((x*(1-x))^4/4) x := λ x,by {
    have hh := (((((((has_deriv_at_id x).pow 5).const_mul (1/20:ℝ)).add (((has_deriv_at_id x).pow 6).const_mul (-1/6:ℝ))).add (((has_deriv_at_id x).pow 7).const_mul (3/14:ℝ))).add (((has_deriv_at_id x).pow 8).const_mul (-1/8:ℝ))).add (((has_deriv_at_id x).pow 9).const_mul (1/36:ℝ))),convert hh using 1;norm_num [id];ring },
 have hc : continuous (λ x:ℝ,(x*(1-x))^4/4) := by continuity,
 rw [interval_integral.integral_eq_sub_of_has_deriv_at (λ x hx,deriv x) (hc.interval_integrable _ _)],norm_num
end

theorem matrix_four_dimensional_pair (p : ℝ) (h : 2+20*p+128*p^2≠0) :
 (7/6)*((1+8*p)/3)*((17+224*p+1568*p^2+9216*p^3)/315)/(((2+20*p+128*p^2)/15)^2)-1=
 5*(1+8*p)*(17+224*p+1568*p^2+9216*p^3)/(18*(2+20*p+128*p^2)^2)-1 :=
by field_simp [h];ring

theorem matrix_single_pair_and_circle :
 ((1/60:ℝ)*(1/2520)/(1/420)^2-1)=1/6 ∧ (5:ℝ)*17/(18*2^2)-1=13/72 := by split;norm_num

-- Retarded propagation in layer space and a gauge-neutral polarization reference.
def front_walk (d b : ℝ) : ℕ → ℤ → ℝ
| 0 j := if j=0 then 1 else 0
| (n+1) j := d*front_walk n j+b*(front_walk n (j-1)+front_walk n (j+1))

theorem front_walk_above (d b : ℝ) : ∀ (n : ℕ) (j : ℤ), (n:ℤ)<j → front_walk d b n j=0 :=
begin
 intro n, induction n with n ih,
 { intros j hj, change (0:ℤ)<j at hj, simp [front_walk, ne_of_gt hj] },
 { intros j hj, rw [int.coe_nat_succ] at hj,
   have h₁ : (n:ℤ)<j := by linarith,
   have h₂ : (n:ℤ)<j-1 := by linarith,
   have h₃ : (n:ℤ)<j+1 := by linarith,
   simp [front_walk, ih _ h₁, ih _ h₂, ih _ h₃] }
end

theorem front_walk_reflect (d b : ℝ) : ∀ (n : ℕ) (j : ℤ), front_walk d b n (-j)=front_walk d b n j :=
begin
 intro n, induction n with n ih,
 { intro j, simp [front_walk] },
 { intro j, change d*front_walk d b n (-j)+b*(front_walk d b n (-j-1)+front_walk d b n (-j+1))=_,
   rw [show -j-1= -(j+1),by ring,show -j+1= -(j-1),by ring, ih, ih, ih],
   change _=d*front_walk d b n j+b*(front_walk d b n (j-1)+front_walk d b n (j+1)),ring }
end

theorem front_walk_edge (d b : ℝ) : ∀ n : ℕ, front_walk d b n (n:ℤ)=b^n :=
begin
 intro n, induction n with n ih,
 { simp [front_walk] },
 { change d*front_walk d b n ((n+1:ℕ):ℤ)+b*(front_walk d b n (((n+1:ℕ):ℤ)-1)+
           front_walk d b n (((n+1:ℕ):ℤ)+1))=_,
   rw [int.coe_nat_succ], have h₁ : (n:ℤ)<n+1 := by linarith,
   have h₂ : (n:ℤ)<n+1+1 := by linarith,
   rw [front_walk_above _ _ _ _ h₁, front_walk_above _ _ _ _ h₂,
       show (n:ℤ)+1-1=n,by ring,ih,pow_succ],ring }
end

theorem front_antipodal_first (d b : ℝ) (m : ℕ) :
 front_walk d b m (m:ℤ)+front_walk d b m (-(m:ℤ))=2*b^m :=
by rw [front_walk_reflect,front_walk_edge];ring

theorem front_antipodal_earlier (d b : ℝ) (m n : ℕ) (h : n<m) :
 front_walk d b n (m:ℤ)+front_walk d b n (-(m:ℤ))=0 :=
by rw [front_walk_reflect,front_walk_above d b n (m:ℤ) (by exact_mod_cast h)];ring

theorem front_image_distance (m q : ℤ) (hm : 0<m) (hq : q≠0) (hn : q≠ -1) :
 m < abs (m+2*m*q) :=
begin
 by_cases h : 0≤q,
 { have hp : 0<q := lt_of_le_of_ne h (ne.symm hq),
   have hp' : 0<m*q := mul_pos hm hp,
   rw [abs_of_pos (show 0<m+2*m*q,by nlinarith)],nlinarith },
 { have hq' : q ≤ -2 := by omega,
   have hprod:=mul_le_mul_of_nonneg_left hq' hm.le,
   rw [abs_of_neg (show m+2*m*q<0, by nlinarith)],nlinarith }
end

theorem front_integrated_power (v t : ℝ) (m : ℕ) :
 (v*t^(2*m+2))^2=v^2*t^(4*m+4) :=
by rw [mul_pow,←pow_mul,show (2*m+2)*2=4*m+4,by ring]

theorem reference_neutral_loop (g h k x y z : ℂ) (hg : g≠0) (hh : h≠0) (hk : k≠0) :
 (g*x/h)*(h*y/k)*(k*z/g)=x*y*z := by field_simp [hg,hh,hk];ring

theorem reference_reciprocal_gap {E : Type*} [seminormed_add_comm_group E] (a b : E) :
 ‖a-b‖=‖b-a‖ := norm_sub_rev _ _

theorem reference_even_odd {E : Type*} [add_comm_group E] [module ℝ E]
 (S : E →ₗ[ℝ] E) (U : E → E) (f : E →ₗ[ℝ] ℝ) (v : E)
 (hin : S v=v) (hc : ∀ w,S (U w)=U (S w)) (hout : ∀ w,f (S w)= -f w) :
 f (U v)=0 :=
begin have h:=hout (U v),rw [hc,hin] at h,linarith end

theorem reference_equal_gap (a b : ℂ) : a*b-b*a=0 := by ring

theorem reference_fock_stimulation (q : ℝ) (hq : q≠1) (t : ℝ)
 (h : t^2=1-q) : t^4/(1-q)^2=1 :=
by rw [show t^4=(t^2)^2,by ring,h];exact div_self (pow_ne_zero 2 (sub_ne_zero.mpr (ne.symm hq)))

theorem reference_bogoliubov (a b : ℝ) (h : a-b=1) (hp : 0≤b) :
 0<1/a ∧ 1/a≤1 ∧ 1-b/a=1/a :=
begin have ha : 0<a := by linarith,refine ⟨one_div_pos.mpr ha, (div_le_one ha).mpr (by linarith), _⟩,
 field_simp [ha.ne'];linarith end

theorem reference_lagrange (a b c d : ℂ) :
 complex.norm_sq (a*d-b*c)+complex.norm_sq ((star_ring_end ℂ a)*c+(star_ring_end ℂ b)*d)=
 (complex.norm_sq a+complex.norm_sq b)*(complex.norm_sq c+complex.norm_sq d) :=
by simp [complex.norm_sq_apply, complex.mul_re,complex.mul_im,complex.add_re,complex.add_im,
         complex.sub_re,complex.sub_im,complex.conj_re,complex.conj_im];ring

theorem reference_born_bound (v det overlap aa bb : ℝ) (hv : 0≤v) (hd : 0≤det)
 (ho : 0≤overlap) (h : det+overlap=aa*bb) :
 0≤v*det/8 ∧ v*det/8 ≤ (v*aa*bb/4)/2 :=
begin split,{positivity},
 calc v*det/8 ≤ v*(det+overlap)/8 : div_le_div_of_le (by norm_num) (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right ho) hv)
 ... = (v*aa*bb/4)/2 : by rw [h];ring
end

theorem reference_wave_wronskian (u v du dv f : ℝ → ℝ) (x : ℝ)
 (hu : has_deriv_at u (du x) x) (hv : has_deriv_at v (dv x) x)
 (hdu : has_deriv_at du (-f x*u x) x) (hdv : has_deriv_at dv (-f x*v x) x) :
 has_deriv_at (λ t,u t*dv t-du t*v t) 0 x :=
begin convert (hu.mul hdv).sub (hdu.mul hv) using 1;ring end

theorem reference_gauss_reduction (z k e phi y dy ddy : ℂ)
 (h : z*(1-z)*ddy+(1-k-2*z)*dy+e*y=0) :
 phi*(4*z^2*(1-z)^2*ddy+4*z*(1-z)*(1-2*z-k)*dy+4*e*z*(1-z)*y)=0 :=
begin linear_combination 4*phi*z*(1-z)*h end

theorem reference_first_pulse (p q a : ℝ) (hp : p≠0) (hq : q≠0) :
 (a/(2*p)-(-a/(2*p))-(a/(2*q)-(-a/(2*q))))^2/8=(a^2/8)*(1/p-1/q)^2 :=
by field_simp [hp,hq];ring

theorem reference_tidal_element (p q e : ℝ) :
 (p*e/2-q*e/2)^2/2=(p-q)^2*e^2/8 := by ring

theorem reference_mixed_curvature (kx ky b f tr : ℝ) :
 (-(kx*ky)*(b*f)+0*tr)^2=(kx*ky*b)^2*f^2 := by ring

theorem reference_trace_transition {ι : Type*} (s : finset ι) (a : ι → ℝ) (p q : ℝ) :
 (∑ i in s,∑ j in s,(p-q)^2*(a i-a j)^2)/8 =
 (p-q)^2*((s.card:ℝ)*(∑ i in s,(a i)^2)-(∑ i in s,a i)^2)/4 :=
begin
 have h:=ordered_differences s a a,
 simp_rw [←sq] at h,
 simp_rw [←mul_sum],rw [h],ring
end

theorem reference_isotropic_blind (p q z : ℝ) : (p-q)^2*(z-z)^2=0 := by ring

theorem reference_reverse_flux (d f : ℝ) (hd : 1<d) (hf : f≠0) :
 (f/(d*(d+1)/2))/(f/(d*(d-1)/2))=(d-1)/(d+1) :=
begin have h₁ : d≠0 := by linarith,have h₂ : d+1≠0 := by linarith,
 have h₃ : d-1≠0 := by linarith,field_simp [h₁,h₂,h₃,hf];ring end

theorem reference_no_absorbing (p q up down : ℝ) (hp : 0<p) (hu : 0<up)
 (h : p*up=q*down) : down≠0 :=
begin intro hh,rw [hh,mul_zero] at h,exact (mul_pos hp hu).ne' h end

theorem reference_strain_power (f q w a : ℝ) (h : q=4*a*w) :
 w*f^2*q/8=a*w^2*f^2/2 := by rw [h];ring

theorem reference_horizon_normalization (r g : ℝ) (hr : r≠0) (hg : g≠0) :
 8*(r^6/(180*g))*(1/(4*real.pi*r))=r^5/(90*real.pi*g) :=
by field_simp [hr,hg,real.pi_ne_zero];ring

-- The contraction of r^5 d_i d_j d_k d_l(1/r) with an STF quadrupole at n=z.
theorem reference_stf_tides (xx yy zz xy xz yz : ℝ) (h : xx+yy+zz=0) :
 (105*zz-15*(zz+4*zz)+6*zz=36*zz) ∧
 (-15*zz+6*xx=6*(xx+zz/2)-18*zz) ∧
 (-15*zz+6*yy=6*(yy+zz/2)-18*zz) ∧
 ((-15*2+6)*xz= -24*xz) ∧ ((-15*2+6)*yz= -24*yz) ∧
 (6*xy=6*xy) ∧ (-15*zz+6*xx-15*zz+6*yy+36*zz=0) :=
by refine ⟨by ring,by ring,by ring,by ring,by ring,rfl,by linarith⟩

theorem reference_horizon_rates (r s g delta : ℝ) (hr : r≠0) (hg : g≠0) :
 (g*6/(2*r^5))^2*(s^5/(90*real.pi*g)/2)*delta^2/8 =
 g*s^5*delta^2/(160*real.pi*r^10) ∧
 (g*(-24)/(2*r^5))^2*(s^5/(90*real.pi*g)/2)*delta^2/8 =
 16*(g*s^5*delta^2/(160*real.pi*r^10)) :=
by split;field_simp [hr,hg,real.pi_ne_zero];ring

theorem reference_acceleration_match (r s g delta : ℝ) (hr : r≠0) :
 g*(s/(2*r^2))^5*delta^2/(5*real.pi)=g*s^5*delta^2/(160*real.pi*r^10) :=
by field_simp [hr,real.pi_ne_zero];ring_nf; simp

theorem reference_horizon_tensor_ratio : ((-24:ℝ)/6)^2=16 := by norm_num

theorem front_sine_bound (u : ℝ) : |real.sin u|≤|u| :=
begin
 have h:= interval_integral.norm_integral_le_of_norm_le_const (show ∀ x ∈ set.uIoc 0 u, ‖real.cos x‖≤1, from λ x hx,real.abs_cos_le_one x),
 simpa [integral_cos,real.norm_eq_abs] using h
end

theorem front_cosine_lipschitz (x y : ℝ) : |real.cos x-real.cos y| ≤ |x-y| :=
begin
 rw [real.cos_sub_cos, abs_mul, abs_mul],
 have h₁:=real.abs_sin_le_one ((x+y)/2),
 have h₂:=front_sine_bound ((x-y)/2),
 have hh:=mul_le_mul h₁ h₂ (abs_nonneg _) zero_le_one,
 rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh,
 rw [abs_of_neg (by norm_num : (-2:ℝ)<0)],linarith [hh]
end

theorem front_cubic_sine (x : ℝ) (hx : 0≤x) : x-real.sin x ≤ x^3/6 :=
begin
 have taylor₂ : ∀ u : ℝ, 0≤u → 1-real.cos u ≤ u^2/2,
 { intros u hu,
   have h : (∫ t in (0:ℝ)..u,real.sin t) ≤ (∫ t in (0:ℝ)..u,id t) := interval_integral.integral_mono_on hu (real.continuous_sin.interval_integrable _ _)
      (continuous_id.interval_integrable _ _) (λ t ht,show real.sin t ≤ id t,from
       (le_abs_self _).trans ((front_sine_bound _).trans_eq (abs_of_nonneg ht.1))),
   simpa [integral_sin,integral_id,id,real.cos_zero] using h },
 have hh : (∫ u in (0:ℝ)..x,(1-real.cos u)) ≤ (∫ u in (0:ℝ)..x,u^2/2) := interval_integral.integral_mono_on hx ((continuous_const.sub real.continuous_cos).interval_integrable 0 x)
    (((continuous_id.pow 2).div_const 2).interval_integrable 0 x)
    (λ t ht, taylor₂ t ht.1),
 have hsub : (∫ u in (0:ℝ)..x,1-real.cos u)=x-real.sin x,
 { have hder : ∀ u : ℝ,has_deriv_at (λ z : ℝ,z-real.sin z) (1-real.cos u) u :=
       λ u,(has_deriv_at_id u).sub (real.has_deriv_at_sin u),
   have hc : continuous (λ u : ℝ,1-real.cos u) := continuous_const.sub real.continuous_cos,
   rw [interval_integral.integral_eq_sub_of_has_deriv_at (λ u hu,hder u) (hc.interval_integrable 0 x)],
   simp },
 rw [hsub] at hh,
 simpa [div_eq_mul_inv,interval_integral.integral_mul_const,integral_pow] using
   (show x-real.sin x ≤ x^3/6,by {
     have hh' : (∫ u in (0:ℝ)..x,u^2/2)=x^3/6 := by {
       simp only [div_eq_mul_inv,interval_integral.integral_mul_const,integral_pow],norm_num,ring },
     rwa [hh'] at hh })
end

theorem front_gap_lipschitz (x y w v k : ℝ) (hx : 0≤x) (hy : 0≤y) (hxy : y≤x)
 (hw : 0≤w) (hv : 0≤v) (hw2 : w^2=k^2+x^2) (hv2 : v^2=k^2+y^2) :
 |w-v|≤x-y :=
begin
 have hx' : x≤w := by nlinarith [sq_nonneg k],
 have hy' : y≤v := by nlinarith [sq_nonneg k],
 have hdiff : v≤w := by nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (add_nonneg hx hy)],
 rw [abs_of_nonneg (sub_nonneg.mpr hdiff)],
 by_contra hh, push_neg at hh,
 have hplus : 0<w+v := by linarith,
 have h₁:=mul_lt_mul_of_pos_right hh hplus,
 have h₂:=mul_le_mul_of_nonneg_left (show x+y≤w+v,by linarith) (sub_nonneg.mpr hxy),
 nlinarith only [hw2,hv2,h₁,h₂]
end

theorem front_kernel_error (w v t : ℝ) (ht : 0≤t) :
 |∫ s in (0:ℝ)..t,(real.cos (w*s)-real.cos (v*s))| ≤ |w-v|*t^2/2 :=
begin
 have hc : continuous (λ s : ℝ, |w-v|*s) := continuous_const.mul continuous_id,
 have h : ‖∫ s in (0:ℝ)..t,real.cos (w*s)-real.cos (v*s)‖ ≤
     (∫ s in (0:ℝ)..t,‖real.cos (w*s)-real.cos (v*s)‖) := interval_integral.norm_integral_le_integral_norm ht,
 have cf : continuous (λ s : ℝ, ‖real.cos (w*s)-real.cos (v*s)‖) := by continuity,
 have hm : (∫ s in (0:ℝ)..t,‖real.cos (w*s)-real.cos (v*s)‖) ≤
    (∫ s in (0:ℝ)..t,|w-v|*s) := interval_integral.integral_mono_on ht (cf.interval_integrable _ _) (hc.interval_integrable _ _)
   (λ s hs,show ‖real.cos (w*s)-real.cos (v*s)‖≤|w-v|*s,by {
    rw [real.norm_eq_abs],have hh:=front_cosine_lipschitz (w*s) (v*s),
    rwa [←sub_mul,abs_mul,abs_of_nonneg hs.1] at hh }),
 have hr:=h.trans hm,
 simpa [real.norm_eq_abs,interval_integral.integral_const_mul,integral_id,mul_div_assoc] using hr
end

theorem front_profile_error {ι : Type*} (s : finset ι) (c f q : ι → ℝ) (a t : ℝ)
 (h : ∀ n∈s, |f n|≤ a^2*t^2/48*|q n|^3) :
 |∑ n in s,c n*f n|≤a^2*t^2/48*(∑ n in s,|c n|*|q n|^3) :=
begin
 refine (abs_sum_le_sum_abs _ _).trans _,rw [mul_sum],apply sum_le_sum,intros n hn,
 rw [abs_mul],calc |c n|*|f n| ≤ |c n|*(a^2*t^2/48*|q n|^3) :
   mul_le_mul_of_nonneg_left (h n hn) (abs_nonneg _)
 ... = _ : by ring
end

theorem reference_partial_gains (eta up rho : ℝ) :
 eta*up*rho+(1-eta)*up*rho=up*rho := by ring

theorem reference_zero_temperature_factor (b : ℝ) (hb : b≠0) :
 tendsto (λ w:ℝ,w/(1-real.exp (-b*w))) (𝓝[≠] 0) (𝓝 (1/b)) :=
begin
 have hd : has_deriv_at (λ w:ℝ,1-real.exp (-b*w)) b 0,
 { convert (has_deriv_at_const (0:ℝ) (1:ℝ)).sub
   ((real.has_deriv_at_exp (-b*0)).comp 0 ((has_deriv_at_id (0:ℝ)).const_mul (-b))) using 1;
   simp [id,function.comp];ring },
 have ht:=has_deriv_at_iff_tendsto_slope.mp hd,
 have hi:=ht.inv₀ hb,
 simpa [slope_fun_def_field,div_eq_mul_inv,mul_comm] using hi
end

theorem direct_bilinear_variation {E : Type*} [add_comm_group E] [module ℝ E]
 (B : E → E → ℝ)
 (left : ∀ (j v x : E) (s : ℝ), B (j+s • v) x=B j x+s*B v x)
 (right : ∀ (x j v : E) (s : ℝ), B x (j+s • v)=B x j+s*B x v)
 (j v : E) (t : ℝ) :
 B (j+t • v) (j+t • v)/2 =
 B j j/2+t*((B j v+B v j)/2)+t^2*B v v/2 :=
by rw [left,right,right];ring

theorem direct_doubled_variation (retarded noise j : ℝ) :
 has_deriv_at (λ d : ℝ,d*retarded*j+noise*d^2/2) (retarded*j) 0 :=
begin
 have hd := ((((has_deriv_at_id (0:ℝ)).mul_const retarded).mul_const j).add
     ((((has_deriv_at_id (0:ℝ)).pow 2).const_mul noise).div_const 2)),
 convert hd using 1;simp [id];ring
end

theorem direct_spectral_noise (n loss : ℝ) (hf : 0≤n+loss) (hr : 0≤n-loss) :
 |loss|≤n := abs_le.mpr ⟨by linarith,by linarith⟩

theorem reference_fock_one (a ac b bc : ℂ) (ha : ac≠0)
 (h : a*ac-b*bc=1) : a-b*(bc/ac)=1/ac :=
begin field_simp [ha],linear_combination h end

theorem reference_pulse_reversal (a b c d : ℂ) :
 complex.norm_sq (b*c-a*d)=complex.norm_sq (a*d-b*c) :=
by rw [←neg_sub,complex.norm_sq_neg]

theorem reference_quiet_update (w v : ℝ) (n : ℕ) (hn : 1-w+w*v^n≠0) :
 (1-w+w*v^n)*(w*v^n/(1-w+w*v^n))=w*v^n := by field_simp [hn];ring

theorem front_neutral_leading (d b : ℝ) (r m : ℕ) (hr : r<m) :
 front_walk d b r (m:ℤ)-front_walk d b r (r:ℤ)= -b^r :=
by rw [front_walk_above d b r (m:ℤ) (by exact_mod_cast hr),front_walk_edge,zero_sub]

theorem front_neutral_before (d b : ℝ) (n r m : ℕ) (hn : n<r) (hr : r<m) :
 front_walk d b n (m:ℤ)-front_walk d b n (r:ℤ)=0 :=
begin
 have hm : n<m := lt_trans hn hr,
 rw [front_walk_above d b n (m:ℤ) (by exact_mod_cast hm),
     front_walk_above d b n (r:ℤ) (by exact_mod_cast hn),sub_self]
end

theorem front_stress_exchange (a dm dp qm q qp j : ℝ) (ha : a≠0) :
 a*(-(dp-dm)/a^2-j/a)*q-(dp*(qp-q)+dm*(q-qm))/(2*a)
 +dp*(qp+q)/(2*a)-dm*(q+qm)/(2*a)= -j*q :=
by field_simp [ha];ring

theorem reference_two_edge_neutral {ι : Type*} [decidable_eq ι] (a b c d : ι) (hab : a≠b)
 (balance : ∀ x, (if x=a then (1:ℤ) else 0)+(if x=c then 1 else 0)=
                 (if x=b then 1 else 0)+(if x=d then 1 else 0)) : a=d ∧ b=c :=
begin
 have first : a=d,
 { by_contra h,have ha:=balance a,simp only [if_pos rfl,if_neg hab,if_neg h] at ha,
   by_cases hac : a=c,{ rw [if_pos hac] at ha,norm_num at ha },{ rw [if_neg hac] at ha,norm_num at ha } },
 refine ⟨first,_⟩,subst d,by_contra h,have hb:=balance b,
 simp only [if_pos rfl,if_neg (ne.symm hab),if_neg h] at hb,norm_num at hb
end

theorem reference_radial_derivative (r g : ℝ) (hr : r≠0) :
 has_deriv_at (λ z:ℝ,6*g/z^4) (-24*g/r^5) r :=
begin
 have hd := (has_deriv_at_const r (6*g)).div ((has_deriv_at_id r).pow 4) (pow_ne_zero 4 hr),
 convert hd using 1;simp [id];field_simp [hr];ring
end

-- Lifetimes of angular momentum sectors driven by a three-dimensional STF tide.
private def ix (i j : fin 3) : ℤ := if i=j then 1 else 0
private def shear_slot (a b i j : fin 3) : ℤ := ix a i*ix b j+ix b i*ix a j
private def axial_slot (i j : fin 3) : ℤ := ix i j*(if i=2 then 2 else -1)
private def plus_slot (i j : fin 3) : ℤ := ix i j*(ix i 0-ix i 1)
-- Multiplication by six clears the squared normalizations of all five modes.
theorem record_stf_frame : ∀ i j k l : fin 3,
 axial_slot i j*axial_slot k l+3*(plus_slot i j*plus_slot k l+
 shear_slot 0 1 i j*shear_slot 0 1 k l+shear_slot 0 2 i j*shear_slot 0 2 k l+
 shear_slot 1 2 i j*shear_slot 1 2 k l) =
 3*(ix i k*ix j l+ix i l*ix j k)-2*ix i j*ix k l := by exact dec_trivial

theorem record_swap_reduction (p q f z : ℝ) :
 -(p-q)^2/4*(f+3*z-4)*f=(p-q)^2/4*(4*f-f^2-3*z*f) := by ring

theorem record_sector_flux (s c d : ℝ) :
 s*c^2/3*5=5*s*c^2/3 ∧ 5*(3*s*d^2/4)=3*(5*s*d^2/4) ∧
 (s*d^2/4*(4-1-3)=0) ∧
 (s*d^2/4*(4-1-0)=3*s*d^2/4) ∧
 (s*d^2/4*(-4-1-0)= -(5*s*d^2/4)) :=
by refine ⟨by ring,by ring,by ring,by ring,by ring⟩

theorem record_second_step (p₂ p₁ : ℝ → ℝ) (u w z : ℝ)
 (h₂ : has_deriv_at p₂ u 0) (h₁ : has_deriv_at p₁ 0 0) :
 has_deriv_at (λ t,w*p₂ t-z*p₁ t) (u*w) 0 :=
begin convert (h₂.const_mul w).sub (h₁.const_mul z) using 1;ring end

theorem record_stationary_mass (u v w z : ℝ) (h₁ : u=5*v) (h₂ : 3*z=5*w) :
 -u+5*v=0 ∧ u-5*(v+w)+3*z=0 ∧ 5*w-3*z=0 := by refine ⟨by linarith,by linarith,by linarith⟩

theorem record_first_transform (s u v w f₂ f₀ : ℝ)
 (h₀ : (s+u)*f₀=u*f₂) (h₂ : (s+v+w)*f₂=w+v*f₀)
 (hd : s^2+(u+v+w)*s+u*w≠0) :
 f₂=w*(s+u)/(s^2+(u+v+w)*s+u*w) :=
begin apply (eq_div_iff hd).2,linear_combination (s+u)*h₂+v*h₀ end

theorem record_partial_transform (eta f r g : ℝ)
 (h : g=eta*f+(1-eta)*f*r*g) (hd : 1-(1-eta)*f*r≠0) :
 g=eta*f/(1-(1-eta)*f*r) :=
begin apply (eq_div_iff hd).2,linear_combination h end

theorem record_first_means (u v w t₀ t₂ : ℝ)
 (h₀ : u*(t₀-t₂)=1) (h₂ : (v+w)*t₂-v*t₀=1) (hu : u≠0) (hw : w≠0) :
 t₀-t₂=1/u ∧ t₂=(u+v)/(u*w) :=
begin
 split,{apply (eq_div_iff hu).2,linear_combination h₀},
 apply (eq_div_iff (mul_ne_zero hu hw)).2,linear_combination u*h₂+v*h₀
end

theorem record_partial_mean_ratio (eta u v w z m₂ m : ℝ)
 (hu : u≠0) (hw : w≠0) (he : eta≠0)
 (huv : u=5*v) (hwz : 3*z=5*w)
 (h₂ : m₂=(u+v)/(u*w))
 (renew : eta*(m*z)=m₂*z+1-eta) : m*z=3/eta-1 :=
begin
 have hf : m₂*z=2,
 { rw [h₂],have hz : z=5*w/3 := by linarith,
   have hv : v=u/5 := by linarith,rw [hz,hv],field_simp [hu,hw];ring },
 rw [hf] at renew,apply (eq_sub_iff_add_eq).2,apply (eq_div_iff he).2,
 linear_combination renew
end

theorem record_decay_exponent (rate t : ℝ) :
 has_deriv_at (λ x : ℝ,real.exp (-rate*x)) (-rate*real.exp (-rate*t)) t :=
begin convert (real.has_deriv_at_exp (-rate*t)).comp t ((has_deriv_at_id t).const_mul (-rate)) using 1;
 simp [id,function.comp];ring end

theorem record_acceleration_clock (g a delta : ℝ) :
 5*(16*g*a^5/(5*real.pi))*(delta/2)^2/4=g*a^5*delta^2/real.pi :=
by field_simp [real.pi_ne_zero];ring

theorem record_recoil_window (gs x y vol L : ℝ) (hg : gs≠0) (hv : vol≠0)
 (hL : L^2=real.pi*x/gs) :
 ((gs^2/(8*vol))*y^5*(x/(2*real.pi))^3*L/real.pi)^2=
 gs^3*x^7*y^10/(4096*real.pi^7*vol^2) :=
begin
 simp only [div_pow,mul_pow,hL],field_simp [hv,hg,real.pi_ne_zero];ring
end


-- Curvature contacts, vacuum stability and a self-supported plane-wave membrane.
-- The two radiative bivectors ux,uy pair only with vx,vy when indices are raised.
private def cm_block (a b c d : ℝ) : ℝ := a*c+b*d+b*d+(-a)*(-c)
theorem cm_null_curvature (a b c d : ℝ) :
 4*(cm_block a b 0 0 + cm_block 0 0 c d)=0 ∧
 4*(cm_block a b c d + cm_block c d a b)=16*(a*c+b*d) :=
by split;unfold cm_block;ring

theorem cm_helicity_rank (p x : ℝ) :
 cm_block p x p x=2*(p^2+x^2) ∧ cm_block p x (-x) p=0 :=
by split;unfold cm_block;ring

theorem cm_pair_cross_section (g k l s : ℝ) (hs : s≠0) :
 (g*(k^2*s^2/2)*(l^2*s^2/2))^2/(32*real.pi*s)=
 g^2*k^4*l^4*s^7/(512*real.pi) ∧
 2*(k^2*s^2/2)^2/(16*real.pi)=k^4*s^4/(32*real.pi) :=
by split;field_simp [real.pi_ne_zero,hs];ring

theorem cm_bright_dark (a z : ℝ) (h : 2*z^2=1) :
 (a*z+a*z)^2=4*(a^2/2) ∧ (a*z-a*z)^2=0 :=
begin split,{linear_combination (2*a^2)*h},{ring} end

theorem cm_pair_return (p eta : ℝ) :
 (1-eta)+eta*((1-p)^2+p^2)=1-2*eta*p*(1-p) := by ring

theorem cm_pole_matching (ga gb m s : ℝ) (hm : m≠0) (hs : m^2-s≠0) :
 (ga*gb/(m^2-s))^2*(1-s/m^2)^2=(ga*gb/m^2)^2 :=
by field_simp [hm,hs];ring

theorem cm_boost_volume_lower (p u : ℝ) (hp : 0≤p) (hu : 0<u) (h : u≤2*p) :
 p/4≤p^2/(2*u) :=
begin apply (le_div_iff (by linarith : 0<2*u)).2,nlinarith [mul_nonneg hp (sub_nonneg.mpr h)] end

theorem cm_boost_primitive (p : ℝ) : has_deriv_at (λ x:ℝ,x^2/8) (p/4) p :=
begin convert ((has_deriv_at_id p).pow 2).div_const 8 using 1;simp [id];ring end

theorem cm_plane_trace (a e : ℝ) :
 3*(a^2+e)+6*(a^2/4-e/2)=9*a^2/2 := by ring

theorem cm_tidal_force (a m e r : ℝ) :
 has_deriv_at (λ x:ℝ,m/2*x^2*((x-a)^2+e)) (m*r*((r-a)*(2*r-a)+e)) r :=
begin
 have hx := has_deriv_at_id r,
 convert (((hx.pow 2).const_mul (m/2)).mul (((hx.sub_const a).pow 2).add_const e)) using 1;
 simp [id];ring
end

theorem cm_work (a m : ℝ) (r v e : ℝ → ℝ) (t ed : ℝ)
 (hr : has_deriv_at r (v t) t) (he : has_deriv_at e ed t)
 (hv : has_deriv_at v (-(r t)*((r t-a)*(2*r t-a)+e t)) t) :
 has_deriv_at (λ u,m/2*(v u^2+r u^2*((r u-a)^2+e u))) (m/2*(r t)^2*ed) t :=
begin
 convert ((hv.pow 2).add ((hr.pow 2).mul (((hr.sub_const a).pow 2).add he))).const_mul (m/2) using 1;
 ring
end

theorem cm_fold (z : ℝ) :
 let f:ℝ:=(3+z)/4, s:ℝ:=(3-z)/4, h:ℝ:=(1-z^2)/8 in
 (f-1)*(2*f-1)+h=0 ∧ (s-1)*(2*s-1)+h=0 ∧
 s^2*((s-1)^2+h)/2-f^2*((f-1)^2+h)/2=z^3/32 :=
by dsimp;refine ⟨by ring,by ring,by ring⟩

theorem cm_vector_hessian (a r t : ℝ) :
 (a+r*t)^2+r*(a-r)*t-(a-r)*(a-2*r)=r*(t+1)*(r*t+3*a-2*r) := by ring

theorem cm_physical_spectra (a r j : ℝ) :
 r*((-j-1)+1)*(r*(-j-1)+3*a-2*r)=r*j*((j+3)*r-3*a) ∧
 r*((-1)+1)*(r*(-1)+3*a-2*r)=0 := by split;ring

theorem cm_hard_modes (a r j : ℝ) (ha : 0<a) (hr : 3*a/4≤r) (hj : 2≤j) :
 0<r*j*((j+3)*r-3*a) :=
begin
 have hpos : 0<r := by linarith,
 have hjpos : 0<j := by linarith,
 apply mul_pos (mul_pos hpos hjpos) _,
 nlinarith [mul_nonneg (sub_nonneg.mpr hj) (le_of_lt hpos)]
end

theorem cm_bounce_factor (f y : ℝ) :
 let h:ℝ:= -(f-1)*(2*f-1) in
 y^2*((y-1)^2+h)-f^2*((f-1)^2+h)=(y-f)^2*((y-(1-f))^2-(1-f)) :=
by dsimp;ring

theorem cm_bounce_width (z b : ℝ) (h : b^2=(1-z)/4) :
 ((1+z)/2-b)*((1+z)/2+b)=z*(3+z)/4 := by nlinarith

theorem cm_orbit_mirror (a r d : ℝ) (ha : 0≤a) (hr : r≤d) :
 (a-r)^2*((a-r)-a)^2=r^2*(r-a)^2 ∧
 a*(a-2*d)≤(a-r)^2-r^2 ∧
 (a-r)*((a-r)-a)*(2*(a-r)-a)= -(r*(r-a)*(2*r-a)) :=
begin refine ⟨by ring,_,by ring⟩,nlinarith [mul_nonneg ha (sub_nonneg.mpr hr)] end

theorem cm_trapped_energy (r d : ℝ) (hd : 0<d) (hm : d<1/2)
 (hr : d<r) (hhalf : r≤1/2) :
 d^2*(1-d)^2<r^2*(1-r)^2 :=
begin
 have hdiff : d*(1-d)<r*(1-r),
 { nlinarith [mul_pos (sub_pos.mpr hr) (show 0<1-r-d,by linarith)] },
 have hsum : 0<r*(1-r)+d*(1-d) := by
 { apply add_pos;apply mul_pos;linarith },
 nlinarith [mul_pos (sub_pos.mpr hdiff) hsum]
end

theorem cm_equal_work : (1/2:ℝ)*(1/4)^2*(1/4-1)^2=9/512 ∧
 (1/2:ℝ)*(3/4)^2*(3/4-1)^2=9/512 := by norm_num

theorem cm_work_readout (a m r v e ed : ℝ) :
 m/2*((a-r)^2-r^2)*ed -
 (m/2*((-2*(a-r)*v-2*r*v)*e+((a-r)^2-r^2)*ed))=m*a*e*v := by ring

theorem cm_floquet_blocks (t : ℝ) :
 (6+4*t+t^2/2)-(3*t)^2/6=6+4*t-t^2 ∧
 (t^2/2-2*t)/2-(3*t)^2/4= -2*t^2-t ∧
 (-2*t^2-t)^2-(6+4*t-t^2)^2=3*(t-2)*(t+1)*(t+2)*(t+3) :=
by refine ⟨by ring,by ring,by ring⟩

theorem cm_j_three_instability :
 (3:ℝ)*(3-2)*(3+1)*(3+2)*(3+3)=360 ∧
 (3:ℝ)*(-4-2)*(-4+1)*(-4+2)*(-4+3)=108 := by norm_num

theorem cm_partition_action (n k a g : ℝ) :
 let D:ℝ:=n*(n^2-1)-k*(k^2-1)-(n-k)*((n-k)^2-1) in
 D=3*n*k*(n-k) ∧ a^3*D*g/24=a/3*(a^2*D*g/8) :=
by dsimp;split;ring

theorem cm_one_unit_fraction (n : ℝ) (h : 1<n) :
 3*n*(n-1)/(n*(n^2-1))=3/(n+1) :=
begin
 have h1 : n≠0 := by linarith,
 have h2 : n^2-1≠0 :=
 ne_of_gt (by nlinarith [mul_pos (show 0<n-1,by linarith) (show 0<n+1,by linarith)]),
 have h3 : n+1≠0 := by linarith,field_simp [h1,h2,h3];ring
end

theorem cm_susceptibility (m a f z w : ℝ) (hw : w≠0) (hf : f≠0) (ha : a≠0) (hz : z≠0)
 (root : w^2=a^2*f*z) : m*(a*f)^2/w^2=m*f/z :=
begin rw [root],field_simp [ha,hf,hz];ring end

theorem cm_soft_filter (m r w b : ℝ) (hw : w≠0) :
 (m*r^2/(2*w))*(b*w^5)^2=m*r^2*b^2*w^9/2 := by field_simp [hw];ring

theorem cm_spectral_moment (w : ℝ) :
 w^3*w^8/3-4*w^5*w^6/5+6*w^7*w^4/7-4*w^9*w^2/9+w^11/11=
 128*w^11/3465 := by ring

theorem cm_radial_measure (w x : ℝ) :
 has_deriv_at (λ y:ℝ,w^8*y^3/3-4*w^6*y^5/5+6*w^4*y^7/7-4*w^2*y^9/9+y^11/11)
 (x^2*(w^2-x^2)^4) x :=
begin
 have h:=has_deriv_at_id x,
 convert ((((((h.pow 3).const_mul (w^8)).div_const 3).sub
 (((h.pow 5).const_mul (4*w^6)).div_const 5)).add
 (((h.pow 7).const_mul (6*w^4)).div_const 7)).sub
 (((h.pow 9).const_mul (4*w^2)).div_const 9)).add ((h.pow 11).div_const 11) using 1;
 simp [id];ring
end


theorem cm_two_spacelike_insertions (k w q : ℝ) (hw : 0<w) (hq : w<q) :
 (2*k^2*(w*(q-w))^2)^2/(q-w)^2+(2*k^2*(w*(q+w))^2)^2/(q+w)^2 =
 8*k^4*w^4*(q^2+w^2) :=
begin
 have hm : q-w≠0 := by linarith,
 have hp : q+w≠0 := by linarith,
 field_simp [hm,hp];ring
end

theorem cm_double_source_kinematics (w q : ℝ) (hw : 0<w) (hq : w<q) :
 0<q^2-w^2 ∧ 0<(w+w)^2-(q-q)^2 :=
begin
 split,{nlinarith [mul_pos (sub_pos.mpr hq) (show 0<q+w,by linarith)]},
 nlinarith [mul_pos hw hw]
end

theorem cm_null_transfer (c : ℝ) (f₃ b : ℝ → ℝ) (u v f₄ bv : ℝ)
 (hf : has_deriv_at f₃ f₄ u) (hb : has_deriv_at b bv v) :
 has_deriv_at (λ x,c*f₃ x*b v) (c*f₄*b v) u ∧
 has_deriv_at (λ x,c*f₄*b x) (c*f₄*bv) v :=
begin
 split,{convert (hf.const_mul c).mul_const (b v) using 1},
 convert hb.const_mul (c*f₄) using 1
end

theorem cm_worldline_prefactor (k w : ℝ) :
 (k^4/(32*real.pi))*(4*real.pi/(2*real.pi)^3)*(128*w^11/3465)=
 2*k^4*w^11/(3465*real.pi^3) ∧
 2*k^4/(3465*real.pi^3)*60=8*k^4/(231*real.pi^3) :=
by split;field_simp [real.pi_ne_zero];ring

theorem cm_spinodal_gaps (a e r j : ℝ) (ha : 0<a) (he : e≤a^2/8)
 (hr : 3*a/4≤r) (hu : r≤a) (hj : 0≤j) :
 0<r*(j+1)*(r*j+3*a-2*r) ∧ 0<r^2*j*(j+1)+a^2/4-e/2 :=
begin
 have hpos : 0<r := by linarith,
 have hjs : 0<j+1 := by linarith,
 split,
 { apply mul_pos (mul_pos hpos hjs),nlinarith [mul_nonneg (le_of_lt hpos) hj] },
 have hterm : 0≤r^2*j*(j+1) := mul_nonneg (mul_nonneg (sq_nonneg _) hj) hjs.le,
 nlinarith [mul_pos ha ha]
end

theorem cm_floquet_virtual (t : ℝ) :
 let p:ℝ:=3*t, c:ℝ:=6+4*t+t^2/2, b:ℝ:=t^2/2-2*t in
 (-4+1)*(p/6)+p/2=0 ∧ 1*(-p/2)+p/2=0 ∧
 c+p/2*(-p/2+p/6)=6+4*t-t^2 ∧
 b/2+p/2*(-p/2)= -2*t^2-t :=
by dsimp;refine ⟨by ring,by ring,by ring,by ring⟩

theorem cm_floquet_secular (d h l : ℝ) (he : 4*l^2=h^2-d^2) :
 d^2+(2*l)^2-h^2=0 := by nlinarith

theorem cm_spherical_scale (n R p a ell : ℝ) (hn : n≠0) (hR : R≠0)
 (hp : p=n/R) :
 n*(n^2-1)/4*ell^6/R^3*a^3=(1-1/n^2)*(a*ell^2*p)^3/4 :=
begin rw [hp],field_simp [hn,hR];ring end


theorem cm_chiral_contacts (xp xm zp zm e o : ℝ) :
 e*(xp+xm)*(zp+zm)-o*(xp-xm)*(zp-zm)=
 (e-o)*(xp*zp+xm*zm)+(e+o)*(xp*zm+xm*zp) := by ring

theorem cm_polarized_quartic (p m z y b c t : ℝ) :
 (p+2*t*z+t^2*b)*(m+2*t*y+t^2*c)=
 p*m+2*t*(p*y+m*z)+t^2*(p*c+m*b+4*z*y)+
 2*t^3*(z*c+y*b)+t^4*b*c := by ring

theorem cm_centered_quartic (p m z y b c : ℝ) :
 (p-2*z+b)*(m-2*y+c)=
 p*m-2*(p*y+m*z)+(p*c+m*b+4*z*y)-2*(z*c+y*b)+b*c := by ring

theorem cm_chiral_matching (same cross a : ℝ) (hs : 4*same=a) (hc : cross=a) :
 cross=4*same := by linarith

theorem cm_chiral_angle_ratio :
 ((1:ℝ)+(1/2)^8+(1/2)^8)/(1+(1/4)^8+(3/4)^8)=33024/36049 :=
by norm_num

theorem cm_all_plus_exclusion (e o n : ℝ) (hn : n≠0) (h : (e-o)*n=0) :
 e=o := sub_eq_zero.mp (or.resolve_right (mul_eq_zero.mp h) hn)


theorem cm_axial_curvature (x : ℝ) :
 (3/2:ℝ)*(x^2-1/3-1/3+3*(1/3)^2)=(3*x^2-1)/2 := by ring

theorem cm_rotor_legendre (x : ℝ) :
 ((3*x^2-1)/2)^2=1/5+2/7*((3*x^2-1)/2)+
 18/35*((35*x^4-30*x^2+3)/8) := by ring

theorem cm_rotor_centering (z : ℝ) :
 (1+1-2*z)^2=4+4*(z^2-2*z) := by ring

theorem cm_rotor_born_ratios :
 (((18/35:ℝ)^2/9)/((2/7)^2/5)=9/5) ∧
 (((18/35:ℝ)^2/9)/((2/7-2)^2/5)=1/20) := by norm_num

theorem cm_rotor_weighted_work :
 (6*((2/7:ℝ)^2/5)+20*((18/35)^2/9)=24/35) ∧
 (6*((2/7:ℝ)-2)^2/5+20*((18/35)^2/9)=144/35) := by norm_num

theorem cm_rotor_moments (x k : ℝ) :
 (1-x^2)*(3*x*(3*x^2-1+k))^2=
 9*((k-1)^2*x^2+(6*(k-1)-(k-1)^2)*x^4+
 (9-6*(k-1))*x^6-9*x^8) := by ring

theorem cm_rotor_mean_work (k : ℝ) :
 9*((k-1)^2/3+(6*(k-1)-(k-1)^2)/5+(9-6*(k-1))/7-9/9)=
 24/35+24*k/35+6*k^2/5 := by ring

theorem cm_rotor_phase_gradient (x t k : ℝ) :
 has_deriv_at (λ y:ℝ,t*(((3*y^2-1)/2)^2+k*((3*y^2-1)/2)))
 (t*(3*x*(3*x^2-1+k))) x :=
begin
 have hp:=((((has_deriv_at_id x).pow 2).const_mul 3).sub_const 1).div_const 2,
 convert ((hp.pow 2).add (hp.const_mul k)).const_mul t using 1;simp [id];ring;try {exact or.inl rfl}
end


-- A spherical gravitational interval, relative angular order, and resolved flux.
theorem fr_annular_primitive (G r : ℝ) (hr : r ≠ 0) :
 has_deriv_at (λ x : ℝ, -(2*G)/x^3) (6*G/r^4) r :=
begin
 have h := (has_deriv_at_const r (-(2*G))).div ((has_deriv_at_id r).pow 3)
    (show (id r)^3 ≠ 0, from pow_ne_zero _ hr),
 convert h using 1; simp [id]; field_simp [hr]; ring
end

theorem fr_kerr_inertia (G M : ℝ) (hg : G≠0) (hm : M≠0) :
  2*G/(2*G*M)^3=1/(4*G^2*M^3) := by field_simp [hg,hm];ring

theorem fr_three_energies (a b g q : ℝ) :
  ((a+b+g)/2)*q=a*q/2+b*q/2+g*q/2 := by ring

theorem fr_schwarzschild_commutator (r h s t : ℝ) (hr : r≠0) :
  3*((-h/(2*r^3))*s*(h/r^3)*t)^2=3*h^4*(s*t)^2/(4*r^12) :=
by field_simp [hr]; ring

theorem fr_commuting_transport {A B : Type*} [comm_group A] [group B]
 (f : A →* B) (u v : A) : f u * f v = f v * f u :=
by rw [←map_mul,←map_mul,mul_comm u v]

theorem fr_relative_quarter_turns (a : ℝ) :
 ((a-(-a/2))^2+((-a/2)-a)^2)=9*a^2/2 := by ring

theorem fr_density_square (f g df dg x t : ℝ) :
 0 ≤ (df^2+dg^2)-t*x*(2*(f*df+g*dg))+t^2*x^2*(f^2+g^2) :=
by nlinarith only [sq_nonneg (df-t*x*f),sq_nonneg (dg-t*x*g)]

private lemma fr_cont_mul {g : ℝ → ℝ} (c : ℝ) (h : continuous g) :
 continuous (λ x,c*g x) := continuous_const.mul h

theorem fr_flux_integral {ρ d : ℝ → ℝ}
 (hr : continuous ρ) (hd : continuous d) (hder : ∀ x,has_deriv_at ρ (d x) x) :
 (∫ x in (0:ℝ)..1, x*(1-x^2)*d x) =
  2*(∫ x in (0:ℝ)..1, ((3*x^2-1)/2)*ρ x) :=
begin
 have deriv : ∀ x : ℝ, has_deriv_at (λ z:ℝ,(z-z^3)*ρ z)
   (x*(1-x^2)*d x-2*(((3*x^2-1)/2)*ρ x)) x,
 { intro x,have h:=((has_deriv_at_id x).sub ((has_deriv_at_id x).pow 3)).mul (hder x),
   convert h using 1; simp [id]; ring },
 have c₁ : continuous (λ x:ℝ,x*(1-x^2)*d x) := by continuity,
 have c₂ : continuous (λ x:ℝ,((3*x^2-1)/2)*ρ x) := by continuity,
 have ft := interval_integral.integral_eq_sub_of_has_deriv_at (λ x hx,deriv x)
    ((c₁.sub (fr_cont_mul 2 c₂)).interval_integrable 0 1),
 rw [interval_integral.integral_sub (c₁.interval_integrable _ _)
     ((fr_cont_mul 2 c₂).interval_integrable _ _),interval_integral.integral_const_mul] at ft,
 norm_num at ft, linarith, all_goals {apply_instance}
end

theorem fr_quadratic_integral {ρ d k : ℝ → ℝ} (hr : continuous ρ)
 (hd : continuous d) (hk : continuous k) (t : ℝ)
 (hpos : ∀ x ∈ set.Icc (0:ℝ) 1, 0 ≤ k x-t*x*d x+t^2*x^2*ρ x) :
 0 ≤ (∫ x in (0:ℝ)..1,(1-x^2)*k x) -
 t*(∫ x in (0:ℝ)..1,x*(1-x^2)*d x) +
 t^2*(∫ x in (0:ℝ)..1,x^2*(1-x^2)*ρ x) :=
begin
 have h₁ : continuous (λ x:ℝ,(1-x^2)*k x) := by continuity,
 have h₂ : continuous (λ x:ℝ,x*(1-x^2)*d x) := by continuity,
 have h₃ : continuous (λ x:ℝ,x^2*(1-x^2)*ρ x) := by continuity,
 rw [←interval_integral.integral_const_mul,←interval_integral.integral_const_mul,
     ←interval_integral.integral_sub (h₁.interval_integrable _ _) ((fr_cont_mul t h₂).interval_integrable _ _),
     ←interval_integral.integral_add ((h₁.sub (fr_cont_mul t h₂)).interval_integrable _ _)
       ((fr_cont_mul (t^2) h₃).interval_integrable _ _)],
 apply interval_integral.integral_nonneg (zero_le_one : (0:ℝ)≤1),
 intros x hx, have h:=mul_nonneg (show 0≤1-x^2,by nlinarith only [hx.1,hx.2,mul_nonneg (sub_nonneg.mpr hx.2) (show 0≤1+x,by linarith [hx.1])]) (hpos x hx),
 convert h using 1;ring, all_goals {apply_instance}
end

theorem fr_variance_integral {ρ : ℝ → ℝ} (hr : continuous ρ)
 (hp : ∀ x ∈ set.Icc (0:ℝ) 1,0 ≤ ρ x) (s : ℝ)
 (hn : (∫ x in (0:ℝ)..1,ρ x)=1)
 (hs : (∫ x in (0:ℝ)..1,(1-x^2)*ρ x)=s) :
 (∫ x in (0:ℝ)..1,x^2*(1-x^2)*ρ x) ≤ s*(1-s) :=
begin
 have h₁ : continuous (λ x:ℝ,x^2*(1-x^2)*ρ x) := by continuity,
 have h₂ : continuous (λ x:ℝ,(1-x^2)*ρ x) := by continuity,
 have hm := interval_integral.integral_mono_on (zero_le_one : (0:ℝ)≤1)
   (h₁.interval_integrable 0 1)
   (((fr_cont_mul (1-2*s) h₂).add (fr_cont_mul (s^2) hr)).interval_integrable 0 1)
   (show ∀ x∈set.Icc (0:ℝ) 1, x^2*(1-x^2)*ρ x≤(1-2*s)*((1-x^2)*ρ x)+s^2*ρ x,
    from λ x hx,by nlinarith only [mul_nonneg (sq_nonneg (1-x^2-s)) (hp x hx)]),
 rw [interval_integral.integral_add ((fr_cont_mul (1-2*s) h₂).interval_integrable _ _)
    ((fr_cont_mul (s^2) hr).interval_integrable _ _),interval_integral.integral_const_mul,
     interval_integral.integral_const_mul,hs,hn] at hm,
 linarith, all_goals {apply_instance}
end

theorem fr_normalized_order {ρ : ℝ → ℝ} (hr : continuous ρ)
 (hn : (∫ x in (0:ℝ)..1,ρ x)=1) :
 (∫ x in (0:ℝ)..1,(1-x^2)*ρ x) =
  2*(1-(∫ x in (0:ℝ)..1,((3*x^2-1)/2)*ρ x))/3 :=
begin
 have c : continuous (λ x:ℝ,((3*x^2-1)/2)*ρ x) := by continuity,
 have h : (λ x:ℝ,(1-x^2)*ρ x)=(λ x:ℝ,(2/3)*ρ x-(2/3)*(((3*x^2-1)/2)*ρ x)) :=
 by {funext x,ring},
 rw [h,interval_integral.integral_sub ((fr_cont_mul (2/3) hr).interval_integrable _ _)
      ((fr_cont_mul (2/3) c).interval_integrable _ _),interval_integral.integral_const_mul,
      interval_integral.integral_const_mul,hn], ring, all_goals {apply_instance}
end

theorem fr_precision_general {ρ d k : ℝ → ℝ} (hr : continuous ρ)
 (hd : continuous d) (hk : continuous k) (hder : ∀ x,has_deriv_at ρ (d x) x)
 (hp : ∀ x ∈ set.Icc (0:ℝ) 1,0 ≤ ρ x)
 (hpos : ∀ t x, x ∈ set.Icc (0:ℝ) 1 → 0 ≤ k x-t*x*d x+t^2*x^2*ρ x)
 (hn : (∫ x in (0:ℝ)..1,ρ x)=1) (v : ℝ)
 (hv : (∫ x in (0:ℝ)..1,((3*x^2-1)/2)*ρ x)=v) (lo : -(1:ℝ)/2<v) (hi : v<1) :
  9*v^2/(2*(1-v)*(1+2*v)) ≤ ∫ x in (0:ℝ)..1,(1-x^2)*k x :=
begin
 let s:=2*(1-v)/3, let a:=s*(1-s),
 have hs : (∫ x in (0:ℝ)..1,(1-x^2)*ρ x)=s := by rw [fr_normalized_order hr hn,hv],
 have ha : 0<a := mul_pos (show 0<s,by {dsimp [s],linarith})
    (show 0<1-s,by {dsimp [s],linarith}),
 have bound:=fr_variance_integral hr hp s hn hs,
 have hq:=fr_quadratic_integral hr hd hk (v/a) (hpos (v/a)),
 rw [fr_flux_integral hr hd hder,hv] at hq,
 have hmul:=mul_le_mul_of_nonneg_left bound (sq_nonneg (v/a)),
 change (v/a)^2* _ ≤ (v/a)^2*a at hmul,
 have hq' : 0 ≤ (∫ x in (0:ℝ)..1,(1-x^2)*k x) - v/a*(2*v)+(v/a)^2*a := by linarith,
 have hclear := (le_div_iff ha).mp (show 0 ≤ ((∫ x in (0:ℝ)..1,(1-x^2)*k x)*a-v^2)/a,
   by {convert hq' using 1,field_simp [ne_of_gt ha];ring}),
 apply (div_le_iff (mul_pos (mul_pos (by norm_num : (0:ℝ)<2) (sub_pos.mpr hi)) (by linarith : 0<1+2*v))).mpr,
 dsimp [a,s] at hclear,nlinarith only [hclear]
end

theorem fr_tail_weight (p q v : ℝ) (hv : 0<v) (hv1 : v<1) (hb : p*(9*v^2/(2*(1-v)*(1+2*v)))≤q) :
 p≤(2*(1-v)*(1+2*v))*q/(9*v^2) :=
begin
 have h : 0<2*(1-v)*(1+2*v) := by positivity <|> nlinarith [mul_pos (sub_pos.mpr hv1) (show 0<1+2*v,by linarith)],
 apply (le_div_iff (by positivity : 0<9*v^2)).mpr,
 rw [←mul_div_assoc] at hb,
 have hx:=(div_le_iff h).mp hb, nlinarith only [hx]
end

theorem fr_real_jump (a b c d : ℝ) :
 a*c+b*d-((a^2+b^2)+(c^2+d^2))/2=-((a-c)^2+(b-d)^2)/2 := by ring
theorem fr_read_edge (a b c d : ℝ) (h : (a-c)^2+(b-d)^2=0) : a=c ∧ b=d :=
by split; nlinarith [sq_nonneg (a-c),sq_nonneg (b-d)]
theorem fr_even_graph {α : Type*} (f : ℕ → α)
 (step : ∀ n,f (n+2)=f n) (bridge : f 1=f 0) : ∀ n,f n=f 0 :=
begin intro n,induction n using nat.strong_induction_on with n ih,
 cases n with k,{refl},cases k with m,{exact bridge},
 exact (step m).trans (ih m (by omega)) end

theorem fr_order_rates (alpha theta : ℝ) :
 -12*alpha*theta*(2/7)/5= -24*alpha*theta/35 ∧
 -12*alpha*theta*(-12/7)/5=144*alpha*theta/35 := by split;ring
theorem fr_gravity_lines :
 ((4/21:ℝ)/(2/15))*(7/3)^5=24010/243 ∧
 ((1/9072:ℝ)*(8/315))/((1/5)*(4/21))=1/13608 := by norm_num
theorem fr_cascade_flux (p q a b c : ℝ) :
 (-a*p-b*p)*10+(a*p-c*q)*3= -(7*a*p+10*b*p+3*c*q) := by ring
theorem fr_measure_counts :
 ((7/3:ℝ)^4*(9/5)/(1+9/5)=343/18) ∧ ((7/3:ℝ)^4*(1/20)/(1+1/20)=343/243) ∧
 ((7/3:ℝ)^3*(9/5)/(1+9/5)=49/6) ∧ ((7/3:ℝ)^3*(1/20)/(1+1/20)=49/81) := by norm_num

theorem fr_angular_spectrum :
 (2/7:ℝ)/5=2/35 ∧ (18/35:ℝ)/9=2/35 ∧ (-12/7:ℝ)/5=(-6)*(2/35) := by norm_num

theorem fr_signed_exchange (a b k : ℝ) (hk : k ≠ 0) (eta : ℝ) :
 k*((a+eta*b)/k)^2/(-2)+((a+eta*b)/k)*(a+eta*b)-
   (a^2+(eta*b)^2)/(2*k)=eta*a*b/k := by field_simp [hk];ring

theorem fr_no_common_sign (s a b : ℝ) (ha : 0≤a) (hb : 0≤b) :
 ¬(s*a=(-12/35:ℝ) ∧ s*b=(2/35:ℝ)) :=
begin rintro ⟨h₁,h₂⟩,by_cases hs : 0≤s,
 { nlinarith only [h₁,mul_nonneg hs ha] },
 { nlinarith only [h₂,mul_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge hs)) hb] } end

theorem fr_angular_rank (n : ℕ) (sample : (fin 14 → ℝ) →ₗ[ℝ] (fin n → ℝ))
 (read : (fin n → ℝ) →ₗ[ℝ] (fin 14 → ℝ))
 (h : function.injective (λ x,read (sample x))) : 14≤n :=
begin
 have h' : function.injective sample,
 { intros x y hxy, apply @h x y, change read (sample x)=read (sample y), rw [hxy] },
 simpa using linear_map.finrank_le_finrank_of_injective h'
end

def fr_xturn : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := λ v,(v.1,-v.2.2,v.2.1)
def fr_zturn : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := λ v,(-v.2.1,v.1,v.2.2)
theorem fr_noncommuting_directions :
 fr_xturn (fr_zturn (0,0,1))=(0,-1,0) ∧ fr_zturn (fr_xturn (0,0,1))=(1,0,0) :=
by norm_num [fr_xturn,fr_zturn]

theorem fr_order_monotone (u v : ℝ) (hu : 0≤u) (hv : u≤v) :
 0≤v^2*((1-u)*(1+2*u))-u^2*((1-v)*(1+2*v)) :=
begin have h:=mul_nonneg (sub_nonneg.mpr hv)
 (show 0≤v+u+v*u,by nlinarith [mul_nonneg (le_trans hu hv) hu]),
 nlinarith only [h] end
theorem fr_upper_edge (j : ℕ) :
 0<(9/4:ℝ)*∏ n in finset.range 4,((j:ℝ)+n+1)/(2*((j:ℝ)+n)+1) :=
begin apply mul_pos (by norm_num : (0:ℝ)<9/4), apply finset.prod_pos,
 intros n hn, apply div_pos;positivity end


theorem fr_monomial_avg (n : ℕ) : (∫ x in (0:ℝ)..1,x^n)=1/((n:ℝ)+1) :=
by rw [integral_pow];simp [nat.cast_add,nat.cast_one]
theorem fr_polynomial_norm (n : ℕ) :
 (∫ x in (0:ℝ)..1,((2:ℝ)*n+3)*x^(2*n+2))=1 :=
begin rw [interval_integral.integral_const_mul,fr_monomial_avg],
 push_cast, ring_nf, have ha:2*(n:ℝ)+3≠0:=by positivity,field_simp [ha];ring end
theorem fr_polynomial_order (n : ℕ) :
 (∫ x in (0:ℝ)..1,(((2:ℝ)*n+3)/2)*(3*x^(2*n+4)-x^(2*n+2)))=
  2*((n:ℝ)+1)/(2*n+5) :=
begin
 have hi : ∀ k:ℕ,interval_integrable (λ x:ℝ,x^k) volume 0 1 :=
  λ k,(continuous_id.pow k).interval_integrable 0 1,
 rw [interval_integral.integral_const_mul,
     interval_integral.integral_sub ((hi _).const_mul 3) (hi _),
     interval_integral.integral_const_mul,fr_monomial_avg,fr_monomial_avg],
 push_cast,have h₁:2*(n:ℝ)+2+1≠0:=by positivity,
 have h₂:2*(n:ℝ)+4+1≠0:=by positivity,
 have h₃:2*(n:ℝ)+5≠0:=by positivity, have h₄:2*(n:ℝ)+3≠0:=by positivity,ring_nf,field_simp [h₁,h₂,h₃,h₄];ring
end
theorem fr_polynomial_work (n : ℕ) :
 (∫ x in (0:ℝ)..1,(((2:ℝ)*n+3)*((n:ℝ)+1)^2)*(x^(2*n)-x^(2*n+2)))=
   2*((n:ℝ)+1)^2/(2*n+1) :=
begin
 have hi : ∀ k:ℕ,interval_integrable (λ x:ℝ,x^k) volume 0 1 :=
  λ k,(continuous_id.pow k).interval_integrable 0 1,
 rw [interval_integral.integral_const_mul,interval_integral.integral_sub (hi _) (hi _),
     fr_monomial_avg,fr_monomial_avg],
 push_cast,have h₁:2*(n:ℝ)+1≠0:=by positivity,
 have h₂:2*(n:ℝ)+2+1≠0:=by positivity,have h₃:2*(n:ℝ)+3≠0:=by positivity,ring_nf,field_simp [h₁,h₂,h₃];ring
end
theorem fr_sharp_error (n : ℝ) (hn : 0≤n) :
 3/2-(1-2*(n+1)/(2*n+5))*(2*(n+1)^2/(2*n+1))=
 (3/2)*(4*n+1)/((2*n+5)*(2*n+1)) ∧
 (3/2)*(4*n+1)/((2*n+5)*(2*n+1))≤3/(n+1) :=
begin
 have h₁:0<2*n+1:=by linarith,have h₂:0<2*n+5:=by linarith,
 have h₃:0<n+1:=by linarith,
 split,{ field_simp [ne_of_gt h₁,ne_of_gt h₂];ring },
 rw [div_le_div_iff (mul_pos h₂ h₁) h₃],nlinarith [sq_nonneg n]
end


theorem fr_squared_triangle {X : Type*} [pseudo_metric_space X] (x y z : X) :
 (dist x z)^2≤2*((dist x y)^2+(dist y z)^2) :=
begin
 have ht:=dist_triangle x y z,
 have hm:=mul_nonneg (sub_nonneg.mpr ht)
     (add_nonneg (add_nonneg (dist_nonneg : 0≤dist x y) (dist_nonneg : 0≤dist y z))
                 (dist_nonneg : 0≤dist x z)),
 nlinarith only [hm,sq_nonneg (dist x y-dist y z)]
end
theorem fr_three_strength_minimax {X : Type*} [pseudo_metric_space X] (x y z : X)
 (w e : ℝ) (hw : 0<w) (h₁ : (dist x y)^2≤(1+e)*w)
 (h₂ : (dist y z)^2≤(1+e)*w) (h₃ : (1-e)*(16*w)≤(dist x z)^2) : 3/5≤e :=
begin
 have h:=fr_squared_triangle x y z,
 by_contra hh,have hm:=mul_pos (sub_pos.mpr (lt_of_not_ge hh)) hw,
 nlinarith only [h,h₁,h₂,h₃,hm]
end
theorem fr_three_strength_attained (w : ℝ) (hw : 0≤w) :
 let t:=real.sqrt ((8/5)*w) in
 t^2-w=(3/5)*w ∧ (2*t)^2-16*w= -(3/5)*(16*w) :=
begin dsimp,have h:=real.sq_sqrt (show 0≤(8/5:ℝ)*w,by positivity),
 split; nlinarith only [h] end
theorem fr_self_counterterms (ax ay bx byval u v k : ℝ) :
 ((ax+bx+k*u*u)+(ay+byval+k*v*v)-(ax+byval+k*u*v)-(ay+bx+k*v*u))/2
    =k*(u-v)^2/2 := by ring
theorem fr_contact_contrast (x y g k : ℝ) (hk : k≠0) :
 -(k/2)*(g*(x-y)^2/k)^2+g*(g*(x-y)^2/k)*(x-y)^2=g^2*(x-y)^4/(2*k) :=
by field_simp [hk];ring
theorem fr_no_transition {α : Type*} (s : finset α) (a gap : α → ℝ)
 (hg : ∀ i∈s,0<gap i) (hs : ∑ i in s,(a i)^2/gap i=0) (i : α) (hi : i∈s) :
 a i=0 :=
begin
 have hn : ∀ i∈s,0≤(a i)^2/gap i := λ j hj,div_nonneg (sq_nonneg _) (le_of_lt (hg j hj)),
 have h:=(finset.single_le_sum hn hi),rw [hs] at h,
 have hz:=le_antisymm h (hn i hi),
 have hval:=(div_eq_zero_iff.mp hz).resolve_right (ne_of_gt (hg i hi)),
 nlinarith only [hval]
end
theorem fr_horizon_fraction (p G r v : ℝ) (hp : p≠0) (hg : G≠0) (hr : r≠0) :
 ((G/r^3)*v)/(r/(2*G))=2*p^2*v/(p*r^2/G)^2 :=
by field_simp [hp,hg,hr];ring


-- Two blocks of the ordinary matrix theory: contrast of velocity and resolved excitation.
theorem fr_cubic_phase_minimax {X : Type*} [pseudo_metric_space X] (x y z : X)
 (w e : ℝ) (hw : 0<w) (h₁ : (dist x y)^2≤(1+e)*w)
 (h₂ : (dist y z)^2≤(1+e)*w) (h₃ : (1-e)*(8*w)≤(dist x z)^2) : 1/3≤e :=
begin
 have h:=fr_squared_triangle x y z,
 apply (mul_le_mul_right hw).mp,linarith only [h,h₁,h₂,h₃]
end
theorem fr_cubic_phase_attained (w : ℝ) (hw : 0≤w) :
 let t:=real.sqrt ((4/3)*w) in t^2-w=w/3 ∧ (2*t)^2-8*w= -(8*w)/3 :=
begin dsimp,have h:=real.sq_sqrt (show 0≤(4/3:ℝ)*w,by positivity),
 split; nlinarith only [h] end
theorem fr_matrix_window (z : ℝ) :
 has_deriv_at (λ x:ℝ,x-2*x^3/3+x^5/5) ((1-z^2)^2) z :=
begin have h:=((has_deriv_at_id z).sub ((((has_deriv_at_id z).pow 3).const_mul 2).div_const 3)).add
   (((has_deriv_at_id z).pow 5).div_const 5),convert h using 1;simp [id];ring end
theorem fr_matrix_phase_coefficient :
 (15/16:ℝ)*(2*(1-2/3+1/5))=1 := by norm_num

def fr_reduced (u : ℝ) := 16*(1+7*u^2+7*u^4+u^6)/(1+u)^8
theorem fr_determinant_loss (u : ℝ) (hu : 1+u≠0) :
 1-((1-u)/(1+u))^8=u*fr_reduced u :=
by unfold fr_reduced;field_simp [hu];ring
theorem fr_elastic_doubling (u : ℝ) (hu : 1+u≠0) :
 2*((1-u)/(1+u))/(1+((1-u)/(1+u))^2)=(1-u^2)/(1+u^2) :=
begin have h₁ : 1+u^2≠0:=by positivity,
 have h₂ : 1+((1-u)/(1+u))^2≠0:=by positivity,
 apply (div_eq_div_iff h₂ h₁).mpr,field_simp [hu];ring end
theorem fr_reduced_cont : continuous_at fr_reduced 0 :=
begin
 have a : continuous (λ u:ℝ,16*(1+7*u^2+7*u^4+u^6)) := by continuity,
 have b : continuous (λ u:ℝ,(1+u)^8) := by continuity,
 exact a.continuous_at.div b.continuous_at (by norm_num)
end
theorem fr_reduced_zero : fr_reduced 0=16 := by norm_num [fr_reduced]
theorem fr_hit_ratio (u eta : ℝ) (hu : u≠0) (he : eta≠0) (hr : fr_reduced (u^2)≠0) :
 (eta*u*fr_reduced u)^2/(eta*u^2*fr_reduced (u^2))=eta*(fr_reduced u)^2/fr_reduced (u^2) :=
by field_simp [hu,he,hr];ring
theorem fr_hit_limit (eta : ℝ) :
 tendsto (λ u:ℝ,eta*(fr_reduced u)^2/fr_reduced (u^2)) (𝓝 0) (𝓝 (16*eta)) :=
begin
 have c₀ : continuous_at (λ x:ℝ,fr_reduced (x^2)) 0 :=
 begin
   have a : continuous (λ u:ℝ,16*(1+7*(u^2)^2+7*(u^2)^4+(u^2)^6)) := by continuity,
   have b : continuous (λ u:ℝ,(1+u^2)^8) := by continuity,
   exact a.continuous_at.div b.continuous_at (by norm_num)
 end,
 have c : continuous_at (λ u:ℝ,eta*(fr_reduced u)^2/fr_reduced (u^2)) 0 :=
 (continuous_at_const.mul (fr_reduced_cont.pow 2)).div c₀
   (by norm_num [fr_reduced]),
 convert c.tendsto using 1, norm_num [fr_reduced];ring
end
theorem fr_phase_log (q r : ℝ) (hq : q≠0) (hr : 0<r) :
 q*real.log (16/(real.exp (-real.pi/q)*r))=real.pi+q*real.log (16/r) :=
begin
 have he:=ne_of_gt (real.exp_pos (-real.pi/q)),
 rw [real.log_div (by norm_num : (16:ℝ)≠0) (mul_ne_zero he (ne_of_gt hr)),
     real.log_mul he (ne_of_gt hr),real.log_exp,real.log_div (by norm_num : (16:ℝ)≠0) (ne_of_gt hr)],
 field_simp [hq];ring
end
theorem fr_joint_phase_limit {ι : Type*} {l : filter ι} {q d k : ι → ℝ}
 (hn : ∀ i,q i≠0) (ha : tendsto (λ i,d i/(q i)^3) l (𝓝 1))
 (hb : tendsto (λ i,q i*k i) l (𝓝 real.pi)) :
 tendsto (λ i,d i*(k i)^3) l (𝓝 (real.pi^3)) :=
begin have h:=ha.mul (hb.pow 3), rw [one_mul] at h,
 convert h using 1,funext i,field_simp [hn i];ring end


def fr_loss_v (q : ℝ) := real.exp (-real.pi/q)*fr_reduced (real.exp (-real.pi/q))
theorem fr_soft_parameter {ι : Type*} {l : filter ι} {q : ι → ℝ}
 (h : tendsto q l (𝓝[>] (0:ℝ))) (a : ℝ) (ha : 0<a) :
 tendsto (λ i,real.exp (-a/q i)) l (𝓝 0) :=
begin
 have hi : tendsto (λ i,(q i)⁻¹) l at_top := tendsto_inv_zero_at_top.comp h,
 simpa only [div_eq_mul_inv,function.comp_app] using
   real.tendsto_exp_at_bot.comp (hi.neg_const_mul_at_top (neg_lt_zero.mpr ha))
end
theorem fr_reduced_positive (u : ℝ) (hu : 0≤u) : 0<fr_reduced u :=
by unfold fr_reduced;positivity
theorem fr_physical_hit_limit {ι : Type*} {l : filter ι} {q : ι → ℝ} (hp : ∀ i,0<q i)
 (h : tendsto q l (𝓝[>] (0:ℝ))) (eta : ℝ) (he : 0<eta) :
 tendsto (λ i,(eta*fr_loss_v (2*q i))^2/(eta*fr_loss_v (q i))) l (𝓝 (16*eta)) :=
begin
 let u:=λ i,real.exp (-(real.pi/2)/q i),
 have hlim:= (fr_hit_limit eta).comp (fr_soft_parameter h (real.pi/2) (half_pos real.pi_pos)),
 refine hlim.congr (λ i,_),
 have hd:real.exp (-real.pi/(2*q i))=u i := by { dsimp [u],congr' 1,field_simp [ne_of_gt (hp i)];ring },
 have hsq:real.exp (-real.pi/q i)=(u i)^2 := by
 { dsimp [u],rw [pow_two,←real.exp_add],congr' 1,field_simp [ne_of_gt (hp i)];ring },
 have hpos:0<u i:=real.exp_pos _,
 change eta*(fr_reduced (u i))^2/fr_reduced ((u i)^2) =
   (eta*fr_loss_v (2*q i))^2/(eta*fr_loss_v (q i)),
 unfold fr_loss_v,rw [hd,hsq],symmetry,
 simpa only [mul_assoc] using fr_hit_ratio (u i) eta (ne_of_gt hpos) (ne_of_gt he)
   (ne_of_gt (fr_reduced_positive _ (sq_nonneg _)))
end
theorem fr_physical_phase_limit {ι : Type*} {l : filter ι} {q d : ι → ℝ} (hp : ∀ i,0<q i)
 (h : tendsto q l (𝓝[>] (0:ℝ))) (phase : tendsto (λ i,d i/(q i)^3) l (𝓝 1)) :
 tendsto (λ i,d i*(real.log (16/fr_loss_v (q i)))^3) l (𝓝 (real.pi^3)) :=
begin
 apply fr_joint_phase_limit (λ i,ne_of_gt (hp i)) phase,
 have hu:=fr_soft_parameter h real.pi real.pi_pos,
 have hr:=fr_reduced_cont.tendsto.comp hu,
 rw [fr_reduced_zero] at hr,
 have hd : tendsto (λ i,(16:ℝ)/fr_reduced (real.exp (-real.pi/q i))) l (𝓝 (16/16)) :=
 tendsto_const_nhds.div hr (by norm_num),
 have hl:= (real.continuous_at_log (show (16:ℝ)/16≠0,by norm_num)).tendsto.comp hd,
 have hq : tendsto q l (𝓝 0) := h.mono_right nhds_within_le_nhds,
 have hs := (hq.mul hl).const_add real.pi,
 rw [zero_mul,add_zero] at hs,
 exact hs.congr (λ i,(fr_phase_log (q i) _ (ne_of_gt (hp i))
   (fr_reduced_positive _ (real.exp_pos _).le)).symm)
end

-- A matrix contact, a tidal echo and a conserved absorption doublet.
theorem mx_normal_form (a b qa qb pa pb : ℝ) :
 (1-a)*(qa+qb)^2/2+(1+a)*(qa-qb)^2/2+
 (1+b)*(pa+pb)^2/2+(1-b)*(pa-pb)^2/2 =
 qa^2+qb^2+pa^2+pb^2-2*a*qa*qb+2*b*pa*pb := by ring
theorem mx_spectrum_sq (sa ca sb cb : ℝ) (ha : sa^2+ca^2=1)
 (hb : sb^2+cb^2=1) :
 (2*sa*cb)^2+(2*ca*sb)^2=2-2*(ca^2-sa^2)*(cb^2-sb^2) :=
by linear_combination 2*(sb^2+cb^2)*ha + 2*hb
theorem mx_resolution (t sa cb : ℝ) (hs : sa≠0) (hc : cb≠0) :
 (t*sa/cb)*(t*cb/(4*sa))=t^2/4 := by field_simp; ring
theorem mx_quadratic_floor (a b q p : ℝ) :
 (a*q)^2+(b*p)^2-2*a*b*q*p=(a*q-b*p)^2 := by ring
theorem mx_vector_threshold (d f g : ℝ) :
 min (d^2+f+g-2*f) (d^2+f+g-2*g)=d^2-abs (f-g) :=
begin by_cases h:f≤g,
 { rw [abs_of_nonpos (sub_nonpos.mpr h),min_eq_right (show d^2+f+g-2*g ≤ d^2+f+g-2*f,by linarith)],ring },
 { rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h)),min_eq_left (show d^2+f+g-2*f ≤ d^2+f+g-2*g,by linarith)],ring } end
theorem mx_spin_trace (a b : ℝ) :
 4+2*(2*a^2-1)+2*(2*b^2-1)-8*a*b=4*(a-b)^2 := by ring
theorem mx_gaussian_overlap (t : ℝ) :
 3-4*t+t^4=(1-t)^2*(t^2+2*t+3) := by ring
theorem mx_fourth_average (x : ℝ) :
 6*(real.sin (x/2))^4 = (3:ℝ)/4*(3-4*real.cos x+real.cos (2*x)) :=
begin
 have h : real.cos x=1-2*(real.sin (x/2))^2 :=
 calc real.cos x=real.cos (2*(x/2)) : by congr' 1;ring
 ... = _ : by rw [real.cos_two_mul'];nlinarith [real.sin_sq_add_cos_sq (x/2)],
 rw [real.cos_two_mul,h],ring
end
theorem mx_aux_static (m g j z : ℝ) (h : m≠0) :
 -m^2*z^2/2+g*z*j=g^2*j^2/(2*m^2)-m^2*(z-g*j/m^2)^2/2 :=
by field_simp;ring
theorem mx_reciprocity (a b : ℝ) : 2*(a-b)+2*(b-a)=0 := by ring
theorem mx_mirror (a : ℝ) : (a-(-a))^2-(a-a)^2=4*a^2 := by ring
theorem mx_partner {w y p : ℝ → ℝ} {u a da v dv om : ℝ}
 (hw : has_deriv_at w da u) (hy : has_deriv_at y dv u)
 (hp : has_deriv_at p (-(om^2+da-a^2)*v) u)
 (wa : w u=a) (yv : y u=v) :
 has_deriv_at (λ t,p t+w t*y t) (-om^2*v+a*(dv+a*v)) u :=
begin convert hp.add (hw.mul hy) using 1,rw [wa,yv],ring end
theorem mx_partner_back {w z y : ℝ → ℝ} {u a da v p om : ℝ}
 (hw : has_deriv_at w da u) (hz : has_deriv_at z (-om^2*v+a*p) u)
 (hy : has_deriv_at y (p-a*v) u) (wa : w u=a) (zv : z u=p) :
 has_deriv_at (λ t,-om^2*y t+w t*z t) (-(om^2-da-a^2)*p) u :=
begin convert (hy.const_mul (-om^2)).add (hw.mul hz) using 1,rw [wa,zv],ring end
theorem mx_asymptotic_sign (om : ℂ) (h : om≠0) (a b : ℂ) :
 ((-complex.I*om)*a+(complex.I*om)*b)/(-complex.I*om)=a-b :=
by field_simp [h,complex.I_ne_zero];ring
theorem mx_echo_composition (a b c : ℂ) :
 a*c*b+b*(star_ring_end ℂ (a*c))=b*(a*c+star_ring_end ℂ (a*c)) := by ring
theorem mx_geometric_return (l n : ℝ) (hn : 0≤n) (hl : l=n/(1+n)) :
 (1-l)/(1+l)=1/(1+2*n) :=
begin rw [hl],apply (div_eq_div_iff (show 1+n/(1+n)≠0,by positivity) (show 1+2*n≠0,by linarith)).2,field_simp [show 1+n≠0,by linarith];ring end
theorem mx_echo_work (eta om n : ℝ) :
 eta*2*om*((1+2*n)*n+n)=4*eta*om*n*(1+n) := by ring
theorem mx_diffusive_variance (k x p xp : ℝ) (pure : x*p-xp^2=1/4) :
 ((k*x+p)^2-k)/2=(k*x-p)^2/2+2*k*xp^2 :=
by linear_combination 2*k*pure
theorem mx_monitor_work (a x p xp slope gam : ℝ) :
 (slope*x + a*(2*xp+gam*(p-a*x)) + (-2*a*xp-gam*a*(p-a*x)))/2
 = slope*x/2 := by ring
theorem mx_einstein_sandwich : ((9:ℝ)/40)/(1+9/40)=9/49 := by norm_num
theorem mx_echo_weak_orders (g a s r v : ℝ) :
 (g*(a*s)^2*(a*v)^2=g*a^4*(s*v)^2) ∧
 (g*(a*r)^4*(a*v)^2=g*a^6*r^4*v^2) := by split;ring
theorem mx_recoil (mass gap : ℝ) (hm : mass≠0) :
 (mass+(gap+gap^2/(2*mass)))^2=(mass+gap)^2+(gap+gap^2/(2*mass))^2 :=
by field_simp;ring
theorem mx_pointer (g y z : ℝ) (hg : g≠0) :
 -2*g*(y^2+z^2)=0 ↔ y=0 ∧ z=0 :=
begin split,
 { intro h,have h' : y^2+z^2=0 := (mul_eq_zero.mp h).resolve_left (mul_ne_zero (by norm_num) hg),
   exact ⟨by nlinarith [sq_nonneg z,sq_nonneg y],by nlinarith [sq_nonneg y,sq_nonneg z]⟩ },
 { rintro ⟨rfl,rfl⟩, ring } end
theorem mx_parallel_fit (g d t : ℝ) (h : g^2+d^2≠0) :
 (g-t*g)^2+(t*d)^2=(g^2+d^2)*(t-g^2/(g^2+d^2))^2+
  g^2*d^2/(g^2+d^2) := by field_simp;ring
theorem mx_detuned_rate (g d om : ℝ) (h : g^2+d^2≠0) (ho : om≠0) :
 2*((g^2/(g^2+d^2))^2*(g^2+d^2))/om=2*g^4/(om*(g^2+d^2)) :=
by field_simp;ring
theorem mx_resonant_absorption (pump material total : ℝ) (hp : total=pump+material)
 (p : ℝ) : (1-p)*total+p*(pump+material)=total := by rw [hp];ring

theorem mx_purity_of_pairs (l : ℝ) (hl : 0≤l) (hs : l<1) :
 (∑' j:ℕ,((1-l)*l^j)^2)=(1-l)/(1+l) :=
begin
 have h2:l^2<1:=by nlinarith [mul_pos (sub_pos.mpr hs) (show 0<1+l,by linarith)],
 simp_rw [mul_pow,show ∀j:ℕ,(l^j)^2=(l^2)^j,from λ j,pow_right_comm l j 2],
 rw [tsum_mul_left,tsum_geometric_of_lt_1 (sq_nonneg l) h2],
 field_simp [show 1-l^2≠0,by linarith,show 1+l≠0,by linarith];ring
end
theorem mx_pair_form (x z : ℝ) :
 ((x+z)^2-(x-z)^2)/2=2*x*z := by ring

theorem mx_damped_coherence (omega rate t : ℝ) :
 has_deriv_at (λ u:ℝ,real.exp (-rate*u)*real.cos (omega*u))
 (-(rate*real.cos (omega*t)+omega*real.sin (omega*t))*real.exp (-rate*t)) t :=
begin
 have he:has_deriv_at (λ u:ℝ,-rate*u) (-rate) t:=by simpa using (has_deriv_at_id t).const_mul (-rate),
 have hw:has_deriv_at (λ u:ℝ,omega*u) omega t:=by simpa using (has_deriv_at_id t).const_mul omega,
 convert he.exp.mul hw.cos using 1;ring
end
theorem mx_mode_infall (f g x y : ℝ) :
 (f*x-g*y)^4=(f*x)^4-4*(f*x)^3*(g*y)+6*(f*x)^2*(g*y)^2-4*(f*x)*(g*y)^3+(g*y)^4 := by ring
theorem mx_zero_linear_force (x y e : ℝ) :
 4*(e*x-e*y)^3=e^3*(4*(x-y)^3) := by ring
theorem mx_born_spread (g p : ℝ) :
 p*g^2+(1-p)*(-g)^2-(p*g+(1-p)*(-g))^2=4*g^2*p*(1-p) := by ring
theorem mx_doublet_fit_unique (g d t : ℝ) (hn : 0<g^2+d^2)
 (best : (g-t*g)^2+(t*d)^2=g^2*d^2/(g^2+d^2)) :
 t=g^2/(g^2+d^2) :=
begin rw [mx_parallel_fit _ _ _ (ne_of_gt hn)] at best,
 have h : (g^2+d^2)*(t-g^2/(g^2+d^2))^2=0:=by linarith,
 have h':=(mul_eq_zero.mp h).resolve_left (ne_of_gt hn),
 nlinarith [sq_nonneg (t-g^2/(g^2+d^2))]
end

theorem mx_diagonal_null :
 (volume.prod volume : measure (ℝ×ℝ)) {p : ℝ×ℝ | p.1=p.2}=0 :=
begin
 have ms : measurable_set {p : ℝ×ℝ | p.1=p.2} := (is_closed_eq continuous_fst continuous_snd).measurable_set,
 rw [measure.measure_prod_null ms],
 apply eventually_of_forall,intro x,
 have he : prod.mk x ⁻¹' {p : ℝ×ℝ | p.1=p.2}=({x}:set ℝ) :=
 by { ext y,change (x=y) ↔ y=x,exact eq_comm },
 change volume (prod.mk x ⁻¹' {p : ℝ×ℝ | p.1=p.2})=0,rw [he,measure_singleton], all_goals { apply_instance }
end
theorem mx_continuum_decay {α : Type*} [measurable_space α] (mu : measure α)
 (w : α → ℝ) (f : ℕ → α → ℝ) (hw : integrable w mu)
 (hm : ∀ n,ae_strongly_measurable (f n) mu)
 (hb : ∀ n,∀ᵐ x ∂mu,‖f n x‖≤w x)
 (ht : ∀ᵐ x ∂mu,∃ C : ℝ,∀ n : ℕ,0≤f n x ∧ f n x≤C*(1/((n:ℝ)+1))) :
 tendsto (λ n,∫ x,f n x ∂mu) at_top (𝓝 0) :=
begin
 have h : ∀ᵐ x ∂mu,tendsto (λ n,f n x) at_top (𝓝 (0:ℝ)) :=
 ht.mono (λ x hx,let ⟨c,hc⟩:=hx in
 squeeze_zero (λ n,(hc n).1) (λ n,(hc n).2) (by simpa using tendsto_one_div_add_at_top_nhds_0_nat.const_mul c)),
 simpa using tendsto_integral_of_dominated_convergence w hm hw hb h
end
theorem mx_resonance_unitarity (a b e : ℝ) :
 (e^2+(a+b)^2/4)-(e^2+(a-b)^2/4)=a*b := by ring
theorem mx_two_pass (p eta : ℝ) : 1-((1-eta)+eta*((1-p)^2+p^2))=2*eta*p*(1-p) := by ring
theorem mx_half_conversion (p : ℝ) : 1/2-2*p*(1-p)=2*(p-1/2)^2 := by ring
theorem mx_width_window (a b : ℝ) (h : a+b≠0) :
 1/2≤4*a*b/(a+b)^2 ↔ a^2-6*a*b+b^2≤0 :=
begin rw [le_div_iff (sq_pos_of_ne_zero _ h)], split;intro z;nlinarith end
theorem mx_reread (c : ℝ) (h : c*c=c) : c=0 ∨ c=1 :=
begin have h':c*(c-1)=0:=by nlinarith,rcases mul_eq_zero.mp h' with a|b,
 exact or.inl a,right,linarith end

theorem mx_private_silence (p q : ℝ) (h : 1-p*q≠0) :
 (1-p*q)*(p*(1-q)/(1-p*q))*(1-p*(1-q)/(1-p*q))=
 p*(1-p)*(1-q)/(1-p*q) := by field_simp;ring
theorem mx_private_loss (p a b : ℝ) (ha : 1-p*a≠0) (hb : 1-p*b≠0) :
 p*(1-p)*(1-b)/(1-p*b)-p*(1-p)*(1-a)/(1-p*a)=
 p*(1-p)^2*(a-b)/((1-p*b)*(1-p*a)) := by field_simp;ring
theorem mx_private_example :
 (1:ℝ)/2*(1-1/2)*(1-9/10)/(1-(1/2)*(9/10))=1/22 ∧
 (1:ℝ)/2*(1-1/2)*(1-1/10)/(1-(1/2)*(1/10))=9/38 := by norm_num
theorem mx_total_variance (m n va vb p : ℝ) :
 p*(va+m^2)+(1-p)*(vb+n^2)-(p*m+(1-p)*n)^2 =
 p*va+(1-p)*vb+p*(1-p)*(m-n)^2 := by ring
theorem mx_radial_redshift (s : ℝ) (hp : s≠1) (hn : s≠-1) :
 (1+s)/(1-s^2)=1/(1-s) :=
begin apply (div_eq_div_iff (show 1-s^2≠0,by
 { intro h,have q:(1-s)*(1+s)=0:=by nlinarith,
   rcases mul_eq_zero.mp q with a|b; [apply hp,apply hn];linarith })
 (show 1-s≠0,by intro h;apply hp;linarith)).2,ring end
theorem mx_sinc_bounds (x : ℝ) (h : 0<x) :
 |real.sin x/x|≤1 ∧ |real.sin x/x|≤1/x :=
begin
 rw [abs_div,abs_of_pos h],
 have ha : |real.sin x|≤x,
 { by_cases small:x≤1,
   { rw [abs_of_nonneg (real.sin_nonneg_of_nonneg_of_le_pi h.le (by linarith [real.two_le_pi]))],
     exact (real.sin_lt h).le },
   { exact (real.abs_sin_le_one _).trans (le_of_not_ge small) } },
 exact ⟨(div_le_one h).2 ha, div_le_div_of_le h.le (real.abs_sin_le_one _)⟩
end
theorem mx_kernel_envelope (w d t : ℝ) (hw : 0≤w) (hd : 0<d) (ht : 0<t) :
 let x:=t*d in
 w*(real.sin x/x)^2≤w ∧ w*(real.sin x/x)^2≤(w/d)*(1/t) :=
begin
 dsimp, have hx:=mul_pos ht hd,
 have h:=mx_sinc_bounds _ hx,
 have ha : 0≤|real.sin (t*d)/(t*d)|:=abs_nonneg _,
 have hs : (real.sin (t*d)/(t*d))^2≤|real.sin (t*d)/(t*d)| :=
 by { rw [←sq_abs],nlinarith [mul_nonneg ha (sub_nonneg.mpr h.1)] },
 split,
 { exact (mul_le_mul_of_nonneg_left (hs.trans h.1) hw).trans_eq (mul_one w) },
 { convert mul_le_mul_of_nonneg_left (hs.trans h.2) hw using 1,field_simp;ring }
end

def mx_band (w d : ℝ) (t : ℝ) := w*(real.sin (t*d)/(t*d))^2
theorem mx_continuum_integral {α : Type*} [measurable_space α] (mu : measure α)
 (w d : α → ℝ) (t : ℕ → ℝ) (ht : ∀ n,0<t n) (htop : tendsto t at_top at_top)
 (hw : integrable w mu) (hn : ∀ᵐ x ∂mu,0≤w x) (hd : ∀ᵐ x ∂mu,0<d x)
 (hm : ∀ n,ae_strongly_measurable (λ x,mx_band (w x) (d x) (t n)) mu) :
 tendsto (λ n,∫ x,mx_band (w x) (d x) (t n) ∂mu) at_top (𝓝 0) :=
begin
 have hb : ∀ n,∀ᵐ x ∂mu,‖mx_band (w x) (d x) (t n)‖≤w x,
 { intro n,filter_upwards [hn,hd] with x hx hz,
   unfold mx_band,rw [real.norm_eq_abs,abs_of_nonneg (mul_nonneg hx (sq_nonneg (real.sin (t n*d x)/(t n*d x))))],
   exact (mx_kernel_envelope _ _ _ hx hz (ht n)).1 },
 have hp : ∀ᵐ x ∂mu,tendsto (λ n,mx_band (w x) (d x) (t n)) at_top (𝓝 (0:ℝ)),
 { filter_upwards [hn,hd] with x hx hz,
   have lo:∀ n:ℕ,0≤mx_band (w x) (d x) (t n):=λ n,mul_nonneg hx (sq_nonneg _),
   have up:∀ n:ℕ,mx_band (w x) (d x) (t n)≤(w x/d x)*(1/t n):=λ n,(mx_kernel_envelope _ _ _ hx hz (ht n)).2,
   apply squeeze_zero lo up,
   simpa only [one_div,mul_zero,function.comp_app] using (tendsto_inv_at_top_zero.comp htop).const_mul (w x/d x) },
 simpa using tendsto_integral_of_dominated_convergence w hm hw hb hp
end

-- A local continuum junction and a material energy read of elapsed time.
theorem mx_flux_bilinear (a b c d e f u v k : ℂ) :
 ((k-(u^2+v^2)/2)*c+u*a+v*b)*f+
 c*((-k-(u^2+v^2)/2)*f+u*d+v*e)=
 a*d+b*e-(a-u*c)*(d-u*f)-(b-v*c)*(e-v*f) := by ring
theorem mx_pulse_dynamics (k a t : ℝ) :
 has_deriv_at (λ x:ℝ,a*x^2*real.exp (-k*x))
 (-k*(a*t^2*real.exp (-k*t))+2*a*t*real.exp (-k*t)) t :=
begin
 have h : has_deriv_at (λ x:ℝ,-k*x) (-k) t:=by simpa using (has_deriv_at_id t).const_mul (-k),
 convert (((has_deriv_at_id t).pow 2).const_mul a).mul h.exp using 1,
 norm_num [id.def];ring
end
theorem mx_filter_dynamics (k t : ℝ) :
 has_deriv_at (λ x:ℝ,x^3*real.exp (-k*x)/3)
 (-k*(t^3*real.exp (-k*t)/3)+t^2*real.exp (-k*t)) t :=
begin
 have h : has_deriv_at (λ x:ℝ,-k*x) (-k) t:=by simpa using (has_deriv_at_id t).const_mul (-k),
 convert ((((has_deriv_at_id t).pow 3).mul h.exp).div_const 3) using 1,
 norm_num [id.def];ring
end
theorem mx_filtered_profile (k t : ℝ) :
 t^2-2*k*t^3/3=t^2*(1-2*k*t/3) := by ring
theorem mx_arrival_node : (1-(3:ℝ)/3)^2=0 := by norm_num
theorem mx_arrival_moments :
 let m:=λ n:ℕ,(∫ x in set.Ioi (0:ℝ),real.exp (-x)*x^n)/(24:ℝ) in
 m 4=1 ∧ m 5=5 ∧ m 4-2*m 5/3+m 6/9=1 ∧ m 5-2*m 6/3+m 7/9=25/3 :=
begin dsimp,simp_rw [radial_gamma_area],norm_num [nat.factorial] end
theorem mx_capture_area (a b k : ℝ) (h : k≠0) :
 a*b*k^3*24/(2*k)^5=3*a*b/(2*k)^2 := by field_simp;ring
theorem mx_delay_shift : (25:ℝ)/3-5=10/3 := by norm_num
theorem mx_clock_shell (a b energy : ℝ) : (energy-(b-a))+b=energy+a := by ring
theorem mx_clock_intertwine (a b w : ℂ) :
 complex.I*(complex.I*(b-a)*w)+b*w-w*a=0 :=
begin calc complex.I*(complex.I*(b-a)*w)+b*w-w*a =
 (complex.I*complex.I)*(b-a)*w+b*w-w*a : by ring
 ... = 0 : by rw [complex.I_mul_I];ring end
theorem mx_clock_absorption (a b x y : ℝ) (ha : a^2+b^2=1) (hb : x^2+y^2=1) :
 ((a-x)^2+(b-y)^2)/4=(1-(a*x+b*y))/2 := by linear_combination (ha+hb)/4
theorem mx_clock_spectra :
 let z:ℂ:=⟨1/2,1/2⟩ in
 (1-(z^5).re)/2=9/16 ∧
 (1-(z^5-(10:ℂ)/3*z^6+10/3*z^7).re)/2=11/24 :=
begin
 dsimp,norm_num [pow_succ,complex.mul_re,complex.mul_im,complex.sub_re,complex.sub_im,
 complex.add_re,complex.add_im,complex.div_re,complex.div_im,complex.norm_sq_apply]
end

-- A gravitational interaction with or without a retained oscillator.
def rc_step (s : ℝ × ℝ × ℝ) (x y : ℝ) : ℝ × ℝ × ℝ :=
 (s.1+x,s.2.1+y,s.2.2+s.1*y-s.2.1*x)
theorem rc_closed_cycle (a b c d q h : ℝ) :
 rc_step (rc_step (rc_step (rc_step (0,0,0) (a*q) (b*q)) (c*h) (d*h))
 (-a*q) (-b*q)) (-c*h) (-d*h) =
 (0,0,2*(a*d-b*c)*q*h) :=
begin unfold rc_step, simp only [prod.mk.inj_iff], repeat {split}, all_goals {ring} end
theorem rc_reversed_area (a b c d : ℝ) : 2*(c*b-d*a)= -(2*(a*d-b*c)) := by ring
theorem rc_direct_disjoint (g a b : ℝ) (h : a*b=0) : g*a*b=0 :=
by rw [mul_assoc,h,mul_zero]
theorem rc_independent_phase {A B G : Type*} [comm_group G]
 (z : A → B → G) (a₀ : A) (b₀ : B)
 (h : ∀ a b, z a b / z a b₀ = z a₀ b / z a₀ b₀) :
 ∀ a b, z a b = z a b₀*(z a₀ b / z a₀ b₀) :=
begin intros a b,rw [←h a b,div_eq_mul_inv], ac_refl <|> simp [mul_assoc,mul_left_comm,mul_comm] end
theorem rc_signed_rate (u : ℝ) : max u 0+max (-u) 0=|u| :=
begin by_cases h:0≤u,
 {rw [max_eq_left h,max_eq_right (neg_nonpos.mpr h),abs_of_nonneg h,add_zero]},
 {have k:u≤0:=le_of_not_ge h,rw [max_eq_right k,max_eq_left (neg_nonneg.mpr k),abs_of_nonpos k,zero_add]} end
theorem rc_echo_rates (r : ℝ) (h:0≤r) :
 (real.sqrt r-real.sqrt r)^2/2=0 ∧
 ((real.sqrt r-0)^2+(0-real.sqrt r)^2)/2=r :=
begin split,{ring},{nlinarith only [real.sq_sqrt h]} end
theorem rc_same_sign_wait (u v : ℝ) : real.exp (-u)*real.exp (-v)=real.exp (-(u+v)) :=
by rw [←real.exp_add,neg_add]
theorem rc_on_shell (m d transverse u : ℝ) (hu:u≠0) :
 ((m+d)^2+transverse)/(2*u)-(m^2+transverse)/(2*u)=(2*m*d+d^2)/(2*u) :=
by field_simp;ring
theorem rc_energy_momentum (E p k h : ℝ) :
 E+h+(k-h)=E+k ∧ p+h+(k-h)=p+k ∧ (E+h)-(p+h)=E-p :=
by repeat {split};ring

def rc_primitive (x : ℝ) : ℝ := (1-15*x^2+15*x^4-x^6)/(1+x^2)^6
def rc_slope (x : ℝ) : ℝ := 6*x*(x^6-21*x^4+35*x^2-7)/(1+x^2)^7
theorem rc_primitive_derivative (x : ℝ) : has_deriv_at rc_primitive (rc_slope x) x :=
begin
 have nz:(1+x^2:ℝ)≠0:=by positivity,
 have h:=has_deriv_at_id x,
 have num:=((((has_deriv_at_const x (1:ℝ)).sub ((h.pow 2).const_mul 15)).add
              ((h.pow 4).const_mul 15)).sub (h.pow 6)),
 have den:=((has_deriv_at_const x (1:ℝ)).add (h.pow 2)).pow 6,
 unfold rc_primitive rc_slope,
 convert num.div den (pow_ne_zero 6 nz) using 1,
 simp [id.def];field_simp [nz];ring
end
theorem rc_log_scan (a lo hi : ℝ) :
 (∫ s in lo..hi, (5/18:ℝ)*a*rc_slope (a*s))=
 (5/18)*(rc_primitive (a*hi)-rc_primitive (a*lo)) :=
begin
 have der:∀ s:ℝ,has_deriv_at (λ x:ℝ,(5/18:ℝ)*rc_primitive (a*x))
      ((5/18:ℝ)*a*rc_slope (a*s)) s,
 {intro s, convert (((rc_primitive_derivative (a*s)).comp s
      ((has_deriv_at_id s).const_mul a)).const_mul (5/18:ℝ)) using 1,
  simp [id.def];ring},
 have ct:continuous (λ s:ℝ,(5/18:ℝ)*a*rc_slope (a*s)),
 {unfold rc_slope,refine continuous_const.mul (continuous.div (by continuity) (by continuity) _),
  intro s,exact pow_ne_zero 7 (by positivity)},
 rw [interval_integral.integral_eq_sub_of_has_deriv_at (λ s hs,der s) (ct.interval_integrable lo hi)],ring
end
theorem rc_scan_at_one : (5/18:ℝ)*rc_slope 1=5/48 ∧ rc_primitive 0=1 :=
by norm_num [rc_slope,rc_primitive]
theorem rc_scan_infinite : tendsto rc_primitive at_top (𝓝 (0:ℝ)) :=
begin
 let f:ℝ→ℝ:=λ y,y^6*(y^6-15*y^4+15*y^2-1)/(1+y^2)^6,
 have hc:continuous f,
 {dsimp [f],refine continuous.div (by continuity) (by continuity) _,intro s,exact pow_ne_zero 6 (by positivity)},
 have h:tendsto (λ x:ℝ, f x⁻¹) at_top (𝓝 (0:ℝ)),
 {have hlim:=hc.continuous_at.tendsto.comp (tendsto_inv_at_top_zero : tendsto (λ x:ℝ,x⁻¹) at_top (𝓝 0)),
  change tendsto (λ x:ℝ,f x⁻¹) at_top (𝓝 (f 0)) at hlim,
  rw [show f 0=0,by norm_num [f]] at hlim,exact hlim},
 refine filter.tendsto.congr' _ h,filter_upwards [eventually_gt_at_top (0:ℝ)] with x hx,
 dsimp [f,rc_primitive],
 apply (div_eq_div_iff (pow_ne_zero 6 (show 1+x⁻¹^2≠0,by positivity)) (pow_ne_zero 6 (show 1+x^2≠0,by positivity))).2,
 simp only [inv_pow],field_simp [ne_of_gt hx];ring
end
theorem rc_pair_log_slope (p t : ℝ) (hp:1+p*t≠0) (hm:1-p*t≠0) :
 (8*p/(1+p*t)+8*p/(1-p*t))*(1-(p*t)^2)=16*p :=
by field_simp;ring
theorem rc_factorial_coefficients (p : ℝ) (a : ℕ → ℝ) (h0:a 0=16*p) (h1:a 1=0)
 (step:∀ n:ℕ,a (n+2)=p^2*a n) (k : ℕ) :
 a (2*k)=16*p*(p^2)^k ∧ a (2*k+1)=0 :=
begin
 induction k with k ih,{simpa using (and.intro h0 h1)},
 have e:2*(k+1)=2*k+2:=by ring,
 have o:2*(k+1)+1=(2*k+1)+2:=by ring,
 change a (2*(k+1))=_ ∧ a (2*(k+1)+1)=_,
 rw [o,e,step (2*k),step (2*k+1),ih.1,ih.2],split,{rw [pow_succ (p^2) k],ring},{ring}
end
theorem rc_pair_third (p : ℝ) (hp:p≠0) : (32*p^3)/(16*p)^3=1/128 := by field_simp;ring
theorem rc_parallel_capture (p e : ℝ) :
 (1+p*((1-e+e)-1))=1 ∧ e*(16*p)^2-(e*16*p)^2=e*(1-e)*(16*p)^2 :=
by split;ring
theorem rc_vacuum_ratio (p : ℝ) (hp:1+p≠0) :
 (1-p)^8/(1+p)^8=((1-p)/(1+p))^8 := by rw [div_pow]
theorem rc_quadrupole_power (g v tension k : ℝ) :
 g/5*(2/3)*(-12*v*tension*k)^2=(96/5)*g*tension^2*k^2*v^2 := by ring

theorem rc_filter_tail (r a : ℝ) (n:ℕ) : a*r^(n+1)-r*(a*r^n)=0 := by rw [pow_succ];ring
theorem rc_filter_success (r : ℝ) (hp:1+r≠0) :
 (1-r^2)/(1+r)^2=(1-r)/(1+r) := by field_simp;ring
theorem rc_filter_passive (r x : ℝ) :
 (1+r^2-2*r*x)+r*(2+2*x)=(1+r)^2 := by ring
theorem rc_gram_min (r x : ℝ) (hr:0≤r) (hl:r<1) (hx:-1≤x) (hy:x≤1) :
 (1-r)/(1+r) ≤ (1-r^2)/(1+r^2-2*r*x) :=
begin
 have d:0<1+r^2-2*r*x:=by nlinarith only [mul_nonneg hr (sub_nonneg.mpr hy),sq_pos_of_pos (sub_pos.mpr hl)],
 apply (div_le_div_iff (by linarith : 0<1+r) d).2,
 nlinarith only [mul_nonneg (mul_nonneg hr (sub_nonneg.mpr hl.le)) (show 0≤1+x,by linarith)]
end
theorem rc_gram_edge (r : ℝ) (hr:1+r≠0) :
 (1-r^2)/(1+r^2-2*r*(-1))=(1-r)/(1+r) :=
begin rw [show 1+r^2-2*r*(-1)=(1+r)^2,by ring],exact rc_filter_success _ hr end
theorem rc_gram_contract {ι : Type*} (s : finset ι) (a : ι → ℝ) (g m rest : ℝ)
 (h: g=m*(∑ i in s,(a i)^2)+rest) (hp:0≤rest) :
 m*(∑ i in s,(a i)^2)≤g := by linarith
theorem rc_thermal_false {ι : Type*} [fintype ι] (w e : ι → ℝ)
 (hw:∀ i,0<w i) (he:∀ i,0≤e i) (h:(∑ i,w i*e i)=0) (j:ι) : e j=0 :=
begin
 have hj:=finset.single_le_sum (λ (i:ι) hi,mul_nonneg (hw i).le (he i)) (finset.mem_univ j),
 rw [h] at hj,by_contra hn, exact (not_lt_of_ge hj) (mul_pos (hw j) (lt_of_le_of_ne (he j) (ne.symm hn)))
end
theorem rc_no_hit_mean (h n : ℝ) : real.exp (-h*n)=real.exp (-(h*n)) := by rw [neg_mul]
theorem rc_weak_capture (x : ℝ) : 1-real.exp (-x)≤x :=
by linarith only [real.add_one_le_exp (-x)]
theorem rc_intensity_limit {ι : Type*} (w u : ι → ℝ) (s : finset ι) (h : ℝ)
 (hw:∀ i∈s,0≤w i) :
 (∑ i in s,w i*(1-real.exp (-(h*u i^2))))≤ h*(∑ i in s,w i*u i^2) :=
begin
 rw [mul_sum],apply sum_le_sum,intros i hi,
 calc w i*(1-real.exp (-(h*u i^2)))≤ w i*(h*u i^2) :
 mul_le_mul_of_nonneg_left (rc_weak_capture _) (hw i hi)
 ... = h*(w i*u i^2) : by ring
end
theorem rc_energy_floor (F : ℝ → ℝ) (s : ℝ)
 (hF : interval_integrable (λ x:ℝ,x*F x) volume 0 1)
 (h : ∀ x∈set.Icc (0:ℝ) 1,s≤F x) :
 s/2≤ ∫ x in (0:ℝ)..1,x*F x :=
begin
 have hc:continuous (λ x:ℝ,x*s):=continuous_id.mul continuous_const,
 have hle:=interval_integral.integral_mono_on (by norm_num : (0:ℝ)≤1)
  (hc.interval_integrable 0 1) hF (λ x hx,mul_le_mul_of_nonneg_left (h x hx) hx.1),
 rw [interval_integral.integral_mul_const,integral_id] at hle,norm_num at hle ⊢,linarith
end
theorem rc_positive_energy_tail {α : Type*} [measurable_space α]
 (μ : measure α) (E : α → ℝ) (hE : integrable E μ)
 (hn : 0≤ᵐ[μ] E) (hz : ∫ x,E x ∂μ=0) : E=ᵐ[μ]0 :=
(measure_theory.integral_eq_zero_iff_of_nonneg_ae hn hE).1 hz
theorem rc_sharp_weight (energy band eps : ℝ) (hne : band≠eps) :
 ((energy-eps)/(band-eps))*band+(1-(energy-eps)/(band-eps))*eps=energy :=
by field_simp [sub_ne_zero.mpr hne];ring

theorem rc_bounded_echo (d t : ℝ) : 1-(d+(1-d)*t)=(1-d)*(1-t) := by ring
theorem rc_matrix_second (w b : ℝ) (hb:b≠0) :
 has_deriv_at (λ x:ℝ,-6*w/x^7) (42*w/b^8) b :=
begin
 have h:=((has_deriv_at_const b (-6*w)).div ((has_deriv_at_id b).pow 7) (pow_ne_zero 7 hb)),
 convert h using 1,simp [id.def];field_simp [hb];ring
end
theorem rc_rectangle (a b c d u v w x : ℝ) :
 (a+u+w)-(b+u+x)-(c+v+w)+(d+v+x)=a-b-c+d := by ring
theorem rc_double_exposure (x y phi : ℝ) (h:|phi|≤x) (k:|phi|≤y) :
 2*|phi|≤x+y := by linarith
theorem rc_echo_bound (visible exposure angle : ℝ) (hd : 0≤visible) (h:2*angle≤exposure) :
 visible*(1-real.exp (-(2*angle)))≤visible*(1-real.exp (-exposure)) :=
mul_le_mul_of_nonneg_left (sub_le_sub_left (real.exp_le_exp.mpr (neg_le_neg h)) 1) hd

theorem rc_dissipative_entry (l m r : ℂ) :
 l*r*m-(l^2*r+r*m^2)/2= -(l-m)^2*r/2 := by ring
theorem rc_population_invariant (l r : ℂ) :
 l*r*l-(l^2*r+r*l^2)/2=0 := by ring
theorem rc_poisson_echo (mu dose : ℝ) :
 (∑' n:ℕ,real.exp (-mu)*((mu*real.exp (-dose))^n/(nat.factorial n:ℝ))) =
 real.exp (-(mu*(1-real.exp (-dose)))) :=
begin
 rw [tsum_mul_left],
 have h:(∑' n:ℕ,(mu*real.exp (-dose))^n/(nat.factorial n:ℝ))=real.exp (mu*real.exp (-dose)),
 {rw [real.exp_eq_exp_ℝ],exact (exp_series_div_has_sum_exp ℝ _).tsum_eq},
 rw [h,←real.exp_add],congr' 1,ring
end
theorem rc_bandwidth_cap (T e mean s : ℝ) (hT:0<T) (hbar:0<e)
 (wrapped:s/2≤mean*T/(2*real.pi*e)) : s≤mean*T/(real.pi*e) :=
begin
 have hpi:=real.pi_pos,apply (le_div_iff (mul_pos hpi hbar)).2,
 have h:=(le_div_iff (mul_pos (mul_pos (by norm_num) hpi) hbar)).1 wrapped,
 nlinarith only [h]
end
theorem rc_rectangle_exact (f df integral : ℝ → ℝ) (a b x : ℝ)
 (hd : ∀ t:ℝ,has_deriv_at f (df t) t)
 (hc : continuous df)
 (edge : ∀ z:ℝ,integral z=∫ t in a..b,df (z+t)) :
 integral x-integral 0=f (x+b)+f a-f (x+a)-f b :=
begin
 have h:∀ z:ℝ,(∫ t in a..b,df (z+t))=f (z+b)-f (z+a),
 {intro z,apply interval_integral.integral_eq_sub_of_has_deriv_at,
  {intros y hy,convert (hd (z+y)).comp y ((has_deriv_at_const y z).add (has_deriv_at_id y)) using 1,
   simp [id.def]},
  {exact (hc.comp (continuous_const.add continuous_id)).interval_integrable _ _}},
 rw [edge x,edge 0,h x,h 0,zero_add,zero_add],ring
end

theorem rc_escape_aberration (c v : ℝ) (h:1+v*c≠0) :
 (1-(c+v)/(1+v*c))/2=(1-v)*(1-c)/(2*(1+v*c)) := by field_simp;ring
theorem rc_escape_rational (c v b f : ℝ) (hv:1-v^2=f) (hc:1-c^2=b^2*f)
 (dv:1+v≠0) (dc:1+c≠0) (de:1+v*c≠0) :
 (1-v)*(1-c)/(2*(1+v*c))=b^2*f^2/(2*(1+v)*(1+c)*(1+v*c)) :=
begin apply (div_eq_div_iff (mul_ne_zero (by norm_num : (2:ℝ)≠0) de) (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (2:ℝ)≠0) dv) dc) de)).2,
 calc (1-v)*(1-c)*(2*(1+v)*(1+c)*(1+v*c))
 = (1-v^2)*(1-c^2)*(2*(1+v*c)) : by ring
 ... = _ : by rw [hv,hc];ring end
theorem rc_escape_horizon :
 ((27:ℝ)/4)/(2*(1+1)*(1+1)*(1+1))=27/64 ∧ ((27:ℝ)/64)/(1+1)=27/128 :=
by norm_num

-- Sharp Gram bound for a decaying sequence. The alternating finite test
-- reaches the same edge that the causal inverse filter realizes.
theorem rc_causal_norm {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
 (r A : ℝ) (hr:0≤r) (ha:0≤A) (u delayed coeff : E) (hu:‖delayed‖=‖u‖)
 (h:u-r • delayed=A • coeff) : A*‖coeff‖≤(1+r)*‖u‖ :=
begin
 have le:=norm_sub_le u (r • delayed),rw [h,norm_smul,norm_smul,real.norm_eq_abs,
  real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hr,hu] at le,linarith
end
def rc_alt_total (r : ℝ) (n : ℕ) : ℝ :=
 (n:ℝ)*(1-r)/(1+r)+2*r*(1-(-r)^n)/(1+r)^2
theorem rc_alt_recurrence (r : ℝ) (hr:1+r≠0) (n:ℕ) :
 rc_alt_total r (n+1)=rc_alt_total r n+1+2*(-r)*(1-(-r)^n)/(1+r) :=
begin unfold rc_alt_total,rw [pow_succ],push_cast,field_simp [hr];ring end
theorem rc_alt_finite (r : ℝ) (hr:1+r≠0) (q:ℕ→ℝ) (hz:q 0=0)
 (step:∀ n,q (n+1)=q n+1+2*(-r)*(1-(-r)^n)/(1+r)) (n:ℕ) :
 q n=rc_alt_total r n :=
begin induction n with n ih,{simp [rc_alt_total,hz]},
 rw [nat.succ_eq_add_one,step,ih,rc_alt_recurrence _ hr] end
theorem rc_scan_small (x:ℝ) : 0≤1-rc_primitive x ∧ 1-rc_primitive x≤21*x^2 :=
begin
 unfold rc_primitive,have hd:0<(1+x^2)^6:=by positivity,split,
 {refine sub_nonneg.mpr ((div_le_iff hd).2 (sub_nonneg.mp _)),
  rw [show 1*(1+x^2)^6-(1-15*x^2+15*x^4-x^6)=x^2*(21+21*x^4+15*x^6+6*x^8+x^10),by ring],
  positivity},
 {refine sub_le_comm.mp ((le_div_iff hd).2 (sub_nonneg.mp _)),
  rw [show (1-15*x^2+15*x^4-x^6)-(1-21*x^2)*(1+x^2)^6=x^4*(126+294*x^2+405*x^4+309*x^6+125*x^8+21*x^10),by ring],
  positivity}
end
theorem rc_spectral_numerator (x:ℝ) :
 |1-15*x^2+15*x^4-x^6|≤(1+x^2)^3 :=
begin apply abs_le.mpr,split,
 {nlinarith only [sq_nonneg (1-3*x^2)]},
 {nlinarith only [mul_nonneg (sq_nonneg x) (sq_nonneg (x^2-3))]} end
theorem rc_uniform_tail (r:ℝ) (F:finset ℕ) (q g:ℕ→ℝ) (h:∀ i∈F,|q i|≤1)
 (hr:|r|≤1) :
 (∑ i in F,|g i*r*q i|)≤∑ i in F,|g i| :=
begin
 apply sum_le_sum,intros i hi,rw [abs_mul,abs_mul],
 calc |g i|*|r|*|q i|≤|g i|*|r|*1 : mul_le_mul_of_nonneg_left (h _ hi) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
 ... ≤ |g i| : by rw [mul_one];simpa using mul_le_mul_of_nonneg_left hr (abs_nonneg (g i))
end

-- The unread supersymmetry Ward identity and its consequences for each write.
theorem rc_commutator_product {R : Type*} [ring R] (Q K A : R) :
 (A*Q-Q*A)*(Q*K-K*Q)=A*(Q*Q)*K-(A*Q*K)*Q-Q*(A*Q*K)+Q*(A*K)*Q :=
by noncomm_ring
theorem rc_strong_ward {R ι : Type*} [ring R] (s : finset ι) (K A : ι → R) (Q : R)
 (hn:(∑ i in s,A i*K i)=1) (hq:(∑ i in s,A i*Q*K i)=Q)
 (he:(∑ i in s,A i*(Q*Q)*K i)=Q*Q) :
 (∑ i in s,(A i*Q-Q*A i)*(Q*K i-K i*Q))=0 :=
begin
 simp_rw [rc_commutator_product],
 simp only [sum_add_distrib,sum_sub_distrib,←sum_mul,←mul_sum,hn,hq,he,mul_one],
 noncomm_ring
end
theorem rc_individual_write {ι E : Type*} [normed_add_comm_group E] (s : finset ι)
 (a : ι → E) (h:(∑ i in s,‖a i‖^2)=0) (j : ι) (hj:j∈s) : a j=0 :=
begin
 have le:=finset.single_le_sum (λ (i:ι) hi,sq_nonneg ‖a i‖) hj,rw [h] at le,
 have z:‖a j‖^2=0:=le_antisymm le (sq_nonneg _),
 rw [pow_two,mul_eq_zero] at z,exact norm_eq_zero.mp (z.elim id id)
end
theorem rc_ward_hellinger {ι E : Type*} [normed_add_comm_group E] (s:finset ι)
 (a b : ι → E) (err : ℝ) (h:(∑ i in s,‖a i-b i‖^2)≤2*err) :
 (∑ i in s,(‖a i‖-‖b i‖)^2)≤2*err :=
begin
 apply le_trans _ h,apply sum_le_sum,intros i hi,
 have he:=abs_norm_sub_norm_le (a i) (b i),
 have h2:=pow_le_pow_of_le_left (abs_nonneg (‖a i‖-‖b i‖)) he 2,
 simpa only [sq_abs] using h2
end
theorem rc_dichotomic_ward (a b : ℝ) (h:a^2+b^2=1) :
 (a-b)^2+(b-a)^2=2*(1-2*a*b) := by linear_combination 2*h
theorem rc_supercharge_rescale {R : Type*} [ring R] (a x y : R)
 (hx:x*a=a*x) (hy:y*a=a*y) :
 (a*x)*(a*y)+(a*y)*(a*x)=(a*a)*(x*y+y*x) :=
begin
 calc (a*x)*(a*y)+(a*y)*(a*x)=a*(x*a)*y+a*(y*a)*x : by noncomm_ring
 ... =(a*a)*(x*y+y*x) : by rw [hx,hy];noncomm_ring
end
theorem rc_dressed_energy (E f : ℝ) (he:0<E) (hf:-1<f) :
 0<E*(1+f) ∧ (real.sqrt (1+f))^2*E=E*(1+f) :=
begin have h:0<1+f:=by linarith,
 exact ⟨mul_pos he h,by rw [real.sq_sqrt h.le,mul_comm]⟩ end
theorem rc_smooth_bounded (x:ℝ) : |x/real.sqrt (1+x^2)|<1 :=
begin
 have hs:0<real.sqrt (1+x^2):=real.sqrt_pos.mpr (by positivity),
 rw [abs_div,abs_of_pos hs,div_lt_one hs],
 have hsq:=real.sq_sqrt (show 0≤1+x^2,by positivity),
 have ha:=sq_abs x,nlinarith only [hs,hsq,ha,abs_nonneg x]
end

-- A remote freely evolving spectator cannot change the local contact energy.
theorem rc_spectator_linear (F : ℝ → ℝ)
 (weak : ∀ eps:ℝ,0<eps→∃ d:ℝ,0<d ∧ ∀ y:ℝ,|y|<d→|F y-y|≤eps*|y|)
 (spectator : ∀ (x t:ℝ),1≤t→t*F (x/t)=F x) (x:ℝ) : F x=x :=
begin
 by_contra hx,
 have hdif : 0 < |F x-x|:=abs_pos.mpr (sub_ne_zero.mpr hx),
 let eps:=|F x-x|/(2*(|x|+1)),
 have posd:0<2*(|x|+1):=by positivity,
 have he:0<eps:=div_pos hdif posd,
 rcases weak eps he with ⟨d,hd,small⟩,
 let t:=1+|x|/d,
 have ht:1≤t:=le_add_of_nonneg_right (div_nonneg (abs_nonneg x) hd.le),
 have hp:0<t:=lt_of_lt_of_le zero_lt_one ht,
 have hprod:t*d=d+|x|:=by dsimp [t];field_simp [ne_of_gt hd];ring,
 have yin:|x/t|<d,
 {rw [abs_div,abs_of_pos hp],apply (div_lt_iff hp).2,nlinarith only [hprod,hd]},
 have hb:=mul_le_mul_of_nonneg_left (small (x/t) yin) hp.le,
 have restore:t*(F (x/t)-x/t)=F x-x:=
 by rw [mul_sub,spectator x t ht];field_simp [ne_of_gt hp];ring,
 have absrestore : t*|F (x/t)-x/t|=|F x-x| :=
 by rw [←restore,abs_mul,abs_of_pos hp],
 rw [absrestore,abs_div,abs_of_pos hp] at hb,
 have cancel_all : ∀ (a b u:ℝ),u≠0→u*(a*(b/u))=a*b,
 {intros a b u h,field_simp [h];ring},
 have cancel:=cancel_all eps (abs x) t (ne_of_gt hp),
 rw [cancel] at hb,
 have hdef:eps*(2*(|x|+1))=|F x-x|:=div_mul_cancel _ (ne_of_gt posd),
 nlinarith only [hdef,hb,he,mul_nonneg he.le (abs_nonneg x)]
end
theorem rc_disjoint_cluster_square {R : Type*} [ring R] (a b : R)
 (h:a*b+b*a=0) : (a+b)*(a+b)=a*a+b*b :=
begin calc (a+b)*(a+b)=a*a+(a*b+b*a)+b*b : by noncomm_ring
 ... = a*a+b*b : by rw [h,add_zero] end
theorem rc_lightfront_energy (pplus transverse internal BB : ℝ) (hp:pplus≠0)
 (h:BB=transverse/(2*pplus^2)) :
 2*pplus*BB+2*internal=2*(transverse/(2*pplus)+internal) :=
by rw [h];field_simp [hp];ring

end matrix_layer_work
