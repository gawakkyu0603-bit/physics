import analysis.special_functions.log.deriv
import analysis.special_functions.exp
import analysis.special_functions.integrals
import data.complex.module
import linear_algebra.matrix.nonsingular_inverse
import topology.instances.real_vector_space
import analysis.specific_limits.basic
import tactic

noncomputable theory
open_locale big_operators
namespace wrapped_capture

-- The two orderings of the two different transverse displacements.
theorem vertex_sum (a b g h : ℂ) :
 (g+h)*a+(g-h)*b=g*(a+b)+h*(a-b) := by ring
theorem symmetric_metric (a g h : ℂ) : (g+h)*a+(g-h)*a=2*g*a := by ring
theorem antisymmetric_form (a g h : ℂ) : (g+h)*a+(g-h)*(-a)=2*h*a := by ring
theorem dbi_charge (m p : ℝ) (hm : m≠0) :
 m^2*(1+(p/m)^2)=m^2+p^2 := by field_simp; ring
theorem neutral_line (w c : ℝ) (hc : c≠0) :
 (w/c)/c^2=w/c^3 := by rw [div_div,show c*c^2=c^3,by ring]

-- The squared mass-shell relations avoid setoid square-root sign choices.
theorem phase_space (w z s c : ℝ) (hc : c≠0) (h : c^2=1+s^2) :
 ((w+s*z)/c)^2-z^2=((w*c)^2-(z-w*s)^2)/c^2 :=
begin field_simp [hc]; linear_combination (w^2+z^2) * (-h) end
theorem daughter_shell (m w q s c z : ℝ) (hc : c≠0) (h : c^2=1+s^2)
 (hw : q^2=m^2-2*m*w) :
 (m*c-(w+s*z)/c)^2-(((w+s*z)/c)^2-z^2)-(m*s-z)^2=q^2 :=
begin rw [hw],field_simp [hc],ring_nf,
 simp only [show c^6=(c^2)^3,by ring,show c^4=(c^2)^2,by ring,h];ring end
theorem open_window (a b n : ℝ) (hb : 0<b) :
 0<b^2-(n-a)^2 ↔ a-b<n ∧ n<a+b :=
begin rw [show b^2-(n-a)^2=(b+(n-a))*(b-(n-a)), by ring, mul_pos_iff],
 split, { rintro (h|h), {split;linarith [h.1,h.2]}, {exfalso;linarith [h.1,h.2]} },
 {rintro ⟨h,k⟩,left,split;linarith} end
theorem reflection (n a b : ℝ) : b^2-((2*a-n)-a)^2=b^2-(n-a)^2 := by ring
theorem reflected_integer (k n : ℤ) : k-(k-n)=n := by ring
theorem rest_boost_frequency (w z s c : ℝ) (hc : c≠0) :
 c*((w+s*z)/c)-s*z=w := by field_simp; ring
theorem rest_boost_charge (w z s c : ℝ) (hc : c≠0) (h : c^2=1+s^2) :
 c*z-s*((w+s*z)/c)=(z-w*s)/c :=
begin field_simp [hc]; linear_combination z*h end
theorem pair_example : (0:ℝ) ∈ set.Ioo ((-1:ℝ)/3) (4/3) ∧
 (1:ℝ) ∈ set.Ioo ((-1:ℝ)/3) (4/3) := by norm_num [set.mem_Ioo]
theorem only_two (n : ℤ) (h : (-1:ℝ)/3 < (n:ℝ)) (k : (n:ℝ)<4/3) :
 n=0 ∨ n=1 :=
begin have hn : (-1:ℤ)<n := by exact_mod_cast (show (-1:ℝ)<(n:ℝ),by linarith),
 have hk : n<(2:ℤ) := by exact_mod_cast (show (n:ℝ)<(2:ℝ),by linarith), omega end
theorem two_momenta : ((5:ℝ)/6)^2-((0:ℝ)-1/2)^2=(2/3:ℝ)^2 ∧
 ((5:ℝ)/6)^2-((1:ℝ)-1/2)^2=(2/3:ℝ)^2 := by norm_num
theorem pole_optical (b x : ℝ) :
 (1-2*b)^2+4*b*(1-b)=1 ∧ (1-4*b*x+4*b^2)+4*b*(1-b)=1+4*b*(1-x) :=
by constructor; ring
theorem sharp_tag (b x : ℝ) (hb : 0<b) :
 1+4*b*(1-x)=1 ↔ x=1 :=
begin split, { intro h, have : (4*b)*(1-x)=0 := by linarith,
 have hb' : 4*b≠0 := by positivity, have := (mul_eq_zero.mp this).resolve_left hb',linarith },
 {rintro rfl,ring} end
theorem balance (l : ℝ) : (1-l)^2+l^2+2*l*(1-l)=1 := by ring
theorem width_inverse (l w : ℝ) (hl : l≠0) (hw : w≠0) :
 2*(l^2*w)/((2*l-l^2)*w+l^2*w)=l :=
begin rw [show (2*l-l^2)*w+l^2*w=2*l*w,by ring],field_simp;ring end
theorem bandwidth_bound (l w : ℝ) (hw : 0≤w) (h : w≤1) :
 ((2*l-l^2)*w+l^2*w)^2≤4*(l^2*w) :=
begin have hk : 0≤1-w := by linarith,
 have he : 0≤(4*l^2*w)*(1-w) := by positivity,
 nlinarith only [he] end
theorem bandwidth_equal (g : ℝ) (h : g≠0) :
 g*(g+g)/((g+g)^2+4*(0:ℝ)^2)=1/2 :=
begin have ha : g+g≠0 := λ hh,h (by linarith),
 rw [show (g+g)^2+4*(0:ℝ)^2=(g+g)^2,by ring],field_simp [ha];ring end
theorem pulse_deriv (x : ℝ) :
 has_deriv_at (λ t:ℝ,(1-real.exp (-t)*(1+t+t^2/2))/2) (x^2*real.exp (-x)/4) x :=
begin
 have hi := has_deriv_at_id x,
 have hp := ((has_deriv_at_const x (1:ℝ)).add hi).add ((hi.pow 2).div_const 2),
 have he := (has_deriv_at_const x (1:ℝ)).sub (hi.neg.exp.mul hp),
 convert he.div_const 2 using 1; simp [id];ring
end
theorem pulse_initial : (1-real.exp (-(0:ℝ))*(1+0+0^2/2))/2=0 := by norm_num
theorem recoil_square (m w : ℝ) (h : w≠0) : m^2+2*m*w<(m+w)^2 :=
begin nlinarith [sq_pos_of_ne_zero w h] end

-- Finite-dimensional charge-instrument completeness in matrix elements,
-- with arbitrary degeneracies. Only finitely many charge differences occur.
theorem shift_completeness {ι : Type*} [fintype ι] [decidable_eq ι] (Q : ι → ℤ)
 (S : ι → ι → ℂ) (i j : ι)
 (hS : ∑ k, star (S k i)*S k j = if i=j then (1:ℂ) else 0) :
 (∑ k, if Q k-Q i=Q k-Q j then star (S k i)*S k j else 0)
 = if i=j then (1:ℂ) else 0 :=
begin classical, by_cases h : Q i=Q j,
 {simpa only [h, if_true, eq_self_iff_true] using hS}, { have hn : ∀ k, Q k-Q i≠Q k-Q j := λ k eq,h (by linarith),
 have hij : i≠j := λ eq,h (congr_arg Q eq),simp [hn,hij]} end

-- Classification of a bidegree action; the target is an additive phase group.
theorem cyclic_character {A : Type*} [add_comm_group A] (f : ℤ →+ A) (r : ℤ) :
 f r = r • f 1 :=
begin simpa only [zsmul_eq_mul, int.cast_id, mul_one] using (f.map_zsmul (1:ℤ) r) end
theorem pair_character {A : Type*} [add_comm_group A] (f : ℤ → ℤ → A)
 (left : ∀ s, ∃ g : ℤ →+ A, ∀ r, g r=f r s)
 (right : ∃ g : ℤ →+ A, ∀ s, g s=f 1 s) (r s : ℤ) :
 f r s=r • (s • f 1 1) :=
begin rcases left s with ⟨g,h⟩, rcases right with ⟨k,j⟩,
 rw [←h,cyclic_character g,h,←j,cyclic_character k,j] end
theorem independent_reversal {A : Type*} [add_comm_group A] (f : ℤ →+ A)
 (h : f (-1)=f 1) : f 1+f 1=0 :=
begin rw [map_neg] at h, exact neg_eq_iff_add_eq_zero.mp h end
theorem phase_only_two (z : ℂ) (h : z*z=1) : z=1 ∨ z= -1 :=
begin have h' : (z-1)*(z+1)=0 := by linear_combination h,
 rcases mul_eq_zero.mp h' with t|t,
 {left,exact sub_eq_zero.mp t},{right,exact eq_neg_of_add_eq_zero_left t} end
theorem together_reversal (r s : ℤ) : (-r)*(-s)=r*s := by ring
theorem local_rephasing (r s : ℤ) :
 (r+s)*(r+s-1)-r*(r-1)-s*(s-1)=2*r*s := by ring
theorem odd_contact (r s : ℤ) : (2*r+1)*(2*s+1)=2*(2*r*s+r+s)+1 := by ring
theorem even_contact (r s : ℤ) : (2*r)*s=2*(r*s) := by ring
theorem fringe_separation (v : ℝ) : (1+v)/2-(1-v)/2=v := by ring
theorem no_pure_cross_noise (v x y : ℝ) (h : v^2≤x*y) (hx : x=0) : v=0 :=
begin rw [hx,zero_mul] at h,nlinarith [sq_nonneg v] end
theorem pulse_coupling_cancellation (r s : ℤ) : r*s+(-r)*s=0 := by ring

-- Coherent soft response and charge recoil.
theorem heavy_difference (p k d v : ℝ) (h0 : d≠0) (h1 : d-v≠0) :
 (k-1)*(-p)/(d-v)-k*(-p)/d=p*(d-k*v)/(d*(d-v)) :=
by field_simp [h0,h1];ring
theorem heavy_positive (p k d v : ℝ) (hp : 0<p) (h : 0<d-k*v)
 (h0 : 0<d) (h1 : 0<d-v) : 0<p*(d-k*v)/(d*(d-v)) :=
div_pos (mul_pos hp h) (mul_pos h0 h1)
theorem shell_lower (w E M s c : ℝ) (hc:c≠0) (hE:E=M*c)
 (hM:M≠0) (h:c^2=1+s^2) :
 E-2*w/c-(M*s)*(s/c)=(M^2-2*M*w)/E :=
begin subst E,field_simp [hc,hM],ring_nf,
 simp only [show c^4=(c^2)^2,by ring,h];ring end
theorem squared_soft_strict (a b t : ℝ) (ha:0<a) (hb:0<b) (ht:0<t) :
 t*a^2<t*(a+b)^2 :=
begin have h : 0<t*b*(2*a+b) := by positivity, nlinarith only [h] end
theorem angular_density (v x : ℝ) (h : 1-v*x≠0) :
 (1-x^2)*v^2/(1-v*x)^2=(v^2-1)/(1-v*x)^2+2/(1-v*x)-1 :=
by field_simp [h];ring
theorem angular_primitive (v x : ℝ) (hv:v≠0) (ht:1-v*x≠0) :
 has_deriv_at (λ x:ℝ, ((v^2-1)/(1-v*x)-2*real.log (1-v*x)+(1-v*x))/v)
 ((1-x^2)*v^2/(1-v*x)^2) x :=
begin
 have ht' := (has_deriv_at_const x (1:ℝ)).sub ((has_deriv_at_id x).const_mul v),
 have hq := (has_deriv_at_const x (v^2-1)).div ht' ht,
 have hl := (ht'.log ht).const_mul (2:ℝ),
 convert ((hq.sub hl).add ht').div_const v using 1;
 simp [id];field_simp [hv,ht];ring
end
theorem angular_endpoints (v : ℝ) (hv:v≠0) (hm:1-v≠0) (hp:1+v≠0) :
 (((v^2-1)/(1-v)-2*real.log(1-v)+(1-v))-
 ((v^2-1)/(1+v)-2*real.log(1+v)+(1+v)))/v
 =2/v*(real.log(1+v)-real.log(1-v))-4 :=
by field_simp [hv,hm,hp];ring
theorem ir_pair_bound (w t : ℝ) (h : w≠0) (h2 : (2-2*real.cos(w*t))≤(w*t)^2)
 (hw:0<w) : (2-2*real.cos(w*t))/w ≤ w*t^2 :=
begin rw [div_le_iff hw]; nlinarith only [h2] end

-- Horizon response identities. ADM parameters and the first law are physical inputs.
theorem boost_potential (s c : ℝ) (hc:c≠0) (h:c^2=1+s^2) :
 1-(s/c)^2=1/c^2 := by field_simp [hc];linear_combination h
theorem grav_firstlaw (r s c dr db : ℝ) (hc:c≠0) (h:c^2=1+s^2) :
 (2+s^2)*dr+2*r*s*c*db - (s/c)*(s*c*dr+r*(c^2+s^2)*db)
 =2*dr+r*s/c*db :=
begin field_simp [hc];linear_combination (r*s*db)*h end
theorem boost_variation (r s c dr db : ℝ) (hc:c≠0) (h:c^2=1+s^2) :
 s*c*dr+r*(c^2+s^2)*db-s*c*(2*dr+r*s/c*db)/2
 =r*(1+3*s^2/2)*db :=
begin field_simp [hc];linear_combination (4*r*c*db)*h end
theorem entropy_hessian (g h p s c r d : ℝ) (hc:c≠0) (hr:r≠0) (hd:d≠0) :
 h*(2*g*h/r+s/c*(4*g*(p-s*c*h/2)/(r*d))/2)
 -p*(4*g*(p-s*c*h/2)/(r*d))/c^2 =
 2*g*h^2/r-4*g*(p-s*c*h/2)^2/(r*d*c^2) :=
by field_simp [hc,hr,hd];ring
theorem horizon_doublet (b h p v : ℝ) :
 b*((h+v*p)-v*p)=b*h := by ring
theorem horizon_potential_split (g d r c D p a : ℝ) :
 4*g*(p+d-a)/(r*D*c^2)-4*g*(p-d-a)/(r*D*c^2)=8*g*d/(r*D*c^2) :=
by ring
theorem entropy_doublet (g r D c h pc d : ℝ) (hr:r≠0) (hD:D≠0) (hc:c≠0) :
 (4*real.pi*r*c)/2*
 ((2*g*h^2/r-4*g*((pc+d)-pc/2)^2/(r*D*c^2))-
  (2*g*h^2/r-4*g*((pc-d)-pc/2)^2/(r*D*c^2))) =
 -16*real.pi*g*pc*d/(c*D) :=
by field_simp [hr,hD,hc];ring
theorem radial_reflection (w k f L V : ℝ) :
 w^2-f*((-k)^2+L+V)=w^2-f*(k^2+L+V) := by ring
theorem entropy_inversion (u q : ℝ) (hh : q*(2-u^2)=u) :
 q*u^2+u-2*q=0 := by linear_combination -hh

-- Neutral half-weight subdivision allows no nontrivial deterministic sign.
theorem refinement_kills_binary (F : ℝ → ℂ) (w : ℝ)
 (split : F w=F (w/2)*F (w/2)) (involution : ∀ u, F u*F u=1) : F w=1 :=
split.trans (involution _)
theorem split_real_nonnegative (F : ℝ → ℝ) (w : ℝ)
 (split : F w=F (w/2)*F (w/2)) : 0≤F w :=
by rw [split];exact mul_self_nonneg _
theorem weighted_composition (a p q : ℝ) :
 real.exp ((p+q)*a)=real.exp (p*a)*real.exp (q*a) :=
by rw [add_mul,real.exp_add]
theorem negative_switch_cannot_divide (p m : ℝ) (h : 1/2<p) :
 1-2*p≠m*m := by nlinarith [mul_self_nonneg m]
theorem one_event_correlation (p q : ℝ) :
 1-2*(q-p)=1-(1-2*p)+(1-2*q) := by ring
theorem two_time_gap (a b : ℝ) (ha : a≠0) :
 1-a+b-b/a=(1-a)*(1-b/a) := by field_simp;ring
theorem spurious_return_positive (a b : ℝ) (ha : 0<a) (h1 : a<1) (hb : b<a) :
 0<(1-a)*(1-b/a)/4 :=
begin have h2 : b/a<1 := (div_lt_one ha).mpr hb,
 exact div_pos (mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2)) (by norm_num) end
theorem donor_recoil_sign (l m : ℝ) :
 1-2*(l^2/2*(1-m))=1-l^2+l^2*m := by ring
theorem survival_deriv (x : ℝ) :
 has_deriv_at (λ t:ℝ,real.exp (-t)*(1+t+t^2/2)) (-real.exp(-x)*x^2/2) x :=
begin have hi := has_deriv_at_id x,
 have hp := ((has_deriv_at_const x (1:ℝ)).add hi).add ((hi.pow 2).div_const 2),
 convert hi.neg.exp.mul hp using 1;simp [id];ring end
theorem material_flip_rate (x g : ℝ) (h : 1+x+x^2/2≠0) :
 -2*(g*x^2/(4*(1+x+x^2/2)))*(real.exp (-x)*(1+x+x^2/2))
 =g*(-real.exp(-x)*x^2/2) :=
begin generalize hh : (1+x+x^2/2)=d, rw [hh] at h, field_simp [h];ring end
theorem tilted_mixture_y (x a : ℝ) :
 (x*real.sin a+(-x)*real.sin (-a))/2=x*real.sin a := by rw [real.sin_neg];ring

-- Finite topological form of the direct sign.
theorem electric_dimension (D : ℕ) (hD : 2≤D) : (D-2)+(D-2)=D ↔ D=4 := by omega
theorem higher_form_dimension (D p : ℤ) : 2*(D-p-1)=D ↔ D=2*p+2 :=
by split;intro h;linarith
theorem exact_shift_invisible {A : Type*} [add_comm_group A] (I : A →+ ℤ)
 (b e : A) (h : I e=0) : I (b+e)=I b := by rw [map_add,h,add_zero]
theorem character_cancel {ι : Type*} [fintype ι] (e : ι ≃ ι) (f : ι → ℝ)
 (h : ∀ i, f (e i)= -f i) : ∑ i,f i=0 :=
begin have he:=e.sum_comp f, simp_rw [h,finset.sum_neg_distrib] at he,linarith end
theorem auxiliary_sum {ι : Type*} [fintype ι] [decidable_eq ι]
 (H : ι → ι → ℝ) (a b : ι) (N : ℝ)
 (horth : ∀ v, ∑ u, H u v*H u a= if v=a then N else 0) :
 (∑ v, ∑ u, H u v*H u a*H v b)=N*H a b :=
begin simp_rw [←finset.sum_mul,horth],simp [ite_mul] end
theorem moving_holonomy_charge (k n x : ℝ) : (k+x)-((k-n)+x)=n := by ring
theorem large_gauge (k x z : ℝ) : (k-z)+(x+z)=k+x := by ring
theorem split_at_half_flux (a b delta : ℝ) (h : 2*a=1) :
 (b^2-(1-(a+delta))^2)-(b^2-(0-(a+delta))^2)=2*delta :=
by linear_combination h
theorem holonomy_ratio (chi M w R : ℝ) (hM:M≠0) (hw:w≠0) (hR:R≠0) :
 1+2*(w*chi/M)/(R*w)^2 =1+2*chi/(M*w*R^2) := by field_simp [hM,hw,hR];ring
theorem half_flux_example : 1+1/((1000:ℝ)*(2/3))=1.0015 := by norm_num
theorem kinetic_square (v mean : ℝ) : v^2-2*v*mean+mean^2=(v-mean)^2 := by ring
theorem half_shift_cost (I T A d : ℝ) (hI:0<I) (hT:0<T)
 (hA : d^2≤T*A) (hd : 1/4≤d^2) : I/(8*T)≤I*A/2 :=
begin apply (div_le_iff (show 0<8*T,by positivity)).mpr,
 have hn : 0≤I*(T*A-1/4) := mul_nonneg hI.le (sub_nonneg.mpr (le_trans hd hA)),
 nlinarith only [hn] end
theorem half_shift_peak (I T A P : ℝ) (hT:0<T) (ha:I/(8*T)≤A) (hp:A≤P*T) :
 I/(8*T^2)≤P :=
begin have ha' := (div_le_iff (show 0<8*T,by positivity)).mp (le_trans ha hp),
 apply (div_le_iff (show 0<8*T^2,by positivity)).mpr,nlinarith only [ha'] end

-- Pair the cochains with a closed four-cycle over F2. The two Stokes
-- identities and the exact/exact identity are the hypotheses supplied by
-- the cup-product Leibniz law for this closed cycle.
theorem sheet_variation {K : Type*} [comm_ring K]
 (base di dj dij left right : K) (hi : di=left) (hj : dj=right) (hij : dij=0) :
 base+di+dj+dij-base=left+right := by rw [hi,hj,hij];ring
theorem attach_endpoints {K : Type*} [comm_ring K]
 (base ai aj l r : K) (hl : l+l=0) (hr : r+r=0) :
 (base+l+r)+(ai+l)+(aj+r)=base+ai+aj :=
begin linear_combination hl+hr end
theorem unreceived_character (a : ℝ) : (a+(-a))/2=0 := by ring

theorem universal_radion_gamma : (1-(1:ℝ)/3)/(1+1/3)=1/2 := by norm_num
theorem weak_metric_ratio (a : ℝ) : (1-a^2)/(1+a^2)-1= -2*a^2/(1+a^2) :=
begin have h : 1+a^2≠0 := by positivity,field_simp [h];ring end
-- Continuous multiplicative parity means on nonnegative exposure weights.
-- Values at negative arguments of m play no role; a continuous function on
-- the half-line can be extended there by x ↦ m(max x 0).
theorem exposure_power (m : ℝ → ℝ) (hz : m 0=1)
 (ha : ∀ x y:ℝ, 0≤x → 0≤y → m (x+y)=m x*m y)
 (x : ℝ) (hx : 0≤x) : ∀ n:ℕ, m ((n:ℝ)*x)=(m x)^n :=
begin intro n,induction n with n ih,
 {simp [hz]}, {rw [nat.cast_succ,add_mul,one_mul,ha ((n:ℝ)*x) x (mul_nonneg (nat.cast_nonneg _) hx) hx,ih,pow_succ],exact mul_comm _ _} end

theorem exposure_positive (m : ℝ → ℝ) (hz : m 0=1) (hm : continuous m)
 (ha : ∀ x y:ℝ, 0≤x → 0≤y → m (x+y)=m x*m y)
 (x : ℝ) (hx : 0≤x) : 0<m x :=
begin
 have seq : filter.tendsto (λ n:ℕ,m (x/(n:ℝ))) filter.at_top (nhds (m 0)) :=
 hm.continuous_at.tendsto.comp (tendsto_const_div_at_top_nhds_0_nat x),
 rw [hz] at seq,
 have good := (tendsto_order.1 seq).1 (0:ℝ) (by norm_num),
 rcases (good.and (filter.eventually_gt_at_top (0:ℕ))).exists with ⟨n,hn,hN⟩,
 have hc : 0<(n:ℝ) := by exact_mod_cast hN,
 have repr : (n:ℝ)*(x/(n:ℝ))=x := by field_simp [ne_of_gt hc];ring,
 rw [←repr,exposure_power m hz ha _ (div_nonneg hx hc.le) n],exact pow_pos hn n
end

theorem exposure_exponential (m : ℝ → ℝ) (hz : m 0=1) (hm : continuous m)
 (ha : ∀ x y:ℝ, 0≤x → 0≤y → m (x+y)=m x*m y)
 (x : ℝ) (hx : 0≤x) : m x=real.exp (x*real.log(m 1)) :=
begin
 have pos := exposure_positive m hz hm ha,
 let p : ℝ → ℝ := λ t,max t 0,
 have hpn : ∀ t,0≤p t := λ t,le_max_right _ _,
 have hdiff : ∀ t,p t-p (-t)=t :=
 by {intro t,dsimp [p],simp only [max_def],split_ifs;linarith},
 have hlog : ∀ t u,0≤t → 0≤u →
 real.log(m(t+u))=real.log(m t)+real.log(m u) :=
 λ t u ht hu,by rw [ha t u ht hu,real.log_mul (ne_of_gt (pos t ht)) (ne_of_gt (pos u hu))],
 let f : ℝ →+ ℝ :=
 {to_fun:=λ t,real.log(m(p t))-real.log(m(p(-t))),
  map_zero':=by simp,
  map_add':=begin
    intros y z,
    have iden : (p(y+z)+p(-y))+p(-z)=(p(-(y+z))+p y)+p z :=
    by linarith [hdiff y,hdiff z,hdiff (y+z)],
    have j := congr_arg (λ t, real.log(m t)) iden,
    dsimp only at j,
    rw [hlog _ _ (add_nonneg (hpn _) (hpn _)) (hpn _),hlog _ _ (hpn _) (hpn _),
        hlog _ _ (add_nonneg (hpn _) (hpn _)) (hpn _),hlog _ _ (hpn _) (hpn _)] at j,
    linarith end},
 have hp : continuous p := continuous_id.max continuous_const,
 have he : continuous (λ t, real.log(m(p t))) :=
 (hm.comp hp).log (λ t,ne_of_gt (pos _ (hpn _))),
 have hf : continuous f := he.sub (he.comp continuous_neg),
 have ff := map_real_smul f hf x (1:ℝ),
 have hn : -x≤0 := by linarith,
 simp [f,p,smul_eq_mul,max_eq_left hx,max_eq_right hn,hz] at ff,
 rw [←ff,real.exp_log (pos x hx)]
end

theorem exposure_rate (m : ℝ → ℝ) (hz : m 0=1) (hm : continuous m)
 (ha : ∀ x y:ℝ, 0≤x → 0≤y → m (x+y)=m x*m y)
 (hbound : m 1≤1) : ∃ μ:ℝ,0≤μ ∧ ∀ x:ℝ,0≤x → m x=real.exp(-2*μ*x) :=
begin
 have hp := exposure_positive m hz hm ha 1 (by norm_num),
 have hl : real.log(m 1)≤0 := real.log_nonpos hp.le hbound,
 refine ⟨-real.log(m 1)/2,by linarith,_⟩,
 intros x hx,rw [exposure_exponential m hz hm ha x hx],congr' 1;ring
end

end wrapped_capture
