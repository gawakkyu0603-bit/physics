import tactic
import topology.homotopy.contractible
import analysis.normed_space.basic
import analysis.analytic.uniqueness
import analysis.special_functions.exp_deriv
import analysis.calculus.bump_function_inner
import measure_theory.integral.set_integral
import measure_theory.measure.open_pos

noncomputable theory
open set continuous_map filter measure_theory
open_locale unit_interval topology big_operators

namespace cat_observer_domains

variables {V : Type*} [normed_add_comm_group V]

def past (events : set (ℝ × V)) : set (ℝ × V) :=
 {p | ∃ (e : ℝ × V) (he : e∈events), p.1 + ‖p.2-e.2‖ < e.1}

def causal (p q : ℝ × V) : Prop := p.1 + ‖p.2-q.2‖ ≤ q.1

theorem open_past (events : set (ℝ × V)) : is_open (past events) :=
begin
 have eqn : past events = ⋃ (e : events), {p : ℝ × V | p.1 + ‖p.2-e.val.2‖ < e.val.1},
 { ext p, split,
   { rintro ⟨e,he,ht⟩, exact mem_Union.mpr ⟨⟨e,he⟩,ht⟩ },
   { intro h, rcases mem_Union.mp h with ⟨e,ht⟩, exact ⟨e.val,e.property,ht⟩ } },
 rw [eqn], apply is_open_Union, intro e,
 exact is_open_lt (continuous_fst.add (continuous_snd.sub continuous_const).norm) continuous_const
end

theorem causal_downset {events : set (ℝ × V)} {p q : ℝ × V}
 (hq : q ∈ past events) (hpq : causal p q) : p ∈ past events :=
begin
 rcases hq with ⟨e,he,ht⟩, refine ⟨e,he,_⟩, unfold causal at hpq,
 have tri := dist_triangle p.2 q.2 e.2, simp only [dist_eq_norm] at tri,
 linarith
end

def diamond {X : Type*} (rel : X → X → Prop) (p q : X) : set X :=
 {x | rel p x ∧ rel x q}

theorem intrinsic_diamond_compact {X : Type*} [topological_space X]
 (rel : X → X → Prop) (U : set X) (p q : U)
 (convex : diamond rel p.val q.val ⊆ U) (ambient : is_compact (diamond rel p.val q.val)) :
 is_compact (diamond (λ a b : U, rel a.val b.val) p q) :=
begin
 rw [is_compact_iff_is_compact_in_subtype],
 have eqn : subtype.val '' diamond (λ a b : U, rel a.val b.val) p q = diamond rel p.val q.val,
 { ext x, split,
   { rintro ⟨y,hy,rfl⟩, exact hy },
   { intro hx, exact ⟨⟨x,convex hx⟩,hx,rfl⟩ } },
 change is_compact (subtype.val '' diamond (λ a b : U, rel a.val b.val) p q),
 rwa [eqn]
end

theorem past_contains_diamond {events : set (ℝ × V)} (p q : past events) :
 diamond causal p.val q.val ⊆ past events :=
λ x hx, causal_downset q.property hx.2

def floor_time (e : ℝ × V) (x : V) : ℝ := e.1-1-‖x-e.2‖

theorem floor_mem {E : set (ℝ × V)} {e : ℝ × V} (he : e ∈ E) (x : V) :
 (floor_time e x, x) ∈ past E :=
by { refine ⟨e,he,_⟩, change e.1-1-‖x-e.2‖+‖x-e.2‖<e.1, linarith }

theorem floor_continuous (e : ℝ × V) : continuous (floor_time e) :=
continuous_const.sub (continuous_id.sub continuous_const).norm

theorem vertical_mem {E : set (ℝ × V)} {e : ℝ × V} (he : e∈E)
 (y : past E) (s : I) :
 ((1-(s:ℝ))*y.val.1+(s:ℝ)*floor_time e y.val.2,y.val.2) ∈ past E :=
begin
 let g := floor_time e y.val.2,
 change ((1-(s:ℝ))*y.val.1+(s:ℝ)*g,y.val.2) ∈ past E,
 cases le_total y.val.1 g with h h,
 { apply causal_downset (floor_mem he y.val.2),
   change (1-(s:ℝ))*y.val.1+(s:ℝ)*g+‖y.val.2-y.val.2‖≤g,
   rw [sub_self,norm_zero,add_zero],
   change (1-s.val)*y.val.1+s.val*g≤g,
   nlinarith only [mul_nonneg (sub_nonneg.mpr s.property.2) (sub_nonneg.mpr h)] },
 { apply causal_downset y.property,
   change (1-(s:ℝ))*y.val.1+(s:ℝ)*g+‖y.val.2-y.val.2‖≤y.val.1,
   rw [sub_self,norm_zero,add_zero],
   change (1-s.val)*y.val.1+s.val*g≤y.val.1,
   nlinarith only [mul_nonneg s.property.1 (sub_nonneg.mpr h)] }
end

/-- Any nonempty collection of receivers, including a continuum, is allowed. -/
theorem contractible_past [normed_space ℝ V] {E : set (ℝ × V)} (nonempty_events : E.nonempty) :
 contractible_space (past E) :=
begin
 obtain ⟨e,he⟩ := nonempty_events,
 let graph : V → past E := λ x, ⟨(floor_time e x,x),floor_mem he x⟩,
 have gcont : continuous graph := ((floor_continuous e).prod_mk continuous_id).subtype_mk _,
 let projection : C(past E,past E) :=
 ⟨λ y, graph y.val.2, gcont.comp continuous_subtype_coe.snd⟩,
 let H : (continuous_map.id (past E)).homotopy projection :=
 { to_fun := λ p, ⟨(_,p.2.val.2), vertical_mem he p.2 p.1⟩,
   continuous_to_fun := begin
     apply continuous.subtype_mk,
     have time : continuous (λ p : I × past E, (p.1:ℝ)) :=
       continuous_subtype_coe.comp continuous_fst,
     have pos : continuous (λ p : I × past E, p.2.val) :=
       continuous_subtype_coe.comp continuous_snd,
     exact (((continuous_const.sub time).mul pos.fst).add
       (time.mul ((floor_continuous e).comp pos.snd))).prod_mk pos.snd
   end,
   map_zero_left' := λ y, subtype.ext (by { rcases y with ⟨⟨t,x⟩,hy⟩, simp }),
   map_one_left' := λ y, subtype.ext (by { change ((1-(1:ℝ))*_+1*_,_) = (_, _), simp }) },
 let K : projection.homotopy (continuous_map.const _ (graph 0)) :=
 { to_fun := λ p, graph ((1-(p.1:ℝ)) • p.2.val.2),
   continuous_to_fun := gcont.comp ((continuous_const.sub (continuous_subtype_coe.comp
     continuous_fst)).smul (continuous_subtype_coe.comp continuous_snd).snd),
   map_zero_left' := λ y, by { change graph ((1-(0:ℝ)) • y.val.2) = graph y.val.2, simp },
   map_one_left' := λ y, by { change graph ((1-(1:ℝ)) • y.val.2) = graph 0, simp } },
 exact (contractible_iff_id_nullhomotopic _).mpr ⟨graph 0,⟨H.trans K⟩⟩
end

-- Put an entire bounded protocol into any scaled open image containing the radius-r ball.
theorem place_bounded_protocol [normed_space ℝ V] (U D : set V) (c : V) (r M a : ℝ)
 (ha : 0<a) (size : M<a*r) (inside : ∀ x : V, ‖x-c‖<r → x∈U)
 (bounded : ∀ x∈D, ‖x‖≤M) : D ⊆ (λ y : V, a • (y-c)) '' U :=
begin
 intros x hx, let y := a⁻¹ • x + c,
 have dy : y-c=a⁻¹ • x := add_sub_cancel _ _,
 have hnorm : ‖y-c‖<r,
 { rw [dy,norm_smul,real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha),inv_mul_eq_div],
   apply (div_lt_iff ha).mpr, linarith [bounded x hx] },
 refine ⟨y,inside y hnorm,_⟩, change a • (y-c)=x,
 rw [dy,smul_smul,mul_inv_cancel (ne_of_gt ha),one_smul]
end

-- The Fock representation identifies each nonzero vector with a nonzero entire f.
-- The measure and weight may be any full-support measure and positive continuous density.
theorem positive_analytic_receipt
 (μ : measure (ℂ × ℂ)) [measure.is_open_pos_measure μ]
 (U : set (ℂ × ℂ)) (hU : is_open U) (hne : U.nonempty)
 (f : (ℂ × ℂ) → ℂ) (hf : analytic_on ℂ f univ) (nonzero : f≠0)
 (weight : (ℂ × ℂ) → ℝ) (hw : continuous weight) (hwpos : ∀ z, 0<weight z)
 (hfin : integrable_on (λ z, weight z*‖f z‖^2) U μ) :
 0 < ∫ z in U, weight z*‖f z‖^2 ∂μ :=
begin
 let d := λ z, weight z*‖f z‖^2,
 have nonneg : ∀ z, 0≤d z := λ z, mul_nonneg (hwpos z).le (sq_nonneg _),
 have df : continuous f := continuous_iff_continuous_on_univ.mpr hf.continuous_on,
 have dc : continuous d := hw.mul (df.norm.pow 2),
 by_contra h,
 have eqzero : ∫ z in U, d z ∂μ = 0 :=
   le_antisymm (not_lt.mp h) (integral_nonneg nonneg),
 have ae := (set_integral_eq_zero_iff_of_nonneg_ae (eventually_of_forall nonneg) hfin).mp eqzero,
 have zcont : continuous_on (0 : (ℂ × ℂ) → ℝ) U :=
   (continuous_const : continuous (λ x : ℂ × ℂ, (0:ℝ))).continuous_on,
 have local_zero := measure.eq_on_open_of_ae_eq ae hU dc.continuous_on zcont,
 obtain ⟨z,hz⟩ := hne, apply nonzero,
 apply hf.eq_of_eventually_eq (analytic_on_const : analytic_on ℂ (λ x : ℂ × ℂ, (0:ℂ)) univ),
 filter_upwards [hU.mem_nhds hz] with p hp,
 have hp0 : weight p*‖f p‖^2=0 := local_zero hp,
 have hn : ‖f p‖^2=0 := (mul_eq_zero.mp hp0).resolve_left (hwpos p).ne',
 exact norm_eq_zero.mp (pow_eq_zero hn)
end

theorem nonprojective_of_strict_receipt {H : Type*} [add_group H]
 (effect : H → H) (state : H) (hn : state≠0)
 (positive : ∀ x, x≠0 → effect x≠0) (loss : ∀ x, x≠0 → effect x≠x) :
 ¬(∀ x, effect (effect x)=effect x) :=
λ idem, loss (effect state) (positive state hn) (idem state)

def gaussian_tail (s : ℝ) : ℝ := (1+s)*real.exp (-s)

theorem two_mode_tail_derivative (s : ℝ) :
 has_deriv_at gaussian_tail (-s*real.exp (-s)) s :=
begin
 have h := ((has_deriv_at_const s (1:ℝ)).add (has_deriv_at_id s)).mul (has_deriv_at_id s).neg.exp,
 convert h using 1, dsimp, ring
end

theorem two_mode_tail_vanishes : tendsto gaussian_tail at_top (𝓝 0) :=
begin
 have h := real.tendsto_exp_neg_at_top_nhds_0.add (real.tendsto_pow_mul_exp_neg_at_top_nhds_0 1),
 change tendsto (λ x : ℝ, (1+x)*real.exp (-x)) at_top (𝓝 0),
 simpa only [gaussian_tail,add_mul,one_mul,pow_one,zero_add] using h
end

theorem shared_buffer_bound (p q tail : ℝ) (pl : 1-tail≤p) (ql : 1-tail≤q)
 (pu : p≤1) (qu : q≤1) : |p-q|≤tail :=
by {rw [abs_le],constructor;linarith}

def comm {A : Type*} [ring A] (x y : A) := x*y-y*x

theorem restrict_matrix_equation {A B J : Type*} [ring A] [ring B] [fintype J]
 (res : A →+* B) (lo hi : J → A) (x : A)
 (solves : ∑ j, comm (lo j) (comm (hi j) x) = 0) :
 ∑ j, comm (res (lo j)) (comm (res (hi j)) (res x)) = 0 :=
begin
 have h := congr_arg res solves,
 rw [map_sum, map_zero] at h, simpa only [comm,map_sub,map_mul] using h
end

def angle (u : ℝ) := real.exp 1 * exp_neg_inv_glue u

theorem smooth_angle : cont_diff ℝ ⊤ angle := cont_diff_const.mul exp_neg_inv_glue.cont_diff

theorem common_past (u : ℝ) (h : u≤0) : angle u=0 :=
by simp [angle,exp_neg_inv_glue.zero_of_nonpos h]

theorem angle_rate (u : ℝ) (hu : 0<u) :
 has_deriv_at angle (real.exp 1*(real.exp (-u⁻¹)*u⁻¹^2)) u :=
begin
 have h := ((has_deriv_at_const u (real.exp 1)).mul
   (((has_deriv_at_id u).inv (ne_of_gt hu)).neg.exp)),
 have hx : has_deriv_at (λ x : ℝ, real.exp 1*real.exp (-x⁻¹))
     (real.exp 1*(real.exp (-u⁻¹)*u⁻¹^2)) u,
 { convert h using 1, dsimp, field_simp [ne_of_gt hu] },
 apply hx.congr_of_eventually_eq,
 filter_upwards [lt_mem_nhds hu] with x hx,
 simp [angle,exp_neg_inv_glue,not_le.mpr hx]
end

theorem positive_rotation (u : ℝ) (hu : 0<u) :
 0<real.exp 1*(real.exp (-u⁻¹)*u⁻¹^2) := by positivity

theorem unit_rotation_at_one :
 real.exp 1*(real.exp (-(1:ℝ)⁻¹)*(1:ℝ)⁻¹^2)=1 :=
by simp [←real.exp_add]

theorem tidal_rotation_norm (s c t radial angular : ℝ) (unit : c^2+t^2=1) :
 let x:=radial*c-angular*t, y:=radial*t+angular*c in
 (s*x-y)^2+(x+s*y)^2=(s^2+1)*(radial^2+angular^2) :=
begin
 dsimp, linear_combination (s^2+1)*(radial^2+angular^2)*unit
end

theorem curved_vacuum (s a b : ℝ) (hs : 0<s) (circle : a^2+b^2=s) :
 2*((a^2+b^2)/s^2-1/s)=0 := by {rw [circle],field_simp [ne_of_gt hs],ring}

theorem tides_at_one :
 (2^2+1)*((1:ℝ)^2/2^5+0^2/2^3)=5/32 ∧
 (2^2+1)*((1:ℝ)^2/2^5+1^2/2^3)=25/32 := by norm_num

theorem tides_split (s u rate : ℝ) (hs : 0<s) (hr : 0<rate) :
 (s^2+1)*(u^2/s^5)<(s^2+1)*(u^2/s^5+rate^2/s^3) :=
by {apply mul_lt_mul_of_pos_left, apply lt_add_of_pos_right, positivity, positivity}

theorem common_metric_error (a b fit ea eb : ℝ) (ha : |a-fit|≤ea) (hb : |b-fit|≤eb) :
 |a-b|≤ea+eb :=
begin
 rw [abs_le] at *, constructor;linarith [ha.1,ha.2,hb.1,hb.2]
end

theorem common_historical_limit {X : Type*} [topological_space X] [t2_space X]
 (history : ℕ → X) (p q : X) (hp : tendsto history at_top (𝓝 p))
 (hq : tendsto history at_top (𝓝 q)) : p=q := tendsto_nhds_unique hp hq

-- For a degree-four v-probe the third derivative term is the last odd Moyal term.
theorem quartic_null_probe (phi1 phi3 h v : ℝ) :
 2*(12*v^2*phi1 - h^2/24*24*phi3) - 24*v^2*phi1 = -2*h^2*phi3 :=
by ring

theorem midpoint_screen {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] (a b : E) :
 ‖a - (2:ℝ)⁻¹ • (a+b)‖ = (2:ℝ)⁻¹ * ‖a-b‖ :=
begin
 have d : a - (2:ℝ)⁻¹ • (a+b) = (2:ℝ)⁻¹ • (a-b),
 { rw [smul_add,smul_sub], have h : a = (2:ℝ)⁻¹ • a + (2:ℝ)⁻¹ • a,
   { rw [←add_smul],norm_num },
   calc a - ((2:ℝ)⁻¹ • a + (2:ℝ)⁻¹ • b) =
     ((2:ℝ)⁻¹ • a + (2:ℝ)⁻¹ • a) - ((2:ℝ)⁻¹ • a + (2:ℝ)⁻¹ • b) :
     congr_arg (λ z : E, z - ((2:ℝ)⁻¹ • a + (2:ℝ)⁻¹ • b)) h
   ... = _ : by abel },
 rw [d,norm_smul_of_nonneg (by norm_num : 0≤(2:ℝ)⁻¹)]
end

theorem lightcone_shell (n R p2 : ℝ) (hn : n≠0) (hR : R≠0) :
 2*(n/R)*(R*p2/(2*n))=p2 := by {field_simp [hn,hR],ring}

theorem relative_transfer_cost (n m q : ℝ) (hn : n≠0) (hm : m≠0)
 (hp : n+q≠0) (hq : m-q≠0) :
 1/(n+q)+1/(m-q) = (1/n+1/m)*(1+q*(n-m+q)/((n+q)*(m-q))) :=
by {field_simp [hn,hm,hp,hq],ring}

theorem equal_energy_swap (c : ℝ) : c*(1/3+1/4)=c*(1/4+1/3) := by ring

theorem active_write_visibility (z : ℂ) :
 (1:ℂ)/2*z+1/2*z=z ∧ ((1:ℂ)*0+0*1)*z=0 := by {split;ring}

-- Continuous families of conditionings can live in a single represented vacuum sector.
theorem conditional_stays_in_sector {M : Type*} [ring M] (z k rho kd : M)
 (central : z*k=k*z) (supported : z*rho=rho) :
 z*(k*rho*kd)=k*rho*kd :=
by rw [←mul_assoc,←mul_assoc,central,mul_assoc k z rho,supported]

theorem likelihood_does_not_create_prior_mass (weight like norm : ℝ) (h : weight=0) :
 weight*like/norm=0 := by simp [h]

theorem same_sector_resolving_bit (eta : ℝ) :
 ((1+eta)/4)/((1+eta)/4+(1-eta)/4)=(1+eta)/2 :=
by { have h : (1+eta)/4+(1-eta)/4=1/2 := by ring, rw [h],ring }

-- Reversing the Legendre transform before expanding the probe Hamiltonian.
theorem kinetic_probe_remainder (p k y : ℝ) (h : 1-k*y≠0) :
 p^2/(2*(1-k*y)) - p^2/2 - k*p^2*y/2 = p^2*(k*y)^2/(2*(1-k*y)) :=
by { field_simp [h], ring }

-- H=(-e² d² + x⁴)/2 and K=-e² d² on smooth test functions.
-- f0..f4 are the jets of the same test function at x.
theorem first_commutator (e x f0 f1 f2 f4 : ℝ) :
 (-e^2*(-e^2*f4)+x^4*(-e^2*f2))/2
 - (-e^2)*(-e^2*f4+12*x^2*f0+8*x^3*f1+x^4*f2)/2 =
 e^2*(6*x^2*f0+4*x^3*f1) := by ring

theorem second_commutator (e x f0 f1 f2 f3 : ℝ) (he : e≠0) :
 -(( -e^2*(e^2*(12*f0+48*x*f1+30*x^2*f2+4*x^3*f3))
     +x^4*(e^2*(6*x^2*f0+4*x^3*f1)) )/2
   - e^2*(6*x^2*((-e^2*f2+x^4*f0)/2)+4*x^3*((-e^2*f3+4*x^3*f0+x^4*f1)/2)))/e^2
 = 8*x^6*f0+12*e^2*(2*x*f1+x^2*f2)+6*e^2*f0 :=
by { field_simp [he], ring }

theorem turn_moment_curvature (a r qpp : ℝ) (ha : a≠0) (hr : r≠0) :
 -2*(qpp/(4*r^3))/(a^2*r^3) = -qpp/(2*a^2*r^6) :=
by {field_simp [ha,hr],ring}

theorem positive_force_defocuses (a r force mixed order : ℝ)
 (ha : 0<a) (hr : 0<r) (dominance : mixed<force+order) :
 -(force-mixed+order)/(2*a^2*r^6)<0 :=
by { apply div_neg_of_neg_of_pos, linarith, positivity }

-- In the exact homogeneous branch V_cell/(4π Δζ) = a R.
theorem volume_lower_bound (a L E q : ℝ) (he : 0≤E)
 (speed : L^2≤a^2*q) (radius : L^2≤E*a^2) :
 L^4≤E*a^4*q :=
begin
 calc L^4 = L^2*L^2 : by ring
 ... ≤ (E*a^2)*(a^2*q) : mul_le_mul radius speed (sq_nonneg _) (mul_nonneg he (sq_nonneg a))
 ... = _ : by ring
end

theorem simultaneous_volume_area_turn :
 let w : ℝ := 1/4, ar := w-2, qrr := -4*ar, vrr := 4*(w-1)*(w-2) in
 qrr=7 ∧ vrr=21/4 ∧ -2*qrr/(4*w*(1/2))= -28 ∧ vrr/(4*w*(1/2))=21/2 :=
by norm_num

theorem flat_open_flrw_null (k a hdot : ℝ) (hk : k≤0) (ha : 0<a) (hh : 0<hdot) :
 2*(k/a^2-hdot)<0 :=
by {have h := div_nonpos_of_nonpos_of_nonneg hk (sq_nonneg a), linarith}

theorem eikonal_integral_endpoints :
 let f := λ y : ℝ, y-2*y^3/3+y^5/5 in f 1-f (-1)=16/15 :=
by norm_num

theorem eikonal_primitive (y : ℝ) :
 has_deriv_at (λ x : ℝ, x-2*x^3/3+x^5/5) ((1-y^2)^2) y :=
begin
 have dy := has_deriv_at_id y,
 have h := (dy.sub (((dy.pow 3).const_mul 2).div_const 3)).add ((dy.pow 5).div_const 5),
 convert h using 1, dsimp, norm_num, ring
end

-- Differentiation of exp(-k*r)*(1+k*r)/r^3 produces the next Fourier kernel.
theorem membrane_fourier_recursion (r k ex : ℝ) (hr : r≠0) :
 -((-k*ex*(1+k*r)+ex*k)/r^3-3*ex*(1+k*r)/r^4)/(4*r)/2 =
 ex*(3+3*k*r+(k*r)^2)/(8*r^5) := by {field_simp [hr],ring}

theorem anticomm_gap {A : Type*} [ring A] (x y : A) (h : x*y+y*x=0) :
 (x+y)*(x+y)=x*x+y*y :=
by {rw [add_mul,mul_add,mul_add], rw [←add_assoc,add_assoc (x*x),h,add_zero]}

theorem oriented_contact (j : ℝ) (h : 0<j) :
 -j/2<0 ∧ 0<j/2 ∧ 4*(-j/2)+4*(j/2)=0 := by {split,linarith,split,linarith,ring}

end cat_observer_domains
