import tactic
import analysis.calculus.mean_value
import analysis.special_functions.integrals

noncomputable theory
namespace mixed_flux_memory

-- Retarded spherical response on a conformally flat dust background.
theorem radial_receipt (L a D x : ℝ) (ha : a ≠ 0) (hx : x ≠ 0)
 (hp : D+x ≠ 0) (hm : D-x ≠ 0) :
 (6*L/(D-x)-6*L/(D+x))/(2*a*x)=6*L/(a*((D-x)*(D+x))) :=
by {field_simp [ha,hx,hp,hm],ring}

theorem receipt_gradient (L a D x : ℝ) (ha : a ≠ 0) (hd : D^2-x^2 ≠ 0) :
 has_deriv_at (λ y:ℝ,6*L/(a*(D^2-y^2)))
 (12*L*x/(a*(D^2-x^2)^2)) x :=
begin
 have h := (has_deriv_at_const x (6*L)).div
   ((has_deriv_at_const x a).mul
    ((has_deriv_at_const x (D^2)).sub ((has_deriv_at_id x).pow 2)))
   (show a*(D^2-x^2)≠0, from mul_ne_zero ha hd),
 convert h using 1,
 dsimp, field_simp [ha,hd], ring
end

theorem positive_receipt (L a x D : ℝ) (hL : 0<L) (ha : 0<a) (hx : 0<x)
 (hd : D^2-x^2≠0) : 0<12*L*x/(a^2*(D^2-x^2)^2) :=
div_pos (by positivity) (mul_pos (sq_pos_of_pos ha) (sq_pos_of_ne_zero _ hd))

theorem full_receipt_deadline (start L x deadline : ℝ) :
 start+L+x < deadline ↔ start < (deadline-L)-x := by split; intro h; linarith

theorem positive_dust_time (a t₁ t₂ : ℝ) (ha : 0<a) (h₁ : 0<t₂) (h₂ : t₂<t₁) :
 0<a*(t₁^3-t₂^3)/3 :=
begin
 have h : t₁^3-t₂^3=(t₁-t₂)*(t₁^2+t₁*t₂+t₂^2) := by ring,
 rw [h], have ht : 0<t₁ := lt_trans h₁ h₂,
 have hs : 0<t₁-t₂ := sub_pos.mpr h₂, positivity
end

def shell (F : ℝ → ℝ) (t x L : ℝ) : ℝ := (F (t-abs(x-L))-F(t-x-L))/2
def inner (F : ℝ → ℝ) (L x : ℝ) := F x + F (x-2*L)
def outer (F : ℝ → ℝ) (L x : ℝ) := -F (x-L)

theorem causal_interior (F : ℝ → ℝ) (t x L : ℝ) (h : x ≤ L) (hL : 0≤L) :
 shell (inner F L) t x L+shell (outer F L) t x (2*L)=shell F t x L :=
begin
 simp only [shell,inner,outer, abs_of_nonpos (show x-L≤0,by linarith),
   abs_of_nonpos (show x-2*L≤0,by linarith)],
 have h₁ : t- -(x-L)-2*L=t- -(x-2*L)-L := by ring,
 have h₂ : t-x-L-2*L=t-x-2*L-L := by ring,
 rw [h₁,h₂],ring
end

theorem causal_exterior (F : ℝ → ℝ) (t x L : ℝ) (h : 2*L≤x) (hL : 0≤L) :
 shell (inner F L) t x L+shell (outer F L) t x (2*L)=0 :=
begin
 simp only [shell,inner,outer,abs_of_nonneg (show 0≤x-L,by linarith),
   abs_of_nonneg (show 0≤x-2*L,by linarith)],
 have h₁ : t-(x-L)-2*L=t-x-L := by ring,
 have h₂ : t-(x-2*L)-L=t-(x-L) := by ring,
 have h₃ : t-x-L-2*L=t-x-2*L-L := by ring,
 rw [h₁,h₂,h₃],ring
end

theorem equal_receipts_cancel (k : ℝ) : k-k=0 := sub_self k

theorem finite_coherent_error (N : ℝ) :
 0<real.exp (-N)/(2*(1+real.sqrt (1-real.exp (-N)))) :=
by {apply div_pos (real.exp_pos _), have h := real.sqrt_nonneg (1-real.exp (-N)), linarith}

-- Energy current and independent normal pressure of two streams.
theorem balanced_stream_obstruction (g q P J : ℝ) (hj : J=0) (hp : 0<P) :
 q*g*J≠P := by {rw [hj,mul_zero],exact ne_of_lt hp}

theorem clock_energy (q c I O : ℝ) :
 (q-c*O)*I-(q-c*I)*O=q*(I-O) := by ring

theorem stress_and_flux (u v q s : ℝ) :
 q*((s*q)*u+q*v)=q^2*(s*u+v) ∧ -q*u+q*v= -q*(u-v) :=
by {split;ring}

theorem base_pressure (R m z : ℝ) (hz : z≠0) (hR : R≠0)
 (hF : z^2=1-2*m/R) :
 z + m/(R*z)=(z+1/z)/2 :=
begin
 have h : z^2*R=R-2*m := by {rw [hF],field_simp [hR]},
 field_simp [hz,hR], linear_combination z*h
end

theorem recoil_connection (R s I O : ℝ) (hR : R≠0) (hminus : 1-s≠0) (hplus : 1+s≠0) :
 -(s*I+O)/(R*((1-s)*(1+s)))-(I-O)/(R*((1-s)*(1+s)))=
 -I/(R*(1-s)) := by {field_simp [hR,hminus,hplus],ring}

theorem curvature_chain (R s ds : ℝ) (hR : R≠0) (hs : s≠0) (hm : 1-s≠0)
 (speed : ds=1/(R*s)) :
 ds/(R*(1-s)^2)=1/(R^2*s*(1-s)^2) :=
by {rw [speed],field_simp [hR,hs,hm],ring}

theorem positive_curvature (R s : ℝ) (hR : 0<R) (hs : 0<s) (hm : s<1) :
 0<1/(R^2*s*(1-s)^2) :=
by {have hh : 0<1-s := by linarith, positivity}

theorem pure_release_telescopes (initial middle final : ℝ) :
 (middle-initial)+(final-middle)=final-initial := by ring

theorem residual_distinguishability (v : ℝ) (hv : v<1) : (1+v)/2<1 := by linarith

theorem packet_energy (m e R zi zf : ℝ) (hR : R≠0) (hz : zi+zf≠0)
 (h : zf^2-zi^2=2*e/R) : R*(zf-zi)=2*e/(zi+zf) :=
begin
 apply (eq_div_iff hz).mpr,
 have ht := (eq_div_iff hR).mp h,
 nlinarith [show R*(zf-zi)*(zi+zf)=(zf^2-zi^2)*R,by ring]
end

-- Continuous wave port. Scattering completeness is imported in the paper from
-- Weder's published half-line theorem. These lemmas cover the application algebra.
theorem port_power (u p v q : ℝ) (ht : u=v) (hn : p=q) : u*p-v*q=0 :=
by {rw [ht,hn],ring}

theorem positive_port_energy (kinetic gradient potential : ℝ)
 (hk : 0≤kinetic) (hg : 0≤gradient) (hv : 0≤potential) :
 0≤(kinetic+gradient+potential)/2 := by linarith

theorem no_negative_eigenvalue (norm E V : ℝ) (hn : 0<norm) (he : E<0)
 (hv : 0≤V) : E*norm≠V := ne_of_lt (lt_of_lt_of_le (mul_neg_of_neg_of_pos he hn) hv)

theorem regular_wronskian (u v a b c d : ℝ)
 (nonzero : a*d-b*c ≠0) (realpart : a*u-b*v=0) (imagpart : c*u-d*v=0) :
 u=0 ∧ v=0 :=
begin
 have h₁ : u*(a*d-b*c)=0 := by {linear_combination d*realpart-b*imagpart},
 have h₂ : v*(a*d-b*c)=0 := by {linear_combination c*realpart-a*imagpart},
 exact ⟨(mul_eq_zero.mp h₁).resolve_right nonzero,
        (mul_eq_zero.mp h₂).resolve_right nonzero⟩
end

theorem final_cone_readout (F : ℝ → ℝ) (U v : ℝ) :
 (F v-F U)-(F v-F v)=F v-F U := by ring

theorem late_flux (H : ℝ → ℝ) (u : ℝ) : (-H u)^2=(H u)^2 := by ring

theorem endpoint_reflection (inc outg : ℝ → ℝ) (cap : ∀ t,inc t+outg t=0) :
 ∀ t,outg t= -inc t := by {intro t,have h := cap t,linarith}

theorem one_sided_acceptance (r c : ℝ) (hr : r≤1) (hc : c≤1) :
 (1-r)*c≤1-r := by nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hc)]

theorem no_later_cancellation (f : ℕ → ℝ) (h₀ : f 0=0)
 (period : ∀ n, f (n+1)=f n) : ∀ n, f n=0 :=
by {intro n,induction n with n ih,exact h₀,exact (period n).trans ih}

theorem perturbation_smaller_than_gap (g e : ℝ) (h : abs e < g) : 0<g+e :=
by {have h₁ := neg_abs_le_self e,linarith}

theorem reflected_depth_change (u₀ u₁ v₀ v₁ : ℝ) :
 (u₁-v₁)/2-(u₀-v₀)/2=((u₁-u₀)-(v₁-v₀))/2 := by ring

theorem finite_optical_duration (T advanced k D : ℝ)
 (hk : 0<k) (advance : advanced≤1/k) (capacity : (T-advanced)/2≤D) :
 T≤2*D+1/k := by linarith

theorem loaded_force (mu db a Z k b : ℝ)
 (force : k*b+Z*db=0) (original : db=a) : k*b+Z*a=0 := by rwa [←original]

theorem moving_mass_constraint (R m z E speed : ℝ) (hR : R≠0) (hz : z^2=1-2*m/R) :
 R*(1+speed^2-(z-E/R)^2)/2=m+z*E-E^2/(2*R)+R*speed^2/2 :=
begin
 have h : z^2*R=R-2*m := by {rw [hz],field_simp [hR]},
 have hm : m = (R-z^2*R)/2 := by linarith,
 rw [hm], field_simp [hR],ring
end

theorem radial_restoring_force (R z mu k Z b w v acc : ℝ)
 (mode : v+z*b=0) (loaded : mu*acc=R*v-k*b-Z*w) :
 mu*acc+Z*w+(k+R*z)*b=0 := by linear_combination loaded+R*mode

theorem loaded_mass_balance (R z mu k Z b w v acc radial : ℝ)
 (wall : mu*acc=R*v-k*b-Z*w) (normal : radial= -z*w) :
 z*(mu*w*acc+k*b*w)+R*v*radial= -z*Z*w^2 :=
by {rw [normal],linear_combination z*w*wall}

theorem current_driven_offset (z load w radial : ℝ) (h : radial= -z*(w-load)) :
 radial+z*w=z*load := by {rw [h],ring}

theorem elastic_energy_balance (M mu R K k Z r b v w a h : ℝ)
 (radial : M*a= -K*r-R*w) (spring : mu*h=R*v-k*b-Z*w) :
 M*v*a+K*r*v+mu*w*h+k*b*w= -Z*w^2 :=
by linear_combination v*radial+w*spring

theorem elastic_dark_mode (K k R r b v : ℝ) (hK : K≠0) (hk : k≠0)
 (radial : K*r=0) (fixed_radius : r=0 → v=0) (force : k*b=R*v) :
 r=0 ∧ v=0 ∧ b=0 :=
begin
 have hr := (mul_eq_zero.mp radial).resolve_left hK,
 have hv := fixed_radius hr,
 rw [hv,mul_zero] at force,
 exact ⟨hr,hv,(mul_eq_zero.mp force).resolve_left hk⟩
end

theorem elastic_equilibrium (A B R : ℝ) (hR : R≠0) (gas : B=2*A*R^3) :
 2*A*R-B/R^2=0 ∧ 2*A+2*B/R^3=6*A :=
by {rw [gas],split;field_simp [hR];ring}

theorem elastic_determinants (M mu R K k Z : ℝ) :
 (M*Z)*(M*k+K*mu+R^2)-(M*mu)*(K*Z)=M*Z*(M*k+R^2) ∧
 (M*Z)*(M*k+K*mu+R^2)*(K*Z)-(M*mu)*(K*Z)^2-(M*Z)^2*(K*k)
 =M*K*Z^2*R^2 := by {split;ring}

theorem elastic_passivity (M R K k Z : ℝ) (hM : 0<M) (hR : 0<R)
 (hK : 0<K) (hk : 0<k) (hZ : 0<Z) :
 0<M*Z*(M*k+R^2) ∧ 0<M*K*Z^2*R^2 := by {split;positivity}

private theorem both_squares_zero (x y : ℝ) (h : x^2+y^2≤0) : x=0 ∧ y=0 :=
begin
 split,
 { by_contra hn, have hp := sq_pos_of_ne_zero x hn,
   linarith only [h,hp,sq_nonneg y] },
 { by_contra hn, have hp := sq_pos_of_ne_zero y hn,
   linarith only [h,hp,sq_nonneg x] }
end

private theorem right_zero (A B : ℝ) (h : A+B=0) (hA : 0≤A) (hB : 0≤B) :
 B=0 := by linarith only [h,hA,hB]

-- Real and imaginary components of an arbitrary normal mode.
theorem elastic_mode_power (M mu K k Z g x y a b c d : ℝ)
 (r1 : M*((x^2-y^2)*a-2*x*y*b)+K*a+g*(x*c-y*d)=0)
 (r2 : M*((x^2-y^2)*b+2*x*y*a)+K*b+g*(x*d+y*c)=0)
 (s1 : mu*((x^2-y^2)*c-2*x*y*d)+k*c+Z*(x*c-y*d)-g*(x*a-y*b)=0)
 (s2 : mu*((x^2-y^2)*d+2*x*y*c)+k*d+Z*(x*d+y*c)-g*(x*b+y*a)=0) :
 x*((M*(x^2+y^2)+K)*(a^2+b^2)+(mu*(x^2+y^2)+k)*(c^2+d^2))+
 Z*(x^2+y^2)*(c^2+d^2)=0 :=
by linear_combination (x*a-y*b)*r1+(x*b+y*a)*r2+(x*c-y*d)*s1+(x*d+y*c)*s2

theorem elastic_eigenvalue_decays (M mu K k Z g x y a b c d : ℝ)
 (hM : 0<M) (hu : 0<mu) (hK : 0<K) (hk : 0<k) (hZ : 0<Z) (hg : 0<g)
 (mode : a≠0 ∨ b≠0 ∨ c≠0 ∨ d≠0)
 (r1 : M*((x^2-y^2)*a-2*x*y*b)+K*a+g*(x*c-y*d)=0)
 (r2 : M*((x^2-y^2)*b+2*x*y*a)+K*b+g*(x*d+y*c)=0)
 (s1 : mu*((x^2-y^2)*c-2*x*y*d)+k*c+Z*(x*c-y*d)-g*(x*a-y*b)=0)
 (s2 : mu*((x^2-y^2)*d+2*x*y*c)+k*d+Z*(x*d+y*c)-g*(x*b+y*a)=0) : x<0 :=
begin
 by_contra bad, push_neg at bad,
 have power := elastic_mode_power M mu K k Z g x y a b c d r1 r2 s1 s2,
 have ex : 0≤x*((M*(x^2+y^2)+K)*(a^2+b^2)+(mu*(x^2+y^2)+k)*(c^2+d^2)) := by positivity,
 have hzero : Z*(x^2+y^2)*(c^2+d^2)=0 :=
   right_zero _ _ power ex (by positivity),
 rcases mul_eq_zero.mp hzero with rate|amp,
 { have e := (mul_eq_zero.mp rate).resolve_left (ne_of_gt hZ),
   obtain ⟨hx,hy⟩ := both_squares_zero _ _ (le_of_eq e),
   have aa : K*a=0 := by simpa [hx,hy] using r1,
   have ab : K*b=0 := by simpa [hx,hy] using r2,
   have ac : k*c=0 := by simpa [hx,hy] using s1,
   have ad : k*d=0 := by simpa [hx,hy] using s2,
   rcases mode with m|m|m|m,
   { exact m ((mul_eq_zero.mp aa).resolve_left (ne_of_gt hK)) },
   { exact m ((mul_eq_zero.mp ab).resolve_left (ne_of_gt hK)) },
   { exact m ((mul_eq_zero.mp ac).resolve_left (ne_of_gt hk)) },
   { exact m ((mul_eq_zero.mp ad).resolve_left (ne_of_gt hk)) } },
 { obtain ⟨hc,hd⟩ := both_squares_zero _ _ (le_of_eq amp),
   have h₁ : g*(x*a-y*b)=0 := by simpa [hc,hd] using s1,
   have h₂ : g*(x*b+y*a)=0 := by simpa [hc,hd] using s2,
   rw [hc,hd] at r1 r2,
   have va := (mul_eq_zero.mp h₁).resolve_left (ne_of_gt hg),
   have vb := (mul_eq_zero.mp h₂).resolve_left (ne_of_gt hg),
   have ac : K*a=0 := by linear_combination r1-M*x*va+M*y*vb,
   have bc : K*b=0 := by linear_combination r2-M*x*vb-M*y*va,
   have ha := (mul_eq_zero.mp ac).resolve_left (ne_of_gt hK),
   have hb := (mul_eq_zero.mp bc).resolve_left (ne_of_gt hK),
   rcases mode with m|m|m|m,
   {exact m ha},{exact m hb},{exact m hc},{exact m hd} }
end

theorem elastic_symplectic_output (M mu K k Z g r s b c v u w p a e h f : ℝ)
 (ra : M*a= -K*r-g*w) (rb : M*e= -K*s-g*p)
 (sa : mu*h=g*v-k*b-Z*w) (sb : mu*f=g*u-k*c-Z*p) :
 M*(r*e-a*s)+g*(v*c+r*p-w*s-b*u)+mu*(b*f-h*c) = -Z*(b*p-w*c) :=
by linear_combination r*rb-s*ra+b*sb-c*sa

-- On the span of the two pure inputs a positive effect with a zero
-- diagonal entry has a zero row. u,v are the off-diagonal real components.
theorem exact_branch_effect (u v p r tail cross₁ cross₂ : ℝ)
 (positive_det : u^2+v^2≤0) (contraction : p≤1) (weight : 0≤tail)
 (normalized : r+tail=1) :
 u=0 ∧ v=0 ∧ p*tail+cross₁*u+cross₂*v≤1-r :=
begin
 obtain ⟨hu,hv⟩ := both_squares_zero _ _ positive_det,
 rw [hu,hv], refine ⟨rfl,rfl,_⟩,
 nlinarith [mul_nonneg (sub_nonneg.mpr contraction) weight]
end

theorem finite_source_precludes_both (N p : ℝ) (certainty : p=1)
 (projection : p≤1-real.exp (-N)) : false :=
by {have h := real.exp_pos (-N), linarith}

theorem exterior_shell_response (L a D x : ℝ) (ha : a≠0) (hx : x≠0)
 (hp : D+L≠0) (hm : D-L≠0) :
 (6*L/(D-L)-6*L/(D+L))/(2*a*x)=6*L^2/(a*x*((D-L)*(D+L))) :=
by {field_simp [ha,hx,hp,hm],ring}

theorem exterior_gradient_sign (value a x D block : ℝ) (hv : 0<value)
 (ha : 0<a) (hx : 0<x) (hD : 0<D) (hb : 0<block) :
 -(value/a)*(1/x+2*D/block)<0 :=
mul_neg_of_neg_of_pos (neg_lt_zero.mpr (div_pos hv ha)) (by positivity)

end mixed_flux_memory
