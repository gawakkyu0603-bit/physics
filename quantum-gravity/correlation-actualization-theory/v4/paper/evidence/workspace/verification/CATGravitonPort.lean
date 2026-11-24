import tactic
import analysis.special_functions.trigonometric.deriv
import topology.instances.real

noncomputable theory
open_locale big_operators
open finset filter

namespace cat_graviton_port

-- Each rotating pair is accelerated parallel to itself, also off the round orbit.
theorem angular_current (x y vx vy s : ℝ) :
 vx*vy+x*(-s*y)-(vy*vx+y*(-s*x))=0 := by ring

theorem conserved_current_jet (x y vx vy : ℝ → ℝ) (t s : ℝ)
 (dx : has_deriv_at x (vx t) t) (dy : has_deriv_at y (vy t) t)
 (dvx : has_deriv_at vx (-s*x t) t) (dvy : has_deriv_at vy (-s*y t) t) :
 has_deriv_at (λ t, x t*vy t-y t*vx t) 0 t :=
begin
 convert (dx.mul dvy).sub (dy.mul dvx) using 1, ring
end

theorem angular_momentum_conserved (x y vx vy s : ℝ → ℝ)
 (dx : ∀t, has_deriv_at x (vx t) t) (dy : ∀t, has_deriv_at y (vy t) t)
 (dvx : ∀t, has_deriv_at vx (-s t*x t) t) (dvy : ∀t, has_deriv_at vy (-s t*y t) t)
 (a b : ℝ) : x a*vy a-y a*vx a=x b*vy b-y b*vx b :=
begin
 have h:=λ t, conserved_current_jet x y vx vy t (s t) (dx t) (dy t) (dvx t) (dvy t),
 exact is_const_of_deriv_eq_zero (λ t,(h t).differentiable_at) (λ t,(h t).deriv) a b
end

theorem energy_jet (a b c av bv cv : ℝ) :
 -(b+c)*av-(a+c)*bv-(a+b)*cv+
   (av*b+a*bv+av*c+a*cv+bv*c+b*cv)=0 := by ring

theorem planar_area (x y v w : ℝ) :
 (x^2+y^2)*(v^2+w^2)-(x*w-y*v)^2=(x*v+y*w)^2 := by ring

theorem axes_compact (a b ell speed : ℝ) (ha : 0≤a)
 (hs : 0<speed) (hl : 0<ell) (hb : ell≤b*speed)
 (h : a*b≤speed) (hal : ell≤a*speed) :
 ell/speed≤a ∧ a≤speed^2/ell :=
begin
 refine ⟨(div_le_iff hs).2 hal,(le_div_iff hl).2 _⟩,
 have u:=mul_le_mul_of_nonneg_left hb ha,
 have v:=mul_le_mul_of_nonneg_right h hs.le,
 nlinarith only [u,v]
end

theorem transverse_clock (a b c x y z floor : ℝ)
 (hx : floor^2≤x^2) (hy : floor^2≤y^2) (hz : floor^2≤z^2)
 (unit : a^2+b^2+c^2=1) :
 floor^2≤(a*x)^2+(b*y)^2+(c*z)^2 :=
begin
 have h₁:=mul_le_mul_of_nonneg_left hx (sq_nonneg a),
 have h₂:=mul_le_mul_of_nonneg_left hy (sq_nonneg b),
 have h₃:=mul_le_mul_of_nonneg_left hz (sq_nonneg c),
 have h₄:=congr_arg (λ u : ℝ, u*floor^2) unit,
 dsimp at h₄, nlinarith only [h₁,h₂,h₃,h₄]
end

theorem regular_embedding_tangent {ι : Type*} (n x y v w z : ι → ℝ) (t : ℝ)
 (some_axis : ∃i, n i≠0) (angular : ∀i, x i*w i-y i*v i≠0)
 (dx : ∀i, t*n i*v i+z i*x i=0) (dy : ∀i, t*n i*w i+z i*y i=0) :
 t=0 ∧ ∀i, z i=0 :=
begin
 obtain ⟨i,hi⟩:=some_axis,
 have h : (t*n i)*(x i*w i-y i*v i)=0 :=
   by {linear_combination x i*dy i-y i*dx i},
 have ht : t=0 := (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (angular i))).resolve_right hi,
 refine ⟨ht,λ j,_⟩,
 have hz : z j*(x j*w j-y j*v j)=0 :=
   by {linear_combination w j*dx j-v j*dy j},
 exact (mul_eq_zero.mp hz).resolve_right (angular j)
end

theorem beam_and_volume_jets (s h q1 q2 d : ℝ) (h0 : h≠0) (hd : d≠0) :
 (s^2-s*h^2)/(h^2*d)=(s^2/h^2-s)/d ∧
 ((s^2/h^2-s)+q1+q2)/(2*d) =
 ((s^2/h^2-s)/d+q1/d+q2/d)/2 :=
by {split; field_simp [h0,hd]; ring}

-- Initial eikonal and expansion jets, including the full angular divergence.
theorem clock_jerk (h s0 s1 a : ℝ) (rest : s0=0) (eikonal : s0^2+(-h)*s1=a)
 (hp : h≠0) : s1= -a/h :=
begin
 apply (eq_div_iff hp).2, rw [rest] at eikonal, nlinarith only [eikonal]
end

theorem area_preserving_angular_drift (xy yx : ℝ) (smooth : xy=yx) : xy-yx=0 :=
sub_eq_zero.mpr smooth

theorem ray_curvature_jet (d h a sttt theta_t r : ℝ) (hd : d≠0) (hh : h≠0)
 (phase : sttt= -a/h) (divergence : theta_t= -sttt/d)
 (optical : r= -(h/d)*theta_t*(d/h^2)) : r= -a/(h^2*d) :=
by {rw [optical,divergence,phase],field_simp [hd,hh],ring}

theorem plane_speed_acceleration (s a h : ℝ) :
 (-s*a)^2+h*(-s*h)=s*(s*a^2-h^2) := by ring

theorem all_beams (a b c : ℝ) :
 (∀x y z:ℝ, x^2+y^2+z^2=1 → 0<x^2*a+y^2*b+z^2*c) ↔ 0<a ∧ 0<b ∧ 0<c :=
begin
 split,
 {intro h, refine ⟨_,_,_⟩,
  {simpa using h 1 0 0 (by norm_num)},
  {simpa using h 0 1 0 (by norm_num)},
  {simpa using h 0 0 1 (by norm_num)}},
 {rintro ⟨ha,hb,hc⟩ x y z unit,
  have x0:=mul_nonneg (sq_nonneg x) ha.le,
  have y0:=mul_nonneg (sq_nonneg y) hb.le,
  have z0:=mul_nonneg (sq_nonneg z) hc.le,
  by_cases hx : x=0,
  {by_cases hy : y=0,
   {have hz : z≠0 := by {intro hz,subst_vars,norm_num at unit},
    linarith [mul_pos (sq_pos_of_ne_zero z hz) hc]},
   {linarith [mul_pos (sq_pos_of_ne_zero y hy) hb]}},
  {linarith [mul_pos (sq_pos_of_ne_zero x hx) ha]} }
end

theorem short_axis_threshold (e : ℝ) :
 (1-e)^2*((1+e)^2+1)=(1-e^2)^2+(1-e)^2 := by ring

theorem threshold_decreases (x y : ℝ) (hx : 0≤x) (hxy : x<y) (hy : y<1) :
 (1-y^2)^2+(1-y)^2 < (1-x^2)^2+(1-x)^2 :=
begin
 have xy : x^2<y^2 := by nlinarith [mul_pos (sub_pos.mpr hxy) (show 0<y+x,by linarith)],
 have yy : y^2<1 := by nlinarith [mul_pos (sub_pos.mpr hy) (show 0<1+y,by linarith)],
 have t:=mul_pos (sub_pos.mpr xy) (show 0<2-x^2-y^2,by linarith),
 have s:=mul_pos (sub_pos.mpr hxy) (show 0<2-x-y,by linarith),
 nlinarith only [t,s]
end

theorem threshold_bracket :
 (1-(75216/100000:ℝ))^2*((1+75216/100000)^2+1)>1/4 ∧
 (1-(75217/100000:ℝ))^2*((1+75217/100000)^2+1)<1/4 := by norm_num

theorem axial_extent (f v : ℝ→ℝ) (c : ℝ) (df : ∀t, has_deriv_at f (v t) t)
 (bound : ∀t, c≤v t) (a b : ℝ) (ab : a≤b) : c*(b-a)≤f b-f a :=
begin
 have d : ∀t, has_deriv_at (λ t, f t-c*t) (v t-c) t := λ t,
   by convert (df t).sub ((has_deriv_at_id t).const_mul c) using 1; simp,
 have m : monotone (λ t, f t-c*t) :=
   monotone_of_deriv_nonneg (λ t, (d t).differentiable_at)
      (λ t, by {rw [(d t).deriv],exact sub_nonneg.mpr (bound t)}),
 have h:=m ab, dsimp at h, linarith
end

theorem axial_affine_lower (lapse velocity lo hi : ℝ) (v : 0<velocity)
 (h : velocity≤hi) (n : lo≤lapse) (p : 0≤lo) :
 lo/hi≤lapse/velocity :=
begin
 apply div_le_div (le_trans p n) n v h
end

-- Gravitational and ordinary vertices at unequal oscillator times.
theorem trace_cancel (vac marked : ℂ) : (vac+marked)-vac=marked := by ring

theorem two_orders (v before after total elapsed : ℂ) (h : after=total-elapsed) :
 v*before+star_ring_end ℂ v*after =
 v*before+star_ring_end ℂ v*total-star_ring_end ℂ v*elapsed :=
by {rw [h],ring}

theorem three_links (a b c : ℝ) :
 c*(2*a+b)+c*(a+2*b)=3*c*(a+b) := by ring

theorem parity_selection {E : Type*} [has_neg E] (b : E → E → ℂ) (rot : E → E) (x y : E)
 (unitary : ∀ x y, b (rot x) (rot y)=b x y)
 (even : rot x=x) (odd : rot y= -y)
 (phase : b x (-y) = -(b x y)) : b x y=0 :=
begin
 have v:=unitary x y, rw [even,odd,phase] at v,
 linear_combination (-1/2:ℂ)*v
end

theorem stationary_orders (m gap : ℝ) (hm : gap-m≠0) (hp : gap+m≠0) :
 1/(gap-m)-1/(gap+m)=2*m/((gap-m)*(gap+m)) :=
by {field_simp [hm,hp],ring}

theorem source_receiver_recoil (line mr ms delta gap : ℝ) (r : mr≠0) (s : ms≠0)
 (receive : delta=line-line^2/(2*mr)) (emit : gap=line+line^2/(2*ms)) :
 gap=delta+line^2/(2*mr)+line^2/(2*ms) := by {rw [receive,emit], ring}

theorem radial_rescale (mu u : ℝ) (hp : mu=u^3) (hu : u≠0) :
 u^2/mu=1/u ∧ mu/u^4=1/u :=
by {rw [hp],split;field_simp [hu];ring}

-- The row of the inverse of the unperturbed two-state north block.
theorem north_resolvent (j b : ℝ) (hj : 0<j) (hb : b^2=2*(2*j-1)) :
 (-2:ℝ)-b^2 = -4*j ∧
 (2*j)*((-2)/((-2)-b^2))=1 :=
begin
 have e : (-2:ℝ)-b^2 = -4*j := by linarith,
 refine ⟨e,_⟩, rw [e], field_simp [ne_of_gt hj], ring
end

theorem compare_positive_square (a d diff r : ℝ) (ha : 0<a)
 (pr : 0≤r) (eq : r^2=d^2+(diff/2)^2) : a/2<r ↔ a^2<4*d^2+diff^2 :=
begin
 have id : 4*d^2+diff^2-a^2=4*((r-a/2)*(r+a/2)) :=
   by {linear_combination (-4)*eq},
 have pos : 0<r+a/2 := by linarith,
 calc (a/2<r) ↔ 0<r-a/2 : sub_pos.symm
 ... ↔ 0<4*((r-a/2)*(r+a/2)) :
   begin
    split,
    { intro h, exact mul_pos (by norm_num) (mul_pos h pos) },
    { intro h, by_contra bad, push_neg at bad,
      exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0:ℝ)≤4)
                  (mul_nonpos_of_nonpos_of_nonneg bad pos.le))) h }
   end
 ... ↔ 0<4*d^2+diff^2-a^2 : by rw [id]
 ... ↔ a^2<4*d^2+diff^2 : sub_pos
end

theorem half_spin_sign (a d diff : ℝ) (ha : 0<a) :
 a/2 < real.sqrt (d^2+(diff/2)^2) ↔ a^2 < 4*d^2+diff^2 :=
compare_positive_square a d diff _ ha (real.sqrt_nonneg _) (real.sq_sqrt (by positivity))

theorem variance_of_excitation (rho base : ℝ) :
 (1-rho)*base+rho*(3*base)=base*(1+2*rho) := by ring

theorem gaussian_boundary (phi : ℝ → ℝ) (x : ℝ) (h : has_deriv_at phi (-x*phi x) x) :
 has_deriv_at (λ z, -z*phi z) ((x^2-1)*phi x) x :=
begin
 convert ((has_deriv_at_id x).neg.mul h) using 1, simp;ring
end

theorem optimum_tail (phi : ℝ → ℝ) (x : ℝ) (h : has_deriv_at phi (-x*phi x) x) :
 has_deriv_at (λ z, z*phi z) ((1-x^2)*phi x) x :=
begin
 convert ((has_deriv_at_id x).mul h) using 1, simp;ring
end

theorem blur_bound (rho s integral cap : ℝ) (rs : 0≤rho) (ss : 0<s)
 (bound : integral≤cap) : 2*rho/s*integral≤2*rho/s*cap :=
mul_le_mul_of_nonneg_left bound (by positivity)

theorem free_point_width (s a : ℝ) (hs : 0<s) :
 2*a ≤ s^2+a^2/s^2 :=
begin
 have h:=sq_nonneg (s-a/s),
 have id : (s-a/s)^2=s^2+a^2/s^2-2*a := by {field_simp [ne_of_gt hs],ring},
 linarith
end

-- A common received sequence cannot have two distinct front points in a Hausdorff space.
theorem identified_front {X Y Z : Type*} [topological_space X] [topological_space Y]
 [topological_space Z] [t2_space Z] (i : X → Z) (j : Y → Z)
 (a : ℕ→X) (b : ℕ→Y) (p : X) (q : Y) (hi : continuous_at i p)
 (hj : continuous_at j q) (ha : tendsto a at_top (nhds p)) (hb : tendsto b at_top (nhds q))
 (same : ∀n, i (a n)=j (b n)) : i p=j q :=
begin
 have e : i ∘ a=j ∘ b := funext same,
 have v : tendsto (i∘a) at_top (nhds (i p)) := hi.tendsto.comp ha,
 rw [e] at v, exact tendsto_nhds_unique v (hj.tendsto.comp hb)
end

theorem single_absorption_budget (k d1 d2 recoil : ℝ) (low : k<d1+d2) (hr : 0≤recoil) :
 k≠d1+d2+recoil := by linarith

theorem shared_weights (w ratio : ℝ) (hw : 0<w) (hr : 0<ratio) :
 w/(w+w/ratio)=ratio/(1+ratio) :=
begin
 have h : 0<w+w/ratio := by positivity,
 have g : 0<1+ratio := by positivity,
 apply (div_eq_div_iff h.ne' g.ne').2, field_simp [hr.ne'], ring
end

theorem last_rank (n r : ℕ) (hr : 0<r) : n+r≠n := by omega

theorem shell_shift (p k h t u s m : ℝ) :
 2*(p+k)*(h+t)-(u+s)^2-(2*p*h-u^2) =
 2*(p*t+h*k-u*s)+(2*k*t-s^2) := by ring

theorem energy_for_circle (e m p : ℝ) (hm : 0≤m) (he : 0≤e)
 (shell : e^2=m^2+p^2) (hp : p≠0) : m<e :=
begin
 by_contra bad, push_neg at bad,
 nlinarith [mul_nonneg (sub_nonneg.mpr bad) (show 0≤m+e, by linarith),sq_pos_of_ne_zero p hp]
end

-- Sharp finite-band first Fourier moment: positive path eigenvector and its quadratic bound.
theorem adjacent_young (a b w v : ℝ) (hw : 0<w) (hv : 0<v) :
 2*a*b ≤ v/w*a^2+w/v*b^2 :=
begin
 apply (le_of_mul_le_mul_right _ (mul_pos hw hv) : _),
 have id : (v/w*a^2+w/v*b^2-2*a*b)*(w*v)=(v*a-w*b)^2 :=
   by {field_simp [ne_of_gt hw,ne_of_gt hv],ring},
 nlinarith only [id,sq_nonneg (v*a-w*b)]
end

theorem sine_path (x theta : ℝ) :
 real.sin (x-theta)+real.sin (x+theta)=2*real.cos theta*real.sin x :=
by {rw [real.sin_sub,real.sin_add],ring}

theorem path_sum (a f : ℕ → ℝ) (c : ℝ) (n : ℕ)
 (edge : ∀i<n, 2*a i*a (i+1)≤2*c*(a i)^2+f (i+1)-f i) :
 (∑ i in range n, 2*a i*a (i+1)) ≤ 2*c*(∑ i in range n, (a i)^2)+f n-f 0 :=
begin
 induction n with k ih,
 {simp},
 { have p:=ih (λ i hi, edge i (nat.lt_succ_of_lt hi)),
   have q:=edge k (nat.lt_succ_self k),
   rw [sum_range_succ,sum_range_succ], linarith }
end

theorem sine_saturates (l a r c : ℝ) (eig : l+r=2*c*a) :
 a*l+a*r=2*c*a^2 := by {linear_combination a*eig}

-- A positive sine trial vector bounds the Rayleigh quotient of any real
-- amplitudes, with Dirichlet endpoints.  Complex phases can only lower it.
theorem path_visibility (n : ℕ) (a w : ℕ→ℝ) (c : ℝ)
 (az : a 0=0) (an : a (n+1)=0) (wz : w 0=0) (wn : w (n+1)=0)
 (pos : ∀i, 0<i → i≤n → 0<w i)
 (rec : ∀i, 0<i → i≤n → w (i-1)+w (i+1)=2*c*w i) :
 (∑ i in range (n+1), 2*a i*a (i+1)) ≤ 2*c*(∑ i in range (n+1), (a i)^2) :=
begin
 let flux : ℕ→ℝ := λ i, w (i-1)/w i*(a i)^2,
 have fz : flux 0=0 := by simp [flux,az],
 have fn : flux (n+1)=0 := by simp [flux,an],
 have step : ∀i<n+1, 2*a i*a (i+1)≤2*c*(a i)^2+flux (i+1)-flux i,
 { intros i hi,
   by_cases z : i=0,
   { subst i, simp [flux,az,wz] },
   have il : i≤n := nat.lt_succ_iff.mp hi,
   have ip : 0<i := nat.pos_of_ne_zero z,
   have wi:=pos i ip il,
   have row : w (i+1)/w i*(a i)^2+flux i=2*c*(a i)^2,
   { dsimp [flux], have e:=rec i ip il,
     field_simp [wi.ne'], linear_combination (a i)^2*e },
   by_cases last : i=n,
   { subst i, rw [wn,zero_div,zero_mul,zero_add] at row,
     rw [an,fn,mul_zero,add_zero], linarith },
   { have wj:=pos (i+1) (nat.succ_pos i) (by omega),
     have v:=adjacent_young (a i) (a (i+1)) (w i) (w (i+1)) wi wj,
     have shift : flux (i+1)=w i/w (i+1)*(a (i+1))^2 := by simp [flux],
     rw [shift], linarith } },
 simpa [fz,fn] using path_sum a flux c (n+1) step
end

theorem finite_sine_data (n : ℕ) :
 let θ := real.pi/((n:ℝ)+1), w := λ i:ℕ, real.sin ((i:ℝ)*θ) in
 w 0=0 ∧ w (n+1)=0 ∧ (∀i,0<i → i≤n → 0<w i) ∧
 ∀i, 0<i → i≤n → w (i-1)+w (i+1)=2*real.cos θ*w i :=
begin
 dsimp only,
 let θ := real.pi/((n:ℝ)+1),
 have hn : (0:ℝ)<(n:ℝ)+1 := by positivity,
 have th : 0<θ := div_pos real.pi_pos hn,
 have end_value : ((n:ℝ)+1)*θ=real.pi := by {dsimp [θ], field_simp [hn.ne'],ring},
 refine ⟨by simp,_,_,_⟩,
 { rw [nat.cast_add,nat.cast_one,end_value,real.sin_pi] },
 { intros i hi hil, apply real.sin_pos_of_pos_of_lt_pi,
   {exact mul_pos (by exact_mod_cast hi) th},
   { change (i:ℝ)*θ<real.pi, rw [←end_value],
     apply mul_lt_mul_of_pos_right _ th, exact_mod_cast nat.lt_succ_of_le hil } },
 { intros i hi hil, rw [nat.cast_sub (by omega : 1≤i), nat.cast_add,nat.cast_one],
   change real.sin (((i:ℝ)-1)*θ)+real.sin (((i:ℝ)+1)*θ)=_,
   rw [sub_mul,add_mul,one_mul], exact sine_path _ _ }
end

theorem finite_band_visibility (n : ℕ) (v : ℕ→ℂ) (z : v 0=0) (e : v (n+1)=0)
 (unit : (∑ i in range (n+1), (complex.abs (v i))^2)=1) :
 complex.abs (∑ i in range (n+1), (star_ring_end ℂ (v i))*v (i+1)) ≤
 real.cos (real.pi/((n:ℝ)+1)) :=
begin
 obtain ⟨wz,wn,wp,rec⟩:=finite_sine_data n,
 have q:=path_visibility n (λ i,complex.abs (v i)) _ _
   (by simp [z]) (by simp [e]) wz wn wp rec,
 dsimp only at q, rw [unit,mul_one] at q,
 have twice : (∑ i in range (n+1), 2*complex.abs (v i)*complex.abs (v (i+1))) =
   2*(∑ i in range (n+1), complex.abs (v i)*complex.abs (v (i+1))) :=
   by simp only [finset.mul_sum,mul_assoc],
 rw [twice] at q,
 have tri := norm_sum_le (range (n+1)) (λ i:ℕ, (star_ring_end ℂ (v i))*v (i+1)),
 change complex.abs _ ≤ ∑ i in range (n+1), complex.abs ((star_ring_end ℂ (v i))*v (i+1)) at tri,
 simp only [map_mul,complex.abs_conj] at tri,
 linarith
end

theorem path_rayleigh_equality (n : ℕ) (w : ℕ→ℝ) (c : ℝ)
 (z : w 0=0) (e : w (n+1)=0)
 (rec : ∀i, 0<i → i≤n → w (i-1)+w (i+1)=2*c*w i) :
 (∑ i in range (n+1), 2*w i*w (i+1))=2*c*(∑ i in range (n+1), (w i)^2) :=
begin
 let f := λ i:ℕ, w (i-1)*w i,
 have all : ∀k, k≤n+1 → (∑ i in range k, 2*w i*w (i+1)) =
   2*c*(∑ i in range k, (w i)^2)+f k,
 { intro k, induction k with k ih,
   {intro hk, simp [f,z]},
   {intro hk, rw [sum_range_succ,sum_range_succ,ih (by omega)],
    by_cases k0 : k=0,
    {subst k,simp [f,z]},
    have eig:=rec k (nat.pos_of_ne_zero k0) (by omega),
    have hks : k.succ-1=k := by omega,
    dsimp [f], simp only [hks,nat.succ_eq_add_one],
    linear_combination w k*eig } },
 have fe : f (n+1)=0 := by {change w (n+1-1)*w (n+1)=0,rw [e,mul_zero]},
 have total:=all (n+1) le_rfl, rw [fe,add_zero] at total, exact total
end

theorem energy_band_one (mu radius budget : ℝ) (hm : 0<mu) (hr : 0<radius)
 (small : budget<1/(2*mu*radius^2)) (q : ℤ)
 (allowed : (q:ℝ)^2/(2*mu*radius^2)≤budget) : q=0 :=
begin
 have hd : 0<2*mu*radius^2 := by positivity,
 have hq : (q:ℝ)^2<1 := (div_lt_div_right hd).mp (lt_of_le_of_lt allowed small),
 by_contra hn,
 have h : (1:ℤ)≤q^2 := by {have := sq_pos_of_ne_zero q hn,omega},
 exact (not_lt_of_ge (by exact_mod_cast h : (1:ℝ)≤(q:ℝ)^2)) hq
end

end cat_graviton_port
