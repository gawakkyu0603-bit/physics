import tactic
import analysis.special_functions.integrals
import analysis.calculus.mean_value
import linear_algebra.basic
import linear_algebra.matrix.trace
import linear_algebra.matrix.hermitian

noncomputable theory
open measure_theory set filter
open_locale big_operators real topology
namespace soft_charge_release

theorem particle_hole_term (ar ai br bi : ℝ) :
 (ar-br)^2+(ai-bi)^2≤2*(ar^2+ai^2)+2*(br^2+bi^2) :=
by nlinarith [sq_nonneg (ar+br),sq_nonneg (ai+bi)]

theorem soft_fraction {ι : Type*} [fintype ι] (energy : ι→ℝ) (mass : ℝ)
 (hm : 0<mass) (h : ∀ i,energy i≤4) : (∑ i,energy i)/mass≤4*(fintype.card ι:ℝ)/mass :=
begin
 apply div_le_div_of_le hm.le,
 have k : (∑ i,energy i)≤∑ i:ι,(4:ℝ) := finset.sum_le_sum (λ i hi,h i),
 simpa [mul_comm] using k
end

theorem squared_dissipation (a b c x y z : ℝ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
 (h : a*x^2+b*y^2+c*z^2=0) : x=0 ∧ y=0 ∧ z=0 :=
begin
 have h₁ := mul_nonneg ha.le (sq_nonneg x),
 have h₂ := mul_nonneg hb.le (sq_nonneg y),
 have h₃ := mul_nonneg hc.le (sq_nonneg z),
 have aux : ∀ u v:ℝ,0<u → u*v^2=0 → v=0 :=
 λ u v hu hv,pow_eq_zero ((mul_eq_zero.mp hv).resolve_left hu.ne'),
 exact ⟨aux a x ha (by linarith),aux b y hb (by linarith),aux c z hc (by linarith)⟩
end

theorem split_moments (i j : ℝ) :
 (i+j)^3-i^3-j^3=3*i*j*(i+j) ∧
 (i+j)^5-i^5-j^5=5*i*j*(i+j)*((i+j)^2-i*j) := ⟨by ring,by ring⟩

theorem same_moment_labels (S T P Q : ℝ) (hs : 0<S) (ht : 0<T) (hp : 0<P)
 (h₁ : S*P=T*Q) (h₂ : S*P*(S^2-P)=T*Q*(T^2-Q)) :
 S=T ∧ P=Q :=
begin
 rw [←h₁] at h₂,
 have h := mul_left_cancel₀ (mul_ne_zero hs.ne' hp.ne') h₂,
 have f : (S-T)*(T*(S+T)+P)=0 := by linear_combination T*h+h₁,
 have nz : 0<T*(S+T)+P := add_pos (mul_pos ht (add_pos hs ht)) hp,
 have hst := sub_eq_zero.mp ((mul_eq_zero.mp f).resolve_right nz.ne'),
 exact ⟨hst,by {rw [hst] at h₁, exact mul_left_cancel₀ ht.ne' h₁}⟩
end

theorem unordered_split (i j a b : ℝ) (s : i+j=a+b) (p : i*j=a*b) :
 (i=a ∧ j=b) ∨ (i=b ∧ j=a) :=
begin
 have h : (i-a)*(i-b)=0 := by linear_combination i*s-p,
 rcases mul_eq_zero.mp h with ha|hb,
 {left,split;linarith}, {right,split;linarith}
end

theorem cubic_moment_collision :
 (6:ℕ)^3-5^3-1^3=5^3-3^3-2^3 ∧ (6:ℕ)^5-5^5-1^5≠5^5-3^5-2^5 := by norm_num

section spectral_filters
variables {E : Type*} [add_comm_group E] [module ℝ E]

def spectral_filter (A : E→ₗ[ℝ]E) : list ℝ → (E→ₗ[ℝ]E)
| [] := linear_map.id
| (b::bs) := (A-b • linear_map.id).comp (spectral_filter bs)

theorem filter_eigenvector (A : E→ₗ[ℝ]E) (x : E) (a : ℝ) (hx : A x=a • x) (bs : list ℝ) :
 spectral_filter A bs x=(bs.map (λ b,a-b)).prod • x :=
begin
 induction bs with b bs ih,
 {simp [spectral_filter]},
 {simp only [spectral_filter,linear_map.comp_apply,linear_map.sub_apply,
     linear_map.smul_apply,linear_map.id_apply,ih,linear_map.map_smul,hx,list.map_cons,list.prod_cons],
  simp only [smul_smul,←sub_smul],congr' 1,ring}
end

theorem isolate_transition {ι : Type*} [fintype ι] [decidable_eq ι] (i₀ : ι)
 (A : E→ₗ[ℝ]E) (x : ι→E) (a : ι→ℝ) (bs : list ℝ)
 (eig : ∀ i,A (x i)=a i • x i) (others : ∀ i,i≠i₀ → a i∈bs) :
 spectral_filter A bs (∑ i,x i)=(bs.map (λ b,a i₀-b)).prod • x i₀ :=
begin
 rw [map_sum],simp_rw [filter_eigenvector A _ _ (eig _) bs],
 apply finset.sum_eq_single i₀,
 {intros j hj hji,
  have hmem : (0:ℝ)∈bs.map (λ b,a j-b) := list.mem_map.mpr ⟨a j,others j hji,sub_self _⟩,
  rw [list.prod_eq_zero hmem,zero_smul]},
 {intro h, exact (h (finset.mem_univ _)).elim}
end

theorem remaining_weight_nonzero (a : ℝ) (bs : list ℝ) (h : a∉bs) :
 (bs.map (λ b,a-b)).prod≠0 :=
begin
 induction bs with b bs ih, {simp},
 simp only [list.mem_cons_iff,not_or_distrib] at h,
 simp only [list.map_cons,list.prod_cons],
 exact mul_ne_zero (sub_ne_zero.mpr h.1) (ih h.2)
end
end spectral_filters

/-- Refining the one part with the sum of a list reaches that list; the rule
is valid inside any untouched prefix. All daughters must be strictly positive. -/
inductive refines : list ℕ → list ℕ → Prop
| refl (l) : refines l l
| split (i j : ℕ) (hi : 0<i) (hj : 0<j) : refines [i+j] [i,j]
| cons_head (i : ℕ) {l r} : refines l r → refines (i::l) (i::r)
| trans {l r t} : refines l r → refines r t → refines l t

theorem sum_pos_of_positive_parts (head : ℕ) (tail : list ℕ) (h : 0<head) :
 0<(head::tail).sum := by {simp only [list.sum_cons],omega}

theorem parts_from_one (t : list ℕ) : ∀ (a : ℕ), (∀ i∈(a::t),0<i) → refines [(a::t).sum] (a::t) :=
begin
 induction t with b u ih,
 {intros a hp,simp [refines.refl]},
 {intros a hp,
  have ha := hp a (list.mem_cons_self _ _),
  have hb := hp b (by simp),
  have step := refines.split a (b::u).sum ha (sum_pos_of_positive_parts b u hb),
  rw [list.sum_cons],
  exact refines.trans step (refines.cons_head a (ih b (λ i hi,hp i (list.mem_cons_of_mem a hi))))}
end

theorem all_partitions_reached (l : list ℕ) (hn : l≠[]) (hp : ∀ i∈l,0<i) : refines [l.sum] l :=
begin cases l with a t, {exact (hn rfl).elim}, {exact parts_from_one t a hp} end

theorem commute_child {E : Type*} [add_comm_group E] [module ℝ E]
 (A T : E→ₗ[ℝ]E) (parent child : E) (c a : ℝ) (ha : a≠0)
 (hc : A (T parent)=T (A parent)) (hp : A parent=c • parent) (ht : T parent=a • child) :
 A child=c • child :=
begin
 rw [ht,linear_map.map_smul,hp,linear_map.map_smul,ht] at hc,
 have k := congr_arg (λ v:E, a⁻¹ • v) hc,
 simpa [smul_smul,ha,mul_comm,mul_left_comm,mul_assoc] using k
end

theorem equilibrium_by_splits (C : list ℕ→Prop)
 (root : ∀ n,C [n]) (inherit : ∀ l r,refines l r→C l→C r)
 (l : list ℕ) (ne : l≠[]) (hp : ∀ i∈l,0<i) : C l :=
 inherit _ _ (all_partitions_reached l ne hp) (root _)

theorem finite_occupation_balance (counts : ℕ→ℝ) (m : ℕ) :
 ∑ i in finset.range (m+1),counts i=counts 0+∑ i in finset.range m,counts (i+1) :=
by {rw [finset.sum_range_succ',add_comm]}

theorem pair_balance (a b c d l r L R : ℝ) (hl : l*a=(1+L)*c) (hr : r*b=(1+R)*d) :
 (l*r)*(a*b)=(1+L)*(1+R)*(c*d) := by {calc
 (l*r)*(a*b)=(l*a)*(r*b) : by ring
 ... =_ : by {rw [hl,hr];ring}}

theorem rayleigh_head_tail {ι : Type*} [fintype ι] (w x cap : ι→ℝ) (W : ℝ) (hW : 0<W)
 (hw : ∀ i,0≤w i) (h : ∀ i,x i≤cap i) :
 (∑ i,w i*x i)/W≤(∑ i,w i*cap i)/W :=
 div_le_div_of_le hW.le (finset.sum_le_sum (λ i hi,mul_le_mul_of_nonneg_left (h i) (hw i)))

theorem time_ratio (pi a f K C z v : ℝ) (hf : f≠0) (hC : C≠0)
 (hz : z≠0) (hv : v≠0) (ha : a≠0) (matchT : K*f=48*v*C^2*z^2) :
 (2*pi*K/(z*v))/(z*C^2/(4*a*f))=384*pi*a :=
by {field_simp [hf,hC,hz,hv,ha];linear_combination 8*pi*a*matchT}

theorem common_mark (d b x y z : ℂ) (h : x+y+z=0) :
 d*x+b*y+b*z=(d-b)*x ∧ b*x+d*y+b*z=(d-b)*y ∧ b*x+b*y+d*z=(d-b)*z :=
 ⟨by linear_combination b*h,by linear_combination b*h,by linear_combination b*h⟩

theorem same_scalar_output (x y z A : ℂ) (h : x+y+z=0) : A*x+A*y+A*z=0 :=
by linear_combination A*h

theorem quadrupole_overlap : (((-1:ℝ)/2)^2-1/3)/(1-1/3)= -1/8 ∧
 (1+2*(-(1:ℝ)/8)=3/4 ∧ 1-(-(1:ℝ)/8)=9/8) := by norm_num

theorem radiation_gram (x y z : ℝ) :
 x^2+y^2+z^2-(x*y+y*z+z*x)/4=
 (3/4)*(x^2+y^2+z^2)+((x-y)^2+(y-z)^2+(z-x)^2)/8 := by ring

theorem absence_of_loss (p f : ℝ) (hp : 0<p) (hf : p*f=0) : f=0 :=
 (mul_eq_zero.mp hf).resolve_left hp.ne'

theorem bright_short (g amp : ℂ) (h : g*amp=0) (hg : g≠0) : amp=0 :=
 (mul_eq_zero.mp h).resolve_left hg

theorem critical_source_ode (g t : ℝ) :
 has_deriv_at (λ s:ℝ,real.exp (-g*s)*(1+g*s)) (-g*(real.exp (-g*t)*(g*t))) t :=
begin
 have d : has_deriv_at (λ s:ℝ,-g*s) (-g) t := by simpa using (has_deriv_at_id t).const_mul (-g),
 have b : has_deriv_at (λ s:ℝ,1+g*s) g t :=
 by simpa using (has_deriv_at_const t (1:ℝ)).add ((has_deriv_at_id t).const_mul g),
 convert d.exp.mul b using 1,ring
end

theorem critical_pair_ode (g t : ℝ) :
 has_deriv_at (λ s:ℝ,real.exp (-g*s)*(g*s))
 (g*(real.exp (-g*t)*(1+g*t))-2*g*(real.exp (-g*t)*(g*t))) t :=
begin
 have d : has_deriv_at (λ s:ℝ,-g*s) (-g) t := by simpa using (has_deriv_at_id t).const_mul (-g),
 convert d.exp.mul ((has_deriv_at_id t).const_mul g) using 1; simp; ring
end

theorem logistic_form (a s q : ℝ) (hs : s≠0) (h : 0<s) :
 q*(a-3*q/(2*s))=a*q-3*q^2/(2*s) := by {field_simp [hs];ring}

theorem logistic_derivative (x dx S : ℝ) (hx : 1+x≠0) :
 S*(dx*(1+x)-x*dx)/(1+x)^2=S*dx/(1+x)^2 := by ring

theorem regular_profile (a s x S : ℝ) (hs : s≠0) (hx : 1+x≠0) (eqn : 2*s*a=3*S) :
 S*a*x/(1+x)^2=(S*x/(1+x))*(a-3*(S*x/(1+x))/(2*s)) :=
begin
 have he : S=2*s*a/3 := by linarith,
 rw [he],field_simp [hs,hx];ring
end

theorem constant_velocity_equation (s B R q dq k dk : ℝ) (hr : R≠0) (hk : k≠0)
 (hq : k=q*R^2) (d : dk= -s*(2*R*q+R*dq))
 (ode : s*dq=q*(B-2*s-3*q/2)) :
 dk/k+B/R-3*k/(2*R^3)=0 :=
begin
 have hcalc : dk=R*q*(-B+3*q/2) := by {rw [d]; linear_combination -R*ode},
 have hn : q≠0 := λ he,hk (by simp [hq,he]),
 rw [hcalc,hq],field_simp [hr,hn];ring
end

theorem time_integrated_mass (m : ℝ→ℝ) (flux : ℝ→ℝ) (a b : ℝ)
 (h : ∀ t∈uIcc a b,has_deriv_at m (-flux t) t)
 (hi : interval_integrable flux volume a b) :
 (∫ t in a..b,flux t)=m a-m b :=
begin
 have h' := interval_integral.integral_eq_sub_of_has_deriv_at h hi.neg,
 rw [interval_integral.integral_neg] at h',linarith
end

theorem smooth_power_bounds (r x q C : ℝ) (hr : 0<r) (hx : 0≤x) (hb : x≤q*r^3)
 (hC : 0≤C) :
 0≤C*x^2/r^4 ∧ C*x^2/r^4≤C*q^2*r^2 :=
begin
 have hk : x^2≤(q*r^3)^2 := pow_le_pow_of_le_left hx hb 2,
 split, {positivity}, {apply (div_le_iff (pow_pos hr _)).2,
  calc C*x^2 ≤ C*(q*r^3)^2 : mul_le_mul_of_nonneg_left hk hC
  ... = _ : by ring}
end

theorem cartesian_last_derivatives (A r : ℝ) (hA : 0≤A) (hr : 0<r) (hs : r≤1)
 (h0 h1 h2 : ℝ) (b0 : |h0|≤A*r^3) (b1 : |h1|≤A*r^2) (b2 : |h2|≤A*r) :
 max (max (abs h0) (abs h1)) (abs h2)≤A*r :=
begin
 apply max_le _ b2,apply max_le,
 {apply b0.trans,apply mul_le_mul_of_nonneg_left _ hA,nlinarith [sq_nonneg r,mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hs)]},
 {apply b1.trans,apply mul_le_mul_of_nonneg_left _ hA,nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hs)]}
end

theorem recoil_log (etaRate kRate k R B v q : ℝ) (hr : R≠0)
 (h : etaRate=kRate/k+B/R-3*q/(2*R)) :
 kRate/k-etaRate-v/R= -((B+v)-3*q/2)/R :=
by {rw [h];field_simp [hr];ring}

theorem inward_mass (e B v q W mass : ℝ) (hw : W=e*(B-v)) (hm : mass=e*(B-q/2)) :
 2*mass=W+e*(B+v-q) := by {rw [hm,hw];ring}

theorem recoil_slope (E q R Rc : ℝ) (hc : 0<Rc) (hr : Rc≤R)
 (he : E≤1) (hq : 0≤q) :
 -1/Rc≤ -(E-3*q/2)/R :=
begin
 have hR := lt_of_lt_of_le hc hr,
 apply (div_le_div_iff hc hR).2,nlinarith [mul_nonneg hc.le hq,mul_nonneg hc.le (sub_nonneg.mpr he)]
end

theorem recoil_integral (logW : ℝ→ℝ) (g : ℝ→ℝ) (a b c : ℝ) (hab : a≤b)
 (h : ∀ t∈uIcc a b,has_deriv_at logW (g t) t)
 (hi : interval_integrable g volume a b) (hl : ∀ t∈Icc a b,c≤g t) :
 c*(b-a)≤logW b-logW a :=
begin
 rw [←interval_integral.integral_eq_sub_of_has_deriv_at h hi],
 have k:=interval_integral.integral_mono_on hab (interval_integrable_const : interval_integrable (λ _:ℝ,c) volume a b) hi hl,
 simpa [interval_integral.integral_const,mul_comm] using k
end

theorem bounce_minimum (m k r H : ℝ) (h : m*r^3=k^2) (hr : r≠0)
 (hk : k≠0) (hb : H=m*r/k+k/(2*r^2)) : 8*k*H^3=27*m^2 :=
begin
 have hm : m=k^2/r^3 := (eq_div_iff (pow_ne_zero _ hr)).2 h,
 rw [hb,hm],field_simp [hr,hk];ring
end

theorem outer_turn (q : ℝ) (hd : q*(1-q/2)>q^2) (hq : 0<q) :
 q<2/3 ∧ 2*q-q^2<8/9 :=
begin
 have h : 0<q*(1-3*q/2) := by nlinarith only [hd],
 have hl : 0<1-3*q/2 := lt_of_not_ge (λ hh,(not_le_of_gt h) (mul_nonpos_of_nonneg_of_nonpos hq.le hh)),
 split, {linarith}, {nlinarith [mul_pos (show 0<2/3-q,by linarith) (show 0<4/3-q,by linarith)]}
end

theorem unique_one_part_head (a b : ℝ) (ha : 0<a) (hb : 0<b) : a^3+b^3<(a+b)^3 :=
begin have h := mul_pos (mul_pos ha hb) (add_pos ha hb),nlinarith end

theorem positive_port_loss {ι : Type*} [fintype ι] (p f : ι→ℝ)
 (hp : ∀ j,0≤p j) (hn : ∀ j,0≤f j) (total : ∑ j,p j*f j=0) (i : ι) (hi : 0<f i) :
 p i=0 :=
begin
 have term := finset.single_le_sum (λ j (hj:j∈(finset.univ:finset ι)), mul_nonneg (hp j) (hn j)) (finset.mem_univ i),
 rw [total] at term,
 exact (mul_eq_zero.mp (le_antisymm term (mul_nonneg (hp i) (hn i)))).resolve_right hi.ne'
end

theorem planar_tide (w : ℝ) :
 105/9 - 15*(4/9) + 6*(w^2-1/3) = 3+6*w^2 := by ring

theorem passive_exchange (G u l w d : ℝ) (hu : 0<u) (hw : 0<w) (hd : d≠0) :
 (9/8)*G*(2*u*l)^2*(1/(2*u*w))/d^5=9*G*u*l^2/(4*w*d^5) :=
by {field_simp [hu.ne',hw.ne',hd];ring}

theorem local_transfer_solution (g t : ℝ) :
 has_deriv_at (λ s:ℝ, real.sin (g*s)) (g*real.cos (g*t)) t ∧
 has_deriv_at (λ s:ℝ, real.cos (g*s)) (-g*real.sin (g*t)) t :=
begin
 have d : has_deriv_at (λ s:ℝ,g*s) g t := by simpa using (has_deriv_at_id t).const_mul g,
 split, {simpa [mul_comm] using d.sin}, {convert d.cos using 1;ring}
end

theorem no_complete_capture_yet (g t : ℝ) (h0 : 0≤g*t) (hpi : g*t<real.pi/2) :
 real.sin (g*t)^2<1 :=
begin
 have hc := real.cos_pos_of_mem_Ioo ⟨lt_of_lt_of_le (by linarith [real.pi_pos] : -(real.pi/2)<0) h0,hpi⟩,
 nlinarith [real.sin_sq_add_cos_sq (g*t),mul_self_pos.mpr hc.ne']
end

theorem recoil_exponential (L T r W W₀ m e z : ℝ) (hr : r≠0) (hp : 0<W₀)
 (hend : W=W₀*real.exp L) (bound : -(1/r)*T≤L) (branch : 0≤e*z) (mass : 2*m=W+e*z) :
 W₀*real.exp (-T/r)/2≤m :=
begin
 have h : -T/r≤L := by {convert bound using 1;ring},
 have he := mul_le_mul_of_nonneg_left (real.exp_le_exp.mpr h) hp.le,
 rw [←hend] at he,linarith
end

theorem subtracted_passive_spectrum (s mu k p : ℝ) (hm : 0<mu) (hk : 0<k)
 (dispersion : k^2=mu^2+s^2) :
 s^2*p^2/((p^2+mu^2)*(p^2+k^2))=k^2/(p^2+k^2)-mu^2/(p^2+mu^2) :=
begin
 have a : p^2+mu^2≠0 := (add_pos_of_nonneg_of_pos (sq_nonneg p) (sq_pos_of_pos hm)).ne',
 have b : p^2+k^2≠0 := (add_pos_of_nonneg_of_pos (sq_nonneg p) (sq_pos_of_pos hk)).ne',
 field_simp [a,b]; rw [dispersion]; ring
end

theorem spectrum_antiderivative (m t : ℝ) (hm : 0<m) :
 has_deriv_at (λ x:ℝ,m*real.arctan (x/m)) (m^2/(t^2+m^2)) t :=
begin
 have d := (((has_deriv_at_id t).div_const m).arctan).const_mul m,
 convert d using 1,
 have a : t^2+m^2≠0 := (add_pos_of_nonneg_of_pos (sq_nonneg t) (sq_pos_of_pos hm)).ne',
 have c : 1+(t/m)^2=(t^2+m^2)/m^2 := by {field_simp [hm.ne'];ring},
 simp only [id.def],rw [c,one_div_div],field_simp [hm.ne',a];ring
end

theorem spectrum_integral (m b : ℝ) (hm : 0<m) :
 (∫ p in (0:ℝ)..b,m^2/(p^2+m^2))=m*real.arctan (b/m) :=
begin
 have cc : continuous (λ p:ℝ,m^2/(p^2+m^2)) :=
 continuous_const.div ((continuous_id.pow 2).add continuous_const)
   (λ p,(add_pos_of_nonneg_of_pos (sq_nonneg p) (sq_pos_of_pos hm)).ne'),
 have h := interval_integral.integral_eq_sub_of_has_deriv_at (λ p hp,spectrum_antiderivative m p hm)
   (cc.interval_integrable 0 b),
 simpa using h
end

theorem subtract_static (k mu : ℝ) : mu+(2/real.pi)*(k*(real.pi/2)-mu*(real.pi/2))=k :=
by {field_simp [real.pi_ne_zero];ring}

theorem first_echo (k e : ℝ) (hk : k≠0) (he : 0<e) (h1 : e≠1) :
 (k-k*((1+e)/(1-e)))/(k+k*((1+e)/(1-e)))= -e :=
begin
 have den : 1-e≠0 := sub_ne_zero.mpr (ne.symm h1),
 have a : k+k*((1+e)/(1-e))=2*k/(1-e) := by {field_simp [den];ring},
 rw [a],field_simp [hk,den];ring
end

theorem discrete_boundary_weights (p mu s : ℝ) (h : 0<p) :
 (mu^2+s^2)/(p^2+mu^2+s^2)-mu^2/(p^2+mu^2)=
 p^2*s^2/((p^2+mu^2)*(p^2+mu^2+s^2)) :=
begin
 have a : 0<p^2+mu^2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos h) (sq_nonneg mu),
 have b : 0<p^2+mu^2+s^2 := add_pos_of_pos_of_nonneg a (sq_nonneg s),
 field_simp [a.ne',b.ne'];ring
end

theorem no_echo_in_window (v L T t : ℝ) (hv : 0<v) (h : v*T<2*L) (cut : t≤T) :
 t<2*L/v :=
(lt_div_iff hv).mpr (by {rw [mul_comm];exact (mul_le_mul_of_nonneg_left cut hv.le).trans_lt h})

section current_algebra
variables {E : Type*} [add_comm_group E] [module ℝ E]
def commutes_on (A V : E→ₗ[ℝ]E) : Prop := ∀ x,A (V x)=V (A x)

theorem closed_under_current_filter (A D V : E→ₗ[ℝ]E) (b : ℝ)
 (hD : commutes_on A D) (hV : commutes_on A V) :
 commutes_on A ((D.comp V-V.comp D)-b • V) :=
begin
 unfold commutes_on at hD hV,
 intro x,simp only [linear_map.sub_apply,linear_map.comp_apply,linear_map.smul_apply,
  map_sub,linear_map.map_smul,hD,hV]
end

theorem recover_split_coefficients (A : E→ₗ[ℝ]E) (stage : E→ₗ[ℝ]E) (c : ℝ)
 (hc : c≠0) (h : commutes_on A (c • stage)) : commutes_on A stage :=
begin
 intro x,have k:=h x,simp only [linear_map.smul_apply,linear_map.map_smul] at k,
 have z := congr_arg (λ y:E,c⁻¹ • y) k,simpa [smul_smul,hc] using z
end

theorem scalar_on_partitions (A : E→ₗ[ℝ]E) (basis : list ℕ→E) (c : ℝ)
 (step : ∀ (pre : list ℕ) (i j : ℕ), 0<i → 0<j → ∃ (T : E→ₗ[ℝ]E) (w : ℝ),
  w≠0 ∧ commutes_on A T ∧ T (basis (pre++[i+j]))=w • basis (pre++[i,j]))
 (t : list ℕ) : ∀ (pre : list ℕ) (a : ℕ), (∀ i∈a::t,0<i) →
 A (basis (pre++[(a::t).sum]))=c • basis (pre++[(a::t).sum]) →
 A (basis (pre++(a::t)))=c • basis (pre++(a::t)) :=
begin
 induction t with b u ih,
 {intros pre a hp root,simpa using root},
 {intros pre a hp root,
  have ha := hp a (by simp),
  have hb := hp b (by simp),
  rcases step pre a (b::u).sum ha (sum_pos_of_positive_parts b u hb) with ⟨T,w,hw,hT,he⟩,
  rw [list.sum_cons] at root,
  have child:=commute_child A T _ _ c w hw (hT _) root he,
  have next := ih (pre++[a]) b (λ i hi,hp i (list.mem_cons_of_mem a hi)),
  simp only [list.append_assoc,list.singleton_append] at next,exact next child}
end
end current_algebra

theorem count_shared_parts (a b n : ℕ) (ha : a≤n) :
 (finset.range n).filter (λ j,j<a ∧ j<b)=finset.range (min a b) :=
begin ext j,simp only [finset.mem_filter,finset.mem_range,lt_min_iff],omega end

theorem independent_tail_square {ι : Type*} [decidable_eq ι] (s : finset ι) (occ : ι→ℕ) (r : ℕ) :
 ((s.product s).filter (λ p:ι×ι,r≤occ p.1 ∧ r≤occ p.2)).card=
 ((s.filter (λ i,r≤occ i)).card)^2 :=
begin
 have sets : (s.product s).filter (λ p:ι×ι,r≤occ p.1 ∧ r≤occ p.2)=
 (s.filter (λ i,r≤occ i)).product (s.filter (λ i,r≤occ i)) :=
 by {ext p,simp only [finset.mem_filter,finset.mem_product],tauto},
 rw [sets,finset.card_product,pow_two]
end

theorem energy_left_without_partners (a b : ℕ) : a+b-2*(min a b)=(a-b)+(b-a) :=
begin rcases le_total a b with h|h, {rw [min_eq_left h],omega}, {rw [min_eq_right h],omega} end

theorem paired_tail_comparison {ι : Type*} (s : finset ι) (q p w tail : ι→ℝ) (d : ℝ)
 (hw : ∀ i,0≤w i) (each : ∀ i∈s,|q i-p i|≤d*p i+tail i) :
 |(∑ i in s,w i*q i)-(∑ i in s,w i*p i)|≤d*(∑ i in s,w i*p i)+(∑ i in s,w i*tail i) :=
begin
 rw [←finset.sum_sub_distrib],
 calc |∑ i in s,(w i*q i-w i*p i)|≤∑ i in s,|w i*q i-w i*p i| : finset.abs_sum_le_sum_abs _ _
 ... ≤ ∑ i in s,(d*(w i*p i)+w i*tail i) : finset.sum_le_sum (λ i hi,begin
   rw [←mul_sub,abs_mul,abs_of_nonneg (hw i)],
   calc w i*|q i-p i|≤w i*(d*p i+tail i) : mul_le_mul_of_nonneg_left (each i hi) (hw i)
   ... = _ : by ring
 end)
 ... = _ : by rw [finset.sum_add_distrib,finset.mul_sum]
end

theorem escaping_quarter (F M err : ℕ→ℝ)
 (hM : tendsto M at_top (𝓝 (1/4:ℝ))) (he : tendsto err at_top (𝓝 0))
 (h : ∀ n,|F n-M n|≤err n) : tendsto F at_top (𝓝 (1/4:ℝ)) :=
begin
 have low : tendsto (λ n,M n-err n) at_top (𝓝 (1/4:ℝ)) := by simpa using hM.sub he,
 have high : tendsto (λ n,M n+err n) at_top (𝓝 (1/4:ℝ)) := by simpa using hM.add he,
 exact tendsto_of_tendsto_of_tendsto_of_le_of_le low high
   (λ n,by {change M n-err n≤F n,have hh := (abs_le.mp (h n)).1, linarith})
   (λ n,by {change F n≤M n+err n,have hh := (abs_le.mp (h n)).2, linarith})
end

theorem all_pair_brightness (a b c d g e : ℝ)
 (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d) (hg : 0<g) (he : 0<e)
 (hl : 0<a+b) (hr : 0<c+d) : 0<g*(a*c+b*d)+e*(a*d+b*c) :=
begin
 have first : 0≤a*c+b*d := add_nonneg (mul_nonneg ha hc) (mul_nonneg hb hd),
 have second : 0≤a*d+b*c := add_nonneg (mul_nonneg ha hd) (mul_nonneg hb hc),
 rcases lt_or_eq_of_le first with h|h,
 {exact add_pos_of_pos_of_nonneg (mul_pos hg h) (mul_nonneg he.le second)},
 {have pos : 0<a*d+b*c := by nlinarith [mul_pos hl hr],rw [←h,mul_zero,zero_add],exact mul_pos he pos}
end

theorem partner_spectrum (x e : ℝ) (hx : x≠1) (nz : 1+e*(1+x)≠0) :
 ((x/(1-x))^2+e*((x/(1-x))+2*(x/(1-x))^2))/
 ((1+x/(1-x))^2+e*(1+3*(x/(1-x))+2*(x/(1-x))^2))=
 (x^2+e*x*(1+x))/(1+e*(1+x)) :=
begin
 have h : 1-x≠0 := sub_ne_zero.mpr (ne.symm hx),
 have a : (x/(1-x))^2+e*(x/(1-x)+2*(x/(1-x))^2)=(x^2+e*x*(1+x))/(1-x)^2 :=
 by {field_simp [h];ring},
 have b : (1+x/(1-x))^2+e*(1+3*(x/(1-x))+2*(x/(1-x))^2)=(1+e*(1+x))/(1-x)^2 :=
 by {field_simp [h];ring},
 rw [a,b],field_simp [h,nz];ring
end

theorem one_percent_partner (e : ℝ) (he : 0≤e) :
 ((1/2:ℝ)^2+e*(1/2)*(1+1/2))/(1+e*(1+1/2))≤(101/100)*(1/2)^2 ↔ e≤2/297 :=
begin
 have nz : 0< 1+e*(1+(1:ℝ)/2) := by linarith,
 rw [div_le_iff nz],split;intro h;ring_nf at *;linarith
end

theorem gaussian_record_square (y u v : ℝ) :
 (y-u)^2+(y-v)^2=2*(y-(u+v)/2)^2+(u-v)^2/2 := by ring

theorem equal_energy_mark (energy : ℝ) (weight : ℝ) (h : weight≠0) :
 (weight*energy)/weight=energy := by {field_simp [h];ring}

section dissipative_matrices
open_locale matrix
variables {ι : Type*} [fintype ι]
def current_bracket (D A : matrix ι ι ℂ) : matrix ι ι ℂ := D ⬝ A-A ⬝ D

theorem trace_adjoint_bracket (D A B : matrix ι ι ℂ) (hD : D.conj_transpose=D) :
 matrix.trace ((current_bracket D A).conj_transpose ⬝ B)=
 matrix.trace (A.conj_transpose ⬝ current_bracket D B) :=
begin
 simp only [current_bracket,matrix.conj_transpose_sub,matrix.conj_transpose_mul,hD,
    matrix.sub_mul,matrix.mul_sub,matrix.trace_sub,matrix.mul_assoc],
 rw [matrix.trace_mul_cycle' A.conj_transpose B D]
end

theorem trace_of_square (Y : matrix ι ι ℂ) :
 (matrix.trace (Y.conj_transpose ⬝ Y)).re=∑ i,∑ j,complex.norm_sq (Y j i) :=
begin
 simp [matrix.trace,matrix.diag,matrix.mul_apply,matrix.conj_transpose_apply,complex.norm_sq_apply,
       complex.mul_re,complex.star_def]
end

theorem matrix_current_dissipation (D A : matrix ι ι ℂ) (hD : D.conj_transpose=D) :
 (matrix.trace (A.conj_transpose ⬝ current_bracket D (current_bracket D A))).re=
 ∑ i,∑ j,complex.norm_sq (current_bracket D A j i) :=
by rw [←trace_adjoint_bracket _ _ _ hD,trace_of_square]

theorem fixed_current_algebra {κ : Type*} [fintype κ] (D : κ→matrix ι ι ℂ) (A : matrix ι ι ℂ)
 (g : κ→ℝ) (hg : ∀ k,0<g k) (hD : ∀ k,(D k).conj_transpose=D k)
 (stationary : ∑ k,(matrix.trace (A.conj_transpose ⬝
   current_bracket (D k) (current_bracket (D k) A))).re*g k=0) :
 ∀ k,current_bracket (D k) A=0 :=
begin
 classical,
 simp_rw [matrix_current_dissipation _ _ (hD _)] at stationary,
 have nonneg : ∀ k,0≤∑ i,∑ j,complex.norm_sq (current_bracket (D k) A j i) :=
 λ k,finset.sum_nonneg (λ i _,finset.sum_nonneg (λ j _,complex.norm_sq_nonneg _)),
 intro k,
 have zero_k:=positive_port_loss _ g nonneg (λ z,(hg z).le) stationary k (hg k),
 have hc : ∀ i,0≤∑ j,complex.norm_sq (current_bracket (D k) A j i) :=
 λ i,finset.sum_nonneg (λ j _,complex.norm_sq_nonneg _),
 have ht : ∀ i,(∑ j,complex.norm_sq (current_bracket (D k) A j i))≤0 :=
 λ i,calc (∑ j,complex.norm_sq (current_bracket (D k) A j i)) ≤ ∑ i,∑ j,complex.norm_sq (current_bracket (D k) A j i) :
   finset.single_le_sum (λ l hl,hc l) (finset.mem_univ i)
 ... = 0 : zero_k,
 apply matrix.ext,intros j i,
 apply complex.norm_sq_eq_zero.mp,
 apply le_antisymm _ (complex.norm_sq_nonneg _),
 have component : ∀ l,0≤complex.norm_sq (current_bracket (D k) A l i) := λ l,complex.norm_sq_nonneg _,
 have alone : complex.norm_sq (current_bracket (D k) A j i)≤∑ l,complex.norm_sq (current_bracket (D k) A l i) :=
    finset.single_le_sum (λ l hl,component l) (finset.mem_univ j),
 exact alone.trans (ht i)
end
end dissipative_matrices

theorem whole_energy_requires_same_parts {ι : Type*} [fintype ι] (w n m : ι→ℝ)
 (hp : ∀ i,0<w i) (h1 : (∑ i,w i*n i)=(∑ i,w i*min (n i) (m i)))
 (h2 : (∑ i,w i*m i)=(∑ i,w i*min (n i) (m i))) : n=m :=
begin
 have left : ∀ i,n i-min (n i) (m i)=0,
 {intro i,apply positive_port_loss (λ j,n j-min (n j) (m j)) w
    (λ j,sub_nonneg.mpr (min_le_left (n j) (m j))) (λ j,(hp j).le) _ i (hp i),
  calc (∑ j,(n j-min (n j) (m j))*w j)=(∑ j,w j*n j)-(∑ j,w j*min (n j) (m j)) :
    by {rw [←finset.sum_sub_distrib],apply finset.sum_congr rfl,intros j hj,ring}
   ... = 0 : by rw [h1,sub_self]},
 have right : ∀ i,m i-min (n i) (m i)=0,
 {intro i,apply positive_port_loss (λ j,m j-min (n j) (m j)) w
    (λ j,sub_nonneg.mpr (min_le_right (n j) (m j))) (λ j,(hp j).le) _ i (hp i),
  calc (∑ j,(m j-min (n j) (m j))*w j)=(∑ j,w j*m j)-(∑ j,w j*min (n j) (m j)) :
    by {rw [←finset.sum_sub_distrib],apply finset.sum_congr rfl,intros j hj,ring}
   ... = 0 : by rw [h2,sub_self]},
 exact funext (λ i,(sub_eq_zero.mp (left i)).trans (sub_eq_zero.mp (right i)).symm)
end

theorem complete_release_probability {ι : Type*} [decidable_eq ι] (s : finset ι) (hs : s.card≠0) :
 (s.diag.card:ℝ)/(s.product s).card=1/(s.card:ℝ) :=
begin
 have h : (s.card:ℝ)≠0 := by exact_mod_cast hs,
 rw [finset.diag_card,finset.card_product,nat.cast_mul],field_simp [h];ring
end

end soft_charge_release
