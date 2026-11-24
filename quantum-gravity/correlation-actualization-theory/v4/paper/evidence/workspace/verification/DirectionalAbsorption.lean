import tactic
import analysis.special_functions.integrals
import data.complex.basic
import analysis.analytic.uniqueness

noncomputable theory
namespace directional_absorption

-- Components in the instantaneous radial spin frame; d=F'+G', v=F'-G'.
theorem born_sum (d v : ℝ) : (d-v)^2+(d+v)^2=2*(d^2+v^2) := by ring
theorem radial_amplitudes (f g : ℂ) : (f+g)-(f-g)=2*g ∧ (f+g)+(f-g)=2*f :=
by {split;ring}
-- Spin-up at the first site in the |+->,|-+> basis.
def sort₀ (d v : ℂ) (x : ℂ × ℂ) : ℂ × ℂ := ((d-v)*x.1,(d+v)*x.2)
def sort₁ (d v : ℂ) (x : ℂ × ℂ) : ℂ × ℂ := ((d-v)*x.2,(d+v)*x.1)
theorem singlet_two_marks (d v z : ℂ) :
 sort₁ d v (z,-z) = (-(sort₀ d v (z,-z)).1,-(sort₀ d v (z,-z)).2) :=
by {apply prod.ext;dsimp [sort₀,sort₁];ring}
theorem outward_only (f z : ℂ) : sort₀ f f (z,-z)=(0,-(2*f*z)) :=
by {apply prod.ext;dsimp [sort₀];ring}
theorem wrong_weight (f g : ℝ) (h : f^2+g^2≠0) :
 ((2*g)^2)/((2*f)^2+(2*g)^2) = g^2/(f^2+g^2) :=
by {have h' : (2*f)^2+(2*g)^2≠0, {rw [show (2*f)^2+(2*g)^2=4*(f^2+g^2),by ring], exact mul_ne_zero (by norm_num) h},field_simp [h,h'];ring}
theorem clean_window (t l χ : ℝ) : (t+2-l-χ)-(t+χ-l)=2*(1-χ) := by ring
theorem clean_before_return (t l χ : ℝ) (h : χ<1) : t+χ-l<t+2-l-χ := by linarith
theorem finite_silence (dose : ℝ) : 0<real.exp (-dose) := real.exp_pos _
theorem finite_cluster_silence (dose : ℝ) (n : ℕ) : 0<(real.exp (-dose))^n :=
pow_pos (real.exp_pos _) _
theorem null_echo (vi vc optical_i optical_b latency : ℝ) :
 vi+2*(optical_b-optical_i)+latency≤vc ↔
 2*(optical_b-optical_i)+latency≤vc-vi := by {constructor;intro h;linarith}
theorem advanced_primitive (x : ℝ) (hx : 0<x) :
 has_deriv_at (λ y:ℝ,2*(y^3/3-y^2/2+y-real.log (1+y))) (2*x^3/(1+x)) x :=
begin
 have hn : (1:ℝ)+x≠0 := by linarith,
 have hlog := (real.has_deriv_at_log hn).comp x ((has_deriv_at_const x (1:ℝ)).add (has_deriv_at_id x)),
 have hp := (((((has_deriv_at_pow 3 x).div_const 3).sub ((has_deriv_at_pow 2 x).div_const 2)).add (has_deriv_at_id x)).sub hlog).const_mul 2,
 convert hp using 1,
 norm_num,field_simp [hn];ring
end

-- Four components ordered empty, spin-up, spin-down, double. Reference
-- amplitudes may be arbitrary complex numbers, including symmetry sectors.
def orbital := ℂ × ℂ × ℂ × ℂ
def bond (a b : ℂ) (v : orbital) : orbital := (a*v.2.2.2,b*v.2.2.1,-b*v.2.1,a*v.1)
def upper (a b : ℂ) (v : orbital) : orbital := (-b*v.2.2.2,a*v.2.2.1,-a*v.2.1,-b*v.1)
def multiple (k : ℂ) (v : orbital) : orbital := (k*v.1,k*v.2.1,k*v.2.2.1,k*v.2.2.2)
theorem crossed_bonds (a b : ℂ) (v : orbital) : bond a b (upper a b v)=multiple (-a*b) v :=
by {rcases v with ⟨v₀,v₁,v₂,v₃⟩,dsimp [bond,upper,multiple],simp only [prod.mk.inj_iff],repeat {split};ring}
theorem entangled_reference {ι : Type} (a b : ℂ) (v : ι → orbital) :
 (λ i, bond a b (upper a b (v i)))=(λ i,multiple (-a*b) (v i)) :=
funext (λ i,crossed_bonds a b (v i))
theorem dimer_weight (u d t : ℝ) (hd : d≠0) (h : d^2=u^2+16*t^2) :
 ((1-u/d)/2)*((1+u/d)/2)/4=t^2/d^2 :=
by {field_simp [hd];nlinarith}
theorem energy_gap (u d : ℝ) : (u+d)/2-(u-d)/2=d := by ring
theorem bond_work (u d spectator : ℝ) :
 ((u+d)/2+spectator)-((u-d)/2+spectator)=d := by ring
theorem source_response (h d : ℝ) (hd : d≠0) :
 (-2*h/d)^2=4*(h^2/d^2) := by {field_simp [hd];ring}

-- The low,high plane at each input vector. On its orthogonal complement the
-- Kraus normalization follows directly from L and 1-L being projections.
def input_project (a b : ℂ) (v : ℂ × ℂ) : ℂ × ℂ := (a*(a*v.1+b*v.2),b*(a*v.1+b*v.2))
def select_low (v : ℂ × ℂ) : ℂ × ℂ := (v.1,0)
theorem normalized_commutator (a b x y : ℂ) (ha : a≠0) (hb : b≠0) :
 let p:=input_project a b (x,y), z:=input_project a b (select_low (x,y)) in
 (((select_low p).1-z.1)/(a*b),((select_low p).2-z.2)/(a*b))=(y,-x) :=
by {dsimp [input_project,select_low],apply prod.ext;dsimp;field_simp [ha,hb];ring}
theorem quarter_turn (z : ℂ × ℂ) :
 (real.cos (real.pi/2):ℂ)*z.1+(real.sin (real.pi/2):ℂ)*z.2=z.2 ∧
 (real.cos (real.pi/2):ℂ)*z.2-(real.sin (real.pi/2):ℂ)*z.1= -z.1 :=
by simp [real.cos_pi_div_two,real.sin_pi_div_two]
theorem preserved_coherence (q : ℝ) (z w : ℂ) :
 (q:ℂ)*z*w+(1-(q:ℂ))*z*w=z*w := by ring

theorem area_single_mode (m ω : ℝ) : (m-ω)^2-ω^2=m^2-2*m*ω := by ring
theorem two_mode_invariant (m a b c : ℝ) :
 (m-a-b)^2-(a^2+b^2+2*a*b*c)=m^2-2*m*(a+b)+2*a*b*(1-c) := by ring
theorem pair_covariance (u v r z : ℝ) (hz : z=1+u+v+u*v*r) (hn : z≠0) :
 u*v*r/z-((u+u*v*r)/z)*((v+u*v*r)/z)=u*v*(r-1)/z^2 :=
by {field_simp [hn];rw [hz];ring}
theorem thermal_cell (f : ℝ) : (1-f)^2+2*f*(1-f)+f^2=1 ∧
 2*f*(1-f)+2*f^2=2*f := by {split;ring}
theorem escaping_one (f t : ℝ) :
 2*f*(1-f)*t+f^2*(2*t*(1-t))=2*f*t*(1-f*t) := by ring
theorem tagged_posterior (f t : ℝ) (hf : f≠0) (ht : t≠0) (hh : 1-f*t≠0) :
 (2*f*(1-f)*t)/(2*f*t*(1-f*t))=(1-f)/(1-f*t) :=
by {field_simp [hf,ht,hh];ring}
theorem return_bookkeeping (m ω ν : ℝ) : m+ω-ν+ν=m+ω := by ring
theorem geometric_survival (t : ℝ) (n : ℕ) : (1-t)^n*(1-t)=(1-t)^(n+1) :=
by rw [pow_succ,mul_comm]
theorem entropy_flags (s f flag : ℝ) :
 (flag+(1-f)*s+f*s)-(flag+f*s)=(1-f)*s := by ring
theorem allowed_reads (capacity cost μ : ℝ) (hc : 0<capacity) :
 cost≤(1-μ)*capacity ↔ μ≤1-cost/capacity :=
begin
 rw [le_sub_comm,div_le_iff hc]
end
theorem transfer_rapidity (a b d : ℝ) (h₁ : |a-b|≤d) :
 |2*a-2*b|≤2*d :=
by {rw [show 2*a-2*b=2*(a-b),by ring,abs_mul,abs_of_nonneg (show (0:ℝ)≤2,by norm_num)],linarith}
-- Gronwall for the no-jump norm squared, in either forward or adjoint
-- evolution. A is the integrated bound on the loss rate.
theorem no_jump_norm {f A q v : ℝ → ℝ} {T : ℝ} (hT : 0≤T)
 (hf : ∀ x, has_deriv_at f (v x) x) (hA : ∀ x, has_deriv_at A (q x) x)
 (loss : ∀ x∈set.Icc 0 T, -(q x)*f x≤v x) (h₀ : A 0=0) :
 f 0≤real.exp (A T)*f T :=
begin
 let k := λ x:ℝ, real.exp (A x)*f x,
 have hd : ∀ x,has_deriv_at k (real.exp (A x)*q x*f x+real.exp (A x)*v x) x :=
   λ x, ((hA x).exp).mul (hf x),
 have hm : monotone_on k (set.Icc 0 T),
 { apply (convex_Icc (0:ℝ) T).monotone_on_of_deriv_nonneg,
   { exact λ x hx,(hd x).continuous_at.continuous_within_at },
   { exact λ x hx,(hd x).differentiable_at.differentiable_within_at },
   { intros x hx,rw [(hd x).deriv],have hl:=loss x (interior_subset hx),
     have h' : 0≤q x*f x+v x := by linarith,
     nlinarith [mul_nonneg (real.exp_pos (A x)).le h'] }},
 have h := hm ⟨le_rfl,hT⟩ ⟨hT,le_rfl⟩ hT,
 change real.exp (A 0)*f 0≤real.exp (A T)*f T at h,
 rwa [h₀,real.exp_zero,one_mul] at h
end
theorem faithful_cut (lower normsq weight other p : ℝ)
 (hlo : 0<lower) (hn : 0<normsq) (hw : lower*normsq≤weight)
 (ho : 0≤other) (hp : p=weight+other) : 0<p :=
by {have h:=mul_pos hlo hn,linarith}

-- A singlet S and the zero-magnetic triplet T in the local radial frame.
def rotate_pair (θ : ℝ) : ℝ × ℝ := (real.cos θ,-real.sin θ)
theorem counterdrive (θ : ℝ → ℝ) (t d : ℝ) (h : has_deriv_at θ d t) :
 has_deriv_at (λ u, (rotate_pair (θ u)).1) (-real.sin (θ t)*d) t ∧
 has_deriv_at (λ u, (rotate_pair (θ u)).2) (-(real.cos (θ t)*d)) t :=
⟨(real.has_deriv_at_cos _).comp t h,((real.has_deriv_at_sin _).comp t h).neg⟩
theorem saturated_pair :
 let a := (rotate_pair (real.pi/4)).1, b := (rotate_pair (real.pi/4)).2 in
 (a+b)/real.sqrt 2=0 ∧ (-a+b)/real.sqrt 2= -1 :=
begin
 dsimp [rotate_pair],rw [real.cos_pi_div_four,real.sin_pi_div_four],
 have hn : real.sqrt 2≠0 := ne_of_gt (real.sqrt_pos.2 (by norm_num)),
 split;field_simp [hn];ring
end
def smooth_gate (x : ℝ) := 10*x^3-15*x^4+6*x^5
theorem gate_ends : smooth_gate 0=0 ∧ smooth_gate 1=1 := by norm_num [smooth_gate]
theorem gate_derivative (x : ℝ) :
 has_deriv_at smooth_gate (30*x^2*(1-x)^2) x :=
begin
 have h:=(((has_deriv_at_pow 3 x).const_mul 10).sub
  ((has_deriv_at_pow 4 x).const_mul 15)).add ((has_deriv_at_pow 5 x).const_mul 6),
 convert h using 1,norm_num;ring
end

-- Exact finite one-loss certificate: an entry lists every residual word of
-- one orbital in one logical word. Unordered signs cannot contribute a cross
-- term when all 455 residual words are distinct.
def reps : list ℕ := [47,115,155,213,233,331,809]
def rot (w : ℕ) : ℕ := (2*w)%8192+w/4096
def orbit (w : ℕ) : list ℕ := ((list.range 13).map (λ n, (rot^[n]) w))
def one_loss (w i : ℕ) : list ℕ :=
 ((orbit w).filter (λ n, (n/(2^i))%2=1)).map (λ n,n-2^i)
def columns : list (list ℕ) :=
 reps.bind (λ w,(list.range 13).map (one_loss w))
-- Lean VM performs the integer certificate check independently of Python.
run_cmd do
  let cs := columns,
  guard (cs.length=91),
  guard (cs.all (λ xs,xs.length=5)),
  guard (cs.join.dedup.length=455)

open_locale big_operators
theorem gram_off {ι : Type} (s : finset ι) (x y : ι → ℝ)
 (h : ∀ i∈s, x i=0 ∨ y i=0) : ∑ i in s, x i*y i=0 :=
finset.sum_eq_zero (λ i hi, mul_eq_zero.2 (h i hi))
theorem gram_on {ι : Type} (s : finset ι) (x : ι → ℝ) (h : ∀ i∈s,x i=1 ∨ x i= -1)
 (hn : s.card=5) : ∑ i in s,x i*x i=(5:ℝ) :=
begin
 calc ∑ i in s,x i*x i = ∑ i in s,(1:ℝ) : finset.sum_congr rfl
  (λ i hi,by {rcases h i hi with h|h;rw [h];norm_num})
 ... = 5 : by simp [hn]
end

-- Proper rest mass after retaining the recoil of a single massless particle.
theorem recoil_scale (M y : ℝ) :
 M^2-2*M*(M*y/2)=M^2*(1-y) := by ring
theorem recoil_positive (M y : ℝ) (hm : 0<M) (hy : y<1) :
 0<M*real.sqrt (1-y) := mul_pos hm (real.sqrt_pos.2 (by linarith))
theorem endpoint_coefficients (M : ℝ) :
 M^2/(4*real.pi)*((M/2)^3/3)=M^5/(96*real.pi) ∧
 M^2/(4*real.pi)*((M/2)^4/4)=M^6/(256*real.pi) :=
by {split;field_simp [ne_of_gt real.pi_pos];ring}
-- Substitution z=sqrt(1-y) turns the mean surviving mass into this polynomial integral.
theorem mean_recoil_primitive (z : ℝ) :
 has_deriv_at (λ a:ℝ,2*a^3-12*a^5/5+6*a^7/7) (6*z^2*(1-z^2)^2) z :=
begin
 have h:=(((has_deriv_at_pow 3 z).const_mul 2).sub
   (((has_deriv_at_pow 5 z).const_mul 12).div_const 5)).add
    (((has_deriv_at_pow 7 z).const_mul 6).div_const 7),
 convert h using 1,norm_num;ring
end
theorem mean_recoil :
 ∫ z in (0:ℝ)..1, 6*z^2*(1-z^2)^2 = (16/35:ℝ) :=
begin
 have hc : continuous (λ z:ℝ, 6*z^2*(1-z^2)^2) := by continuity,
 rw [interval_integral.integral_eq_sub_of_has_deriv_at
    (λ z hz,mean_recoil_primitive z) (hc.interval_integrable _ _)],
 norm_num
end
theorem even_terminal_probability (g b m R : ℝ) (hg : 0<g) (hb : 0≤b)
 (hm : 0<m) (hR : m≤R) :
 g/(g+b*R^2)≤(g*m^3)/(g*m^3+b*m^5) :=
begin
 have hm3 : 0<m^3 := pow_pos hm 3,
 have hm5 : 0<m^5 := pow_pos hm 5,
 have h1 : 0<g+b*R^2 := add_pos_of_pos_of_nonneg hg (mul_nonneg hb (sq_nonneg R)),
 have h2 : 0<g*m^3+b*m^5 := add_pos_of_pos_of_nonneg (mul_pos hg hm3) (mul_nonneg hb hm5.le),
 apply (div_le_div_iff h1 h2).2,
 have hsq : 0≤R^2-m^2 := by nlinarith [mul_nonneg (sub_nonneg.2 hR) (show 0≤R+m,by linarith)],
 nlinarith [mul_nonneg (mul_nonneg (mul_pos hg hm3).le hb) hsq]
end
theorem even_survival (a : ℕ → ℝ) (r : ℝ) (hn : 0≤r) (h₁ : r<1)
 (h₀ : ∀ n,0≤a n) (step : ∀ n, a (n+1)≤a n*r) :
 filter.tendsto a filter.at_top (nhds 0) :=
begin
 have bound : ∀ n, a n≤a 0*r^n,
 {intro n,induction n with n h, {simp},
  calc a (n+1) ≤ a n*r : step n
  ... ≤ (a 0*r^n)*r : mul_le_mul_of_nonneg_right h hn
  ... = a 0*r^(n+1) : by {rw [pow_succ],ring}},
 have lim := (tendsto_const_nhds : filter.tendsto (λ n:ℕ,a 0) filter.at_top (nhds (a 0))).mul
   (tendsto_pow_at_top_nhds_0_of_lt_1 hn h₁),
 rw [mul_zero] at lim,exact squeeze_zero h₀ bound lim
end
theorem delay_tail_primitive (x : ℝ) (hx : 0<x) :
 has_deriv_at (λ z:ℝ,-(z^3)⁻¹/3) ((x^4)⁻¹) x :=
begin
 have hn : x≠0 := ne_of_gt hx,
 have h:=(((has_deriv_at_pow 3 x).inv (pow_ne_zero _ hn)).neg).div_const 3,
 convert h using 1,field_simp [hn];ring
end
-- Arbitrarily late odd daughters. In a fixed allowed parent channel the
-- daughter density has a linear factor m from y=1-(m/M)^2.
theorem soft_wait_diverges (B : ℝ) (hB : 0≤B) :
 ∃ a:ℝ,0<a ∧ a≤1 ∧ B<∫ x in a..1,(x^4)⁻¹ :=
begin
 let n:=B+2,
 have h1 : 1<n := by {dsimp [n],linarith},
 have hp : 0<n := by linarith,
 have hn : n≠0 := ne_of_gt hp,
 let a:=n⁻¹,
 have ha : 0<a := inv_pos.2 hp,
 have hal : a≤1, {change n⁻¹≤1,rw [←one_div,div_le_iff hp,one_mul],exact h1.le},
 refine ⟨a,ha,hal,_⟩,
 have hc : continuous_on (λ x:ℝ,(x^4)⁻¹) (set.uIcc a 1),
 {rw [set.uIcc_of_le hal],intros x hx,
  exact ((continuous_at_id.pow 4).inv₀ (pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le ha hx.1)))).continuous_within_at},
 have pos : ∀ (x:ℝ),x∈set.uIcc a 1 → 0<x := by {intros x hx,rw [set.uIcc_of_le hal] at hx,exact lt_of_lt_of_le ha hx.1},
 rw [interval_integral.integral_eq_sub_of_has_deriv_at
  (λ x hx,delay_tail_primitive x (pos x hx))
  (hc.interval_integrable)],
 dsimp [a],rw [inv_pow,inv_inv],norm_num,
 dsimp [n], nlinarith [sq_nonneg B,mul_nonneg hB (sq_nonneg B)]
end
-- For an emitted spinor in the odd-to-even step the map is an identity
-- from both input amplitudes to the outgoing amplitudes. An even origin
-- creates a singlet; the second step moves its remaining spin to the field.
def odd_release (p : ℂ × ℂ) : ℂ × ℂ := (p.1,p.2)
def even_then_odd (z : ℂ) : (ℂ × ℂ) × (ℂ × ℂ) := (odd_release (0,z),odd_release (-z,0))
theorem emitted_singlet (z : ℂ) : even_then_odd z=((0,z),(-z,0)) := rfl
theorem analytic_plateau {p : ℝ → ℝ} {s : set ℝ} {center : ℝ}
 (hana : analytic_on ℝ p s) (hconn : is_preconnected s)
 (hcenter : center∈s) (hbase : (0:ℝ)∈s) (hwrong : p 0≠0) :
 ¬filter.eventually_eq (nhds center) p (λ _,0) :=
begin
 intro flat,
 have hconst : analytic_on ℝ (λ x:ℝ,(0:ℝ)) s := λ x hx,analytic_at_const,
 exact hwrong ((hana.eq_on_of_preconnected_of_eventually_eq hconst hconn hcenter flat) hbase)
end
theorem regularized_rate (N gap : ℝ) (hN : 0≤N) (hg : 0<gap) :
 N^3/(N^2+gap^2) ≤ N :=
begin
 apply (div_le_iff (add_pos_of_nonneg_of_pos (sq_nonneg N) (pow_pos hg 2))).2,
 nlinarith [mul_nonneg hN (sq_nonneg gap)]
end
-- A resolved outgoing helicity has only a rank-one angular port.
theorem angular_rank_one (x y z : ℝ) (h : x^2+y^2+z^2=1) :
 ((1+z)/2)*((1-z)/2)-(x^2+y^2)/4=0 := by nlinarith
theorem angular_second_moment (r m₁ m₂ m₃ : ℝ) (h : m₁=m₂) (k : m₂=m₃)
 (tr : m₁+m₂+m₃=1) : m₁*r=r/3 :=
by {have hm : m₁=1/3 := by linarith,rw [hm],ring}
theorem angular_bell_fidelity : (1+3*(1/3:ℝ))/4=1/2 := by norm_num
end directional_absorption
