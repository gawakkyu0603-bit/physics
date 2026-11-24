import analysis.special_functions.log.basic
import analysis.special_functions.pow.real
import analysis.calculus.deriv.basic
import analysis.calculus.mean_value
import measure_theory.integral.interval_integral
import analysis.special_functions.integrals
import tactic

noncomputable theory
open_locale big_operators
namespace hawking_correlation
-- Spin multiplicities from the SU(2) weights, for any list of permutation cycles.
def wt : list ℤ → ℤ → ℤ
| [] m := if m=0 then 1 else 0
| (l::ls) m := wt ls (m-2*l) + wt ls (m-l) + wt ls m + wt ls (m+l) + wt ls (m+2*l)
def chi (ls : list ℤ) : ℤ := wt ls 0 - wt ls 1
theorem spin_characters :
 [chi [],chi [1],chi [1,1],chi [1,1,1],chi [1,1,1,1],chi [1,1,2],chi [2,2],chi [1,3],chi [4]]
 = [1,0,1,1,5,1,5,-1,1] := dec_trivial

-- Class sizes 1,6,3,8,6. The two [22] copies are the standard action
-- on three pairings modulo the line of constants.
theorem representation_content (triv sign std twist pair : ℤ)
 (ha: triv+sign+3*std+3*twist+2*pair=5)
 (hb: triv-sign+std-twist=1)
 (hc: triv+sign-std-twist+2*pair=5)
 (hd: triv+sign-pair= -1)
 (he: triv-sign-std+twist=1) :
 triv=1 ∧ sign=0 ∧ std=0 ∧ twist=0 ∧ pair=2 := by
 { repeat {split}, all_goals {linarith} }

-- An arbitrary block intertwining two standard S3 modules:
-- commuting with S=[[0,1],[1,0]], T=[[1,0],[-1,-1]] forces a scalar.
theorem block_intertwiner {K : Type*} [field K] (a b c d : K)
 (hab : b=c) (had : a=d) (ht : a-b=a) :
 b=0 ∧ c=0 ∧ d=a := by { have hb : b=0 := by linear_combination -ht, exact ⟨hb,hab ▸ hb,had.symm⟩ }
theorem no_fixed_vector (a b : ℝ) (hs:a=b) (ht: -a-b=b) : a=0 ∧ b=0 := by
 { split;linarith }
theorem no_fixed_covector (a b : ℝ) (hs:a=b) (ht:a-b=a) : a=0 ∧ b=0 := by
 { split;linarith }
theorem swap_block {K : Type*} [ring K] (a b w : K) (h:w*a=b*w) (hinv:w*w=1) :
 w*a*w=b := by rw [h,mul_assoc,hinv,mul_one]

def Z (e : ℝ) := 625+750*e^2+200*e^3+105*e^4
def rs (e : ℝ) := 1+6*e^2+8*e^3+9*e^4
def rm (e : ℝ) := 1-4*e^3+3*e^4
theorem class_trace (e : ℝ) :
 5^4+6*5^3*e^2+3*5^2*e^4+8*5^2*e^3+6*5*e^4=Z e := by unfold Z;ring
theorem mixed_eigenvalue (e : ℝ) :
 (2+3*2*e^4-8*e^3)/2=rm e := by unfold rm;ring
theorem gap (e : ℝ) : rs e-rm e=6*e^2*(1+e)^2 := by unfold rs rm;ring
theorem mixed_zero (e : ℝ) : rm e=(1-e)^2*(1+2*e+3*e^2) := by unfold rm;ring
theorem singlet_mass (e : ℝ) :
 rs e+4*rm e=5+6*e^2-8*e^3+21*e^4 := by unfold rm rs;ring
theorem endpoints :
 (rs 0+4*rm 0)/Z 0=1/125 ∧ 4*rm 0/Z 0=4/625 ∧
 (rs 1+4*rm 1)/Z 1=1/70 ∧ 4*rm 1/Z 1=0 :=
 by norm_num [rs,rm,Z]
theorem matched_optimum {ι : Type*} (p d : ℝ) (hd:0<d) (r : ι → ℝ) :
 (∀ i, 0≤r i-p/d) ↔ (∀ i,p≤d*r i) :=
begin
 split; intros h i; specialize h i,
 { have := (div_le_iff hd).mp (show p/d≤r i, by linarith), nlinarith },
 { have := (div_le_iff hd).mpr (show p≤r i*d,by nlinarith),linarith }
end
theorem attaining_minimum {ι : Type*} (r : ι → ℝ) (j : ι) (h:∀ i,r j≤r i) (d : ℝ)
 (hd:0<d) : (∀ i,0≤r i-(d*r j)/d) ∧ (∀ p,(∀ i,p≤d*r i) → p≤d*r j) :=
begin split, { rw [matched_optimum _ _ hd],intro i,exact mul_le_mul_of_nonneg_left (h i) hd.le },
 { intros p hp,exact hp j } end
theorem exchange_complete {K : Type*} [ring K] (f : K) (h:f*f=f) :
 (1-f)*(1-f)+f*f=1 := by {simp only [sub_mul,mul_sub,one_mul,mul_one,h],abel}
theorem mismatch (purity : ℝ) (h:purity≤1) : 0≤(1-purity)/2 := by linarith
theorem affine_counterexample : ((1-(1:ℝ))/2+(1-1)/2)/2 ≠ (1-1/2)/2 := by norm_num
theorem branch_partner : 1-(1:ℝ)/25=24/25 := by norm_num
theorem six_partial_trace_trace (a v : ℝ) : (25*a+5*a*v)-(5*a+25*a*v)=20*a*(1-v) := by ring
theorem six_pair_prob (v : ℝ) (hv:0≤v) :
 (25+5*v-(5+25*v))/(2*(25+5*v))=2*(1-v)/(5+v) :=
begin have h1:25+5*v≠0 := by linarith,have h2:5+v≠0 := by linarith,field_simp;ring end
theorem six_separated : (2:ℚ)/5*(4/625)=8/3125 := by norm_num
theorem radial_redshift (y : ℝ) (h:y≠1) :
 (y^2+y+1+1/(y-1))*(y-1)=y^3 :=
begin have hz:y-1≠0 := sub_ne_zero.mpr h,field_simp [hz];ring end
theorem recoupling_echo : ((1:ℚ)^2+3^2+5^2+7^2+9^2)/25^2=33/125 := by norm_num
theorem area_fraction (n e g deltaM2 power area pi0 : ℝ) (he:0<e) (hn:0<n)
 (hg:0≤g) (hm:0≤deltaM2) (hp:2*e≤power) (hc:0<pi0)
 (ha:area=4*pi0*g*deltaM2) :
 2*g*n*deltaM2/power≤area/(4*pi0*(e/n)) :=
begin
 have hpower : 0<power := by linarith,
 have hden : 0<4*pi0*(e/n) := by positivity,
 rw [div_le_div_iff hpower hden,ha],
 calc 2*g*n*deltaM2*(4*pi0*(e/n)) = (4*pi0*g*deltaM2)*(2*e) : by field_simp [ne_of_gt hn];ring
 ... ≤ _ : mul_le_mul_of_nonneg_left hp (by positivity)
end
-- Measured energy and spin are identical at a degenerate exchange vertex.
theorem energy_exchange (e q r m : ℝ) (h:e+q=r+m) : e-r=m-q := by linarith

-- Terms of the Bell projector on each side of rho tensor sigma after partial trace.
theorem left_bell_trace {ι : Type*} [fintype ι] [decidable_eq ι] (x y : ι → ι → ℂ)
 (m n : ι) :
 (∑ a : ι, if a=m then ∑ u : ι, ∑ v : ι, if v=u then x u a*y v n else 0 else 0)
   = ∑ u : ι, x u m*y u n := by simp
theorem bell_sandwich_trace {ι : Type*} [fintype ι] [decidable_eq ι] (x y : ι → ι → ℂ)
 (m n : ι) :
 (∑ a : ι, if a=m then (if a=n then ∑ u : ι, ∑ v : ι, if v=u then
       ∑ k : ι, ∑ l : ι, if l=k then x u k*y v l else 0 else 0 else 0) else 0)
   = (if m=n then ∑ u : ι, ∑ k : ι, x u k*y u k else 0) := by simp
theorem scalar_mark_normalization (q d : ℝ) : (1-q*d)+q*d=1 := by ring
theorem dark_bound (b : ℝ) (h:4*b≤1) : b≤1/4 := by linarith
theorem dark_phase (a b x y : ℝ) (h:a= -b) :
 (a+x*b)^2+(y*b)^2=b^2*((1-x)^2+y^2) := by rw [h];ring
theorem dark_bright_loss (x y : ℝ) :
 ((1-x)^2+y^2)/4+((1+x)^2+y^2)/4+(1-x^2-y^2)/2=1 := by ring
theorem same_packet_control (d : ℝ) (hd:0≤d) : 4*(1/4)*(1-d/2)/25 < 1/24 :=
begin have h : 4*(1/4)*(1-d/2)/25=(2-d)/50 := by ring,rw [h,div_lt_iff (show (0:ℝ)<50,by norm_num)],linarith end
def transfer (q d : ℝ) := (4*q+2*d*q*(1-2*q))/25
theorem phase_factor (q d : ℝ) :
 2*(1-(1-d*q)*(1-2*q))/25=transfer q d := by unfold transfer;ring
theorem normalized_choi (t : ℝ) : ((1+t)/25-t < 0) ↔ 1/24<t := by split;intro h;linarith
theorem quarter_width (d : ℝ) : 1/24 < transfer (1/4) d ↔ 1/6 < d :=
begin
 have hh: transfer (1/4) d=(d+4)/100 := by unfold transfer;ring,
 rw [hh,lt_div_iff (show (0:ℝ)<100,by norm_num)],split;intro h;linarith
end
theorem visibility_condition (v : ℝ) (hv : 0≤v) : 1/6 < 2*(1-v)/(5+v) ↔ v<7/13 :=
begin have hz:0<5+v := by linarith,rw [lt_div_iff hz],split;intro h;linarith end
theorem loss_threshold (b d : ℝ) (hb:0<b) :
 1/24 < (1+d*b/4)/(24+b) ↔ 1/6<d :=
begin
 rw [lt_div_iff (show 0<24+b,by linarith)],
 split,
 { intro h,by_contra hh,push_neg at hh,nlinarith [mul_le_mul_of_nonneg_right hh hb.le] },
 { intro h,nlinarith [mul_lt_mul_of_pos_right h hb] }
end
theorem nonuniform_minor (x y a b : ℝ) (h:0<x) (hz:a≠0 ∨ b≠0) :
 0*y-(a^2+b^2)*x^2/625<0 :=
begin
 have hp : 0<a^2+b^2,
 { cases hz with u v,
   { nlinarith [sq_pos_of_ne_zero _ u,sq_nonneg b] },
   { nlinarith [sq_pos_of_ne_zero _ v,sq_nonneg a] } },
 have ht := mul_pos hp (sq_pos_of_ne_zero _ (ne_of_gt h)), linarith
end
theorem line_primitive (x : ℝ) :
 has_deriv_at (λ y:ℝ,-y/(1+y^2)) ((1/(1+x^2))*(1-2/(1+x^2))) x :=
begin
 have hne:1+x^2≠0 := by positivity,
 have H := (has_deriv_at_id x).neg.div (((has_deriv_at_id x).pow 2).const_add 1) hne,
 convert H using 1; dsimp;field_simp [hne];ring
end
section integrals
open_locale interval
theorem line_integral (Y : ℝ) :
 (∫ x in (-Y)..Y, (1/(1+x^2))*(1-2/(1+x^2))) = -2*Y/(1+Y^2) :=
begin
 have hz:∀ x:ℝ,1+x^2≠0 := λ x,by positivity,
 have hc : continuous (λ x:ℝ, (1/(1+x^2))*(1-2/(1+x^2))) :=
  (continuous_const.div (continuous_const.add (continuous_id.pow 2)) hz).mul
  (continuous_const.sub (continuous_const.div (continuous_const.add (continuous_id.pow 2)) hz)),
 calc (∫ x in (-Y)..Y, (1/(1+x^2))*(1-2/(1+x^2))) =
    -Y/(1+Y^2)- -(-Y)/(1+(-Y)^2) :
  interval_integral.integral_eq_sub_of_has_deriv_at (λ x hx,line_primitive x) (hc.interval_integrable _ _)
 ... = _ : by rw [neg_sq];ring
end
end integrals
theorem beam_det_factor (A r y H : ℝ) :
 (A+5*r)^2-(25*r^2+(r^2+y^2)*(H-25))=
    A^2+10*A*r-(r^2+y^2)*(H-25) := by ring
theorem beam_matched_threshold (b H : ℝ) (hb:0<b) :
 (5+b/5)^2-5*(5+b/5)-b*(H-25)<0 ↔ 26+b/25<H :=
begin
 have h:(5+b/5)^2-5*(5+b/5)-b*(H-25)=b*(26+b/25-H) := by ring,
 rw [h],split,
 { intro ha,by_contra hh,push_neg at hh,exact (not_lt_of_ge (mul_nonneg hb.le (sub_nonneg.mpr hh))) ha },
 { intro ha,exact mul_neg_of_pos_of_neg hb (sub_neg.mpr ha) }
end
theorem kk_loss_bound (b : ℝ) (hb:0≤b) (ht:b≤1/6) :
 (4*b+2*b^2)/(25-4*b) < 1/24 :=
begin
 have hh:0<25-4*b := by linarith,
 rw [div_lt_iff hh],
 nlinarith [mul_nonneg (sub_nonneg.mpr ht) (add_nonneg hb (show (0:ℝ)≤1/6,by norm_num))]
end
theorem narrow_weight (b q : ℝ) : b^2*q*(1-4*b*(1-b)*q/25)=
 b^2*q-4*b^3*(1-b)*q^2/25 := by ring
theorem stable_gap (mu alpha : ℝ) : (3:ℝ)/2*(mu*alpha^4)/405=mu*alpha^4/270 := by ring

-- Laplace expansion with total access; valid here on the displayed square matrices.
def d3 (a b c d e f g h i : ℤ) := a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)
def d4 (a b c d e f g h i j k l m n o p : ℤ) :=
 a*d3 f g h j k l n o p-b*d3 e g h i k l m o p+c*d3 e f h i j l m n p-d*d3 e f g i j k m n o
def lifted_minor : ℤ :=
 46*d4 32 32 13 67 70 70 66 77 30 46 30 29 7 9 35 31
 - 58*d4 21 32 13 67 76 70 66 77 3 46 30 29 8 9 35 31
 + 58*d4 21 32 13 67 76 70 66 77 3 30 30 29 8 7 35 31
 - 83*d4 21 32 32 67 76 70 70 77 3 30 46 29 8 7 9 31
 + 16*d4 21 32 32 13 76 70 70 66 3 30 46 30 8 7 9 35
theorem modular_minor : lifted_minor % 101=97 := by norm_num [lifted_minor,d4,d3]
theorem nonzero_lift (d : ℤ) (h:d%101=97) : d≠0 := by { intro hz,rw [hz] at h,norm_num at h }
theorem passive_port_unit (r x y : ℝ) (hw:x^2+y^2=1) :
 (r+x)^2+y^2=(1+r*x)^2+(r*y)^2 :=
begin nlinarith [congr_arg (λ a:ℝ,r^2*a) hw] end
theorem port_weight (r k : ℝ) (n : ℕ) :
 (1-k) + (∑ j in finset.range n, k*(1-r^2)*(r^2)^j) = 1-k*(r^2)^n :=
begin induction n with n ih, {simp}, {rw [finset.sum_range_succ,←add_assoc,ih,pow_succ (r^2) n],ring} end
theorem two_port_threshold :
 (((1:ℝ)-1/2)^2+(1/2)^2)/4=1/8 ∧ ((1:ℝ)-(1/2)^2-(1/2)^2)=1/2 := by norm_num

-- Independent finite oscillator calculation. B_ab=3 e_a e_b^T - delta_ab I.
-- Its matrix product is evaluated in Cartesian coordinates without CG coefficients.
-- Fock monomials are unnormalized, so lowering carries occupation n.
def axes : list ℕ := [0,1,2]
def coord_terms : list (ℕ × ℕ) := axes.bind (λ a,axes.map (λ b,(a,b)))
def belem (a : ℕ × ℕ) (i j : ℕ) : ℤ :=
 (if a.1=i ∧ a.2=j then 3 else 0) - (if a.1=a.2 ∧ i=j then 1 else 0)
def prod_elem (a b : ℕ × ℕ) (i j : ℕ) : ℤ :=
 belem a i 0*belem b 0 j + belem a i 1*belem b 1 j + belem a i 2*belem b 2 j
def tr2 (a b : ℕ × ℕ) : ℤ := prod_elem a b 0 0+prod_elem a b 1 1+prod_elem a b 2 2
def tr4 (a b c d : ℕ × ℕ) : ℤ :=
 (coord_terms.map (λ (p : ℕ × ℕ),prod_elem a b p.1 p.2*prod_elem c d p.2 p.1)).sum
def phase_slots (axis : ℕ) (p ph : ℕ × ℕ) : list (ℕ × ℕ) :=
 (if p.1=axis then [ph] else []) ++ (if p.2=axis then [ph] else [])
def hop : list (ℕ × ℕ) → ℕ → ℕ → ℤ
| [] n f := if n=f then 1 else 0
| (p::ps) n f := (p.1:ℤ)*hop ps (n+1) f +
 (if n=0 then 0 else (n:ℤ)*(p.2:ℤ)*hop ps (n-1) f)
def path_one (axis n f : ℕ) (a b c d : ℕ × ℕ) : ℤ :=
 let slots := phase_slots axis a (1,1) ++ phase_slots axis b (49,33) ++
              phase_slots axis c (10,91) ++ phase_slots axis d (68,52) in
 if (n+slots.length)%2=f%2 then (hop slots n f)%101 else 0
def trial_rows := list (list ℤ)
def terms4 : list ((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) :=
 coord_terms.bind (λ a,coord_terms.bind (λ b,coord_terms.bind
    (λ c,coord_terms.map (λ d,(a,b,c,d)))))
def add_cartesian (tot : trial_rows)
 (w : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) : trial_rows :=
 let a := w.1, b := w.2.1, c := w.2.2.1, d := w.2.2.2,
 y := path_one 1 0 0 a b c d in
 if y=0 then tot else
 let vac := path_one 0 0 0 a b c d*y, one := path_one 0 1 1 a b c d*y,
 z0 := path_one 2 0 0 a b c d, z2 := path_one 2 0 2 a b c d, z4 := path_one 2 0 4 a b c d,
 amps := [vac*z0,vac*z2,vac*z4,one*z0,one*z2],
 cs := [tr2 a b*tr2 c d,tr2 a c*tr2 b d,tr2 a d*tr2 b c,tr4 a b c d,tr4 a c b d] in
 list.zip_with (λ row amp,list.zip_with (λ (old coef : ℤ),(old+amp*coef)%101) row cs) tot amps
def fock_rows : trial_rows := terms4.foldl add_cartesian (list.repeat (list.repeat (0:ℤ) 5) 5)
def expected_rows : trial_rows :=
 [[46,58,58,83,16],[21,32,32,13,67],[76,70,70,66,77],[3,30,46,30,29],[8,7,9,35,31]]
run_cmd if fock_rows=expected_rows then tactic.skip else tactic.fail "independent Fock contraction failed"
end hawking_correlation
