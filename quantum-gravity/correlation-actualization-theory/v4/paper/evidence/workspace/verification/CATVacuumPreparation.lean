import tactic
import analysis.special_functions.integrals
import algebra.big_operators.order
import data.real.sqrt

/- Dimensionless identities for the material-clock sector. The ordinary external
   metric, the harmonic fast sector and the single incident mode are hypotheses. -/
namespace cat_vacuum_preparation
noncomputable theory
open_locale big_operators
open finset

theorem schur_test (du dv coupling : ℝ) (hu : 0<du) (hv : 0<dv)
 (h : coupling^2<du*dv) : coupling^2/dv<du :=
(div_lt_iff hv).mpr h
theorem separated_product (R L a b : ℝ) (h1 : L≤a) (h2 : L≤b) (hL : 0≤L)
 (hR : R≤a+b) : L*(R-L)≤a*b :=
by nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2),
              mul_nonneg hL (sub_nonneg.mpr hR)]
theorem gram_trace_bound (b c : ℝ) : (b+c)^2≤2*(b^2+c^2) :=
by nlinarith [sq_nonneg (b-c)]
theorem transverse_gap {R : Type*} [ring R] (a b : R) (h : a*b= -(b*a)) :
 (a+b)*(a+b) = a*a+b*b :=
by {rw [add_mul,mul_add,mul_add,h], abel}
theorem axis_band (x s w : ℝ) (hw : 0≤w) :
 (x-s)^2<w^2 ↔ s-w<x ∧ x<s+w :=
begin
 have hn := abs_nonneg (x-s),
 split,
 { intro he, have : abs (x-s)<w,
   { by_contra c, push_neg at c,
     have hc := mul_self_le_mul_self hw c,
     rw [←pow_two,←pow_two,sq_abs] at hc, linarith },
   rcases abs_lt.mp this with ⟨ha,hb⟩, constructor; linarith },
 { rintro ⟨ha,hb⟩, have he : abs (x-s)<w := abs_lt.mpr ⟨by linarith,by linarith⟩,
   have hn' : 0<w-abs (x-s) := by linarith,
   have hp : 0<w+abs (x-s) := by linarith,
   have hm := mul_pos hn' hp, nlinarith [sq_abs (x-s)] }
end
theorem axial_singulars (u v : ℝ) :
 ((u+v)+(u-v))^2 = 4*u^2 ∧ ((u+v)-(u-v))^2 = 4*v^2 :=
by constructor; ring
theorem oscillator_variance (g R : ℝ) (hg : g≠0) (hR : R≠0) :
 1/(2*(2/g)*R) = g/(4*R) := by {field_simp [hg,hR]; ring}
theorem shape_gate (s x v : ℝ) (hs : 0<s) :
 abs (x/s-1)<v ↔ abs (x-s)<v*s :=
begin
 rw [show x/s-1=(x-s)/s, by {field_simp [ne_of_gt hs]}],
 rw [abs_div,abs_of_pos hs,div_lt_iff hs]
end
theorem harmonic_tide (k : ℝ) : 1/4-k*(1-k)=(k-1/2)^2 := by ring
theorem bessel_reduction (p q m : ℝ) (h : m^2*(1+p)^2=1/4-q) :
 (q-1/4)+m^2*(1+p)^2=0 := by linarith
theorem dust_orders : ((1:ℝ)/10)^2*(1+2/3)^2=1/4-2/9 ∧
 ((3:ℝ)/10)^2*(1+2/3)^2=1/4 := by norm_num
theorem kasner_growth_ratio (u : ℝ) (hu : 1≤u) :
 (2*(u/(1+u+u^2))-(1+u)/(1+u+u^2))/(1+(1+u)/(1+u+u^2))
 =(u-1)/(u^2+2*u+2) :=
begin
 have h1 : 0<1+u+u^2 := by nlinarith [sq_nonneg u],
 have h2 : 0<u^2+2*u+2 := by nlinarith [sq_nonneg u],
 have h3 : 1+(1+u)/(1+u+u^2)≠0 := ne_of_gt (by positivity),
 apply (div_eq_iff h3).mpr,
 field_simp [ne_of_gt h1,ne_of_gt h2]; ring
end
theorem kasner_optimum (u s : ℝ) (hs : s^2=5) (hpos : 2<s) :
 2*(u-1) ≤ (s-2)*(u^2+2*u+2) :=
begin
 have he : (s-2)*(u^2+2*u+2)-2*(u-1)=(s-2)*(u-1-s)^2 :=
  by linear_combination (2*u-s)*(hs),
 nlinarith [mul_nonneg (sub_nonneg.mpr hpos.le) (sq_nonneg (u-1-s))]
end
theorem nicolson_weight (w a b : ℝ) (hw : 0≤w) (h : a≤b) : w*a≤w*b :=
mul_le_mul_of_nonneg_left h hw

theorem pair_charge (x1 x2 y1 y2 : ℝ) :
 ((x1-y2)^2+(y1+x2)^2)*((x1+y2)^2+(y1-x2)^2)
  = (x1^2-y1^2+x2^2-y2^2)^2+(2*(x1*y1+x2*y2))^2 := by ring
theorem same_bin (p : ℝ) : 1-(p^2+(1-p)^2)=2*p*(1-p) := by ring
theorem single_port_half (p : ℝ) : 2*p*(1-p)≤1/2 :=
by { have h : 1/2-2*p*(1-p)=2*(p-1/2)^2 := by ring,
     linarith only [h,sq_nonneg (p-1/2)] }
theorem shared_ports {k : Type*} [fintype k] (p : k → ℝ) (b : ℝ)
 (h : ∑ i, p i=1) (hn : (fintype.card k:ℝ)*b=1) :
 1-∑ i, (p i)^2 ≤ 1-b :=
begin
 have hs : 0≤∑ i, (p i-b)^2 := finset.sum_nonneg (λ i hi, sq_nonneg _),
 have hi : ∑ i, (p i-b)^2 = ∑ i, (p i)^2-2*b*∑ i, p i+(fintype.card k:ℝ)*b^2,
 { simp only [sub_sq, finset.sum_add_distrib,finset.sum_sub_distrib,
              finset.sum_const,finset.card_univ,nsmul_eq_mul,finset.mul_sum],
   congr' 1, congr' 1, apply finset.sum_congr rfl, intros i hi, ring },
 rw [hi,h,show (fintype.card k:ℝ)*b^2=((fintype.card k:ℝ)*b)*b,by ring,hn] at hs,
 linarith
end
theorem gamma_gate (j d k : ℕ) (hit : k<d+2*j) : k+1≤d+2*j := hit
theorem parity_envelope (k d j : ℕ) (t : ℝ) (ht : 0≤t) (hu : t≤1)
 (h : k+1≤d+2*j) : t^d*(t^j)^2≤t^(k+1) :=
begin
 rw [←pow_mul,←pow_add,show j*2=2*j,by omega],
 exact pow_le_pow_of_le_one ht hu h
end
theorem positive_comparison (z w j : ℝ) :
 j*z^2+(j+1)*w^2=(j+1)*(z^2+w^2)-z^2 := by ring
theorem euclidean_chain (j t : ℝ) :
 t^2+(j*(1+t^2))=j+(j+1)*t^2 := by ring
theorem probability_cut (small large mass prob upper markov : ℝ)
 (hs : small≤mass*upper) (hl : large≤markov) (ht : prob≤small+large) :
 prob≤mass*upper+markov := by linarith
theorem mean_count (x threshold tail : ℝ) (hT : 0<threshold)
 (h : tail*threshold≤x) : tail≤x/threshold := (le_div_iff hT).mpr h
theorem dust_budget (g rho gw u f : ℝ) (gu : 6*g*rho*u^2=1)
 (hf : gw≤f*rho) (hg : 0≤g) :
 4*g*gw*u^2 ≤ 2*f/3 :=
begin
 have hm := mul_le_mul_of_nonneg_left hf (mul_nonneg hg (sq_nonneg u)),
 have he : g*u^2*(f*rho)=f/6 := by linear_combination (f/6)*gu,
 nlinarith
end
theorem two_colour_squeeze (U V Y z : ℝ) :
 (2*(2*z-U))^2 < 4*(V^2+2*Y) ↔ (2*z-U)^2<V^2+2*Y :=
by split; intro h; nlinarith
theorem independent_pump_charge_moment (a b : ℝ) : (a+1)*b-a*b=b := by ring

theorem controlled_matching {R : Type*} [ring R] (P U V : R)
 (hP : P*P=P) (hUV : U*V=1) (hVU : V*U=1) :
 ((1-P)+V*P)*((1-P)+P*U)=1 ↔ P*U=U*P :=
begin
 have hc : ((1-P)+V*P)*((1-P)+P*U)=1-P+V*P*U :=
  calc ((1-P)+V*P)*((1-P)+P*U)=1-P+(P*P-P)+(P-P*P)*U+V*(P-P*P)+V*(P*P)*U :
        by noncomm_ring
   ... = 1-P+V*P*U : by simp [hP],
 rw [hc], split,
 { intro h, have hh : V*P*U=P := calc
     V*P*U = (1-P+V*P*U)-(1-P) : by abel
     ... = P : by {rw [h],abel},
   calc P*U = U*(V*P*U) : by {rw [←mul_assoc,←mul_assoc,hUV,one_mul]}
   ... = U*P : by rw [hh] },
 { intro h, have hh : V*P*U=P := by rw [mul_assoc,h,←mul_assoc,hVU,one_mul],
   rw [hh], abel }
end
theorem bessel_residual (m z nu q h h' h'' : ℝ)
  (hode : z^2*h''+z*h'+(z^2-nu^2)*h=0)
  (horder : m^2*nu^2=1/4-q) :
  m^2*z^2*h''+m^2*z*h'+(m^2*z^2+q-1/4)*h=0 :=
by linear_combination m^2*hode+h*horder

theorem cluster_gap_cost (gap split energy g : ℝ)
 (hg : 0<g) (h : gap^2*split^2 ≤ 4*g*energy) :
 gap^2*split^2/(4*g) ≤ energy := (div_le_iff (by positivity)).mpr (by linarith)

theorem pair_budget {ι : Type*} [fintype ι] (gap weight cost : ι→ℝ)
 (h : ∀ i, cost i ≤ (gap i)^2*weight i) :
 (∑ i, cost i) ≤ ∑ i, (gap i)^2*weight i :=
finset.sum_le_sum (λ i hi, h i)

theorem arrow_completion {ι : Type*} [fintype ι] (a w x : ι→ℝ) (c y : ℝ)
 (ha : ∀ i, a i≠0) :
 (∑ i, (-(a i)*(x i)^2+2*w i*x i*y))-c*y^2 =
 (∑ i, -(a i)*(x i-w i*y/a i)^2)+((∑ i, (w i)^2/a i)-c)*y^2 :=
begin
 have he : ∀ i, -(a i)*(x i)^2+2*w i*x i*y =
  -(a i)*(x i-w i*y/a i)^2+((w i)^2/a i)*y^2,
 { intro i, field_simp [ha i]; ring },
 simp_rw [he], rw [finset.sum_add_distrib,←finset.sum_mul], ring
end

theorem collective_witness : (4:ℝ)/2<3 ∧ (4:ℝ)/3<3 ∧ 3<(4:ℝ)/2+4/3 := by norm_num
theorem oriented_chance (p : ℝ) : p*(1-p)≤1/4 :=
by {have he : 1/4-p*(1-p)=(p-1/2)^2 := by ring, linarith only [he,sq_nonneg (p-1/2)]}

-- Conditional on the first recorded history, the two second-charge
-- probabilities are diagonal effects in the signed angular-momentum code.
theorem second_record_contrast (x y b : ℝ) (h : 0≤b) :
 abs (b*x/2-b*y/2)+abs (((1-b)*x+y)/2-((1-b)*y+x)/2)=b*abs(x-y) :=
begin
 have h1 : b*x/2-b*y/2 = (b/2)*(x-y) := by ring,
 have h2 : ((1-b)*x+y)/2-((1-b)*y+x)/2 = -((b/2)*(x-y)) := by ring,
 rw [h1,h2,abs_neg,abs_mul,abs_of_nonneg (show 0≤b/2,by linarith)], ring
end
theorem two_record_distance {ι : Type*} [fintype ι] (x y : ι→ℝ) (b : ℝ) (hb : 0≤b) :
 (∑ i, (abs (b*x i/2-b*y i/2)+abs (((1-b)*x i+y i)/2-((1-b)*y i+x i)/2)))/2
 = b*((∑ i, abs(x i-y i))/2) :=
by {simp_rw [second_record_contrast _ _ _ hb], rw [←finset.mul_sum], ring}
theorem charge_alone {ι : Type*} [fintype ι] (p : ι→ℝ) (b : ℝ) (hp : ∑ i, p i=1) :
 (∑ i, b*p i/2)=b/2 :=
begin
 have he : ∀ i, b*p i/2=(b/2)*p i := λ i, by ring,
 simp_rw [he], rw [←finset.mul_sum,hp,mul_one]
end
theorem efficient_history_fidelity {ι : Type*} [fintype ι] (s t : ι→ℝ)
 (hs : ∑ i, (s i)^2=1) (ht : ∑ i, (t i)^2=1) :
 (∑ i, (s i+t i)^2)/4=(1+(∑ i, s i*t i))/2 :=
begin
 have he : ∀ i, (s i+t i)^2=(s i)^2+(t i)^2+2*(s i*t i) := λ i, by ring,
 simp_rw [he], rw [finset.sum_add_distrib,finset.sum_add_distrib,←finset.mul_sum,hs,ht], ring
end

-- The spin doublet compression of sin²(x C). The two M=0 transitions
-- involve the same symmetric magnetic vector; its cross term has weight d.
def rotor_tensor (a d : ℂ) (i k j l : bool) : ℂ :=
 if i=j then (if k=l then (if i=k then a else d) else 0)
 else (if k=j ∧ l=i then d else 0)
def reduce_receiver (t : bool→bool→bool→bool→ℂ) (r : bool→bool→ℂ) (i j : bool) : ℂ :=
 t i ff j ff*r ff ff+t i ff j tt*r tt ff+t i tt j ff*r ff tt+t i tt j tt*r tt tt
theorem rotor_full_effect (a d : ℂ) (r : bool→bool→ℂ) (i j : bool) :
 reduce_receiver (rotor_tensor a d) r i j =
 if i=j then a*r i i+d*r (bnot i) (bnot i) else d*r i j :=
by {cases i; cases j; simp [reduce_receiver,rotor_tensor,bnot,add_comm]}

theorem phase_eigenvalues (a d : ℝ) :
 (a+d)/2+d/2=a/2+d ∧ (a+d)/2-d/2=a/2 := by constructor; ring
theorem phase_fidelity (x y : ℝ) (hx : x^2+y^2=1) (u v : ℝ) (hu : u^2+v^2=1) :
 ((x+u)^2+(y+v)^2)/4=(1+x*u+y*v)/2 := by linear_combination hx/4+hu/4
theorem bright_first (b1 b2 : ℝ) (h1 : 0≤b1) :
 (b2/2)*(abs (b1-0)+abs ((1-b1)-1))=b1*b2 :=
by {rw [sub_zero,show (1-b1)-1= -b1,by ring,abs_neg,abs_of_nonneg h1],ring}
theorem sorted_pair_contrast (a d : ℝ) :
 (abs (a/2-d/2)+abs ((1-a)/2-(1-d)/2)+abs (d/2-a/2)+abs ((1-d)/2-(1-a)/2))/2
 = abs(a-d) :=
begin
 have ha : a/2-d/2=(a-d)/2 := by ring,
 have hb : (1-a)/2-(1-d)/2= -((a-d)/2) := by ring,
 have hc : d/2-a/2= -((a-d)/2) := by ring,
 have hd : (1-d)/2-(1-a)/2=(a-d)/2 := by ring,
 rw [ha,hb,hc,hd,abs_neg,abs_div,abs_of_nonneg (show (0:ℝ)≤2,by norm_num)], ring
end
theorem sorted_balanced_fidelity (p : ℝ) (hp : 0≤p) (hu : p≤1) :
 (1+real.sqrt (p*p)+real.sqrt ((1-p)*(1-p)))/2=1 :=
by {rw [real.sqrt_mul_self hp,real.sqrt_mul_self (sub_nonneg.mpr hu)],ring}
theorem coherent_balanced_loss (p u v r s : ℝ) (hp : p>0)
 (h : u^2=3*p/2) (k : v^2=p/2) (hu : u^2+r^2=1) (hv : v^2+s^2=1) :
 (1+u*v+r*s)/2<1 :=
begin
 have hd : u≠v := λ e, by {rw [e] at h, linarith},
 have hn : 0<(u-v)^2 := sq_pos_of_ne_zero (u-v) (sub_ne_zero.mpr hd),
 have he : (u-v)^2+(r-s)^2=2-2*(u*v+r*s) := by linear_combination hu+hv,
 linarith only [he,hn,sq_nonneg (r-s)]
end
theorem restore_recorded_sectors {R : Type*} [ring R] (u v q p m : R)
 (hvu : v*u=1) (hp : q*(u*p)=u*p) (hm : q*(u*m)=0) :
 v*(q*(u*(p+m)))=p ∧ v*((1-q)*(u*(p+m)))=m :=
begin
 have vp : v*(u*p)=p := by rw [←mul_assoc,hvu,one_mul],
 have vm : v*(u*m)=m := by rw [←mul_assoc,hvu,one_mul],
 constructor,
 { rw [mul_add u,mul_add q,hp,hm,add_zero,vp] },
 { rw [sub_mul,one_mul,mul_add u,mul_add q,hp,hm,add_zero],
   have ht : u*p+u*m-u*p=u*m := by abel, rw [ht,vm] }
end
end cat_vacuum_preparation
