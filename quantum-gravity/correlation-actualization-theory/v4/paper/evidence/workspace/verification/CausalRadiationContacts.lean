import analysis.special_functions.exp_deriv
import analysis.calculus.deriv.mul
import measure_theory.integral.bochner
import data.complex.basic
import tactic

noncomputable theory
open measure_theory
open_locale big_operators
namespace causal_receipts

-- Annihilators commute with other annihilators. Adjoints are applied only after this identity.
theorem exterior_pair {R : Type*} [comm_ring R] (a b c d u v U V : R) :
 (a*u+b*v)*(c*U+d*V)-(a*U+b*V)*(c*u+d*v)=(a*d-b*c)*(u*V-U*v) := by ring

theorem compose_det {R : Type*} [comm_ring R] (a b c d e f g h : R) :
 (a*e+b*g)*(c*f+d*h)-(a*f+b*h)*(c*e+d*g)=(a*d-b*c)*(e*h-f*g) := by ring

theorem square_norm_survival (D w : ℂ) :
 complex.norm_sq (D*w) = complex.norm_sq D * complex.norm_sq w := complex.norm_sq_mul D w

-- This single homogeneous identity also applies inside arbitrary normally ordered states.
theorem wedge_sum {ι : Type*} (slots : finset ι) (a : ι → ℝ) (D : ℝ) :
 (∑ i in slots, D*a i) = D*(∑ i in slots, a i) := (finset.mul_sum.symm)

-- Unitary invariant survival reduced to singular values. Calibration permits zero singular values.
theorem born_character {S : Type*} [monoid S] (p : S → ℝ) (diag : ℝ → S) (u v l r : S)
 (x y : ℝ) (hu : p u=1) (hv : p v=1) (hc : ∀ a, p (diag a)=a^2)
 (hl : p l=1) (hr : p r=1) (comp : ∀ a b, p (a*b)=p a*p b) :
 p (u*(diag x)*(l*(diag y)*r)*v)=(x*y)^2 :=
by simp only [comp,hu,hv,hl,hr,hc,one_mul,mul_one];ring

theorem serial_erasure (s t : ℝ) :
 1-s*t=(1-s)+s*(1-t) := by ring

theorem trace_generator {R : Type*} [comm_ring R] (A B C D a b c d : R) :
 (A*a+B*c)*d+a*(C*b+D*d)-(A*b+B*d)*c-b*(C*a+D*c)=(A+D)*(a*d-b*c) := by ring

theorem norm_decay (z w dz dw k h : ℝ) (e1 : dz= -k*z/2-h*w) (e2 : dw= h*z-k*w/2) :
 2*z*dz+2*w*dw= -k*(z^2+w^2) := by rw [e1,e2];ring

theorem survival_law (k t : ℝ) :
 has_deriv_at (λ s : ℝ, real.exp (-k*s)) (-k*real.exp (-k*t)) t :=
begin
 have h := ((has_deriv_at_id t).const_mul (-k)).exp,
 convert h using 1; simp [mul_comm],
end

theorem darbouxfactors (f w t r : ℂ) (h : f-w≠0) :
 (f-w)*t/(f-w)=t ∧ ((f+w)*r/(f-w)-r)/2=(w*r)/(f-w) :=
begin
 split,
 { field_simp,ring },
 { field_simp [h],ring }, 
end

theorem dark_probability (a b w : ℝ) (h : a^2+w^2≠0) :
 (b^2*a^2)/(a^2+w^2)+(w^2+(1-b^2)*a^2)/(a^2+w^2)=1 :=
by field_simp;ring

theorem halfwave_norm (k x : ℝ) (h : k^2+x^2≠0) :
 (x^4+(k*x)^2)/(k^2+x^2)^2=x^2/(k^2+x^2) := by field_simp;ring

theorem angular_tail (l : ℝ) (a : l-1≠0) (b : l≠0) (c : l+1≠0) (d : l+2≠0) :
 (2*l+1)/((l-1)*l*(l+1)*(l+2))^2=
 (1/((l-1)*l*(l+1))^2-1/(l*(l+1)*(l+2))^2)/3 := by field_simp;ring
theorem first_tail : (1:ℝ)/(3*(1*2*3)^2)=1/108 := by norm_num

def g (b d u v : ℝ) := (100*b-4*b^2+48*d*b^2)*u-96*d*b^3*v
theorem werner_score (b d u v : ℝ) :
 24*(4*b*u+2*d*b^2*u-4*d*b^3*v)-(25-4*b*(1-b)*u)=g b d u v-25 :=
by unfold g;ring
theorem matched_score (b d : ℝ) (hb : b≠0) :
 g b d (1/(4*b)) ((1/(4*b))^2)=25+b*(6*d-1) := by unfold g;field_simp;ring

theorem packet_deadline (b d u v T : ℝ) (hb : 0≤b) (hd : 0≤d) (hv : 0≤v)
 (hp : 0≤100*b-4*b^2+48*d*b^2) (hu : u≤T/4) (he : 25<g b d u v) :
 100<(100*b-4*b^2+48*d*b^2)*T :=
begin
 unfold g at he,
 have h1:=mul_le_mul_of_nonneg_left hu hp,
 have h2 : 0≤96*d*b^3*v := by positivity,
 linarith,
end

theorem mean_square {X : Type*} [measurable_space X] (μ : measure X) [is_probability_measure μ]
 (F : X → ℝ) (h1 : integrable F μ) (h2 : integrable (λ x,(F x)^2) μ)
 (unit : (∫ x,(F x)^2 ∂μ)=1) (z : ℝ) : 0≤1-2*z*(∫ x,F x ∂μ)+z^2 :=
begin
 have h := @integral_nonneg X _ μ (λ x,(F x-z)^2) (λ x,sq_nonneg _),
 have e : (λ x,(F x-z)^2)=(λ x,(F x)^2-(2*z)*F x+z^2) := by {funext x,ring},
 have hs : integrable (λ x,(F x)^2-(2*z)*F x) μ := h2.sub (h1.const_mul (2*z)),
 have hc : integrable (λ x:X,z^2) μ := integrable_const (z^2),
 rw [e,integral_add hs hc,
     integral_sub h2 (h1.const_mul (2*z)),integral_mul_left,unit] at h,
 simpa using h,
end

-- Schur/L1 bound directly on a finite window with measure normalized to one.
theorem bounded_kernel {X : Type*} [measurable_space X] (μ : measure X) [is_probability_measure μ]
 (F : X → ℝ) (k : X → X → ℝ) (hf : integrable F μ)
 (hn : ∀ x, 0 ≤ F x) (hk : ∀ x y, k x y ≤ 1)
 (hi : ∀ x, integrable (λ y, k x y * F y) μ)
 (ho : integrable (λ x, F x*(∫ y, k x y * F y ∂μ)) μ)
 (square : ∀ z : ℝ, 0≤1-2*z*(∫ x, F x ∂μ)+z^2) :
 (∫ x, F x*(∫ y, k x y * F y ∂μ) ∂μ) ≤ 1 :=
begin
 have hx : ∀ x, (∫ y,k x y * F y ∂μ) ≤ ∫ y,F y ∂μ :=
 λ x, integral_mono (hi x) hf (λ y,by simpa using mul_le_mul_of_nonneg_right (hk x y) (hn y)),
 have hz:=square (∫ x,F x ∂μ),
 have ht:=integral_mono ho (hf.mul_const (∫ y,F y ∂μ)) (λ x,mul_le_mul_of_nonneg_left (hx x) (hn x)),
 rw [integral_mul_right] at ht,nlinarith,
end

theorem wick_threshold (v : ℝ) (h : 0≤v) :
 (1-v)/(2*(2+v))>1/6 ↔ v<1/4 :=
begin have hp : 0<2*(2+v) := by linarith, rw [gt_iff_lt,lt_div_iff hp],constructor;intro ht;linarith end

theorem species_det (c s a b : ℝ) (hn : c*c+s*s=1) :
 (c*c*a+s*s*b)*(s*s*a+c*c*b)-(c*s*(a-b))^2=a*b :=
begin linear_combination a*b*(c*c+s*s+1)*hn end

theorem gaussian_cut (a b c : ℝ) :
 ((25*a*b+5*c^2)-(5*a*b+25*c^2))/2=10*(a*b-c^2) := by ring

theorem no_dark_transmission (t : ℂ) : (t-t)/2=0 := by simp
theorem thermal_criterion (eta n : ℝ) :
 n+(1-eta)/2<(1+eta)/2 ↔ n<eta := by constructor;intro h;linarith

theorem pulse_clock (u : ℝ) (h : u≠0) : u^2*(1/u)^2=1 := by field_simp

theorem curvature_slope {K : Type*} [field K] (a b x : K) (h : 1-2*x≠0)
 (hs : (1-2*x)*a=b-3) : a=(b-3)/(1-2*x) :=
by { rw [eq_div_iff h], simpa [mul_comm] using hs }

theorem pair_budget (n L w : ℝ) : 2*w*n+2*w*(L-n)=2*w*L := by ring
theorem matched_source (l : ℝ) (hl : l^2=3) (hp : l>0) :
 (2-l)^2*(2+l)^2=1 ∧ (2-l)^2/(1-(2-l)^2)=1/l-1/2 :=
begin
 have ha : l≠0 := ne_of_gt hp,
 have hb : 1-(2-l)^2≠0 := by {intro h, nlinarith},
 split,
 { linear_combination (l^2-5)*hl },
 { field_simp [ha,hb], nlinarith [congr_arg (λ z:ℝ,z*l) hl] },
end
theorem stationary_links (r p q : ℝ) : (q-r*p)^2=0 ↔ q=r*p :=
by constructor;intro h; nlinarith [sq_nonneg (q-r*p)]
theorem quadrupole_mass (a b : ℝ) (h : a+b≠0) :
 a*(b/(a+b))^2+b*(a/(a+b))^2=a*b/(a+b) := by field_simp;ring
theorem quadrupole_charge (a b : ℝ) (h : a+b≠0) :
 (b/(a+b))^2-(a/(a+b))^2= -(a-b)/(a+b) := by field_simp;ring

theorem atom_pair (e g G : ℝ) (h : G≠0) :
 2*G*10*((e*g-(-e)*g)^2/G^2)=80*e^2*g^2/G := by field_simp;ring
theorem total_dark_law (rho a b c g : ℝ) (h : 0≤g) (s : a+b=c) :
 g*a*rho+g*b*rho=g*c*rho := by rw [←s];ring
theorem cone_leakage (a b v s : ℝ) (ha : 0<a) (hb : 0<b) :
 2*a*b*(1-v)≤s ↔ 1-s/(2*a*b)≤v :=
begin
 have hp : 0<2*a*b := by positivity,
 constructor,
 { intro ht, have hx : 1-v≤s/(2*a*b) := (le_div_iff hp).2 (by nlinarith only [ht]), linarith },
 { intro ht, have hx : 1-v≤s/(2*a*b) := by linarith,
   have hy := (le_div_iff hp).1 hx, nlinarith only [hy] },
end
theorem neutral_charge_cap (z : ℝ) (hz : 0≤z) (hm : z≤3/4) :
 16*z^2/(9+16*z^2) ≤ 1/2 :=
begin
 have h : 0<9+16*z^2 := by positivity,
 rw [div_le_iff h],nlinarith [mul_nonneg (sub_nonneg.mpr hm) (show 0≤3/4+z, by linarith)],
end
theorem exit_completeness {R : Type*} [ring R] (p B : R) (hp : p*p=p) (hc : p*B=B*p) :
 p*B*p+(1-p)*B*(1-p)=B :=
begin
 have h : p*B*p=B*p := by rw [hc,mul_assoc,hp],
 calc p*B*p+(1-p)*B*(1-p) = B-p*B-B*p+(p*B*p+p*B*p) : by noncomm_ring
 ... = B : by rw [h,hc];noncomm_ring,
end

theorem same_null_two (a b v : ℝ) (ha : 0<a) (hb : 0<b) :
 2*a*b*(1-v)=0 ↔ v=1 :=
begin have k : (2*a*b)≠0 := ne_of_gt (by positivity),
 rw [mul_eq_zero,or_iff_right k],constructor;intro h;linarith end

theorem orthogonal_channel_example :
 ((1/2:ℚ)*(1/2))^2=1/16 ∧ ((1:ℚ)*0)^2=0 ∧ ((0:ℚ)*1)^2=0 := by norm_num
theorem soft_collinear (x y d c : ℝ) (hd : d≠0) (hc : c≠0) (hj : 1-c≠0) :
 (c*x)*(c*y)/(c*d)+((1-c)*x)*((1-c)*y)/((1-c)*d)=x*y/d :=
by field_simp;ring
theorem soft_current_recoil (E M z : ℝ) (h1 : 1-z≠0) (h2 : M+E*(1-z)≠0) :
 E^2/(M+E*(1-z))-E/(1-z)= -M*E/((1-z)*(M+E*(1-z))) :=
by field_simp [h1,h2];ring
theorem angular_soft_cancellation (z : ℝ) (h : 1-z≠0) :
 (1-z^2)^2/(1-z)^2=(1+z)^2 := by field_simp;ring
theorem inclusive_recoil_bound (E D d q : ℝ) (hE : 0≤E) (hD : 0≤D)
 (hd : 0≤d) (hu : d≤2*E*D) (hq : 0≤q) (hv : q≤D^2) :
 abs (q-2*d) ≤ 4*E*D+D^2 :=
by rw [abs_le];constructor;nlinarith [mul_nonneg hE hD,sq_nonneg D]
def entry (xs : list ℕ) (i : ℕ) : ℕ := (xs.nth i).get_or_else 0
def labels : list ℕ := [0,1,2,3]
def cycle_count (f : ℕ → ℕ) : ℕ :=
 let a := (labels.filter (λ i,f i=i)).length, b := (labels.filter (λ i,f (f i)=i)).length in
 if a=4 then 4 else if a=2 then 3 else if a=1 then 2 else if b=4 then 2 else 1
def exchange_degree (p : list ℕ) : ℕ := ([0,2].filter (λ (i:ℕ),entry p i%2=1)).length
def four_perms : list (list ℕ) :=
 (labels.bind (λ a, labels.bind (λ b, labels.bind (λ c, labels.map (λ d,[a,b,c,d]))))).filter list.nodup
theorem four_perms_count : four_perms.length=24 := dec_trivial
def wick_coeff (sw : list ℕ) (k : ℕ) : ℕ :=
 ((four_perms.map (λ p, if exchange_degree p=k then
     (5:ℕ)^cycle_count (λ i,entry sw (entry p i)) else 0))).sum
def three (sw : list ℕ) := [wick_coeff sw 0, wick_coeff sw 1, wick_coeff sw 2]
theorem four_slot_wick :
 [three [0,1,2,3],three [1,0,2,3],three [0,1,3,2],three [1,0,3,2]]
 = [[900,720,60],[180,1320,180],[180,1320,180],[60,720,900]] := dec_trivial
theorem four_receipt_sign (v : ℝ) :
 (900+720*v+60*v^2)*(60+720*v+900*v^2)-(180+1320*v+180*v^2)^2
 =21600*(1-v)^2*(1+12*v+v^2) := by ring
theorem observed_threshold :
 let v : ℚ:=9/20, Z:=900+720*v+60*v^2, X:=180+1320*v+180*v^2, W:=60+720*v+900*v^2 in
 (Z-W)/(2*(Z+X))=2233/13644 ∧ (Z-X)/(2*Z)=473/2747 ∧
 (2233/13644:ℚ)<1/6 ∧ (1/6:ℚ)<473/2747 := by norm_num
theorem partial_retention (q : ℝ) (hq : 0≤q) :
 ((2274/2747:ℝ)*(2233/13644)+q*(473/2747)*(55/258))/(2274/2747+q*(473/2747))<1/6 ↔
 q<41/132 :=
begin
 rw [div_lt_iff (show (0:ℝ)<2274/2747+q*(473/2747), by positivity)],
 constructor; intro h;linarith,
end
theorem survival_bias (Z X Y W : ℝ) (hz : 0<Z) (hp : 0<Z+X) (h : X*Y<Z*W) :
 (Z+X-Y-W)/(2*(Z+X))<(Z-Y)/(2*Z) :=
begin rw [div_lt_div_iff (by linarith : 0<2*(Z+X)) (by linarith : 0<2*Z)], nlinarith end
theorem equal_site_law (n p : ℝ) (hn : n≠0) (sum : n*p=1) : p=1/n :=
by rw [eq_div_iff hn,mul_comm];exact sum
theorem no_equal_positive_site (p : ℝ) (hp : 0<p) : ∃ n : ℕ, 1<(n:ℝ)*p :=
begin obtain ⟨n,hn⟩:=exists_nat_gt (1/p), exact ⟨n,(div_lt_iff hp).1 hn⟩ end
theorem grounded_transmission : (((-3:ℝ)/5)^2+(4/5)^2)=1 ∧ (1*(2/3))^2=4/9 := by norm_num
theorem weak_dual (thick thin alpha bound : ℝ) (ha : 0≤alpha) (ht : thin≤25)
 (h : thick-alpha*thin≤bound) : thick≤bound+25*alpha :=
by nlinarith [mul_nonneg ha (sub_nonneg.mpr ht)]

theorem matrix_force (y d v w : ℝ) :
 4*v*(-4*y*(y^2+d^2))+2*w*(-8*y^2*d)+16*y^3*v+16*y*v*d^2+16*y^2*d*w=0 := by ring
theorem matrix_current_rank :
 let y : ℚ:=1, d : ℚ:=1/2, c : ℚ:=1/2, y2:=-4*y*(y^2+d^2), d2:=-8*y^2*d,
 y4:=-4*(y2*(3*y^2+d^2)+2*y*d*d2), d4:=-8*(2*y*y2*d+y^2*d2),
 q2:=(8/3)*d*d2, q4:=(8/3)*(3*d2^2+d*d4),
 j2:=(16/3)*c*(d2*y^2+2*d*y*y2),
 j4:=(16/3)*c*(d4*y^2+12*d2*y*y2+d*(2*y*y4+6*y2^2))
 in q2*j4-q4*j2= -1280 := by norm_num

theorem edge_ground_unique (k : ℕ) (r p : ℕ → ℝ)
 (rec : ∀ n, p (n+1)=r n*p n) : p k=(∏ i in finset.range k,r i)*p 0 :=
begin induction k with k ih, { simp }, { rw [rec k,ih,finset.prod_range_succ],ring } end

theorem mediator_sign (A B : bool) : (if A && B then (-1:ℤ) else 1)^2=1 :=
by cases A;cases B;norm_num
end causal_receipts
