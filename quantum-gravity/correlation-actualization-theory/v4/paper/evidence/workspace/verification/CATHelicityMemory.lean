import tactic
import analysis.special_functions.trigonometric.basic
import analysis.inner_product_space.basic
import data.nat.choose.basic

namespace cat_helicity_memory
noncomputable theory

-- The two factors of the material mark each anticommute with a transfer.
theorem double_odd {A : Type*} [ring A] (e s v : A)
 (he : e*v= -(v*e)) (hs : s*v= -(v*s)) : (e*s)*v=v*(e*s) :=
begin rw [mul_assoc,hs,mul_neg,←mul_assoc,he,neg_mul,neg_neg,mul_assoc] end

theorem even_product {A : Type*} [ring A] (a b h : A)
 (ha : a*h=h*a) (hb : b*h=h*b) : (a*b)*h=h*(a*b) :=
by rw [mul_assoc,hb,←mul_assoc,ha,mul_assoc]

theorem central_square {A : Type*} [ring A] (e s : A) (hc : e*s=s*e)
 (he : e*e=1) (hs : s*s=1) : (e*s)*(e*s)=1 :=
begin calc (e*s)*(e*s)=(e*e)*(s*s) : by {rw [mul_assoc,←mul_assoc s e s,←hc]; simp only [mul_assoc]}
 ... =1 : by rw [he,hs,one_mul] end

theorem even_sum {A : Type*} [ring A] (k h v : A) (hc : k*h=h*k) (hv : k*v=v*k) :
 k*(h+v)=(h+v)*k := by rw [mul_add,add_mul,hc,hv]

theorem compatible_energy {A : Type*} [ring A] (p h : A) (hp : p*p=p)
 (c : p*h=h*p) : p*h*p+(1-p)*h*(1-p)=h :=
begin
 have s : p*h*p=h*p := by rw [c,mul_assoc,hp],
 calc p*h*p+(1-p)*h*(1-p)=h-h*p-p*h+2*(p*h*p) : by noncomm_ring
 ... =h : by rw [s,c]; noncomm_ring
end

theorem sharp_read_energy_cost {A : Type*} [ring A] (p h : A) :
 p*h*p+(1-p)*h*(1-p)-h = -(p*h*(1-p)+(1-p)*h*p) := by noncomm_ring

theorem no_load_blank {A : Type*} [ring A] (p u b : A)
 (c : p*u=u*p) (blank : p*b=0) : p*(u*b)=0 := by rw [←mul_assoc,c,mul_assoc,blank,mul_zero]

theorem signed_class (chi l r frozen q : ℤ) (left : l=frozen+q) (right : r=frozen-q) :
 chi*(l-r)=2*(chi*q) := by rw [left,right];ring

theorem distinguish_even_when_neutral (a k : ℤ) (hk : 0<k) :
 ¬(a=k ∧ a= -k) := by rintro ⟨l,r⟩;linarith

theorem selected_number (na nb nc nd : ℤ) :
 (na-nb)+(nc-nd)=(na+nc)-(nb+nd) := by ring

theorem spectator_momentum (q act dark : ℤ) (h : q+act+dark=0) : act= -q-dark := by linarith
theorem unique_one_plus (q act : ℤ) (gauss : q+act-1=0)
 (count : |act|+1=1) : q=1 :=
begin have z : |act|=0 := by linarith, rw [abs_eq_zero.mp z] at gauss, linarith end
theorem unique_one_minus (q act : ℤ) (gauss : q+act+1=0)
 (count : |act|+1=1) : q= -1 :=
begin have z : |act|=0 := by linarith, rw [abs_eq_zero.mp z] at gauss, linarith end
theorem no_empty_after_return (a d : ℤ) (g : a+d=0) (s : |d|=1) :
 |a|+|d|=2 :=
begin have t : a= -d := by linarith, rw [t,abs_neg,s], norm_num end

theorem plus_two_sort (m h : ℤ) (mh : m=1 ∨ m= -1) (ph : h=1 ∨ h= -1)
 (incoming : m+h=2) : m=1 ∧ h=1 :=
by rcases mh with hm|hm;rcases ph with hh|hh;constructor;linarith
theorem zero_sort (m h : ℤ) (total : m+h=0) : m= -h := by linarith

theorem radial_quartic (x y a b : ℝ) :
 (x*b-y*a)^2*4 =
 (((x+b)^2+(y-a)^2)/2-((x-b)^2+(y+a)^2)/2)^2 := by ring

theorem pair_energy_floor (e w a d z1 z2 : ℝ) (hw : 0≤w)
 (s1 : a≤z1) (s2 : d≤z2) (h : w*(2+z1+z2)≤e) :
 w*(a+d)≤e-2*w := by nlinarith only [h,mul_nonneg hw (sub_nonneg.mpr s1),mul_nonneg hw (sub_nonneg.mpr s2)]

theorem states_per_orientation :
 nat.choose 2 0^4+nat.choose 2 1^4+nat.choose 2 2^4=18 := by norm_num [nat.choose]
theorem neutral_capacity : nat.choose 8 4 * nat.choose 8 4=4900 := by norm_num [nat.choose]
theorem mixed_weight : (36:ℝ)/4900=9/1225 := by norm_num
theorem matter_prior (a b success : ℝ) (h : success≠0) (s : a+b=1) :
 a*success/(a*success+b*success)=a :=
begin rw [←add_mul,s,one_mul], field_simp [h] end

theorem blocked_projection {A : Type*} [ring A] (p v : A) (hp : p*p=p)
 (c : p*v=v*p) : (1-p)*v*p=0 :=
begin rw [sub_mul,one_mul,sub_mul,c,mul_assoc,hp,sub_self] end

theorem conserved_sector_wrong {A : Type*} [ring A] (wrong u mark : A)
 (c : u*mark=mark*u) (r : wrong*mark=0) : wrong*u*mark=0 :=
by rw [mul_assoc,c,←mul_assoc,r,zero_mul]

theorem twice_real_circular (x y : ℝ) : ((x^2+y^2)/2)^2=(x^2+y^2)^2/4 := by ring
theorem mass_shell (E p mass lo hi : ℝ) (kin : E^2-p^2=mass^2)
 (km : 2*lo*hi=(E-p)*(E+p)) : 2*lo*hi=mass^2 := by nlinarith
theorem offset_gap (lo hi d : ℝ) (h : hi=lo+d) : hi-lo=d := by linarith
theorem complex_rotation (a b x y : ℝ) :
 (a*x-b*y)^2+(b*x+a*y)^2=(a^2+b^2)*(x^2+y^2) := by ring
theorem circular_phase_pair (a b c d : ℝ) :
 (a*c-b*d)^2+(a*d+b*c)^2=(a^2+b^2)*(c^2+d^2) := by ring

theorem sine_doubled_detection (p x : ℝ) :
 p^2*real.sin (2*x)^2=4*p*real.cos x^2*(p*real.sin x^2) :=
by rw [real.sin_two_mul];ring

-- A contraction at each accepted site gives the telescoping n-use amplitude bound.
theorem telescope (a : ℕ→ℝ) (d : ℝ) (zero : a 0=0)
 (step : ∀ n,a (n+1)≤a n+d) (n : ℕ) : a n≤(n:ℝ)*d :=
begin induction n with n h, {rw [zero,nat.cast_zero,zero_mul]},
 calc a (n+1)≤a n+d : step n
 ... ≤(n:ℝ)*d+d : add_le_add_right h _
 ... =((n+1:ℕ):ℝ)*d : by push_cast;ring
end

theorem next_cost (n p : ℝ) (hn : 0≤n) (hp : 0≤p) :
 (n+2)^2*p≤4*p*(n+1)^2 :=
begin have h : (n+2)^2≤4*(n+1)^2 := by nlinarith [sq_nonneg n],
 convert mul_le_mul_of_nonneg_right h hp using 1;ring end

theorem loss_factor (p : ℝ) (hp : 0≤p) (n : ℕ) :
 ((n:ℝ)+1)^2*p^n≤(4*p)^n :=
begin
 induction n with n h, {simp},
 have hn : (0:ℝ)≤n := nat.cast_nonneg _,
 calc (((n+1:ℕ):ℝ)+1)^2*p^(n+1)=(((n:ℝ)+2)^2*p)*p^n : by {rw [pow_succ p n];push_cast;ring}
 ... ≤(4*p*((n:ℝ)+1)^2)*p^n : mul_le_mul_of_nonneg_right (next_cost n p hn hp) (pow_nonneg hp _)
 ... =4*p*(((n:ℝ)+1)^2*p^n) : by ring
 ... ≤4*p*(4*p)^n : mul_le_mul_of_nonneg_left h (by positivity)
 ... =(4*p)^(n+1) : by rw [pow_succ];ring
end

theorem receipt_bound (p risk leak : ℝ) (h : 0<p) (h' : risk≤leak) :
 risk/p≤leak/p := div_le_div_of_le h.le h'

theorem orthogonal_flags_fidelity (p : ℝ) (h : p≤1) :
 (1+real.sqrt ((1-p)^2))/2=1-p/2 :=
by rw [real.sqrt_sq (sub_nonneg.mpr h)];ring

def effect (a b c d x y : ℂ) : ℂ × ℂ := (a*x+b*y,c*x+d*y)

theorem scalar_on_helicity_pair (a b c d : ℂ)
 (turn : ∀ x y, effect a b c d x (-y)=((effect a b c d x y).1,-(effect a b c d x y).2))
 (mirror : ∀ x y, effect a b c d y x=((effect a b c d x y).2,(effect a b c d x y).1))
 (x y : ℂ) : effect a b c d x y=(a*x,a*y) :=
begin
 have hb := congr_arg prod.fst (turn 0 1),
 have hc := congr_arg prod.snd (turn 1 0),
 have hd := congr_arg prod.fst (mirror 0 1),
 simp [effect] at hb hc hd,
 have b0 : b=0 := by linear_combination (-(1/2):ℂ)*hb,
 have c0 : c=0 := by linear_combination (1/2:ℂ)*hc,
 simp [effect,b0,c0,hd]
end

theorem normalize_gram (p : ℝ) (hp : 0<p) (x y : ℂ) (h : x=(p:ℂ)*y) :
 x/((real.sqrt p:ℂ)^2)=y :=
begin
 have e : ((real.sqrt p:ℂ)^2)=(p:ℂ) := by exact_mod_cast real.sq_sqrt hp.le,
 have nz : (p:ℂ)≠0 := by exact_mod_cast ne_of_gt hp,
 rw [e,h],field_simp [nz],ring
end

theorem record_sequence {A : Type*} [ring A] (k a b : A)
 (ha : a*k=k*a) (hb : b*k=k*b) : (a*b)*k=k*(a*b) := even_product _ _ _ ha hb

theorem erased_key (p c : ℝ) : (1+(1-p)+2*p*c)/2=1-p*(1-2*c)/2 := by ring
theorem pure_even_key (p : ℝ) : 1-p*(1-2*(1/2))/2=1 := by ring
theorem sea_loading (n g w strength : ℝ) (hn : 0<n) (hw : 0<w) (hg : 0<g)
 (hs : 0<strength) : 0<4*g*strength/(n*w) := by positivity

theorem kraus_overlap {V : Type*} [normed_add_comm_group V] [inner_product_space ℂ V]
 (x y : V) (hx : ‖x‖≤1) (hy : ‖y‖≤1) : ‖@inner ℂ V _ x y‖≤1 :=
begin
 exact (norm_inner_le_norm x y).trans
 (calc ‖x‖*‖y‖≤1*1 : mul_le_mul hx hy (norm_nonneg _) zero_le_one
 ... =1 : one_mul _)
end

theorem successful_fidelity_bound (p a b c u v z : ℝ) (hp : 0≤p)
 (ha : 0≤a) (hb : 0≤b) (mass : a+b=1) (left : u≤1) (right : v≤1)
 (cross : z≤c) : p/4*(a*u+b*v+2*z)≤p/4*(1+2*c) :=
begin
 apply mul_le_mul_of_nonneg_left _ (show 0≤p/4, from div_nonneg hp (by norm_num)),
 have h1 := mul_le_mul_of_nonneg_left left ha,
 have h2 := mul_le_mul_of_nonneg_left right hb,
 linarith
end

theorem optimal_fidelity (p c : ℝ) :
 (1-p)+2*(p/4*(1+2*c))=1-p*(1-2*c)/2 := by ring

theorem quartic_before_cutoff {A : Type*} [ring A] (p r : A) (hp : p*p=p) :
 p*(r*r)*p=(p*r*p)*(p*r*p)+p*r*(1-p)*r*p :=
begin
 have h : (p*r*p)*(p*r*p)=p*r*(p*p)*r*p := by noncomm_ring,
 rw [h,hp], noncomm_ring
end

theorem ph_ready (N s w p : ℝ) (hN : 0<N) (hw : 0<w) (hs : 0≤s)
 (h : p=4*s/(N*w)) : p=0 ↔ s=0 :=
begin
 rw [h,div_eq_zero_iff], have nn : N*w≠0 := ne_of_gt (mul_pos hN hw),
 simp [nn]
end

-- a and b can be different histories that the CAT update assigns the same charge.
theorem shared_output_intertwiner {A : Type*} [ring A] (s t a b : A)
 (ha : s*a=a*t) (hb : t*b=b*s) : s*(a*b)=(a*b)*s :=
by rw [←mul_assoc,ha,mul_assoc,hb,←mul_assoc]

theorem tagged_trace_norm (w s angle : ℝ) :
 w^2+(1-w)^2+2*w*(1-w)*s^2*real.cos (2*angle)+2*w*(1-w)*(1-s^2)
 =1-4*w*(1-w)*s^2*(real.sin angle)^2 :=
begin
 have c : real.cos (2*angle)=1-2*(real.sin angle)^2 :=
   by {rw [real.cos_two_mul], nlinarith [real.sin_sq_add_cos_sq angle]},
 rw [c],ring
end

theorem tag_determinant (w x s t : ℂ) :
 (w+x*s^2)*(x*t^2)-(x*s*t)^2=w*x*t^2 := by ring

theorem coincident_routes (w s : ℝ) : 1-4*w*(1-w)*s^2*(real.sin 0)^2=1 := by simp
theorem separable_routes (w t : ℝ) : 1-4*w*(1-w)*(0:ℝ)^2*t^2=1 := by ring

theorem tag_worst_posterior (w : ℝ) : 4*w*(1-w)≤1 := by nlinarith [sq_nonneg (2*w-1)]
theorem tag_stable_deficit (d x : ℝ) (hx : 0≤x) (e : x^2=1-d) :
 (1-x)/2=d/(2*(1+x)) :=
begin
 apply (eq_div_iff (show 2*(1+x)≠0, from ne_of_gt (by positivity))).2,
 nlinarith
end

end cat_helicity_memory
