import tactic
import analysis.calculus.mean_value
import measure_theory.integral.bochner
import analysis.special_functions.integrals

noncomputable theory
open filter set measure_theory
open_locale topology filter

namespace tidal_memory_release

-- The exterior wave equation fixes a, B and the horizon probability coefficient.
-- The following are exact consequences of the port flux equation.
theorem flux_complement (u g d : ℝ) :
 d^2+(u+g)^2-4*u*g=d^2+(u-g)^2 := by ring

theorem passivity (u g d : ℝ) (hu : 0≤u) (hg : 0≤g)
 (hd : 0<d^2+(u+g)^2) : 0≤4*u*g/(d^2+(u+g)^2) ∧ 4*u*g/(d^2+(u+g)^2)≤1 :=
⟨div_nonneg (by positivity) hd.le,(div_le_iff hd).2 (by nlinarith [sq_nonneg (u-g),sq_nonneg d])⟩

theorem fifth_loss_identity (k a B g C : ℝ) (hk : k≠0)
 (he : C*k^6*((B*k^2)^2+(g+a*k^5)^2)=4*g*(a*k^5)) :
 (g/k^5)*(4*a-C*k*(g+2*a*k^5))=C*(B^2+a^2*k^6) :=
begin
 field_simp [hk],
 have h : (C*k*((B*k^2)^2+(g+a*k^5)^2)-4*g*a)*k^5=0 :=
 by nlinarith only [he],
 have h' := (mul_eq_zero.mp h).resolve_right (pow_ne_zero 5 hk),
 nlinarith only [h']
end

theorem fifth_loss_limit (k a B g C : ℕ → ℝ) (a₀ B₀ g₀ C₀ : ℝ)
 (hk : tendsto k at_top (𝓝 0)) (ha : tendsto a at_top (𝓝 a₀))
 (hB : tendsto B at_top (𝓝 B₀)) (hg : tendsto g at_top (𝓝 g₀))
 (hC : tendsto C at_top (𝓝 C₀)) (hpos : 0<a₀) (hn : ∀n,k n≠0)
 (flux : ∀n,C n*(k n)^6*((B n*(k n)^2)^2+(g n+a n*(k n)^5)^2)=4*g n*(a n*(k n)^5)) :
 tendsto (λ n,g n/(k n)^5) at_top (𝓝 (C₀*B₀^2/(4*a₀))) :=
begin
 have cst : ∀c:ℝ,tendsto (λ _:ℕ,c) at_top (𝓝 c) := λ c,tendsto_const_nhds,
 have hd : tendsto (λ n,4*a n-C n*k n*(g n+2*a n*(k n)^5)) at_top (𝓝 (4*a₀)) :=
 by simpa using (((cst 4).mul ha).sub ((hC.mul hk).mul (hg.add (((cst 2).mul ha).mul (hk.pow 5))))),
 have hu : tendsto (λ n,C n*((B n)^2+(a n)^2*(k n)^6)) at_top (𝓝 (C₀*B₀^2)) :=
 by simpa using hC.mul ((hB.pow 2).add ((ha.pow 2).mul (hk.pow 6))),
 have hh : 0<4*a₀ := by positivity,
 refine filter.tendsto.congr' _ (hu.div hd (ne_of_gt hh)),
 filter_upwards [hd.eventually (lt_mem_nhds hh)] with n h,
 exact ((eq_div_iff (ne_of_gt h)).2 (fifth_loss_identity _ _ _ _ _ (hn n) (flux n))).symm
end

theorem quadrupole_coefficient (d B : ℝ) (hd : d≠0) :
 (4/225:ℝ)*B^2/(4*(1/(9*d^2)))=d^2*B^2/25 := by {field_simp [hd]; ring}

theorem port_imaginary_numerator (m K k : ℝ) :
 (m*k^3)*(K-m*k^2)-(-m*k^2*K)*(-k) = -m^2*k^5 := by ring

theorem mass_spring_match (m I d : ℝ) (hm : m≠0) (hd : d≠0) (hB : I+m≠0) :
 (m/(5*m/(d*(I+m))))^2=d^2*(I+m)^2/25 := by {field_simp [hm, hd, hB];ring}

theorem flat_denom (m K k : ℝ) (h : 2*m*K=1) :
 (K-m*k^2)^2+k^2=K^2+m^2*k^4 := by {linear_combination -(k^2)*h}

theorem threshold_square (f df d dd : ℝ) (hd : d ≠ 0) :
 d^2*((df*d-f*dd)/d^2)^2=df^2-2*f*df*dd/d+f^2*(dd/d)^2 :=
by {field_simp [hd];ring}

theorem write_before_return {α : Type*} [add_group α] (pulse : ℝ → α)
 (T D : ℝ) (late : ∀u≤T,pulse (u-D)=0) :
 ∀u≤T,pulse u - pulse (u-D)=pulse u :=
λ u hu, by rw [late u hu,sub_zero]

-- All shell energies are G times masses, and R is areal radius.
def F (y : ℝ) : ℝ := (27*y-18*y^2+7*y^3)/32
def Fy (y : ℝ) : ℝ := (27-36*y+21*y^2)/32
def mass (R P D : ℝ) : ℝ := R*(1+P^2-2*P*D)/2

theorem cubic_coefficients (a b c : ℝ) (v : a+b+c=1/2)
 (w : a+2*b+3*c=3/8) (z : 2*b+6*c=3/16) :
 a=27/32 ∧ b= -18/32 ∧ c=7/32 := by {split,linarith,split; linarith}

theorem phase_coexistence (y : ℝ) :
 F y-(27/56)*y=(7/32)*y*(y-9/7)^2 := by {unfold F,ring}

theorem outgoing_constraint (P D v : ℝ) (h : P=D+v) :
 1+P^2-2*P*D=1-D^2+v^2 := by {rw [h],ring}

theorem proper_flux_balance (R v P D Pd Dn ND RD : ℝ) (cross : v=P-D)
 (local_flux : v*(1+P^2-2*P*D)+2*R*((P-D)*Pd-P*(RD*v+Dn*ND))= -2*R*P*Dn*ND)
 (moving : v≠0) :
 R*Pd=R*P*RD-(1+P^2-2*P*D)/2 :=
begin
 have h : v*(2*R*Pd-2*R*P*RD+(1+P^2-2*P*D))=0,
 { rw [←cross] at local_flux, nlinarith only [local_flux] },
 linarith only [(mul_eq_zero.mp h).resolve_left moving]
end

theorem local_lapse (P y A f : ℝ) :
 P*(2*y*A)-(1+P^2-2*P*(1-f))/2= -(P-1)^2/2+P*(2*y*A-f) := by ring

theorem impulse_budget (R P d₁ d₂ : ℝ) :
 mass R P d₂-mass R P d₁= -R*P*(d₂-d₁) := by {unfold mass,ring}

theorem empty_rim (R P : ℝ) : mass R P 1=R*(P-1)^2/2 := by {unfold mass,ring}
theorem empty_exact (R P : ℝ) (hr : 0<R) : mass R P 1=0 ↔ P=1 :=
begin
 rw [empty_rim], split, { intro h, by_contra he,
   have hq : 0<(P-1)^2 := sq_pos_of_ne_zero _ (sub_ne_zero.mpr he),
   nlinarith only [mul_pos hr hq,h] },
 {intro h,rw [h],ring}
end

theorem mean_empty {α : Type*} [measurable_space α] (μ : measure α) (R P : α → ℝ)
 (hr : ∀ᵐ a ∂μ,0<R a) (hi : integrable (λ a,mass (R a) (P a) 1) μ) :
 (∫ a,mass (R a) (P a) 1 ∂μ)=0 ↔ ∀ᵐ a ∂μ,P a=1 :=
begin
 have hn : 0 ≤ᵐ[μ] (λ a,mass (R a) (P a) 1),
 { filter_upwards [hr] with a ha, change 0 ≤ mass (R a) (P a) 1, rw [empty_rim], positivity },
 rw [integral_eq_zero_iff_of_nonneg_ae hn hi],
 split; intro h; filter_upwards [hr,h] with a ha hp,
 { exact (empty_exact _ _ ha).1 hp }, { exact (empty_exact _ _ ha).2 hp }
end

theorem rest_flash : mass 1 (1/2) 1 / mass 1 (1/2) (1/2) = 1/3 :=
by norm_num [mass]

theorem two_pulse_start : F (4/5)=427/1000 ∧
 mass 1 (1/2) (1-F (4/5))=677/2000 := by norm_num [mass,F]

theorem locked_pressure (y f slope : ℝ) (h : 2*y*slope=f) :
 -((1:ℝ)-1)^2/2+1*(2*y*slope-f)=0 := by rw [h];ring

theorem pressureless_energy (R f : ℝ) : mass R 1 (1-f)=R*f :=
by {unfold mass,ring}

theorem smooth_endpoint (u : ℝ) : 1-3*u^2+2*u^3=(1-u)^2*(1+2*u) := by ring

theorem chirp_area (mi mf a : ℝ) (ha : a≠0) :
 (mi^4-mf^4)/(2*a)=(mi-mf)*(mi+mf)*(mi^2+mf^2)/(2*a) := by ring

-- A rational orbit. Here t is the inverse radius and the speed squared is t*G(t).
def G (t : ℝ) : ℝ := (677/1000:ℝ)+(-27/20:ℝ)*t+(1881/1600:ℝ)*t^3+(-71/100:ℝ)*t^5+(351/1250:ℝ)*t^7+(-252/3125:ℝ)*t^9+(196/15625:ℝ)*t^11
def Gprime (t : ℝ) : ℝ := (-27/20:ℝ)+(5643/1600:ℝ)*t^2+(-71/20:ℝ)*t^4+(2457/1250:ℝ)*t^6+(-2268/3125:ℝ)*t^8+(2156/15625:ℝ)*t^10
theorem orbit_speed (t : ℝ) : t*G t=2*(677/2000)*t-2*F ((4/5)*t^2)+(F ((4/5)*t^2))^2 := by {unfold G F,ring}
private def heval (x : ℝ) : list ℝ → ℝ
| [] := 0
| (c::cs) := c+x*heval cs

private def lower_tail : list ℝ → ℝ
| [] := 0
| (c::cs) := c+min 0 (lower_tail cs)

private theorem horner_bound (cs : list ℝ) (x : ℝ) (h0 : 0≤x) (h1 : x≤1) :
 lower_tail cs ≤ heval x cs :=
begin
 induction cs with c tail ih, {refl},
 change c+min 0 (lower_tail tail) ≤ c+x*heval x tail,
 apply add_le_add_left,
 by_cases h : 0≤lower_tail tail,
 { rw [min_eq_left h], exact mul_nonneg h0 (le_trans h ih) },
 { have hn := le_of_not_ge h, rw [min_eq_right hn],
   have t := mul_le_mul_of_nonpos_right h1 hn,
   exact (by {rw [one_mul] at t,exact le_trans t (mul_le_mul_of_nonneg_left ih h0)} ) }
end

private theorem cell_bound (f : ℝ→ℝ) (cs : list ℝ) (a w D t : ℝ)
 (hw : 0<w) (hd : 0<D) (lower : 0<lower_tail cs)
 (formula : ∀x,D*f (a+w*x)=heval x cs) (hl : a≤t) (hr : t≤a+w) : 0<f t :=
begin
 let x := (t-a)/w,
 have hx : 0≤x := div_nonneg (sub_nonneg.mpr hl) hw.le,
 have hx' : x≤1 := (div_le_iff hw).2 (by linarith),
 have rec : a+w*x=t := by {dsimp [x],field_simp [ne_of_gt hw]; ring},
 have e := lt_of_lt_of_le lower (horner_bound cs x hx hx'),
 rw [←formula,rec] at e, exact pos_of_mul_pos_right e hd.le
end

private theorem bcell0 (t : ℝ) (hl : 0≤t) (hr : t≤13/40) : 0 < G t :=
begin
 let cs : list ℝ := [1109196800000000000000,-718848000000000000000,0,66120912000000000000,0,-4217888480000000000,0,176197835736000000,0,-5344667683992000,0,87815859307813],
 apply cell_bound G cs (0) (13/40) 1638400000000000000000 t (by norm_num) (by norm_num) _ _ hl (by linarith only [hr]),
 { norm_num [cs,lower_tail,min_def] },
 { intro x, dsimp [cs,heval,G],ring }
end

private theorem bcell1 (t : ℝ) (hl : 13/40≤t) (hr : t≤39/80) : 0 < G t :=
begin
 let cs : list ℝ := [926561821704010374785024,-553357780566580779066368,81764570924080239470080,7596669179415158053120,-1992571781612980954880,-73637832366514073216,26400118134300211392,204304522941860640,-268899138961110840,-2059181688249140,1931948904771886,87815859307813],
 apply cell_bound G cs (13/40) (13/80) 3355443200000000000000000 t (by norm_num) (by norm_num) _ _ hl (by linarith only [hr]),
 { norm_num [cs,lower_tail,min_def] },
 { intro x, dsimp [cs,heval,G],ring }
end

private theorem bcell2 (t : ℝ) (hl : 39/80≤t) (hr : t≤13/20) : 0 < G t :=
begin
 let cs : list ℝ := [460525407111046855005511,-375219426068276308883793,92255550077120258004345,-589828249271213867655,-1976256221244506503770,74262884797527394774,20574382839171510258,-1760206027379790510,-186004456654829085,22090179621399435,2897923357157829,87815859307813],
 apply cell_bound G cs (39/80) (13/80) 3355443200000000000000000 t (by norm_num) (by norm_num) _ _ hl (by linarith only [hr]),
 { norm_num [cs,lower_tail,min_def] },
 { intro x, dsimp [cs,heval,G],ring }
end

private theorem bcell3 (t : ℝ) (hl : 13/20≤t) (hr : t≤117/160) : 0 < G t :=
begin
 let cs : list ℝ := [358580966978450607933751296,-204699295279948876866387968,40774927679452578599403520,-1897098822275496075591680,-175044181993287235665920,9848500219533487243264,177584825004117393408,-33220242845080412160,1261626622365258240,223597141819629760,7727795619087544,87815859307813],
 apply cell_bound G cs (13/20) (13/160) 6871947673600000000000000000 t (by norm_num) (by norm_num) _ _ hl (by linarith only [hr]),
 { norm_num [cs,lower_tail,min_def] },
 { intro x, dsimp [cs,heval,G],ring }
end

private theorem bcell4 (t : ℝ) (hl : 117/160≤t) (hr : t≤13/16) : 0 < G t :=
begin
 let cs : list ℝ := [192594450731526594543017117,-129490825463864394317332857,34133860997760223758082635,-2496311184976949232724455,-124182478100387431584990,10317196375956241030246,814238434639232694,-14121418052789591310,3636241318386654705,305704970272434915,8693770071473487,87815859307813],
 apply cell_bound G cs (117/160) (13/160) 6871947673600000000000000000 t (by norm_num) (by norm_num) _ _ hl (by linarith only [hr]),
 { norm_num [cs,lower_tail,min_def] },
 { intro x, dsimp [cs,heval,G],ring }
end

private theorem bcell5 (t : ℝ) (hl : 13/16≤t) (hr : t≤143/160) : 0 < G t :=
begin
 let cs : list ℝ := [94627300442269300000000000,-69157242989113370000000000,26002833417969395000000000,-2890116732008733500000000,-72783621886444300000000,10269911768524486000000,31324549124832600000,27046123066259700000,6793295320840665000,397472543249099500,9659744523859430,87815859307813],
 apply cell_bound G cs (13/16) (13/160) 6871947673600000000000000000 t (by norm_num) (by norm_num) _ _ hl (by linarith only [hr]),
 { norm_num [cs,lower_tail,min_def] },
 { intro x, dsimp [cs,heval,G],ring }
end

private theorem bcell6 (t : ℝ) (hl : 143/160≤t) (hr : t≤39/40) : 0 < G t :=
begin
 let cs : list ℝ := [48520326000186287251231743,-26061275986568846798304257,16999723405929953844506065,-3076564010688890447981255,-19489910761138476354410,11458808552628411862966,446316490482124167906,96889645766387311890,10819726330442023995,498899860749623515,10625718976245373,87815859307813],
 apply cell_bound G cs (143/160) (13/160) 6871947673600000000000000000 t (by norm_num) (by norm_num) _ _ hl (by linarith only [hr]),
 { norm_num [cs,lower_tail,min_def] },
 { intro x, dsimp [cs,heval,G],ring }
end

private theorem bcell7 (t : ℝ) (hl : 39/40≤t) (hr : t≤91/80) : 0 < G t :=
begin
 let cs : list ℝ := [17761100020569320470528,-1278065942833213228032,15188927383711967408640,-11824097652175752103680,380566559116117021440,263169911963804849536,45989872134818504256,12669494806726935840,1975309005988183320,152496730693501740,5795846714315658,87815859307813],
 apply cell_bound G cs (39/40) (13/80) 3355443200000000000000000 t (by norm_num) (by norm_num) _ _ hl (by linarith only [hr]),
 { norm_num [cs,lower_tail,min_def] },
 { intro x, dsimp [cs,heval,G],ring }
end

private theorem bcell8 (t : ℝ) (hl : 91/80≤t) (hr : t≤39/32) : 0 < G t :=
begin
 let cs : list ℝ := [42091301553547356502136832,-3228189462662451494085632,-7347863269411816310781440,-1582787971636563610330880,382518892124543168700160,59936099354605361170816,6529677186074778625344,554981279982206756640,28984658409277541880,861140280394352140,13523642333403202,87815859307813],
 apply cell_bound G cs (91/80) (13/160) 6871947673600000000000000000 t (by norm_num) (by norm_num) _ _ hl (by linarith only [hr]),
 { norm_num [cs,lower_tail,min_def] },
 { intro x, dsimp [cs,heval,G],ring }
end

private theorem bcell9 (t : ℝ) (hl : 39/32≤t) (hr : t≤13/10) : 0 < G t :=
begin
 let cs : list ℝ := [30382030359191878466796875,-20799221155316055791015625,-9091309888478115263671875,698363592909704947265625,801709190196171592968750,112503862425724623343750,11301332900780137556250,819511413664203731250,37357974454615644375,1001206575990313875,14489616785789145,87815859307813],
 apply cell_bound G cs (39/32) (13/160) 6871947673600000000000000000 t (by norm_num) (by norm_num) _ _ hl (by linarith only [hr]),
 { norm_num [cs,lower_tail,min_def] },
 { intro x, dsimp [cs,heval,G],ring }
end

theorem before_turn_left (t : ℝ) (hl : 0≤t) (hr : t≤13/20) : 0<G t :=
begin
 by_cases h0 : t≤13/40, {exact bcell0 t (by linarith) h0},
 by_cases h1 : t≤39/80, {exact bcell1 t (by linarith) h1},
 exact bcell2 t (by linarith) hr
end

theorem before_turn_right (t : ℝ) (hl : 13/20≤t) (hr : t≤13/10) : 0<G t :=
begin
 by_cases h3 : t≤117/160, {exact bcell3 t (by linarith) h3},
 by_cases h4 : t≤13/16, {exact bcell4 t (by linarith) h4},
 by_cases h5 : t≤143/160, {exact bcell5 t (by linarith) h5},
 by_cases h6 : t≤39/40, {exact bcell6 t (by linarith) h6},
 by_cases h7 : t≤91/80, {exact bcell7 t (by linarith) h7},
 by_cases h8 : t≤39/32, {exact bcell8 t (by linarith) h8},
 exact bcell9 t (by linarith) hr
end

private theorem down0 (t : ℝ) (hl : 13/10≤t) (hr : t≤131/100) : 0 < -Gprime t :=
begin
 let cs : list ℝ := [23117635312640000000000,150360529280000000000,-168093543648000000000,-8166007865600000000,-160326746960000000,-2154135110400000,-19680788400000,-112617960000,-381559500,-700700,-539],
 apply cell_bound (λ z:ℝ,-Gprime z) cs (13/10) (1/100) 390625000000000000000000 t (by norm_num) (by norm_num) _ _ hl (by linarith only [hr]),
 { norm_num [cs,lower_tail,min_def] },
 { intro x, dsimp [cs,heval,Gprime],ring }
end

theorem slope_at_turn (t : ℝ) (hl : 13/10≤t) (hr : t≤131/100) : 0 < -Gprime t := down0 t hl hr

theorem orbital_derivative (t : ℝ) : has_deriv_at G (Gprime t) t :=
begin
 unfold G Gprime,
 convert (((((((has_deriv_at_const t (677/1000:ℝ)).add ((has_deriv_at_id t).const_mul (-27/20:ℝ))).add ((has_deriv_at_pow 3 t).const_mul (1881/1600:ℝ))).add ((has_deriv_at_pow 5 t).const_mul (-71/100:ℝ))).add ((has_deriv_at_pow 7 t).const_mul (351/1250:ℝ))).add ((has_deriv_at_pow 9 t).const_mul (-252/3125:ℝ))).add ((has_deriv_at_pow 11 t).const_mul (196/15625:ℝ))) using 1; norm_num; ring
end

theorem unique_simple_bounce :
 ∃ t∈Icc (13/10:ℝ) (131/100), G t=0 ∧ Gprime t<0 ∧
    (∀u:ℝ,0≤u → u<t → 0<G u) :=
begin
 have hh : continuous G := continuous_iff_continuous_at.2 (λx,(orbital_derivative x).continuous_at),
 have lb : 0<G (13/10) := by norm_num [G],
 have ub : G (131/100)<0 := by norm_num [G],
 rcases intermediate_value_Icc' (by norm_num : (13/10:ℝ)≤131/100) hh.continuous_on
   (show (0:ℝ) ∈ Icc (G (131/100)) (G (13/10)), from ⟨ub.le,lb.le⟩) with ⟨t,ht,eq⟩,
 have dec : strict_anti_on G (Icc (13/10:ℝ) (131/100)),
 { apply (convex_Icc _ _).strict_anti_on_of_deriv_neg hh.continuous_on,
   intros u hu, have hi := interior_subset hu,
   rw [(orbital_derivative u).deriv], linarith only [slope_at_turn u hi.1 hi.2] },
 refine ⟨t,ht,eq,by linarith only [slope_at_turn t ht.1 ht.2],_⟩,
 intros u hu ut, by_cases h : u≤13/20, {exact before_turn_left u hu h},
 by_cases h' : u≤13/10, {exact before_turn_right u (le_of_not_ge h) h'},
 have hh' := dec (show u∈Icc (13/10:ℝ) (131/100), from ⟨le_of_not_ge h',le_trans ut.le ht.2⟩) ht ut,
 rwa [eq] at hh'
end

theorem outward_release_radius :
 ∃ t∈Icc (3/5:ℝ) (31/50), (677/2000)*t = F ((4/5)*t^2) :=
begin
 let h := λ t:ℝ,F ((4/5)*t^2)-(677/2000)*t,
 have hc : continuous h := by { dsimp [h,F],continuity },
 have hl : h (3/5)≤0 := by norm_num [h,F],
 have hr : 0≤h (31/50) := by norm_num [h,F],
 rcases intermediate_value_Icc (by norm_num : (3/5:ℝ)≤31/50) hc.continuous_on
  (show (0:ℝ)∈ Icc (h (3/5)) (h (31/50)), from ⟨hl,hr⟩) with ⟨t,ht,he⟩,
 exact ⟨t,ht,(sub_eq_zero.mp he).symm⟩
end

theorem outward_speed_at_release (M t f v : ℝ) (hv : 0≤v) (hf : 0≤f)
 (e : v^2=2*M*t-2*f+f^2) (h : M*t=f) : v=f :=
begin
 have sq : v*v=f*f := by nlinarith only [h,e],
 exact (mul_self_inj_of_nonneg hv hf).mp sq
end

theorem cap_news_energy (q p : ℝ) :
 (∫ x in (-1:ℝ)..1,(q*(12*x^2-4)+p*(4*x^3-4*x))^2)=128/5*q^2+256/105*p^2 :=
begin
 let L := λ x:ℝ,(16*q^2)*x^1+(16*q*p)*x^2+(((16*p^2-96*q^2)/3))*x^3+((-32*p*q))*x^4+(((144*q^2-32*p^2)/5))*x^5+(16*p*q)*x^6+((16*p^2/7))*x^7,
 let j := λ x:ℝ,(q*(12*x^2-4)+p*(4*x^3-4*x))^2,
 have dj : ∀x∈uIcc (-1:ℝ) 1,has_deriv_at L (j x) x,
 { intros x hx, dsimp only [L,j], convert ((((((((has_deriv_at_pow 1 x).const_mul (16*q^2)).add ((has_deriv_at_pow 2 x).const_mul (16*q*p))).add ((has_deriv_at_pow 3 x).const_mul (((16*p^2-96*q^2)/3)))).add ((has_deriv_at_pow 4 x).const_mul ((-32*p*q)))).add ((has_deriv_at_pow 5 x).const_mul (((144*q^2-32*p^2)/5)))).add ((has_deriv_at_pow 6 x).const_mul (16*p*q))).add ((has_deriv_at_pow 7 x).const_mul ((16*p^2/7)))) using 1; norm_num; ring },
 have cont : continuous j := by {dsimp [j],continuity},
 change (∫ x in (-1:ℝ)..1,j x)=_,
 rw [interval_integral.integral_eq_sub_of_has_deriv_at dj (cont.interval_integrable _ _)],
 dsimp [L],ring
end
theorem cap_symplectic_area :
 (∫ x in (-1:ℝ)..1,(4*x^3-4*x)^2-(1-x^2)^2*(12*x^2-4))=512/105 :=
begin
 let L := λ x:ℝ,(4)*x^1+((-4/3:ℝ))*x^3+((-4/5:ℝ))*x^5+((4/7:ℝ))*x^7,
 let j := λ x:ℝ,(4*x^3-4*x)^2-(1-x^2)^2*(12*x^2-4),
 have dj : ∀x∈uIcc (-1:ℝ) 1,has_deriv_at L (j x) x,
 { intros x hx, dsimp only [L,j], convert (((((has_deriv_at_pow 1 x).const_mul (4)).add ((has_deriv_at_pow 3 x).const_mul ((-4/3:ℝ)))).add ((has_deriv_at_pow 5 x).const_mul ((-4/5:ℝ)))).add ((has_deriv_at_pow 7 x).const_mul ((4/7:ℝ)))) using 1; norm_num; ring },
 have cont : continuous j := by {dsimp [j],continuity},
 change (∫ x in (-1:ℝ)..1,j x)=_,
 rw [interval_integral.integral_eq_sub_of_has_deriv_at dj (cont.interval_integrable _ _)],
 dsimp [L],ring
end

theorem cap_energy_normalization (R q p : ℝ) (h : R≠0) :
 (5*R/16)^2*R*(128/5*(q/R^2)^2+256/105*(p/R)^2)
 =5*q^2/(2*R)+5*R*p^2/21 := by {field_simp [h];ring}

theorem cap_canonical_normalization (R : ℝ) (h : R≠0) :
 (5*R/16)^2/R*(512/105)=10*R/21 := by {field_simp [h];ring}

theorem shielded_pair (a b : ℝ) (hb : b≠0) : a^2-(a/b)^2*b^2=0 ∧
 -a^4/42-(a/b)^2*(-b^4/42)=a^2*(b^2-a^2)/42 := by {split;field_simp [hb];ring}

-- Gauss--Bonnet, compact flux integrality and the monopole Dirac spectrum
-- provide the geometric inputs. The variation and charge selection rules follow.
theorem euler_flux (Q g : ℤ) (constraint : 2*Q+(2-2*g)=0) : Q=g-1 := by linarith

theorem common_genus (q r g : ℤ) (l : 2*q+(2-2*g)=0) (h : 2*r+(2-2*g)=0) :
 q-r=0 := by omega

theorem neutral_cap (j : ℤ) : 2*j+(-2)=0 ↔ j=1 := by omega

theorem neutral_birth (j : ℤ) : 2*j+2=0 ↔ j= -1 := by omega

theorem degree_obstructs_regular_ball (q : ℤ) (surface : 2*q+2=0)
 (smooth_extension : q=0) : false := by omega

theorem level_ratio (k q : ℤ) (unit_charge : k*(-1)+2*q=0) : k=2*q := by linarith

theorem singlet_overlap {E : Type*} [normed_add_comm_group E] [inner_product_space ℂ E]
 (g f : E) (h : ‖f‖=1) (w : ℝ) (norm_on_cap : ‖g‖^2=w) :
 ‖@inner ℂ E _ g f‖^2≤w :=
begin
 have hh := norm_inner_le_norm g f,
 rw [h,mul_one] at hh, rw [←norm_on_cap],
 exact pow_le_pow_of_le_left (norm_nonneg _) hh 2
end

theorem two_flavour_count : nat.choose 1 0=1 ∧ nat.choose 1 1=1 ∧ nat.choose 2 1=2 :=
by norm_num [nat.choose]

theorem curvature_disk_phase (left waist : ℝ) (hl : left=1) (hw : waist=0) :
 -(2*real.pi*(left-waist))/2= -real.pi := by {rw [hl,hw],ring}

theorem waist_negative (L a β : ℝ) (hl : 0<L) (ha : 0<a) (hb : 1/3<β) :
 -(3*β-1)/(L*a)<0 := div_neg_of_neg_of_pos (by linarith) (mul_pos hl ha)

theorem curvature_shear_bound (k₁ k₂ K A a : ℝ)
 (gauss : k₁*k₂=K-A) (lower : a≤A) : 4*(a-K)≤(k₁-k₂)^2 :=
by nlinarith only [gauss,lower,sq_nonneg (k₁+k₂)]

theorem round_waist_bound (L a : ℝ) (hl : L≠0) (ha : a≠0) :
 4*L^2*(-3/(8*L^2)+(3*(1-a/L)-1)/(L*a))=4*(2*L/a-27/8) :=
by {field_simp [hl,ha];ring}

theorem isotropic_exclusion (k K A : ℝ) (g : k*k=K-A) : A≤K :=
by nlinarith only [g,sq_nonneg k]

theorem moving_waist_density (k v a m r : ℝ) (ha : a≠0) (hr : r≠0)
 (normal : (a*k)^2-v^2=1-2*m*a^2/r^3) :
 k^2=(1+v^2)/a^2-2*m/r^3 :=
begin
 field_simp [hr] at normal, field_simp [hr,ha], nlinarith only [normal]
end

theorem uniform_exclusion_polynomial (x : ℝ) (hx : 0<x)
 (required : 1/x^2-3/4≤3/(1+2*x)) : 0≤6*x^3+15*x^2-8*x-4 :=
begin
 have den : 0<1+2*x := by linarith,
 have positive := mul_le_mul_of_nonneg_right ((le_div_iff den).1 required) (sq_nonneg x),
 have cancel : ((1/x^2-3/4)*(1+2*x))*x^2=(1-3*x^2/4)*(1+2*x) :=
 by {field_simp [ne_of_gt hx];ring},
 rw [cancel] at positive, nlinarith only [positive]
end

theorem no_genuine_waist (x : ℝ) (hx : 0<x) (waist : x≤2/3) :
 6*x^3+15*x^2-8*x-4<0 :=
begin
 have h1 : x*x≤(2/3)*x := mul_le_mul_of_nonneg_right waist hx.le,
 have h2 : x*x*x≤(2/3)*x*x := mul_le_mul_of_nonneg_right h1 hx.le,
 nlinarith only [h1,h2,waist]
end

end tidal_memory_release
