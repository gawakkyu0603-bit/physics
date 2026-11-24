import analysis.special_functions.integrals
import data.matrix.notation
import data.matrix.basic
import algebra.big_operators.order
import tactic

noncomputable theory
open_locale big_operators interval real matrix
open finset matrix measure_theory set

namespace boundary_exchange_recovery

theorem ward_vertex {α β : Type*} (ei : α→ℝ) (eo : β→ℝ) (V : β→α→ℂ)
 (p q : ℝ→ℂ) (cancel : ∀x,p x*q x=1)
 (conserve : ∀b a,eo b≠ei a→V b a=0) (b : β) (a : α) :
 p (eo b)*V b a*q (ei a)=V b a :=
begin
 by_cases h : eo b=ei a,
 {rw [h],calc p (ei a)*V b a*q (ei a)=(p (ei a)*q (ei a))*V b a : by ring
 ... = _ : by rw [cancel,one_mul] },
 {rw [conserve b a h],ring}
end

theorem pair_prob_real (x y : ℝ) : x^2+(-y)^2=x^2+y^2 := by ring

theorem local_double_mark {ι : Type*} [fintype ι] (p : ι→ℝ)
 (hp : ∀i,0≤p i) (cap : ∀i,p i≤1) (hn : ∑i,p i=1) :
 (∑i,p i^2)≤1 :=
begin rw [←hn],apply sum_le_sum,intros i hi,
 nlinarith only [mul_nonneg (hp i) (sub_nonneg.mpr (cap i))] end

theorem spectral_diagonal {ι : Type*} [fintype ι] [decidable_eq ι]
 (w : ι→ℝ) (hn : ∑i,w i=1) (v : ℝ) :
 (∑i, ∑j, w i*w j*(if j=i then (1:ℝ) else v)) =
 (∑i,w i^2)+(1-(∑i,w i^2))*v :=
begin
 have row : ∀i, (∑j, w i*w j*(if j=i then (1:ℝ) else v))=w i*v+(1-v)*w i^2,
 { intro i, have term : ∀j,w i*w j*(if j=i then (1:ℝ) else v)=
      (w i*v)*w j+(if i=j then (1-v)*w i^2 else 0),
   { intro j,by_cases h : j=i, {subst j,simp;ring}, {simp [h,ne.symm h];ring} },
   simp_rw [term],rw [sum_add_distrib,←mul_sum,hn],simp },
 simp_rw [row],rw [sum_add_distrib,←sum_mul,←mul_sum,hn],ring
end

theorem weighted_return {ι : Type*} [fintype ι] [decidable_eq ι]
 (w : ι→ℝ) (hw : ∀i,0≤w i) (hn : ∑i,w i=1) (φ : ι→ι→ℝ)
 (a b : ℝ) (diag : ∀i,φ i i=1) (off : ∀i j,i≠j→a≤φ i j ∧ φ i j≤b) :
 (∑i,w i^2)+(1-(∑i,w i^2))*a ≤ ∑i,∑j,w i*w j*φ i j ∧
 (∑i,∑j,w i*w j*φ i j) ≤ (∑i,w i^2)+(1-(∑i,w i^2))*b :=
begin
 rw [←spectral_diagonal w hn a,←spectral_diagonal w hn b],split,
 {apply sum_le_sum,intros i _,apply sum_le_sum,intros j _,
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hw i) (hw j)),
  by_cases h : j=i, {subst j,simp [diag]}, {simp [h,(off i j (ne.symm h)).1]}},
 {apply sum_le_sum,intros i _,apply sum_le_sum,intros j _,
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hw i) (hw j)),
  by_cases h : j=i, {subst j,simp [diag]}, {simp [h,(off i j (ne.symm h)).2]}}
end

theorem variance_write (v a R : ℝ) (h : 0≤v) (ha : 0≤a)
 (hw : 4/real.pi^2*(a^2*v)≤R) (s : ℝ) (hs : s≤v) :
 4/real.pi^2*(a^2*s)≤R :=
le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs (sq_nonneg a)) (by positivity)) hw

theorem one_photon_geometric (m cap : ℝ) (hm : 0≤m) (hc : m≤cap) :
 m/(1+cap)^2≤m/(1+m)^2 :=
begin
 apply div_le_div_of_le_left hm (show 0<(1+m)^2, by positivity),
 exact pow_le_pow_of_le_left (show 0≤1+m, by linarith) (show 1+m≤1+cap, by linarith) 2
end

theorem translating_kernel (source receiver shift : ℝ) :
 (source+shift)-(receiver+shift)=source-receiver := by ring

theorem bps_cancellation (h tension : ℝ) :
 tension*h⁻¹-tension*(h⁻¹-1)=tension := by ring

theorem warped_slope (c tail slope : ℝ) (hc : 0<c) (ht : tail<c)
 (h : c-tail≤slope) : 0<slope := by linarith

theorem exact_dispersion (h f : ℝ) (hpos : 0<h) :
 h*(f+1)-h*f=h := by ring

theorem one_port_overlap (p u v : ℝ) (trig : u^2+v^2=1) :
 u^2+((2*p-1)*v)^2 = 1-4*p*(1-p)*v^2 := by nlinarith only [trig]

theorem overlap_decay (z a : ℝ) (hz : 0≤z) (ha : 0≤a)
 (h : z^2=1-a) : a/2≤1-z :=
begin
 have hn := sq_nonneg (1-z),
 nlinarith only [hn,h]
end

theorem thermal_overlap (m z : ℝ) (hm : 0≤m) (hz : 0≤z) (hc : z≤1) :
 m*(1-z)/(1+m)≤real.log (1+m*(1-z)) :=
begin
 have hx : 0≤m*(1-z) := mul_nonneg hm (by linarith),
 have hpos : 0<1+m*(1-z) := by linarith,
 have base := real.log_le_sub_one_of_pos (inv_pos.mpr hpos),
 rw [real.log_inv] at base,
 have hdiv : m*(1-z)/(1+m*(1-z))=1-(1+m*(1-z))⁻¹ :=
   by field_simp [ne_of_gt hpos];ring,
 have hb : m*(1-z)/(1+m*(1-z))≤real.log (1+m*(1-z)) := by rw [hdiv];linarith,
 apply le_trans _ hb,
 apply div_le_div_of_le_left hx hpos,
 nlinarith only [mul_nonneg hm hz]
end

theorem single_photon_visibility (n g : ℝ) (hn : 0<n) (hg : 0≤g)
 (hc : g≤n) : n≤n+n^2-g^2 ∧ n+n^2-g^2≤n*(1+n) :=
begin
 have h:=pow_le_pow_of_le_left hg hc 2,
 constructor; nlinarith [sq_nonneg g]
end

theorem clicks_to_affinity (b p q : ℝ) (h : b^2+(p-q)^2≤1) :
 (p-q)^2/2≤1-b := by nlinarith [sq_nonneg (1-b)]

theorem decodable_tail {ι : Type*} (s : finset ι) (pr err : ι→ℝ) (a : ℝ)
 (h : ∀i∈s, a*pr i≤err i) :
 a*(∑i in s,pr i)≤∑i in s,err i :=
by rw [mul_sum];exact sum_le_sum h

theorem gram_cross {ι : Type*} [fintype ι] [decidable_eq ι] (v : ι→ℝ) :
 (∑i,∑j,if j=i then (0:ℝ) else 2*v i*v j)≤
 2*((fintype.card ι:ℝ)-1)*(∑i,v i^2) :=
begin
 have r : ∀i j, (if j=i then (0:ℝ) else 2*v i*v j)≤
   v i^2+v j^2-(if i=j then 2*v i^2 else 0),
 {intros i j,by_cases h : j=i, {subst j,simp;ring_nf}, {simp [h,ne.symm h],nlinarith [sq_nonneg (v i-v j)]}},
 calc (∑i,∑j,if j=i then (0:ℝ) else 2*v i*v j) ≤
   ∑i,∑j,(v i^2+v j^2-(if i=j then 2*v i^2 else 0)) :
     sum_le_sum (λ i hi,sum_le_sum (λ j hj,r i j))
 ... = _ : by simp_rw [sum_sub_distrib,sum_add_distrib];simp [nsmul_eq_mul,←mul_sum,fintype.card];ring
end

theorem exact_decoder {α β ι : Type*} [fintype α] [fintype β] [fintype ι]
 [decidable_eq ι] [decidable_eq α] (r : ι) (w : ι→ℂ)
 (W : ι→matrix β α ℂ) (D : matrix α β ℂ) (V : ι→matrix α α ℂ)
 (P : matrix α α ℂ) (isom : ∀j,D ⬝ W j=if r=j then 1 else 0)
 (rev : P ⬝ V r=1) :
 P ⬝ (D ⬝ (∑j,w j • (W j ⬝ V j))) = (w r) • 1 :=
begin
 rw [matrix.mul_sum],
 have ht : ∀j,D ⬝ (w j • (W j ⬝ V j))=if r=j then w j • V j else 0,
 {intro j,rw [matrix.mul_smul,←matrix.mul_assoc,isom],
  by_cases h : r=j; simp [h]},
 simp_rw [ht],simp [matrix.mul_smul,rev]
end

theorem gram_sqrt_margin (x delta : ℝ) (hd : 0≤delta) (hu : delta<1)
 (lo : 1-delta≤x) (hi : x≤1+delta) :
 1-delta≤real.sqrt x ∧ real.sqrt x≤1+delta :=
begin have hx : 0≤x := by linarith, have s:=real.sq_sqrt hx,have p:=real.sqrt_nonneg x,
 split,
 {by_contra hh, have hlt : real.sqrt x < 1-delta := lt_of_not_ge hh,
  have k:=mul_pos (sub_pos.mpr hlt) (show 0<1-delta+real.sqrt x,by linarith only [hu,p]),
  nlinarith only [k,s,lo,mul_nonneg hd (show 0≤1-delta,by linarith only [hu])]},
 {by_contra hh, have hlt : 1+delta < real.sqrt x := lt_of_not_ge hh,
  have k:=mul_pos (sub_pos.mpr hlt) (show 0<real.sqrt x+(1+delta),by linarith only [p,hd]),
  nlinarith only [k,s,hi,sq_nonneg delta,hd]}
end

theorem conditional_fidelity (bad submitted horizon : ℝ) (hh : 0<horizon)
 (h : horizon*bad≤submitted) : bad≤submitted/horizon :=
(le_div_iff hh).mpr (by linarith only [h])

theorem spin_odd_sum (d : ℕ) :
 (∑i in range d,(2*(i:ℝ)+1))=(d:ℝ)^2 :=
begin induction d with n ih, {simp},rw [sum_range_succ,ih],push_cast,ring end

theorem spin_square_sum (d : ℕ) :
 (∑i in range d,(2*(i:ℝ)+1)^2)=((d:ℝ)*(4*d^2-1))/3 :=
begin induction d with n ih, {simp},rw [sum_range_succ,ih],push_cast,ring end

theorem spin_collision (d : ℕ) (hd : 0<d) :
 (∑i in range d,((2*(i:ℝ)+1)/(d:ℝ)^2)^2)=
 (4*(d:ℝ)^2-1)/(3*(d:ℝ)^3) :=
begin
 have h : (d:ℝ)≠0 := by exact_mod_cast (ne_of_gt hd),
 simp_rw [div_pow],rw [←sum_div,spin_square_sum],field_simp [h];ring
end

theorem null_coordinate_density (u v : ℝ) (hv : v≠0) :
 (v-u/v)^2/v = v-2*u/v+u^2/v^3 := by field_simp [hv];ring

theorem binomial_jensen {ι : Type*} [fintype ι] (w mean : ι→ℝ)
 (m : ℝ) (h : ∀i,(mean i)^2≤w i) (hi : ∑i,w i≤m) :
 (∑i,(mean i)^2)≤m := le_trans (sum_le_sum (λ i _,h i)) hi

theorem structural_resolution (u v s a b δ : ℝ)
 (hl : abs (a-u)≤δ) (hr : abs (v-b)≤δ) (hc : abs (a-b)≤s) :
 abs (u-v)≤s+2*δ :=
begin
 have e : u-v=(u-a)+(a-b)+(b-v) := by ring,rw [e],
 have x:=abs_add (u-a+a-b) (b-v),
 calc abs ((u-a)+(a-b)+(b-v)) ≤ abs ((u-a)+(a-b))+abs (b-v) : abs_add _ _
 ... ≤ (abs (u-a)+abs (a-b))+abs (b-v) : add_le_add_right (abs_add _ _) _
 ... ≤ _ : by rw [abs_sub_comm u a,abs_sub_comm b v];linarith
end

theorem time_slice_square (l : ℝ) (h : 0<l) :
 (2:ℝ)*32^2*(1/2)^7/(7*l)=16/(7*l) := by norm_num;ring

theorem orbit_capacity (words orbits size : ℕ) (h : words≤orbits*size)
 (q : ℕ) (hs : 0<size) (hq : q*size≤words) : q≤orbits :=
begin by_contra bad, have strict := nat.mul_lt_mul_of_pos_right (lt_of_not_ge bad) hs,
 exact (not_lt_of_ge (le_trans hq h)) strict end

-- A fixed total forbids two distinct words from differing only at the erased site.
theorem fixed_type_slot {ι : Type*} [fintype ι] [decidable_eq ι]
 (a b : ι→ℕ) (i : ι) (same_total : ∑j,a j=∑j,b j)
 (same_others : ∀j,j≠i→a j=b j) : a i=b i :=
begin
 have same : (∑j in ((finset.univ : finset ι).erase i),a j)=∑j in ((finset.univ : finset ι).erase i),b j :=
 sum_congr rfl (λ j hj,same_others j (mem_erase.mp hj).1),
 have aa:=sum_erase_add univ a (mem_univ i),
 have bb:=sum_erase_add univ b (mem_univ i),
 omega
end

-- Slot transitivity on a fixed-content orbit enforces its one-slot diagonal.
theorem orbit_slot_marginal {ι κ : Type*} [fintype ι] [fintype κ]
 (value : κ→ι→ℝ) (m : ℝ) (type_fixed : ∀s,∑j,value s j=m)
 (i : ι) (rotate : ∀j,∃g : κ≃κ,∀s,value (g s) j=value s i) :
 (fintype.card ι:ℝ)*(∑s,value s i)=(fintype.card κ:ℝ)*m :=
begin
 have same : ∀j,(∑s,value s j)=∑s,value s i,
 {intro j,rcases rotate j with ⟨g,hg⟩,
  calc (∑s,value s j) = ∑s,value (g s) j : (g.sum_comp (λs,value s j)).symm
  ... = _ : sum_congr rfl (λs _,hg s)},
 calc (fintype.card ι:ℝ)*(∑s,value s i)=∑j:ι,∑s,value s i :
   by simp [nsmul_eq_mul,fintype.card]
 ... = ∑j:ι,∑s,value s j : sum_congr rfl (λj _,(same j).symm)
 ... = ∑s,∑j,value s j : sum_comm
 ... = _ : by simp [type_fixed,nsmul_eq_mul,fintype.card]
end

end boundary_exchange_recovery
