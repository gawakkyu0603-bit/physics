import tactic
import analysis.special_functions.integrals
import data.complex.basic

noncomputable theory
open_locale big_operators
namespace preterminal_matching

-- For the two multiplication arrows a column Y_k consists of X_k padded
-- with a zero below, and the next column is X_k padded above. Extend by zero
-- beyond the allowed row indices. These are precisely the two link equations.
def column_law (Y : ℕ → ℤ → ℂ) (n : ℕ) :=
 ∀ k<n, ∀ r:ℤ, Y (k+1) (r+1)=Y k r
def supported (Y : ℕ → ℤ → ℂ) (m n : ℕ) :=
 ∀ k≤n, ∀ r:ℤ, r<0 ∨ (m:ℤ)<r → Y k r=0

theorem shifted_column (Y : ℕ → ℤ → ℂ) (n : ℕ) (h : column_law Y n) :
 ∀ k≤n, ∀ r:ℤ,Y k (r+(k:ℤ))=Y 0 r :=
begin
 intro k,induction k with k ih,
 {intros hk r,simp},
 {intros hk r,have ht : k<n := by omega,
  rw [nat.cast_succ,←add_assoc,h k ht,ih (le_of_lt ht)]}
end

theorem first_column_support (Y : ℕ → ℤ → ℂ) (n m : ℕ)
 (h : column_law Y n) (hs : supported Y m n) (r : ℤ)
 (ho : r<0 ∨ (m:ℤ)-(n:ℤ)<r) : Y 0 r=0 :=
begin
 cases ho with neg big,
 {exact hs 0 (nat.zero_le _) r (or.inl neg)},
 {rw [← shifted_column Y n h n (le_refl _) r],
  exact hs n (le_refl _) _ (or.inr (by linarith))}
end

theorem column_formula (Y : ℕ → ℤ → ℂ) (n : ℕ) (h : column_law Y n)
 (k : ℕ) (hk : k≤n) (r : ℤ) : Y k r=Y 0 (r-(k:ℤ)) :=
by {have t:=shifted_column Y n h k hk (r-(k:ℤ)),simpa only [sub_add_cancel] using t}

theorem closed_link (Y : ℕ → ℤ → ℂ) (n m : ℕ) (hm : m<n)
 (h : column_law Y n) (hs : supported Y m n) (k : ℕ) (hk : k≤n)
 (r : ℤ) : Y k r=0 :=
begin
 rw [column_formula Y n h k hk r],apply first_column_support Y n m h hs,
 have hm' : (m:ℤ)<(n:ℤ) := by exact_mod_cast hm,
 by_cases h0 : r-(k:ℤ)<0, {exact or.inl h0}, {right,linarith}
end

theorem matched_link (Y : ℕ → ℤ → ℂ) (n : ℕ) (h : column_law Y n)
 (hs : supported Y n n) (k : ℕ) (hk : k≤n) (r : ℤ) :
 Y k r=if r=(k:ℤ) then Y 0 0 else 0 :=
begin
 rw [column_formula Y n h k hk r],split_ifs with eq,
 {rw [eq,sub_self]},
 {apply first_column_support Y n n h hs,
  rw [sub_self],by_cases neg : r<(k:ℤ),{left,linarith},{right,omega}}
end

theorem column_from_polynomial (a : ℤ → ℂ) (n : ℕ) :
 column_law (λ k r,a (r-(k:ℤ))) n :=
by {intros k hk r,dsimp,rw [nat.cast_add,nat.cast_one],congr' 1,ring}
theorem polynomial_fits (a : ℤ → ℂ) (m n : ℕ)
 (ha : ∀ r:ℤ, r<0 ∨ (m:ℤ)-(n:ℤ)<r → a r=0) :
 supported (λ k r,a (r-(k:ℤ))) m n :=
begin
 intros k hk r hr,dsimp,apply ha,
 have hk' : (k:ℤ)≤(n:ℤ) := by exact_mod_cast hk,
 have hzero : (0:ℤ)≤(k:ℤ) := by exact_mod_cast (nat.zero_le k),
 cases hr with neg big,{left,linarith},{right,linarith}
end
theorem link_euler (m n : ℤ) : (m*n+(m+1)*(n+1))-2*n*(m+1)=m-n+1 := by ring
theorem schwinger_casimir (m n j : ℝ) :
 m+n+(m-1)*(n-1)/2+((m^2-1)+(n^2-1))/4-j*(j+1)
 =(m+n)*(m+n+2)/4-j*(j+1) := by ring
theorem first_pair (n : ℝ) :
 ((n-1+n)*(n-1+n+2))/4-(1/2)*(1/2+1)=n^2-1 := by ring
theorem soft_gap (n : ℝ) (hn : 1≤n) :
 n-real.sqrt(n^2-1)=1/(n+real.sqrt(n^2-1)) :=
begin
 have t : 0≤n^2-1 := by nlinarith [mul_nonneg (sub_nonneg.2 hn) (show 0≤n+1,by linarith)],
 have hpos : 0<n+real.sqrt(n^2-1) := by linarith [real.sqrt_nonneg (n^2-1)],
 apply (eq_div_iff (ne_of_gt hpos)).2,nlinarith [real.sq_sqrt t]
end
theorem rank_balance (n : ℤ) : (n-1)+n+2=n+(n+1) := by ring
theorem undistinguished_spin (n a : ℝ) (hn : n≠0) : a/n+(n-a)/n=1 :=
by {field_simp [hn];ring}
theorem full_swap : real.cos (real.pi/2)=0 ∧ real.sin (real.pi/2)=1 :=
⟨real.cos_pi_div_two,real.sin_pi_div_two⟩

-- Primary and daughter have invariant masses squared s and s-2 M ω.
theorem mass_recoil (M ω : ℝ) : (M-ω)^2-ω^2=M^2-2*M*ω := by ring
theorem lightcone_area (G p E : ℝ) : 4*real.pi*G*(2*p*E)=8*real.pi*G*p*E := by ring
theorem entropy_curvature (s a p d ds : ℝ)
 (hs : s≠0) (ha : a≠0) (hd : s*d=(p-1)*a) (hds : ds=2*s*d/a) :
 ds=2*(p-1) := by {rw [hds],field_simp [ha],linear_combination 2*hd}
theorem phase_curvatures : 2*((9/14:ℝ)-1)= -5/7 ∧ 2*((1/2:ℝ)-1)= -1 :=
by norm_num
theorem word_spacing (d n : ℝ) (hd : 0<d) (hn : 0<n) :
 real.log (d*n)-real.log n = real.log d := by rw [real.log_mul hd.ne' hn.ne',add_sub_cancel]
theorem frequency_ratio (n m : ℝ) (hn : 0<n) (hm : 0<m) :
 real.exp (real.log n-real.log m)=n/m := by rw [real.exp_sub,real.exp_log hn,real.exp_log hm]
theorem fermi_weight (n m : ℝ) (hn : 0<n) (hm : 0<m) :
 m/(n+m)=1/(n/m+1) :=
by {field_simp [hm.ne',show n+m≠0,by linarith];ring}
theorem bose_weight (n m : ℝ) (h : m<n) (hm : 0<m) :
 m/(n-m)=1/(n/m-1) :=
by {field_simp [hm.ne',show n-m≠0,by linarith];ring}
theorem inverse_squared_amplitude (n m a : ℝ) (hn : 0<n) (hm : 0<m)
 (h : m*a=m/(n+m)) : a=1/(n+m) :=
begin
 apply (mul_left_cancel₀ hm.ne'),rw [h],ring
end
theorem inaccessible_number (t n m : ℝ) (ht : t≤1) (hm : 0≤m) (hn : 0<n) :
 t/(n+m)≤1/n :=
begin
 apply (div_le_div_iff (by linarith : 0<n+m) hn).2,
 nlinarith [mul_nonneg (sub_nonneg.2 ht) hn.le]
end
theorem photon_tail (t n m h : ℝ) (ht : t≤1) (h0 : h<n) (h1 : m≤h) :
 t/(n-m)≤1/(n-h) :=
begin
 apply (div_le_div_iff (by linarith : 0<n-m) (by linarith : 0<n-h)).2,
 nlinarith [mul_nonneg (sub_nonneg.2 ht) (sub_nonneg.2 h0.le)]
end

-- The log-weighted energy tail is the integral of log(1/z) up to h/n.
theorem tail_derivative (x : ℝ) (hx : 0<x) :
 has_deriv_at (λ z:ℝ,z*(1-real.log z)) (-real.log x) x :=
begin
 have h:=(has_deriv_at_id x).mul ((has_deriv_at_const x (1:ℝ)).sub (real.has_deriv_at_log hx.ne')),
 convert h using 1,dsimp,field_simp [hx.ne'];ring
end

-- Plus and minus extensions of a Hadamard row. Inducting on the bits gives
-- orthogonal real rows; the frozen-weight Gram diagonalizes by these rows.
theorem sign_pair (a b : ℝ) : a*b+(-a)*(-b)=2*(a*b) ∧ a*b+a*(-b)=0 :=
by {split;ring}
theorem four_cycle : (1:ℤ)*1*1*(-1)= -1 := by norm_num
theorem dark_difference (a b : ℝ) :
 (a-b)^2/2=(a^2+b^2)/2-a*b := by ring
theorem two_residues (even odd x y : ℝ) :
 even*(x+y)^2+odd*(x-y)^2 =
 (even+odd)*(x^2+y^2)+2*(even-odd)*x*y := by ring
theorem rate_for_equal_rows (w x y : ℂ) : w*x+w*y=w*(x+y) := by ring
theorem halo_entropy (S A B : ℝ) (h : S-B≤A) : S-2*B≤A-B := by linarith
theorem single_cell_fermi (u : ℝ) (hu : 0<u) :
 (u/(1+u))*(1-u/(1+u))=u/(1+u)^2 :=
by {field_simp [show 1+u≠0,by linarith]; try {left}; ring}
theorem single_cell_photon (u : ℝ) :
 2*((1-u)*u)*(1-u)=2*u*(1-u)^2 := by ring
theorem no_tag_product {ι : Type} (s : finset ι) (p : ι → ℝ)
 (h0 : ∀ i∈s,0≤p i) (h1 : ∀ i∈s,p i≤1) :
 ∏ i in s,(1-p i) ≤ real.exp (-(∑ i in s,p i)) :=
begin
 classical,
 rw [← finset.sum_neg_distrib,real.exp_sum],
 apply finset.prod_le_prod,
 {intros i hi, exact sub_nonneg.2 (h1 i hi)},
 {intros i hi,linarith [real.add_one_le_exp (-p i)]}
end
-- The no-write and all write outcomes exhaust the initially ready sector.
theorem complete_instrument (θ : ℝ) :
 real.cos θ ^ 2 + real.sin θ ^ 2 = 1 :=
by linarith [real.sin_sq_add_cos_sq θ]

theorem massive_recoil (M ω μ : ℝ) :
 (M-ω)^2-(ω^2-μ^2)=M^2+μ^2-2*M*ω := by ring
theorem daughter_threshold (M ω μ s : ℝ) (hM : 0<M)
 (h : s=M^2+μ^2-2*M*ω) : μ≤ω ↔ s≤(M-μ)^2 :=
begin
 have eq : (M-μ)^2-s=(2*M)*(ω-μ) := by rw [h]; ring,
 calc μ≤ω ↔ 0≤ω-μ : sub_nonneg.symm
 ... ↔ 0≤(2*M)*(ω-μ) : (mul_nonneg_iff_right_nonneg_of_pos (show 0<2*M,by linarith)).symm
 ... ↔ 0≤(M-μ)^2-s : by rw [eq]
 ... ↔ s≤(M-μ)^2 : sub_nonneg
end
theorem massive_index (G s t μ M ω : ℝ) (h : t=s+μ^2-2*M*ω) :
 8*real.pi*G*M*ω=(4*real.pi*G*s-4*real.pi*G*t)+4*real.pi*G*μ^2 :=
by rw [h];ring
theorem exponent_shift (x δ : ℝ) :
 real.exp (-x+δ)=real.exp (-x)*real.exp δ := real.exp_add _ _
theorem inclusive_lower {α : Type} (s : finset α) (w r l : α → ℝ)
 (hw : ∀ i∈s,0≤w i) (hr : ∀ i∈s,l i≤r i) :
 ∑ i in s,w i*l i ≤ ∑ i in s,w i*r i :=
finset.sum_le_sum (λ i hi,mul_le_mul_of_nonneg_left (hr i hi) (hw i hi))

-- The two radiation species each have an even and an odd parity-pair state.
-- Joint indices (a,b) and (c,d) label bra and ket. Both partial traces are
-- computed for every complex logical matrix, including its off-diagonals.
def pair_code (ρ : bool → bool → ℂ) (a b c d : bool) : ℂ :=
 if a=b ∧ c=d then ρ a c else 0
theorem joint_decoder (ρ : bool → bool → ℂ) (i j : bool) :
 pair_code ρ i i j j=ρ i j := by simp [pair_code]
theorem trace_gravity (ρ : bool → bool → ℂ) (i j : bool) :
 pair_code ρ i ff j ff + pair_code ρ i tt j tt=if i=j then ρ i j else 0 :=
by {cases i;cases j;simp [pair_code]}
theorem trace_photons (ρ : bool → bool → ℂ) (i j : bool) :
 pair_code ρ ff i ff j + pair_code ρ tt i tt j=if i=j then ρ i j else 0 :=
by {cases i;cases j;simp [pair_code]}
theorem lost_phase (ρ : bool → bool → ℂ) :
 pair_code ρ ff ff tt ff + pair_code ρ ff tt tt tt=0 :=
by simp [trace_gravity]

-- This eigenvector identity is independent of the number of daughters,
-- of their weights and of how many daughters occupy each residue.
theorem weighted_gram_eigen {ι κ : Type} [decidable_eq ι]
 (rows : finset ι) (modes : finset κ) (H : ι → ι → ℝ) (w : κ → ℝ)
 (res : κ → ι) (D : ℝ) (i t : ι)
 (orth : ∀ r, ∑ j in rows,H j r*H j t = if r=t then D else 0) :
 ∑ j in rows,(∑ m in modes,H i (res m)*w m*H j (res m))*H j t
 = H i t*(D*∑ m in modes,if res m=t then w m else 0) :=
begin
 classical,
 calc (∑ j in rows,(∑ m in modes,H i (res m)*w m*H j (res m))*H j t) = ∑ m in modes,∑ j in rows,(H i (res m)*w m)*(H j (res m)*H j t) :
      by {simp only [finset.sum_mul,mul_assoc]; try {rw [finset.sum_comm]}}
 ... = ∑ m in modes,(H i (res m)*w m)*(if res m=t then D else 0) :
      by {apply finset.sum_congr rfl,intros m hm,rw [←finset.mul_sum,orth]}
 ... = _ : by {simp only [finset.mul_sum],apply finset.sum_congr rfl,intros m hm,
                 by_cases h : res m=t; simp [h];ring}
end
-- Entropy or mutual-information data enter as explicit premises. The last
-- inequality is an interval obstruction even if the remaining core is returned.
theorem full_interval_budget (S0 Srest Hout : ℝ) (h : S0 ≤ Hout+Srest) :
 S0-Srest ≤ Hout := by linarith
theorem photon_budget_obstruction (Sin Srest Hout factor : ℝ)
 (hgap : Srest < Sin) (hfac : factor < 1)
 (hcap : Hout ≤ factor*(Sin-Srest)) : Hout+Srest < Sin :=
by nlinarith [mul_pos (sub_pos.2 hfac) (sub_pos.2 hgap)]
end preterminal_matching
