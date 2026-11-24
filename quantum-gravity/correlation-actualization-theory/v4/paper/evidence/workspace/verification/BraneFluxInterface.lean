import data.real.sqrt
import algebra.geom_sum
import data.complex.basic
import analysis.special_functions.trigonometric.basic
import tactic

noncomputable theory
namespace brane_flux_interface

def energy (m p : ℝ) := real.sqrt (m^2 + p^2)

lemma energy_sq (m p : ℝ) : (energy m p)^2 = m^2 + p^2 :=
real.sq_sqrt (by positivity)

lemma energy_pos {m : ℝ} (hm : 0 < m) (p : ℝ) : 0 < energy m p :=
real.sqrt_pos.2 (by positivity)

theorem split_polynomial (M a b : ℝ) :
 ((energy M a + energy M b)^2-(a+b)^2)*((energy M a + energy M b)^2-(a-b)^2)
 = 4*M^2*(energy M a + energy M b)^2 :=
begin
  generalize ha : energy M a = A, generalize hb : energy M b = B,
  have hA := energy_sq M a, rw [ha] at hA,
  have hB := energy_sq M b, rw [hb] at hB,
  linear_combination (A^2 + 4*A*B + 6*B^2 - 3*M^2 - a^2 - 2*b^2)*(hA)
   + (B^2 + 4*A*B + 3*M^2 + 4*a^2 - b^2)*(hB)
end

-- Substitute X=t^2, C=(p1+p2)^2, d=(p1-p2)^2 in the two-body identity.
theorem spread_order (m C X Y d e : ℝ) (hm : 0≤m) (hC : 0≤C)
 (hx : C<X) (hy : C<Y) (hX : (X-C)*(X-d)=4*m^2*X)
 (hY : (Y-C)*(Y-e)=4*m^2*Y) (hde : d≤e) : X≤Y :=
begin
  by_contra h, have hyx : Y<X := lt_of_not_ge h,
  have hx' : 0<X-C := sub_pos.mpr hx,
  have hy' : 0<Y-C := sub_pos.mpr hy,
  have hz : 0 < (X-Y)*((X-C)*(Y-C)+4*m^2*C) :=
    mul_pos (sub_pos.mpr hyx) (add_pos_of_pos_of_nonneg (mul_pos hx' hy') (by positivity)),
  have hnon : 0≤(e-d)*(X-C)*(Y-C) := mul_nonneg (mul_nonneg (sub_nonneg.mpr hde) hx'.le) hy'.le,
  have hid : (X-Y)*((X-C)*(Y-C)+4*m^2*C)+(e-d)*(X-C)*(Y-C)=0 :=
    by linear_combination (Y-C)*hX-(X-C)*hY,
  linarith
end

theorem integer_nearest (k n : ℤ) :
 (1:ℤ) ≤ ((n-((2*k+1)-n))^2) :=
begin
  by_cases a : n≤k,
  { have h : (0:ℤ)≤(k-n)*(k-n+1) := mul_nonneg (by linarith) (by linarith), nlinarith },
  { have b : k+1≤n := by omega,
    have h : (0:ℤ)≤(n-k-1)*(n-k) := mul_nonneg (by linarith) (by linarith), nlinarith }
end

theorem time_like (M a b : ℝ) (hM : 0<M) :
 (a+b)^2 < (energy M a+energy M b)^2 :=
begin
  have hA := energy_pos hM a, have hB := energy_pos hM b,
  have h1 := energy_sq M a, have h2 := energy_sq M b,
  have h3 : |a|<energy M a := (sq_lt_sq.mp (show a^2<(energy M a)^2, by rw [h1];nlinarith)).trans_le
    (le_of_eq (abs_of_pos hA)),
  have h4 : |b|<energy M b := (sq_lt_sq.mp (show b^2<(energy M b)^2, by rw [h2];nlinarith)).trans_le
    (le_of_eq (abs_of_pos hB)),
  exact sq_lt_sq.mpr (by rw [abs_of_pos (add_pos hA hB)]; exact lt_of_le_of_lt (abs_add _ _) (add_lt_add h3 h4))
end

theorem split_closest (M m : ℝ) (hM : 0<M) (k n : ℤ) :
 energy M ((k:ℝ)*m) + energy M (((k:ℝ)+1)*m) ≤
 energy M ((n:ℝ)*m) + energy M ((2*(k:ℝ)+1-(n:ℝ))*m) :=
begin
  let a : ℝ := (k:ℝ)*m, let b : ℝ := ((k:ℝ)+1)*m,
  let c : ℝ := (n:ℝ)*m, let d : ℝ := (2*(k:ℝ)+1-(n:ℝ))*m,
  have hsum : a+b=c+d := by dsimp [a,b,c,d];ring,
  have hi : (1:ℝ) ≤ ((n:ℝ) - (2*(k:ℝ)+1-(n:ℝ)))^2 := by exact_mod_cast integer_nearest k n,
  have hd : (a-b)^2≤(c-d)^2 :=
  begin dsimp [a,b,c,d],convert mul_le_mul_of_nonneg_right hi (sq_nonneg m) using 1; ring end,
  have h1 := split_polynomial M a b, have h2 := split_polynomial M c d,
  have ht := time_like M a b hM, rw [hsum] at ht h1,
  have h := spread_order M ((c+d)^2) _ _ _ _ hM.le (sq_nonneg _) ht (time_like M c d hM) h1 h2 hd,
  have hh := sq_le_sq.mp h,
  rw [abs_of_pos (add_pos (energy_pos hM a) (energy_pos hM b)), abs_of_pos (add_pos (energy_pos hM c) (energy_pos hM d))] at hh,
  exact hh
end

theorem gap_rationalized (M m k : ℝ) (hM : 0<M) (hm : 0<m) (hk : 0≤k) :
 let a:=energy M (k*m), b:=energy M ((k+1)*m), parent:=energy (2*M) ((2*k+1)*m),
     dot:=M^2+k*(k+1)*m^2 in
 a+b-parent = 2*M^2*m^2/((a+b+parent)*(a*b+dot)) :=
begin
  dsimp only,
  have hA := energy_sq M (k*m), have hB := energy_sq M ((k+1)*m),
  have hP := energy_sq (2*M) ((2*k+1)*m),
  generalize ha : energy M (k*m) = A, rw [ha] at hA,
  generalize hb : energy M ((k+1)*m) = B, rw [hb] at hB,
  generalize hp : energy (2*M) ((2*k+1)*m) = W, rw [hp] at hP,
  have hpA : 0<A := ha ▸ energy_pos hM (k*m), have hpB : 0<B := hb ▸ energy_pos hM ((k+1)*m),
  have hpW : 0<W := hp ▸ energy_pos (show 0<2*M,by linarith) ((2*k+1)*m),
  let D := M^2+k*(k+1)*m^2,
  have hD : 0<D := by dsimp [D];positivity,
  change A+B-W = 2*M^2*m^2/((A+B+W)*(A*B+D)),
  have hnorm : (A*B)^2-D^2=M^2*m^2 :=
  begin rw [mul_pow,hA,hB],dsimp [D],ring end,
  have hsum : (A+B-W)*(A+B+W)=2*(A*B-D) := by dsimp [D]; linear_combination hA+hB-hP,
  have den1 : 0<A+B+W := add_pos (add_pos hpA hpB) hpW,
  have den2 : 0<A*B+D := add_pos (mul_pos hpA hpB) hD,
  apply (eq_div_iff (ne_of_gt (mul_pos den1 den2))).mpr,
  calc (A+B-W)*((A+B+W)*(A*B+D)) = ((A+B-W)*(A+B+W))*(A*B+D) : by ring
    ... = 2*(A*B-D)*(A*B+D) : by rw [hsum]
    ... = 2*M^2*m^2 : by linear_combination 2*hnorm
end

theorem odd_gap_positive (M m k : ℝ) (hM : 0<M) (hm : 0<m) (hk : 0≤k) :
 0< energy M (k*m)+energy M ((k+1)*m)-energy (2*M) ((2*k+1)*m) :=
begin
  have he := gap_rationalized M m k hM hm hk, dsimp only at he, rw [he],
  have h1 := energy_pos hM (k*m), have h2 := energy_pos hM ((k+1)*m),
  have h3 := energy_pos (show 0<2*M,by linarith) ((2*k+1)*m),
  exact div_pos (by positivity) (mul_pos (add_pos (add_pos h1 h2) h3) (add_pos (mul_pos h1 h2) (by positivity)))
end

theorem even_gap (M p : ℝ) : energy (2*M) (2*p)=2*energy M p :=
begin
 have h1 := energy_sq (2*M) (2*p),have h2 := energy_sq M p,
 have h3 : 0≤energy (2*M) (2*p) := real.sqrt_nonneg _,
 have h4 : 0≤energy M p := real.sqrt_nonneg _, nlinarith
end

theorem matrix_gap (k M R : ℝ) (hk : 0<k) :
 (M^2*R/2)*(1/k+1/(k+1)-4/(2*k+1)) =
 M^2*R/(2*(2*k+1)*k*(k+1)) :=
begin have h1 : k+1≠0 := by linarith, have h2 : 2*k+1≠0 := by linarith,
 field_simp [ne_of_gt hk,h1,h2];ring end

-- A component of the defect transport on an anticommuting source cannot
-- intertwine commuting target transports.  The target may have many rows.
theorem unmatched_row (r s u v : ℂ)
 (hx1 : s=u*r) (hx2 : r=u*s) (hz1 : r=v*r) (hz2 : -s=v*s) :
 r=0 ∧ s=0 :=
begin
 have ha : s=v*s := calc s=u*r : hx1
   ... = u*(v*r) : congr_arg ((*) u) hz1
   ... = v*(u*r) : by ring
   ... = v*s : by rw [←hx1],
 have hb : s=0 := by linear_combination (ha-hz2)/2,
 exact ⟨by rw [hx2,hb,mul_zero],hb⟩
end

theorem matched_matrix (a b c d : ℂ)
 (hx : a=d ∧ b=c) (hz : b= -b ∧ c= -c) : a=d ∧ b=0 ∧ c=0 :=
⟨hx.1,by linear_combination hz.1/2,by linear_combination hz.2/2⟩

theorem unordered (p : bool) : bnot (bnot p)=p := by cases p;refl

theorem twice_open_mode (L f : ℝ) (hL : 0<L) :
 2*(real.pi/(L*real.sqrt (1+f^2)))=4*real.pi/(2*L*real.sqrt (1+f^2)) :=
begin have hr : 0<real.sqrt (1+f^2) := real.sqrt_pos.2 (by positivity),
 field_simp [ne_of_gt hL,ne_of_gt hr];ring end

theorem screen_decomposition (a b d u v h : ℝ) (ht : a+d= -h) :
 let ext:=a^2+2*b^2+d^2, full:=ext+2*(u^2+v^2)+h^2 in
 (ext-h^2/2)+h^2+h^2/2+2*(u^2+v^2) = full :=
by dsimp;ring

theorem screen_cross (ext h2 v2 c : ℝ) :
 (ext + h2*c^2-h2/2)+h2/2+2*c*v2=ext+2*c*v2+h2*c^2 := by ring

theorem sky_weights :
 ((7/15:ℝ)-(2/15)/2=2/5) ∧ ((2/15:ℝ)/2=1/15) ∧
 (2*(1/5:ℝ)=2/5) ∧ ((2/5:ℝ)+2/15+1/15+2/5=1) := by norm_num

theorem width (G w : ℝ) (hw : w≠0) :
 ((2*G/5)*(2*w)^5/w^2)/(2/5)=4*G*(2*w)^3 := by field_simp;ring

theorem receipt_overlap :
 ((2/5:ℝ)+(2/5)*(9/13)=44/65) ∧
 ((2/5:ℝ)-(2/5)*(9/13)=8/65) ∧ ((8/65:ℝ)/(44/65)=2/11) ∧
 ((7+6*(-5/13:ℝ)+2*(-5/13)^2)/15=281/845) := by norm_num

theorem reception_peak (t : ℝ) :
 ((44/65:ℝ)*t)^2=(121/4)*((8/65)*t)^2 := by ring

theorem invariant_threshold (mass delta line : ℝ) (hm : mass+line≠0) :
 (mass+line)^2+2*(mass+line)*((delta-line)*(2*mass+delta+line)/(2*(mass+line)))=(mass+delta)^2 :=
by field_simp;ring

theorem critical_lapse (energy ratio : ℝ) :
 energy^2-ratio*(2*energy-ratio)=(energy-ratio)^2 := by ring

theorem doppler_inverse (energy speed z : ℝ) (hs : speed^2=energy^2-z^2) :
 (energy-speed)*(energy+speed)=z^2 := by nlinarith only [hs]

theorem complement_flux (captured transmitted : ℝ) (h : 0≤transmitted) (ht : transmitted≤captured) :
 0≤captured-transmitted ∧ transmitted+(captured-transmitted)=captured := ⟨sub_nonneg.mpr ht,by ring⟩

open_locale big_operators
theorem character_off (q : ℕ) (z : ℂ) (hq : z^q=1) (hz : z≠1) :
 (∑ j in finset.range q, z^j) = 0 :=
begin
 have h := geom_sum_mul z q, rw [hq, sub_self] at h,
 exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hz)
end

theorem character_on (q : ℕ) (hq : 0<q) :
 (∑ j in finset.range q, (1:ℂ)^j)/(q:ℂ)=1 :=
by simp [ne_of_gt hq]

theorem pair_difference (n d : ℤ) : (n+d)-(n-d)=2*d := by ring
theorem rank_two_blind (d : ℤ) : (2:ℤ)∣2*d := dvd_mul_right _ _
theorem rank_three_selective (d : ℤ) : (3:ℤ)∣2*d ↔ (3:ℤ)∣d :=
begin
 split,
 { rintro ⟨x,h⟩, use 2*x-d, linarith },
 { rintro ⟨x,h⟩, exact ⟨2*x,by linarith⟩ }
end
theorem matching_power (p p' : ℝ) (h : 0≤p) (hh : p≤1) (hp : p'=p*p) :
 1-p≤1-p' := by rw [hp];nlinarith [mul_nonneg h (sub_nonneg.mpr hh)]
theorem eikonal_coefficient (M v Q R b n K : ℝ) (hr : R≠0) (hb : b≠0) :
 (3*real.pi/64*M*v^3*Q)/(real.pi*R)*(2*n^2/(3*R^2*b^2))*K =
 M*v^3*Q*n^2*K/(32*R^3*b^2) := by field_simp [ne_of_gt real.pi_pos];ring

end brane_flux_interface
