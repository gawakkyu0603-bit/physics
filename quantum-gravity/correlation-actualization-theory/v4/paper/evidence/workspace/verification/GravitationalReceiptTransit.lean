import analysis.special_functions.integrals
import tactic

noncomputable theory
namespace gravitational_receipt_transit

theorem time_scale (L c : ℝ) (hc : c≠0) : (L/c)*c=L := by field_simp

theorem weak_port (a b : ℝ) (h : a+b+1≠0) :
 (2/(1+a+b)-1)^2 = (1-2/(1+a+b))^2 := by ring

theorem escape_rate (L : ℝ) (h : L≠0) :
 1-(1-2/L)^2=4*(L-1)/L^2 := by {field_simp,ring}

theorem real_geometric (r c : ℝ) (nonzero : (1-r)^2+2*r*(1-c)≠0) :
 ((1-r)*(c-r))/((1-r)^2+2*r*(1-c))=
 (1-r)*((1-r)-(1-c))/((1-r)^2+2*r*(1-c)) := by ring

theorem upper_by_gap (r l : ℝ) (hr : 0≤r) (rc : r<1) (hl : 0≤l) :
 (1-r)*((1-r)-l)/((1-r)^2+2*r*l)≤(1-r)^2/((1-r)^2+2*r*l) :=
begin apply div_le_div_of_le, nlinarith [sq_nonneg (1-r),mul_nonneg hr hl],
 nlinarith [mul_nonneg (sub_nonneg.mpr rc.le) hl] end

theorem junction_energy (energy length tension c L : ℝ) (he : 2≤L)
 (hl : 0≤length) (ht : 0<tension) (hc : 0<c)
 (cap : length*tension*L≤energy) :
 2*length/(c*(4*(L-1)/L^2)) ≤ energy/(c*tension) :=
begin
 have hL : 0<L := by linarith,
 have hb : 0<L-1 := by linarith,
 have hn : 0<c*(4*(L-1)/L^2) := by positivity,
 apply (div_le_div_iff hn (mul_pos hc ht)).2,
 have he0 : 0≤energy := le_trans (mul_nonneg (mul_nonneg hl ht.le) hL.le) cap,
 have hq : energy*(c*(4*(L-1)/L^2))=energy*(4*c*(L-1))/L^2 := by ring,
 rw [hq],apply (le_div_iff (show 0<L^2,by positivity)).2,
 have hcap:=mul_le_mul_of_nonneg_right cap (show 0≤4*c*(L-1),by positivity),
 have more:=mul_nonneg (show 0≤2*length*c*tension*L,by positivity) (show 0≤L-2,by linarith),
 nlinarith only [hcap,more]
end

theorem charge_differences (w v x y : ℝ) :
 w*v*x+(w*v)*y=w*v*(x+y) := by ring

theorem repeated_bound (q r : ℝ) (K m : ℕ) (error fail : ℝ)
 (bound : error≤3*q^K) (deadline : fail≤(K:ℝ)*r^m) :
 error+fail≤3*q^K+(K:ℝ)*r^m := add_le_add bound deadline

end gravitational_receipt_transit
