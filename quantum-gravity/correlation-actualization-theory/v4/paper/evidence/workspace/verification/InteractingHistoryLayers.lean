import analysis.inner_product_space.basic
import tactic

noncomputable theory
namespace interacting_history_layers

-- Born normalization of the two outgoing branches. V is isometric on the transfer output.
theorem formation_norm {E F : Type*} [normed_add_comm_group E] [inner_product_space ℝ E]
 [normed_add_comm_group F] (formed other incoming : E) (lifted : F)
 (U : ‖formed+other‖=‖incoming‖) (orth : inner formed other=(0:ℝ))
 (V : ‖lifted‖=‖formed‖) : ‖lifted‖^2+‖other‖^2=‖incoming‖^2 :=
by rw [V,←U,norm_add_sq_real,orth];ring

theorem four_quanta (w : ℝ) : 1*w+3*w=2*w+2*w := by ring

-- A direct sum in which only one layer acts cannot generate an interaction density.
theorem exclusive_source (x y : ℝ) (h : x=0 ∨ y=0) : x*y=0 := mul_eq_zero.mpr h

theorem square_displacement (w p x J : ℝ) (hw : 0<w) :
 w*(p^2+(x+J/w)^2)-J^2/w = w*(p^2+x^2)+2*J*x :=
by field_simp [ne_of_gt hw];ring

-- The two real components of each j are its real and imaginary parts.
def shift (h w ar ai br bi x y : ℝ) :=
 -h*((ar*x+br*y)^2+(ai*x+bi*y)^2)/w

theorem mutual_energy (h w ar ai br bi x y : ℝ) :
 shift h w ar ai br bi x y-shift h w ar ai br bi x 0-shift h w ar ai br bi 0 y
 = -2*h*(ar*br+ai*bi)*x*y/w :=
by unfold shift;ring

theorem mixed_work (h w ar ai br bi x y u v : ℝ) :
 shift h w ar ai br bi (x+u) (y+v)-shift h w ar ai br bi (x+u) y
 -shift h w ar ai br bi x (y+v)+shift h w ar ai br bi x y
 = -2*h*(ar*br+ai*bi)*u*v/w :=
by unfold shift;ring

theorem mode_normalization (s : ℝ) (hs : 0≤s) (hs' : s≤1) :
 (real.sqrt s)^2+(real.sqrt (1-s))^2=1 :=
by rw [real.sq_sqrt hs,real.sq_sqrt (sub_nonneg.mpr hs')];ring

theorem mode_overlap (s : ℝ) (hs : 0≤s) :
 real.sqrt s*real.sqrt s+real.sqrt (1-s)*0+0*real.sqrt (1-s)=s :=
by rw [real.mul_self_sqrt hs];ring

theorem shared_and_resolved (s η : ℝ) (hs : 0<s) (hs' : s<1) (hη : 0<η) :
 0<s ∧ 0<η*(1-s) := ⟨hs,mul_pos hη (sub_pos.mpr hs')⟩

theorem equal_receipt (s η₁ η₂ : ℝ) (h : s<1) :
 η₁*(1-s)=η₂*(1-s) ↔ η₁=η₂ :=
begin
 split,
 { intro hh, have hmul : (η₁-η₂)*(1-s)=0 := by linarith only [hh],
   exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right (ne_of_gt (sub_pos.mpr h))) },
 { intro hh,rw [hh] }
end

-- The common and the uncollected exclusive modes carry all of the missed signal.
theorem receive_only (s η : ℝ) :
 s+(1-η)*(1-s)=1-η*(1-s) := by ring

theorem missed_overlap (s p : ℝ) (hp : p<1) :
 (1-p)*(s/(1-p))=s :=
by field_simp [ne_of_gt (sub_pos.mpr hp)];ring

theorem passive_invariant (pA pB s vA vB : ℝ)
 (hA : (1-pA)*vA=s) (hB : (1-pB)*vB=s) :
 (1-pA)*vA=(1-pB)*vB := hA.trans hB.symm

-- Retarded support and the physical response profiles must be supplied by the field theory.
def force (p h k' x₁ x₂ qblank qmark : ℝ) :=
 (1-p)*(2*h*k'*x₁*(x₂+qblank))+p*(2*h*k'*x₁*(x₂+qmark))

theorem feedback_difference (pA pB h k' x₁ x₂ qblank qmark : ℝ) :
 force pA h k' x₁ x₂ qblank qmark-force pB h k' x₁ x₂ qblank qmark
 =2*h*k'*x₁*(qmark-qblank)*(pA-pB) := by unfold force;ring

theorem no_retarded_path (p h x₁ x₂ qblank qmark : ℝ) :
 force p h 0 x₁ x₂ qblank qmark=0 := by unfold force;ring

theorem identical_stress (pA pB h k' x₁ x₂ q : ℝ) :
 force pA h k' x₁ x₂ q q=force pB h k' x₁ x₂ q q := by unfold force;ring

end interacting_history_layers
