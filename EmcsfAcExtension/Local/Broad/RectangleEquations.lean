module

public import EmcsfAcExtension.Local.Broad.RectangleState
public import EmcsfAcExtension.Infra.Null.IntegralForm

/-! # Literal full-system characteristic equations on positive rectangles

All source components come from the frozen characteristic integral
identities. Neither transverse derivatives nor normalized envelopes enter.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local.Broad

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

/-- Pair two characteristic integral equations, with no change of constants
or assumptions on the derivatives at their endpoints. -/
theorem integralForm_prod {a b : ℝ} {f g : ℝ → X} {h k : ℝ → Y}
    (hf : IntegralForm f g a b) (hh : IntegralForm h k a b) :
    IntegralForm (fun x => (f x, h x)) (fun x => (g x, k x)) a b := by
  refine ⟨⟨hf.1.1.prodMk hh.1.1, hf.1.2.prodMk hh.1.2⟩, ?_⟩
  rw [intervalIntegral, integral_pair hf.1.1 hh.1.1,
    integral_pair hf.1.2 hh.1.2]
  exact Prod.ext hf.2 hh.2

/-- The incoming block satisfies the literal frozen incoming equations
on every prefix of a positive-radius rectangle. -/
theorem rectangle_in_integralForm {e a b c d : ℝ} {S : Fields}
    (hpos : b < c) (hS : IsSolution e S (Icc a b ×ˢ Icc c d))
    {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc c d) :
    IntegralForm (fun x => (rectangle_state S (x, v)).1)
      (fun x => rectangle_in_source e (rectangle_state S (x, v))) a u := by
  have hs : inSeg a u v ⊆ Icc a b ×ˢ Icc c d := by
    rintro p ⟨hx, hy, rfl⟩
    exact ⟨⟨hx, hy.trans hu.2⟩, hv⟩
  have hi := hS.eq_in a u v hu.1 (hu.2.trans_lt (hpos.trans_le hv.1)) hs
  simp_rw [rectangle_in_source_state]
  simpa only [rectangle_state] using
    integralForm_prod hi.2.1 hi.2.2.2.2.2

/-- The outgoing block contains all seven outgoing equations, including
the Maxwell charge and potential constraints, on every rectangle prefix. -/
theorem rectangle_out_integralForm {e a b c d : ℝ} {S : Fields}
    (hpos : b < c) (hS : IsSolution e S (Icc a b ×ˢ Icc c d))
    {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc c d) :
    IntegralForm (fun y => (rectangle_state S (u, y)).2)
      (fun y => rectangle_out_source e (rectangle_state S (u, y))) c v := by
  have hs : outSeg u c v ⊆ Icc a b ×ˢ Icc c d := by
    rintro p ⟨rfl, hx⟩
    exact ⟨hu, hx.1, hx.2.trans hv.2⟩
  have ho := hS.eq_out u c v (hu.2.trans_lt hpos) hv.1 hs
  simp_rw [rectangle_out_source_state]
  simpa only [rectangle_state] using
    integralForm_prod ho.1 (integralForm_prod ho.2.1 (integralForm_prod ho.2.2.1
      (integralForm_prod ho.2.2.2.1 (integralForm_prod ho.2.2.2.2.1
        (integralForm_prod ho.2.2.2.2.2.1 ho.2.2.2.2.2.2)))))

end EmcsfAcExtension.Local.Broad
