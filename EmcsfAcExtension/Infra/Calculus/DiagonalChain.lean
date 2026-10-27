/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Infra.Calculus.PartialsC1

/-! # The diagonal chain rule within a closed triangle

internal project record infrastructure. The two coordinate partials add along the axis.
The formulas apply to curried fields by taking `f := Function.uncurry g`.
-/

public section

namespace EmcsfAcExtension

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative of the diagonal trace is the sum of the incoming and outgoing
domain partials, including the endpoints as within derivatives. -/
theorem hasDerivWithinAt_diagonal {a b t : ℝ} {f : ℝ × ℝ → E}
    (hf : ContDiffOn ℝ 1 f (triangle a b)) (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun s => f (s, s))
      (fderivWithin ℝ f (triangle a b) (t, t) (1, 0) +
        fderivWithin ℝ f (triangle a b) (t, t) (0, 1)) (Icc a b) t := by
  have hd := (hf.differentiableOn (by norm_num) (t, t) ⟨ht.1, le_rfl, ht.2⟩).hasFDerivWithinAt
  have h := hd.comp_hasDerivWithinAt
    (f := fun s => (s, s)) (s := Icc a b) t
    (((hasDerivAt_id t).prodMk (hasDerivAt_id t)).hasDerivWithinAt)
    (fun s hs => (show (s, s) ∈ triangle a b from ⟨hs.1, le_rfl, hs.2⟩))
  simpa only [show ((1, 1) : ℝ × ℝ) = (1, 0) + (0, 1) by ext <;> norm_num,
    map_add, Function.comp_def] using h

end EmcsfAcExtension
