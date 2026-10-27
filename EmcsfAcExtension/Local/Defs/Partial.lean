module

public import Mathlib

/-! # Partial derivatives within a domain

Literal internal definitions from internal project record and
`source/charged_SF_new_version.tex`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Partial derivative in the incoming coordinate `u`, within the domain `D`. -/
noncomputable def pdU (D : Set (ℝ × ℝ)) (f : ℝ → ℝ → E) (u v : ℝ) : E :=
  fderivWithin ℝ (Function.uncurry f) D (u, v) (1, 0)

/-- Partial derivative in the outgoing coordinate `v`, within the domain `D`. -/
noncomputable def pdV (D : Set (ℝ × ℝ)) (f : ℝ → ℝ → E) (u v : ℝ) : E :=
  fderivWithin ℝ (Function.uncurry f) D (u, v) (0, 1)

end EmcsfAcExtension.Local
