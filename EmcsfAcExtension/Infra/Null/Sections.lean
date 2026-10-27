/- Copyright (c) 2026. All rights reserved. -/

module

public import EmcsfAcExtension.Infra.Null.Segments

/-! # Continuity and uniform convergence on characteristic sections -/

public section

open Set Filter

namespace EmcsfAcExtension

variable {E : Type*} {a b u v₁ v₂ u₁ u₂ v : ℝ}

/-- Restrict a continuous field to any incoming segment contained in the triangle. -/
theorem continuousOn_incoming [TopologicalSpace E] {f : ℝ → ℝ → E}
    (hf : ContinuousOn (Function.uncurry f) (triangle a b))
    (hs : inSeg u₁ u₂ v ⊆ triangle a b) :
    ContinuousOn (fun u => f u v) (Icc u₁ u₂) := by
  apply hf.comp (continuous_id.prodMk continuous_const).continuousOn
  intro x hx
  exact hs ⟨hx.1, hx.2, rfl⟩

end EmcsfAcExtension
