module

public import EmcsfAcExtension.Local.Defs.Params
public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Frozen.Fields.EqOn

import EmcsfAcExtension.Local.Broad.Propagation

/-! # Broad uniqueness for normalized restart data

The general entering-cone uniqueness theorem applies directly to two solutions
with the same restart datum and the prescribed axis gauge.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- [internal] Two broad solutions with the same normalized restart datum agree
on the full nondegenerate triangle. No smallness or envelope premise is required.
This specializes broad uniqueness; it does not close the constructed-competitor node. -/
theorem broad_uniqueness_restart {e T : ℝ} {h : ℝ → ℂ} {S₁ S₂ : Fields}
    (hT : 0 < T) (hS₁ : IsSolution e S₁ (triangle 0 T))
    (hS₂ : IsSolution e S₂ (triangle 0 T))
    (hd₁ : IsRestartData S₁ h T) (hd₂ : IsRestartData S₂ h T) :
    S₁.EqOn S₂ (triangle 0 T) := by
  apply broad_uniqueness hT hS₁ hS₂
  · intro v hv
    exact ⟨(hd₁.1 v hv).1.trans (hd₂.1 v hv).1.symm,
      (hd₁.1 v hv).2.trans (hd₂.1 v hv).2.symm⟩
  · intro t ht
    exact ⟨hd₁.2 t ht, hd₂.2 t ht⟩

end EmcsfAcExtension.Local
