module

public import EmcsfAcExtension.Local.Limit.Inputs
public import EmcsfAcExtension.Local.Defs.Limit
public import EmcsfAcExtension.Local.Assembly.Inputs
import EmcsfAcExtension.Local.Limit.StabilitySettings
import EmcsfAcExtension.Local.Limit.StabilityPassage

/-! # Stability of the constructed AC limit class

The internal project record statement, conditional only on the authorized full
classical comparison input. Existing constructed-limit witnesses supply
their own approximants; whole-triangle existence is not a premise of this
stability implication. internal project record L1/L2, charged_SF_new_version.tex:L6477–L6482.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local

/-- [internal]
The exact architecture stability statement for constructed limits, from the
pending full C¹ comparison theorem. The positive thresholds and constant
are universal: independent of time, coupling, both data and both limits.
All common-setting, smooth-comparison and limit-passage premises are
discharged inside the proof. No general-AC sequence node is used. -/
theorem limit_class_stability_of_inputs (hstab : StabExtendedStmt) :
    LimitClassStabilityStmt := by
  obtain ⟨η, C, hη, hC, hcomp⟩ := hstab 1 (by norm_num)
  obtain ⟨ε, δ, q, hε, hδ, _, ht⟩ := comparison_tails_of_constructed_limits η hη
  refine ⟨ε, δ, C, hε, hδ, hC, ?_⟩
  intro T e h₁ h₂ S₁ S₂ hT hac₁ hd₁ he₁ hac₂ hd₂ he₂ hc₁ hc₂
  obtain ⟨Sn₁, Sn₂, hn₁, hn₂, M, hs₁, hs₂, hl₁, hl₂, hdist, hsmall⟩ :=
    ht T e h₁ h₂ S₁ S₂ hT hac₁ hd₁ he₁ hac₂ hd₂ he₂ hc₁ hc₂
  exact stab_conclusion_of_smooth_bounds hC.le hl₁ hl₂ hs₁ hs₂ hdist
    (fun n => hcomp T e q M (Sn₁ n) (Sn₂ n) (hn₁ n) (hn₂ n) (hs₁ n) (hs₂ n) hsmall)

end EmcsfAcExtension.Local
