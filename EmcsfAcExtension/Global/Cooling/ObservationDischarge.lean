module

public import EmcsfAcExtension.Global.Cooling.Main
public import EmcsfAcExtension.Global.Observation.Main

/-! # Unconditional charged cooling

The source observation theorem discharges the sole remaining input of
the landed cooling assembly. Source: charged_SF_new_version.tex:L2791–2870;
approved internal project record.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.Cooling

/-- [internal]
Discharge the literal observation interface from the proved source
observation proposition. All four constants depend only on `δ`, before
every solution, coupling, scalar background, radius and clock center.
There is no additional hypothesis. -/
theorem observation_input (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) : observationInput δ :=
  Observation.observation δ hδ

end EmcsfAcExtension.Global.Cooling

namespace EmcsfAcExtension.Global.Observation

end EmcsfAcExtension.Global.Observation
