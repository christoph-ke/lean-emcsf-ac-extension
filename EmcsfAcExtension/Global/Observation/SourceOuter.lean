module

public import EmcsfAcExtension.Global.Observation.SourceGeometry
public import EmcsfAcExtension.Global.Observation.SourceBoundary
public import EmcsfAcExtension.Global.Observation.CentralParameters
public import EmcsfAcExtension.Global.Observation.Static.OuterReference
public import EmcsfAcExtension.Global.Observation.IncomingTransfer
import EmcsfAcExtension.Global.Observation.Gauge
import Mathlib

/-! # The outer comparison record from the original observation setting

All analytic, geometric, boundary and static-reference fields are
constructed from source data. The only map and gauge inputs are their
defining calibration and parallel-frame conditions.
Source: charged_SF_new_version.tex:L1957–2544; approved internal project record.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.Observation

private theorem failed_bound_of_coefficient_le {A E : ℝ≥0∞} {c C : ℝ}
    (hc : c ≤ C) (hf : ¬A ≤ ENNReal.ofReal C * E) : ¬A ≤ ENNReal.ofReal c * E := by
  intro hh
  exact hf (hh.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hc) (zero_le : 0 ≤ E)))

end EmcsfAcExtension.Global.Observation
