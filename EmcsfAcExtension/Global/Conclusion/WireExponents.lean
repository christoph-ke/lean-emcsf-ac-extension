module

public import EmcsfAcExtension.Global.Conclusion.CompactAxis
import EmcsfAcExtension.Global.Conclusion.PositiveExponent

/-! # Unconditional local and earlier internal project record exponent nodes

Only the frozen solution class on the source domain is required. In
particular these node exports do not depend on `ClosureObligations` or on
any existence theorem. Source: charged_SF_new_version.tex:L4199–4212; approved internal project
record.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.Closure

/-- [node sec:charged-closure#local-positive-incoming-exponent]
internal project record route
`sec:charged-closure#local-positive-incoming-exponent#route-ga1-compact-axis`.
The restart's closed-triangle class supplies one bound for every complete
incoming section. The constant may depend on fixed `e,S,a,b`, uniformly in
`v`; no universal small-BV estimate is claimed or assumed.
Source: charged_SF_new_version.tex:L4199–4207; approved internal project record:L160–168. -/
theorem local_positive_incoming_exponent {e a b : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle a b)) :
    ∃ C > 0, ∀ v ∈ Icc a b,
      (∫⁻ u in Ico a v, ENNReal.ofReal (positiveExpIntegrand S u v)) ≤
        ENNReal.ofReal C :=
  local_positive_incoming_exponent_of_solution hS

/-- [node sec:charged-closure#local-positive-incoming-exponent#route-ga1-compact-axis]
The internal project record route exports the same complete-ray bound as its owner.
The constant may depend on fixed `e,S,a,b`, uniformly in `v`.
Source: approved internal project record:L160–168. -/
theorem local_positive_incoming_exponent_ga1 {e a b : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle a b)) :
    ∃ C > 0, ∀ v ∈ Icc a b,
      (∫⁻ u in Ico a v, ENNReal.ofReal (positiveExpIntegrand S u v)) ≤
        ENNReal.ofReal C :=
  local_positive_incoming_exponent hS

/-- [node sec:charged-closure#earlier-positive-exponent]
internal project record route
`sec:charged-closure#earlier-positive-exponent#route-ga1-compact-axis`.
The constant may depend on fixed `ui,a,e,S`, uniformly over all complete
incoming rays and their earlier portions. The proper split point is the
source premise; no mass-sign or off-axis radius lower bound is assumed.
Source: charged_SF_new_version.tex:L4209–4212; approved internal project record:L173–182. -/
theorem earlier_positive_exponent {ui a e : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (ha : a ∈ Ioo ui 0) :
    ∃ C > 0, ∀ v ∈ Ioo ui 0,
      (∫⁻ u in Ico ui (min a v), ENNReal.ofReal (positiveExpIntegrand S u v)) ≤
        ENNReal.ofReal C :=
  earlier_positive_exponent_of_solution hS ha

/-- [node sec:charged-closure#earlier-positive-exponent#route-ga1-compact-axis]
The internal project record route exports the same earlier-ray bound as its owner.
The constant may depend on fixed `ui,a,e,S`, uniformly over all incoming rays.
Source: approved internal project record:L173–182. -/
theorem earlier_positive_exponent_ga1 {ui a e : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (ha : a ∈ Ioo ui 0) :
    ∃ C > 0, ∀ v ∈ Ioo ui 0,
      (∫⁻ u in Ico ui (min a v), ENNReal.ofReal (positiveExpIntegrand S u v)) ≤
        ENNReal.ofReal C :=
  earlier_positive_exponent hS ha

end EmcsfAcExtension.Global.Closure
