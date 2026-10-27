module

public import EmcsfAcExtension.Global.Defs.Original
import EmcsfAcExtension.Global.Closure.Final
import EmcsfAcExtension.Global.Conclusion.WireFinal

/-! # Unconditional terminal variation and exponent node exports

The owner records and their approved internal project record route records have the same
literal conclusions. Closure is discharged by the proved shrinking
construction. Source: `charged_SF_new_version.tex:L4194–L4215`; approved internal project record,
terminal-variation and uniform-positive-exponents sections.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.Closure

/-- [node sec:charged-closure#terminal-variation#route-ga1-continuation-class]
The continuation's frozen class gives the literal sum of the three
terminal variations on the full original half-open interval. No
continuation or variation premise remains. Source: `charged_SF_new_version.tex:L4194–L4196`;
approved internal project record:L118–L139. -/
theorem terminal_variation_ga1 (ui e : ℝ) (S : Fields)
    (hold : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    eVariationOn (fun u => S.phi u 0) (Ico ui 0) +
      eVariationOn (fun u => S.b u 0) (Ico ui 0) +
      eVariationOn (fun u => Real.log (-S.nu u 0)) (Ico ui 0) < ⊤ :=
  terminal_variation_ga1_of_closure closure_obligations ui e S hold hs

/-- [node sec:charged-closure#terminal-variation]
The sum of the terminal variations of φ, β/ν and log(-ν) is finite on
`[ui,0)`, through the approved internal project record continuation-class route.
Source: `charged_SF_new_version.tex:L4194–L4196`. -/
theorem terminal_variation (ui e : ℝ) (S : Fields)
    (hold : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    eVariationOn (fun u => S.phi u 0) (Ico ui 0) +
      eVariationOn (fun u => S.b u 0) (Ico ui 0) +
      eVariationOn (fun u => Real.log (-S.nu u 0)) (Ico ui 0) < ⊤ :=
  terminal_variation_ga1 ui e S hold hs

/-- [node sec:charged-closure#uniform-positive-exponents#route-ga1-compact-axis]
One compact-axis bound for the continuation controls every complete
original incoming ray. Its finite bound may depend on that continuation
and is uniform in the ray; no universal quantitative constant is asserted.
Source: `charged_SF_new_version.tex:L4205–L4215`; approved internal project record:L144–L155. -/
theorem uniform_positive_exponents_ga1 (ui e : ℝ) (S : Fields)
    (hold : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    (⨆ v ∈ Ioo ui 0,
      ∫⁻ u in Ico ui v, ENNReal.ofReal (positiveExpIntegrand S u v)) < ⊤ :=
  uniform_positive_exponents_of_closure closure_obligations ui e S hold hs

/-- [node sec:charged-closure#uniform-positive-exponents]
The supremum of the complete positive incoming exponents is finite,
through the approved internal project record compact-axis route. The implicit finite bound
may depend on the continuation and is uniform in every `ui < v < 0`.
The production assembly proves the same clause by the two-application
variant `uniform_positive_exponents_of_continuation`.
Source: `charged_SF_new_version.tex:L4205–L4215`. -/
theorem uniform_positive_exponents (ui e : ℝ) (S : Fields)
    (hold : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    (⨆ v ∈ Ioo ui 0,
      ∫⁻ u in Ico ui v, ENNReal.ofReal (positiveExpIntegrand S u v)) < ⊤ :=
  uniform_positive_exponents_ga1 ui e S hold hs

end EmcsfAcExtension.Global.Closure
