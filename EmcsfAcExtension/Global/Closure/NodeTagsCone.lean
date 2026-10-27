module

public import EmcsfAcExtension.Global.Assembly.Inputs
import EmcsfAcExtension.Global.Restart.ConeSmallness

/-! # Complete-cone exports conditional on the construction obligations

The helpers consume `ClosureObligations`. Its common finite paths construct
the proper limiting cone. The quantitative helper retains its abstract
entry-error envelope; the literal initial-density record requires a
stronger bound from the construction producer.
Source: `charged_SF_new_version.tex:L4115–L4133`.
-/

public section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global

/-- [internal]
Envelope support for `eq:cc-complete-cone`, not a closure of its literal
initial-density statement. `ClosureObligations` does not identify `D` with
`initialInteraction`. All constants and the entry error function may depend
on the development, and precede the energy
tolerance, entry row and stage family. The same coefficient controls TV
on the full closed cone, hence on every compact subinterval. No local
theorem is used. Source: charged_SF_new_version.tex:L4124–L4131. -/
theorem cc_complete_cone_of_closure (hclosure : ClosureObligations)
    (ui e : ℝ) (S : Fields) (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    ∃ C Camp εmax : ℝ, ∃ D M : ℝ → ℝ,
      0 < C ∧ 1 ≤ Camp ∧ 0 < εmax ∧ Tendsto D (𝓝[<] 0) (𝓝 0) ∧
      (∀ u, M u = Camp * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) ∧
      (∀ ε₀ ∈ Ioc 0 εmax, ∀ᶠ u₀ in 𝓝[<] (0 : ℝ),
        ∃ us ∈ Ioo ui 0, u₀ ≤ us ∧
          AbsolutelyContinuousOnInterval (S.a us) us 0 ∧
          eVariationOn (S.a us) (Icc us 0) ≤
            ENNReal.ofReal (C * (D u₀ + ε₀ + e ^ 2 * M u₀ ^ 2 * S.r u₀ 0 ^ 2)) ∧
          ‖S.phi us us‖ ≤ M u₀ ∧ S.r us 0 ≤ S.r u₀ 0) := by
  obtain ⟨c, F, A, hc, hF, hA, Camp, εmax, D, M,
    hCamp, hεmax, hD, hM, hfamilies⟩ := hclosure ui e S h hs
  have hC : 0 < c⁻¹ * A / (1 - F ^ 2) :=
    div_pos (mul_pos (inv_pos.mpr hc) hA) (sub_pos.mpr hF)
  refine ⟨c⁻¹ * A / (1 - F ^ 2), Camp, εmax, D, M, hC, hCamp, hεmax, hD, hM, ?_⟩
  intro ε₀ hε₀
  filter_upwards [hfamilies ε₀ hε₀, Ioo_mem_nhdsLT h.ui_neg] with u₀ hfamily hu₀
  obtain ⟨v₀, ρ, b₀, K, U, vb, B, E, J,
    hρ, hU, hcuts, hR, hrad, hbudget, hEsum, hamp, hclosed, hrow⟩ := hfamily
  exact Restart.selected_cone_of_closure c F A hc hF ui e S h hu₀ hρ U vb B
    hU hcuts hR hrad E J hbudget hEsum hamp hclosed hrow

namespace Closure

/-- [internal]
Conditional export for `sec:charged-closure#complete-cone-ac`: the selected
closed datum is AC, including its existing axis endpoint, with the source
vertex modulus bound. Constants and `M` may depend on the development,
before the tolerance and entry row. The cone is produced by the common
construction obligations. Source: charged_SF_new_version.tex:L4132–L4133. -/
theorem complete_cone_ac_of_closure (hclosure : ClosureObligations)
    (ui e : ℝ) (S : Fields) (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    ∃ Camp εmax : ℝ, ∃ M : ℝ → ℝ, 1 ≤ Camp ∧ 0 < εmax ∧
      (∀ u, M u = Camp * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) ∧
      ∀ ε₀ ∈ Ioc 0 εmax, ∀ᶠ u₀ in 𝓝[<] (0 : ℝ),
        ∃ us ∈ Ioo ui 0, u₀ ≤ us ∧
          AbsolutelyContinuousOnInterval (S.a us) us 0 ∧ ‖S.phi us us‖ ≤ M u₀ := by
  obtain ⟨C, Camp, εmax, D, M, _hC, hCamp, hεmax, _hD, hM, hcones⟩ :=
    cc_complete_cone_of_closure hclosure ui e S h hs
  refine ⟨Camp, εmax, M, hCamp, hεmax, hM, ?_⟩
  intro ε₀ hε₀
  filter_upwards [hcones ε₀ hε₀] with u₀ hcone
  obtain ⟨us, hus, hentry, hac, _hvar, hvertex, _hr⟩ := hcone
  exact ⟨us, hus, hentry, hac, hvertex⟩

end Closure

end EmcsfAcExtension.Global
