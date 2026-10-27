module

public import EmcsfAcExtension.Global.Assembly.Inputs
public import EmcsfAcExtension.Global.Defs.Interaction
import EmcsfAcExtension.Global.Closure.ConeTagsFamilies
import EmcsfAcExtension.Global.Closure.Final
import EmcsfAcExtension.Global.Closure.NodeTagsCone
import EmcsfAcExtension.Global.Restart.ConeSmallness

/-! # Unconditional complete-cone node exports

The proper shrinking construction gives a complete closed cone with the
literal initial-density variation bound, and an AC datum whose vertex
modulus is bounded by the fixed logarithmic amplitude majorant.
Source: `charged_SF_new_version.tex:L3873–L3898`, `charged_SF_new_version.tex:L4124–L4133`.
-/

public section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global

/-- [node eq:cc-complete-cone]
The complete limiting cone has total variation at most
`C * (D₀ + ε₀ + ζ²)`, with the literal initial density
`D₀ = (initialInteraction S u₀ (V u₀)).toReal` of the produced proper
entry family, and `ζ² = e² (M u₀)² (S.r u₀ 0)²`.
The constants depend on the fixed development, geometric and stopping
bounds and connector ratio. They precede every shrinking entry scale,
energy tolerance, stage number and duration. The bound covers the full
closed cone, including its axis endpoint; the same constant therefore
controls every compact subinterval. Source: charged_SF_new_version.tex:L4124–L4131. -/
theorem cc_complete_cone
    (ui e : ℝ) (S : Fields) (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    ∃ C Camp εmax : ℝ, ∃ ell V M : ℝ → ℝ,
      0 < C ∧ 1 ≤ Camp ∧ 0 < εmax ∧
      Tendsto (fun u => (initialInteraction S u (V u)).toReal) (𝓝[<] 0) (𝓝 0) ∧
      (∀ u, M u = Camp * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) ∧
      (∀ᶠ u in 𝓝[<] (0 : ℝ), u < V u ∧ V u < 0 ∧
        S.r u (V u) = ell (S.r u 0) ∧
        0 < ell (S.r u 0) ∧ ell (S.r u 0) < S.r u 0) ∧
      Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0) ∧
      (∀ ε₀ ∈ Ioc 0 εmax, ∀ᶠ u₀ in 𝓝[<] (0 : ℝ),
        ∃ us ∈ Ioo ui 0, u₀ ≤ us ∧
          AbsolutelyContinuousOnInterval (S.a us) us 0 ∧
          eVariationOn (S.a us) (Icc us 0) ≤
            ENNReal.ofReal (C * ((initialInteraction S u₀ (V u₀)).toReal + ε₀ +
              e ^ 2 * M u₀ ^ 2 * S.r u₀ 0 ^ 2)) ∧
          ‖S.phi us us‖ ≤ M u₀ ∧ S.r us 0 ≤ S.r u₀ 0) := by
  obtain ⟨c, F, A, hc, hF, hA, Camp, εmax, ell, V, M,
    hCamp, hεmax, hD, hM, hroot, hratio, hfamilies⟩ :=
    Closure.closure_families_with_initial_density ui e S h hs
  have hC : 0 < c⁻¹ * A / (1 - F ^ 2) :=
    div_pos (mul_pos (inv_pos.mpr hc) hA) (sub_pos.mpr hF)
  refine ⟨c⁻¹ * A / (1 - F ^ 2), Camp, εmax, ell, V, M,
    hC, hCamp, hεmax, hD, hM, hroot, hratio, ?_⟩
  intro ε₀ hε₀
  filter_upwards [hfamilies ε₀ hε₀, Ioo_mem_nhdsLT h.ui_neg] with u₀ hfamily hu₀
  obtain ⟨ρ, b₀, K, U, vb, B, E, J,
    hρ, hU, hcuts, hR, hrad, hbudget, hEsum, hamp, hclosed, hrow⟩ := hfamily
  exact Restart.selected_cone_of_closure c F A hc hF ui e S h hu₀ hρ U vb B
    hU hcuts hR hrad E J hbudget hEsum hamp hclosed hrow

namespace Closure

/-- [node sec:charged-closure#complete-cone-ac]
The produced proper complete-cone datum is AC on its full closed interval,
including the existing axis endpoint, with vertex modulus at most the
logarithmic amplitude majorant. The amplitude coefficient may depend on
the fixed development and is chosen before the energy tolerance and entry
row. No closure obligation is assumed. Source: charged_SF_new_version.tex:L4132–L4133. -/
theorem complete_cone_ac
    (ui e : ℝ) (S : Fields) (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    ∃ Camp εmax : ℝ, ∃ M : ℝ → ℝ, 1 ≤ Camp ∧ 0 < εmax ∧
      (∀ u, M u = Camp * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) ∧
      ∀ ε₀ ∈ Ioc 0 εmax, ∀ᶠ u₀ in 𝓝[<] (0 : ℝ),
        ∃ us ∈ Ioo ui 0, u₀ ≤ us ∧
          AbsolutelyContinuousOnInterval (S.a us) us 0 ∧ ‖S.phi us us‖ ≤ M u₀ := by
  exact complete_cone_ac_of_closure closure_obligations ui e S h hs

end Closure

end EmcsfAcExtension.Global
