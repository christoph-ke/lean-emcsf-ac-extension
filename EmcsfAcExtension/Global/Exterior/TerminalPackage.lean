module

public import EmcsfAcExtension.Global.Exterior.Geometry
public import EmcsfAcExtension.Global.Exterior.DerivativeSourceTerminal
import EmcsfAcExtension.Global.Terminal.Hypotheses
import EmcsfAcExtension.Global.Exterior.Radii

/-! # The signed-terminal inputs to the adaptive exterior

All terminal estimates used by the density argument are consequences of
the original signed hypothesis. The mass and radius profiles are chosen
before every late row, carrier and endpoint. Source:
`charged_SF_new_version.tex:L914–1031`, L1098–1182; approved internal project record.
-/

public section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.Exterior

/-- [internal] One terminal package discharges radius collapse and the
logarithmic scalar estimate. Its positive constant depends on the fixed
original development and signed bound, uniformly in the terminal label. -/
theorem terminal_control {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    ∃ C > 0,
      Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0) ∧
      (∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
        C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) := by
  obtain ⟨δ, C, lam₀, _, hC, _, _, _, _, hcollapse, _, _, hphi⟩ :=
    (charged_terminal_equivalence ui e S h).2 hs
  exact ⟨C, hC, hcollapse, hphi⟩

end EmcsfAcExtension.Global.Exterior
