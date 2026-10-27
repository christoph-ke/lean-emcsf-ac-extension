module

public import EmcsfAcExtension.Global.Observation.BarrierContradiction
public import EmcsfAcExtension.Global.Observation.Window
public import EmcsfAcExtension.Global.Observation.BoundaryFailure
public import EmcsfAcExtension.Global.Observation.BoundaryClosed
public import EmcsfAcExtension.Global.Observation.ChartBox
public import EmcsfAcExtension.Global.Observation.OpticsExports
public import EmcsfAcExtension.Global.Observation.ACJustification
public import EmcsfAcExtension.Global.Observation.ChartEquations
public import EmcsfAcExtension.Global.Observation.BoundaryCharts
public import EmcsfAcExtension.Global.Observation.ChartDomains
public import EmcsfAcExtension.Global.Observation.WindowSource
public import EmcsfAcExtension.Global.Observation.IncomingClockDischarge
public import EmcsfAcExtension.Global.Observation.Static.CutoffFamily
public import EmcsfAcExtension.Global.Observation.Static.OuterReference
public import EmcsfAcExtension.Global.Observation.Static.InnerReference
public import EmcsfAcExtension.Global.Observation.SourceContradiction
import EmcsfAcExtension.Global.Observation.CoreCharge
import EmcsfAcExtension.Frozen.Fields.NormalizedOut

/-! # Quantitative charged observation assembly

The original solution supplies both actual comparison records and all
source estimates. Their closed comparisons contradict a uniform strict
static barrier whenever the physical observation inequality fails.
Source: charged_SF_new_version.tex:L2741–2791; approved internal project record.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.Observation

/-- [node prop:charged-observation]
[node prop:charged-observation#strict-barrier-contradiction]
[node prop:charged-observation#quantitative-observation-constant]
The charged observation inequality on the complete original inward
region, in the literal internal project record form. The positive constants
`Tstar,Cstar,δstar,ηstar` depend only on the prescribed gap `δ`, before
all solutions, couplings, scalar backgrounds, radii and clock centers.
The zero-scale branch is exact; otherwise physical smallness forces the
uniform static cutoff and the constructed comparison yields a strict
barrier contradiction. Every comparison, chart and primitive-estimate
input is discharged from the original solution. -/
theorem observation (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    ∃ Tstar Cstar δstar ηstar : ℝ,
    0 < Tstar ∧ 0 < Cstar ∧ 0 < δstar ∧ 0 < ηstar ∧
    ∀ (ui e b τ₀ : ℝ) (S : Fields), 0 < b → OriginalData ui e S →
    ∀ γ : ClockCylinder S (origDomain ui) b (τ₀ - Tstar * b) (τ₀ + Tstar * b),
    triangle (γ.U (τ₀ - Tstar * b)) (γ.V (τ₀ + Tstar * b)) ⊆ origDomain ui →
    (∀ p ∈ triangle (γ.U (τ₀ - Tstar * b)) (γ.V (τ₀ + Tstar * b)),
      0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) →
    AbsolutelyContinuousOnInterval
      (curveParallel e S S.a γ.U γ.V (τ₀ - Tstar * b))
        (τ₀ - Tstar * b) (τ₀ + Tstar * b) →
    (∀ τ ∈ Icc (τ₀ - Tstar * b) (τ₀ + Tstar * b),
      S.mu (γ.U τ) (γ.V τ) +
        ‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ ≤ δstar) →
    |e| * b * (1 + ‖S.a (γ.U τ₀) (γ.V τ₀)‖) ≤ ηstar →
    ENNReal.ofReal (b * (‖S.theta (γ.U τ₀) (γ.V τ₀) /
      (S.lam (γ.U τ₀) (γ.V τ₀) : ℂ)‖ ^ 2 + S.mu (γ.U τ₀) (γ.V τ₀) ^ 2)) ≤
    ENNReal.ofReal Cstar *
      (ENNReal.ofReal (cylinderDissipation S γ.U γ.V
        (τ₀ - Tstar * b) (τ₀ + Tstar * b)) + ENNReal.ofReal b *
        (curveCovVar e S S.a γ.U γ.V (τ₀ - Tstar * b) (τ₀ + Tstar * b)) ^ 2) := by
  obtain ⟨T, Cobs, ηstar, Lzero, hT, hCobs, hηstar, hL1, hcontradiction⟩ :=
    strict_barrier_contradiction δ hδ
  have hLzero : 0 < Lzero := zero_lt_one.trans_le hL1
  obtain ⟨δstar, hδstar, _hδstar1, hlarge⟩ :=
    co_normalization_large hδ.1 hδ.2 hηstar.le hLzero
  refine ⟨T / 2, Cobs, δstar, ηstar, half_pos hT, hCobs, hδstar, hηstar, ?_⟩
  intro ui e b τ₀ S hb h γ _htriangle hgap _hac hweak hcharged
  have hwindow : τ₀ - T / 2 * b ≤ τ₀ + T / 2 * b := by
    nlinarith only [mul_pos hT hb]
  have hτ : τ₀ ∈ Icc (τ₀ - T / 2 * b) (τ₀ + T / 2 * b) := by
    constructor <;> nlinarith only [mul_pos hT hb]
  have hsection := cylinder_full_section h.solution γ hb hτ
  have hm := (mass_bounds_on_full_section h.solution hsection.1.le hsection.2
    ⟨hsection.1.le, le_rfl⟩).1
  rcases mass_scalar_charge_normalization (q := S.Q (γ.U τ₀) (γ.V τ₀))
    (S.theta (γ.U τ₀) (γ.V τ₀) / S.lam (γ.U τ₀) (γ.V τ₀)) hb hm with hzero | hs
  · have hz : b * (‖S.theta (γ.U τ₀) (γ.V τ₀) / S.lam (γ.U τ₀) (γ.V τ₀)‖ ^ 2 +
        S.mu (γ.U τ₀) (γ.V τ₀) ^ 2) = 0 := by
      simpa only [Fields.mu, γ.radius τ₀ hτ] using hzero.2
    rw [hz, ENNReal.ofReal_zero]
    exact zero_le
  · have hleft : τ₀ - T / 2 * b = τ₀ - T * b / 2 := by ring
    have hright : τ₀ + T / 2 * b = τ₀ + T * b / 2 := by ring
    let γ' : ClockCylinder S (origDomain ui) b (τ₀ - T * b / 2) (τ₀ + T * b / 2) :=
      { U := γ.U, V := γ.V
        c1_U := by simpa only [hleft, hright] using γ.c1_U
        c1_V := by simpa only [hleft, hright] using γ.c1_V
        mem := by simpa only [hleft, hright] using γ.mem
        radius := by simpa only [hleft, hright] using γ.radius
        rate_U := by simpa only [hleft, hright] using γ.rate_U
        rate_V := by simpa only [hleft, hright] using γ.rate_V }
    have hUleft := (γ.strictMonoOn_U h.solution).monotoneOn
      (left_mem_Icc.mpr hwindow) hτ hτ.1
    have hVright := (γ.strictMonoOn_V h.solution).monotoneOn hτ
      (right_mem_Icc.mpr hwindow) hτ.2
    have hsectionGap (x) (hx : x ∈ Icc (γ.U τ₀) (γ.V τ₀)) :
        δ ≤ 1 - S.mu (γ.U τ₀) x :=
      (hgap (γ.U τ₀,x) ⟨hUleft, hx.1, hx.2.trans hVright⟩).2
    have hlarge' := hlarge e S (origDomain ui) h.solution (γ.U τ₀) (γ.V τ₀)
      (S.a (γ.U τ₀) (γ.V τ₀)) hsection.1 hsection.2 hsectionGap rfl (hweak τ₀ hτ)
      (by rwa [γ.radius τ₀ hτ]) (by simpa only [γ.radius τ₀ hτ] using hs)
    rw [γ.radius τ₀ hτ] at hlarge'
    apply Classical.byContradiction
    intro hfailure
    apply hcontradiction ui e b
      (S.m (γ.U τ₀) (γ.V τ₀) + b *
        ‖S.theta (γ.U τ₀) (γ.V τ₀) / S.lam (γ.U τ₀) (γ.V τ₀)‖ +
          |S.Q (γ.U τ₀) (γ.V τ₀)|) τ₀ S h γ' hb hs hlarge' rfl
    · change ∀ p ∈ triangle (γ.U (τ₀ - T * b / 2)) (γ.V (τ₀ + T * b / 2)),
        δ ≤ 1 - S.mu p.1 p.2
      simpa only [hleft, hright] using (fun p hp => (hgap p hp).2)
    · exact hcharged
    · change ¬ ENNReal.ofReal (b * (‖S.theta (γ.U τ₀) (γ.V τ₀) /
        S.lam (γ.U τ₀) (γ.V τ₀)‖ ^ 2 + S.mu (γ.U τ₀) (γ.V τ₀) ^ 2)) ≤
          ENNReal.ofReal Cobs * (ENNReal.ofReal (cylinderDissipation S γ.U γ.V
            (τ₀ - T * b / 2) (τ₀ + T * b / 2)) + ENNReal.ofReal b *
              (curveCovVar e S S.a γ.U γ.V (τ₀ - T * b / 2) (τ₀ + T * b / 2)) ^ 2)
      simpa only [hleft, hright] using hfailure

end EmcsfAcExtension.Global.Observation
