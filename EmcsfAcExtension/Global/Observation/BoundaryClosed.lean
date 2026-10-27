module

public import EmcsfAcExtension.Global.Observation.BoundaryExports

/-! # Boundary control with the parallel frame constructed internally

The only inputs are the original solution, cylinder, physical scale and
failed observation. Source: charged_SF_new_version.tex:L2082–2106; internal project record (B),
(C3).
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.Observation

/-- [node eq:co-boundary-close]
[node eq:co-boundary-charge]
The original observation setting supplies a constructed C¹ parallel frame
and every boundary scalar, mass and charge estimate. Gauge derivatives,
clock tangents, trace regularity, finite variation and both small-boundary
norms are derived internally. The boundary constant depends only on `T`,
and the failure coefficient only on `T,ε`, before all physical solution
data, normalizing scales and scalar backgrounds. -/
theorem co_boundary_control {T : ℝ} (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / C → ∃ Cobs : ℝ, 0 < Cobs ∧
    ∀ (ui e b s τ₀ : ℝ) (S : Fields) (_h : OriginalData ui e S)
      (γ : ClockCylinder S (origDomain ui) b (τ₀ - T * b / 2) (τ₀ + T * b / 2)),
    0 < b → 0 < s → s ≤ b →
    S.m (γ.U τ₀) (γ.V τ₀) + b *
      ‖S.theta (γ.U τ₀) (γ.V τ₀) / S.lam (γ.U τ₀) (γ.V τ₀)‖ ≤ s →
    (¬ ENNReal.ofReal (b * (‖S.theta (γ.U τ₀) (γ.V τ₀) /
      S.lam (γ.U τ₀) (γ.V τ₀)‖ ^ 2 + S.mu (γ.U τ₀) (γ.V τ₀) ^ 2)) ≤
      ENNReal.ofReal Cobs * (ENNReal.ofReal (cylinderDissipation S γ.U γ.V
        (τ₀ - T * b / 2) (τ₀ + T * b / 2)) + ENNReal.ofReal b *
        (curveCovVar e S S.a γ.U γ.V (τ₀ - T * b / 2) (τ₀ + T * b / 2)) ^ 2)) →
    ∃ χ : ℝ → ℝ, ContDiff ℝ 1 χ ∧ χ (γ.U (τ₀ - T * b / 2)) = 0 ∧
      (∀ τ ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2),
        HasDerivAt χ (S.A (γ.U τ) (γ.V τ)) (γ.U τ)) ∧
    let G := gaugeFields e S χ
    let L := b / s
    let f := fun t => τ₀ + s * t / 2
    let φ := fun t => G.phi (γ.U (f t)) (γ.V (f t))
    let y := fun t => G.theta (γ.U (f t)) (γ.V (f t)) / G.lam (γ.U (f t)) (γ.V (f t))
    let M := S.m (γ.U τ₀) (γ.V τ₀) / s
    let H := G.a (γ.U τ₀) (γ.V τ₀)
    let P := -(L : ℂ) * y 0
    ∀ t ∈ Icc (-T * L) (T * L),
      ((‖φ t - H - P / (L : ℝ)‖ ≤ C * ε / L ∧
        |S.m (γ.U (f t)) (γ.V (f t)) / s - M| ≤ C * ε / L ∧
        S.m (γ.U (f t)) (γ.V (f t)) / s ≤ 2 ∧
        ‖φ t‖ ≤ ‖H‖ + 2 / L ∧ ‖y t + P / (L : ℝ)‖ ≤ C * ε / L) ∧
        |S.Q (γ.U (f t)) (γ.V (f t)) / s - S.Q (γ.U τ₀) (γ.V τ₀) / s| ≤
          C * (|s * e| * L * (1 + ‖H‖))) ∧
      (|S.m (γ.U (f t)) (γ.V (f t)) / s - M| ≤ 1 ∧
        S.m (γ.U (f t)) (γ.V (f t)) ≤ 2 * s ∧
        ‖S.phi (γ.U (f t)) (γ.V (f t))‖ ≤ ‖H‖ + 2 * s / b) := by
  obtain ⟨C, hC, hcontrol⟩ := co_boundary_control_of_failed_observation hT
  refine ⟨C, hC, ?_⟩
  intro ε hε hεC
  obtain ⟨Cobs, hCobs, hcontrol⟩ := hcontrol ε hε hεC
  refine ⟨Cobs, hCobs, ?_⟩
  intro ui e b s τ₀ S h γ hb hs hsb hscale hfailure
  have hst : τ₀ - T * b / 2 ≤ τ₀ + T * b / 2 := by
    nlinarith only [mul_nonneg hT hb.le]
  obtain ⟨χ, hχ, hχ0, hχd, _hclock⟩ :=
    boundary_clock_equations_of_solution (τ₀ := τ₀) h.solution γ hst hs hb
  exact ⟨χ, hχ, hχ0, hχd,
    hcontrol ui e b s τ₀ S h γ χ hb hs hsb hχ hχd hχ0 hscale hfailure⟩

end EmcsfAcExtension.Global.Observation
