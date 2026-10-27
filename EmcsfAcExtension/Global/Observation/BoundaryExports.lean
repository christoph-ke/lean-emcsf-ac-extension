module

public import EmcsfAcExtension.Global.Observation.BoundaryFailedSource

/-! # Source-setting observation boundary exports

The boundary equations, regularity and small-boundary inputs are all
discharged from the original solution, its chosen parallel gauge and
failure of the observation estimate. Source: charged_SF_new_version.tex:L2082–2106.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
Boundary scalar, mass and charge estimates on the original solution in
its constructed parallel observation frame. All independent-profile,
clock-tangent and small-boundary premises are discharged. The boundary
constant depends only on `T`; the failure coefficient depends only on
`T,ε`. Both precede all physical data, scales, backgrounds and gauges.
The scale may be the source mass–scalar–charge denominator or any larger
positive scale at most the cylinder radius. -/
theorem co_boundary_control_of_failed_observation {T : ℝ} (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / C → ∃ Cobs : ℝ, 0 < Cobs ∧
    ∀ (ui e b s τ₀ : ℝ) (S : Fields) (_h : OriginalData ui e S)
      (γ : ClockCylinder S (origDomain ui) b (τ₀ - T * b / 2) (τ₀ + T * b / 2))
      (χ : ℝ → ℝ),
    let G := gaugeFields e S χ
    let L := b / s
    let f := fun t => τ₀ + s * t / 2
    let φ := fun t => G.phi (γ.U (f t)) (γ.V (f t))
    let y := fun t => G.theta (γ.U (f t)) (γ.V (f t)) / G.lam (γ.U (f t)) (γ.V (f t))
    let M := S.m (γ.U τ₀) (γ.V τ₀) / s
    let H := G.a (γ.U τ₀) (γ.V τ₀)
    let P := -(L : ℂ) * y 0
    0 < b → 0 < s → s ≤ b →
    ContDiff ℝ 1 χ →
    (∀ τ ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2),
      HasDerivAt χ (S.A (γ.U τ) (γ.V τ)) (γ.U τ)) →
    χ (γ.U (τ₀ - T * b / 2)) = 0 →
    S.m (γ.U τ₀) (γ.V τ₀) + b *
      ‖S.theta (γ.U τ₀) (γ.V τ₀) / S.lam (γ.U τ₀) (γ.V τ₀)‖ ≤ s →
    (¬ ENNReal.ofReal (b * (‖S.theta (γ.U τ₀) (γ.V τ₀) /
      S.lam (γ.U τ₀) (γ.V τ₀)‖ ^ 2 + S.mu (γ.U τ₀) (γ.V τ₀) ^ 2)) ≤
      ENNReal.ofReal Cobs * (ENNReal.ofReal (cylinderDissipation S γ.U γ.V
        (τ₀ - T * b / 2) (τ₀ + T * b / 2)) + ENNReal.ofReal b *
        (curveCovVar e S S.a γ.U γ.V (τ₀ - T * b / 2) (τ₀ + T * b / 2)) ^ 2)) →
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
  obtain ⟨C, hC, hcontrol⟩ := boundary_control_of_small_boundary hT
  refine ⟨C, hC, ?_⟩
  intro ε hε hεC
  obtain ⟨Cobs, hCobs, hsmall⟩ := small_boundary_of_solution_failed_observation hT hε
  refine ⟨Cobs, hCobs, ?_⟩
  intro ui e b s τ₀ S h γ χ
  dsimp only
  intro hb hs hsb hχ hχd hχ0 hscale hfailure
  have hbnd := hsmall ui e b s τ₀ S h γ χ hb hs hχ hχd hχ0 hscale hfailure
  exact hcontrol ui e b s τ₀ ε S h γ χ hb hs hsb hε.le hεC hχ hχd hscale hbnd.1 hbnd.2

end EmcsfAcExtension.Global.Observation
