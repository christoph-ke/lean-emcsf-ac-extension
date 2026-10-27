module

public import EmcsfAcExtension.Global.Observation.Scaling
public import EmcsfAcExtension.Global.Observation.BoundarySource
import EmcsfAcExtension.Global.Observation.Gauge
import Mathlib

/-! # The actual central static parameters

The source mass–scalar–charge scale puts the physical central data in
the compact normalized static family, in any chosen unitary gauge.
Source: charged_SF_new_version.tex:L1964–2037; approved internal project record normalization.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
The actual gauge-transformed central parameters satisfy the compact
static normalization, nonnegative mass and unit charge bound. The
boundary-control scale inequality also follows. Only the defining
physical scale is supplied, with no normalized-parameter premises or
estimate constants. -/
theorem central_parameters_of_physical_scale
    {ui e b s a z τ₀ : ℝ} {S : Fields} (h : OriginalData ui e S)
    (γ : ClockCylinder S (origDomain ui) b a z)
    (hb : 0 < b) (hs : 0 < s) (hτ : τ₀ ∈ Icc a z) (χ : ℝ → ℝ)
    (hscale : s = S.m (γ.U τ₀) (γ.V τ₀) + b *
      ‖S.theta (γ.U τ₀) (γ.V τ₀) / S.lam (γ.U τ₀) (γ.V τ₀)‖ +
        |S.Q (γ.U τ₀) (γ.V τ₀)|) :
    let B := gaugeFields e S χ
    let M := S.m (γ.U τ₀) (γ.V τ₀) / s
    let P := -((b / s : ℝ) : ℂ) * (B.theta (γ.U τ₀) (γ.V τ₀) / B.lam (γ.U τ₀) (γ.V τ₀))
    let q := S.Q (γ.U τ₀) (γ.V τ₀) / s
    0 ≤ M ∧ M + ‖P‖ + |q| = 1 ∧ |q| ≤ 1 ∧
      S.m (γ.U τ₀) (γ.V τ₀) + b *
        ‖S.theta (γ.U τ₀) (γ.V τ₀) / S.lam (γ.U τ₀) (γ.V τ₀)‖ ≤ s := by
  let B := gaugeFields e S χ
  let φ := B.phi (γ.U τ₀) (γ.V τ₀)
  let y := B.theta (γ.U τ₀) (γ.V τ₀) / B.lam (γ.U τ₀) (γ.V τ₀)
  let H := B.a (γ.U τ₀) (γ.V τ₀)
  let M := S.m (γ.U τ₀) (γ.V τ₀) / s
  let P := -((b / s : ℝ) : ℂ) * y
  let q := S.Q (γ.U τ₀) (γ.V τ₀) / s
  have hyNorm := (gauge_ratio_norms e S χ (γ.U τ₀) (γ.V τ₀)).1
  have hscale' : s = S.m (γ.U τ₀) (γ.V τ₀) + b * ‖y‖ +
      |S.Q (γ.U τ₀) (γ.V τ₀)| := by rwa [hyNorm]
  have hH : H = φ + y := rfl
  have hP : ((b / s : ℝ) : ℂ) * (φ - H) = P := by rw [hH]; dsimp only [P]; ring
  have hnorm := normalized_central_data hb hs hscale' hH
  rw [hP] at hnorm
  have hm0 : 0 ≤ S.m (γ.U τ₀) (γ.V τ₀) := by
    have hh := (h.mu _ (γ.mem τ₀ hτ)).1
    simp only [Fields.mu, γ.radius τ₀ hτ] at hh
    have hmul := (le_div_iff₀ hb).mp hh
    linarith only [hmul]
  have hM : 0 ≤ M := div_nonneg hm0 hs.le
  refine ⟨hM, hnorm, ?_, ?_⟩
  · have hPnonneg := norm_nonneg P
    change M + ‖P‖ + |q| = 1 at hnorm
    linarith only [hM, hPnonneg, hnorm]
  · rw [hscale]
    exact le_add_of_nonneg_right (abs_nonneg _)

end EmcsfAcExtension.Global.Observation
