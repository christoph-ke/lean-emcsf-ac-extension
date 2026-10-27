module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Scalar absorption on the initial cone

This algebra keeps the initial scalar datum contribution separate from
the radial derivative difference. Every coefficient is literal.
-/

public section

namespace EmcsfAcExtension.Local

/-- The initial mass feedback absorbs with the explicit threshold
`2688 A ε² ≤ 1`. The resulting coefficients `672` and `80` are
universal and no datum-only replacement of `Δj` is made. -/
theorem stab_initial_mass_absorb {A ε σ J U Δ : ℝ}
    (hA : 0 ≤ A) (hε : 0 ≤ ε) (hσ : σ ≤ 1)
    (hJ : 0 ≤ J) (hU : 0 ≤ U)
    (hsmall : 2688 * A * ε ^ 2 ≤ 1)
    (hfeedback : U ≤ 2 * ε * (8 * J + 32 * A * ε * U) +
      40 * σ * ε * ((8 * J + 32 * A * ε * U) + ε * Δ)) :
    U ≤ 672 * ε * J + 80 * σ * ε ^ 2 * Δ := by
  have hX : 0 ≤ 8 * J + 32 * A * ε * U := by positivity
  have hσscale := mul_le_mul_of_nonneg_right hσ
    (show 0 ≤ 40 * ε * (8 * J + 32 * A * ε * U) by positivity)
  have hsmallscale := mul_le_mul_of_nonneg_right hsmall hU
  nlinarith only [hfeedback, hσscale, hsmallscale]

end EmcsfAcExtension.Local
