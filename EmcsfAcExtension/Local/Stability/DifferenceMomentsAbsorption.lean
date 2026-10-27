module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Scalar absorption of the outgoing optical feedback

The numerical coefficients are those of the independently proved raw
optical and Hardy comparisons. No field conclusion is assumed here.
-/

public section

namespace EmcsfAcExtension.Local

/-- The optical mass feedback gives a coarse uniform mass-ratio
comparison with coefficients depending only on `A`. This conditional
algebraic helper does not assert the sharper mass-Volterra node. -/
theorem stab_mass_le_of_feedback {A ε G U J : ℝ}
    (hA : 0 < A) (hG : 0 ≤ G) (hU : 0 ≤ U)
    (hε1 : ε ^ 2 ≤ 1) (hsmall : 524288 * A * ε ^ 2 ≤ 1)
    (hraw : U ≤ 20 * G + 131072 * ε * (J + (G + U) * (A * ε)) +
      20480 * A * ε ^ 2 * G) :
    U ≤ (40 + 303104 * A) * G + 262144 * ε * J := by
  have hUU : 131072 * A * ε ^ 2 * U ≤ (1 / 2 : ℝ) * U :=
    mul_le_mul_of_nonneg_right (by linarith only [hsmall]) hU
  have hGG := mul_le_mul_of_nonneg_left hε1
    (show 0 ≤ 151552 * A * G by positivity)
  nlinarith only [hraw, hUU, hGG]

/-- The outgoing optical feedback closes its radial budget under the
literal smallness condition `524288 A ε² ≤ 1`. The resulting factor
depends only on `A`; all numerical coefficients are universal. This
conditional algebraic helper closes no field graph node by itself. -/
theorem stab_out_budget_le_of_feedback {A ε G U J : ℝ}
    (hA : 0 < A) (hε : 0 ≤ ε) (hG : 0 ≤ G) (hU : 0 ≤ U) (hJ : 0 ≤ J)
    (hε1 : ε ^ 2 ≤ 1) (hsmall : 524288 * A * ε ^ 2 ≤ 1)
    (hraw : U ≤ 20 * G + 131072 * ε * (J + (G + U) * (A * ε)) +
      20480 * A * ε ^ 2 * G) :
    J + (G + U) * (A * ε) ≤
      (2 + A * (41 + 303104 * A)) * (J + ε * G) := by
  have hUU : 131072 * A * ε ^ 2 * U ≤ (1 / 2 : ℝ) * U :=
    mul_le_mul_of_nonneg_right (by linarith only [hsmall]) hU
  have hGG := mul_le_mul_of_nonneg_left hε1
    (show 0 ≤ 151552 * A * G by positivity)
  have hUr : U ≤ (40 + 303104 * A) * G + 262144 * ε * J := by
    nlinarith only [hraw, hUU, hGG]
  have hRU := mul_le_mul_of_nonneg_right hUr (mul_nonneg hA.le hε)
  have hJJ := mul_le_mul_of_nonneg_right
    (show 1 + 262144 * A * ε ^ 2 ≤ 2 by linarith only [hsmall]) hJ
  have hRB : J + (G + U) * (A * ε) ≤
      2 * J + A * (41 + 303104 * A) * (ε * G) := by
    nlinarith only [hRU, hJJ]
  apply hRB.trans
  have hBJ : 0 ≤ (A * (41 + 303104 * A)) * J := by positivity
  have heG : 0 ≤ ε * G := mul_nonneg hε hG
  nlinarith only [hBJ, heG]

end EmcsfAcExtension.Local
