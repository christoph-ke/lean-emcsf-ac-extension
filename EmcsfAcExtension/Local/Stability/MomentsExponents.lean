module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Separated exponents for stability moments

The individual-field exponent is `3/4`; the difference exponent is `1/2`.
The numerical threshold below allows both the individual cubic damping and
the Lipschitz bound `3 * ε²` for the cubic difference. See
`charged_SF_new_version.tex:L5024–5025` and `charged_SF_new_version.tex:L5130–5200`.
-/

public section

namespace EmcsfAcExtension.Local

/-- [node restart-sec-bv-stability-independent#separated-Hardy-exponents]
A universal smallness threshold makes `3/4` admissible for individual fields
and `1/2` admissible for differences. Their gap has inverse exactly `4`.
The threshold is independent of the domain, coupling, data, and solutions. -/
theorem stab_separated_hardy_exponents : ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, ε ^ 2 ≤ η →
    (0 < (1 / 2 : ℝ)) ∧ (1 / 2 : ℝ) < 3 / 4 ∧
    (3 / 4 : ℝ) ≤ 1 - ε ^ 2 ∧ (1 / 2 : ℝ) ≤ 1 - 3 * ε ^ 2 ∧
    ((3 / 4 : ℝ) - 1 / 2)⁻¹ = 4 := by
  refine ⟨1 / 12, by norm_num, ?_⟩
  intro ε hε
  refine ⟨by norm_num, by norm_num, ?_, ?_, by norm_num⟩ <;> linarith only [hε]

end EmcsfAcExtension.Local
