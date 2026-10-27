module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassAlgebra
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassSign
import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux

/-! # Exact outgoing normalized mass difference forcing

The forcing is the literal subtraction of the two normalized mass
constraints, leaving the positive first-solution damping separate.
Its estimate uses only the fixed box, rather than a mass conclusion.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- The undamped forcing obtained by subtracting the two normalized
outgoing mass equations. The remaining linear coefficient is
`(λ₁/r₁)(1+|x₁|²)`. -/
@[expose] noncomputable def massDifferenceForcing (S₁ S₂ : Fields) (u v : ℝ) : ℝ :=
  S₁.lam u v / S₁.r u v *
    ((1 - S₂.mu u v) * (‖S₁.theta u v / (S₁.lam u v : ℂ)‖ ^ 2 -
      ‖S₂.theta u v / (S₂.lam u v : ℂ)‖ ^ 2) +
      (S₁.Q u v ^ 2 / S₁.r u v ^ 2 - S₂.Q u v ^ 2 / S₂.r u v ^ 2)) +
    (S₁.lam u v / S₁.r u v - S₂.lam u v / S₂.r u v) *
      ((1 - S₂.mu u v) * ‖S₂.theta u v / (S₂.lam u v : ℂ)‖ ^ 2 +
        S₂.Q u v ^ 2 / S₂.r u v ^ 2 - S₂.mu u v)

/-- The mass difference forcing keeps the scalar ratio difference,
the electromagnetic square difference, and the weighted individual
mass. The only geometric coefficient is the universal number `20`. -/
theorem stab_out_mass_difference_forcing_le
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    |massDifferenceForcing S₁ S₂ u v| ≤
      (2 * ε) * (S₁.lam u v / S₁.r u v *
        ‖S₁.theta u v / (S₁.lam u v : ℂ) - S₂.theta u v / (S₂.lam u v : ℂ)‖) +
      S₁.lam u v / S₁.r u v *
        |S₁.Q u v ^ 2 / S₁.r u v ^ 2 - S₂.Q u v ^ 2 / S₂.r u v ^ 2| +
      (20 * (geomDist T S₁ S₂).toReal) * (S₁.lam u v / S₁.r u v *
        (‖S₂.theta u v / (S₂.lam u v : ℂ)‖ ^ 2 + S₂.Q u v ^ 2 / S₂.r u v ^ 2 +
          |S₂.mu u v|)) := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hμ := stab_mu_nonneg h₂s hu huv.le hvT
  rw [abs_of_nonneg hμ]
  exact stab_mass_difference_forcing_le
    (div_nonneg (h₁s.c1.lam_pos (u, v) hp).le (h₁s.c1.r_pos (u, v) hp huv).le)
    hμ (by linarith only [h₂s.c1.one_sub_mu_pos (u, v) hp]) (by positivity)
    ((le_add_of_nonneg_right (norm_nonneg _)).trans (h₁s.box.2 (u, v) hp).2.2.2.2.2.1)
    ((le_add_of_nonneg_right (norm_nonneg _)).trans (h₂s.box.2 (u, v) hp).2.2.2.2.2.1)
    (stab_out_weight_sub_le h₁s h₂s hu huv hvT)

end EmcsfAcExtension.Local
