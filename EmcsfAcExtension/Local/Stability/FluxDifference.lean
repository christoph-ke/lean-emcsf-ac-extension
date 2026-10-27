module

public import EmcsfAcExtension.Local.Stability.FluxDifferenceAlgebra
public import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux

/-! # Raw classical quadratic flux differences

These estimates retain the weighted scalar difference and the individual
quadratic flux. The closed graph-node estimates additionally require
the coupled radial absorption; they are not asserted here.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- The outgoing quadratic flux difference before radial absorption.
The constants `2` and `20` are universal, independent of all parameters,
the solutions and minimum radius. -/
theorem stab_out_quadratic_flux_sub_le
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    |S₁.lam u v / S₁.r u v * ‖S₁.theta u v / (S₁.lam u v : ℂ)‖ ^ 2 -
      S₂.lam u v / S₂.r u v * ‖S₂.theta u v / (S₂.lam u v : ℂ)‖ ^ 2| ≤
      2 * ε * (S₁.lam u v / S₁.r u v *
        ‖S₁.theta u v / (S₁.lam u v : ℂ) - S₂.theta u v / (S₂.lam u v : ℂ)‖) +
      20 * (geomDist T S₁ S₂).toReal *
        (S₁.lam u v / S₁.r u v * ‖S₂.theta u v / (S₂.lam u v : ℂ)‖ ^ 2) := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  exact stab_quadratic_flux_sub_le_of_weight
    (div_nonneg (h₁s.c1.lam_pos (u, v) hp).le (h₁s.c1.r_pos (u, v) hp huv).le)
    ((le_add_of_nonneg_right (norm_nonneg (S₁.xi u v / (S₁.nu u v : ℂ)))).trans
      (h₁s.box.2 (u, v) hp).2.2.2.2.2.1)
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi u v / (S₂.nu u v : ℂ)))).trans
      (h₂s.box.2 (u, v) hp).2.2.2.2.2.1)
    (stab_out_weight_sub_le h₁s h₂s hu huv hvT)

/-- The incoming quadratic flux difference uses the positive weight
`-ν/r`, with the same universal coefficients `2` and `20`. This raw
bound retains the weighted incoming difference and its phase feedback. -/
theorem stab_in_quadratic_flux_sub_le
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    |(-S₁.nu u v) / S₁.r u v * ‖S₁.xi u v / (S₁.nu u v : ℂ)‖ ^ 2 -
      (-S₂.nu u v) / S₂.r u v * ‖S₂.xi u v / (S₂.nu u v : ℂ)‖ ^ 2| ≤
      2 * ε * ((-S₁.nu u v) / S₁.r u v *
        ‖S₁.xi u v / (S₁.nu u v : ℂ) - S₂.xi u v / (S₂.nu u v : ℂ)‖) +
      20 * (geomDist T S₁ S₂).toReal *
        ((-S₁.nu u v) / S₁.r u v * ‖S₂.xi u v / (S₂.nu u v : ℂ)‖ ^ 2) := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  exact stab_quadratic_flux_sub_le_of_weight
    (div_nonneg (neg_pos.mpr (h₁s.c1.nu_neg (u, v) hp)).le
      (h₁s.c1.r_pos (u, v) hp huv).le)
    ((le_add_of_nonneg_left (norm_nonneg (S₁.theta u v / (S₁.lam u v : ℂ)))).trans
      (h₁s.box.2 (u, v) hp).2.2.2.2.2.1)
    ((le_add_of_nonneg_left (norm_nonneg (S₂.theta u v / (S₂.lam u v : ℂ)))).trans
      (h₂s.box.2 (u, v) hp).2.2.2.2.2.1)
    (stab_in_weight_sub_le h₁s h₂s hu huv hvT)

end EmcsfAcExtension.Local
