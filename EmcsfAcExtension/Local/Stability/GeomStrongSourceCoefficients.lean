module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeomStrongSourceAlgebra
import EmcsfAcExtension.Local.Stability.PotentialDifferenceAlgebra
import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux

/-! # The outer coefficients in the geometric scalar subtraction

The absolute and difference bounds retain their cubic separation power
and the finite mass and relative geometric distances explicitly.
-/

public section

namespace EmcsfAcExtension.Local

/-- The classical outer scalar coefficient and its difference have
universal bounds `512` and `4096`. There is no dependence on the
minimum radius, field parameters, data or higher derivatives.
-/
theorem stab_geometric_scalar_coefficients_c1
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    |2 * S₁.nu u v * S₁.lam u v / ((1 - S₁.mu u v) * S₁.r u v ^ 3)| ≤
      512 / (v - u) ^ 3 ∧
    |2 * S₁.nu u v * S₁.lam u v / ((1 - S₁.mu u v) * S₁.r u v ^ 3) -
      2 * S₂.nu u v * S₂.lam u v / ((1 - S₂.mu u v) * S₂.r u v ^ 3)| ≤
      4096 * ((geomDist T S₁ S₂).toReal + (supDist T S₁.mu S₂.mu).toReal) /
        (v - u) ^ 3 := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hb₁ := h₁s.box.2 (u, v) hp
  have hb₂ := h₂s.box.2 (u, v) hp
  have hR₁ := (stab_radius_bounds h₁s hu huv.le hvT).1
  have hR₂ := (stab_radius_bounds h₂s hu huv.le hvT).1
  have hgeo := stab_geom_sum_le h₁s h₂s hp
  have hrr0 : 0 ≤ |S₁.r u v - S₂.r u v| / S₁.r u v :=
    div_nonneg (abs_nonneg _) (h₁s.c1.r_pos _ hp huv).le
  have hgeom : |S₁.nu u v - S₂.nu u v| + |S₁.lam u v - S₂.lam u v| ≤
      (geomDist T S₁ S₂).toReal := by linarith only [hgeo, hrr0]
  have hrel : |S₁.r u v - S₂.r u v| / S₁.r u v ≤ (geomDist T S₁ S₂).toReal := by
    linarith only [hgeo, abs_nonneg (S₁.lam u v - S₂.lam u v),
      abs_nonneg (S₁.nu u v - S₂.nu u v)]
  have hc₁ := stab_potential_coefficient_abs_le
    (by rw [abs_of_neg (h₁s.c1.nu_neg _ hp)]; exact hb₁.2.2.2.1)
    (by rw [abs_of_pos (h₁s.c1.lam_pos _ hp)]; exact hb₁.2.1) hb₁.2.2.2.2.1
  have hc₂ := stab_potential_coefficient_abs_le
    (by rw [abs_of_neg (h₂s.c1.nu_neg _ hp)]; exact hb₂.2.2.2.1)
    (by rw [abs_of_pos (h₂s.c1.lam_pos _ hp)]; exact hb₂.2.1) hb₂.2.2.2.2.1
  have hdiff := stab_potential_coefficient_sub_le
    (by rw [abs_of_pos (h₁s.c1.lam_pos _ hp)]; exact hb₁.2.1)
    (by rw [abs_of_pos (h₂s.c1.lam_pos _ hp)]; exact hb₂.2.1)
    (by rw [abs_of_neg (h₂s.c1.nu_neg _ hp)]; exact hb₂.2.2.2.1)
    hb₁.2.2.2.2.1 hb₂.2.2.2.2.1 hgeom (stab_mu_sub_le h₁s h₂s hp)
  constructor
  · simpa only [div_div] using
      stab_geometric_cubic_coefficient_abs_le (sub_pos.mpr huv) hR₁ hc₁
  · simpa only [div_div] using
      stab_geometric_cubic_coefficient_sub_le (sub_pos.mpr huv) hR₁ hR₂
        ENNReal.toReal_nonneg hrel hdiff hc₂

end EmcsfAcExtension.Local
