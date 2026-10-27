module

public import EmcsfAcExtension.Local.Stability.MomentsIncoming
public import EmcsfAcExtension.Local.Stability.AssemblyIdentity
public import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux
import EmcsfAcExtension.Local.Calculus.RadialIdentity

/-! # Incoming individual moments in the comparison radius

The common incoming labels are retained. Only the positive radial
kernel is compared, so the connection introduces no error in this
individual moment estimate.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

-- `stab_in_reconstruction_smul` is provided by `Local/Stability/AssemblyIdentity` (internal project
-- record); the
-- identical copy
-- of internal project record was removed at landing.

/-- The second incoming `3/4` moment in the first radius costs exactly
`64`, uniformly in all parameters, the pair and minimum radius. This
individual moment is a helper for the unabsorbed difference estimate. -/
theorem stab_in_moment_common_radius
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : ε ^ 2 ≤ 1 / 4)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ENNReal.ofReal ‖S₂.xi u v / (S₂.nu u v : ℂ)‖ ≤
      ENNReal.ofReal 64 * ∫⁻ s in Icc u v,
        ENNReal.ofReal ((S₁.r s v / S₁.r u v) ^ (3 / 4 : ℝ)) *
          inEnv T (kC1 e (triangle 0 T) S₂) s := by
  have hm := stab_in_moment_of_identity h₂s
    (fun u v hu huv hvT => stab_in_reconstruction_smul h₂s.c1 hu huv hvT)
    (by norm_num : (0 : ℝ) < 3 / 4) (by linarith only [hε]) hu huv hvT
  have hI : (∫⁻ s in Icc u v,
      ENNReal.ofReal ((S₂.r s v / S₂.r u v) ^ (3 / 4 : ℝ)) *
        inEnv T (kC1 e (triangle 0 T) S₂) s) ≤
      ENNReal.ofReal 16 * ∫⁻ s in Icc u v,
        ENNReal.ofReal ((S₁.r s v / S₁.r u v) ^ (3 / 4 : ℝ)) *
          inEnv T (kC1 e (triangle 0 T) S₂) s := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' measurableSet_Icc
    intro s hs
    have hr₁ := stab_radius_bounds h₁s (hu.trans hs.1) hs.2 hvT
    have hr₂ := stab_radius_bounds h₂s (hu.trans hs.1) hs.2 hvT
    have hc := stab_radius_power_compare
      (show 0 ≤ S₁.r s v by linarith only [hr₁.1, hs.2])
      (show 0 ≤ S₂.r s v by linarith only [hr₂.1, hs.2])
      (h₁s.c1.r_pos (u, v) ⟨hu, huv.le, hvT⟩ huv)
      (h₂s.c1.r_pos (u, v) ⟨hu, huv.le, hvT⟩ huv)
      (stab_radius_compare h₁s h₂s (hu.trans hs.1) hs.2 hvT).2
      (stab_radius_compare h₁s h₂s hu huv.le hvT).1
      (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) ≤ 1)
    have hc' := ENNReal.ofReal_le_ofReal hc
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)] at hc'
    simpa only [mul_assoc] using mul_le_mul' hc' (le_rfl :
      inEnv T (kC1 e (triangle 0 T) S₂) s ≤ inEnv T (kC1 e (triangle 0 T) S₂) s)
  apply hm.trans
  calc
    _ ≤ ENNReal.ofReal 4 * (ENNReal.ofReal 16 * ∫⁻ s in Icc u v,
        ENNReal.ofReal ((S₁.r s v / S₁.r u v) ^ (3 / 4 : ℝ)) *
          inEnv T (kC1 e (triangle 0 T) S₂) s) := mul_le_mul' le_rfl hI
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num

end EmcsfAcExtension.Local
