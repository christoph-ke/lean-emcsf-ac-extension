module

public import EmcsfAcExtension.Local.Stability.Moments
public import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux
import EmcsfAcExtension.Local.Calculus.RadialIdentity

/-! # Individual moments in the comparison radius

The second solution's `3/4` moment can be expressed using the first
solution's radius, uniformly down to the axis. No radius-dependent
logarithm or change of common null labels enters this comparison.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem out_reconstruction_smul_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (fun s => S.theta u s / (S.lam u s : ℂ))
      (jC1 (triangle 0 T) S u v / ((1 - S.mu u v : ℝ) : ℂ) -
        (S.lam u v / S.r u v * (1 - ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2)) •
          (S.theta u v / (S.lam u v : ℂ))) (Icc u T) v := by
  apply (stab_out_reconstruction hS hu huv hvT).congr_deriv
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_pow]

/-- The second solution's outgoing `3/4` moment in the first radius has
the exact universal coefficient `64`. It is independent of the coupling,
domain, data, background, envelope bound and minimum radius. This is an
individual-field helper, with no difference-node tag. -/
theorem stab_out_moment_common_radius
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : ε ^ 2 ≤ 1 / 4)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ENNReal.ofReal ‖S₂.theta u v / (S₂.lam u v : ℂ)‖ ≤
      ENNReal.ofReal 64 * ∫⁻ s in Icc u v,
        ENNReal.ofReal ((S₁.r u s / S₁.r u v) ^ (3 / 4 : ℝ)) *
          outEnv 0 (jC1 (triangle 0 T) S₂) s := by
  have hm := stab_out_moment_of_identity h₂s
    (fun u v hu huv hvT => out_reconstruction_smul_aux h₂s.c1 hu huv hvT)
    (by norm_num : (0 : ℝ) < 3 / 4) (by linarith only [hε]) hu huv hvT
  have hI : (∫⁻ s in Ioc u v,
      ENNReal.ofReal ((S₂.r u s / S₂.r u v) ^ (3 / 4 : ℝ)) *
        outEnv 0 (jC1 (triangle 0 T) S₂) s) ≤
      ENNReal.ofReal 16 * ∫⁻ s in Icc u v,
        ENNReal.ofReal ((S₁.r u s / S₁.r u v) ^ (3 / 4 : ℝ)) *
          outEnv 0 (jC1 (triangle 0 T) S₂) s := by
    apply (lintegral_mono_set (show Ioc u v ⊆ Icc u v from
      fun _ hs => ⟨hs.1.le, hs.2⟩)).trans
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' measurableSet_Icc
    intro s hs
    have hsT := hs.2.trans hvT
    have hr₁ := stab_radius_bounds h₁s hu hs.1 hsT
    have hr₂ := stab_radius_bounds h₂s hu hs.1 hsT
    have hc := stab_radius_power_compare
      (show 0 ≤ S₁.r u s by linarith only [hr₁.1, hs.1])
      (show 0 ≤ S₂.r u s by linarith only [hr₂.1, hs.1])
      (h₁s.c1.r_pos (u, v) ⟨hu, huv.le, hvT⟩ huv)
      (h₂s.c1.r_pos (u, v) ⟨hu, huv.le, hvT⟩ huv)
      (stab_radius_compare h₁s h₂s hu hs.1 hsT).2
      (stab_radius_compare h₁s h₂s hu huv.le hvT).1
      (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) ≤ 1)
    have hc' := ENNReal.ofReal_le_ofReal hc
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)] at hc'
    simpa only [mul_assoc] using mul_le_mul' hc' (le_rfl :
      outEnv 0 (jC1 (triangle 0 T) S₂) s ≤ outEnv 0 (jC1 (triangle 0 T) S₂) s)
  apply hm.trans
  calc
    _ ≤ ENNReal.ofReal 4 * (ENNReal.ofReal 16 * ∫⁻ s in Icc u v,
        ENNReal.ofReal ((S₁.r u s / S₁.r u v) ^ (3 / 4 : ℝ)) *
          outEnv 0 (jC1 (triangle 0 T) S₂) s) := mul_le_mul' le_rfl hI
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num

end EmcsfAcExtension.Local
