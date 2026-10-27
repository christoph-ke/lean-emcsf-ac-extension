module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.PotentialHardyPrimitive
import EmcsfAcExtension.Local.Stability.PotentialChargePrimitiveDiff
import EmcsfAcExtension.Local.Stability.MomentsSections
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # The charge difference Hardy forcing

The positive primitive theorem applies to the actual local scalar ratio
difference and the second solution's vanishing ratio. No uniform scalar
error is integrated against an isolated singular endpoint weight.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- Common-radius charge Hardy comparison with its complete local
forcing retained. The coefficients `1/2` and `8` are universal, uniform
in all solution, data, scale and coupling parameters and derivative
suprema. No smallness or prior integrability conclusion is assumed.
-/
theorem stab_charge_difference_hardy_raw_c1
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    (∫⁻ t in Icc u v, ENNReal.ofReal
      (S₁.lam u t * |S₁.Q u t - S₂.Q u t| / S₁.r u t ^ 3)) ≤
      ENNReal.ofReal (|e| / 2) * ∫⁻ t in Icc u v, ENNReal.ofReal
        (S₁.lam u t / S₁.r u t *
          (M * ‖S₁.theta u t / (S₁.lam u t : ℂ) - S₂.theta u t / (S₂.lam u t : ℂ)‖ +
            ((supDist T S₁.phi S₂.phi).toReal + 8 * (geomDist T S₁ S₂).toReal * M) *
              ‖S₂.theta u t / (S₂.lam u t : ℂ)‖)) := by
  let Φ := (supDist T S₁.phi S₂.phi).toReal
  let G := (geomDist T S₁ S₂).toReal
  let f := fun t => M *
    ‖S₁.theta u t / (S₁.lam u t : ℂ) - S₂.theta u t / (S₂.lam u t : ℂ)‖ +
      (Φ + 8 * G * M) * ‖S₂.theta u t / (S₂.lam u t : ℂ)‖
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans h₁s.box.1
  have hΦ : 0 ≤ Φ := ENNReal.toReal_nonneg
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hmap : MapsTo (fun t : ℝ => (u, t)) (Icc u v) (triangle 0 T) :=
    fun t ht => ⟨hu, ht.1, ht.2.trans hvT⟩
  have cX₁ := (stab_out_ratio_c1 h₁s.c1).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cX₂ := (stab_out_ratio_c1 h₂s.c1).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cf : ContinuousOn f (Icc u v) :=
    ((cX₁.sub cX₂).norm.const_mul M).add (cX₂.norm.const_mul (Φ + 8 * G * M))
  have hf : ∀ t ∈ Icc u v, 0 ≤ f t := by
    intro t ht
    dsimp only [f]
    positivity
  exact stab_charge_primitive_hardy_of_c1_bound h₁s hu huv hvT (abs_nonneg e) cf hf
    (fun t ht => stab_charge_difference_primitive_le_c1 h₁s h₂s hu ht.1 (ht.2.trans hvT))

end EmcsfAcExtension.Local
