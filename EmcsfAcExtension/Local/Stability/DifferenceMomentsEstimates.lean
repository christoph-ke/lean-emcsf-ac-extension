module

public import EmcsfAcExtension.Local.Stability.DifferenceMomentsBudget
import EmcsfAcExtension.Local.Stability.DifferenceMomentsRaw
import EmcsfAcExtension.Local.Stability.DifferenceMomentsHardyRaw

/-! # Unabsorbed outgoing supremum and Hardy estimates

The exact forcing budget controls both radial norms before the optical
mass feedback is absorbed. Envelope dependence remains explicit as `A ε`.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The outgoing difference on any section is bounded by the unabsorbed
budget with universal coefficient `8192`, independently of every field
parameter and minimum radius. The factor `A ε` is displayed explicitly. -/
theorem stab_out_difference_point_before_absorption
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : 3 * ε ^ 2 ≤ 1 / 2)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ENNReal.ofReal ‖S₁.theta u v / (S₁.lam u v : ℂ) -
      S₂.theta u v / (S₂.lam u v : ℂ)‖ ≤
      8192 * (jDist T S₁ S₂ +
        ENNReal.ofReal ((geomDist T S₁ S₂).toReal + (supDist T S₁.mu S₂.mu).toReal) *
          ENNReal.ofReal (A * ε)) := by
  let q := fun t : ℝ =>
    jC1 (triangle 0 T) S₁ u t / ((1 - S₁.mu u t : ℝ) : ℂ) -
    jC1 (triangle 0 T) S₂ u t / ((1 - S₂.mu u t : ℝ) : ℂ) -
    (S₁.lam u t / S₁.r u t - S₂.lam u t / S₂.r u t) •
      (S₂.theta u t / (S₂.lam u t : ℂ) -
        ‖S₂.theta u t / (S₂.lam u t : ℂ)‖ ^ 2 • (S₂.theta u t / (S₂.lam u t : ℂ)))
  have hm := stab_out_difference_moment_raw h₁s h₂s hε hu huv hvT
  have hq := stab_out_difference_forcing_lintegral_le h₁s h₂s hε hu (huv.le.trans hvT)
  apply hm.trans
  apply le_trans ?_ hq
  apply le_trans ?_ (lintegral_mono_set (Ioc_subset_Ioc_right hvT))
  apply setLIntegral_mono' measurableSet_Ioc
  intro t ht
  apply ENNReal.ofReal_le_ofReal
  have hr : 0 < S₁.r u v := h₁s.c1.r_pos (u, v) ⟨hu, huv.le, hvT⟩ huv
  have hrt : 0 < S₁.r u t := h₁s.c1.r_pos (u, t) ⟨hu, ht.1.le, ht.2.trans hvT⟩ ht.1
  have hpow := Real.rpow_le_one (div_nonneg hrt.le hr.le)
    ((div_le_one hr).mpr (stab_radius_section_order h₁s hu ht.1.le ht.2 hvT).1)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow (norm_nonneg (q t))

/-- The outgoing weighted difference has the unabsorbed budget with
universal coefficient `16384`. No mass difference estimate is assumed,
and all envelope dependence remains in the explicit factor `A ε`. -/
theorem stab_out_difference_hardy_before_absorption
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : 3 * ε ^ 2 ≤ 1 / 2)
    {u : ℝ} (hu : 0 ≤ u) (huT : u ≤ T) :
    (∫⁻ s in Ioc u T, ENNReal.ofReal (S₁.lam u s / S₁.r u s *
      ‖S₁.theta u s / (S₁.lam u s : ℂ) - S₂.theta u s / (S₂.lam u s : ℂ)‖)) ≤
      16384 * (jDist T S₁ S₂ +
        ENNReal.ofReal ((geomDist T S₁ S₂).toReal + (supDist T S₁.mu S₂.mu).toReal) *
          ENNReal.ofReal (A * ε)) := by
  rcases huT.eq_or_lt with rfl | huT
  · simp only [Ioc_self, Measure.restrict_empty, lintegral_zero_measure]
    exact bot_le
  · have hh := stab_out_difference_hardy_raw h₁s h₂s hε hu huT le_rfl
    have hq := stab_out_difference_forcing_lintegral_le h₁s h₂s hε hu huT.le
    apply hh.trans
    apply (mul_le_mul' le_rfl hq).trans_eq
    norm_num only [ENNReal.ofReal_ofNat]
    ring

end EmcsfAcExtension.Local
