module

public import EmcsfAcExtension.Local.Stability.DifferenceMomentsIncomingBudget
import EmcsfAcExtension.Local.Stability.DifferenceMomentsIncomingRaw
import EmcsfAcExtension.Local.Stability.DifferenceMomentsIncomingHardyRaw

/-! # Unabsorbed incoming supremum and Hardy estimates

The exact forcing budget controls both radial norms before the optical
mass feedback is absorbed. Envelope dependence remains explicit as `A ε`.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The incoming difference on any section is bounded by the unabsorbed
budget with universal coefficient `8192`, independently of every field
parameter and minimum radius. The factor `A ε` is displayed explicitly. -/
theorem stab_in_difference_point_before_absorption
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : 3 * ε ^ 2 ≤ 1 / 2)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ENNReal.ofReal ‖S₁.xi u v / (S₁.nu u v : ℂ) -
      S₂.xi u v / (S₂.nu u v : ℂ)‖ ≤
      8192 * (kDist e T S₁ S₂ +
        ENNReal.ofReal ((geomDist T S₁ S₂).toReal +
          T * |e| * (supDist T S₁.A S₂.A).toReal + (supDist T S₁.mu S₂.mu).toReal) *
          ENNReal.ofReal (A * ε)) := by
  let q := fun t : ℝ =>
    kC1 e (triangle 0 T) S₁ t v / ((1 - S₁.mu t v : ℝ) : ℂ) -
    kC1 e (triangle 0 T) S₂ t v / ((1 - S₂.mu t v : ℝ) : ℂ) -
    (S₁.nu t v / S₁.r t v - S₂.nu t v / S₂.r t v) •
      (S₂.xi t v / (S₂.nu t v : ℂ) -
        ‖S₂.xi t v / (S₂.nu t v : ℂ)‖ ^ 2 • (S₂.xi t v / (S₂.nu t v : ℂ))) -
    (e * (S₁.A t v - S₂.A t v)) • (Complex.I * (S₂.xi t v / (S₂.nu t v : ℂ)))
  have hm := stab_in_difference_moment_raw h₁s h₂s hε hu huv hvT
  have hq := stab_in_difference_forcing_lintegral_le h₁s h₂s hε (hu.trans huv.le) hvT
  apply hm.trans
  apply le_trans ?_ hq
  apply le_trans ?_ (lintegral_mono_set (Icc_subset_Icc_left hu))
  apply setLIntegral_mono' measurableSet_Icc
  intro t ht
  apply ENNReal.ofReal_le_ofReal
  have hr : 0 < S₁.r u v := h₁s.c1.r_pos (u, v) ⟨hu, huv.le, hvT⟩ huv
  have hrt := (stab_radius_bounds h₁s (hu.trans ht.1) ht.2 hvT).1
  have hrt0 : 0 ≤ S₁.r t v := by linarith only [hrt, ht.2]
  have hpow := Real.rpow_le_one (div_nonneg hrt0 hr.le)
    ((div_le_one hr).mpr (stab_radius_section_order h₁s hu ht.1 ht.2 hvT).2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow (norm_nonneg (q t))

/-- The incoming weighted difference has the unabsorbed budget with
universal coefficient `16384`. No mass difference estimate is assumed,
and all envelope dependence remains in the explicit factor `A ε`. -/
theorem stab_in_difference_hardy_before_absorption
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : 3 * ε ^ 2 ≤ 1 / 2)
    {v : ℝ} (hv : 0 ≤ v) (hvT : v ≤ T) :
    (∫⁻ s in Icc 0 v, ENNReal.ofReal (-S₁.nu s v / S₁.r s v *
      ‖S₁.xi s v / (S₁.nu s v : ℂ) - S₂.xi s v / (S₂.nu s v : ℂ)‖)) ≤
      16384 * (kDist e T S₁ S₂ +
        ENNReal.ofReal ((geomDist T S₁ S₂).toReal +
          T * |e| * (supDist T S₁.A S₂.A).toReal + (supDist T S₁.mu S₂.mu).toReal) *
          ENNReal.ofReal (A * ε)) := by
  rcases hv.eq_or_lt with rfl | hv
  · simp
  · have hh := stab_in_difference_hardy_raw h₁s h₂s hε le_rfl hv hvT
    have hq := stab_in_difference_forcing_lintegral_le h₁s h₂s hε hv.le hvT
    apply hh.trans
    apply (mul_le_mul' le_rfl hq).trans_eq
    norm_num only [ENNReal.ofReal_ofNat]
    ring

end EmcsfAcExtension.Local
