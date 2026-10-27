/- Copyright (c) 2026. All rights reserved. -/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Power-weight integrals for ordered kernels

Exact primitives and universal bounds for the weights in
`charged_SF_new_version.tex:L5072–L5072`, `L5057–L5077`, and `L6224–L6227`.
The constants depend only on the displayed exponent.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension

/-- The real ordered power kernel. Its values on the diagonal use Lean's total
real powers and division; for positive exponent its numerator vanishes there. -/
@[expose] noncomputable def orderedPowerKernel (p a w v : ℝ) : ℝ :=
  (w - a) ^ p / (v - a) ^ (1 + p)

/-- Nonnegativity on the ordered region. -/
theorem orderedPowerKernel_nonneg {p a w v : ℝ} (haw : a ≤ w) (hwv : w ≤ v) :
    0 ≤ orderedPowerKernel p a w v :=
  div_nonneg (Real.rpow_nonneg (sub_nonneg.mpr haw) _)
    (Real.rpow_nonneg (sub_nonneg.mpr (haw.trans hwv)) _)

/-- Away from the initial vertex, the outgoing kernel is interval integrable. -/
theorem intervalIntegrable_orderedPowerKernel {p a w V : ℝ} (haw : a < w) (hwV : w ≤ V) :
    IntervalIntegrable (orderedPowerKernel p a w) volume w V := by
  apply ContinuousOn.intervalIntegrable
  unfold orderedPowerKernel
  apply continuousOn_const.div
  · exact (continuousOn_id.sub continuousOn_const).rpow_const
      (fun x hx => Or.inl (ne_of_gt (by
        rw [uIcc_of_le hwV] at hx
        exact sub_pos.mpr (haw.trans_le hx.1))))
  · intro x hx
    rw [uIcc_of_le hwV] at hx
    exact ne_of_gt (Real.rpow_pos_of_pos (sub_pos.mpr (haw.trans_le hx.1)) _)

/-- Exact outgoing primitive; the missing tail is displayed explicitly. -/
theorem integral_orderedPowerKernel_eq {p a w V : ℝ}
    (hp : 0 < p) (haw : a < w) (hwV : w ≤ V) :
    (∫ v in w..V, orderedPowerKernel p a w v) =
      (1 - (w - a) ^ p * (V - a) ^ (-p)) / p := by
  have hw : 0 < w - a := sub_pos.mpr haw
  have hr : -(1 + p) ≠ -1 := by linarith only [hp]
  have hz : (0 : ℝ) ∉ uIcc (w - a) (V - a) := by
    rw [uIcc_of_le (sub_le_sub_right hwV a)]
    exact fun h => (not_le_of_gt hw) h.1
  unfold orderedPowerKernel
  have heq : (∫ v in w..V, (w - a) ^ p / (v - a) ^ (1 + p)) =
      ∫ v in w..V, (w - a) ^ p * (v - a) ^ (-(1 + p)) := by
    apply intervalIntegral.integral_congr
    intro v hv
    dsimp only
    rw [uIcc_of_le hwV] at hv
    rw [Real.rpow_neg (sub_nonneg.mpr (haw.le.trans hv.1)), div_eq_mul_inv]
  rw [heq, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right (fun x : ℝ => x ^ (-(1 + p))) a,
    integral_rpow (Or.inr ⟨hr, hz⟩)]
  have hexp : -(1 + p) + 1 = -p := by ring
  rw [hexp, Real.rpow_neg hw.le]
  have hwne := ne_of_gt (Real.rpow_pos_of_pos hw p)
  field_simp
  ring

/-- The outgoing weight has total mass at most `1/p`, uniformly in all endpoints. -/
theorem integral_orderedPowerKernel_le {p a w V : ℝ}
    (hp : 0 < p) (haw : a < w) (hwV : w ≤ V) :
    (∫ v in w..V, orderedPowerKernel p a w v) ≤ 1 / p := by
  rw [integral_orderedPowerKernel_eq hp haw hwV]
  exact div_le_div_of_nonneg_right
    (sub_le_self _ (mul_nonneg (Real.rpow_nonneg (sub_nonneg.mpr haw.le) _)
      (Real.rpow_nonneg (sub_nonneg.mpr (haw.le.trans hwV)) _))) hp.le

/-- Exact integral in the middle variable. The optimal range is `-1 < p`. -/
theorem integral_orderedPowerKernel_middle {p a v : ℝ} (hp : -1 < p) (hav : a < v) :
    (∫ w in a..v, orderedPowerKernel p a w v) = 1 / (1 + p) := by
  have hv : 0 < v - a := sub_pos.mpr hav
  have hp1 : p + 1 ≠ 0 := ne_of_gt (by linarith only [hp])
  unfold orderedPowerKernel
  simp_rw [div_eq_mul_inv]
  rw [intervalIntegral.integral_mul_const,
    intervalIntegral.integral_comp_sub_right (fun x : ℝ => x ^ p) a,
    integral_rpow (Or.inl hp), sub_self, Real.zero_rpow hp1]
  rw [show 1 + p = p + 1 by ring]
  have hvne := ne_of_gt (Real.rpow_pos_of_pos hv (p + 1))
  field_simp
  ring

/-- Exact reflected primitive below the singularity, with arbitrary ordered endpoints. -/
theorem integral_reflected_rpow_eq {p b c v : ℝ} (hp : -1 < p)
    (hbc : b ≤ c) (hcv : c < v) :
    (∫ s in b..c, (v - s) ^ (-p - 2)) =
      ((v - c) ^ (-(p + 1)) - (v - b) ^ (-(p + 1))) / (p + 1) := by
  have hz : (0 : ℝ) ∉ uIcc (v - c) (v - b) := by
    rw [uIcc_of_le (sub_le_sub_left hbc v)]
    exact fun h => (not_le_of_gt (sub_pos.mpr hcv)) h.1
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-p - 2)) v,
    integral_rpow (Or.inr ⟨by linarith only [hp], hz⟩)]
  rw [show -p - 2 + 1 = -(p + 1) by ring, div_neg]
  ring

/-- The outgoing mass bound as a nonnegative Lebesgue integral, including `a = w`. -/
theorem lintegral_orderedPowerKernel_le {p a w V : ℝ}
    (hp : 0 < p) (haw : a ≤ w) (hwV : w ≤ V) :
    (∫⁻ v in Icc w V, ENNReal.ofReal (orderedPowerKernel p a w v)) ≤
      ENNReal.ofReal (1 / p) := by
  rcases haw.eq_or_lt with h | h
  · subst w
    simp only [orderedPowerKernel, sub_self, Real.zero_rpow hp.ne', zero_div,
      ENNReal.ofReal_zero, lintegral_zero]
    exact zero_le
  · have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hwV).mp
      (intervalIntegrable_orderedPowerKernel h hwV)
    have hnonneg : 0 ≤ᵐ[volume.restrict (Icc w V)] orderedPowerKernel p a w := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
      exact orderedPowerKernel_nonneg h.le hv.1
    rw [← ofReal_integral_eq_lintegral_ofReal hi hnonneg,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hwV]
    exact ENNReal.ofReal_le_ofReal (integral_orderedPowerKernel_le hp h hwV)

end EmcsfAcExtension
