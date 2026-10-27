/- Copyright (c) 2026. All rights reserved. -/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Absolute continuity of an integrable function's mass

Small-set and translation-uniform interval versions of Mathlib's absolute
continuity of the Lebesgue integral. These are the single-function moduli needed
by the ordered-kernel nonconcentration argument at `charged_SF_new_version.tex:L5072–L5072`.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace EmcsfAcExtension

variable {α β : Type*} [MeasurableSpace α] [NormedAddCommGroup β]

/-- Absolute continuity of the norm integral, with a positive real measure threshold.
The set need not be measurable. The threshold depends only on the function and `ε`. -/
theorem exists_pos_setIntegral_norm_le {g : α → β} {μ : Measure α}
    (hg : Integrable g μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : Set α, μ s ≤ ENNReal.ofReal δ →
      (∫ x in s, ‖g x‖ ∂μ) ≤ ε := by
  obtain ⟨θ, hθ, hbound⟩ := exists_pos_setLIntegral_lt_of_measure_lt
    hg.hasFiniteIntegral.ne (ENNReal.ofReal_pos.mpr hε).ne'
  obtain ⟨δ, _, hδ, hδθ⟩ := ENNReal.lt_iff_exists_real_btwn.mp hθ
  refine ⟨δ, ?_, fun s hs => ?_⟩
  · exact ENNReal.ofReal_pos.mp hδ
  · apply (ENNReal.ofReal_le_ofReal_iff hε.le).mp
    rw [ofReal_integral_norm_eq_lintegral_enorm hg.integrableOn]
    exact (hbound s (hs.trans_lt hδθ)).le

/-- Intervals with sufficiently small nonnegative length have uniformly small mass,
independently of the initial endpoint. -/
theorem exists_pos_integral_norm_Icc_le {g : ℝ → β} (hg : Integrable g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ d : ℝ, d ≤ δ → ∀ a : ℝ,
      (∫ x in Icc a (a + d), ‖g x‖) ≤ ε := by
  obtain ⟨δ, hδ, hbound⟩ := exists_pos_setIntegral_norm_le hg hε
  refine ⟨δ, hδ, fun d hd a => hbound _ ?_⟩
  rw [Real.volume_Icc, add_sub_cancel_left]
  exact ENNReal.ofReal_le_ofReal hd

end EmcsfAcExtension
