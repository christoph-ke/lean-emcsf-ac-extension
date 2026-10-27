module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.BootstrapBox
import EmcsfAcExtension.Local.Api.Mono
import EmcsfAcExtension.Infra.AC.Variation

/-! # One standing setting for a fixed datum

For finite derivative bounds it suffices to choose one positive variation
margin before the constructed apex. The canonical background for that
margin is controlled by twice the datum's background, so universal charged
scale thresholds remain uniform over all complete subtriangles.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- Choose positive thresholds and a positive variation margin before the
datum. On every existing positive complete subtriangle the standing
setting and any prescribed positive charged-scale threshold then hold.
The constants depend only on the supplied universal caps `α,β`, uniformly
in data, higher derivatives, and the constructed apex. -/
theorem smooth_uniform_settings_aux {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∃ ε₀ δ₀ η : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧ 0 < η ∧ η ≤ α ∧
    ∀ (T e : ℝ) (h : ℝ → ℂ), 0 < T → ContDiffOn ℝ 1 h (Icc 0 T) →
      datumVar h T ≤ ε₀ → chargedScale e h T ≤ δ₀ →
      ∀ (s : ℝ) (S : Fields), 0 < s → s ≤ T →
        IsC1Solution e S (triangle 0 s) → IsRestartData S h s →
        AprioriSetting e s η (1 + ‖h 0‖ + 10 * η) S h ∧
        |e| * (s / 2) * (1 + ‖h 0‖ + 10 * η) ≤ β := by
  obtain ⟨εb, δb, hεb, hδb, hbox⟩ := bootBox_of_positive_margin
  let η := min (1 / 20) (min α εb) / 2
  have hη : 0 < η := half_pos (lt_min (by norm_num) (lt_min hα hεb))
  have hηα : η ≤ α := (half_le_self (le_min (by norm_num)
    (le_min hα.le hεb.le))).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηb : η ≤ εb := (half_le_self (le_min (by norm_num)
    (le_min hα.le hεb.le))).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hη20 : η ≤ 1 / 20 := (half_le_self (le_min (by norm_num)
    (le_min hα.le hεb.le))).trans (min_le_left _ _)
  refine ⟨η / 2, min β δb / 2, η, by positivity,
    half_pos (lt_min hβ hδb), hη, hηα, ?_⟩
  intro T e h hT hh hε hδ s S hs hsT hS hdata
  have hac : AbsolutelyContinuousOnInterval h 0 T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hT.le] using hh
  have hfinite := hac.boundedVariationOn_Icc hT.le
  have hvar : datumVar h s ≤ datumVar h T := ENNReal.toReal_mono hfinite
    (eVariationOn.mono h (Icc_subset_Icc le_rfl hsT))
  have hd : 0 ≤ datumVar h T := ENNReal.toReal_nonneg
  have hn : 0 ≤ ‖h 0‖ := norm_nonneg _
  have hM0 : 0 ≤ datumM h T := by dsimp only [datumM]; positivity
  have hmargin : datumVar h s < η := by linarith only [hvar, hε, hη]
  have hM : 1 + ‖h 0‖ + 10 * η ≤ 2 * datumM h T := by
    dsimp only [datumM]
    linarith only [hη20, hd, hn]
  have hM' : 0 ≤ 1 + ‖h 0‖ + 10 * η := by positivity
  have hscale : |e| * (s / 2) * (1 + ‖h 0‖ + 10 * η) ≤ min β δb := by
    have hh' : |e| * (s / 2) * (1 + ‖h 0‖ + 10 * η) ≤
        |e| * (T / 2) * (2 * datumM h T) := by
      apply mul_le_mul _ hM hM' (by positivity : 0 ≤ |e| * (T / 2))
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hsT (by norm_num)) (abs_nonneg e)
    change |e| * (T / 2) * datumM h T ≤ min β δb / 2 at hδ
    nlinarith only [hh', hδ]
  refine ⟨⟨hs, hS, hdata, hmargin.le, rfl, ?_⟩,
    hscale.trans (min_le_left _ _)⟩
  exact hbox e s η (1 + ‖h 0‖ + 10 * η) S h hs hS hdata hmargin rfl hηb
    (hscale.trans (min_le_right _ _))

end EmcsfAcExtension.Local
