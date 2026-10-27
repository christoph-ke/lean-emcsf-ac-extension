module

public import EmcsfAcExtension.Local.Stability.JCloseForcing
public import EmcsfAcExtension.Local.Stability.KCloseFlux
public import EmcsfAcExtension.Local.Stability.MainRecords
import EmcsfAcExtension.Local.Stability.JCloseForcingAlgebra
import EmcsfAcExtension.Local.Stability.JCloseIntegrability
import EmcsfAcExtension.Local.Stability.SourceDifferenceArea
import EmcsfAcExtension.Local.Stability.SourceDifferenceScalarAreaK
import EmcsfAcExtension.Local.Stability.SourceDifferenceScalarMeasurable
import EmcsfAcExtension.Local.Stability.SourceDifferenceEMMeasurable
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Full k forcing area with the repaired datum remainder

The outgoing coefficient forcing is placed in the common incoming area
order using its measurable zero extension before the three estimates are added.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- [internal]
 Complete k forcing from internal project record conclusions, retaining the approved
`C σ ε Δ₀/M` repair. `C` depends only on the fixed constants `A,D`, uniformly
in the coupling, length, background, pair and all derivative suprema. -/
theorem k_forcing_area_of_differences (A D : ℝ) (hA : 0 < A) (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ^ 2 + sigma e M T ≤ 1 / 4 →
      RatioDifferences D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      FieldDifference D T ε (dataDist h₁ h₂ T) S₁ S₂ →
      ChargeDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      OutgoingFluxDifference D T ε S₁ S₂ →
      (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, ‖kDifferenceForcing e T S₁ S₂ u v‖ₑ) ≤
        ENNReal.ofReal (C * (ε ^ 2 + sigma e M T) *
          ((jDist T S₁ S₂).toReal + (kDist e T S₁ S₂).toReal) +
          C * ε * (ε ^ 2 + sigma e M T) * (geomDist T S₁ S₂).toReal +
          C * sigma e M T * ε * dataDist h₁ h₂ T / M) := by
  obtain ⟨Cf, hCf, hflux⟩ := k_homogeneous_coefficient_difference_of_differences A D hA hD
  obtain ⟨Cs, hCs, hscalar⟩ := scalar_source_k_difference_of_differences A D hA hD
  obtain ⟨Ce, hCe, hem⟩ := electromagnetic_source_difference_sharp_of_differences D hD
  obtain ⟨C, hC, habs⟩ := k_forcing_remainder_absorption Cf Cs Ce hCf hCs hCe
  refine ⟨C, hC, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hsmall hratio hfield hcharge hfl
  let J := (jDist T S₁ S₂).toReal
  let K := (kDist e T S₁ S₂).toReal
  let G := (geomDist T S₁ S₂).toReal
  let δ := dataDist h₁ h₂ T
  have hδ : 0 ≤ δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hε : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans
    (hs₂.box.2 (0, 0) ⟨le_rfl, le_rfl, hs₂.pos.le⟩).2.2.2.2.2.1
  have hM : 0 ≤ M := zero_le_one.trans hs₂.box.1
  have hσ : 0 ≤ sigma e M T := by unfold sigma; positivity
  have hε₂ : ε ^ 2 ≤ 1 / 4 := (le_add_of_nonneg_right hσ).trans hsmall
  have hε₁ : ε ≤ 1 := by nlinarith only [hε₂]
  have hσ₁ : sigma e M T ≤ 1 := by nlinarith only [hsmall, sq_nonneg ε]
  let f₁ := fun p : ℝ × ℝ =>
    ((kRealCoefficient S₁ p.1 p.2 - kRealCoefficient S₂ p.1 p.2 : ℝ) : ℂ) * kC1 e (triangle 0 T) S₂
        p.1 p.2
  let f₂ := fun p : ℝ × ℝ => scalarTransportSourceK e T S₁ p.1 p.2 - scalarTransportSourceK e T S₂
      p.1 p.2
  let f₃ := fun p : ℝ × ℝ => emTransportSourceK e S₁ p.1 p.2 - emTransportSourceK e S₂ p.1 p.2
  let f₄ := fun _p : ℝ × ℝ => (0 : ℂ)
  have hc₁ := (transport_real_coefficients_continuousOn hs₁).2
  have hc₂ := (transport_real_coefficients_continuousOn hs₂).2
  have hk := continuousOn_kC1_aux hs₂.pos hs₂.c1
  have hf₁ : Measurable ((triangle 0 T).indicator f₁) :=
    measurable_triangle_indicator_of_continuousOn (by dsimp only [f₁]; fun_prop)
  have hf₂ : Measurable ((triangle 0 T).indicator f₂) :=
    measurable_triangle_sub (measurable_scalar_source_k hs₁) (measurable_scalar_source_k hs₂)
  have hf₃ : Measurable ((triangle 0 T).indicator f₃) :=
    measurable_triangle_sub (measurable_emTransportSource_pair hs₁).2
        (measurable_emTransportSource_pair hs₂).2
  have hf₄ : Measurable ((triangle 0 T).indicator f₄) :=
    measurable_const.indicator (measurableSet_triangle 0 T)
  have harea := incoming_area_le_sum4_norm hf₁ hf₂ hf₃ hf₄
    (q := Function.uncurry (kDifferenceForcing e T S₁ S₂)) (by
      intro p hp
      have heq : kDifferenceForcing e T S₁ S₂ p.1 p.2 = f₁ p + f₂ p + f₃ p + f₄ p := by
        dsimp only [kDifferenceForcing, f₁, f₂, f₃, f₄]
        ring
      rw [show Function.uncurry (kDifferenceForcing e T S₁ S₂) p = _ from heq]
      exact (enorm_add_le _ _).trans (add_le_add
        ((enorm_add_le _ _).trans (add_le_add (enorm_add_le _ _) le_rfl)) le_rfl))
  let Bf := Cf * (ε ^ 2 * J + ε ^ 3 * G)
  let Bs := Cs * (ε ^ 2 * (J + K) + ε ^ 3 * G + sigma e M T * ε ^ 4 * δ / M)
  let Be := Ce * sigma e M T * (J + K + ε * G + ε * δ / M)
  have hBf : 0 ≤ Bf := by dsimp [Bf, J, G]; positivity
  have hBs : 0 ≤ Bs := by dsimp [Bs, J, K, G]; positivity
  have hBe : 0 ≤ Be := by dsimp [Be, J, K, G]; positivity
  have hb₁ : (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, ‖f₁ (u, v)‖ₑ) ≤ ENNReal.ofReal Bf := by
    rw [← outgoing_area_eq_incoming_of_measurable_indicator
      (measurable_triangle_enorm_of_measurable_indicator hf₁)]
    exact hflux T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hfl
  have hb₂ : (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, ‖f₂ (u, v)‖ₑ) ≤ ENNReal.ofReal Bs := by
    apply (hscalar T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hε₂ hσ₁ hratio).trans_eq
    congr 1
    dsimp only [Bs, J, K, G, δ]
    ring
  have hb₃ : (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, ‖f₃ (u, v)‖ₑ) ≤ ENNReal.ofReal Be := by
    apply le_trans _ (hem T e ε M A S₁ S₂ h₁ h₂ hs₁ hs₂ hε₁ hσ₁ hratio hfield hcharge)
    apply lintegral_mono
    intro v
    apply lintegral_mono
    intro u
    exact le_add_left le_rfl
  have hb₄ : (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, ‖f₄ (u, v)‖ₑ) = 0 := by simp [f₄]
  calc
    _ ≤ _ := harea
    _ ≤ ENNReal.ofReal Bf + ENNReal.ofReal Bs + ENNReal.ofReal Be + 0 :=
      add_le_add (add_le_add (add_le_add hb₁ hb₂) hb₃) hb₄.le
    _ = ENNReal.ofReal (Bf + Bs + Be) := by
      rw [add_zero, ← ENNReal.ofReal_add hBf hBs, ← ENNReal.ofReal_add (add_nonneg hBf hBs) hBe]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (habs ε (sigma e M T) M δ J K G hε hε₁ hσ hσ₁
      hs₂.box.1 hδ ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)

end EmcsfAcExtension.Local.Stab
