module

public import EmcsfAcExtension.Local.Stability.JCloseForcing
public import EmcsfAcExtension.Local.Stability.SourceDifferencePhase
public import EmcsfAcExtension.Local.Stability.SourceDifferenceCoefficient
public import EmcsfAcExtension.Local.Stability.MainRecords
import EmcsfAcExtension.Local.Stability.JCloseFlux
import EmcsfAcExtension.Local.Stability.JCloseForcingAlgebra
import EmcsfAcExtension.Local.Stability.JCloseIntegrability
import EmcsfAcExtension.Local.Stability.SourceDifferenceScalarAreaJ
import EmcsfAcExtension.Local.Stability.SourceDifferenceScalarMeasurable
import EmcsfAcExtension.Local.Stability.SourceDifferenceEMMeasurable
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # The full j forcing area from the first-half comparison records

Each forcing is estimated separately and then combined by Tonelli. The
repaired scalar datum term is retained until the final numerical absorption.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- [internal]
 Complete j difference forcing estimate from internal project record conclusions.
`C` depends only on the fixed envelope and comparison constants `A,D`,
uniformly in the coupling, length, background, pair and derivative suprema. -/
theorem j_forcing_area_of_differences (A D : ℝ) (hA : 0 < A) (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ^ 2 + sigma e M T ≤ 1 / 4 →
      RatioDifferences D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      FieldDifference D T ε (dataDist h₁ h₂ T) S₁ S₂ →
      ChargeDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      PotentialDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      IncomingFluxDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, ‖jDifferenceForcing e T S₁ S₂ u v‖ₑ) ≤
        ENNReal.ofReal (C * dataDist h₁ h₂ T +
          C * (ε ^ 2 + sigma e M T) * ((jDist T S₁ S₂).toReal + (kDist e T S₁ S₂).toReal) +
          C * ε * (ε ^ 2 + sigma e M T) * (geomDist T S₁ S₂).toReal) := by
  obtain ⟨Cf, hCf, hflux⟩ := j_coefficient_area_sharp_of_differences A D hA hD
  obtain ⟨Cp, hCp, hphase⟩ := covariant_transport_phase_difference_of_differences A D hA hD
  obtain ⟨Cs, hCs, hscalar⟩ := scalar_source_j_difference_of_differences A D hA hD
  obtain ⟨Ce, hCe, hem⟩ := electromagnetic_source_difference_sharp_of_differences D hD
  obtain ⟨C, hC, habs⟩ := j_forcing_remainder_absorption Cf Cp Cs Ce hCf hCp hCs hCe
  refine ⟨C, hC, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hsmall hratio hfield hcharge hpot hfl
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
    ((jRealCoefficient S₁ p.1 p.2 - jRealCoefficient S₂ p.1 p.2 : ℝ) : ℂ) * jC1 (triangle 0 T) S₂
        p.1 p.2
  let f₂ := fun p : ℝ × ℝ => -(I * e * (S₁.A p.1 p.2 - S₂.A p.1 p.2) * jC1 (triangle 0 T) S₂ p.1
      p.2)
  let f₃ := fun p : ℝ × ℝ => scalarTransportSourceJ T S₁ p.1 p.2 - scalarTransportSourceJ T S₂ p.1
      p.2
  let f₄ := fun p : ℝ × ℝ => emTransportSourceJ e S₁ p.1 p.2 - emTransportSourceJ e S₂ p.1 p.2
  have hc₁ := (transport_real_coefficients_continuousOn hs₁).1
  have hc₂ := (transport_real_coefficients_continuousOn hs₂).1
  have hj := continuousOn_jC1_aux hs₂.pos hs₂.c1
  have hA₁ := hs₁.c1.c1_A.continuousOn
  have hA₂ := hs₂.c1.c1_A.continuousOn
  have hf₁ : Measurable ((triangle 0 T).indicator f₁) :=
    measurable_triangle_indicator_of_continuousOn (by dsimp only [f₁]; fun_prop)
  have hf₂ : Measurable ((triangle 0 T).indicator f₂) :=
    measurable_triangle_indicator_of_continuousOn (by dsimp only [f₂]; fun_prop)
  have hf₃ : Measurable ((triangle 0 T).indicator f₃) :=
    measurable_triangle_sub (measurable_scalar_source_j hs₁) (measurable_scalar_source_j hs₂)
  have hf₄ : Measurable ((triangle 0 T).indicator f₄) :=
    measurable_triangle_sub (measurable_emTransportSource_pair hs₁).1
        (measurable_emTransportSource_pair hs₂).1
  have harea := incoming_area_le_sum4_norm hf₁ hf₂ hf₃ hf₄
    (q := Function.uncurry (jDifferenceForcing e T S₁ S₂)) (by
      intro p hp
      have heq : jDifferenceForcing e T S₁ S₂ p.1 p.2 = f₁ p + f₂ p + f₃ p + f₄ p := by
        dsimp only [jDifferenceForcing, f₁, f₂, f₃, f₄]
        ring
      rw [show Function.uncurry (jDifferenceForcing e T S₁ S₂) p = _ from heq]
      exact (enorm_add_le _ _).trans (add_le_add
        ((enorm_add_le _ _).trans (add_le_add (enorm_add_le _ _) le_rfl)) le_rfl))
  let Bf := Cf * (ε ^ 2 * K + ε ^ 3 * G + sigma e M T * ε ^ 3 * (J + ε * G + ε * δ / M))
  let Bp := Cp * sigma e M T * (δ + J + ε * G)
  let Bs := Cs * (ε ^ 2 * (J + K) + ε ^ 3 * G + sigma e M T * ε ^ 4 * δ / M)
  let Be := Ce * sigma e M T * (J + K + ε * G + ε * δ / M)
  have hBf : 0 ≤ Bf := by dsimp [Bf, J, K, G]; positivity
  have hBp : 0 ≤ Bp := by dsimp [Bp, J, G]; positivity
  have hBs : 0 ≤ Bs := by dsimp [Bs, J, K, G]; positivity
  have hBe : 0 ≤ Be := by dsimp [Be, J, K, G]; positivity
  have hb₁ : (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, ‖f₁ (u, v)‖ₑ) ≤ ENNReal.ofReal Bf :=
    hflux T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hfl
  have hb₂ : (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, ‖f₂ (u, v)‖ₑ) ≤ ENNReal.ofReal Bp :=
    hphase T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hε₁ hpot
  have hb₃ : (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, ‖f₃ (u, v)‖ₑ) ≤ ENNReal.ofReal Bs := by
    apply (hscalar T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hε₂ hσ₁ hratio).trans_eq
    congr 1
    dsimp only [Bs, J, K, G, δ]
    ring
  have hb₄ : (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, ‖f₄ (u, v)‖ₑ) ≤ ENNReal.ofReal Be := by
    apply le_trans _ (hem T e ε M A S₁ S₂ h₁ h₂ hs₁ hs₂ hε₁ hσ₁ hratio hfield hcharge)
    apply lintegral_mono
    intro v
    apply lintegral_mono
    intro u
    exact le_add_right le_rfl
  calc
    _ ≤ _ := harea
    _ ≤ ENNReal.ofReal Bf + ENNReal.ofReal Bp + ENNReal.ofReal Bs + ENNReal.ofReal Be :=
      add_le_add (add_le_add (add_le_add hb₁ hb₂) hb₃) hb₄
    _ = ENNReal.ofReal (Bf + Bp + Bs + Be) := by
      rw [← ENNReal.ofReal_add hBf hBp, ← ENNReal.ofReal_add (add_nonneg hBf hBp) hBs,
        ← ENNReal.ofReal_add (add_nonneg (add_nonneg hBf hBp) hBs) hBe]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (habs ε (sigma e M T) M δ J K G hε hε₁ hσ hσ₁
      hs₂.box.1 hδ ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)

end EmcsfAcExtension.Local.Stab
