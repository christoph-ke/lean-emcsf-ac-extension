module

public import EmcsfAcExtension.Local.Stability.JCloseForcingArea
import EmcsfAcExtension.Local.Stability.JCloseInitialLipschitz
import EmcsfAcExtension.Local.Stability.JCloseBudget
import EmcsfAcExtension.Local.Stability.JCloseEnvelope
import EmcsfAcExtension.Local.Stability.JCloseIntegrability
import EmcsfAcExtension.Local.Stability.MainFinite
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Closure of the outgoing renormalized derivative comparison

The full forcing is integrable on the triangle before variation of
constants is applied. No characteristic AC or initial-j bound is assumed.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- [internal]
 Conditional helper for `restart-stab-j-close`, charged_SF_new_version.tex:L5343–5347.
The only difference inputs are the listed first-half conclusion records.
Constants depend only on their fixed constant `D` and the fixed independent
envelope constant `A`, uniformly in all physical parameters and derivatives. -/
theorem j_close_of_differences (A D : ℝ) (hA : 0 < A) (hD : 0 < D) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
    ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ^ 2 + sigma e M T ≤ η →
      RatioDifferences D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      FieldDifference D T ε (dataDist h₁ h₂ T) S₁ S₂ →
      ChargeDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      PotentialDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      IncomingFluxDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      (jDist T S₁ S₂).toReal ≤ C * dataDist h₁ h₂ T +
        C * (ε ^ 2 + sigma e M T) * ((jDist T S₁ S₂).toReal + (kDist e T S₁ S₂).toReal) +
        C * ε * (ε ^ 2 + sigma e M T) * (geomDist T S₁ S₂).toReal := by
  obtain ⟨Ch, hCh, hprop⟩ := j_propagator_budget
  obtain ⟨ηi, Ci, hηi, hCi, hinit⟩ := initial_j_lipschitz A hA
  obtain ⟨Cf, hCf, hforce⟩ := j_forcing_area_of_differences A D hA hD
  let C := Real.exp 1 * (Ci + Cf)
  refine ⟨min (1 / 4) (min ηi (1 / (Ch * A))), C,
    lt_min (by norm_num) (lt_min hηi (by positivity)), by dsimp [C]; positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hsmall hratio hfield hcharge hpot hflux
  have hσ : 0 ≤ sigma e M T := by unfold sigma; positivity
  have hε : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans
    (hs₂.box.2 (0, 0) ⟨le_rfl, le_rfl, hs₂.pos.le⟩).2.2.2.2.2.1
  have hquarter := hsmall.trans (min_le_left _ _)
  have hε₂ : ε ^ 2 ≤ 1 / 4 := (le_add_of_nonneg_right hσ).trans hquarter
  have hi := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hamp' : ε ^ 2 ≤ 1 / (Ch * A) :=
    (le_add_of_nonneg_right hσ).trans (hsmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hamp : Ch * A * ε ^ 2 ≤ 1 := by
    have h := (le_div_iff₀ (mul_pos hCh hA)).mp hamp'
    nlinarith only [h]
  let δ := dataDist h₁ h₂ T
  let J := (jDist T S₁ S₂).toReal
  let K := (kDist e T S₁ S₂).toReal
  let G := (geomDist T S₁ S₂).toReal
  let B := Cf * δ + Cf * (ε ^ 2 + sigma e M T) * (J + K) +
    Cf * ε * (ε ^ 2 + sigma e M T) * G
  have hδ : 0 ≤ δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hB : 0 ≤ B := by dsimp [B, J, K, G]; positivity
  have hforcing := hforce T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hquarter hratio hfield hcharge hpot hflux
  have hqmeas := (measurable_difference_forcings hs₁ hs₂).1
  have hqint := integrableOn_triangle_of_incoming_area_ne_top hqmeas
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hforcing)
  let g := fun u v => jC1 (triangle 0 T) S₁ u v - jC1 (triangle 0 T) S₂ u v
  have hg : ContinuousOn (Function.uncurry g) (triangle 0 T) := by
    simpa only [g, Function.uncurry_def, Pi.sub_def] using!
      (continuousOn_jC1_aux hs₁.pos hs₁.c1).sub (continuousOn_jC1_aux hs₂.pos hs₂.c1)
  have hc (v : ℝ) (hv : v ∈ Icc 0 T) :
      IntervalIntegrable (fun u => (jRealCoefficient S₁ u v : ℂ) - I * e * S₁.A u v) volume 0 v :=
          by
    simpa only [Function.comp_apply, Function.uncurry_def, id_eq] using!
      ((transport_complex_coefficients_continuousOn hs₁).1.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (show MapsTo (fun u => (u, v)) (Icc 0 v) (triangle 0 T) from
        fun u hu => ⟨hu.1, hu.2, hv.2⟩)).intervalIntegrable_of_Icc (μ := volume) hv.1
  have htransport := outEnv_integral_le_of_transport (B := 1) hs₁.pos.le hg hc
    (ae_intervalIntegrable_triangle_right hqint)
    (fun v hv u hu => (j_difference_transport_forcing hs₁ hs₂ hu.1.le hu.2 hv.2).hasDerivAt
      (Icc_mem_nhds hu.1 hu.2))
    (fun v hv s hs t ht => (hprop T e ε M A S₁ h₁ hA hs₁ hε₂ v hv s hs t ht).trans hamp)
  have hjbound : jDist T S₁ S₂ ≤ ENNReal.ofReal
      (C * δ + C * (ε ^ 2 + sigma e M T) * (J + K) + C * ε * (ε ^ 2 + sigma e M T) * G) := by
    calc
      _ ≤ ENNReal.ofReal (Real.exp 1) *
          ((∫⁻ v in Icc 0 T, ‖g 0 v‖ₑ) +
            ∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, ‖jDifferenceForcing e T S₁ S₂ u v‖ₑ) := htransport
      _ ≤ ENNReal.ofReal (Real.exp 1) * (ENNReal.ofReal (Ci * δ) + ENNReal.ofReal B) :=
        mul_le_mul' le_rfl (add_le_add (hinit T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hi) hforcing)
      _ = ENNReal.ofReal (Real.exp 1 * (Ci * δ + B)) := by
        rw [← ENNReal.ofReal_add (mul_nonneg hCi.le hδ) hB,
          ← ENNReal.ofReal_mul (Real.exp_pos 1).le]
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hnonneg : 0 ≤ (ε ^ 2 + sigma e M T) * (J + K) + ε * (ε ^ 2 + sigma e M T) * G := by
          dsimp [J, K, G]
          positivity
        have h := mul_nonneg (Real.exp_pos 1).le (mul_nonneg hCi.le hnonneg)
        dsimp only [C, B]
        nlinarith only [h]
  have htarget : 0 ≤ C * δ + C * (ε ^ 2 + sigma e M T) * (J + K) +
      C * ε * (ε ^ 2 + sigma e M T) * G := by dsimp [C, J, K, G]; positivity
  have hreal := (ENNReal.toReal_le_toReal (jDist_ne_top_of_settings hs₁ hs₂)
      ENNReal.ofReal_ne_top).mpr hjbound
  rw [ENNReal.toReal_ofReal htarget] at hreal
  exact hreal

end EmcsfAcExtension.Local.Stab
