module

public import EmcsfAcExtension.Local.Stability.KCloseForcingArea
import EmcsfAcExtension.Local.Stability.KClose
import EmcsfAcExtension.Local.Stability.KCloseEnvelope
import EmcsfAcExtension.Local.Stability.JCloseBudget
import EmcsfAcExtension.Local.Stability.JCloseIntegrability
import EmcsfAcExtension.Local.Stability.SourceDifferenceArea
import EmcsfAcExtension.Local.Stability.MainFinite
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Closure of the incoming renormalized derivative comparison

The real coefficient is nonpositive. The regular-axis identity therefore
retains the exact coefficient one on the outgoing derivative distance.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- [internal]
 Conditional helper for the repaired `restart-stab-k-close` contract.
The data remainder is exactly `C σ ε Δ₀/M` as adopted in internal project record.
Constants depend only on fixed `A,D`, uniformly in all physical parameters,
solution pairs and derivative suprema. Only first-half records are inputs. -/
theorem k_close_of_differences (A D : ℝ) (hA : 0 < A) (hD : 0 < D) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
    ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ^ 2 + sigma e M T ≤ η →
      RatioDifferences D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      FieldDifference D T ε (dataDist h₁ h₂ T) S₁ S₂ →
      ChargeDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      OutgoingFluxDifference D T ε S₁ S₂ →
      (kDist e T S₁ S₂).toReal ≤ (jDist T S₁ S₂).toReal +
        C * (ε ^ 2 + sigma e M T) * ((jDist T S₁ S₂).toReal + (kDist e T S₁ S₂).toReal) +
        C * ε * (ε ^ 2 + sigma e M T) * (geomDist T S₁ S₂).toReal +
        C * sigma e M T * ε * dataDist h₁ h₂ T / M := by
  obtain ⟨C, hC, hforce⟩ := k_forcing_area_of_differences A D hA hD
  refine ⟨1 / 4, C, by norm_num, hC, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hsmall hratio hfield hcharge hflux
  have hε : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans
    (hs₂.box.2 (0, 0) ⟨le_rfl, le_rfl, hs₂.pos.le⟩).2.2.2.2.2.1
  have hσ : 0 ≤ sigma e M T := by unfold sigma; positivity
  have hM : 0 ≤ M := zero_le_one.trans hs₂.box.1
  let δ := dataDist h₁ h₂ T
  let J := (jDist T S₁ S₂).toReal
  let K := (kDist e T S₁ S₂).toReal
  let G := (geomDist T S₁ S₂).toReal
  let B := C * (ε ^ 2 + sigma e M T) * (J + K) +
    C * ε * (ε ^ 2 + sigma e M T) * G + C * sigma e M T * ε * δ / M
  have hδ : 0 ≤ δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hB : 0 ≤ B := by dsimp [B, J, K, G]; positivity
  have hforcing := hforce T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hsmall hratio hfield hcharge hflux
  have hqmeas := (measurable_difference_forcings hs₁ hs₂).2
  have hqint := integrableOn_triangle_of_incoming_area_ne_top hqmeas
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hforcing)
  let g := fun u v => kC1 e (triangle 0 T) S₁ u v - kC1 e (triangle 0 T) S₂ u v
  have hg : ContinuousOn (Function.uncurry g) (triangle 0 T) := by
    simpa only [g, Function.uncurry_def, Pi.sub_def] using!
      (continuousOn_kC1_aux hs₁.pos hs₁.c1).sub (continuousOn_kC1_aux hs₂.pos hs₂.c1)
  have hc (u : ℝ) (hu : u ∈ Icc 0 T) :
      IntervalIntegrable (fun v => (kRealCoefficient S₁ u v : ℂ)) volume u T := by
    simpa only [Function.comp_apply, Function.uncurry_def, id_eq] using!
      ((transport_complex_coefficients_continuousOn hs₁).2.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (show MapsTo (fun v => (u, v)) (Icc u T) (triangle 0 T) from
        fun v hv => ⟨hu.1, hv.1, hv.2⟩)).intervalIntegrable_of_Icc (μ := volume) hu.2
  have htransport := inEnv_integral_le_of_transport (B := 0) hs₁.pos.le hg hc
    (ae_intervalIntegrable_triangle_left hqint)
    (fun u hu v hv => (k_difference_transport_forcing hs₁ hs₂ hu.1 hv.1 hv.2.le).hasDerivAt
      (Icc_mem_nhds hv.1 hv.2))
    (fun u hu s hs t ht => k_propagator_budget hs₁ hu hs ht)
  have hswap := outgoing_area_eq_incoming_of_measurable_indicator
    (measurable_triangle_enorm_of_measurable_indicator hqmeas)
  have hboundary := k_axis_difference_le_jDist hs₁ hs₂
  have hkbound : kDist e T S₁ S₂ ≤ jDist T S₁ S₂ + ENNReal.ofReal B := by
    have ht : kDist e T S₁ S₂ ≤
        (∫⁻ u in Icc 0 T, ‖g u u‖ₑ) +
          ∫⁻ u in Icc 0 T, ∫⁻ v in Icc u T, ‖kDifferenceForcing e T S₁ S₂ u v‖ₑ := by
      simpa only [Real.exp_zero, ENNReal.ofReal_one, one_mul, kDist, g, Function.uncurry_def] using
          htransport
    have hswap' : (∫⁻ u in Icc 0 T, ∫⁻ v in Icc u T, ‖kDifferenceForcing e T S₁ S₂ u v‖ₑ) =
        ∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, ‖kDifferenceForcing e T S₁ S₂ u v‖ₑ := by
      simpa only [Function.uncurry_def] using hswap
    rw [hswap'] at ht
    exact ht.trans (add_le_add hboundary hforcing)
  have hjfin := jDist_ne_top_of_settings hs₁ hs₂
  have hkfin := kDist_ne_top_of_settings hs₁ hs₂
  have hreal := (ENNReal.toReal_le_toReal hkfin
    (ENNReal.add_ne_top.mpr ⟨hjfin, ENNReal.ofReal_ne_top⟩)).mpr hkbound
  rw [ENNReal.toReal_add hjfin ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hB] at hreal
  dsimp only [B, J, K, G, δ] at hreal
  linarith only [hreal]

end EmcsfAcExtension.Local.Stab
