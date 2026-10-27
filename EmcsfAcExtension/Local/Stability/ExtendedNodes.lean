module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.MainLipschitz
import EmcsfAcExtension.Local.Stability.W11Comparison
import EmcsfAcExtension.Local.Stability.W11Ordinary
import EmcsfAcExtension.Local.Stability.GeomStrongEnvelopeMain

/-! # Unconditional characteristic and geometric comparison nodes

The main stability theorem discharges each local comparison helper's
explicit internal project record input, without changing its quantitative conclusion.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [node restart-sec-bv-stability-independent#characteristic-variation-difference]
The complete smooth comparison node. Threshold and positive constant
depend only on `A` and the fixed box, before all fields, data, coupling,
time and background, uniformly in derivative suprema and minimum radii.
-/
theorem Stab.characteristic_variation_difference
    (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T,
          ‖pdV (triangle 0 T) S₁.a u v - pdV (triangle 0 T) S₂.a u v‖ₑ) +
        (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
          ‖(pdU (triangle 0 T) S₁.b u v + Complex.I * e * S₁.A u v * S₁.b u v) -
            (pdU (triangle 0 T) S₂.b u v + Complex.I * e * S₂.A u v * S₂.b u v)‖ₑ) ≤
          ENNReal.ofReal (C * dataDist h₁ h₂ T) := by
  obtain ⟨ηm, C₀, hηm, hC₀, hMain⟩ := stab_main_lipschitz A hA
  obtain ⟨η, C, hη, hC, hPair⟩ := Stab.characteristic_variation_difference_of_main_lipschitz A C₀ hA
      hC₀
  refine ⟨min ηm η, C, lt_min hηm hη, hC, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall
  have hm := hMain T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hsmall.trans (min_le_left _ _))
  apply hPair T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hsmall.trans (min_le_right _ _))
  exact (le_add_of_nonneg_right bot_le).trans ((le_add_of_nonneg_right bot_le).trans
      ((le_add_of_nonneg_right bot_le).trans hm))

/-- [node restart-sec-bv-stability-independent#ordinary-incoming-difference-variation]
The complete smooth comparison node. Threshold and positive constant
depend only on `A` and the fixed box, before all fields, data, coupling,
time and background, uniformly in derivative suprema and minimum radii.
-/
theorem Stab.ordinary_incoming_difference_variation
    (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
          ‖pdU (triangle 0 T) S₁.b u v - pdU (triangle 0 T) S₂.b u v‖ₑ) ≤
          ENNReal.ofReal (C * dataDist h₁ h₂ T) := by
  obtain ⟨ηm, C₀, hηm, hC₀, hMain⟩ := stab_main_lipschitz A hA
  obtain ⟨η, C, hη, hC, hPair⟩ := Stab.ordinary_incoming_difference_variation_of_main_lipschitz A C₀
      hA hC₀
  refine ⟨min ηm η, C, lt_min hηm hη, hC, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall
  have hm := hMain T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hsmall.trans (min_le_left _ _))
  apply (le_add_of_nonneg_left bot_le).trans
  apply hPair T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hsmall.trans (min_le_right _ _))
  exact hm

/-- [node restart-sec-bv-stability-independent#geometric-renormalized-envelope-difference]
The complete smooth comparison node. Threshold and positive constant
depend only on `A` and the fixed box, before all fields, data, coupling,
time and background, uniformly in derivative suprema and minimum radii.
-/
theorem Stab.geometric_renormalized_envelope_difference
    (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        (∫⁻ v in Icc 0 T, outEnv 0 (fun u v =>
          geomL (triangle 0 T) S₁ u v - geomL (triangle 0 T) S₂ u v) v) +
        (∫⁻ u in Icc 0 T, inEnv T (fun u v =>
          geomN (triangle 0 T) S₁ u v - geomN (triangle 0 T) S₂ u v) u) ≤
          ENNReal.ofReal (C * (ε + sigma e M T) * dataDist h₁ h₂ T) := by
  obtain ⟨ηm, C₀, hηm, hC₀, hMain⟩ := stab_main_lipschitz A hA
  obtain ⟨η, C, hη, hC, hPair⟩ := stab_geometric_envelope_difference_of_main_lipschitz A C₀ hA hC₀
  refine ⟨min ηm η, C, lt_min hηm hη, hC, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall
  have hm := hMain T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hsmall.trans (min_le_left _ _))
  apply hPair T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hsmall.trans (min_le_right _ _))
  exact (le_add_of_nonneg_right bot_le).trans ((le_add_of_nonneg_right bot_le).trans
      ((le_add_of_nonneg_right bot_le).trans hm))

end EmcsfAcExtension.Local
