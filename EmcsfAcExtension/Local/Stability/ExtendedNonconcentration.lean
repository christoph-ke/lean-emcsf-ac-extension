module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.MainLipschitz
import EmcsfAcExtension.Local.Stability.W11Nonconcentration

/-! # Uniform quadratic-flux nonconcentration from normalized data

The main stability theorem makes the two envelope families strongly
Cauchy. Localized Hardy bounds then give a width uniform over every
approximation and every null section in both directions.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [internal]
The positive smallness threshold depends only on `A` and the fixed box,
before all fields, data, coupling, time and background parameters.
For each positive error tolerance the same positive width controls
the entire approximation sequence and both orientations. There is no
bound on higher initial derivatives and no minimum-radius dependence.
-/
theorem Stab.quadratic_flux_nonconcentration (A : ℝ) (hA : 0 < A) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (T e ε M : ℝ) (Sn : ℕ → Fields) (hn : ℕ → ℝ → ℂ),
        (∀ n, StabSetting e T ε M A (Sn n) (hn n)) →
        ε ^ 2 + sigma e M T ≤ η →
        (∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, dataDist (hn n) (hn m) T < δ) →
        ∀ δ > (0 : ℝ), ∃ d : ℝ, 0 < d ∧
          ∀ n u v, 0 ≤ u → u ≤ v → v ≤ T → v - u ≤ d →
            (∫⁻ s in Icc u v, ENNReal.ofReal
              ((Sn n).lam u s / (Sn n).r u s *
                ‖(Sn n).theta u s / ((Sn n).lam u s : ℂ)‖ ^ 2)) +
            (∫⁻ s in Icc u v, ENNReal.ofReal
              (-(Sn n).nu s v / (Sn n).r s v *
                ‖(Sn n).xi s v / ((Sn n).nu s v : ℂ)‖ ^ 2)) ≤ ENNReal.ofReal δ := by
  obtain ⟨ηm, C₀, hηm, hC₀, hMain⟩ := stab_main_lipschitz A hA
  refine ⟨min ηm (1 / 4), lt_min hηm (by norm_num), ?_⟩
  intro T e ε M Sn hn hset hsmall hdata
  have hσ0 : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hεsq : ε ^ 2 ≤ 1 / 4 := by
    linarith only [hsmall.trans (min_le_right _ _), hσ0]
  apply Stab.quadratic_flux_nonconcentration_of_main_lipschitz C₀ hC₀ hset hεsq hdata
  intro n m
  have hm := hMain T e ε M (Sn n) (Sn m) (hn n) (hn m)
    (hset n) (hset m) (hsmall.trans (min_le_left _ _))
  exact (le_add_of_nonneg_right bot_le).trans ((le_add_of_nonneg_right bot_le).trans
    ((le_add_of_nonneg_right bot_le).trans hm))

end EmcsfAcExtension.Local
