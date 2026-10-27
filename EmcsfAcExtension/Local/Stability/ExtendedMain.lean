module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Defs.Bounds
import EmcsfAcExtension.Local.Stability.W11
import EmcsfAcExtension.Local.Stability.ExtendedExtras
import EmcsfAcExtension.Local.Stability.ExtendedHardy
import EmcsfAcExtension.Local.Stability.ExtendedMass
import EmcsfAcExtension.Local.Stability.GeomStrongPure
import EmcsfAcExtension.Local.Stability.GeomStrongEnvelopeMain

/-! # The complete extended pair conclusion from main stability

Every field of the internal project record `StabBounds` record is supplied. The only
pending internal project record input is the main Lipschitz inequality; no extended
conclusion bundle or strong-limit assertion is assumed.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The full extended stability record follows from the main Lipschitz
conclusion. The threshold and constant depend only on `A` and its
uniform main constant `C₀`, before all fields, data, coupling, scale and
background parameters, uniformly in minimum radii and higher initial
derivatives. All four internal project record extra clauses are included. -/
theorem stab_extended_of_main_lipschitz
    (A C₀ : ℝ) (hA : 0 < A) (hC₀ : 0 < C₀) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        jDist T S₁ S₂ + kDist e T S₁ S₂ + geomDist T S₁ S₂ +
          supDist T S₁.a S₂.a + supDist T S₁.b S₂.b + supDist T S₁.phi S₂.phi ≤
            ENNReal.ofReal (C₀ * dataDist h₁ h₂ T) →
        StabBounds C e T M (dataDist h₁ h₂ T) S₁ S₂ := by
  obtain ⟨ηx, Cx, hηx, hCx, hExtra⟩ := stab_extra_fields_of_main_lipschitz A C₀ hA hC₀
  obtain ⟨ηt, Ct, hηt, hCt, hVariation⟩ :=
    Stab.scalar_characteristic_strong_W11_of_main_lipschitz_c1 A C₀ hA hC₀
  obtain ⟨ηg, Cg, hηg, hCg, hPure⟩ := stab_pure_geometric_derivatives_of_main_lipschitz_c1 A C₀ hA
      hC₀
  obtain ⟨ηh, Ch, hηh, hCh, hHardy⟩ := stab_hardy_difference_of_main_lipschitz A C₀ hA hC₀
  obtain ⟨ηm, Cm, hηm, hCm, hMass⟩ := stab_mu_flux_difference_of_main_lipschitz A C₀ hA hC₀
  obtain ⟨ηe, Ce, hηe, hCe, hEnvelope⟩ :=
    stab_geometric_envelope_difference_of_main_lipschitz A C₀ hA hC₀
  obtain ⟨ηa, Ca, hηa, hCa, hArea⟩ := stab_xi_ratio_area_of_main_lipschitz A C₀ hA hC₀
  let C := C₀ + Cx + Ct + Cg + Ch + Cm + 2 * Ce + Ca
  have hC₀C : C₀ ≤ C := by dsimp only [C]; linarith only [hCx, hCt, hCg, hCh, hCm, hCe, hCa]
  have hCxC : Cx ≤ C := by dsimp only [C]; linarith only [hC₀, hCt, hCg, hCh, hCm, hCe, hCa]
  have hCtC : Ct ≤ C := by dsimp only [C]; linarith only [hC₀, hCx, hCg, hCh, hCm, hCe, hCa]
  have hCgC : Cg ≤ C := by dsimp only [C]; linarith only [hC₀, hCx, hCt, hCh, hCm, hCe, hCa]
  have hChC : Ch ≤ C := by dsimp only [C]; linarith only [hC₀, hCx, hCt, hCg, hCm, hCe, hCa]
  have hCmC : Cm ≤ C := by dsimp only [C]; linarith only [hC₀, hCx, hCt, hCg, hCh, hCe, hCa]
  have hCeC : 2 * Ce ≤ C := by dsimp only [C]; linarith only [hC₀, hCx, hCt, hCg, hCh, hCm, hCa]
  have hCaC : Ca ≤ C := by dsimp only [C]; linarith only [hC₀, hCx, hCt, hCg, hCh, hCm, hCe]
  refine ⟨min ηx (min ηt (min ηg (min ηh (min ηm (min ηe (min ηa (1 / 4))))))), C,
    lt_min hηx (lt_min hηt (lt_min hηg (lt_min hηh (lt_min hηm
      (lt_min hηe (lt_min hηa (by norm_num))))))), by dsimp only [C]; positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall hmain
  let Δ := dataDist h₁ h₂ T
  have hΔ : 0 ≤ Δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hT : 0 ≤ T := h₁s.pos.le
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans h₁s.box.1
  have hs1 := hsmall.trans (min_le_right _ _)
  have hs2 := hs1.trans (min_le_right _ _)
  have hs3 := hs2.trans (min_le_right _ _)
  have hs4 := hs3.trans (min_le_right _ _)
  have hs5 := hs4.trans (min_le_right _ _)
  have hs6 := hs5.trans (min_le_right _ _)
  have hsize := hs6.trans (min_le_right _ _)
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hσ0 : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hε1 : ε ≤ 1 := by nlinarith only [hsize, hσ0, sq_nonneg (ε - 1)]
  have hσ : sigma e M T ≤ 1 := by linarith only [hsize, sq_nonneg ε]
  have hmain3 : jDist T S₁ S₂ + kDist e T S₁ S₂ + geomDist T S₁ S₂ ≤
      ENNReal.ofReal (C₀ * Δ) :=
    (le_add_of_nonneg_right bot_le).trans ((le_add_of_nonneg_right bot_le).trans
      ((le_add_of_nonneg_right bot_le).trans hmain))
  have lift_bound {X : ℝ≥0∞} {c : ℝ} (hc : c ≤ C)
      (hX : X ≤ ENNReal.ofReal (c * Δ)) : X ≤ ENNReal.ofReal (C * Δ) :=
    hX.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hc hΔ))
  obtain ⟨hμ, hQ, hAfield⟩ := hExtra T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
    (hsmall.trans (min_le_left _ _)) hmain3
  refine {
    main := lift_bound hC₀C hmain
    extra_mu := lift_bound hCxC hμ
    extra_Q := ?_
    extra_A := ?_
    tv := lift_bound hCtC (hVariation T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
      (hs1.trans (min_le_left _ _)) hmain)
    geomStrong := lift_bound hCgC (hPure T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
      (hs2.trans (min_le_left _ _)) hmain3)
    hardyDiff := lift_bound hChC (hHardy T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
      (hs3.trans (min_le_left _ _)) hmain3)
    muFluxDiff := lift_bound hCmC (hMass T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
      (hs4.trans (min_le_left _ _)) hmain3)
    geomEnvDiff := ?_
    xiRatioArea := ?_ }
  · intro p hp hlt
    exact (hQ p hp hlt).trans (by gcongr)
  · apply hAfield.trans
    apply ENNReal.ofReal_le_ofReal
    gcongr
  · apply lift_bound hCeC
    apply (hEnvelope T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
      (hs5.trans (min_le_left _ _)) hmain3).trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ Ce * (1 + 1) * Δ := by gcongr
      _ = _ := by ring
  · apply (hArea T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
      (hs6.trans (min_le_left _ _)) hmain3).trans
    apply ENNReal.ofReal_le_ofReal
    gcongr

end EmcsfAcExtension.Local
