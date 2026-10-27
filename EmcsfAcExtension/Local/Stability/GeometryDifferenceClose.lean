module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMass
import EmcsfAcExtension.Local.Stability.GeometryDifferenceInitialOptical
import EmcsfAcExtension.Local.Stability.GeometryDifferenceGlobal
import EmcsfAcExtension.Local.Stability.GeometryDifferenceExponentBudget
import EmcsfAcExtension.Local.Stability.GeometryDifferenceCloseAlgebra
import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux
import EmcsfAcExtension.Local.Stability.FluxDifferenceCloseOut
import EmcsfAcExtension.Local.Stability.FluxDifferenceCloseIn

/-! # Geometry difference before comparison closure

The normalized mass and quadratic flux estimates are inserted into
the two ordered optical integrations. The initial optical comparison
is proved on the initial cone itself, so no free axis term remains.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [node restart-stab-geometry-difference]
The geometric difference before absorption, charged_SF_new_version.tex:L5343–5343
and approved internal project record. The threshold and constant depend only on `A`
and the literal fixed box, before all other parameters and the pair,
uniformly at the axis and independently of data derivative suprema. -/
theorem stab_geometry_difference (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        (geomDist T S₁ S₂).toReal ≤
          C * ε * ((jDist T S₁ S₂).toReal + (kDist e T S₁ S₂).toReal) +
          C * sigma e M T * dataDist h₁ h₂ T +
          C * (ε ^ 2 + sigma e M T) * (geomDist T S₁ S₂).toReal := by
  obtain ⟨ηm, Cm, hηm, hCm, hMass⟩ := Stab.mass_volterra_difference A hA
  obtain ⟨η₀, C₀, hη₀, hC₀, hInitial⟩ := Stab.initial_optical_factor_difference A hA
  obtain ⟨ηo, Co, hηo, hCo, hOut⟩ := Stab.outgoing_quadratic_flux_difference A hA
  obtain ⟨ηi, Ci, hηi, hCi, hIn⟩ := Stab.incoming_quadratic_flux_difference A hA
  let C := 100 * (2 * Cm + C₀ + Co + 2 * Ci + 1)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨min ηm (min η₀ (min ηo (min ηi (1 / 12)))), C,
    lt_min hηm (lt_min hη₀ (lt_min hηo (lt_min hηi (by norm_num)))), hC, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall
  let J := (jDist T S₁ S₂).toReal
  let K := (kDist e T S₁ S₂).toReal
  let G := (geomDist T S₁ S₂).toReal
  let Δ := dataDist h₁ h₂ T
  let H := J + ε * Δ + ε * G
  let U := Cm * ε * J + Cm * ε ^ 2 * G + Cm * sigma e M T * ε * H
  let I := C₀ * ε * J + C₀ * sigma e M T * ε ^ 2 * Δ
  let Fo := Co * ε * J + Co * ε ^ 2 * G
  let Fi := Ci * ε * K + Ci * ε ^ 2 * G + Ci * sigma e M T * ε * H
  have hJ : 0 ≤ J := ENNReal.toReal_nonneg
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hΔ : 0 ≤ Δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hσ0 : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hI : 0 ≤ I := by dsimp only [I]; positivity
  have hFo : 0 ≤ Fo := by dsimp only [Fo]; positivity
  have hFi : 0 ≤ Fi := by dsimp only [Fi]; positivity
  have hm := hMass T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hsmall.trans (min_le_left _ _))
  have hs₁ := hsmall.trans (min_le_right _ _)
  have h₀ := hInitial T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hs₁.trans (min_le_left _ _))
  have hs₂ := hs₁.trans (min_le_right _ _)
  have ho := hOut T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hs₂.trans (min_le_left _ _))
  have hs₃ := hs₂.trans (min_le_right _ _)
  have hi := hIn T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hs₃.trans (min_le_left _ _))
  have hsize := hs₃.trans (min_le_right _ _)
  have hσ1 : sigma e M T ≤ 1 := by linarith only [hsize, sq_nonneg ε]
  have hεsq : ε ^ 2 ≤ 1 := by linarith only [hsize, hσ0]
  have hUSup : supDist T S₁.mu S₂.mu ≤ ENNReal.ofReal U :=
    (le_add_of_nonneg_right bot_le).trans hm
  have hUreal : (supDist T S₁.mu S₂.mu).toReal ≤ U := by
    simpa only [ENNReal.toReal_ofReal hU] using!
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hUSup
  have hMassPt : ∀ u v, 0 ≤ u → u ≤ v → v ≤ T → |S₁.mu u v - S₂.mu u v| ≤ U := by
    intro u v hu huv hvT
    exact (stab_mu_sub_le h₁s h₂s ⟨hu, huv, hvT⟩).trans hUreal
  have hInitialPt : ∀ v ∈ Icc 0 T,
      |S₁.lam 0 v / (1 - S₁.mu 0 v) - S₂.lam 0 v / (1 - S₂.mu 0 v)| ≤ I := by
    intro v hv
    have hPt : ENNReal.ofReal
        |S₁.lam 0 v / (1 - S₁.mu 0 v) - S₂.lam 0 v / (1 - S₂.mu 0 v)| ≤
          ENNReal.ofReal I := (le_iSup₂_of_le v hv le_rfl).trans h₀
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hPt
    simpa only [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal hI] using! hh
  have hGeom := stab_geometry_le_of_optical_bounds h₁s h₂s hU hI hFo hFi hMassPt hInitialPt
    (stab_out_exponent_le_of_flux_bound h₁s h₂s hFo ho)
    (stab_in_exponent_le_of_flux_bound h₁s h₂s hFi hi)
  apply hGeom.trans
  exact stab_geometry_budgets_le hCm.le hCi.le hCo.le hC₀.le hε hσ0 hσ1 hεsq hJ hK hG hΔ

end EmcsfAcExtension.Local
