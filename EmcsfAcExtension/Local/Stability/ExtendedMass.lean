module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMass
import EmcsfAcExtension.Local.Stability.GeomStrongMassIn

/-! # The two weighted mass clauses of extended stability

The outgoing Volterra comparison and the independently oriented incoming
comparison supply the two singular mass norms required by internal project record.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace EmcsfAcExtension.Local

/-- Weighted mass-ratio pair comparison conditional on the first
three main Lipschitz clauses. Constants depend only on `A` and its
uniform main constant `C₀`, before all field parameters, data, pairs,
derivative suprema and minimum radii. -/
theorem stab_mu_flux_difference_of_main_lipschitz
    (A C₀ : ℝ) (hA : 0 < A) (hC₀ : 0 < C₀) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        jDist T S₁ S₂ + kDist e T S₁ S₂ + geomDist T S₁ S₂ ≤
          ENNReal.ofReal (C₀ * dataDist h₁ h₂ T) →
        (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ENNReal.ofReal
          (S₁.lam u v / S₁.r u v * |S₁.mu u v - S₂.mu u v|)) +
        (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v, ENNReal.ofReal
          (-S₁.nu u v / S₁.r u v * |S₁.mu u v - S₂.mu u v|)) ≤
          ENNReal.ofReal (C * dataDist h₁ h₂ T) := by
  obtain ⟨ηo, Co, hηo, hCo, hOut⟩ := Stab.mass_volterra_difference A hA
  obtain ⟨ηi, Ci, hηi, hCi, hIn⟩ := stab_in_weighted_mass_difference A hA
  let C := (Co + Ci) * (4 * C₀ + 1)
  refine ⟨min ηo (min ηi (1 / 4)), C, lt_min hηo (lt_min hηi (by norm_num)),
    by dsimp only [C]; positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall hmain
  let Δ := dataDist h₁ h₂ T
  let B := C₀ * Δ
  have hΔ : 0 ≤ Δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hB : 0 ≤ B := mul_nonneg hC₀.le hΔ
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hσ : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hs : ε ^ 2 + sigma e M T ≤ 1 / 4 :=
    hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hε1 : ε ≤ 1 := by nlinarith only [hs, hσ, sq_nonneg (ε - 1)]
  have hεsq : ε ^ 2 ≤ 1 := by linarith only [hs, hσ]
  have hσ1 : sigma e M T ≤ 1 := by linarith only [hs, sq_nonneg ε]
  have hb {X : ℝ≥0∞} (hX : X ≤ ENNReal.ofReal B) : X.toReal ≤ B := by
    simpa only [ENNReal.toReal_ofReal hB] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hX
  have hJ : (jDist T S₁ S₂).toReal ≤ B := hb
    ((le_add_of_nonneg_right bot_le).trans ((le_add_of_nonneg_right bot_le).trans hmain))
  have hK : (kDist e T S₁ S₂).toReal ≤ B := hb
    ((le_add_of_nonneg_left bot_le).trans ((le_add_of_nonneg_right bot_le).trans hmain))
  have hG : (geomDist T S₁ S₂).toReal ≤ B := hb ((le_add_of_nonneg_left bot_le).trans hmain)
  have ho := (le_add_of_nonneg_left bot_le).trans
    (hOut T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hsmall.trans (min_le_left _ _)))
  have hi := hIn T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
    (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
  apply (add_le_add ho hi).trans
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (Co * 1 * B + Co * 1 * B + Co * 1 * 1 * (B + 1 * Δ + 1 * B)) +
        (Ci * 1 * B + Ci * 1 * B + Ci * 1 * 1 * (B + 1 * Δ + 1 * B)) := by gcongr
    _ = _ := by dsimp only [B, C]; ring

end EmcsfAcExtension.Local
