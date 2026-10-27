module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeometryDifferenceInitialGauge
import EmcsfAcExtension.Local.Stability.GeometryDifferenceInitialMassFeedback
import EmcsfAcExtension.Local.Stability.GeometryDifferenceInitialAbsorption
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassSign
import EmcsfAcExtension.Local.Stability.GeometryDifferenceOpticalComparison
import EmcsfAcExtension.Local.Stability.DifferenceMomentsInitial

/-! # Initial optical comparison with unequal initial masses

The initial mass supremum is introduced only on `u=0`. The common
radius and expansion gauges remove all geometric errors, and the
radial mass feedback is absorbed on that same cone.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [node restart-sec-bv-stability-independent#initial-optical-factor-difference]
The initial `λ/(1-μ)` difference, charged_SF_new_version.tex:L5203–5344 and
approved internal project record. The threshold depends only on `A` and the fixed box;
the displayed constant is universal. Both are chosen before all other
parameters and the pair, uniformly at both initial-cone endpoints. -/
theorem Stab.initial_optical_factor_difference (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        (⨆ v ∈ Icc 0 T, ENNReal.ofReal
          |S₁.lam 0 v / (1 - S₁.mu 0 v) - S₂.lam 0 v / (1 - S₂.mu 0 v)|) ≤
          ENNReal.ofReal (C * ε * (jDist T S₁ S₂).toReal +
            C * sigma e M T * ε ^ 2 * dataDist h₁ h₂ T) := by
  refine ⟨min (1 / 12) (1 / (2688 * A)), 12032,
    lt_min (by norm_num) (by positivity), by norm_num, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall
  let Ue := ⨆ v ∈ Icc 0 T, ENNReal.ofReal |S₁.mu 0 v - S₂.mu 0 v|
  let U := Ue.toReal
  let J := (jDist T S₁ S₂).toReal
  let Δ := dataDist h₁ h₂ T
  let X := 8 * J + 32 * A * ε * U
  have hU : 0 ≤ U := ENNReal.toReal_nonneg
  have hJ : 0 ≤ J := ENNReal.toReal_nonneg
  have hΔ : 0 ≤ Δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hσ0 : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hsize : ε ^ 2 + sigma e M T ≤ 1 / 12 := hsmall.trans (min_le_left _ _)
  have hεsq : 3 * ε ^ 2 ≤ 1 / 2 := by linarith only [hsize, hσ0]
  have hσ : sigma e M T ≤ 1 := by linarith only [hsize, sq_nonneg ε]
  have hsmallA : 2688 * A * ε ^ 2 ≤ 1 := by
    have hh := ((le_add_of_nonneg_right hσ0).trans hsmall).trans (min_le_right _ _)
    have hp : 0 < 2688 * A := by positivity
    have hs := (le_div_iff₀ hp).mp hh
    nlinarith only [hs]
  have hUe : Ue ≤ ENNReal.ofReal 1 := by
    apply iSup₂_le
    intro v hv
    have hμ₁ := stab_mu_nonneg h₁s le_rfl hv.1 hv.2
    have hμ₂ := stab_mu_nonneg h₂s le_rfl hv.1 hv.2
    have hg₁ := (h₁s.box.2 (0, v) ⟨le_rfl, hv.1, hv.2⟩).2.2.2.2.1
    have hg₂ := (h₂s.box.2 (0, v) ⟨le_rfl, hv.1, hv.2⟩).2.2.2.2.1
    apply ENNReal.ofReal_le_ofReal
    rw [abs_le]
    constructor <;> linarith only [hμ₁, hμ₂, hg₁, hg₂]
  have hUfinite : Ue ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hUe
  have hmass : ∀ v ∈ Icc 0 T, |S₁.mu 0 v - S₂.mu 0 v| ≤ U := by
    intro v hv
    have hh : ENNReal.ofReal |S₁.mu 0 v - S₂.mu 0 v| ≤ Ue :=
      le_iSup₂_of_le v hv le_rfl
    simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using!
      ENNReal.toReal_mono hUfinite hh
  have hratio := stab_initial_ratio_le_of_mass_bound hA h₁s h₂s hεsq hU hmass
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hx : ∀ v ∈ Icc 0 T,
      ‖S₁.theta 0 v / (S₁.lam 0 v : ℂ) - S₂.theta 0 v / (S₂.lam 0 v : ℂ)‖ ≤ X := by
    intro v hv
    have hxB : ENNReal.ofReal
        ‖S₁.theta 0 v / (S₁.lam 0 v : ℂ) - S₂.theta 0 v / (S₂.lam 0 v : ℂ)‖ ≤
          ENNReal.ofReal X := hratio.1 v hv
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hxB
    simpa only [ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_ofReal hX] using! hh
  have hfeedback := stab_initial_mass_le_of_ratio_bounds h₁s h₂s hX hx hratio.2
  have hB : 0 ≤ 2 * ε * X + 40 * sigma e M T * ε * (X + ε * Δ) := by positivity
  have hUfeedback : U ≤ 2 * ε * X + 40 * sigma e M T * ε * (X + ε * Δ) := by
    have hh : Ue ≤ ENNReal.ofReal (2 * ε * X + 40 * sigma e M T * ε * (X + ε * Δ)) := by
      apply iSup₂_le
      intro v hv
      exact ENNReal.ofReal_le_ofReal (hfeedback v hv)
    simpa only [ENNReal.toReal_ofReal hB] using! ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  have hsharp : U ≤ 672 * ε * J + 80 * sigma e M T * ε ^ 2 * Δ :=
    stab_initial_mass_absorb hA.le hε hσ hJ hU hsmallA hUfeedback
  apply iSup₂_le
  intro v hv
  have hp : (0, v) ∈ triangle (0 : ℝ) T := ⟨le_rfl, hv.1, hv.2⟩
  have ho := stab_optical_quotient_sub_le
    (n₁ := (1 / 2 : ℝ)) (n₂ := (1 / 2 : ℝ))
    (h₁s.box.2 (0, v) hp).2.2.2.2.1 (h₂s.box.2 (0, v) hp).2.2.2.2.1
    (by norm_num : |(1 / 2 : ℝ)| ≤ 1)
  have hgap : |(1 - S₁.mu 0 v) - (1 - S₂.mu 0 v)| = |S₁.mu 0 v - S₂.mu 0 v| := by
    rw [show (1 - S₁.mu 0 v) - (1 - S₂.mu 0 v) = -(S₁.mu 0 v - S₂.mu 0 v) by ring,
      abs_neg]
  rw [sub_self, abs_zero, mul_zero, zero_add, hgap] at ho
  rw [stab_initial_lam h₁s hv, stab_initial_lam h₂s hv]
  apply ENNReal.ofReal_le_ofReal
  have hm := hmass v hv
  have hj := mul_nonneg hε hJ
  have hd := mul_nonneg (mul_nonneg hσ0 (sq_nonneg ε)) hΔ
  dsimp only [J, Δ] at hsharp hj hd ⊢
  nlinarith only [ho, hm, hsharp, hj, hd]

end EmcsfAcExtension.Local
