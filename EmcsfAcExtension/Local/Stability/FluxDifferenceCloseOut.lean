module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.DifferenceMomentsCloseOut
import EmcsfAcExtension.Local.Stability.FluxDifferenceAbsolute

/-! # Closed outgoing quadratic flux comparison

The closed outgoing radial estimate gives the stronger electromagnetic
free bound recorded in approved internal project record (QF). The varying radial measure
is included through the individual mixed quadratic Hardy budget.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [node restart-sec-bv-stability-independent#outgoing-quadratic-flux-difference]
The absolute outgoing optical flux difference, charged_SF_new_version.tex:L5344 and
approved internal project record (QF), in its stronger form `CεΔj + Cε²G`. Constants
depend only on the fixed box and `A`, before every other parameter,
the solution pair, derivative suprema and minimum radius. -/
theorem Stab.outgoing_quadratic_flux_difference (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ENNReal.ofReal
          |S₁.lam u v / S₁.r u v * ‖S₁.theta u v / (S₁.lam u v : ℂ)‖ ^ 2 -
            S₂.lam u v / S₂.r u v * ‖S₂.theta u v / (S₂.lam u v : ℂ)‖ ^ 2|) ≤
          ENNReal.ofReal (C * ε * (jDist T S₁ S₂).toReal +
            C * ε ^ 2 * (geomDist T S₁ S₂).toReal) := by
  obtain ⟨η, C₀, hη, hC₀, hOut⟩ := stab_out_difference A hA
  refine ⟨min η (1 / 12), 2 * C₀ + 5120 * A,
    lt_min hη (by norm_num), by positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall
  let J := (jDist T S₁ S₂).toReal
  let G := (geomDist T S₁ S₂).toReal
  let H := J + ε * G
  have hJ : 0 ≤ J := ENNReal.toReal_nonneg
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hH : 0 ≤ H := add_nonneg hJ (mul_nonneg hε0 hG)
  have hσ : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hε : ε ^ 2 ≤ 1 / 4 := by
    have hb := ((le_add_of_nonneg_right hσ).trans hsmall).trans (min_le_right _ _)
    linarith only [hb]
  have hclosed := hOut T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hsmall.trans (min_le_left _ _))
  have hHardy := (le_add_of_nonneg_left bot_le).trans hclosed
  apply iSup₂_le
  intro u hu
  rcases hu.2.eq_or_lt with rfl | huT
  · simp
  · have hraw := stab_out_quadratic_flux_lintegral_raw hA h₁s h₂s hε hu.1 huT le_rfl
    have hh : (∫⁻ s in Icc u T, ENNReal.ofReal (S₁.lam u s / S₁.r u s *
        ‖S₁.theta u s / (S₁.lam u s : ℂ) - S₂.theta u s / (S₂.lam u s : ℂ)‖)) ≤
        ENNReal.ofReal (C₀ * H) := (le_iSup₂_of_le u hu le_rfl).trans hHardy
    apply (hraw.trans (add_le_add (mul_le_mul' le_rfl hh) le_rfl)).trans
    rw [← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hε0),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hscale := mul_le_mul_of_nonneg_left
      (show ε * G ≤ H from le_add_of_nonneg_left hJ) (show 0 ≤ 5120 * A * ε by positivity)
    dsimp only [H, J, G] at hscale ⊢
    nlinarith only [hscale]

end EmcsfAcExtension.Local
