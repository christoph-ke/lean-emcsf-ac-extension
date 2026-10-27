module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.DifferenceMomentsEstimates
import EmcsfAcExtension.Local.Stability.DifferenceMomentsAbsorption
import EmcsfAcExtension.Local.Stability.GeometryDifferenceFeedback

/-! # Closed outgoing radial difference estimate

The optical identity controls mass feedback without using the later
charge or potential comparison nodes. All constants are fixed after
the envelope constant and before the pair, as in internal project record.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem budget_ofReal_aux {X : ℝ≥0∞} {c G U A ε : ℝ}
    (hX : X ≠ ⊤) (hc : 0 ≤ c) (hG : 0 ≤ G) (hU : 0 ≤ U)
    (hA : 0 ≤ A) (hε : 0 ≤ ε) :
    ENNReal.ofReal c * (X + ENNReal.ofReal (G + U) * ENNReal.ofReal (A * ε)) =
      ENNReal.ofReal (c * (X.toReal + (G + U) * (A * ε))) := by
  rw [ENNReal.ofReal_mul hc,
    ENNReal.ofReal_add ENNReal.toReal_nonneg (mul_nonneg (add_nonneg hG hU)
      (mul_nonneg hA hε)), ENNReal.ofReal_mul (add_nonneg hG hU), ENNReal.ofReal_toReal hX]

/-- [node restart-stab-out-difference]
The closed outgoing radial supremum and weighted difference estimate,
charged_SF_new_version.tex:L5116–5246 and approved internal project record (R0). The threshold and
constant depend only on `A` and the literal fixed box, before all solution
parameters, the pair and data. No charge or potential estimate is assumed. -/
theorem stab_out_difference (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        supDist T (fun u v => S₁.theta u v / (S₁.lam u v : ℂ))
          (fun u v => S₂.theta u v / (S₂.lam u v : ℂ)) +
        (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ENNReal.ofReal (S₁.lam u v / S₁.r u v *
          ‖S₁.theta u v / (S₁.lam u v : ℂ) - S₂.theta u v / (S₂.lam u v : ℂ)‖)) ≤
          ENNReal.ofReal (C * ((jDist T S₁ S₂).toReal + ε * (geomDist T S₁ S₂).toReal)) := by
  let B := 2 + A * (41 + 303104 * A)
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨min (1 / 12) (1 / (524288 * A)), 24576 * B, ?_, by positivity, ?_⟩
  · exact lt_min (by norm_num) (one_div_pos.mpr (by positivity))
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall
  let G := (geomDist T S₁ S₂).toReal
  let U := (supDist T S₁.mu S₂.mu).toReal
  let J := (jDist T S₁ S₂).toReal
  let R := J + (G + U) * (A * ε)
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hU : 0 ≤ U := ENNReal.toReal_nonneg
  have hJ : 0 ≤ J := ENNReal.toReal_nonneg
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hsig : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hεsq : ε ^ 2 ≤ min (1 / 12) (1 / (524288 * A)) :=
    (le_add_of_nonneg_right hsig).trans hsmall
  have hε12 : ε ^ 2 ≤ 1 / 12 := hεsq.trans (min_le_left _ _)
  have hεrad : 3 * ε ^ 2 ≤ 1 / 2 := by linarith only [hε12]
  have hε1 : ε ^ 2 ≤ 1 := by linarith only [hε12]
  have hcoeff : 524288 * A * ε ^ 2 ≤ 1 := by
    have hc := (le_div_iff₀ (show 0 < 524288 * A by positivity)).mp
      (hεsq.trans (min_le_right _ _))
    nlinarith only [hc]
  have hrawU := stab_out_mass_feedback_before_absorption hA h₁s h₂s hεrad
  have hR : R ≤ B * (J + ε * G) :=
    stab_out_budget_le_of_feedback hA hε0 hG hU hJ hε1 hcoeff hrawU
  have hL : 0 ≤ J + ε * G := add_nonneg hJ (mul_nonneg hε0 hG)
  have hJne := stab_jDist_ne_top h₁s h₂s
  have h8192 : 8192 * (jDist T S₁ S₂ +
      ENNReal.ofReal (G + U) * ENNReal.ofReal (A * ε)) = ENNReal.ofReal (8192 * R) := by
    simpa only [ENNReal.ofReal_ofNat] using
      budget_ofReal_aux hJne (by norm_num : (0 : ℝ) ≤ 8192) hG hU hA.le hε0
  have h16384 : 16384 * (jDist T S₁ S₂ +
      ENNReal.ofReal (G + U) * ENNReal.ofReal (A * ε)) = ENNReal.ofReal (16384 * R) := by
    simpa only [ENNReal.ofReal_ofNat] using
      budget_ofReal_aux hJne (by norm_num : (0 : ℝ) ≤ 16384) hG hU hA.le hε0
  have hpoint : ∀ u v : ℝ, (u, v) ∈ triangle 0 T →
      ENNReal.ofReal ‖S₁.theta u v / (S₁.lam u v : ℂ) -
        S₂.theta u v / (S₂.lam u v : ℂ)‖ ≤ ENNReal.ofReal (8192 * B * (J + ε * G)) := by
    intro u v hp
    rcases eq_or_lt_of_le hp.2.1 with heq | huv
    · change u = v at heq
      subst v
      rw [stab_out_ratio_axis h₁s ⟨hp.1, hp.2.2⟩,
        stab_out_ratio_axis h₂s ⟨hp.1, hp.2.2⟩, sub_self, norm_zero, ENNReal.ofReal_zero]
      exact bot_le
    · have hpraw := stab_out_difference_point_before_absorption h₁s h₂s hεrad hp.1 huv hp.2.2
      apply (hpraw.trans_eq h8192).trans
      apply ENNReal.ofReal_le_ofReal
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hR
        (by norm_num : (0 : ℝ) ≤ 8192)
  have hSup : supDist T (fun u v => S₁.theta u v / (S₁.lam u v : ℂ))
      (fun u v => S₂.theta u v / (S₂.lam u v : ℂ)) ≤
      ENNReal.ofReal (8192 * B * (J + ε * G)) := by
    apply iSup₂_le
    rintro ⟨u, v⟩ hp
    rw [← ofReal_norm]
    exact hpoint u v hp
  have hHardy : (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ENNReal.ofReal
      (S₁.lam u v / S₁.r u v *
        ‖S₁.theta u v / (S₁.lam u v : ℂ) - S₂.theta u v / (S₂.lam u v : ℂ)‖)) ≤
      ENNReal.ofReal (16384 * B * (J + ε * G)) := by
    apply iSup₂_le
    intro u hu
    have hh := stab_out_difference_hardy_before_absorption h₁s h₂s hεrad hu.1 hu.2
    rw [restrict_Ioc_eq_restrict_Icc] at hh
    apply (hh.trans_eq h16384).trans
    apply ENNReal.ofReal_le_ofReal
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hR
      (by norm_num : (0 : ℝ) ≤ 16384)
  apply (add_le_add hSup hHardy).trans_eq
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

end EmcsfAcExtension.Local
