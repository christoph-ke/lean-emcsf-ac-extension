module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.DifferenceMomentsCloseOut
import EmcsfAcExtension.Local.Stability.DifferenceMomentsCloseIn

/-! # Common constants for the two closed radial comparisons

The approved optical route closes each radial mass feedback before the
charge and potential projections. This assembles the exact pair (R0)
with one threshold and constant, retaining the incoming phase term.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [node restart-sec-bv-stability-independent#coupled-radial-mass-charge-absorption]
The simultaneous closed radial estimates (R0) of approved internal project record,
charged_SF_new_version.tex:L5116–5246. The optical feedback and scalar absorption
are proved in the per-direction dependencies, so this assembly assumes
no field, charge, potential or mass comparison conclusion. The common
threshold and constant depend only on `A` and the literal fixed box,
before all other parameters, the pair and minimum radius. -/
theorem Stab.coupled_radial_mass_charge_absorption (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        (supDist T (fun u v => S₁.theta u v / (S₁.lam u v : ℂ))
          (fun u v => S₂.theta u v / (S₂.lam u v : ℂ)) +
          (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ENNReal.ofReal (S₁.lam u v / S₁.r u v *
            ‖S₁.theta u v / (S₁.lam u v : ℂ) - S₂.theta u v / (S₂.lam u v : ℂ)‖)) ≤
          ENNReal.ofReal (C * ((jDist T S₁ S₂).toReal + ε * (geomDist T S₁ S₂).toReal))) ∧
        (supDist T (fun u v => S₁.xi u v / (S₁.nu u v : ℂ))
          (fun u v => S₂.xi u v / (S₂.nu u v : ℂ)) +
          (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v, ENNReal.ofReal (-S₁.nu u v / S₁.r u v *
            ‖S₁.xi u v / (S₁.nu u v : ℂ) - S₂.xi u v / (S₂.nu u v : ℂ)‖)) ≤
          ENNReal.ofReal (C * ((kDist e T S₁ S₂).toReal + ε * (geomDist T S₁ S₂).toReal) +
            C * ε * |e| * (T / 2) * (supDist T S₁.A S₂.A).toReal)) := by
  obtain ⟨ηo, Co, hηo, hCo, hOut⟩ := stab_out_difference A hA
  obtain ⟨ηi, Ci, hηi, hCi, hIn⟩ := stab_in_difference A hA
  refine ⟨min ηo ηi, Co + Ci, lt_min hηo hηi, by positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hT : 0 < T := h₁s.pos
  have ho0 : 0 ≤ (jDist T S₁ S₂).toReal + ε * (geomDist T S₁ S₂).toReal :=
    add_nonneg ENNReal.toReal_nonneg (mul_nonneg hε0 ENNReal.toReal_nonneg)
  have hi0 : 0 ≤ (kDist e T S₁ S₂).toReal + ε * (geomDist T S₁ S₂).toReal :=
    add_nonneg ENNReal.toReal_nonneg (mul_nonneg hε0 ENNReal.toReal_nonneg)
  have hp0 : 0 ≤ ε * |e| * (T / 2) * (supDist T S₁.A S₂.A).toReal := by positivity
  constructor
  · apply (hOut T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hsmall.trans (min_le_left _ _))).trans
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCi.le) ho0)
  · apply (hIn T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hsmall.trans (min_le_right _ _))).trans
    apply ENNReal.ofReal_le_ofReal
    have hCi' : Ci ≤ Co + Ci := le_add_of_nonneg_left hCo.le
    have hb := mul_le_mul_of_nonneg_right hCi' hi0
    have hp := mul_le_mul_of_nonneg_right hCi' hp0
    nlinarith only [hb, hp]

end EmcsfAcExtension.Local
