module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassRaw
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassForcingBudget
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassCharge
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassBudgets
import EmcsfAcExtension.Local.Stability.DifferenceMomentsCloseOut

/-! # Normalized mass Volterra comparison

The damped normalized mass equation proves both the uniform difference
and the singular outgoing weighted difference. The separate coefficient
estimate records the small linear coefficient of the ordinary mass
Volterra equation. No unnormalized mass estimate is asserted.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [node restart-sec-bv-stability-independent#mass-Volterra-difference]
The ordinary mass Volterra coefficient has integral `Cε²` on
every outgoing section. The constant depends only on `A` and the fixed
box, before all other parameters and the solution; it is independent
of the minimum radius and initial derivative supremum. For the graph node,
`A` is the fixed box-dependent envelope constant from the independent area
estimate, as in internal project record; uniformity over arbitrary `A` is not asserted. -/
theorem Stab.mass_volterra_coefficient (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T e ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
      StabSetting e T ε M A S h → ε ^ 2 ≤ 1 / 4 →
      (⨆ u ∈ Icc 0 T, ∫⁻ t in Icc u T, ENNReal.ofReal (S.lam u t / S.r u t *
        ‖S.theta u t / (S.lam u t : ℂ)‖ ^ 2)) ≤ ENNReal.ofReal (C * ε ^ 2) := by
  refine ⟨256 * A, by positivity, ?_⟩
  intro T e ε M S h hset hε
  apply iSup₂_le
  intro u hu
  exact stab_out_mixed_quadratic_le hset hset hε hu.1 hu.2

/-- [node restart-sec-bv-stability-independent#mass-Volterra-difference]
The scale-invariant mass difference and its stronger outgoing weighted
version, charged_SF_new_version.tex:L5344–5344 and approved internal project record (MV).
The threshold and constant depend only on `A` and the fixed box,
before all other parameters, the pair and the minimum radius. The
ordinary mass coefficient is bounded in `mass_volterra_coefficient`. -/
theorem Stab.mass_volterra_difference (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        supDist T S₁.mu S₂.mu +
          (⨆ u ∈ Icc 0 T, ∫⁻ t in Icc u T, ENNReal.ofReal
            (S₁.lam u t / S₁.r u t * |S₁.mu u t - S₂.mu u t|)) ≤
          ENNReal.ofReal (C * ε * (jDist T S₁ S₂).toReal +
            C * ε ^ 2 * (geomDist T S₁ S₂).toReal + C * sigma e M T * ε *
              ((jDist T S₁ S₂).toReal + ε * dataDist h₁ h₂ T +
                ε * (geomDist T S₁ S₂).toReal)) := by
  obtain ⟨ηo, Co, hηo, hCo, hOut⟩ := stab_out_difference A hA
  obtain ⟨ηe, Ce, hηe, hCe, hEm⟩ := stab_out_em_difference A hA
  let C := 4 * Co + 2 * Ce + 174080 * A + 21760 + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨min ηo (min ηe (1 / 12)), C,
    lt_min hηo (lt_min hηe (by norm_num)), hC, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall
  let J := (jDist T S₁ S₂).toReal
  let G := (geomDist T S₁ S₂).toReal
  let H := J + ε * dataDist h₁ h₂ T + ε * G
  let B := 2 * Co * ε * (J + ε * G) + Ce * sigma e M T * ε * H +
    (87040 * A + 10880) * ε ^ 2 * G
  have hJ : 0 ≤ J := ENNReal.toReal_nonneg
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hΔ : 0 ≤ dataDist h₁ h₂ T := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hσ0 : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hsize : ε ^ 2 + sigma e M T ≤ 1 / 12 :=
    hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hεsq : ε ^ 2 ≤ 1 / 4 := by linarith only [hsize, hσ0]
  have hσ : sigma e M T ≤ 1 := by linarith only [hsize, sq_nonneg ε]
  have ho := hOut T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hsmall.trans (min_le_left _ _))
  have he := hEm T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
    (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hforcing : ∀ u ∈ Icc 0 T,
      (∫⁻ t in Icc u T, ENNReal.ofReal |massDifferenceForcing S₁ S₂ u t|) ≤
        ENNReal.ofReal B := by
    intro u hu
    have hh := (le_iSup₂_of_le u hu le_rfl).trans
      ((le_add_of_nonneg_left bot_le).trans ho)
    have hem := (le_iSup₂_of_le u hu le_rfl).trans he
    apply (stab_out_mass_forcing_budget hA h₁s h₂s hεsq hσ hu.1 hu.2).trans
    apply (add_le_add (add_le_add (mul_le_mul' le_rfl hh) hem) le_rfl).trans_eq
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * ε),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    dsimp only [B, J, G, H]
    ring
  have hU : supDist T S₁.mu S₂.mu ≤ ENNReal.ofReal B := by
    apply iSup₂_le
    rintro ⟨u, v⟩ hp
    rw [← ofReal_norm, Real.norm_eq_abs]
    change ENNReal.ofReal |S₁.mu u v - S₂.mu u v| ≤ ENNReal.ofReal B
    rcases hp.2.1.eq_or_lt with heq | huv
    · change u = v at heq
      subst v
      simp only [Fields.mu, (h₁s.c1.axis u hp).1, (h₂s.c1.axis u hp).1,
        div_zero, sub_self, abs_zero, ENNReal.ofReal_zero]
      exact bot_le
    · apply (stab_out_mass_difference_raw h₁s h₂s hp.1 huv hp.2.2).1.trans
      apply (lintegral_mono_set (Ioc_subset_Icc_self.trans
        (Icc_subset_Icc_right hp.2.2))).trans
      exact hforcing u ⟨hp.1, huv.le.trans hp.2.2⟩
  have hW : (⨆ u ∈ Icc 0 T, ∫⁻ t in Icc u T, ENNReal.ofReal
      (S₁.lam u t / S₁.r u t * |S₁.mu u t - S₂.mu u t|)) ≤ ENNReal.ofReal B := by
    apply iSup₂_le
    intro u hu
    rcases hu.2.eq_or_lt with rfl | huT
    · simp
    · have hh := (stab_out_mass_difference_raw h₁s h₂s hu.1 huT le_rfl).2
      rw [restrict_Ioc_eq_restrict_Icc] at hh
      exact hh.trans (hforcing u hu)
  apply (add_le_add hU hW).trans
  rw [← ENNReal.ofReal_add hB hB]
  apply ENNReal.ofReal_le_ofReal
  have hCJ : 4 * Co ≤ C := by dsimp only [C]; linarith only [hCe, hA]
  have hCG : 4 * Co + 174080 * A + 21760 ≤ C := by
    dsimp only [C]; linarith only [hCe]
  have hCE : 2 * Ce ≤ C := by dsimp only [C]; linarith only [hCo, hA]
  have hj := mul_le_mul_of_nonneg_right hCJ (mul_nonneg hε hJ)
  have hg := mul_le_mul_of_nonneg_right hCG (mul_nonneg (sq_nonneg ε) hG)
  have he := mul_le_mul_of_nonneg_right hCE (show 0 ≤ sigma e M T * ε * H by positivity)
  dsimp only [B, H, J, G] at hj hg he ⊢
  nlinarith only [hj, hg, he]

end EmcsfAcExtension.Local
