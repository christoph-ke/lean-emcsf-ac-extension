module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.DifferenceMomentsCloseIn
import EmcsfAcExtension.Local.Stability.FluxDifferenceIncomingAbsolute
import EmcsfAcExtension.Local.Stability.PotentialDifferenceBudget

/-! # Closed incoming quadratic flux comparison

The incoming radial estimate retains its phase term. The scale-correct
potential bound makes that term perturbative with the explicit factor
`σ`, preserving every data contribution in the graph contract.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [node restart-sec-bv-stability-independent#incoming-quadratic-flux-difference]
The absolute incoming quadratic flux difference, charged_SF_new_version.tex:L5422–5422
and approved internal project record (QFi). Constants depend only on `A` and the fixed
box, before all other parameters, the pair and minimum radius. -/
theorem Stab.incoming_quadratic_flux_difference (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v, ENNReal.ofReal
          |(-S₁.nu u v) / S₁.r u v * ‖S₁.xi u v / (S₁.nu u v : ℂ)‖ ^ 2 -
            (-S₂.nu u v) / S₂.r u v * ‖S₂.xi u v / (S₂.nu u v : ℂ)‖ ^ 2|) ≤
          ENNReal.ofReal (C * ε * (kDist e T S₁ S₂).toReal +
            C * ε ^ 2 * (geomDist T S₁ S₂).toReal + C * sigma e M T * ε *
              ((jDist T S₁ S₂).toReal + ε * dataDist h₁ h₂ T +
                ε * (geomDist T S₁ S₂).toReal)) := by
  obtain ⟨ηi, Ci, hηi, hCi, hIn⟩ := stab_in_difference A hA
  obtain ⟨ηp, Cp, hηp, hCp, hPhase⟩ := stab_potential_phase_bounds A hA
  let C := 2 * Ci + 5120 * A + Ci * Cp + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨min ηi (min ηp (1 / 12)), C,
    lt_min hηi (lt_min hηp (by norm_num)), hC, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall
  let J := (jDist T S₁ S₂).toReal
  let K := (kDist e T S₁ S₂).toReal
  let G := (geomDist T S₁ S₂).toReal
  let P := T * |e| * (supDist T S₁.A S₂.A).toReal
  let H := J + ε * dataDist h₁ h₂ T + ε * G
  have hJ : 0 ≤ J := ENNReal.toReal_nonneg
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hΔ : 0 ≤ dataDist h₁ h₂ T := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hP : 0 ≤ P := mul_nonneg (mul_nonneg h₁s.pos.le (abs_nonneg e)) ENNReal.toReal_nonneg
  have hH : 0 ≤ H := add_nonneg (add_nonneg hJ (mul_nonneg hε0 hΔ)) (mul_nonneg hε0 hG)
  have hσ : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hεsq : ε ^ 2 ≤ 1 / 12 := ((le_add_of_nonneg_right hσ).trans hsmall).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hε1 : ε ≤ 1 := by nlinarith only [hεsq, sq_nonneg (ε - 1)]
  have hεself : ε ^ 2 ≤ ε := by nlinarith only [hε0, hε1]
  have hclosed := hIn T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hsmall.trans (min_le_left _ _))
  have hHardy := (le_add_of_nonneg_left bot_le).trans hclosed
  have hPb := (hPhase T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
    (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _)))).2
  have hprod : 0 < Ci * Cp := mul_pos hCi hCp
  have hCK : 2 * Ci ≤ C := by dsimp only [C]; nlinarith only [hprod, hA]
  have hCG : 2 * Ci + 5120 * A ≤ C := by dsimp only [C]; nlinarith only [hprod]
  have hCP : Ci * Cp ≤ C := by dsimp only [C]; nlinarith only [hCi, hA]
  apply iSup₂_le
  intro v hv
  rcases hv.1.eq_or_lt with rfl | hv0
  · simp
  · have hraw := stab_in_quadratic_flux_lintegral_raw hA h₁s h₂s
      (by linarith only [hεsq]) le_rfl hv0 hv.2
    have hh : (∫⁻ u in Icc 0 v, ENNReal.ofReal (-S₁.nu u v / S₁.r u v *
        ‖S₁.xi u v / (S₁.nu u v : ℂ) - S₂.xi u v / (S₂.nu u v : ℂ)‖)) ≤
        ENNReal.ofReal (Ci * (K + ε * G) + Ci * ε * P / 2) := by
      have he := (le_iSup₂_of_le v hv le_rfl).trans hHardy
      convert he using 1
      dsimp only [K, G, P]
      congr 1
      ring
    apply (hraw.trans (add_le_add (mul_le_mul' le_rfl hh) le_rfl)).trans
    rw [← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hε0),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hpScale := mul_le_mul_of_nonneg_left hPb (show 0 ≤ Ci * ε ^ 2 by positivity)
    have heScale := mul_le_mul_of_nonneg_left hεself
      (show 0 ≤ Ci * Cp * sigma e M T * H by positivity)
    have hkScale := mul_le_mul_of_nonneg_right hCK (mul_nonneg hε0 hK)
    have hgScale := mul_le_mul_of_nonneg_right hCG (mul_nonneg (sq_nonneg ε) hG)
    have hcScale := mul_le_mul_of_nonneg_right hCP
      (mul_nonneg (mul_nonneg hσ hε0) hH)
    dsimp only [J, K, G, P, H] at hpScale heScale hkScale hgScale hcScale ⊢
    nlinarith only [hpScale, heScale, hkScale, hgScale, hcScale]

end EmcsfAcExtension.Local
