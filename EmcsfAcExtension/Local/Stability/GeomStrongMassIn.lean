module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeomStrongMassInForcing
import EmcsfAcExtension.Local.Stability.GeomStrongMassInCharge
import EmcsfAcExtension.Local.Stability.DifferenceMomentsCloseIn
import EmcsfAcExtension.Local.Stability.PotentialDifferenceBudget

/-! # Incoming weighted normalized mass comparison

The positive incoming radial damping is integrated from its own axis.
The phase term in the incoming scalar difference is closed by the
scale-correct potential comparison. No outgoing weighted mass conclusion
is substituted for this incoming calculation.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The incoming weighted mass difference has a derivative-independent
comparison bound. The threshold and constant depend only on `A` and
the fixed box, before every parameter, datum, solution and minimum radius. -/
theorem stab_in_weighted_mass_difference (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v, ENNReal.ofReal
          (-S₁.nu u v / S₁.r u v * |S₁.mu u v - S₂.mu u v|)) ≤
          ENNReal.ofReal (C * ε * (kDist e T S₁ S₂).toReal +
            C * ε ^ 2 * (geomDist T S₁ S₂).toReal + C * sigma e M T * ε *
              ((jDist T S₁ S₂).toReal + ε * dataDist h₁ h₂ T +
                ε * (geomDist T S₁ S₂).toReal)) := by
  obtain ⟨ηi, Ci, hηi, hCi, hIn⟩ := stab_in_difference A hA
  obtain ⟨ηp, Cp, hηp, hCp, hPhase⟩ := stab_potential_phase_bounds A hA
  obtain ⟨ηe, Ce, hηe, hCe, hEm⟩ := stab_in_em_difference A hA
  let C := 2 * Ci + Ci * Cp + Ce + 87040 * A + 10880 + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨min ηi (min ηp (min ηe (1 / 12))), C,
    lt_min hηi (lt_min hηp (lt_min hηe (by norm_num))), hC, ?_⟩
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
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hσ : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hP : 0 ≤ P := mul_nonneg (mul_nonneg h₁s.pos.le (abs_nonneg e))
    ENNReal.toReal_nonneg
  have hsize : ε ^ 2 + sigma e M T ≤ 1 / 12 := hsmall.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hεsq : ε ^ 2 ≤ 1 / 4 := by linarith only [hsize, hσ]
  have hσ1 : sigma e M T ≤ 1 := by linarith only [hsize, sq_nonneg ε]
  have hε1 : ε ≤ 1 := by nlinarith only [hεsq, sq_nonneg (ε - 1)]
  have hεself : ε ^ 2 ≤ ε := by nlinarith only [hε, hε1]
  have hHardy := (le_add_of_nonneg_left bot_le).trans
    (hIn T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hsmall.trans (min_le_left _ _)))
  have hPb := (hPhase T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
    (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _)))).2
  have hEb := hEm T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
    (hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hprod : 0 < Ci * Cp := mul_pos hCi hCp
  have hCK : 2 * Ci ≤ C := by dsimp only [C]; linarith only [hprod, hCe, hA]
  have hCG : 2 * Ci + 87040 * A + 10880 ≤ C := by
    dsimp only [C]; linarith only [hprod, hCe]
  have hCE : Ci * Cp + Ce ≤ C := by dsimp only [C]; linarith only [hCi, hA]
  apply iSup₂_le
  intro v hv
  rcases hv.1.eq_or_lt with rfl | hv0
  · simp
  · have hraw := stab_in_mass_difference_raw h₁s h₂s le_rfl hv0 hv.2
    have hsource := stab_in_mass_forcing_budget hA h₁s h₂s hεsq hσ1 hv0.le hv.2
    have hh : (∫⁻ u in Icc 0 v, ENNReal.ofReal (-S₁.nu u v / S₁.r u v *
        ‖S₁.xi u v / (S₁.nu u v : ℂ) - S₂.xi u v / (S₂.nu u v : ℂ)‖)) ≤
        ENNReal.ofReal (Ci * (K + ε * G) + Ci * ε * P / 2) := by
      have he := (le_iSup₂_of_le v hv le_rfl).trans hHardy
      convert he using 1
      dsimp only [K, G, P]
      congr 1
      ring
    have he := (le_iSup₂_of_le v hv le_rfl).trans hEb
    apply (hraw.trans (hsource.trans (add_le_add
      (add_le_add (mul_le_mul' le_rfl hh) he) le_rfl))).trans
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * ε),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hpScale := mul_le_mul_of_nonneg_left hPb (show 0 ≤ Ci * ε ^ 2 by positivity)
    have heScale := mul_le_mul_of_nonneg_left hεself
      (show 0 ≤ Ci * Cp * sigma e M T * H by positivity)
    have hkScale := mul_le_mul_of_nonneg_right hCK (mul_nonneg hε hK)
    have hgScale := mul_le_mul_of_nonneg_right hCG (mul_nonneg (sq_nonneg ε) hG)
    have hcScale := mul_le_mul_of_nonneg_right hCE
      (mul_nonneg (mul_nonneg hσ hε) hH)
    dsimp only [J, K, G, P, H] at hpScale heScale hkScale hgScale hcScale ⊢
    nlinarith only [hpScale, heScale, hkScale, hgScale, hcScale]

/-- [node restart-sec-bv-stability-independent#incoming-weighted-mass-difference]
Incoming weighted mass comparison and both undifferenced budgets.
The threshold and constant depend only on `A` and the fixed geometric
box, uniformly in all parameters, data, fields, minimum radii and
initial derivative suprema. The comparison tends to zero when the
main comparison distances do; it uses the incoming constraint. -/
theorem Stab.incoming_weighted_mass_difference (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        ((⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v, ENNReal.ofReal
          (-S₁.nu u v / S₁.r u v * |S₁.mu u v - S₂.mu u v|)) ≤
          ENNReal.ofReal (C * ε * (kDist e T S₁ S₂).toReal +
            C * ε ^ 2 * (geomDist T S₁ S₂).toReal + C * sigma e M T * ε *
              ((jDist T S₁ S₂).toReal + ε * dataDist h₁ h₂ T +
                ε * (geomDist T S₁ S₂).toReal))) ∧
        ((⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v, ENNReal.ofReal
          (-S₁.nu u v / S₁.r u v * |S₁.mu u v|)) ≤
            ENNReal.ofReal (C * (1 + sigma e M T) * ε ^ 2)) ∧
        ((⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v, ENNReal.ofReal
          (-S₂.nu u v / S₂.r u v * |S₂.mu u v|)) ≤
            ENNReal.ofReal (C * (1 + sigma e M T) * ε ^ 2)) := by
  obtain ⟨ηm, Cm, hηm, hCm, hMass⟩ := stab_in_weighted_mass_difference A hA
  let C := Cm + 4096 * A + 512
  have hC : 0 < C := by dsimp only [C]; positivity
  have hCmC : Cm ≤ C := by dsimp only [C]; linarith only [hA]
  have hbaseC : 4096 * A + 512 ≤ C := by dsimp only [C]; linarith only [hCm]
  refine ⟨min ηm (1 / 4), C, lt_min hηm (by norm_num), hC, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall
  have hσ : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₁.xi 0 0 / (S₁.nu 0 0 : ℂ)))).trans
      (h₁s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₁s.pos.le⟩).2.2.2.2.2.1)
  have hεsq : ε ^ 2 ≤ 1 / 4 :=
    ((le_add_of_nonneg_right hσ).trans hsmall).trans (min_le_right _ _)
  have hΔ : 0 ≤ dataDist h₁ h₂ T := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hbudget {S : Fields} {h : ℝ → ℂ} (hs : StabSetting e T ε M A S h) :
      (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v, ENNReal.ofReal
        (-S.nu u v / S.r u v * |S.mu u v|)) ≤
          ENNReal.ofReal (C * (1 + sigma e M T) * ε ^ 2) := by
    apply iSup₂_le
    intro v hv
    apply (stab_in_mixed_mass_le hA hs hs hεsq hv.1 hv.2).trans
    apply ENNReal.ofReal_le_ofReal
    have hcoef : 16 * (256 * A + 32 * sigma e M T) ≤ C * (1 + sigma e M T) := by
      calc
        _ ≤ (4096 * A + 512) * (1 + sigma e M T) := by
          nlinarith only [mul_nonneg hA.le hσ]
        _ ≤ _ := mul_le_mul_of_nonneg_right hbaseC (by positivity)
    have hh := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ε)
    linarith only [hh]
  refine ⟨?_, hbudget h₁s, hbudget h₂s⟩
  apply (hMass T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hsmall.trans (min_le_left _ _))).trans
  apply ENNReal.ofReal_le_ofReal
  have hh := mul_le_mul_of_nonneg_right hCmC
    (show 0 ≤ ε * (kDist e T S₁ S₂).toReal + ε ^ 2 * (geomDist T S₁ S₂).toReal +
      sigma e M T * ε * ((jDist T S₁ S₂).toReal + ε * dataDist h₁ h₂ T +
        ε * (geomDist T S₁ S₂).toReal) by positivity)
  linarith only [hh]

end EmcsfAcExtension.Local
