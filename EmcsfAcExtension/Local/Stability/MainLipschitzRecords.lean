module

public import EmcsfAcExtension.Local.Stability.MainLipschitzMono
import EmcsfAcExtension.Local.Stability.MainLipschitzRatio
import EmcsfAcExtension.Local.Stability.FieldDifference
import EmcsfAcExtension.Local.Stability.ChargeDifference
import EmcsfAcExtension.Local.Stability.PotentialDifference
import EmcsfAcExtension.Local.Stability.FluxDifferenceCloseOut
import EmcsfAcExtension.Local.Stability.GeometryDifferenceClose

/-! # Seven unconditional comparison records with one common constant

The finite maximum of constants and minimum of thresholds are formed
before the physical parameters, the data, and the solution pair.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- [internal] internal project record supplies all seven closure inputs unconditionally.
The common constant and threshold depend only on `A` and the literal fixed
box, uniformly in every physical scale, datum, pair and derivative supremum.
No stability conclusion is a premise. -/
theorem difference_records (A : ℝ) (hA : 0 < A) :
    ∃ η D : ℝ, 0 < η ∧ 0 < D ∧
    ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ^ 2 + sigma e M T ≤ η →
      RatioDifferences D e T ε M (dataDist h₁ h₂ T) S₁ S₂ ∧
      FieldDifference D T ε (dataDist h₁ h₂ T) S₁ S₂ ∧
      ChargeDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ ∧
      PotentialDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ ∧
      IncomingFluxDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ ∧
      OutgoingFluxDifference D T ε S₁ S₂ ∧
      GeometryDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ := by
  obtain ⟨ηr, Cr, hηr, hCr, hr⟩ := ratio_records A hA
  obtain ⟨ηf, Cf, hηf, hCf, hf⟩ := stab_field_difference A hA
  obtain ⟨ηq, Cq, hηq, hCq, hq⟩ := stab_charge_difference A hA
  obtain ⟨ηp, Cp, hηp, hCp, hp⟩ := stab_potential_difference A hA
  obtain ⟨ηi, Ci, hηi, hCi, hi⟩ := incoming_flux_record A hA
  obtain ⟨ηo, Co, hηo, hCo, ho⟩ := outgoing_quadratic_flux_difference A hA
  obtain ⟨ηg, Cg, hηg, hCg, hg⟩ := stab_geometry_difference A hA
  let D := max 1 (max Cr (max Cf (max Cq (max (2 * Cp) (max Ci (max Co Cg))))))
  let η := min ηr (min ηf (min ηq (min ηp (min ηi (min ηo ηg)))))
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hη : 0 < η := lt_min hηr (lt_min hηf
    (lt_min hηq (lt_min hηp (lt_min hηi (lt_min hηo hηg)))))
  have hCrD : Cr ≤ D := by
    dsimp only [D]
    apply le_max_of_le_right
    exact le_max_left _ _
  have hCfD : Cf ≤ D := by
    dsimp only [D]
    apply le_max_of_le_right
    apply le_max_of_le_right
    exact le_max_left _ _
  have hCqD : Cq ≤ D := by
    dsimp only [D]
    apply le_max_of_le_right
    apply le_max_of_le_right
    apply le_max_of_le_right
    exact le_max_left _ _
  have hCpD : 2 * Cp ≤ D := by
    dsimp only [D]
    apply le_max_of_le_right
    apply le_max_of_le_right
    apply le_max_of_le_right
    apply le_max_of_le_right
    exact le_max_left _ _
  have hCiD : Ci ≤ D := by
    dsimp only [D]
    apply le_max_of_le_right
    apply le_max_of_le_right
    apply le_max_of_le_right
    apply le_max_of_le_right
    apply le_max_of_le_right
    exact le_max_left _ _
  have hCoD : Co ≤ D := by
    dsimp only [D]
    apply le_max_of_le_right
    apply le_max_of_le_right
    apply le_max_of_le_right
    apply le_max_of_le_right
    apply le_max_of_le_right
    apply le_max_of_le_right
    exact le_max_left _ _
  have hCgD : Cg ≤ D := by
    dsimp only [D]
    apply le_max_of_le_right
    apply le_max_of_le_right
    apply le_max_of_le_right
    apply le_max_of_le_right
    apply le_max_of_le_right
    apply le_max_of_le_right
    exact le_max_right _ _
  refine ⟨η, D, hη, hD, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hsmall
  have hε : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans
    (hs₂.box.2 (0, 0) ⟨le_rfl, le_rfl, hs₂.pos.le⟩).2.2.2.2.2.1
  have hM : 0 ≤ M := zero_le_one.trans hs₂.box.1
  have hδ : 0 ≤ dataDist h₁ h₂ T := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hsr := hsmall.trans (min_le_left _ _)
  have hs := hsmall.trans (min_le_right _ _)
  have hsf := hs.trans (min_le_left _ _)
  have hs := hs.trans (min_le_right _ _)
  have hsq := hs.trans (min_le_left _ _)
  have hs := hs.trans (min_le_right _ _)
  have hsp := hs.trans (min_le_left _ _)
  have hs := hs.trans (min_le_right _ _)
  have hsi := hs.trans (min_le_left _ _)
  have hs := hs.trans (min_le_right _ _)
  have hso := hs.trans (min_le_left _ _)
  have hsg := hs.trans (min_le_right _ _)
  refine ⟨(hr T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hsr).mono hCrD hε hM hδ,
    ?_, ?_, ?_, (hi T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hsi).mono hCiD hε hM hδ,
    ?_, ?_⟩
  · constructor
    intro p hpt
    have hfields := hf T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hsf
    have hptwise : ENNReal.ofReal (‖S₁.a p.1 p.2 - S₂.a p.1 p.2‖ +
        ‖S₁.phi p.1 p.2 - S₂.phi p.1 p.2‖) ≤
        ENNReal.ofReal (Cf * (dataDist h₁ h₂ T + (jDist T S₁ S₂).toReal +
          ε * (geomDist T S₁ S₂).toReal)) := by
      rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _), ofReal_norm, ofReal_norm]
      exact (add_le_add (le_iSup₂_of_le p hpt le_rfl)
        (le_iSup₂_of_le p hpt le_rfl)).trans hfields
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    exact hptwise.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hCfD (by positivity)))
  · constructor
    intro p hpt hlt
    apply (hq T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hsq p.1 p.2 hpt.1 hlt hpt.2.2).trans
    gcongr
  · have hpot : PotentialDifference (2 * Cp) e T ε M (dataDist h₁ h₂ T) S₁ S₂ := by
      constructor
      apply (hp T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hsp).trans_eq
      congr 1
      ring
    exact hpot.mono hCpD hs₂.pos.le hε hM hδ
  · constructor
    intro u hu
    have hflux := (le_iSup₂_of_le u hu le_rfl).trans
      (ho T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hso)
    have heq : (∫⁻ v in Icc u T, ENNReal.ofReal
        |kRealCoefficient S₁ u v - kRealCoefficient S₂ u v|) =
        (∫⁻ v in Icc u T, ENNReal.ofReal
          |S₁.lam u v / S₁.r u v * ‖S₁.theta u v / (S₁.lam u v : ℂ)‖ ^ 2 -
            S₂.lam u v / S₂.r u v * ‖S₂.theta u v / (S₂.lam u v : ℂ)‖ ^ 2|) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro v hv
      dsimp only
      rw [k_coefficient_eq_flux hs₁ ⟨hu.1, hv.1, hv.2⟩,
        k_coefficient_eq_flux hs₂ ⟨hu.1, hv.1, hv.2⟩]
      congr 1
      rw [neg_div, neg_div, neg_mul, neg_mul, neg_sub_neg, abs_sub_comm]
    rw [heq]
    apply hflux.trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ = Co * (ε * (jDist T S₁ S₂).toReal + ε ^ 2 * (geomDist T S₁ S₂).toReal) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hCoD (by positivity)
  · exact (GeometryDifference.mk (hg T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hsg)).mono hCgD hε hδ

end EmcsfAcExtension.Local.Stab
