module

public import EmcsfAcExtension.Local.Stability.JCloseEstimate
public import EmcsfAcExtension.Local.Stability.KCloseEstimate
public import EmcsfAcExtension.Local.Stability.MainRecords
import EmcsfAcExtension.Local.Stability.MainClosure

/-! # Simultaneous comparison absorption from the first-half records

The j and repaired k inequalities are proved before the three comparison
distances are absorbed. Only conclusions belonging to internal project record are inputs.
-/

public section

open Set Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- [internal]
 Derivative and geometry comparison from the listed first-half records.
Threshold and constant depend only on fixed `A,D`, uniformly in every
physical parameter, datum and solution derivative supremum. The repaired
k datum remainder is included in the simultaneous absorption. -/
theorem comparison_norms_of_differences (A D : ℝ) (hA : 0 < A) (hD : 0 < D) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
    ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ^ 2 + sigma e M T ≤ η →
      RatioDifferences D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      FieldDifference D T ε (dataDist h₁ h₂ T) S₁ S₂ →
      ChargeDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      PotentialDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      IncomingFluxDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      OutgoingFluxDifference D T ε S₁ S₂ →
      GeometryDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      (jDist T S₁ S₂).toReal + (kDist e T S₁ S₂).toReal + (geomDist T S₁ S₂).toReal ≤
        C * dataDist h₁ h₂ T := by
  obtain ⟨ηj, Cj, hηj, hCj, hj⟩ := j_close_of_differences A D hA hD
  obtain ⟨ηk, Ck, hηk, hCk, hk⟩ := k_close_of_differences A D hA hD
  let B := max 1 (max D (max Cj Ck))
  have hB : 1 ≤ B := le_max_left _ _
  have hDB : D ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hjB : Cj ≤ B := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hkB : Ck ≤ B := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨ηa, C, hηa, hC, habs⟩ := comparison_absorption B hB
  refine ⟨min 1 (min ηa (min ηj ηk)), C,
    lt_min zero_lt_one (lt_min hηa (lt_min hηj hηk)), hC, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hsmall hratio hfield hcharge hpot hfi hfo hgeom
  have hε : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans
    (hs₂.box.2 (0, 0) ⟨le_rfl, le_rfl, hs₂.pos.le⟩).2.2.2.2.2.1
  have hσ : 0 ≤ sigma e M T := by unfold sigma; positivity
  have hδ : 0 ≤ dataDist h₁ h₂ T := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hM : 0 < M := zero_lt_one.trans_le hs₂.box.1
  have hsmall₁ := hsmall.trans (min_le_left _ _)
  have hε₁ : ε ≤ 1 := by nlinarith only [hsmall₁, hσ]
  have hja := hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hka := hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hjraw := hj T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hja hratio hfield hcharge hpot hfi
  have hkraw := hk T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hka hratio hfield hcharge hfo
  let J := (jDist T S₁ S₂).toReal
  let K := (kDist e T S₁ S₂).toReal
  let G := (geomDist T S₁ S₂).toReal
  have hJ : 0 ≤ J := ENNReal.toReal_nonneg
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hjclosed : J ≤ B * dataDist h₁ h₂ T + B * (ε ^ 2 + sigma e M T) * (J + K) +
      B * ε * (ε ^ 2 + sigma e M T) * G := by
    apply hjraw.trans
    dsimp only [J, K, G] at *
    gcongr
  have hkclosed : K ≤ J + B * (ε ^ 2 + sigma e M T) * (J + K) +
      B * ε * (ε ^ 2 + sigma e M T) * G + B * sigma e M T * ε * dataDist h₁ h₂ T / M := by
    apply hkraw.trans
    dsimp only [J, K, G] at *
    gcongr
  have hgeomclosed : G ≤ B * ε * (J + K) + B * sigma e M T * dataDist h₁ h₂ T +
      B * (ε ^ 2 + sigma e M T) * G := by
    apply hgeom.bound.trans
    dsimp only [J, K, G] at *
    gcongr
  exact habs ε (sigma e M T) M (dataDist h₁ h₂ T) J K G hε hε₁ hσ hs₂.box.1 hδ hJ hK hG
    (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))) hjclosed hkclosed hgeomclosed

end EmcsfAcExtension.Local.Stab
