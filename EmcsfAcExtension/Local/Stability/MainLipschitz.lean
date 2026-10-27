module

public import EmcsfAcExtension.Local.Stability.MainLipschitzRecords
import EmcsfAcExtension.Local.Stability.JCloseEstimate
import EmcsfAcExtension.Local.Stability.KCloseEstimate
import EmcsfAcExtension.Local.Stability.MainIncomingClosed
import EmcsfAcExtension.Local.Stability.MainDifference
public import EmcsfAcExtension.Local.Stability.MainLipschitzSources

/-! # Unconditional small-data stability comparisons

The seven comparison inputs are produced from internal project record with a common
constant before the data or solution pair. The approved scalar and k
remainders are retained throughout the closure argument.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [node restart-stab-j-close]
The comparison on the §4.4 small-data scope. Threshold and constant depend
only on `A` and the fixed box, before every physical parameter, datum and
solution pair, uniformly in derivative suprema and the minimum radius. -/
theorem stab_j_close (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
    ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ^ 2 + sigma e M T ≤ η →
      (jDist T S₁ S₂).toReal ≤ C * dataDist h₁ h₂ T +
        C * (ε ^ 2 + sigma e M T) * ((jDist T S₁ S₂).toReal + (kDist e T S₁ S₂).toReal) +
        C * ε * (ε ^ 2 + sigma e M T) * (geomDist T S₁ S₂).toReal := by
  obtain ⟨ηr, D, hηr, hD, hrecords⟩ := Stab.difference_records A hA
  obtain ⟨ηh, C, hηh, hC, hclose⟩ := Stab.j_close_of_differences A D hA hD
  refine ⟨min ηr (min ηh (1 / 4)), C, lt_min hηr (lt_min hηh (by norm_num)), hC, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hsmall
  rcases hrecords T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂
    (hsmall.trans (min_le_left _ _)) with ⟨hr, hf, hq, hp, hi, ho, hg⟩
  exact hclose T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂
    (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))) hr hf hq hp hi

/-- [node restart-stab-k-close]
The comparison on the §4.4 small-data scope. Threshold and constant depend
only on `A` and the fixed box, before every physical parameter, datum and
solution pair, uniformly in derivative suprema and the minimum radius. -/
theorem stab_k_close (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
    ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ^ 2 + sigma e M T ≤ η →
      (kDist e T S₁ S₂).toReal ≤ (jDist T S₁ S₂).toReal +
        C * (ε ^ 2 + sigma e M T) * ((jDist T S₁ S₂).toReal + (kDist e T S₁ S₂).toReal) +
        C * ε * (ε ^ 2 + sigma e M T) * (geomDist T S₁ S₂).toReal +
        C * sigma e M T * ε * dataDist h₁ h₂ T / M := by
  obtain ⟨ηr, D, hηr, hD, hrecords⟩ := Stab.difference_records A hA
  obtain ⟨ηh, C, hηh, hC, hclose⟩ := Stab.k_close_of_differences A D hA hD
  refine ⟨min ηr (min ηh (1 / 4)), C, lt_min hηr (lt_min hηh (by norm_num)), hC, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hsmall
  rcases hrecords T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂
    (hsmall.trans (min_le_left _ _)) with ⟨hr, hf, hq, hp, hi, ho, hg⟩
  exact hclose T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂
    (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))) hr hf hq ho

/-- [node restart-sec-bv-stability-independent#incoming-normalized-field-comparison]
The comparison on the §4.4 small-data scope. Threshold and constant depend
only on `A` and the fixed box, before every physical parameter, datum and
solution pair, uniformly in derivative suprema and the minimum radius. -/
theorem Stab.incoming_normalized_field_comparison (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
    ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ^ 2 + sigma e M T ≤ η →
      supDist T S₁.b S₂.b ≤ ENNReal.ofReal (C * dataDist h₁ h₂ T) := by
  obtain ⟨ηr, D, hηr, hD, hrecords⟩ := Stab.difference_records A hA
  obtain ⟨ηh, C, hηh, hC, hclose⟩ := Stab.incoming_normalized_field_comparison_of_differences A D hA
      hD
  refine ⟨min ηr (min ηh (1 / 4)), C, lt_min hηr (lt_min hηh (by norm_num)), hC, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hsmall
  rcases hrecords T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂
    (hsmall.trans (min_le_left _ _)) with ⟨hr, hf, hq, hp, hi, ho, hg⟩
  exact hclose T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂
    (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))) hr hf hq hp hi ho hg

/-- [node restart-stab-main-lipschitz]
The comparison on the §4.4 small-data scope. Threshold and constant depend
only on `A` and the fixed box, before every physical parameter, datum and
solution pair, uniformly in derivative suprema and the minimum radius. -/
theorem stab_main_lipschitz (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
    ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ^ 2 + sigma e M T ≤ η →
      jDist T S₁ S₂ + kDist e T S₁ S₂ + geomDist T S₁ S₂ + supDist T S₁.a S₂.a +
        supDist T S₁.b S₂.b + supDist T S₁.phi S₂.phi ≤
          ENNReal.ofReal (C * dataDist h₁ h₂ T) := by
  obtain ⟨ηr, D, hηr, hD, hrecords⟩ := Stab.difference_records A hA
  obtain ⟨ηh, C, hηh, hC, hclose⟩ := stab_main_lipschitz_of_differences A D hA hD
  refine ⟨min ηr (min ηh (1 / 4)), C, lt_min hηr (lt_min hηh (by norm_num)), hC, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hsmall
  rcases hrecords T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂
    (hsmall.trans (min_le_left _ _)) with ⟨hr, hf, hq, hp, hi, ho, hg⟩
  exact hclose T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂
    (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))) hr hf hq hp hi ho hg

end EmcsfAcExtension.Local
