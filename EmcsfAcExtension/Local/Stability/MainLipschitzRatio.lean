module

public import EmcsfAcExtension.Local.Stability.MainRecords
public import EmcsfAcExtension.Local.Stability.SourceDifferenceCoefficient
import EmcsfAcExtension.Local.Stability.DifferenceMomentsCloseOut
import EmcsfAcExtension.Local.Stability.DifferenceMomentsCloseIn
import EmcsfAcExtension.Local.Stability.PotentialDifference
import EmcsfAcExtension.Local.Stability.FluxDifferenceIncomingAbsolute

/-! # Incoming phase and flux at the approved radial comparison scale

The potential comparison is substituted before forming the incoming ratio
record. The factor `1/M` is retained in both incoming records.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- [internal] The outgoing and incoming radial records from internal project record.
The threshold and constant depend only on `A` and the fixed box, before
all physical parameters, data and the pair. The incoming remainder is
exactly internal project record (R), `σεH/M`. -/
theorem ratio_records (A : ℝ) (hA : 0 < A) :
    ∃ η D : ℝ, 0 < η ∧ 0 < D ∧
    ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ^ 2 + sigma e M T ≤ η →
      RatioDifferences D e T ε M (dataDist h₁ h₂ T) S₁ S₂ := by
  obtain ⟨ηo, Co, hηo, hCo, ho⟩ := stab_out_difference A hA
  obtain ⟨ηi, Ci, hηi, hCi, hi⟩ := stab_in_difference A hA
  obtain ⟨ηp, Cp, hηp, hCp, hp⟩ := stab_potential_difference A hA
  let D := Co + Ci + 2 * Ci * Cp
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨min ηo (min ηi ηp), D, lt_min hηo (lt_min hηi hηp), hD, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hsmall
  have hε : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans
    (hs₂.box.2 (0, 0) ⟨le_rfl, le_rfl, hs₂.pos.le⟩).2.2.2.2.2.1
  have hM : 0 < M := zero_lt_one.trans_le hs₂.box.1
  have hT : 0 ≤ T := hs₂.pos.le
  have hσ : 0 ≤ sigma e M T := by unfold sigma; positivity
  let J := (jDist T S₁ S₂).toReal
  let K := (kDist e T S₁ S₂).toReal
  let G := (geomDist T S₁ S₂).toReal
  let δ := dataDist h₁ h₂ T
  let H := J + ε * G + ε * δ / M
  let Eo := J + ε * G
  let Ei := K + ε * G + sigma e M T * ε / M * H
  have hδ : 0 ≤ δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hJ : 0 ≤ J := ENNReal.toReal_nonneg
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hEo : 0 ≤ Eo := by dsimp [Eo]; positivity
  have hEi : 0 ≤ Ei := by dsimp [Ei]; positivity
  have hCoD : Co ≤ D := by dsimp [D]; linarith only [hCi, mul_pos hCi hCp]
  have hCiD : Ci ≤ D := by dsimp [D]; linarith only [hCo, mul_pos hCi hCp]
  have hCpD : 2 * Ci * Cp ≤ D := by dsimp [D]; linarith only [hCo, hCi]
  have hout := ho T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ (hsmall.trans (min_le_left _ _))
  have hin := hi T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂
    (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hpot := hp T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂
    (hsmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hpotreal : (supDist T S₁.A S₂.A).toReal ≤
      Cp * |e| * T * (M * J + ε * δ + M * ε * G) := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hpot).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have hphase : Ci * ε * |e| * (T / 2) * (supDist T S₁.A S₂.A).toReal ≤
      (2 * Ci * Cp) * (sigma e M T * ε / M * H) := by
    calc
      _ ≤ Ci * ε * |e| * (T / 2) *
          (Cp * |e| * T * (M * J + ε * δ + M * ε * G)) := by
        exact mul_le_mul_of_nonneg_left hpotreal (by positivity)
      _ = _ := by
        dsimp [sigma, H]
        rw [← sq_abs e]
        field_simp [ne_of_gt hM]
        ; ring
  have hinbound : Ci * (K + ε * G) +
      Ci * ε * |e| * (T / 2) * (supDist T S₁.A S₂.A).toReal ≤ D * Ei := by
    calc
      _ ≤ D * (K + ε * G) + D * (sigma e M T * ε / M * H) :=
        add_le_add (mul_le_mul_of_nonneg_right hCiD (by positivity))
          (hphase.trans (mul_le_mul_of_nonneg_right hCpD (by positivity)))
      _ = _ := by dsimp [Ei]; ring
  have hout' := hout.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hCoD hEo))
  have hin' := hin.trans (ENNReal.ofReal_le_ofReal hinbound)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hpt
    apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hD.le hEo)).mp
    rw [ofReal_norm]
    exact (le_iSup₂_of_le p hpt le_rfl).trans ((le_add_right le_rfl).trans hout')
  · intro p hpt
    apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hD.le hEi)).mp
    rw [ofReal_norm]
    exact (le_iSup₂_of_le p hpt le_rfl).trans ((le_add_right le_rfl).trans hin')
  · intro u hu
    exact (le_iSup₂_of_le u hu le_rfl).trans ((le_add_left le_rfl).trans hout')
  · intro v hv
    exact (le_iSup₂_of_le v hv le_rfl).trans ((le_add_left le_rfl).trans hin')

/-- [internal] The sharper incoming flux record follows from the raw
quadratic-flux inequality and internal project record (R). Constants depend only on `A`,
before the pair and all scales; the remainder is `σε²H/M`. -/
theorem incoming_flux_record (A : ℝ) (hA : 0 < A) :
    ∃ η D : ℝ, 0 < η ∧ 0 < D ∧
    ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ^ 2 + sigma e M T ≤ η →
      IncomingFluxDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ := by
  obtain ⟨η, C, hη, hC, hr⟩ := ratio_records A hA
  refine ⟨min η (1 / 4), 2 * C + 5120 * A,
    lt_min hη (by norm_num), by positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hsmall
  have hratio := hr T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ (hsmall.trans (min_le_left _ _))
  have hε : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans
    (hs₂.box.2 (0, 0) ⟨le_rfl, le_rfl, hs₂.pos.le⟩).2.2.2.2.2.1
  have hσ : 0 ≤ sigma e M T := by unfold sigma; positivity
  have hM : 0 < M := zero_lt_one.trans_le hs₂.box.1
  have hδ : 0 ≤ dataDist h₁ h₂ T := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hε₂ : ε ^ 2 ≤ 1 / 4 :=
    ((le_add_of_nonneg_right hσ).trans hsmall).trans (min_le_right _ _)
  constructor
  intro v hv
  rcases eq_or_lt_of_le hv.1 with heq | hvpos
  · subst v
    simp
  have hraw := stab_in_quadratic_flux_lintegral_raw hA hs₁ hs₂ hε₂ (u := 0)
    le_rfl hvpos hv.2
  apply (hraw.trans (add_le_add
    (mul_le_mul' le_rfl (hratio.in_hardy v hv)) le_rfl)).trans
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * ε),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  let J := (jDist T S₁ S₂).toReal
  let K := (kDist e T S₁ S₂).toReal
  let G := (geomDist T S₁ S₂).toReal
  let H := J + ε * G + ε * dataDist h₁ h₂ T / M
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hH : 0 ≤ H := by dsimp [H, J]; positivity
  change (2 * ε) * (C * (K + ε * G + sigma e M T * ε / M * H)) +
      5120 * A * ε ^ 2 * G ≤
    (2 * C + 5120 * A) * (ε * K + ε ^ 2 * G + sigma e M T * ε ^ 2 / M * H)
  have h₁ : 0 ≤ 5120 * A * (ε * K + sigma e M T * ε ^ 2 / M * H) := by positivity
  calc
    _ ≤ (2 * ε) * (C * (K + ε * G + sigma e M T * ε / M * H)) +
        5120 * A * ε ^ 2 * G +
        5120 * A * (ε * K + sigma e M T * ε ^ 2 / M * H) :=
      le_add_of_nonneg_right h₁
    _ = _ := by ring

end EmcsfAcExtension.Local.Stab
