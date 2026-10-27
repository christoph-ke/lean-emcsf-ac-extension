module

public import EmcsfAcExtension.Local.Stability.MainRecords

/-! # Incoming normalized field after closing the derivative norms

The incoming ratio difference includes its connection error. The identity
`b = phi + xi / nu` then supplies the full incoming normalized field on the
closed triangle, including its axis values.
-/

public section

open Set Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- Conditional incoming normalized-field comparison from the first-half
field and ratio conclusions and the closed derivative/geometric sum.
`C` depends only on their fixed constants `D,L`, uniformly in the pair. -/
theorem incoming_normalized_field_comparison_of_closed_distances (D L : ℝ)
    (hD : 0 < D) (hL : 0 < L) : ∃ C : ℝ, 0 < C ∧
    ∀ (T e ε M A : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ≤ 1 → sigma e M T ≤ 1 →
      FieldDifference D T ε (dataDist h₁ h₂ T) S₁ S₂ →
      RatioDifferences D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      (jDist T S₁ S₂).toReal + (kDist e T S₁ S₂).toReal + (geomDist T S₁ S₂).toReal ≤
        L * dataDist h₁ h₂ T →
      supDist T S₁.b S₂.b ≤ ENNReal.ofReal (C * dataDist h₁ h₂ T) := by
  refine ⟨3 * D * (L + 1), mul_pos (mul_pos (by norm_num) hD) (by linarith), ?_⟩
  intro T e ε M A S₁ S₂ h₁ h₂ _hset₁ hset₂ hε1 hσ1 hfield hratio hclosed
  have hε0 : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans
    (hset₂.box.2 (0, 0) ⟨le_rfl, le_rfl, hset₂.pos.le⟩).2.2.2.2.2.1
  have hM : 1 ≤ M := hset₂.box.1
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hσ0 : 0 ≤ sigma e M T := by unfold sigma; positivity
  let δ := dataDist h₁ h₂ T
  let J := (jDist T S₁ S₂).toReal
  let K := (kDist e T S₁ S₂).toReal
  let G := (geomDist T S₁ S₂).toReal
  have hδ : 0 ≤ δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hJ : 0 ≤ J := ENNReal.toReal_nonneg
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hHd : ε * δ / M ≤ δ := by
    apply (div_le_iff₀ hM0).2
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hε1.trans hM) hδ
  have hq : sigma e M T * ε / M ≤ 1 := by
    apply (div_le_iff₀ hM0).2
    rw [one_mul]
    exact (((mul_le_of_le_one_left hε0 hσ1).trans hε1)).trans hM
  have hGε : ε * G ≤ G := by nlinarith only [hε1, hG]
  have hH : J + ε * G + ε * δ / M ≤ δ + J + G := by
    linarith only [hGε, hHd]
  have hH0 : 0 ≤ J + ε * G + ε * δ / M := by positivity
  have hphase : sigma e M T * ε / M * (J + ε * G + ε * δ / M) ≤ δ + J + G := by
    calc
      _ ≤ 1 * (δ + J + G) := mul_le_mul hq hH hH0 zero_le_one
      _ = _ := by ring
  have hsum : (δ + J + ε * G) +
      (K + ε * G + sigma e M T * ε / M * (J + ε * G + ε * δ / M)) ≤
        3 * (δ + J + K + G) := by
    linarith only [hphase, hGε, hδ, hJ, hK]
  have htotal : δ + J + K + G ≤ (L + 1) * δ := by
    change J + K + G ≤ L * δ at hclosed
    linarith only [hclosed]
  apply iSup₂_le
  intro p hp
  rw [← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  have hφ : ‖S₁.phi p.1 p.2 - S₂.phi p.1 p.2‖ ≤ D * (δ + J + ε * G) :=
    (le_add_of_nonneg_left (norm_nonneg _)).trans (hfield.bound p hp)
  have hξ := hratio.in_pointwise p hp
  have hb : S₁.b p.1 p.2 - S₂.b p.1 p.2 =
      (S₁.phi p.1 p.2 - S₂.phi p.1 p.2) +
        (S₁.xi p.1 p.2 / (S₁.nu p.1 p.2 : ℂ) -
          S₂.xi p.1 p.2 / (S₂.nu p.1 p.2 : ℂ)) := by
    simp only [Fields.b]
    ring
  calc
    _ ≤ ‖S₁.phi p.1 p.2 - S₂.phi p.1 p.2‖ +
        ‖S₁.xi p.1 p.2 / (S₁.nu p.1 p.2 : ℂ) -
          S₂.xi p.1 p.2 / (S₂.nu p.1 p.2 : ℂ)‖ := by rw [hb]; exact norm_add_le _ _
    _ ≤ D * ((δ + J + ε * G) +
        (K + ε * G + sigma e M T * ε / M * (J + ε * G + ε * δ / M))) := by
      have := add_le_add hφ hξ
      nlinarith only [this]
    _ ≤ D * (3 * (δ + J + K + G)) := mul_le_mul_of_nonneg_left hsum hD.le
    _ ≤ D * (3 * ((L + 1) * δ)) := by gcongr
    _ = _ := by ring

end EmcsfAcExtension.Local.Stab
