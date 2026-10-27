module

public import EmcsfAcExtension.Local.Defs.Setting

/-! # Simultaneous absorption with the repaired k datum term

Pure real algebra for the closure system at charged_SF_new_version.tex:L5343–5371
and the approved internal project record comparison closure. The small datum remainder
in the k inequality is retained throughout.
-/

public section

namespace EmcsfAcExtension.Local.Stab

/-- Absorb the three comparison inequalities with the repaired k remainder.
The threshold and bound depend only on their common coefficient `B`,
independently of all distances, backgrounds, lengths and couplings. -/
theorem comparison_absorption (B : ℝ) (hB : 1 ≤ B) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (ε σ M δ j k G : ℝ), 0 ≤ ε → ε ≤ 1 → 0 ≤ σ → 1 ≤ M →
        0 ≤ δ → 0 ≤ j → 0 ≤ k → 0 ≤ G → ε ^ 2 + σ ≤ η →
        j ≤ B * δ + B * (ε ^ 2 + σ) * (j + k) + B * ε * (ε ^ 2 + σ) * G →
        k ≤ j + B * (ε ^ 2 + σ) * (j + k) + B * ε * (ε ^ 2 + σ) * G +
          B * σ * ε * δ / M →
        G ≤ B * ε * (j + k) + B * σ * δ + B * (ε ^ 2 + σ) * G →
        j + k + G ≤ C * δ := by
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hBp : B + 1 ≠ 0 := ne_of_gt (by linarith only [hB0])
  let η := 1 / (48 * (B + 1) ^ 2)
  refine ⟨η, 32 * (B + 1) ^ 2, by dsimp [η]; positivity, by positivity, ?_⟩
  intro ε σ M δ j k G hε0 hε1 hσ0 hM hδ hj0 hk0 hG0 hsmall hj hk hG
  let q := ε ^ 2 + σ
  have hq0 : 0 ≤ q := add_nonneg (sq_nonneg ε) hσ0
  have hq : q ≤ η := hsmall
  have hBq : B * q ≤ 1 / 48 := by
    have hBB : B ≤ (B + 1) ^ 2 := by nlinarith only [hB0.le, sq_nonneg B]
    calc
      B * q ≤ (B + 1) ^ 2 * η := mul_le_mul hBB hq hq0 (sq_nonneg _)
      _ = 1 / 48 := by dsimp [η]; field_simp [hBp]
  have hBBq : B ^ 2 * q ≤ 1 / 48 := by
    have hBB : B ^ 2 ≤ (B + 1) ^ 2 := by nlinarith only [hB0.le]
    calc
      B ^ 2 * q ≤ (B + 1) ^ 2 * η := mul_le_mul hBB hq hq0 (sq_nonneg _)
      _ = 1 / 48 := by dsimp [η]; field_simp [hBp]
  have hσq : σ ≤ q := le_add_of_nonneg_left (sq_nonneg ε)
  have hBσ : B * σ ≤ 1 / 48 :=
    (mul_le_mul_of_nonneg_left hσq hB0.le).trans hBq
  have hBε : B * ε ≤ B := by nlinarith only [hε1, hB0.le]
  have hGterm : B * q * G ≤ G / 48 := by
    convert mul_le_mul_of_nonneg_right hBq hG0 using 1; ring
  have hGmain : B * ε * (j + k) ≤ B * (j + k) :=
    mul_le_mul_of_nonneg_right hBε (add_nonneg hj0 hk0)
  have hGdata : B * σ * δ ≤ δ / 48 := by
    convert mul_le_mul_of_nonneg_right hBσ hδ using 1; ring
  have hGcoarse : G ≤ 2 * B * (j + k + δ) := by
    have hGB : B * (j + k) + δ / 48 ≤ B * (j + k + δ) := by
      have := mul_le_mul_of_nonneg_right hB hδ
      linarith only [this, hδ]
    change G ≤ B * ε * (j + k) + B * σ * δ + B * q * G at hG
    have hZ : 0 ≤ B * (j + k + δ) := by positivity
    linarith only [hG, hGterm, hGmain, hGdata, hGB, hZ]
  have hrem : B * σ * ε * δ / M ≤ B * δ := by
    have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
    apply (div_le_iff₀ hM0).2
    calc
      B * σ * ε * δ ≤ (1 / 48) * 1 * δ := by gcongr
      _ = δ / 48 := by ring
      _ ≤ δ := by linarith only [hδ]
      _ = 1 * δ * 1 := by ring
      _ ≤ B * δ * M := by
        exact mul_le_mul (mul_le_mul_of_nonneg_right hB hδ) hM zero_le_one
          (mul_nonneg hB0.le hδ)
  have hfeedback : B * ε * q * G ≤ B * q * G := by
    have := mul_le_mul_of_nonneg_right hε1 (mul_nonneg (mul_nonneg hB0.le hq0) hG0)
    nlinarith only [this]
  have hS : j + k ≤ 3 * B * δ + 3 * B * q * (j + k) + 3 * B * q * G := by
    change j ≤ B * δ + B * q * (j + k) + B * ε * q * G at hj
    change k ≤ j + B * q * (j + k) + B * ε * q * G +
      B * σ * ε * δ / M at hk
    linarith only [hj, hk, hrem, hfeedback]
  have hSterm : 3 * B * q * (j + k) ≤ (j + k) / 16 := by
    have := mul_le_mul_of_nonneg_right hBq (add_nonneg hj0 hk0)
    linarith only [this]
  have hGfeedback : 3 * B * q * G ≤ (j + k + δ) / 8 := by
    calc
      _ ≤ 3 * B * q * (2 * B * (j + k + δ)) := by gcongr
      _ = 6 * (B ^ 2 * q) * (j + k + δ) := by ring
      _ ≤ 6 * (1 / 48) * (j + k + δ) := by gcongr
      _ = _ := by ring
  have hSbound : j + k ≤ (6 * B + 2) * δ := by
    have hBd : 0 ≤ B * δ := mul_nonneg hB0.le hδ
    linarith only [hS, hSterm, hGfeedback, hBd, hδ]
  calc
    j + k + G ≤ (1 + 2 * B) * (j + k) + 2 * B * δ := by
      linarith only [hGcoarse]
    _ ≤ (1 + 2 * B) * ((6 * B + 2) * δ) + 2 * B * δ := by gcongr
    _ ≤ 32 * (B + 1) ^ 2 * δ := by
      have : (1 + 2 * B) * (6 * B + 2) + 2 * B ≤ 32 * (B + 1) ^ 2 := by
        nlinarith only [hB0.le, sq_nonneg B]
      convert mul_le_mul_of_nonneg_right this hδ using 1; ring

end EmcsfAcExtension.Local.Stab
