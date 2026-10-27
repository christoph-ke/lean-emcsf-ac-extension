module

public import Mathlib

/-! # Numerical closure of the repaired scalar source budget

The incoming phase remainder retains the datum factor `sigma ε⁴ δ/M`.
All other higher powers are absorbed into the two displayed source scales.
-/

public section

namespace EmcsfAcExtension.Local.Stab

/-- Numerical closure of the four-kernel scalar source estimate.
`C` depends only on the fixed envelope, ratio, and pointwise constants
`A,D,P`, and is uniform in all distances and physical parameters. -/
theorem scalar_source_remainder_absorption (A D P : ℝ)
    (hA : 0 < A) (hD : 0 < D) (hP : 0 < P) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε σ M δ J K G : ℝ),
      0 ≤ ε → ε ≤ 1 → 0 ≤ σ → σ ≤ 1 → 1 ≤ M →
      0 ≤ δ → 0 ≤ J → 0 ≤ K → 0 ≤ G →
      P * (16 * A ^ 2 * ε ^ 2 * (J + ε * G) +
        2 * D * A * ε ^ 2 * (K + ε * G + σ * ε / M * (J + ε * G + ε * δ / M)) +
        16 * A * ε ^ 2 * J + 16 * A ^ 2 * ε ^ 3 * G) ≤
      C * ε ^ 2 * (J + K) + C * ε ^ 3 * G + C * σ * ε ^ 4 * δ / M := by
  let Q := 32 * P * (A + 1) ^ 2 * (D + 1)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  refine ⟨4 * Q, mul_pos (by norm_num) hQ, ?_⟩
  intro ε σ M δ J K G hε0 hε1 hσ0 hσ1 hM hδ hJ hK hG
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hA₂ : A ^ 2 ≤ (A + 1) ^ 2 := by nlinarith only [hA.le]
  have hA₁ : A ≤ (A + 1) ^ 2 := by nlinarith only [hA.le, sq_nonneg A]
  have hD₁ : 1 ≤ D + 1 := by linarith only [hD]
  have hcoeff₁ : P * (16 * A ^ 2) ≤ Q := by
    calc
      _ ≤ P * (32 * (A + 1) ^ 2) := by gcongr; norm_num
      _ ≤ P * (32 * (A + 1) ^ 2) * (D + 1) := le_mul_of_one_le_right (by positivity) hD₁
      _ = _ := by dsimp [Q]; ring
  have hcoeff₂ : P * (2 * D * A) ≤ Q := by
    calc
      _ = P * (2 * A) * D := by ring
      _ ≤ P * (32 * (A + 1) ^ 2) * (D + 1) := by gcongr <;> norm_num
      _ = _ := by dsimp [Q]; ring
  have hcoeff₃ : P * (16 * A) ≤ Q := by
    calc
      _ ≤ P * (32 * (A + 1) ^ 2) := by gcongr; norm_num
      _ ≤ P * (32 * (A + 1) ^ 2) * (D + 1) := le_mul_of_one_le_right (by positivity) hD₁
      _ = _ := by dsimp [Q]; ring
  have hσε : σ * ε / M ≤ 1 := by
    apply (div_le_iff₀ hM0).2
    rw [one_mul]
    exact ((mul_le_of_le_one_left hε0 hσ1).trans hε1).trans hM
  have hphase₁ : σ * ε ^ 3 / M * J ≤ ε ^ 2 * J := by
    convert mul_le_mul_of_nonneg_right hσε
      (mul_nonneg (sq_nonneg ε) hJ) using 1 <;> ring
  have hphase₂ : σ * ε ^ 4 / M * G ≤ ε ^ 3 * G := by
    convert mul_le_mul_of_nonneg_right hσε
      (mul_nonneg (pow_nonneg hε0 3) hG) using 1 <;> ring
  have hphase₃ : σ * ε ^ 4 * δ / M / M ≤ σ * ε ^ 4 * δ / M :=
    div_le_self (by positivity) hM
  have hphase : σ * ε ^ 3 / M * (J + ε * G + ε * δ / M) ≤
      ε ^ 2 * J + ε ^ 3 * G + σ * ε ^ 4 * δ / M := by
    calc
      _ = (σ * ε ^ 3 / M * J + σ * ε ^ 4 / M * G) +
          σ * ε ^ 4 * δ / M / M := by ring
      _ ≤ _ := add_le_add (add_le_add hphase₁ hphase₂) hphase₃
  have hZ : 0 ≤ σ * ε ^ 4 * δ / M := by positivity
  have hraw : ε ^ 2 * (J + ε * G) +
      ε ^ 2 * (K + ε * G + σ * ε / M * (J + ε * G + ε * δ / M)) +
      ε ^ 2 * J + ε ^ 3 * G ≤
        4 * (ε ^ 2 * (J + K) + ε ^ 3 * G + σ * ε ^ 4 * δ / M) := by
    have hεJ : 0 ≤ ε ^ 2 * J := mul_nonneg (sq_nonneg _) hJ
    have hεK : 0 ≤ ε ^ 2 * K := mul_nonneg (sq_nonneg _) hK
    calc
      _ = (2 * ε ^ 2 * J + ε ^ 2 * K + 3 * ε ^ 3 * G) +
          σ * ε ^ 3 / M * (J + ε * G + ε * δ / M) := by ring
      _ ≤ (2 * ε ^ 2 * J + ε ^ 2 * K + 3 * ε ^ 3 * G) +
          (ε ^ 2 * J + ε ^ 3 * G + σ * ε ^ 4 * δ / M) :=
        add_le_add le_rfl hphase
      _ ≤ _ := by nlinarith only [hεJ, hεK, hZ]
  calc
    _ ≤ Q * (ε ^ 2 * (J + ε * G)) +
        Q * (ε ^ 2 * (K + ε * G + σ * ε / M * (J + ε * G + ε * δ / M))) +
        Q * (ε ^ 2 * J) + Q * (ε ^ 3 * G) := by
      rw [mul_add, mul_add, mul_add]
      apply add_le_add
      · apply add_le_add
        · apply add_le_add
          · convert mul_le_mul_of_nonneg_right hcoeff₁
              (show 0 ≤ ε ^ 2 * (J + ε * G) by positivity) using 1; ring
          · convert mul_le_mul_of_nonneg_right hcoeff₂
              (show 0 ≤ ε ^ 2 * (K + ε * G + σ * ε / M * (J + ε * G + ε * δ / M)) by
                positivity) using 1; ring
        · convert mul_le_mul_of_nonneg_right hcoeff₃
            (show 0 ≤ ε ^ 2 * J by positivity) using 1; ring
      · convert mul_le_mul_of_nonneg_right hcoeff₁
          (show 0 ≤ ε ^ 3 * G by positivity) using 1; ring
    _ = Q * (ε ^ 2 * (J + ε * G) +
        ε ^ 2 * (K + ε * G + σ * ε / M * (J + ε * G + ε * δ / M)) +
        ε ^ 2 * J + ε ^ 3 * G) := by ring
    _ ≤ Q * (4 * (ε ^ 2 * (J + K) + ε ^ 3 * G + σ * ε ^ 4 * δ / M)) :=
      mul_le_mul_of_nonneg_left hraw hQ.le
    _ = _ := by ring

/-- Numerical closure of the reflected four-kernel scalar source estimate.
`C` depends only on the fixed envelope, ratio, and pointwise constants
`A,D,P`, and is uniform in all distances and physical parameters. -/
theorem scalar_source_remainder_absorption_in (A D P : ℝ)
    (hA : 0 < A) (hD : 0 < D) (hP : 0 < P) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε σ M δ J K G : ℝ),
      0 ≤ ε → ε ≤ 1 → 0 ≤ σ → σ ≤ 1 → 1 ≤ M →
      0 ≤ δ → 0 ≤ J → 0 ≤ K → 0 ≤ G →
      P * (16 * A ^ 2 * ε ^ 2 * (K + ε * G + σ * ε / M * (J + ε * G + ε * δ / M)) +
        2 * D * A * ε ^ 2 * (J + ε * G) +
        16 * A * ε ^ 2 * K + 16 * A ^ 2 * ε ^ 3 * G) ≤
      C * ε ^ 2 * (J + K) + C * ε ^ 3 * G + C * σ * ε ^ 4 * δ / M := by
  let Q := 32 * P * (A + 1) ^ 2 * (D + 1)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  refine ⟨4 * Q, mul_pos (by norm_num) hQ, ?_⟩
  intro ε σ M δ J K G hε0 hε1 hσ0 hσ1 hM hδ hJ hK hG
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hA₂ : A ^ 2 ≤ (A + 1) ^ 2 := by nlinarith only [hA.le]
  have hA₁ : A ≤ (A + 1) ^ 2 := by nlinarith only [hA.le, sq_nonneg A]
  have hD₁ : 1 ≤ D + 1 := by linarith only [hD]
  have hcoeff₁ : P * (16 * A ^ 2) ≤ Q := by
    calc
      _ ≤ P * (32 * (A + 1) ^ 2) := by gcongr; norm_num
      _ ≤ P * (32 * (A + 1) ^ 2) * (D + 1) := le_mul_of_one_le_right (by positivity) hD₁
      _ = _ := by dsimp [Q]; ring
  have hcoeff₂ : P * (2 * D * A) ≤ Q := by
    calc
      _ = P * (2 * A) * D := by ring
      _ ≤ P * (32 * (A + 1) ^ 2) * (D + 1) := by gcongr <;> norm_num
      _ = _ := by dsimp [Q]; ring
  have hcoeff₃ : P * (16 * A) ≤ Q := by
    calc
      _ ≤ P * (32 * (A + 1) ^ 2) := by gcongr; norm_num
      _ ≤ P * (32 * (A + 1) ^ 2) * (D + 1) := le_mul_of_one_le_right (by positivity) hD₁
      _ = _ := by dsimp [Q]; ring
  have hσε : σ * ε / M ≤ 1 := by
    apply (div_le_iff₀ hM0).2
    rw [one_mul]
    exact ((mul_le_of_le_one_left hε0 hσ1).trans hε1).trans hM
  have hphase₁ : σ * ε ^ 3 / M * J ≤ ε ^ 2 * J := by
    convert mul_le_mul_of_nonneg_right hσε
      (mul_nonneg (sq_nonneg ε) hJ) using 1 <;> ring
  have hphase₂ : σ * ε ^ 4 / M * G ≤ ε ^ 3 * G := by
    convert mul_le_mul_of_nonneg_right hσε
      (mul_nonneg (pow_nonneg hε0 3) hG) using 1 <;> ring
  have hphase₃ : σ * ε ^ 4 * δ / M / M ≤ σ * ε ^ 4 * δ / M :=
    div_le_self (by positivity) hM
  have hphase : σ * ε ^ 3 / M * (J + ε * G + ε * δ / M) ≤
      ε ^ 2 * J + ε ^ 3 * G + σ * ε ^ 4 * δ / M := by
    calc
      _ = (σ * ε ^ 3 / M * J + σ * ε ^ 4 / M * G) +
          σ * ε ^ 4 * δ / M / M := by ring
      _ ≤ _ := add_le_add (add_le_add hphase₁ hphase₂) hphase₃
  have hZ : 0 ≤ σ * ε ^ 4 * δ / M := by positivity
  have hraw : ε ^ 2 * (K + ε * G + σ * ε / M * (J + ε * G + ε * δ / M)) +
      ε ^ 2 * (J + ε * G) +
      ε ^ 2 * K + ε ^ 3 * G ≤
        4 * (ε ^ 2 * (J + K) + ε ^ 3 * G + σ * ε ^ 4 * δ / M) := by
    have hεJ : 0 ≤ ε ^ 2 * J := mul_nonneg (sq_nonneg _) hJ
    have hεK : 0 ≤ ε ^ 2 * K := mul_nonneg (sq_nonneg _) hK
    calc
      _ = (ε ^ 2 * J + 2 * ε ^ 2 * K + 3 * ε ^ 3 * G) +
          σ * ε ^ 3 / M * (J + ε * G + ε * δ / M) := by ring
      _ ≤ (ε ^ 2 * J + 2 * ε ^ 2 * K + 3 * ε ^ 3 * G) +
          (ε ^ 2 * J + ε ^ 3 * G + σ * ε ^ 4 * δ / M) :=
        add_le_add le_rfl hphase
      _ ≤ _ := by nlinarith only [hεJ, hεK, hZ]
  calc
    _ ≤ Q * (ε ^ 2 * (K + ε * G + σ * ε / M * (J + ε * G + ε * δ / M))) +
        Q * (ε ^ 2 * (J + ε * G)) +
        Q * (ε ^ 2 * K) + Q * (ε ^ 3 * G) := by
      rw [mul_add, mul_add, mul_add]
      apply add_le_add
      · apply add_le_add
        · apply add_le_add
          · convert mul_le_mul_of_nonneg_right hcoeff₁
              (show 0 ≤ ε ^ 2 * (K + ε * G + σ * ε / M * (J + ε * G + ε * δ / M)) by positivity)
                  using 1; ring
          · convert mul_le_mul_of_nonneg_right hcoeff₂
              (show 0 ≤ ε ^ 2 * (J + ε * G) by
                positivity) using 1; ring
        · convert mul_le_mul_of_nonneg_right hcoeff₃
            (show 0 ≤ ε ^ 2 * K by positivity) using 1; ring
      · convert mul_le_mul_of_nonneg_right hcoeff₁
          (show 0 ≤ ε ^ 3 * G by positivity) using 1; ring
    _ = Q * (ε ^ 2 * (K + ε * G + σ * ε / M * (J + ε * G + ε * δ / M)) +
        ε ^ 2 * (J + ε * G) +
        ε ^ 2 * K + ε ^ 3 * G) := by ring
    _ ≤ Q * (4 * (ε ^ 2 * (J + K) + ε ^ 3 * G + σ * ε ^ 4 * δ / M)) :=
      mul_le_mul_of_nonneg_left hraw hQ.le
    _ = _ := by ring

end EmcsfAcExtension.Local.Stab
