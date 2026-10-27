module

public import Mathlib

/-! # Numerical closure of the four difference forcings

The outgoing estimate absorbs its datum remainders into the initial-data
term. The incoming estimate retains the repaired `σ ε Δ₀/M` term exactly.
-/

public section

namespace EmcsfAcExtension.Local.Stab

private theorem forcing_terms_le {ε σ M δ J K G : ℝ}
    (hε : 0 ≤ ε) (hε₁ : ε ≤ 1) (hσ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (hM : 1 ≤ M)
    (hδ : 0 ≤ δ) (hJ : 0 ≤ J) (hK : 0 ≤ K) (hG : 0 ≤ G) :
    let H := J + ε * G + ε * δ / M
    let Yj := δ + (ε ^ 2 + σ) * (J + K) + ε * (ε ^ 2 + σ) * G
    let Yk := (ε ^ 2 + σ) * (J + K) + ε * (ε ^ 2 + σ) * G + σ * ε * δ / M
    (ε ^ 2 * K + ε ^ 3 * G + σ * ε ^ 3 * H ≤ Yj) ∧
    (σ * (δ + J + ε * G) ≤ Yj) ∧
    (ε ^ 2 * (J + K) + ε ^ 3 * G + σ * ε ^ 4 * δ / M ≤ Yj) ∧
    (σ * (J + K + ε * G + ε * δ / M) ≤ Yj) ∧
    (ε ^ 2 * J + ε ^ 3 * G ≤ Yk) ∧
    (ε ^ 2 * (J + K) + ε ^ 3 * G + σ * ε ^ 4 * δ / M ≤ Yk) ∧
    (σ * (J + K + ε * G + ε * δ / M) ≤ Yk) := by
  dsimp only
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hS : 0 ≤ J + K := add_nonneg hJ hK
  have hq : 0 ≤ ε ^ 2 + σ := add_nonneg (sq_nonneg _) hσ
  have hε₃ := pow_le_one₀ hε hε₁ (n := 3)
  have hε₄ := pow_le_one₀ hε hε₁ (n := 4)
  have hε₄ε : ε ^ 4 ≤ ε := by
    convert mul_le_mul_of_nonneg_right hε₃ hε using 1 <;> ring
  have hdata (z : ℝ) (hz : 0 ≤ z) (hz₁ : z ≤ 1) : σ * z * δ / M ≤ δ := by
    have hdiv : δ / M ≤ δ := div_le_self hδ hM
    calc
      _ = σ * (z * (δ / M)) := by ring
      _ ≤ 1 * (1 * δ) := mul_le_mul hσ₁ (mul_le_mul hz₁ hdiv (by positivity) zero_le_one)
        (by positivity) zero_le_one
      _ = _ := by ring
  have hd₄ := hdata (ε ^ 4) (by positivity) hε₄
  have hd₁ := hdata ε hε hε₁
  have hd₀ : σ * δ ≤ δ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hσ₁ hδ
  have hd₄k : σ * ε ^ 4 * δ / M ≤ σ * ε * δ / M := by
    convert mul_le_mul_of_nonneg_right hε₄ε (by positivity : 0 ≤ σ * δ / M) using 1 <;> ring
  have hdk : 0 ≤ σ * ε * δ / M := by positivity
  have hεfb : ε ^ 2 * (J + K) ≤ (ε ^ 2 + σ) * (J + K) :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hσ) hS
  have hσfb : σ * (J + K) ≤ (ε ^ 2 + σ) * (J + K) :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (sq_nonneg ε)) hS
  have hσJ : σ * J ≤ (ε ^ 2 + σ) * (J + K) :=
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hK) hσ).trans hσfb
  have hεJ : ε ^ 2 * J ≤ (ε ^ 2 + σ) * (J + K) :=
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hK) (sq_nonneg ε)).trans hεfb
  have hgeoε : ε ^ 3 * G ≤ ε * (ε ^ 2 + σ) * G := by
    have h := mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right hσ : ε ^ 2 ≤ ε ^ 2 + σ) (mul_nonneg hε hG)
    convert h using 1 <;> ring
  have hgeoσ : σ * ε * G ≤ ε * (ε ^ 2 + σ) * G := by
    have h := mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (sq_nonneg ε) : σ ≤ ε ^ 2 + σ) (mul_nonneg hε hG)
    convert h using 1 <;> ring
  have hfluxfb : ε ^ 2 * K + σ * ε ^ 3 * J ≤ (ε ^ 2 + σ) * (J + K) := by
    have h₁ : ε ^ 2 * K ≤ ε ^ 2 * (J + K) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hJ) (sq_nonneg ε)
    have h₂ : σ * ε ^ 3 * J ≤ σ * (J + K) := by
      have h := (mul_le_mul_of_nonneg_right hε₃ hJ).trans
          (by simpa only [one_mul] using le_add_of_nonneg_right hK)
      convert mul_le_mul_of_nonneg_left h hσ using 1; ring
    convert add_le_add h₁ h₂ using 1; ring
  have hfluxgeo : ε ^ 3 * G + σ * ε ^ 4 * G ≤ ε * (ε ^ 2 + σ) * G := by
    have h := mul_le_mul_of_nonneg_right hε₄ε (mul_nonneg hσ hG)
    nlinarith only [h]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      _ = (ε ^ 2 * K + σ * ε ^ 3 * J) + (ε ^ 3 * G + σ * ε ^ 4 * G) + σ * ε ^ 4 * δ / M := by ring
      _ ≤ (ε ^ 2 + σ) * (J + K) + ε * (ε ^ 2 + σ) * G + δ := add_le_add (add_le_add hfluxfb
          hfluxgeo) hd₄
      _ = _ := by ring
  · calc
      _ = σ * δ + σ * J + σ * ε * G := by ring
      _ ≤ _ := add_le_add (add_le_add hd₀ hσJ) hgeoσ
  · exact add_le_add (add_le_add hεfb hgeoε) hd₄ |>.trans_eq (by ring)
  · calc
      _ = σ * (J + K) + σ * ε * G + σ * ε * δ / M := by ring
      _ ≤ (ε ^ 2 + σ) * (J + K) + ε * (ε ^ 2 + σ) * G + δ := add_le_add (add_le_add hσfb hgeoσ) hd₁
      _ = _ := by ring
  · exact (add_le_add hεJ hgeoε).trans (le_add_of_nonneg_right hdk)
  · exact add_le_add (add_le_add hεfb hgeoε) hd₄k
  · calc
      _ = σ * (J + K) + σ * ε * G + σ * ε * δ / M := by ring
      _ ≤ _ := add_le_add (add_le_add hσfb hgeoσ) le_rfl

/-- Algebraic j forcing closure. `C` depends only on the four fixed
forcing constants `F,P,S,E`, uniformly in all nonnegative comparison
variables and physical parameters. Datum remainders are kept until this step. -/
theorem j_forcing_remainder_absorption (F P S E : ℝ)
    (hF : 0 < F) (hP : 0 < P) (hS : 0 < S) (hE : 0 < E) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε σ M δ J K G : ℝ,
      0 ≤ ε → ε ≤ 1 → 0 ≤ σ → σ ≤ 1 → 1 ≤ M →
      0 ≤ δ → 0 ≤ J → 0 ≤ K → 0 ≤ G →
      F * (ε ^ 2 * K + ε ^ 3 * G + σ * ε ^ 3 * (J + ε * G + ε * δ / M)) +
        P * σ * (δ + J + ε * G) +
        S * (ε ^ 2 * (J + K) + ε ^ 3 * G + σ * ε ^ 4 * δ / M) +
        E * σ * (J + K + ε * G + ε * δ / M) ≤
      C * δ + C * (ε ^ 2 + σ) * (J + K) + C * ε * (ε ^ 2 + σ) * G := by
  refine ⟨F + P + S + E, by positivity, ?_⟩
  intro ε σ M δ J K G hε hε₁ hσ hσ₁ hM hδ hJ hK hG
  have h := forcing_terms_le hε hε₁ hσ hσ₁ hM hδ hJ hK hG
  have h₁ := mul_le_mul_of_nonneg_left h.1 hF.le
  have h₂ := mul_le_mul_of_nonneg_left h.2.1 hP.le
  have h₃ := mul_le_mul_of_nonneg_left h.2.2.1 hS.le
  have h₄ := mul_le_mul_of_nonneg_left h.2.2.2.1 hE.le
  convert add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄ using 1 <;> ring

/-- Algebraic k forcing closure. `C` depends only on the three fixed
forcing constants `F,S,E`, uniformly in all parameters. The repaired
`C σ ε Δ₀/M` remainder is retained with its full scale. -/
theorem k_forcing_remainder_absorption (F S E : ℝ) (hF : 0 < F) (hS : 0 < S) (hE : 0 < E) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε σ M δ J K G : ℝ,
      0 ≤ ε → ε ≤ 1 → 0 ≤ σ → σ ≤ 1 → 1 ≤ M →
      0 ≤ δ → 0 ≤ J → 0 ≤ K → 0 ≤ G →
      F * (ε ^ 2 * J + ε ^ 3 * G) +
        S * (ε ^ 2 * (J + K) + ε ^ 3 * G + σ * ε ^ 4 * δ / M) +
        E * σ * (J + K + ε * G + ε * δ / M) ≤
      C * (ε ^ 2 + σ) * (J + K) + C * ε * (ε ^ 2 + σ) * G + C * σ * ε * δ / M := by
  refine ⟨F + S + E, by positivity, ?_⟩
  intro ε σ M δ J K G hε hε₁ hσ hσ₁ hM hδ hJ hK hG
  have h := forcing_terms_le hε hε₁ hσ hσ₁ hM hδ hJ hK hG
  have h₁ := mul_le_mul_of_nonneg_left h.2.2.2.2.1 hF.le
  have h₂ := mul_le_mul_of_nonneg_left h.2.2.2.2.2.1 hS.le
  have h₃ := mul_le_mul_of_nonneg_left h.2.2.2.2.2.2 hE.le
  convert add_le_add (add_le_add h₁ h₂) h₃ using 1 <;> ring

end EmcsfAcExtension.Local.Stab
