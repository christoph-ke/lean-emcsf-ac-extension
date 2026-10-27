module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeomStrongSource
import EmcsfAcExtension.Local.Stability.GeomStrongSourceOrders
import EmcsfAcExtension.Local.Stability.GeomStrongInitial

/-! # Strong comparison of the geometric renormalized envelopes

G1, the initial common-gauge comparison and the actual smooth axis
match give the small envelope difference consumed by the limit layer.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [internal]
The smooth geometric envelopes differ by `C(ε+σ)Δ₀`,
charged_SF_new_version.tex:L5428–5435. This helper takes the pending main Lipschitz
conclusion explicitly. The threshold and constant depend only on `A`
and its uniform main constant `C₀`, before all field parameters and
pairs, uniformly in minimum radii and derivative suprema. -/
theorem stab_geometric_envelope_difference_of_main_lipschitz
    (A C₀ : ℝ) (hA : 0 < A) (hC₀ : 0 < C₀) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        jDist T S₁ S₂ + kDist e T S₁ S₂ + geomDist T S₁ S₂ ≤
          ENNReal.ofReal (C₀ * dataDist h₁ h₂ T) →
        (∫⁻ v in Icc 0 T, outEnv 0 (fun u v =>
          geomL (triangle 0 T) S₁ u v - geomL (triangle 0 T) S₂ u v) v) +
        (∫⁻ u in Icc 0 T, inEnv T (fun u v =>
          geomN (triangle 0 T) S₁ u v - geomN (triangle 0 T) S₂ u v) u) ≤
          ENNReal.ofReal (C * (ε + sigma e M T) * dataDist h₁ h₂ T) := by
  obtain ⟨ηs, Cs, hηs, hCs, hSource⟩ := stab_geometric_source_difference A hA
  obtain ⟨Ci, hCi, hInitial⟩ := Stab.initial_geometric_renormalized_difference
  let C := 2 * Ci + 3 * Cs * (3 * C₀ + 1)
  refine ⟨min ηs (1 / 4), C, lt_min hηs (by norm_num),
    by dsimp only [C]; positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall hmain
  let Δ := dataDist h₁ h₂ T
  let B := C₀ * Δ
  let J := (jDist T S₁ S₂).toReal
  let K := (kDist e T S₁ S₂).toReal
  let G := (geomDist T S₁ S₂).toReal
  have hΔ : 0 ≤ Δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hB : 0 ≤ B := mul_nonneg hC₀.le hΔ
  have hJ0 : 0 ≤ J := ENNReal.toReal_nonneg
  have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
  have hG0 : 0 ≤ G := ENNReal.toReal_nonneg
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hσ : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hs := hsmall.trans (min_le_right _ _)
  have hε1 : ε ≤ 1 := by nlinarith only [hs, hσ, sq_nonneg (ε - 1)]
  have hε2 : ε ^ 2 ≤ ε := by nlinarith only [hε1, hε]
  have rb {X : ℝ≥0∞} (hX : X ≤ ENNReal.ofReal B) : X.toReal ≤ B := by
    simpa only [ENNReal.toReal_ofReal hB] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hX
  have hJ : J ≤ B := rb ((le_add_of_nonneg_right bot_le).trans
    ((le_add_of_nonneg_right bot_le).trans hmain))
  have hK : K ≤ B := rb ((le_add_of_nonneg_left bot_le).trans
    ((le_add_of_nonneg_right bot_le).trans hmain))
  have hG : G ≤ B := rb ((le_add_of_nonneg_left bot_le).trans hmain)
  have hsraw := hSource T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hsmall.trans (min_le_left _ _))
  have hsclose : (∫⁻ p in triangle 0 T, ‖geomSource S₁ p.1 p.2 - geomSource S₂ p.1 p.2‖ₑ) ≤
      ENNReal.ofReal (Cs * (3 * C₀ + 1) * (ε + sigma e M T) * Δ) := by
    apply hsraw.trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ Cs * ε * (B + B) + Cs * ε * (1 * B) + Cs * sigma e M T * (Δ + B + B + 1 * B) := by
        change Cs * ε * (J + K) + Cs * ε ^ 2 * G +
          Cs * sigma e M T * (Δ + J + K + ε * G) ≤ _
        gcongr; first | exact hε2 | simpa only [one_mul] using hG
      _ ≤ Cs * (3 * C₀ + 1) * (ε + sigma e M T) * Δ := by
        apply sub_nonneg.mp
        convert (show 0 ≤ Cs * ε * Δ by positivity) using 1; dsimp only [B]; ring
  apply (stab_geometric_envelope_difference_le_source_c1 h₁s h₂s).trans
  apply (add_le_add (mul_le_mul' le_rfl
    (hInitial T e ε M A S₁ S₂ h₁ h₂ h₁s h₂s)) (mul_le_mul' le_rfl hsclose)).trans
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_ofNat 3,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  apply sub_nonneg.mp
  convert (show 0 ≤ 2 * Ci * sigma e M T * Δ by positivity) using 1;
    dsimp only [C, Δ]; ring

end EmcsfAcExtension.Local
