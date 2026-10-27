module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.MomentsFieldMeasurable

/-! # Connection forcing in the derivative difference equation

The potential estimate from internal project record is consumed in its conclusion form.
All integrations use the same incoming coordinate and the outgoing j envelope.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- Potential-difference conclusion consumed from internal project record
(charged_SF_new_version.tex:L5370–5370).
`C` is chosen before the pair; the displayed length and background factors are retained. -/
structure PotentialDifference (C e T ε M Δ₀ : ℝ) (S₁ S₂ : Fields) : Prop where
  /-- Uniform potential comparison in the fixed common gauge. -/
  bound : supDist T S₁.A S₂.A ≤ ENNReal.ofReal
    (C * |e| * (T / 2) * (M * (jDist T S₁ S₂).toReal + ε * Δ₀ +
      M * ε * (geomDist T S₁ S₂).toReal))

/-- Two integrations of the connection difference cost at most the incoming
length times its uniform bound times the outgoing envelope norm.
The coefficient is exactly `1`, independent of all parameters. -/
theorem phase_area_le_of_bound {e T ε M A B : ℝ} {S₁ S₂ : Fields}
    {h₂ : ℝ → ℂ} (hset₂ : StabSetting e T ε M A S₂ h₂)
    (hpot : supDist T S₁.A S₂.A ≤ ENNReal.ofReal B) :
    (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v,
      ‖-(I * e * (S₁.A u v - S₂.A u v) * jC1 (triangle 0 T) S₂ u v)‖ₑ) ≤
        ENNReal.ofReal (T * |e| * B) *
          ∫⁻ v in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S₂) v := by
  have hpoint (u v : ℝ) (hp : (u, v) ∈ triangle 0 T) :
      ‖-(I * e * (S₁.A u v - S₂.A u v) * jC1 (triangle 0 T) S₂ u v)‖ₑ ≤
        ENNReal.ofReal (|e| * B) * outEnv 0 (jC1 (triangle 0 T) S₂) v := by
    have hA' : ‖S₁.A u v - S₂.A u v‖ₑ ≤ ENNReal.ofReal B :=
      (le_iSup₂_of_le (u, v) hp (le_rfl :
        ‖S₁.A u v - S₂.A u v‖ₑ ≤ ‖S₁.A u v - S₂.A u v‖ₑ)).trans hpot
    have hA : ENNReal.ofReal |S₁.A u v - S₂.A u v| ≤ ENNReal.ofReal B := by
      simpa only [← ofReal_norm, Real.norm_eq_abs] using hA'
    rw [← ofReal_norm]
    simp only [norm_neg, norm_mul, norm_I, one_mul, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    rw [ENNReal.ofReal_mul (mul_nonneg (abs_nonneg e) (abs_nonneg _)),
      ENNReal.ofReal_mul (abs_nonneg e), ofReal_norm]
    calc
      _ ≤ (ENNReal.ofReal |e| * ENNReal.ofReal B) *
          outEnv 0 (jC1 (triangle 0 T) S₂) v := by
        exact mul_le_mul' (mul_le_mul' le_rfl hA)
          (le_iSup₂_of_le u ⟨hp.1, hp.2.1⟩ le_rfl)
      _ = _ := by rw [ENNReal.ofReal_mul (abs_nonneg e)]
  calc
    _ ≤ ∫⁻ v in Icc 0 T, ENNReal.ofReal (T * |e| * B) *
        outEnv 0 (jC1 (triangle 0 T) S₂) v := by
      apply setLIntegral_mono' measurableSet_Icc
      intro v hv
      calc
        _ ≤ ∫⁻ _u in Icc 0 v, ENNReal.ofReal (|e| * B) *
            outEnv 0 (jC1 (triangle 0 T) S₂) v := by
          apply setLIntegral_mono' measurableSet_Icc
          intro u hu
          exact hpoint u v ⟨hu.1, hu.2, hv.2⟩
        _ = ENNReal.ofReal v * (ENNReal.ofReal (|e| * B) *
            outEnv 0 (jC1 (triangle 0 T) S₂) v) := by
          rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
          ac_rfl
        _ ≤ ENNReal.ofReal T * (ENNReal.ofReal (|e| * B) *
            outEnv 0 (jC1 (triangle 0 T) S₂) v) := by gcongr; exact hv.2
        _ = _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hset₂.pos.le]
          congr 2
          ring
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- [internal]
 Conditional helper for the covariant-transport-phase-difference node.
Connection forcing from the potential-difference conclusion of internal project record,
charged_SF_new_version.tex:L5345–5358. `C` depends only on the envelope constant `A`
and the input estimate constant `D`, uniformly in all pair parameters. -/
theorem covariant_transport_phase_difference_of_differences (A D : ℝ)
    (hA : 0 < A) (hD : 0 < D) : ∃ C : ℝ, 0 < C ∧
    ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ≤ 1 → PotentialDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v,
        ‖-(I * e * (S₁.A u v - S₂.A u v) * jC1 (triangle 0 T) S₂ u v)‖ₑ) ≤
        ENNReal.ofReal (C * sigma e M T * (dataDist h₁ h₂ T +
          (jDist T S₁ S₂).toReal + ε * (geomDist T S₁ S₂).toReal)) := by
  refine ⟨2 * A * D, mul_pos (mul_pos (by norm_num) hA) hD, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ _hset₁ hset₂ hε hpot
  have hε0 : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans
    (hset₂.box.2 (0, 0) ⟨le_rfl, le_rfl, hset₂.pos.le⟩).2.2.2.2.2.1
  have hT0 : 0 ≤ T := hset₂.pos.le
  have hM : 1 ≤ M := hset₂.box.1
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hδ : 0 ≤ dataDist h₁ h₂ T :=
    add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  let F := M * (jDist T S₁ S₂).toReal + ε * dataDist h₁ h₂ T +
    M * ε * (geomDist T S₁ S₂).toReal
  let X := dataDist h₁ h₂ T + (jDist T S₁ S₂).toReal +
    ε * (geomDist T S₁ S₂).toReal
  have hF0 : 0 ≤ F := by dsimp [F]; positivity
  have hX0 : 0 ≤ X := by dsimp [X]; positivity
  have hFM : F ≤ M * X := by
    dsimp [F, X]
    calc
      _ ≤ M * (jDist T S₁ S₂).toReal + M * dataDist h₁ h₂ T +
          M * ε * (geomDist T S₁ S₂).toReal := by
        gcongr
        exact hε.trans hM
      _ = _ := by ring
  have hF : F * ε ≤ M ^ 2 * X := by
    calc
      F * ε ≤ (M * X) * M := by gcongr; exact hε.trans hM
      _ = _ := by ring
  let B := D * |e| * (T / 2) * F
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have harea := phase_area_le_of_bound hset₂ hpot.bound
  have henv : (∫⁻ v in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S₂) v) ≤
      ENNReal.ofReal (A * ε) :=
    (le_add_right le_rfl).trans hset₂.env
  calc
    _ ≤ ENNReal.ofReal (T * |e| * B) * ENNReal.ofReal (A * ε) :=
      harea.trans (mul_le_mul' le_rfl henv)
    _ = ENNReal.ofReal ((T * |e| * B) * (A * ε)) := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ T * |e| * B)]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ = (2 * A * D * (e ^ 2 * (T / 2) ^ 2)) * (F * ε) := by
          dsimp [B]
          rw [← sq_abs e]
          ring
        _ ≤ (2 * A * D * (e ^ 2 * (T / 2) ^ 2)) * (M ^ 2 * X) := by
          exact mul_le_mul_of_nonneg_left hF (by positivity)
        _ = _ := by dsimp [sigma, X]; ring

end EmcsfAcExtension.Local.Stab
