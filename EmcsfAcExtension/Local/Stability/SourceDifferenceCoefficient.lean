module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity
import EmcsfAcExtension.Local.Api.Finite

/-! # Multiplication of flux differences by the opposite derivative envelope

This module consumes the incoming quadratic-flux conclusion from internal project record.
The integration order agrees with the j transport in charged_SF_new_version.tex:L5345–5345.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- Incoming quadratic-flux difference consumed from internal project record (QFi).
The input constant is fixed before the data and the pair. -/
structure IncomingFluxDifference (C e T ε M Δ₀ : ℝ) (S₁ S₂ : Fields) : Prop where
  /-- Absolute coefficient difference on each complete incoming section. -/
  bound : ∀ v ∈ Icc 0 T,
    (∫⁻ u in Icc 0 v, ENNReal.ofReal
      |(-S₁.nu u v / S₁.r u v * ‖S₁.xi u v / (S₁.nu u v : ℂ)‖ ^ 2) -
        (-S₂.nu u v / S₂.r u v * ‖S₂.xi u v / (S₂.nu u v : ℂ)‖ ^ 2)|) ≤
      ENNReal.ofReal (C * (ε * (kDist e T S₁ S₂).toReal +
        ε ^ 2 * (geomDist T S₁ S₂).toReal + sigma e M T * ε ^ 2 / M *
          ((jDist T S₁ S₂).toReal + ε * (geomDist T S₁ S₂).toReal + ε * Δ₀ / M)))

/-- [internal]
 Multiplying the incoming flux-difference bound by `j₂` costs its outgoing
label norm. The numerical multiplier is exactly `1`; the input constant is
unchanged and is fixed before the data and the pair. -/
theorem homogeneous_coefficient_area_of_differences {C e T ε M A Δ₀ : ℝ}
    {S₁ S₂ : Fields} {h₂ : ℝ → ℂ} (hset₂ : StabSetting e T ε M A S₂ h₂)
    (hflux : IncomingFluxDifference C e T ε M Δ₀ S₁ S₂) :
    (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v,
      ‖(((-S₁.nu u v / S₁.r u v * ‖S₁.xi u v / (S₁.nu u v : ℂ)‖ ^ 2) -
          (-S₂.nu u v / S₂.r u v * ‖S₂.xi u v / (S₂.nu u v : ℂ)‖ ^ 2) : ℝ) : ℂ) *
        jC1 (triangle 0 T) S₂ u v‖ₑ) ≤
      ENNReal.ofReal (C * (ε * (kDist e T S₁ S₂).toReal +
        ε ^ 2 * (geomDist T S₁ S₂).toReal + sigma e M T * ε ^ 2 / M *
          ((jDist T S₁ S₂).toReal + ε * (geomDist T S₁ S₂).toReal + ε * Δ₀ / M))) *
        ∫⁻ v in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S₂) v := by
  let F := fun u v => ENNReal.ofReal
    |(-S₁.nu u v / S₁.r u v * ‖S₁.xi u v / (S₁.nu u v : ℂ)‖ ^ 2) -
      (-S₂.nu u v / S₂.r u v * ‖S₂.xi u v / (S₂.nu u v : ℂ)‖ ^ 2)|
  let B := ENNReal.ofReal (C * (ε * (kDist e T S₁ S₂).toReal +
    ε ^ 2 * (geomDist T S₁ S₂).toReal + sigma e M T * ε ^ 2 / M *
      ((jDist T S₁ S₂).toReal + ε * (geomDist T S₁ S₂).toReal + ε * Δ₀ / M)))
  calc
    _ ≤ ∫⁻ v in Icc 0 T, B * outEnv 0 (jC1 (triangle 0 T) S₂) v := by
      apply setLIntegral_mono' measurableSet_Icc
      intro v hv
      have hJfinite := outEnv_ne_top_of_continuousOn
        (continuousOn_jC1_aux hset₂.pos hset₂.c1) hv
      calc
        _ ≤ ∫⁻ u in Icc 0 v, F u v * outEnv 0 (jC1 (triangle 0 T) S₂) v := by
          apply setLIntegral_mono' measurableSet_Icc
          intro u hu
          rw [enorm_mul]
          apply mul_le_mul'
          · dsimp [F]
            rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
          · exact le_iSup₂_of_le u hu le_rfl
        _ = (∫⁻ u in Icc 0 v, F u v) * outEnv 0 (jC1 (triangle 0 T) S₂) v :=
          lintegral_mul_const' _ _ hJfinite
        _ ≤ _ := mul_le_mul' (hflux.bound v hv) le_rfl
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- [internal]
 Conditional helper for the homogeneous-coefficient-difference node,
charged_SF_new_version.tex:L5345–5345. `C` depends only on the independent envelope
constant `A` and the incoming flux estimate constant `D`; it is uniform
in the coupling, background, triangle, data, and derivative suprema. -/
theorem homogeneous_coefficient_difference_of_differences (A D : ℝ)
    (hA : 0 < A) (hD : 0 < D) : ∃ C : ℝ, 0 < C ∧
    ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ → ε ≤ 1 →
      IncomingFluxDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v,
        ‖(((-S₁.nu u v / S₁.r u v * ‖S₁.xi u v / (S₁.nu u v : ℂ)‖ ^ 2) -
            (-S₂.nu u v / S₂.r u v * ‖S₂.xi u v / (S₂.nu u v : ℂ)‖ ^ 2) : ℝ) : ℂ) *
          jC1 (triangle 0 T) S₂ u v‖ₑ) ≤
        ENNReal.ofReal
          (C * ε * (∫⁻ v in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S₂) v).toReal *
              (kDist e T S₁ S₂).toReal +
            C * ε ^ 2 * (∫⁻ v in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S₂) v).toReal *
              (geomDist T S₁ S₂).toReal +
            C * sigma e M T * (dataDist h₁ h₂ T + (jDist T S₁ S₂).toReal +
              (kDist e T S₁ S₂).toReal + ε * (geomDist T S₁ S₂).toReal)) := by
  let C := D * (A + 1)
  refine ⟨C, mul_pos hD (by linarith only [hA]), ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ _hset₁ hset₂ hε1 hflux
  have hε0 : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans
    (hset₂.box.2 (0, 0) ⟨le_rfl, le_rfl, hset₂.pos.le⟩).2.2.2.2.2.1
  have hM : 1 ≤ M := hset₂.box.1
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hδ : 0 ≤ dataDist h₁ h₂ T := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hσ : 0 ≤ sigma e M T := by unfold sigma; positivity
  let J := (jDist T S₁ S₂).toReal
  let K := (kDist e T S₁ S₂).toReal
  let G := (geomDist T S₁ S₂).toReal
  let δ := dataDist h₁ h₂ T
  let N := (∫⁻ v in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S₂) v).toReal
  let H := J + ε * G + ε * δ / M
  let X := δ + J + K + ε * G
  have hNenv : (∫⁻ v in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S₂) v) ≤
      ENNReal.ofReal (A * ε) := (le_add_right le_rfl).trans hset₂.env
  have hNfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hNenv
  have hN : N ≤ A * ε := by
    exact (ENNReal.toReal_le_toReal hNfin ENNReal.ofReal_ne_top).mpr hNenv |>.trans_eq
      (ENNReal.toReal_ofReal (mul_nonneg hA.le hε0))
  have hH0 : 0 ≤ H := by dsimp [H, J, G, δ]; positivity
  have hX0 : 0 ≤ X := by dsimp [X, J, K, G, δ]; positivity
  have hHd : ε * δ / M ≤ δ := by
    apply (div_le_iff₀ hM0).2
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hε1.trans hM) hδ
  have hHX : H ≤ X := by
    have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
    dsimp only [H, X]
    linarith only [hHd, hK0]
  have hε3 : ε ^ 3 ≤ 1 := pow_le_one₀ hε0 hε1
  have hres : ε ^ 2 * H * N ≤ A * X := by
    calc
      _ ≤ ε ^ 2 * H * (A * ε) := by gcongr
      _ = A * (ε ^ 3 * H) := by ring
      _ ≤ A * (1 * X) := by gcongr
      _ = _ := by ring
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hDC : D ≤ C := by
    dsimp [C]
    have := mul_nonneg hD.le hA.le
    nlinarith only [this]
  have hDAC : D * A ≤ C := by
    dsimp [C]
    linarith only [hD]
  have hF0 : 0 ≤ D * (ε * K + ε ^ 2 * G + sigma e M T * ε ^ 2 * H) := by
    dsimp [K, G]; positivity
  have harea := homogeneous_coefficient_area_of_differences hset₂ hflux
  have hflux_weak :
      D * (ε * K + ε ^ 2 * G + sigma e M T * ε ^ 2 / M * H) ≤
        D * (ε * K + ε ^ 2 * G + sigma e M T * ε ^ 2 * H) := by
    gcongr
    exact div_le_self (by positivity : 0 ≤ sigma e M T * ε ^ 2) hM
  have harea_weak := harea.trans
    (mul_le_mul' (ENNReal.ofReal_le_ofReal hflux_weak) le_rfl)
  calc
    _ ≤ ENNReal.ofReal (D * (ε * K + ε ^ 2 * G + sigma e M T * ε ^ 2 * H)) *
        ENNReal.ofReal N := by
      simpa only [N, ENNReal.ofReal_toReal hNfin] using harea_weak
    _ = ENNReal.ofReal ((D * (ε * K + ε ^ 2 * G + sigma e M T * ε ^ 2 * H)) * N) := by
      rw [ENNReal.ofReal_mul hF0]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ = D * ε * N * K + D * ε ^ 2 * N * G +
            D * sigma e M T * (ε ^ 2 * H * N) := by ring
        _ ≤ C * ε * N * K + C * ε ^ 2 * N * G +
            D * sigma e M T * (A * X) := by gcongr
        _ = C * ε * N * K + C * ε ^ 2 * N * G + D * A * sigma e M T * X := by ring
        _ ≤ C * ε * N * K + C * ε ^ 2 * N * G + C * sigma e M T * X := by gcongr

end EmcsfAcExtension.Local.Stab
