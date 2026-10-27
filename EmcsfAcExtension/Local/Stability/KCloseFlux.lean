module

public import EmcsfAcExtension.Local.Stability.JCloseCoefficient
import EmcsfAcExtension.Local.Api.Finite
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Outgoing flux-difference input for the k closure

Multiplication by the opposite derivative costs precisely its label
integral. The signed coefficient is the negative outgoing quadratic flux.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- Outgoing quadratic-flux difference conclusion consumed from internal project record.
`C` is fixed before all pair parameters. The negative flux is written in
its exactly equivalent literal k-coefficient form. -/
structure OutgoingFluxDifference (C T ε : ℝ) (S₁ S₂ : Fields) : Prop where
  /-- Absolute coefficient difference on every complete outgoing section. -/
  bound : ∀ u ∈ Icc 0 T,
    (∫⁻ v in Icc u T, ENNReal.ofReal |kRealCoefficient S₁ u v - kRealCoefficient S₂ u v|) ≤
      ENNReal.ofReal (C * (ε * (jDist T S₁ S₂).toReal + ε ^ 2 * (geomDist T S₁ S₂).toReal))

/-- [internal]
 Multiplication of the outgoing flux difference by `k₂` costs exactly
its incoming label norm. The coefficient one is universal; the input
constant `D` stays fixed before the pair. -/
theorem k_coefficient_area_of_differences {D e T ε M A : ℝ}
    {S₁ S₂ : Fields} {h₂ : ℝ → ℂ} (hs₂ : StabSetting e T ε M A S₂ h₂)
    (hflux : OutgoingFluxDifference D T ε S₁ S₂) :
    (∫⁻ u in Icc 0 T, ∫⁻ v in Icc u T,
      ‖((kRealCoefficient S₁ u v - kRealCoefficient S₂ u v : ℝ) : ℂ) *
        kC1 e (triangle 0 T) S₂ u v‖ₑ) ≤
      ENNReal.ofReal (D * (ε * (jDist T S₁ S₂).toReal + ε ^ 2 * (geomDist T S₁ S₂).toReal)) *
        ∫⁻ u in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S₂) u := by
  let F := fun u v => ENNReal.ofReal |kRealCoefficient S₁ u v - kRealCoefficient S₂ u v|
  let B := ENNReal.ofReal (D * (ε * (jDist T S₁ S₂).toReal + ε ^ 2 * (geomDist T S₁ S₂).toReal))
  calc
    _ ≤ ∫⁻ u in Icc 0 T, B * inEnv T (kC1 e (triangle 0 T) S₂) u := by
      apply setLIntegral_mono' measurableSet_Icc
      intro u hu
      have hKfinite := inEnv_ne_top_of_continuousOn (continuousOn_kC1_aux hs₂.pos hs₂.c1) hu
      calc
        _ ≤ ∫⁻ v in Icc u T, F u v * inEnv T (kC1 e (triangle 0 T) S₂) u := by
          apply setLIntegral_mono' measurableSet_Icc
          intro v hv
          rw [enorm_mul]
          apply mul_le_mul'
          · dsimp [F]
            rw [← ofReal_norm, norm_real, Real.norm_eq_abs]
          · exact le_iSup₂_of_le v hv le_rfl
        _ = (∫⁻ v in Icc u T, F u v) * inEnv T (kC1 e (triangle 0 T) S₂) u :=
          lintegral_mul_const' _ _ hKfinite
        _ ≤ _ := mul_le_mul' (hflux.bound u hu) le_rfl
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- [internal]
 The outgoing coefficient forcing has size `C(ε² Δ_j + ε³ G)`.
`C` depends only on the fixed envelope and outgoing flux constants `A,D`,
uniformly in all physical parameters, data and derivative suprema. -/
theorem k_homogeneous_coefficient_difference_of_differences (A D : ℝ) (hA : 0 < A) (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      OutgoingFluxDifference D T ε S₁ S₂ →
      (∫⁻ u in Icc 0 T, ∫⁻ v in Icc u T,
        ‖((kRealCoefficient S₁ u v - kRealCoefficient S₂ u v : ℝ) : ℂ) *
          kC1 e (triangle 0 T) S₂ u v‖ₑ) ≤
        ENNReal.ofReal (C * (ε ^ 2 * (jDist T S₁ S₂).toReal + ε ^ 3 * (geomDist T S₁ S₂).toReal)) :=
            by
  refine ⟨A * D, mul_pos hA hD, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ _hs₁ hs₂ hflux
  have hε : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans
    (hs₂.box.2 (0, 0) ⟨le_rfl, le_rfl, hs₂.pos.le⟩).2.2.2.2.2.1
  have hb := k_coefficient_area_of_differences hs₂ hflux
  have henv := (le_add_left le_rfl).trans hs₂.env
  apply (hb.trans (mul_le_mul' le_rfl henv)).trans_eq
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ D * (ε * (jDist T S₁ S₂).toReal +
    ε ^ 2 * (geomDist T S₁ S₂).toReal))]
  congr 1
  ring

end EmcsfAcExtension.Local.Stab
