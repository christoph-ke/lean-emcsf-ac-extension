module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeomStrongInitial
import EmcsfAcExtension.Local.Stability.ExtendedNonconcentration
import EmcsfAcExtension.Local.Stability.W11FluxLocal

/-! # Complete initial-geometric and quadratic-flux exports

These conjunctions retain every conclusion of the node records at
charged_SF_new_version.tex:L5425–5428 and charged_SF_new_version.tex:L5594–5600: the initial
identities accompany the L¹ comparison, and the quantitative localized
flux budgets accompany uniform nonconcentration.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [node restart-sec-bv-stability-independent#initial-geometric-renormalized-difference]
Both initial renormalizations equal their quadratic corrections on the
entire closed initial cone, including both endpoints, and their L¹
difference is at most `CεΔ₀`, charged_SF_new_version.tex:L5425–5428. The universal
constant has witness `2` and precedes all parameters, fields and data;
no smallness, coupling or derivative-supremum dependence is needed. -/
theorem Stab.initial_geometric_renormalized_difference_complete :
    ∃ C : ℝ, 0 < C ∧ ∀ (T e ε M A : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      (∀ v ∈ Icc 0 T,
        geomL (triangle 0 T) S₁ 0 v =
          S₁.lam 0 v / S₁.r 0 v * ‖S₁.theta 0 v / (S₁.lam 0 v : ℂ)‖ ^ 2 ∧
        geomL (triangle 0 T) S₂ 0 v =
          S₂.lam 0 v / S₂.r 0 v * ‖S₂.theta 0 v / (S₂.lam 0 v : ℂ)‖ ^ 2) ∧
      (∫⁻ v in Icc 0 T, ‖geomL (triangle 0 T) S₁ 0 v -
        geomL (triangle 0 T) S₂ 0 v‖ₑ) ≤
          ENNReal.ofReal (C * ε * dataDist h₁ h₂ T) := by
  obtain ⟨C, hC, hbound⟩ := Stab.initial_geometric_renormalized_difference
  refine ⟨C, hC, ?_⟩
  intro T e ε M A S₁ S₂ h₁ h₂ hset₁ hset₂
  exact ⟨fun v hv => ⟨stab_initial_geomL hset₁ hv, stab_initial_geomL hset₂ hv⟩,
    hbound T e ε M A S₁ S₂ h₁ h₂ hset₁ hset₂⟩

/-- [node restart-sec-bv-stability-independent#quadratic-flux-nonconcentration]
The local outgoing and incoming quadratic fluxes are bounded by their
matching envelope integrals with the universal coefficient `16/3`,
charged_SF_new_version.tex:L5594–5600. The positive threshold depends only on `A`
and the fixed box, before all remaining parameters, fields and data.
For every positive tolerance one positive width controls the entire
sequence and both orientations. Neither bound depends on a minimum
radius or on a supremum of initial derivatives. -/
theorem Stab.quadratic_flux_nonconcentration_complete (A : ℝ) (hA : 0 < A) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (T e ε M : ℝ) (Sn : ℕ → Fields) (hn : ℕ → ℝ → ℂ),
        (∀ n, StabSetting e T ε M A (Sn n) (hn n)) →
        ε ^ 2 + sigma e M T ≤ η →
        (∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, dataDist (hn n) (hn m) T < δ) →
        (∀ n u v, 0 ≤ u → u ≤ v → v ≤ T →
          ((∫⁻ s in Icc u v, ENNReal.ofReal
            ((Sn n).lam u s / (Sn n).r u s *
              ‖(Sn n).theta u s / ((Sn n).lam u s : ℂ)‖ ^ 2)) ≤
            ENNReal.ofReal ((16 / 3) * ε) *
              ∫⁻ s in Icc u v, outEnv 0 (jC1 (triangle 0 T) (Sn n)) s) ∧
          ((∫⁻ s in Icc u v, ENNReal.ofReal
            (-(Sn n).nu s v / (Sn n).r s v *
              ‖(Sn n).xi s v / ((Sn n).nu s v : ℂ)‖ ^ 2)) ≤
            ENNReal.ofReal ((16 / 3) * ε) *
              ∫⁻ s in Icc u v, inEnv T (kC1 e (triangle 0 T) (Sn n)) s)) ∧
        (∀ δ > (0 : ℝ), ∃ d : ℝ, 0 < d ∧
          ∀ n u v, 0 ≤ u → u ≤ v → v ≤ T → v - u ≤ d →
            (∫⁻ s in Icc u v, ENNReal.ofReal
              ((Sn n).lam u s / (Sn n).r u s *
                ‖(Sn n).theta u s / ((Sn n).lam u s : ℂ)‖ ^ 2)) +
            (∫⁻ s in Icc u v, ENNReal.ofReal
              (-(Sn n).nu s v / (Sn n).r s v *
                ‖(Sn n).xi s v / ((Sn n).nu s v : ℂ)‖ ^ 2)) ≤ ENNReal.ofReal δ) := by
  obtain ⟨η₀, hη₀, hnonconcentration⟩ := Stab.quadratic_flux_nonconcentration A hA
  refine ⟨min η₀ (1 / 4), lt_min hη₀ (by norm_num), ?_⟩
  intro T e ε M Sn hn hset hsmall hdata
  have hσ0 : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hεsq : ε ^ 2 ≤ 1 / 4 := by
    linarith only [hsmall.trans (min_le_right _ _), hσ0]
  exact ⟨fun n u v hu huv hvT =>
    ⟨Stab.quadratic_flux_out_local_c1 (hset n) hεsq hu huv hvT,
      Stab.quadratic_flux_in_local_c1 (hset n) hεsq hu huv hvT⟩,
    hnonconcentration T e ε M Sn hn hset
      (hsmall.trans (min_le_left _ _)) hdata⟩

end EmcsfAcExtension.Local
