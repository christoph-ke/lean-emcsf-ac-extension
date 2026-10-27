module

public import EmcsfAcExtension.Local.Defs.Limit
public import EmcsfAcExtension.Local.Assembly.Bundles
public import EmcsfAcExtension.Frozen.IsSolution

/-! # Explicit Limit-layer inputs for the Root B assembly

These internal propositions record the internal project record/§1.3 producer contracts.
The later sealed provider must discharge both inputs with Limit-layer theorems.
-/

public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [internal] Limit-layer producer packet LI-* (`Local.ac_data_existence`).
Contracts: `restart-sec-independent-null-construction#ac-data-existence` and
`restart-sec-independent-null-construction#limit-characteristic-bounds`.
The positive thresholds and bound constant are universal, independent of `T, e, h, S`.
This proposition records an input contract and closes no graph node. -/
@[expose] def AcDataExistenceStmt : Prop :=
  ∃ ε₃ δ₃ C₃ : ℝ, 0 < ε₃ ∧ 0 < δ₃ ∧ 0 < C₃ ∧
    ∀ (T e : ℝ) (h : ℝ → ℂ), 0 < T → AbsolutelyContinuousOnInterval h 0 T →
      datumVar h T ≤ ε₃ → |e| * (T / 2) * (1 + ‖h 0‖ + 10 * datumVar h T) ≤ δ₃ →
      ∃ S : Fields, IsSolution e S (triangle 0 T) ∧ IsRestartData S h T ∧
        IsConstructedLimit e T h S ∧ ExistenceBounds C₃ e T h S

/-- [internal] Limit-layer producer packet LI-* (`Local.limit_class_stability`).
Contracts: `restart-sec-independent-null-construction#limit-class-stability-uniqueness`,
`restart-sec-independent-null-construction#limit-characteristic-variation-difference`, and
`restart-charged-local-BV#quantitative-characteristic-W11`.
The positive thresholds and Lipschitz constant are universal, independent of
`T, e, h₁, h₂, S₁, S₂` and their approximation families.
This proposition records an input contract and closes no graph node. -/
@[expose] def LimitClassStabilityStmt : Prop :=
  ∃ ε₄ δ₄ C₄ : ℝ, 0 < ε₄ ∧ 0 < δ₄ ∧ 0 < C₄ ∧
    ∀ (T e : ℝ) (h₁ h₂ : ℝ → ℂ) (S₁ S₂ : Fields), 0 < T →
      AbsolutelyContinuousOnInterval h₁ 0 T → datumVar h₁ T ≤ ε₄ →
      |e| * (T / 2) * (1 + ‖h₁ 0‖ + 10 * datumVar h₁ T) ≤ δ₄ →
      AbsolutelyContinuousOnInterval h₂ 0 T → datumVar h₂ T ≤ ε₄ →
      |e| * (T / 2) * (1 + ‖h₂ 0‖ + 10 * datumVar h₂ T) ≤ δ₄ →
      IsConstructedLimit e T h₁ S₁ → IsConstructedLimit e T h₂ S₂ →
      StabConclusion C₄ e T h₁ h₂ S₁ S₂

end EmcsfAcExtension.Local
