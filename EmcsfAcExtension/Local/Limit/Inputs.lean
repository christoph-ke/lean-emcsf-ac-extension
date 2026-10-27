module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Defs.Bounds

/-! # Pending producer interfaces for the Limit layer

These are internal propositions under internal project record. They record
the exact producer contracts from internal project record, with the C¹ construction
class required by internal project record and the background argument of internal project record.
Defining an interface does not supply its proof.
-/

@[expose] public section

open Set Complex

namespace EmcsfAcExtension.Local

/-- Pending internal project record contract: full-triangle classical existence for C¹ data.
Both positive thresholds are universal, before time, coupling and datum.
This is internal project record with the regularity of internal project record. -/
def WholeTriangleExistenceStmt : Prop :=
  ∃ ε₃ δ₃ : ℝ, 0 < ε₃ ∧ 0 < δ₃ ∧
    ∀ (T e : ℝ) (h : ℝ → ℂ), 0 < T → ContDiffOn ℝ 1 h (Icc 0 T) →
      datumVar h T ≤ ε₃ → chargedScale e h T ≤ δ₃ →
      ∃ S : Fields, IsC1Solution e S (triangle 0 T) ∧ IsRestartData S h T

/-- Pending internal project record contract: the full classical comparison record.
The threshold and constant depend only on the envelope coefficient `A`;
they precede every triangle, coupling, size parameter, datum and pair.
Every clause of `StabBounds`, including the internal project record clauses, is required. -/
def StabExtendedStmt : Prop :=
  ∀ A : ℝ, 0 < A → ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
    ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ^ 2 + sigma e M T ≤ η →
      StabBounds C e T M (dataDist h₁ h₂ T) S₁ S₂

end EmcsfAcExtension.Local
