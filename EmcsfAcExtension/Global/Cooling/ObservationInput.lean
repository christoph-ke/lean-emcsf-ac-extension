/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Global.Defs.Curves
public import EmcsfAcExtension.Global.Defs.Observation
public import EmcsfAcExtension.Global.Defs.Original

/-! # The remaining observation interface

Literal internal project record observation result, retained under its original name
and signature for discharge by the observation packets. Source: L1710–L1748.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.Cooling

/-- [internal] Literal internal project record observation interface at a fixed gap.
Its witnesses precede all physical data. The triangle is the approved
complete inward comparison region (internal project record). -/
@[expose] def observationInput (δ : ℝ) : Prop :=
  ∃ Tstar Cstar δstar ηstar : ℝ,
    0 < Tstar ∧ 0 < Cstar ∧ 0 < δstar ∧ 0 < ηstar ∧
    ∀ (ui e b τ₀ : ℝ) (S : Fields), 0 < b → OriginalData ui e S →
    ∀ γ : ClockCylinder S (origDomain ui) b (τ₀ - Tstar * b) (τ₀ + Tstar * b),
    triangle (γ.U (τ₀ - Tstar * b)) (γ.V (τ₀ + Tstar * b)) ⊆ origDomain ui →
    (∀ p ∈ triangle (γ.U (τ₀ - Tstar * b)) (γ.V (τ₀ + Tstar * b)),
      0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) →
    AbsolutelyContinuousOnInterval
      (curveParallel e S S.a γ.U γ.V (τ₀ - Tstar * b))
        (τ₀ - Tstar * b) (τ₀ + Tstar * b) →
    (∀ τ ∈ Icc (τ₀ - Tstar * b) (τ₀ + Tstar * b),
      S.mu (γ.U τ) (γ.V τ) +
        ‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ ≤ δstar) →
    |e| * b * (1 + ‖S.a (γ.U τ₀) (γ.V τ₀)‖) ≤ ηstar →
    ENNReal.ofReal (b * (‖S.theta (γ.U τ₀) (γ.V τ₀) /
      (S.lam (γ.U τ₀) (γ.V τ₀) : ℂ)‖ ^ 2 + S.mu (γ.U τ₀) (γ.V τ₀) ^ 2)) ≤
    ENNReal.ofReal Cstar *
      (ENNReal.ofReal (cylinderDissipation S γ.U γ.V
        (τ₀ - Tstar * b) (τ₀ + Tstar * b)) + ENNReal.ofReal b *
        (curveCovVar e S S.a γ.U γ.V (τ₀ - Tstar * b) (τ₀ + Tstar * b)) ^ 2)

end EmcsfAcExtension.Global.Cooling
