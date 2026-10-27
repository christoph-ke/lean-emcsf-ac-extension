module

public import EmcsfAcExtension.Local.Assembly.Inputs
import EmcsfAcExtension.Local.Assembly.Main
import EmcsfAcExtension.Local.Construction.WireC1Bound
import EmcsfAcExtension.Local.Stability.ExtendedLipschitz
import EmcsfAcExtension.Local.Limit.Existence
import EmcsfAcExtension.Local.Limit.Stability

/-! # Unconditional assembly of the frozen Root B statement

Whole-triangle C¹ existence and full classical stability discharge the
Limit-layer contracts. The audited assembly supplies broad uniqueness,
quantitative stability and all bounds with universal constants.
-/

public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [node restart-charged-local-BV]
The exact frozen Root B conclusion from the unconditional construction and
stability producers and their AC limits. The positive thresholds and bound
constant are universal, before time, coupling, data and solutions.
The constant synthesis and broad competitor identification are those of
`restart_local_main_of_limit`. -/
theorem restart_local_main :
    ∃ ε₀ δ₀ C : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧ 0 < C ∧
    ∀ T e : ℝ, 0 < T →
    -- existence on the closed triangle, bounds, and uniqueness in the broad class
    (∀ h : ℝ → ℂ, AbsolutelyContinuousOnInterval h 0 T →
      datumVar h T ≤ ε₀ → |e| * (T / 2) * (1 + ‖h 0‖ + 10 * datumVar h T) ≤ δ₀ →
      ∃ S : Fields,
        IsSolution e S (triangle 0 T) ∧
        (∀ v ∈ Icc 0 T, S.r 0 v = v / 2 ∧ S.a 0 v = h v) ∧
        (∀ t ∈ Icc 0 T, S.A t t = 0) ∧
        (∀ u ∈ Icc 0 T, AbsolutelyContinuousOnInterval (S.a u) u T) ∧
        (∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun u => S.b u v) 0 v) ∧
        AbsolutelyContinuousOnInterval (fun t => S.phi t t) 0 T ∧
        (⨆ u ∈ Icc 0 T, eVariationOn (S.a u) (Icc u T)) +
            (⨆ v ∈ Icc 0 T, covVarIn e S.A S.b 0 v v) ≤
          ENNReal.ofReal (C * datumVar h T) ∧
        (∀ p ∈ triangle 0 T,
          ‖S.phi p.1 p.2‖ ≤ 1 + ‖h 0‖ + 10 * datumVar h T ∧
          ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ + ‖S.xi p.1 p.2 / S.nu p.1 p.2‖ ≤
            C * datumVar h T ∧
          |S.lam p.1 p.2 - 1 / 2| + |S.nu p.1 p.2 + 1 / 2| + S.mu p.1 p.2 ≤
            C * datumVar h T ^ 2 ∧
          |S.Q p.1 p.2| ≤
            C * |e| * (1 + ‖h 0‖ + 10 * datumVar h T) * datumVar h T * S.r p.1 p.2 ^ 2) ∧
        (∀ u ∈ Icc 0 T,
          eVariationOn (S.lam u) (Icc u T) ≤ ENNReal.ofReal (C * datumVar h T ^ 2) ∧
          eVariationOn (S.nu u) (Icc u T) ≤ ENNReal.ofReal (C * datumVar h T ^ 2) ∧
          eVariationOn (S.mu u) (Icc u T) ≤ ENNReal.ofReal (C * datumVar h T ^ 2) ∧
          eVariationOn (S.Omega2 u) (Icc u T) ≤ ENNReal.ofReal (C * datumVar h T ^ 2)) ∧
        (∀ v ∈ Icc 0 T,
          eVariationOn (fun u => S.lam u v) (Icc 0 v) ≤ ENNReal.ofReal (C * datumVar h T ^ 2) ∧
          eVariationOn (fun u => S.nu u v) (Icc 0 v) ≤ ENNReal.ofReal (C * datumVar h T ^ 2) ∧
          eVariationOn (fun u => S.mu u v) (Icc 0 v) ≤ ENNReal.ofReal (C * datumVar h T ^ 2) ∧
          eVariationOn (fun u => S.Omega2 u v) (Icc 0 v) ≤
            ENNReal.ofReal (C * datumVar h T ^ 2)) ∧
        (∀ u ∈ Icc 0 T,
          AbsolutelyContinuousOnInterval (S.lam u) u T ∧
          AbsolutelyContinuousOnInterval (S.nu u) u T ∧
          AbsolutelyContinuousOnInterval (S.mu u) u T ∧
          AbsolutelyContinuousOnInterval (S.Omega2 u) u T) ∧
        (∀ v ∈ Icc 0 T,
          AbsolutelyContinuousOnInterval (fun u => S.lam u v) 0 v ∧
          AbsolutelyContinuousOnInterval (fun u => S.nu u v) 0 v ∧
          AbsolutelyContinuousOnInterval (fun u => S.mu u v) 0 v ∧
          AbsolutelyContinuousOnInterval (fun u => S.Omega2 u v) 0 v) ∧
        ContDiffOn ℝ 1 (Function.uncurry S.r) (triangle 0 T) ∧
        (⨆ v ∈ Icc 0 T, eVariationOn (fun u => S.b u v) (Icc 0 v)) ≤
          ENNReal.ofReal (C * datumVar h T) ∧
        (∀ T' ∈ Ioc 0 T, ∀ S' : Fields, IsSolution e S' (triangle 0 T') →
          (∀ v ∈ Icc 0 T', S'.r 0 v = v / 2 ∧ S'.a 0 v = h v) →
          (∀ t ∈ Icc 0 T', S'.A t t = 0) → S'.EqOn S (triangle 0 T'))) ∧
    -- Lipschitz stability in `W^{1,1}` of the datum, fixed gauge
    (∀ (h₁ h₂ : ℝ → ℂ) (S₁ S₂ : Fields),
      AbsolutelyContinuousOnInterval h₁ 0 T → datumVar h₁ T ≤ ε₀ →
      |e| * (T / 2) * (1 + ‖h₁ 0‖ + 10 * datumVar h₁ T) ≤ δ₀ →
      AbsolutelyContinuousOnInterval h₂ 0 T → datumVar h₂ T ≤ ε₀ →
      |e| * (T / 2) * (1 + ‖h₂ 0‖ + 10 * datumVar h₂ T) ≤ δ₀ →
      IsSolution e S₁ (triangle 0 T) → (∀ v ∈ Icc 0 T, S₁.r 0 v = v / 2 ∧ S₁.a 0 v = h₁ v) →
      (∀ t ∈ Icc 0 T, S₁.A t t = 0) →
      IsSolution e S₂ (triangle 0 T) → (∀ v ∈ Icc 0 T, S₂.r 0 v = v / 2 ∧ S₂.a 0 v = h₂ v) →
      (∀ t ∈ Icc 0 T, S₂.A t t = 0) →
      (∃ J K : ℝ → ℝ, IntegrableOn J (Icc 0 T) ∧ IntegrableOn K (Icc 0 T) ∧
        (∀ u ∈ Icc 0 T, ∀ᵐ v ∂(volume.restrict (Icc u T)),
          ‖jOut S₁ u v - jOut S₂ u v‖ ≤ J v) ∧
        (∀ v ∈ Icc 0 T, ∀ᵐ u ∂(volume.restrict (Icc 0 v)),
          ‖kIn e S₁ u v - kIn e S₂ u v‖ ≤ K u) ∧
        ∀ p₁ ∈ triangle 0 T, ∀ p₂ ∈ triangle 0 T, ∀ p₃ ∈ triangle 0 T, ∀ p₄ ∈ triangle 0 T,
          (∫ v in (0 : ℝ)..T, J v) + (∫ u in (0 : ℝ)..T, K u) +
            (|S₁.lam p₁.1 p₁.2 - S₂.lam p₁.1 p₁.2| + |S₁.nu p₁.1 p₁.2 - S₂.nu p₁.1 p₁.2| +
              |S₁.r p₁.1 p₁.2 - S₂.r p₁.1 p₁.2| / S₁.r p₁.1 p₁.2) +
            ‖S₁.a p₂.1 p₂.2 - S₂.a p₂.1 p₂.2‖ + ‖S₁.b p₃.1 p₃.2 - S₂.b p₃.1 p₃.2‖ +
            ‖S₁.phi p₄.1 p₄.2 - S₂.phi p₄.1 p₄.2‖ ≤
          C * (‖h₁ 0 - h₂ 0‖ + datumVar (h₁ - h₂) T)) ∧
      (⨆ u ∈ Icc 0 T, eVariationOn (fun v => S₁.a u v - S₂.a u v) (Icc u T)) +
          (⨆ v ∈ Icc 0 T, eVariationOn (fun u => S₁.b u v - S₂.b u v) (Icc 0 v)) ≤
        ENNReal.ofReal (C * (‖h₁ 0 - h₂ 0‖ + datumVar (h₁ - h₂) T))) := by
  have hW : WholeTriangleExistenceStmt := whole_triangle_existence
  have hS : StabExtendedStmt := stab_extended
  exact restart_local_main_of_limit
    (ac_data_existence_of_inputs hW hS) (limit_class_stability_of_inputs hS)

end EmcsfAcExtension.Local
