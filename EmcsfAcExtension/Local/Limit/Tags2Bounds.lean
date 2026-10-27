module

public import EmcsfAcExtension.Local.Assembly.Inputs
import EmcsfAcExtension.Local.Construction.WireC1Bound
import EmcsfAcExtension.Local.Stability.ExtendedLipschitz
import EmcsfAcExtension.Local.Limit.Existence

/-! # Quantitative bounds for the same constructed AC solution

The producer contracts are discharged. Each component of the frozen bound
package refers to the same fixed-label limit, with the original numerical
background and universal constants. charged_SF_new_version.tex:L4421–4436, L6488–6502.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [internal]
All pointwise, covariant and ordinary scalar, and both geometric variation
bounds for one constructed limit. The three positive constants are universal,
before time, coupling, datum and smooth derivative size. The output retains
the exact numerical background `1 + ‖h 0‖ + 10 * datumVar h T`.
`ExistenceBounds` contains every displayed clause of these three records. -/
theorem constructed_limit_quantitative_bounds : AcDataExistenceStmt :=
  ac_data_existence_of_inputs whole_triangle_existence stab_extended

/-- [node restart-sec-independent-null-construction#limit-pointwise-bounds]
The four pointwise estimates for the same constructed limit with the literal
frozen background. All three positive constants are universal, before time,
coupling, datum and smooth approximation derivative size. -/
theorem limit_pointwise_bounds :
    ∃ ε δ C : ℝ, 0 < ε ∧ 0 < δ ∧ 0 < C ∧
      ∀ (T e : ℝ) (h : ℝ → ℂ), 0 < T → AbsolutelyContinuousOnInterval h 0 T →
        datumVar h T ≤ ε → chargedScale e h T ≤ δ →
        ∃ S : Fields, IsSolution e S (triangle 0 T) ∧ IsRestartData S h T ∧
          IsConstructedLimit e T h S ∧
          ∀ p ∈ triangle 0 T,
            ‖S.phi p.1 p.2‖ ≤ datumM h T ∧
            ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ + ‖S.xi p.1 p.2 / S.nu p.1 p.2‖ ≤
              C * datumVar h T ∧
            |S.lam p.1 p.2 - 1/2| + |S.nu p.1 p.2 + 1/2| + S.mu p.1 p.2 ≤
              C * datumVar h T ^ 2 ∧
            |S.Q p.1 p.2| ≤ C * |e| * datumM h T * datumVar h T * S.r p.1 p.2 ^ 2 := by
  obtain ⟨ε,δ,C,hε,hδ,hC,hex⟩ := constructed_limit_quantitative_bounds
  refine ⟨ε,δ,C,hε,hδ,hC,?_⟩
  intro T e h hT hac hd he
  obtain ⟨S,hS,hr,hc,hb⟩ := hex T e h hT hac hd he
  exact ⟨S,hS,hr,hc,hb.2.2.2.2.1⟩

/-- [node restart-sec-independent-null-construction#limit-scalar-variation-bounds]
Retain the sum of outgoing and covariant incoming variation budgets and the
ordinary incoming variation bound for the same constructed limit. Positive
thresholds and coefficient are universal, before time, coupling and datum,
independent of every smooth initial derivative supremum. -/
theorem limit_scalar_variation_bounds :
    ∃ ε δ C : ℝ, 0 < ε ∧ 0 < δ ∧ 0 < C ∧
      ∀ (T e : ℝ) (h : ℝ → ℂ), 0 < T → AbsolutelyContinuousOnInterval h 0 T →
        datumVar h T ≤ ε → chargedScale e h T ≤ δ →
        ∃ S : Fields, IsSolution e S (triangle 0 T) ∧ IsRestartData S h T ∧
          IsConstructedLimit e T h S ∧
          (⨆ u ∈ Icc 0 T, eVariationOn (S.a u) (Icc u T)) +
            (⨆ v ∈ Icc 0 T, covVarIn e S.A S.b 0 v v) ≤ ENNReal.ofReal (C * datumVar h T) ∧
          (⨆ v ∈ Icc 0 T, eVariationOn (fun u => S.b u v) (Icc 0 v)) ≤
            ENNReal.ofReal (C * datumVar h T) := by
  obtain ⟨ε,δ,C,hε,hδ,hC,hex⟩ := constructed_limit_quantitative_bounds
  refine ⟨ε,δ,C,hε,hδ,hC,?_⟩
  intro T e h hT hac hd he
  obtain ⟨S,hS,hr,hc,_,_,_,hs,_,_,_,_,_,_,ho⟩ := hex T e h hT hac hd he
  exact ⟨S,hS,hr,hc,hs,ho⟩

/-- [node restart-sec-independent-null-construction#limit-geometric-variation-bounds]
Every geometric characteristic variation in either direction for the same
constructed limit. The positive thresholds and coefficient are universal,
before time, coupling, datum and every smooth initial derivative supremum. -/
theorem limit_geometric_variation_bounds :
    ∃ ε δ C : ℝ, 0 < ε ∧ 0 < δ ∧ 0 < C ∧
      ∀ (T e : ℝ) (h : ℝ → ℂ), 0 < T → AbsolutelyContinuousOnInterval h 0 T →
        datumVar h T ≤ ε → chargedScale e h T ≤ δ →
        ∃ S : Fields, IsSolution e S (triangle 0 T) ∧ IsRestartData S h T ∧
          IsConstructedLimit e T h S ∧
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
              ENNReal.ofReal (C * datumVar h T ^ 2)) := by
  obtain ⟨ε,δ,C,hε,hδ,hC,hex⟩ := constructed_limit_quantitative_bounds
  refine ⟨ε,δ,C,hε,hδ,hC,?_⟩
  intro T e h hT hac hd he
  obtain ⟨S,hS,hr,hc,_,_,_,_,_,hgo,hgi,_⟩ := hex T e h hT hac hd he
  exact ⟨S,hS,hr,hc,hgo,hgi⟩

end EmcsfAcExtension.Local
