module

public import EmcsfAcExtension.Global.Defs.Curves
public import EmcsfAcExtension.Global.Defs.Domains
public import EmcsfAcExtension.Global.Defs.Interaction
public import EmcsfAcExtension.Global.Defs.Observation
public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Stages
public import EmcsfAcExtension.Global.Interaction.WrappersProfiles
public import EmcsfAcExtension.Local.Defs.Params
import EmcsfAcExtension.Global.Closure.CallbackEnergy

/-! # Finite and partial stage budget node exports

The actual stopped-history energy induction supplies every starting energy
from the entry energy. Its budgets cover whole cylinder-and-connector
stages, including an unfinished last cylinder and short observation windows.
Source: `charged_SF_new_version.tex:L3919–L3932`.
-/

public section

open Set

namespace EmcsfAcExtension.Global.Closure

/-- [node sec:charged-closure#finite-stage-budgets]
Derive the literal cylinder-and-connector supremum and integrated budgets,
and both finite sums, from entry energy in the inherited stopped setting.
The thresholds depend only on δ; `H,C₁,Cbudget,Csum` may depend on
`δ,εweak,ρ,χ`, before all fields, coupling, radii, entry energy, variations,
stage counts and durations. The fixed connector factor is included in
`Cbudget`. No later starting energy or budget is assumed. The last cylinder
may be unfinished. Source: `charged_SF_new_version.tex:L3919–L3928`. -/
theorem finite_stage_budgets (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    ∃ δs ηs : ℝ, 0 < δs ∧ 0 < ηs ∧
      ∀ (εweak ρ χ : ℝ), 0 ≤ εweak → 0 < ρ → (0 < χ ∧ χ < 1) →
      ∃ H C₁ Cbudget Csum : ℝ,
        0 < H ∧ 0 < C₁ ∧ 0 < Cbudget ∧ 0 < Csum ∧
      ∀ (ui e a b v₀ R₀ c Λ F Jstop εentry : ℝ) (S : Fields)
        (vb : ℝ → ℝ) (σ : ℕ → ℝ) (N : ℕ)
        (B : FiniteBoundary S ui a b v₀ ρ vb N) (T : Fin N → ℝ),
      OriginalData ui e S → ExteriorBox δ c Λ F εweak ρ → 0 ≤ Jstop → 0 < εentry →
      F + εweak ≤ δs → ExteriorStops S (exteriorDomain ui a b vb) δ c Λ F εweak →
      S.r a 0 = R₀ → (∀ u ∈ Icc a b, R₀ / 2 ≤ S.r u 0) →
      (interactionNorm e S (exteriorDomain ui a b vb) a v₀).toReal ≤ Jstop →
      (∀ p ∈ origDomain ui, a ≤ p.1 → 0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) →
      (∀ n, B.radii n < R₀ / 2) → (∀ n, 0 ≤ T n) →
      (∀ n : Fin N, n.val + 1 < N →
        T n = H * B.radii n / energyEnvelope χ C₁ εentry σ n) →
      ∀ γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n),
      (∀ n, (γ n).U 0 = B.cuts n.castSucc ∧ (γ n).U (T n) = B.cool n) →
      (∀ n, ∀ τ ∈ Icc 0 (T n), vb ((γ n).U τ) = (γ n).V τ) →
      (∀ n : Fin N, σ n = (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal) →
      cylinderEnergy S (S.r a v₀) a v₀ / S.r a v₀ ≤ εentry →
      let z := Local.sigma e (Interaction.scalarBackground ui R₀ c F Jstop S) (2 * R₀)
      z ≤ 1 → 9 * z ≤ ηs ^ 2 →
      let E := fun n : Fin N => stageBudget Cbudget χ C₁ εentry σ n
      let V := ∑ n : Fin N, σ n
      BoundaryBudgets S ui a b v₀ ρ vb N B E ∧
        (∑ n, E n) ≤ Csum * (εentry + V ^ 2) ∧
        (∑ n, Real.sqrt (E n)) ≤ Csum * (Real.sqrt εentry + V) :=
  stopped_partial_budgets δ hδ

/-- [node sec:charged-closure#partial-stage-budgets]
The same physical budgets and finite sums hold for every unfinished last
cylinder, without a lower bound on its duration or a full-window premise.
All thresholds and coefficient dependencies are exactly those of
`finite_stage_budgets`: δ first, then `εweak,ρ,χ`, before fields, coupling,
shrinking scales, variations, stage counts and durations.
Source: `charged_SF_new_version.tex:L3930–L3932`. -/
theorem partial_stage_budgets (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    ∃ δs ηs : ℝ, 0 < δs ∧ 0 < ηs ∧
      ∀ (εweak ρ χ : ℝ), 0 ≤ εweak → 0 < ρ → (0 < χ ∧ χ < 1) →
      ∃ H C₁ Cbudget Csum : ℝ,
        0 < H ∧ 0 < C₁ ∧ 0 < Cbudget ∧ 0 < Csum ∧
      ∀ (ui e a b v₀ R₀ c Λ F Jstop εentry : ℝ) (S : Fields)
        (vb : ℝ → ℝ) (σ : ℕ → ℝ) (N : ℕ)
        (B : FiniteBoundary S ui a b v₀ ρ vb N) (T : Fin N → ℝ),
      OriginalData ui e S → ExteriorBox δ c Λ F εweak ρ → 0 ≤ Jstop → 0 < εentry →
      F + εweak ≤ δs → ExteriorStops S (exteriorDomain ui a b vb) δ c Λ F εweak →
      S.r a 0 = R₀ → (∀ u ∈ Icc a b, R₀ / 2 ≤ S.r u 0) →
      (interactionNorm e S (exteriorDomain ui a b vb) a v₀).toReal ≤ Jstop →
      (∀ p ∈ origDomain ui, a ≤ p.1 → 0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) →
      (∀ n, B.radii n < R₀ / 2) → (∀ n, 0 ≤ T n) →
      (∀ n : Fin N, n.val + 1 < N →
        T n = H * B.radii n / energyEnvelope χ C₁ εentry σ n) →
      ∀ γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n),
      (∀ n, (γ n).U 0 = B.cuts n.castSucc ∧ (γ n).U (T n) = B.cool n) →
      (∀ n, ∀ τ ∈ Icc 0 (T n), vb ((γ n).U τ) = (γ n).V τ) →
      (∀ n : Fin N, σ n = (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal) →
      cylinderEnergy S (S.r a v₀) a v₀ / S.r a v₀ ≤ εentry →
      let z := Local.sigma e (Interaction.scalarBackground ui R₀ c F Jstop S) (2 * R₀)
      z ≤ 1 → 9 * z ≤ ηs ^ 2 →
      let E := fun n : Fin N => stageBudget Cbudget χ C₁ εentry σ n
      let V := ∑ n : Fin N, σ n
      BoundaryBudgets S ui a b v₀ ρ vb N B E ∧
        (∑ n, E n) ≤ Csum * (εentry + V ^ 2) ∧
        (∑ n, Real.sqrt (E n)) ≤ Csum * (Real.sqrt εentry + V) :=
  finite_stage_budgets δ hδ

end EmcsfAcExtension.Global.Closure
