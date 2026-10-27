module

public import EmcsfAcExtension.Global.Closure.NodeTagsImprovements

/-! # Canonical strict-improvement record names

The shared finite estimate produces budgets from initial stage energies and
retains all three strict improvements with the same parameter choice.
Source: `charged_SF_new_version.tex:L4061–L4072`.
-/

public section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace EmcsfAcExtension.Global

/-- [node sec:charged-closure#scalar-mass-improvement]
Strict scalar and mass improvements on every available
finite stopped prefix. Observation thresholds depend only on the gap; all
other constants and tolerances depend only on the fixed geometric,
recurrence and stopping parameters, before data, shrinking scales and
stage durations. Actual budgets are constructed from the propagated
initial energies. Source: charged_SF_new_version.tex:L4061–L4072. -/
theorem Closure.scalar_mass_improvement (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    ∃ Ts δs ηs : ℝ, 0 < Ts ∧ 0 < δs ∧ 0 < ηs ∧
      ∀ (εweak ρ χ C₁ c Λ F : ℝ),
      ExteriorBox δ c Λ F εweak ρ → 0 < ρ →
      0 ≤ χ → χ < 1 → 0 ≤ C₁ → F + εweak ≤ δs → 0 < F → 0 < εweak →
      ∃ Cbudget Csum C η : ℝ, 0 < Cbudget ∧ 0 < Csum ∧ 0 < C ∧ 0 < η ∧
      ∀ (ui e : ℝ) (S : Fields), OriginalData ui e S → SignedTerminalBound ui S →
      ∃ a ∈ Ioo ui 0,
      ∀ (u₀ u₁ v₀ R₀ εentry : ℝ) (vb : ℝ → ℝ) (σ : ℕ → ℝ)
        (N : ℕ) (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (T : Fin N → ℝ),
      a ≤ u₀ → 0 < N → 0 ≤ εentry → (∀ n, 0 ≤ σ n) →
      ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F εweak →
      S.r u₀ 0 = R₀ → (∀ u ∈ Icc u₀ u₁, R₀ / 2 ≤ S.r u 0) →
      (∀ p ∈ origDomain ui, u₀ ≤ p.1 → 0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) →
      (∀ n, B.radii n < R₀ / 2) → (∀ n, 0 < T n) →
      ∀ γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n),
      (∀ n, (γ n).U 0 = B.cuts n.castSucc ∧ (γ n).U (T n) = B.cool n) →
      (∀ n, ∀ τ ∈ Icc 0 (T n), vb ((γ n).U τ) = (γ n).V τ) →
      (∀ n : Fin N, σ n = (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal) →
      (∀ n, cylinderEnergy S (B.radii n) ((γ n).U 0) ((γ n).V 0) / B.radii n ≤
        energyEnvelope χ C₁ εentry σ n) →
      let J := (interactionNorm e S (exteriorDomain ui u₀ u₁ vb) u₀ v₀).toReal
      let V := ∑ n ∈ Finset.range N, σ n
      let z := Local.sigma e (Interaction.scalarBackground ui R₀ c F η S) (2 * R₀)
      J + V ≤ η → εentry ≤ η → z ≤ η →
      (⨆ v ∈ Icc v₀ 0, ∫⁻ u in {u | (u, v) ∈ exteriorDomain ui u₀ u₁ vb},
        ENNReal.ofReal (positiveExpIntegrand S u v)) ≤
          ENNReal.ofReal (C * (εentry + V ^ 2 + J ^ 2 + z)) ∧
      C * (εentry + V ^ 2 + J ^ 2 + z) < Real.log 2 ∧
      (∀ p ∈ exteriorDomain ui u₀ u₁ vb,
        ‖S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ)‖ < F ∧
        S.mu p.1 p.2 / (1 - S.mu p.1 p.2) < εweak) ∧
      ((∀ v ∈ Icc v₀ 0, 2 * c ≤ S.lam u₀ v) →
        (∀ p ∈ exteriorDomain ui u₀ u₁ vb,
          0 ≤ signedExpIntegrand S p.1 p.2 ∧
          signedExpIntegrand S p.1 p.2 ≤ positiveExpIntegrand S p.1 p.2 ∧
          c < S.lam p.1 p.2) ∧
        ∀ u ∈ Icc u₀ u₁, (-S.nu u 0) / (-S.nu u (vb u)) < 2) := by
  exact cc_optics δ hδ

/-- [node sec:charged-closure#expansion-clock-improvement]
Signed exponent bounds, strict expansion improvement and clock comparison on every available
finite stopped prefix. Observation thresholds depend only on the gap; all
other constants and tolerances depend only on the fixed geometric,
recurrence and stopping parameters, before data, shrinking scales and
stage durations. Actual budgets are constructed from the propagated
initial energies. Source: charged_SF_new_version.tex:L4061–L4072. -/
theorem Closure.expansion_clock_improvement (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    ∃ Ts δs ηs : ℝ, 0 < Ts ∧ 0 < δs ∧ 0 < ηs ∧
      ∀ (εweak ρ χ C₁ c Λ F : ℝ),
      ExteriorBox δ c Λ F εweak ρ → 0 < ρ →
      0 ≤ χ → χ < 1 → 0 ≤ C₁ → F + εweak ≤ δs → 0 < F → 0 < εweak →
      ∃ Cbudget Csum C η : ℝ, 0 < Cbudget ∧ 0 < Csum ∧ 0 < C ∧ 0 < η ∧
      ∀ (ui e : ℝ) (S : Fields), OriginalData ui e S → SignedTerminalBound ui S →
      ∃ a ∈ Ioo ui 0,
      ∀ (u₀ u₁ v₀ R₀ εentry : ℝ) (vb : ℝ → ℝ) (σ : ℕ → ℝ)
        (N : ℕ) (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (T : Fin N → ℝ),
      a ≤ u₀ → 0 < N → 0 ≤ εentry → (∀ n, 0 ≤ σ n) →
      ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F εweak →
      S.r u₀ 0 = R₀ → (∀ u ∈ Icc u₀ u₁, R₀ / 2 ≤ S.r u 0) →
      (∀ p ∈ origDomain ui, u₀ ≤ p.1 → 0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) →
      (∀ n, B.radii n < R₀ / 2) → (∀ n, 0 < T n) →
      ∀ γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n),
      (∀ n, (γ n).U 0 = B.cuts n.castSucc ∧ (γ n).U (T n) = B.cool n) →
      (∀ n, ∀ τ ∈ Icc 0 (T n), vb ((γ n).U τ) = (γ n).V τ) →
      (∀ n : Fin N, σ n = (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal) →
      (∀ n, cylinderEnergy S (B.radii n) ((γ n).U 0) ((γ n).V 0) / B.radii n ≤
        energyEnvelope χ C₁ εentry σ n) →
      let J := (interactionNorm e S (exteriorDomain ui u₀ u₁ vb) u₀ v₀).toReal
      let V := ∑ n ∈ Finset.range N, σ n
      let z := Local.sigma e (Interaction.scalarBackground ui R₀ c F η S) (2 * R₀)
      J + V ≤ η → εentry ≤ η → z ≤ η →
      (⨆ v ∈ Icc v₀ 0, ∫⁻ u in {u | (u, v) ∈ exteriorDomain ui u₀ u₁ vb},
        ENNReal.ofReal (positiveExpIntegrand S u v)) ≤
          ENNReal.ofReal (C * (εentry + V ^ 2 + J ^ 2 + z)) ∧
      C * (εentry + V ^ 2 + J ^ 2 + z) < Real.log 2 ∧
      (∀ p ∈ exteriorDomain ui u₀ u₁ vb,
        ‖S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ)‖ < F ∧
        S.mu p.1 p.2 / (1 - S.mu p.1 p.2) < εweak) ∧
      ((∀ v ∈ Icc v₀ 0, 2 * c ≤ S.lam u₀ v) →
        (∀ p ∈ exteriorDomain ui u₀ u₁ vb,
          0 ≤ signedExpIntegrand S p.1 p.2 ∧
          signedExpIntegrand S p.1 p.2 ≤ positiveExpIntegrand S p.1 p.2 ∧
          c < S.lam p.1 p.2) ∧
        ∀ u ∈ Icc u₀ u₁, (-S.nu u 0) / (-S.nu u (vb u)) < 2) := by
  exact cc_optics δ hδ

end EmcsfAcExtension.Global
