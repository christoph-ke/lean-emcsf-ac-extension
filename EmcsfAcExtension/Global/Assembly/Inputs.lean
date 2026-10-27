module

public import EmcsfAcExtension.Global.Defs.Stages
public import EmcsfAcExtension.Global.Defs.Original

/-! # Explicit upstream obligations for conditional Root A assembly

These are precisely the unfinished construction inputs of internal project record's
`Restart.complete_cone_smallness_of_closure`, not a continuation or a
conclusion of the charged theorem. The finite records include connectors.
Source: charged_SF_new_version.tex:L3841–4168; approved internal project record; internal project
record handoff,
remaining upstream obligations 1–7. internal project record adds no premise beyond the
continuation conclusion, so no final-estimate assumption occurs here.
-/

public section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global

/-- [internal]
The remaining shrinking-construction obligations. For each fixed development
and signed terminal bound, the constants `c,F,A,C,εmax` and functions `D,M`
may depend on that development and are chosen before the energy tolerance,
entry row and stage family. For each fixed tolerance, one common family of
finite paths, budgets, amplitudes, closed interaction bounds and radial row inequalities
exists at every sufficiently late entry row. No cone or root conclusion
is assumed. These obligations must be discharged before sealing Root A.
-/
@[expose] def ClosureObligations : Prop :=
  ∀ (ui e : ℝ) (S : Fields), OriginalData ui e S → SignedTerminalBound ui S →
    ∃ c F A : ℝ, 0 < c ∧ F ^ 2 < 1 ∧ 0 < A ∧
    ∃ C εmax : ℝ, ∃ D M : ℝ → ℝ,
      1 ≤ C ∧ 0 < εmax ∧ Tendsto D (𝓝[<] 0) (𝓝 0) ∧
      (∀ u, M u = C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) ∧
      (∀ ε₀ ∈ Ioc 0 εmax, ∀ᶠ u₀ in 𝓝[<] (0 : ℝ),
        ∃ v₀ ρ b₀ K : ℝ, ∃ U : ℕ → ℝ, ∃ vb : ℝ → ℝ,
        ∃ B : ∀ N, FiniteBoundary S ui u₀ (U N) v₀ ρ vb N,
        ∃ E J : ℕ → ℝ,
          (0 ≤ ρ ∧ ρ < 1) ∧ Monotone U ∧ (∀ N i, (B N).cuts i = U i) ∧
          (∀ n, S.r u₀ 0 / 2 ≤ S.r (U n) 0) ∧
          (∀ n, S.r (U n) (vb (U n)) = stageRadius ρ b₀ n) ∧
          (∀ N, BoundaryBudgets S ui u₀ (U N) v₀ ρ vb N (B N) (fun i => E i)) ∧
          (∀ N, ∑ n ∈ Finset.range N, E n ≤ K) ∧
          (∀ n, ‖S.phi (U n) (vb (U n))‖ ≤ M u₀) ∧
          (∀ n, J n ≤ A * (D u₀ + ε₀ + e ^ 2 * M u₀ ^ 2 * S.r u₀ 0 ^ 2)) ∧
          (∀ n, (1 - F ^ 2) *
            (eVariationOn (S.a (U n)) (Icc (vb (U n)) 0)).toReal ≤ c⁻¹ * J n +
              F ^ 2 * ‖S.theta (U n) (vb (U n)) /
                (S.lam (U n) (vb (U n)) : ℂ)‖))

end EmcsfAcExtension.Global
