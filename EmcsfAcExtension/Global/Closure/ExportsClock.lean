module

public import EmcsfAcExtension.Global.Defs.Stages
import EmcsfAcExtension.Global.Closure.Clock
import EmcsfAcExtension.Global.Closure.StageSums
import EmcsfAcExtension.Infra.Sequence.GeometricClock
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Separate prescribed cylinder and connector clock exports

The finite cylinder bound passes to the full nonnegative series. Connector
losses telescope and sum exactly to the initial radius. These are numerical
conclusions about the prescribed schedule, before proving stage existence.
Source: `charged_SF_new_version.tex:L4074–L4079`; internal project record.
-/

public section

namespace EmcsfAcExtension.Global.Closure

/-- [node sec:charged-closure#total-boundary-clock]
The separate finite and infinite prescribed cylinder bounds and exact
connector sums. The fixed coefficients `H,ρ,χ,C` precede the entry energy,
radius and arbitrary variation sequence; there is no stage-existence input.
The cylinder coefficient is exactly `H / (ε₀ * (1 - ρ / χ))`, and the
connector coefficient is exactly one, uniformly over every finite prefix.
Source: charged_SF_new_version.tex:L4074–L4079. -/
theorem total_boundary_clock_complete (H ρ χ C : ℝ)
    (hH : 0 ≤ H) (hρ : 0 < ρ ∧ ρ < χ) (hχ : χ < 1) (hC : 0 ≤ C) :
    ∀ (ε₀ b₀ : ℝ) (σ : ℕ → ℝ), 0 < ε₀ → 0 < b₀ →
      (∀ N : ℕ, (∑ n ∈ Finset.range N, stageDuration H ρ b₀ χ C ε₀ σ n) ≤
        H * b₀ / (ε₀ * (1 - ρ / χ))) ∧
      Summable (fun n => stageDuration H ρ b₀ χ C ε₀ σ n) ∧
      (∑' n, stageDuration H ρ b₀ χ C ε₀ σ n) ≤
        H * b₀ / (ε₀ * (1 - ρ / χ)) ∧
      (∀ N : ℕ, (∑ n ∈ Finset.range N,
        (stageRadius ρ b₀ n - stageRadius ρ b₀ (n + 1))) =
          b₀ - stageRadius ρ b₀ N) ∧
      HasSum (fun n => stageRadius ρ b₀ n - stageRadius ρ b₀ (n + 1)) b₀ ∧
      (∑' n, (stageRadius ρ b₀ n - stageRadius ρ b₀ (n + 1))) = b₀ := by
  intro ε₀ b₀ σ he hb
  have hfinite := total_prescribed_clock H ρ χ C ε₀ b₀ σ hH hρ hχ hC he hb
  have hnonneg (n : ℕ) : 0 ≤ stageDuration H ρ b₀ χ C ε₀ σ n :=
    div_nonneg (mul_nonneg hH (mul_nonneg (pow_nonneg hρ.1.le n) hb.le))
      (energyEnvelope_pos (hρ.1.trans hρ.2) hC he σ n).le
  have hconnector : HasSum
      (fun n => stageRadius ρ b₀ n - stageRadius ρ b₀ (n + 1)) b₀ :=
    hasSum_connector_clock hρ.1.le (hρ.2.trans hχ) b₀
  exact ⟨hfinite, summable_of_sum_range_le hnonneg hfinite,
    Real.tsum_le_of_sum_range_le hnonneg hfinite,
    connector_radius_sum ρ b₀, hconnector, hconnector.tsum_eq⟩

end EmcsfAcExtension.Global.Closure
