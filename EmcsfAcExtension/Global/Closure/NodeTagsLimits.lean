module

public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Stages
import EmcsfAcExtension.Global.Restart.AxisLimit
import EmcsfAcExtension.Global.Restart.ConeVariation

/-! # Limits on an infinite available shrinking boundary

These exports take the infinite construction stipulated by their source
records. They do not produce finite stages or prove that all stages exist.
Source: `charged_SF_new_version.tex:L4115–L4124`.
-/

public section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.Closure

/-- [node sec:charged-closure#proper-axis-limit]
An infinite shrinking boundary retaining a positive terminal radius has a
common proper axis limit. The infinite family and radius stop are exactly
the source setting. `Rmin` is any fixed positive retained radius; there are
no estimate constants. Source: charged_SF_new_version.tex:L4115–L4120. -/
theorem proper_axis_limit (ui e : ℝ) (S : Fields) (h : OriginalData ui e S)
    {u₀ v₀ ρ b₀ Rmin : ℝ} (hu₀ : u₀ ∈ Ioo ui 0)
    (hρ : 0 ≤ ρ ∧ ρ < 1) (hRmin : 0 < Rmin)
    (U : ℕ → ℝ) (vb : ℝ → ℝ)
    (B : ∀ N, FiniteBoundary S ui u₀ (U N) v₀ ρ vb N)
    (hU : Monotone U)
    (hstart : u₀ ≤ U 0)
    (hR : ∀ n, Rmin ≤ S.r (U n) 0)
    (hrad : ∀ n, S.r (U n) (vb (U n)) = stageRadius ρ b₀ n) :
    ∃ us ∈ Ioo ui 0, Tendsto U atTop (𝓝 us) ∧
      Tendsto (fun n => vb (U n)) atTop (𝓝 us) := by
  exact Restart.proper_axis_limit_of_closure ui e S h hu₀ hρ hRmin U vb B hU hstart hR hrad

/-- [node sec:charged-closure#boundary-scalar-decay]
The recursive energies and variations vanish, and the scalar ratio tends
to zero along every choice of points in the successive entire pieces,
including connectors. The coefficients `χ,C₁` precede all sequences and
entry energies; `K,L` are uniform finite-sum bounds, independent of cutoff.
The budget and sum hypotheses are the established estimates of the source
infinite construction, not pointwise decay premises.
Source: charged_SF_new_version.tex:L4122–L4124. -/
theorem boundary_scalar_decay (χ C₁ : ℝ) (hχ : 0 ≤ χ ∧ χ < 1) (hC₁ : 0 ≤ C₁)
    (ui e : ℝ) (S : Fields) (h : OriginalData ui e S)
    {u₀ v₀ ρ K L ε₀ : ℝ} (he : 0 ≤ ε₀) (U : ℕ → ℝ) (vb : ℝ → ℝ)
    (B : ∀ N, FiniteBoundary S ui u₀ (U N) v₀ ρ vb N)
    (E σ : ℕ → ℝ) (hσ : ∀ n, 0 ≤ σ n)
    (hbudget : ∀ N, BoundaryBudgets S ui u₀ (U N) v₀ ρ vb N (B N) (fun i => E i))
    (hEsum : ∀ N, ∑ n ∈ Finset.range N, E n ≤ K)
    (hσsum : ∀ N, ∑ n ∈ Finset.range N, σ n ≤ L) :
    Tendsto (energyEnvelope χ C₁ ε₀ σ) atTop (𝓝 0) ∧ Tendsto σ atTop (𝓝 0) ∧
      ∀ w : ℕ → ℝ,
        (∀ n, w n ∈ Icc ((B (n + 1)).cuts ⟨n, by omega⟩)
          ((B (n + 1)).cuts ⟨n + 1, by omega⟩)) →
        Tendsto (fun n => S.theta (w n) (vb (w n)) /
          (S.lam (w n) (vb (w n)) : ℂ)) atTop (𝓝 0) := by
  have hen := Restart.energyEnvelope_decay_of_closure χ C₁ hχ hC₁ he σ hσ hσsum
  have hboundary := Restart.boundary_scalar_decay_of_closure ui e S h U vb B E σ hσ
    hbudget hEsum hσsum
  exact ⟨hen.1, hen.2, hboundary.2.2⟩

end EmcsfAcExtension.Global.Closure
