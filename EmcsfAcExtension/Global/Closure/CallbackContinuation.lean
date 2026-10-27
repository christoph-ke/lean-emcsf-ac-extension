module

public import EmcsfAcExtension.Global.Closure.Callback
import Mathlib.Tactic

/-! # Applying the callback to an actual available finite path

Transfer the literal entry stop to the finite graph, apply finite stopping
continuation, and identify the final clipped sum with full variations.
Source: `charged_SF_new_version.tex:L4104–L4106`.
-/

public section

open Set

namespace EmcsfAcExtension.Global.Closure

/-- [internal]
The strict singleton entry data transfer to every available boundary with
the same entry label. Its actual incoming norm is the initial density and
its clipped variation is zero. Constants: none. -/
theorem strict_entry_of_initial {ui e a b v₀ ρ R₀ δ c Λ F ε εstop : ℝ} {S : Fields}
    (h : OriginalData ui e S) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui a b v₀ ρ vb N) (T : Fin N → ℝ)
    (γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n))
    (hentry : StrictFiniteCutoffStops S ui a R₀ (fun _ => v₀)
      (fun _ => (initialInteraction S a v₀).toReal) (fun _ => 0)
      δ c Λ F ε εstop a) :
    StrictFiniteCutoffStops S ui a R₀ vb
      (fun t => (interactionNorm e S (exteriorDomain ui a t vb) a v₀).toReal)
      (fun t => ∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0
        (max 0 (min (T n) (cylinderClock S vb (B.cuts n.castSucc) t)))).toReal)
      δ c Λ F ε εstop a := by
  have heq : EqOn vb (fun _ => v₀) (Icc a a) := by
    intro u hu
    have hua : u = a := le_antisymm hu.2 hu.1
    simpa only [hua] using B.entry_label
  have hdom := exteriorDomain_congr_boundary (ui := ui) heq
  simpa only [StrictFiniteCutoffStops, hdom, interactionNorm_initial_cutoff,
    clipped_variation_initial h B T γ] using hentry

/-- [internal]
Apply a discharged literal cutoff callback to the actual finite stopping
continuation, retaining the full final stops in the form used by completed
prefixes. The helper's callback is discharged by
`actual_cutoff_callback_of_small_entry`. Constants: none are selected here. -/
theorem strict_full_path_of_callback {ui e a b v₀ ρ R₀ δ c Λ F ε εstop : ℝ} {S : Fields}
    (h : OriginalData ui e S) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui a b v₀ ρ vb N) (T : Fin N → ℝ) (hT : ∀ n, 0 ≤ T n)
    (γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n))
    (hends : ∀ n, (γ n).U 0 = B.cuts n.castSucc ∧ (γ n).U (T n) = B.cool n)
    (hgraph : ∀ n, ∀ s ∈ Icc 0 (T n), vb ((γ n).U s) = (γ n).V s)
    (hfixed : ∀ p ∈ exteriorDomain ui a b vb,
      0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2 ∧ S.lam p.1 p.2 ≤ Λ ∧
        S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 ≤ S.mu p.1 p.2 / 2)
    (hentry : StrictFiniteCutoffStops S ui a R₀ (fun _ => v₀)
      (fun _ => (initialInteraction S a v₀).toReal) (fun _ => 0)
      δ c Λ F ε εstop a)
    (hcallback :
      let J := fun t => (interactionNorm e S (exteriorDomain ui a t vb) a v₀).toReal
      let V := fun t => ∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0
        (max 0 (min (T n) (cylinderClock S vb (B.cuts n.castSucc) t)))).toReal
      ∀ t ∈ Icc a b, FiniteCutoffStops S ui a R₀ vb J V δ c Λ F ε εstop t →
        StrictFiniteCutoffStops S ui a R₀ vb J V δ c Λ F ε εstop t) :
    StrictFiniteCutoffStops S ui a R₀ vb
      (fun _ => (interactionNorm e S (exteriorDomain ui a b vb) a v₀).toReal)
      (fun _ => ∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal)
      δ c Λ F ε εstop b := by
  have hab : a ≤ b := by
    simpa only [B.first, B.last] using B.ordered (Fin.zero_le (Fin.last N))
  have hall := actual_finite_stopping_continuation_of_estimates h B T hT γ hends hgraph
    δ c Λ F ε εstop hfixed (strict_entry_of_initial h B T γ hentry) hcallback
  simpa only [StrictFiniteCutoffStops, clipped_variation_final h B T hT γ hends hgraph] using
    hall b ⟨hab, le_rfl⟩

end EmcsfAcExtension.Global.Closure
