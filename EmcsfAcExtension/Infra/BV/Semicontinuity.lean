module

public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Order.LiminfLimsup

/-!
# Variation bounds under pointwise limits

Pointwise convergence is required only on the set on which variation is measured.
The filter formulation includes sequences and nets. A nontrivial filter is needed
only when passing a uniform bound to the limit.

Applications include `charged_SF_new_version.tex:L4128–L4134`, `L4941–L4943`, and `L6448–L6459`.
-/

public section

open Set Filter
open scoped Topology ENNReal

variable {α ι E : Type*} [LinearOrder α] [PseudoEMetricSpace E]
  {F : ι → α → E} {f : α → E} {s : Set α} {p : Filter ι}

/-- Variation is lower semicontinuous under pointwise convergence on its domain. -/
theorem eVariationOn.le_liminf_of_tendsto
    (hF : ∀ x ∈ s, Tendsto (fun i => F i x) p (𝓝 (f x))) :
    eVariationOn f s ≤ liminf (fun i => eVariationOn (F i) s) p := by
  apply (le_liminf_iff).2
  intro v hv
  exact eVariationOn.lowerSemicontinuous_aux hF hv

/-- An eventual uniform variation bound passes to a pointwise limit. -/
theorem eVariationOn.le_of_tendsto_of_eventually_le [NeBot p] {C : ℝ≥0∞}
    (hF : ∀ x ∈ s, Tendsto (fun i => F i x) p (𝓝 (f x)))
    (hC : ∀ᶠ i in p, eVariationOn (F i) s ≤ C) :
    eVariationOn f s ≤ C :=
  (eVariationOn.le_liminf_of_tendsto hF).trans
    (liminf_le_of_frequently_le' hC.frequently)

