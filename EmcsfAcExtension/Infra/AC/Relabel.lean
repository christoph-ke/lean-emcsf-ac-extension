module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Order.Interval.Set.Disjoint

/-!
# Increasing changes of interval labels

Monotone surjections preserve total variation. Absolute continuity pulls back along
an absolutely continuous monotone label; in particular a Lipschitz increasing label
suffices. The inverse formulation uses explicit inverse identities on the intervals.

Applications include `charged_SF_new_version.tex:L3954–L4161`, `L4376–L4379`, and `L6586–L6591`.
-/

public section

open Set Filter Function
open scoped Topology ENNReal NNReal

/-- A monotone label whose image is the target interval preserves variation exactly. -/
theorem eVariationOn.comp_Icc_eq_of_monotoneOn
    {E : Type*} [TopologicalSpace E] [WeakPseudoEMetricSpace E]
    (f : ℝ → E) {φ : ℝ → ℝ} {a b c d : ℝ}
    (hφ : MonotoneOn φ (Icc a b)) (himage : φ '' Icc a b = Icc c d) :
    eVariationOn (f ∘ φ) (Icc a b) = eVariationOn f (Icc c d) := by
  rw [eVariationOn.comp_eq_of_monotoneOn f φ hφ, himage]

namespace AbsolutelyContinuousOnInterval

private theorem map_disjWithin {φ : ℝ → ℝ} {a b : ℝ}
    (hφ : MonotoneOn φ (uIcc a b)) {n : ℕ} {I : ℕ → ℝ × ℝ}
    (hI : (n, I) ∈ disjWithin a b) :
    (n, fun i => (φ (I i).1, φ (I i).2)) ∈ disjWithin (φ a) (φ b) := by
  constructor
  · intro i hi
    exact ⟨hφ.image_uIcc_subset ⟨_, (hI.1 i hi).1, rfl⟩,
      hφ.image_uIcc_subset ⟨_, (hI.1 i hi).2, rfl⟩⟩
  · intro i hi j hj hij
    have hi' := hI.1 i hi
    have hj' := hI.1 j hj
    have hd := hI.2 hi hj hij
    simp only [uIoc, Ioc_disjoint_Ioc] at hd ⊢
    rw [← hφ.map_max hi'.1 hi'.2, ← hφ.map_max hj'.1 hj'.2,
      ← hφ.map_min hi'.1 hi'.2, ← hφ.map_min hj'.1 hj'.2,
      ← hφ.map_min (by grind [mem_uIcc]) (by grind [mem_uIcc]),
      ← hφ.map_max (by grind [mem_uIcc]) (by grind [mem_uIcc])]
    exact hφ (by grind [mem_uIcc]) (by grind [mem_uIcc]) hd

/-- Absolute continuity pulls back along an absolutely continuous monotone label. -/
theorem comp_monotoneOn {E : Type*} [PseudoMetricSpace E]
    {f : ℝ → E} {φ : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f (φ a) (φ b))
    (hφ : AbsolutelyContinuousOnInterval φ a b) (hm : MonotoneOn φ (uIcc a b)) :
    AbsolutelyContinuousOnInterval (f ∘ φ) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf hφ ⊢
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := hf ε hε
  obtain ⟨η, hη, hφη⟩ := hφ δ hδ
  refine ⟨η, hη, ?_⟩
  rintro ⟨n, I⟩ hI hlen
  exact hfδ (n, fun i => (φ (I i).1, φ (I i).2))
    (map_disjWithin hm hI) (hφη (n, I) hI hlen)

/-- The target interval can contain the image of the monotone AC label. -/
theorem comp_monotoneOn_mapsTo {E : Type*} [PseudoMetricSpace E]
    {f : ℝ → E} {φ : ℝ → ℝ} {a b c d : ℝ}
    (hf : AbsolutelyContinuousOnInterval f c d)
    (hφ : AbsolutelyContinuousOnInterval φ a b) (hm : MonotoneOn φ (uIcc a b))
    (hmap : MapsTo φ (uIcc a b) (uIcc c d)) :
    AbsolutelyContinuousOnInterval (f ∘ φ) a b :=
  (hf.mono (uIcc_subset_uIcc (hmap left_mem_uIcc) (hmap right_mem_uIcc))).comp_monotoneOn
    hφ hm

end AbsolutelyContinuousOnInterval
