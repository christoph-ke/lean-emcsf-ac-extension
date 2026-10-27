module

public import EmcsfAcExtension.Global.Exterior.VariationTransport
public import EmcsfAcExtension.Infra.Level.OrderIso

/-! # The canonical capped exit for a local moving boundary

The compact-interval boundary isomorphism supplies the actual exit map.
Its constant endpoint extension stops every surviving label at the last row,
without assuming a global boundary isomorphism. Source:
`charged_SF_new_version.tex:L1337–L1340`, approved internal project record support-moving-interval.
-/

public section

open Set MeasureTheory Filter Topology

namespace EmcsfAcExtension.Global.Exterior

/-- [internal] The inverse of the boundary on its actual image, extended
constantly at both endpoints. Above the last boundary label this is the
stopping time `b`, hence the inverse is already capped. -/
@[expose] noncomputable def variationBoundaryExit {a b : ℝ} {V : ℝ → ℝ}
    (hab : a ≤ b) (hV : ContinuousOn V (Icc a b)) (hs : StrictMonoOn V (Icc a b)) :
    ℝ → ℝ :=
  Level.intervalInverse (Level.intervalOrderIso hab hV hs)
    (hs.monotoneOn ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)

/-- [internal] The canonical capped exit is continuous on all labels. -/
theorem continuous_variationBoundaryExit {a b : ℝ} {V : ℝ → ℝ}
    (hab : a ≤ b) (hV : ContinuousOn V (Icc a b)) (hs : StrictMonoOn V (Icc a b)) :
    Continuous (variationBoundaryExit hab hV hs) :=
  Level.continuous_intervalInverse _ _

/-- [internal] Every canonical exit is an existing incoming time. -/
theorem variationBoundaryExit_mem {a b : ℝ} {V : ℝ → ℝ}
    (hab : a ≤ b) (hV : ContinuousOn V (Icc a b)) (hs : StrictMonoOn V (Icc a b))
    (v : ℝ) : variationBoundaryExit hab hV hs v ∈ Icc a b :=
  Level.intervalInverse_mem _ _ _

/-- [internal] The canonical exit recovers every boundary time, including
both endpoints. -/
theorem variationBoundaryExit_apply_boundary {a b u : ℝ} {V : ℝ → ℝ}
    (hab : a ≤ b) (hV : ContinuousOn V (Icc a b)) (hs : StrictMonoOn V (Icc a b))
    (hu : u ∈ Icc a b) : variationBoundaryExit hab hV hs (V u) = u := by
  unfold variationBoundaryExit
  simpa only [Level.intervalOrderIso_apply] using
    Level.intervalInverse_apply_apply (Level.intervalOrderIso hab hV hs)
      (hs.monotoneOn ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab) ⟨u, hu⟩

/-- [internal] The actual active-label/exit equivalence. It holds for all
initial labels, including labels that survive beyond the last boundary
label; there is no inverse-image restriction on those labels. -/
theorem le_variationBoundaryExit_iff {a b u v : ℝ} {V : ℝ → ℝ}
    (hab : a ≤ b) (hV : ContinuousOn V (Icc a b)) (hs : StrictMonoOn V (Icc a b))
    (hu : u ∈ Icc a b) (hv : V a ≤ v) :
    u ≤ variationBoundaryExit hab hV hs v ↔ V u ≤ v := by
  let E := Level.intervalOrderIso hab hV hs
  have hVab : V a ≤ V b := hs.monotoneOn ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  let q : Icc (V a) (V b) := projIcc (V a) (V b) hVab v
  have hi := E.le_symm_apply (x := ⟨u, hu⟩) (y := q)
  change u ≤ (E.symm q : ℝ) ↔ (E ⟨u, hu⟩ : ℝ) ≤ (q : ℝ) at hi
  change u ≤ (E.symm q : ℝ) ↔ V u ≤ v
  rw [hi]
  have hEu : (E ⟨u, hu⟩ : ℝ) = V u := Level.intervalOrderIso_apply hab hV hs _
  rw [hEu]
  change V u ≤ max (V a) (min (V b) v) ↔ V u ≤ v
  rw [max_eq_right (le_min hVab hv), le_min_iff]
  have hub : V u ≤ V b := hs.monotoneOn hu ⟨hab, le_rfl⟩ hu.2
  simp only [hub, true_and]

/-- [internal] Every initial label's canonical stopped history ends on the
exact swept domain. All histories remain in that domain by incoming past
invariance. -/
theorem variationBoundaryExit_mem_swept {a b v : ℝ} {V : ℝ → ℝ}
    (hab : a ≤ b) (hV : ContinuousOn V (Icc a b)) (hs : StrictMonoOn V (Icc a b))
    (hv : v ∈ Icc (V a) 0) :
    (variationBoundaryExit hab hV hs v, v) ∈ variationSweptDomain a b V := by
  have ht := variationBoundaryExit_mem hab hV hs v
  exact ⟨ht, (le_variationBoundaryExit_iff hab hV hs ht hv.1).1 le_rfl, hv.2⟩

/-- [internal] The geometric hypotheses of the stopped-history argument
are all discharged by the canonical local inverse. In particular no global
boundary isomorphism and no separately chosen measurable inverse is needed. -/
theorem exists_variation_swept_exit {a b : ℝ} {V : ℝ → ℝ}
    (hab : a ≤ b) (hV : ContinuousOn V (Icc a b)) (hs : StrictMonoOn V (Icc a b)) :
    ∃ τ : ℝ → ℝ, Continuous τ ∧
      (∀ v, τ v ∈ Icc a b) ∧
      (∀ u ∈ Icc a b, τ (V u) = u) ∧
      (∀ u ∈ Icc a b, ∀ v, V a ≤ v → (u ≤ τ v ↔ V u ≤ v)) ∧
      (∀ v ∈ Icc (V a) 0, (τ v, v) ∈ variationSweptDomain a b V) := by
  refine ⟨variationBoundaryExit hab hV hs, continuous_variationBoundaryExit hab hV hs,
    variationBoundaryExit_mem hab hV hs, ?_, ?_, ?_⟩
  · exact fun u hu => variationBoundaryExit_apply_boundary hab hV hs hu
  · exact fun u hu v hv => le_variationBoundaryExit_iff hab hV hs hu hv
  · exact fun v hv => variationBoundaryExit_mem_swept hab hV hs hv

end EmcsfAcExtension.Global.Exterior
