/- Copyright (c) 2026. All rights reserved. -/

module

public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Small-set concentration defects

The defect at `charged_SF_new_version.tex:L4946–L4947` is the decreasing-small-set limit of
an extended-real modulus. All constants and bounds below are independent of the
index of the family. The definitions also apply to signed and vector-valued functions.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace EmcsfAcExtension

variable {α ι β : Type*} [MeasurableSpace α] [NormedAddCommGroup β]

/-- Largest integral of the norm on a set of measure at most `η`, over the whole family.
No measurability or finiteness is needed to define this extended-real quantity. -/
@[expose] noncomputable def smallSetModulus (f : ι → α → β) (μ : Measure α)
    (η : ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (i : ι) (s : Set α) (_ : μ s ≤ η), ∫⁻ x in s, ‖f i x‖ₑ ∂μ

/-- The concentration defect, with the scale tending to zero through positive values. -/
@[expose] noncomputable def concentrationDefect (f : ι → α → β) (μ : Measure α) : ℝ≥0∞ :=
  ⨅ η > 0, smallSetModulus f μ η

/-- Every positive scale bounds the concentration defect. -/
theorem concentrationDefect_le (f : ι → α → β) (μ : Measure α)
    {η : ℝ≥0∞} (hη : 0 < η) :
    concentrationDefect f μ ≤ smallSetModulus f μ η :=
  iInf_le_of_le η (iInf_le_of_le hη le_rfl)

/-- For measurable families, zero concentration defect is exactly Mathlib's
`UnifIntegrable` at exponent one. No uniform bound on total norms is needed here. -/
theorem concentrationDefect_eq_zero_iff {f : ι → α → β} {μ : Measure α}
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) :
    concentrationDefect f μ = 0 ↔ UnifIntegrable f 1 μ := by
  have heq (i : ι) (s : Set α) :
      eLpNorm (f i) 1 (μ.restrict s) = ∫⁻ x in s, ‖f i x‖ₑ ∂μ :=
    eLpNorm_one_eq_lintegral_enorm (hf i).restrict
  rw [unifIntegrable_iff]
  constructor
  · intro h ε hε
    have hlt : (⨅ η > 0, smallSetModulus f μ η) < ε := by
      rw [← concentrationDefect, h]
      exact hε
    obtain ⟨δ, hδ⟩ := iInf_lt_iff.mp hlt
    obtain ⟨hδ0, hδε⟩ := iInf_lt_iff.mp hδ
    refine ⟨δ, hδ0, fun i s hs => ?_⟩
    rw [heq]
    apply le_trans (b := smallSetModulus f μ δ) _ hδε.le
    exact le_iSup_of_le i (le_iSup_of_le s (le_iSup_of_le hs le_rfl))
  · intro h
    apply le_antisymm _ zero_le
    apply le_of_forall_gt
    intro ε hε
    obtain ⟨ε', hε'0, hε'ε⟩ := exists_between hε
    obtain ⟨δ, hδ, hbound⟩ := h ε' hε'0
    apply lt_of_le_of_lt _ hε'ε
    refine (concentrationDefect_le f μ hδ).trans ?_
    exact iSup_le fun i => iSup_le fun s => iSup_le fun hs => by
      rw [← heq]
      exact hbound i s hs

end EmcsfAcExtension
