/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Locality on relatively open covers

internal project record infrastructure. The neighborhood formulation covers arbitrary relatively
open patches of triangles, trapezoids and rectangles, including boundary points.
-/

public section

namespace EmcsfAcExtension

open Set Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {D : Set (ℝ × ℝ)} {f : ℝ × ℝ → E} {n : ℕ∞ω}

/-- Relatively open patches of a unique-differentiation domain also have
unique derivatives, including where a patch meets the domain boundary. -/
theorem uniqueDiffOn_relative_patch {C : Set (ℝ × ℝ)}
    (hD : UniqueDiffOn ℝ D) (hsub : C ⊆ D) (hrel : ∀ p ∈ C, C ∈ 𝓝[D] p) :
    UniqueDiffOn ℝ C := by
  intro p hp
  exact (hD p (hsub hp)).mono_nhds
    (le_inf nhdsWithin_le_nhds (le_principal_iff.mpr (hrel p hp)))

/-- Cⁿ regularity glues over a cover by relative neighborhoods of each point.
The neighborhoods may meet the boundary of the domain. -/
theorem contDiffOn_of_relative_cover {ι : Type*} {C : ι → Set (ℝ × ℝ)}
    (hcover : ∀ p ∈ D, ∃ i, p ∈ C i ∧ C i ∈ 𝓝[D] p)
    (hf : ∀ i, ContDiffOn ℝ n f (C i)) : ContDiffOn ℝ n f D := by
  intro p hp
  obtain ⟨i, hpi, hi⟩ := hcover p hp
  exact (hf i p hpi).mono_of_mem_nhdsWithin hi

/-- On a relative neighborhood, the local and global derivatives coincide.
Uniqueness is needed only on the full domain. -/
theorem fderivWithin_eq_on_relative_patch {C : Set (ℝ × ℝ)}
    (hD : UniqueDiffOn ℝ D) {p : ℝ × ℝ} (hp : p ∈ D) (hC : C ∈ 𝓝[D] p)
    (hf : DifferentiableWithinAt ℝ f C p) :
    fderivWithin ℝ f C p = fderivWithin ℝ f D p :=
  (fderivWithin_of_mem_nhdsWithin hC (hD p hp) hf).symm

end EmcsfAcExtension
