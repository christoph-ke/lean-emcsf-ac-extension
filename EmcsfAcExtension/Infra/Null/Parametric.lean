/- Copyright (c) 2026. All rights reserved. -/

module

public import EmcsfAcExtension.Infra.Null.Sections

/-! # Parametric integrals on the frozen triangle

A continuous retraction onto a nonempty triangle gives a continuous extension
without assumptions on the field outside the triangle. Integral continuity then
follows from Mathlib's continuous parametric primitive theorem.
-/

public section

open Set MeasureTheory Filter
open scoped Topology

namespace EmcsfAcExtension

/-- Clamp first to `[a,b]`, then clamp the second coordinate above the first. -/
@[expose] def triangleProj (a b : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (min (max a p.1) b, max (min (max a p.1) b) (min p.2 b))

/-- The explicit projection is continuous, including for unordered endpoints. -/
theorem continuous_triangleProj (a b : ℝ) : Continuous (triangleProj a b) := by
  unfold triangleProj
  fun_prop

/-- For ordered endpoints the projection takes every point into the triangle. -/
theorem triangleProj_mem {a b : ℝ} (hab : a ≤ b) (p : ℝ × ℝ) :
    triangleProj a b p ∈ triangle a b := by
  exact ⟨le_min (le_max_left _ _) hab, le_max_left _ _,
    max_le (min_le_right _ _) (min_le_right _ _)⟩

/-- The projection fixes all points of the triangle. -/
@[simp] theorem triangleProj_of_mem {a b : ℝ} {p : ℝ × ℝ} (hp : p ∈ triangle a b) :
    triangleProj a b p = p := by
  rcases p with ⟨u, v⟩
  change (min (max a u) b, max (min (max a u) b) (min v b)) = (u, v)
  rw [max_eq_right hp.1, min_eq_left (hp.2.1.trans hp.2.2), min_eq_left hp.2.2,
    max_eq_right hp.2.1]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : ℝ → ℝ → E} {a b : ℝ}

omit [NormedSpace ℝ E] in
/-- A continuous field on the triangle extends continuously by projection. -/
theorem continuous_comp_triangleProj (hab : a ≤ b)
    (hF : ContinuousOn (Function.uncurry F) (triangle a b)) :
    Continuous (fun p => Function.uncurry F (triangleProj a b p)) :=
  hF.comp_continuous (continuous_triangleProj a b) (triangleProj_mem hab)

/-- Outgoing primitives depend jointly continuously on both characteristic coordinates. -/
theorem continuousOn_integral_outgoing
    (hF : ContinuousOn (Function.uncurry F) (triangle a b)) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ s in p.1..p.2, F p.1 s) (triangle a b) := by
  by_cases hab : a ≤ b
  · let G : ℝ → ℝ → E := fun u s => Function.uncurry F (triangleProj a b (u, s))
    have hG : Continuous (Function.uncurry G) := continuous_comp_triangleProj hab hF
    have hupper : Continuous (fun p : ℝ × ℝ => ∫ s in a..p.2, G p.1 s) :=
      intervalIntegral.continuous_parametric_primitive_of_continuous hG
    have hlower : Continuous (fun p : ℝ × ℝ => ∫ s in a..p.1, G p.1 s) :=
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hG
        continuous_id).comp continuous_fst
    apply (hupper.sub hlower).continuousOn.congr
    intro p hp
    dsimp only [Pi.sub_apply]
    symm
    have hi : ∀ c d, IntervalIntegrable (G p.1) volume c d :=
      (hG.comp (continuous_const.prodMk continuous_id)).intervalIntegrable
    rw [intervalIntegral.integral_interval_sub_left (hi a p.2) (hi a p.1)]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hp.2.1] at hs
    change Function.uncurry F (triangleProj a b (p.1, s)) = F p.1 s
    rw [triangleProj_of_mem (p := (p.1, s)) ⟨hp.1, hs.1, hs.2.trans hp.2.2⟩]
    rfl
  · have he : triangle a b = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hab (hp.1.trans (hp.2.1.trans hp.2.2))
    rw [he]
    exact continuousOn_empty _

/-- Incoming primitives depend jointly continuously on both characteristic coordinates. -/
theorem continuousOn_integral_incoming
    (hF : ContinuousOn (Function.uncurry F) (triangle a b)) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ s in a..p.1, F s p.2) (triangle a b) := by
  by_cases hab : a ≤ b
  · let G : ℝ → ℝ → E := fun v s => Function.uncurry F (triangleProj a b (s, v))
    have hG : Continuous (Function.uncurry G) :=
      (continuous_comp_triangleProj hab hF).comp continuous_swap
    have hc : Continuous (fun p : ℝ × ℝ => ∫ s in a..p.1, G p.2 s) :=
      (intervalIntegral.continuous_parametric_primitive_of_continuous hG).comp continuous_swap
    apply hc.continuousOn.congr
    intro p hp
    symm
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hp.1] at hs
    change Function.uncurry F (triangleProj a b (s, p.2)) = F s p.2
    rw [triangleProj_of_mem (p := (s, p.2)) ⟨hs.1, hs.2.trans hp.2.1, hp.2.2⟩]
    rfl
  · have he : triangle a b = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hab (hp.1.trans (hp.2.1.trans hp.2.2))
    rw [he]
    exact continuousOn_empty _

end EmcsfAcExtension
