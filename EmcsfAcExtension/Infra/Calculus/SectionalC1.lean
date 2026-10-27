/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Infra.Calculus.PartialsC1

/-! # Continuous sectional partials give C¹ regularity on a closed triangle

internal project record infrastructure for the frozen C¹ radius clause. Joint continuity is
derived from the sectional assumptions. At the boundary, differentiability
is obtained by extending the continuous derivative from the convex interior.
No extra continuity, extension, or boundary differentiability is assumed.
-/

public section

namespace EmcsfAcExtension

open Set Filter ContinuousLinearMap
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {a b : ℝ} {f gU gV : ℝ × ℝ → E}

private theorem norm_sub_le_of_ordered_sections {C : ℝ} (hC : 0 ≤ C)
    (hU : ∀ p ∈ triangle a b,
      HasDerivWithinAt (fun x => f (x, p.2)) (gU p) (Icc a p.2) p.1)
    (hV : ∀ p ∈ triangle a b,
      HasDerivWithinAt (fun x => f (p.1, x)) (gV p) (Icc p.1 b) p.2)
    (bU : ∀ p ∈ triangle a b, ‖gU p‖ ≤ C)
    (bV : ∀ p ∈ triangle a b, ‖gV p‖ ≤ C)
    {p q : ℝ × ℝ} (hp : p ∈ triangle a b) (hq : q ∈ triangle a b)
    (hpq : p.1 ≤ q.1) : ‖f q - f p‖ ≤ (2 * C) * ‖q - p‖ := by
  have hU' : ∀ x ∈ Icc a q.2,
      HasDerivWithinAt (fun x => f (x, q.2)) (gU (x, q.2)) (Icc a q.2) x := by
    intro x hx
    exact hU (x, q.2) ⟨hx.1, hx.2, hq.2.2⟩
  have bU' : ∀ x ∈ Icc a q.2, ‖gU (x, q.2)‖ ≤ C := by
    intro x hx
    exact bU (x, q.2) ⟨hx.1, hx.2, hq.2.2⟩
  have hH : ‖f q - f (p.1, q.2)‖ ≤ C * ‖q.1 - p.1‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hU' bU' (convex_Icc a q.2)
      ⟨hp.1, hpq.trans hq.2.1⟩ ⟨hq.1, hq.2.1⟩
  have hV' : ∀ x ∈ Icc p.1 b,
      HasDerivWithinAt (fun x => f (p.1, x)) (gV (p.1, x)) (Icc p.1 b) x := by
    intro x hx
    exact hV (p.1, x) ⟨hp.1, hx.1, hx.2⟩
  have bV' : ∀ x ∈ Icc p.1 b, ‖gV (p.1, x)‖ ≤ C := by
    intro x hx
    exact bV (p.1, x) ⟨hp.1, hx.1, hx.2⟩
  have hW : ‖f (p.1, q.2) - f p‖ ≤ C * ‖q.2 - p.2‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hV' bV' (convex_Icc p.1 b)
      ⟨hp.2.1, hp.2.2⟩ ⟨hpq.trans hq.2.1, hq.2.2⟩
  calc
    ‖f q - f p‖ ≤ ‖f q - f (p.1, q.2)‖ + ‖f (p.1, q.2) - f p‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C * ‖q.1 - p.1‖ + C * ‖q.2 - p.2‖ := add_le_add hH hW
    _ ≤ C * ‖q - p‖ + C * ‖q - p‖ := add_le_add
      (mul_le_mul_of_nonneg_left (norm_fst_le (q - p)) hC)
      (mul_le_mul_of_nonneg_left (norm_snd_le (q - p)) hC)
    _ = (2 * C) * ‖q - p‖ := by ring

/-- Continuous sectional derivatives on a closed triangle imply joint continuity.
No continuity of the uncurried function is required as a premise. -/
theorem continuousOn_triangle_of_sectional_derivatives
    (hU : ∀ p ∈ triangle a b,
      HasDerivWithinAt (fun x => f (x, p.2)) (gU p) (Icc a p.2) p.1)
    (hV : ∀ p ∈ triangle a b,
      HasDerivWithinAt (fun x => f (p.1, x)) (gV p) (Icc p.1 b) p.2)
    (cU : ContinuousOn gU (triangle a b)) (cV : ContinuousOn gV (triangle a b)) :
    ContinuousOn f (triangle a b) := by
  obtain ⟨CU, bU⟩ := (isCompact_triangle a b).exists_bound_of_continuousOn cU
  obtain ⟨CV, bV⟩ := (isCompact_triangle a b).exists_bound_of_continuousOn cV
  let C : ℝ := max 0 (max CU CV)
  have hC : 0 ≤ C := le_max_left _ _
  have bU' : ∀ p ∈ triangle a b, ‖gU p‖ ≤ C :=
    fun p hp => (bU p hp).trans ((le_max_left _ _).trans (le_max_right _ _))
  have bV' : ∀ p ∈ triangle a b, ‖gV p‖ ≤ C :=
    fun p hp => (bV p hp).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hLip : LipschitzOnWith ⟨2 * C, mul_nonneg (by norm_num) hC⟩ f (triangle a b) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro p hp q hq
    simp only [dist_eq_norm]
    change ‖f p - f q‖ ≤ (2 * C) * ‖p - q‖
    rcases le_total q.1 p.1 with hqp | hpq
    · exact norm_sub_le_of_ordered_sections hC hU hV bU' bV' hq hp hqp
    · simpa only [norm_sub_rev] using
        norm_sub_le_of_ordered_sections hC hU hV bU' bV' hp hq hpq
  exact hLip.continuousOn

/-- Continuous sectional partials give the total within derivative at every
point of a nondegenerate closed triangle, including edges and corners. -/
theorem hasFDerivWithinAt_triangle_of_sectional_derivatives (hab : a < b)
    (hU : ∀ p ∈ triangle a b,
      HasDerivWithinAt (fun x => f (x, p.2)) (gU p) (Icc a p.2) p.1)
    (hV : ∀ p ∈ triangle a b,
      HasDerivWithinAt (fun x => f (p.1, x)) (gV p) (Icc p.1 b) p.2)
    (cU : ContinuousOn gU (triangle a b)) (cV : ContinuousOn gV (triangle a b))
    (p : ℝ × ℝ) (hp : p ∈ triangle a b) :
    HasFDerivWithinAt f
      ((toSpanSingleton ℝ (gU p)).coprod (toSpanSingleton ℝ (gV p))) (triangle a b) p := by
  let L : E → (ℝ →L[ℝ] E) := toSpanSingleton ℝ
  have cL : Continuous L := (toSpanSingletonCLE : E ≃L[ℝ] (ℝ →L[ℝ] E)).continuous
  let A (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] E := (L (gU p)).coprod (L (gV p))
  have cA : ContinuousOn A (triangle a b) :=
    (cL.comp_continuousOn cU).continuousLinearMapCoprod (cL.comp_continuousOn cV)
  have hIntU : ∀ p ∈ interior (triangle a b),
      HasDerivAt (fun x => f (x, p.2)) (gU p) p.1 := by
    intro p hp
    apply (hU p (interior_subset hp)).hasDerivAt
    have ht := (show Continuous (fun x : ℝ => (x, p.2)) from
      continuous_id.prodMk continuous_const).continuousAt (x := p.1)
    exact Filter.mem_of_superset (ht.preimage_mem_nhds
      (mem_interior_iff_mem_nhds.mp hp)) (fun _ hx => ⟨hx.1, hx.2.1⟩)
  have hIntV : ∀ p ∈ interior (triangle a b),
      HasDerivAt (fun x => f (p.1, x)) (gV p) p.2 := by
    intro p hp
    apply (hV p (interior_subset hp)).hasDerivAt
    have ht := (show Continuous (fun x : ℝ => (p.1, x)) from
      continuous_const.prodMk continuous_id).continuousAt (x := p.2)
    exact Filter.mem_of_superset (ht.preimage_mem_nhds
      (mem_interior_iff_mem_nhds.mp hp)) (fun _ hx => ⟨hx.2.1, hx.2.2⟩)
  have hInt : ∀ p ∈ interior (triangle a b), HasFDerivAt f (A p) p := by
    intro p hp
    apply HasStrictFDerivAt.hasFDerivAt
    apply hasStrictFDerivAt_uncurry_coprod
      (f := fun x y => f (x, y)) (f₁ := fun x y => L (gU (x, y)))
      (f₂ := fun x y => L (gV (x, y)))
    · filter_upwards [isOpen_interior.eventually_mem hp] with q hq
      exact (hIntU q hq).hasFDerivAt
    · filter_upwards [isOpen_interior.eventually_mem hp] with q hq
      exact (hIntV q hq).hasFDerivAt
    · exact ((cL.comp_continuousOn cU) p (interior_subset hp)).continuousAt
        (mem_interior_iff_mem_nhds.mp hp)
    · exact ((cL.comp_continuousOn cV) p (interior_subset hp)).continuousAt
        (mem_interior_iff_mem_nhds.mp hp)
  have cf := continuousOn_triangle_of_sectional_derivatives hU hV cU cV
  have hAll : ∀ p ∈ triangle a b, HasFDerivWithinAt f (A p) (triangle a b) p := by
    intro p hp
    rw [← closure_interior_triangle hab]
    apply hasFDerivWithinAt_closure_of_tendsto_fderiv
      (fun q hq => (hInt q hq).differentiableAt.differentiableWithinAt)
      (convex_triangle a b).interior isOpen_interior
    · intro q hq
      rw [closure_interior_triangle hab] at hq
      exact (cf q hq).mono interior_subset
    · apply Filter.Tendsto.congr' _ ((cA p hp).mono interior_subset)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hInt q hq).fderiv.symm
  exact hAll p hp

/-- Continuous sectional partials imply C¹ regularity of the uncurried function
on a nondegenerate closed triangle, including all edges and corners. -/
theorem contDiffOn_triangle_of_sectional_derivatives (hab : a < b)
    (hU : ∀ p ∈ triangle a b,
      HasDerivWithinAt (fun x => f (x, p.2)) (gU p) (Icc a p.2) p.1)
    (hV : ∀ p ∈ triangle a b,
      HasDerivWithinAt (fun x => f (p.1, x)) (gV p) (Icc p.1 b) p.2)
    (cU : ContinuousOn gU (triangle a b)) (cV : ContinuousOn gV (triangle a b)) :
    ContDiffOn ℝ 1 f (triangle a b) := by
  let L : E → (ℝ →L[ℝ] E) := toSpanSingleton ℝ
  have cL : Continuous L := (toSpanSingletonCLE : E ≃L[ℝ] (ℝ →L[ℝ] E)).continuous
  let A (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] E := (L (gU p)).coprod (L (gV p))
  have cA : ContinuousOn A (triangle a b) :=
    (cL.comp_continuousOn cU).continuousLinearMapCoprod (cL.comp_continuousOn cV)
  apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
    (n := 0) (uniqueDiffOn_triangle hab)).mpr
  exact ⟨by simp, A, contDiffOn_zero.mpr cA,
    hasFDerivWithinAt_triangle_of_sectional_derivatives hab hU hV cU cV⟩

/-- Curried form of the closed-triangle C¹ converse, for the local field API. -/
theorem contDiffOn_uncurry_triangle_of_sectional_derivatives (hab : a < b)
    {F U V : ℝ → ℝ → E}
    (hU : ∀ u v, (u, v) ∈ triangle a b →
      HasDerivWithinAt (fun x => F x v) (U u v) (Icc a v) u)
    (hV : ∀ u v, (u, v) ∈ triangle a b →
      HasDerivWithinAt (F u) (V u v) (Icc u b) v)
    (cU : ContinuousOn (Function.uncurry U) (triangle a b))
    (cV : ContinuousOn (Function.uncurry V) (triangle a b)) :
    ContDiffOn ℝ 1 (Function.uncurry F) (triangle a b) :=
  contDiffOn_triangle_of_sectional_derivatives hab
    (fun p hp => hU p.1 p.2 hp) (fun p hp => hV p.1 p.2 hp) cU cV

end EmcsfAcExtension
