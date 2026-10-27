/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Infra.Calculus.PartialsC1

/-! # Continuous sectional derivatives on the closed construction wedge

The domain is exactly the polygon underlying `PicardDomain` in the internal project record
carrier handoff. Its incoming sections end at `min c v`, rather than `v`.
The closed-domain C¹ argument of internal project record `#smooth-regularity` retains
both the cutoff edge and the possibly collapsed top outgoing section.
-/

public section

namespace EmcsfAcExtension.Local.Null

open Set Filter ContinuousLinearMap
open scoped Topology

/-- The closed construction wedge is convex. -/
theorem convex_wedge (a b c : ℝ) :
    Convex ℝ (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) := by
  apply (convex_triangle a b).inter
  intro p hp q hq s t hs ht hst
  change s * p.1 + t * q.1 ≤ c
  calc
    s * p.1 + t * q.1 ≤ s * c + t * c := add_le_add
      (mul_le_mul_of_nonneg_left hp hs) (mul_le_mul_of_nonneg_left hq ht)
    _ = c := by rw [← add_mul, hst, one_mul]

/-- The closed construction wedge is compact, including when a section collapses. -/
theorem isCompact_wedge (a b c : ℝ) :
    IsCompact (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) :=
  (isCompact_triangle a b).inter_right (isClosed_le continuous_fst continuous_const)

/-- A nondegenerate construction wedge is the closure of its ambient interior. -/
theorem closure_interior_wedge {a b c : ℝ} (hac : a < c) (hcb : c ≤ b) :
    closure (interior (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c})) =
      triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c} := by
  have hi : (interior (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c})).Nonempty := by
    let U : Set (ℝ × ℝ) := {p | a < p.1 ∧ p.1 < p.2 ∧ p.2 < b ∧ p.1 < c}
    have hU : IsOpen U := (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_snd).inter
        ((isOpen_lt continuous_snd continuous_const).inter
          (isOpen_lt continuous_fst continuous_const)))
    refine ⟨((2 * a + c) / 3, (a + 2 * c) / 3),
      mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hU.mem_nhds ?_) ?_)⟩
    · change a < (2 * a + c) / 3 ∧ (2 * a + c) / 3 < (a + 2 * c) / 3 ∧
        (a + 2 * c) / 3 < b ∧ (2 * a + c) / 3 < c
      constructor
      · linarith
      constructor
      · linarith
      constructor <;> linarith
    · exact fun p hp => ⟨⟨hp.1.le, hp.2.1.le, hp.2.2.1.le⟩, hp.2.2.2.le⟩
  rw [(convex_wedge a b c).closure_interior_eq_closure_of_nonempty_interior hi,
    ((isClosed_triangle a b).inter (isClosed_le continuous_fst continuous_const)).closure_eq]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {a b c : ℝ} {f gU gV : ℝ × ℝ → E}

private theorem norm_sub_le_of_ordered_wedge_sections {C : ℝ} (hC : 0 ≤ C)
    (hU : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      HasDerivWithinAt (fun x => f (x, p.2)) (gU p) (Icc a (min c p.2)) p.1)
    (hV : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      HasDerivWithinAt (fun x => f (p.1, x)) (gV p) (Icc p.1 b) p.2)
    (bU : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, ‖gU p‖ ≤ C)
    (bV : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, ‖gV p‖ ≤ C)
    {p q : ℝ × ℝ} (hp : p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c})
    (hq : q ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c})
    (hpq : p.1 ≤ q.1) : ‖f q - f p‖ ≤ (2 * C) * ‖q - p‖ := by
  have hU' : ∀ x ∈ Icc a (min c q.2),
      HasDerivWithinAt (fun x => f (x, q.2)) (gU (x, q.2)) (Icc a (min c q.2)) x := by
    intro x hx
    exact hU (x, q.2) ⟨⟨hx.1, (le_min_iff.mp hx.2).2, hq.1.2.2⟩, (le_min_iff.mp hx.2).1⟩
  have bU' : ∀ x ∈ Icc a (min c q.2), ‖gU (x, q.2)‖ ≤ C := by
    intro x hx
    exact bU (x, q.2) ⟨⟨hx.1, (le_min_iff.mp hx.2).2, hq.1.2.2⟩, (le_min_iff.mp hx.2).1⟩
  have hH : ‖f q - f (p.1, q.2)‖ ≤ C * ‖q.1 - p.1‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hU' bU' (convex_Icc a (min c q.2))
      ⟨hp.1.1, le_min hp.2 (hpq.trans hq.1.2.1)⟩ ⟨hq.1.1, le_min hq.2 hq.1.2.1⟩
  have hV' : ∀ x ∈ Icc p.1 b,
      HasDerivWithinAt (fun x => f (p.1, x)) (gV (p.1, x)) (Icc p.1 b) x := by
    intro x hx
    exact hV (p.1, x) ⟨⟨hp.1.1, hx.1, hx.2⟩, hp.2⟩
  have bV' : ∀ x ∈ Icc p.1 b, ‖gV (p.1, x)‖ ≤ C := by
    intro x hx
    exact bV (p.1, x) ⟨⟨hp.1.1, hx.1, hx.2⟩, hp.2⟩
  have hW : ‖f (p.1, q.2) - f p‖ ≤ C * ‖q.2 - p.2‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hV' bV' (convex_Icc p.1 b)
      ⟨hp.1.2.1, hp.1.2.2⟩ ⟨hpq.trans hq.1.2.1, hq.1.2.2⟩
  calc
    ‖f q - f p‖ ≤ ‖f q - f (p.1, q.2)‖ + ‖f (p.1, q.2) - f p‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C * ‖q.1 - p.1‖ + C * ‖q.2 - p.2‖ := add_le_add hH hW
    _ ≤ C * ‖q - p‖ + C * ‖q - p‖ := add_le_add
      (mul_le_mul_of_nonneg_left (norm_fst_le (q - p)) hC)
      (mul_le_mul_of_nonneg_left (norm_snd_le (q - p)) hC)
    _ = (2 * C) * ‖q - p‖ := by ring

/-- Continuous sectional derivatives on a closed construction wedge imply joint continuity.
No continuity of the uncurried function is required as a premise. -/
theorem continuousOn_wedge_of_sectional_derivatives
    (hU : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      HasDerivWithinAt (fun x => f (x, p.2)) (gU p) (Icc a (min c p.2)) p.1)
    (hV : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      HasDerivWithinAt (fun x => f (p.1, x)) (gV p) (Icc p.1 b) p.2)
    (cU : ContinuousOn gU (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cV : ContinuousOn gV (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c})) :
    ContinuousOn f (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) := by
  obtain ⟨CU, bU⟩ := (isCompact_wedge a b c).exists_bound_of_continuousOn cU
  obtain ⟨CV, bV⟩ := (isCompact_wedge a b c).exists_bound_of_continuousOn cV
  let C : ℝ := max 0 (max CU CV)
  have hC : 0 ≤ C := le_max_left _ _
  have bU' : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, ‖gU p‖ ≤ C :=
    fun p hp => (bU p hp).trans ((le_max_left _ _).trans (le_max_right _ _))
  have bV' : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, ‖gV p‖ ≤ C :=
    fun p hp => (bV p hp).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hLip : LipschitzOnWith ⟨2 * C, mul_nonneg (by norm_num) hC⟩ f
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro p hp q hq
    simp only [dist_eq_norm]
    change ‖f p - f q‖ ≤ (2 * C) * ‖p - q‖
    rcases le_total q.1 p.1 with hqp | hpq
    · exact norm_sub_le_of_ordered_wedge_sections hC hU hV bU' bV' hq hp hqp
    · simpa only [norm_sub_rev] using
        norm_sub_le_of_ordered_wedge_sections hC hU hV bU' bV' hp hq hpq
  exact hLip.continuousOn

/-- Continuous sectional partials give the total within derivative at every
point of a nondegenerate closed construction wedge, including edges and corners. -/
theorem hasFDerivWithinAt_wedge_of_sectional_derivatives (hac : a < c) (hcb : c ≤ b)
    (hU : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      HasDerivWithinAt (fun x => f (x, p.2)) (gU p) (Icc a (min c p.2)) p.1)
    (hV : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      HasDerivWithinAt (fun x => f (p.1, x)) (gV p) (Icc p.1 b) p.2)
    (cU : ContinuousOn gU (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cV : ContinuousOn gV (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (p : ℝ × ℝ) (hp : p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) :
    HasFDerivWithinAt f
      ((toSpanSingleton ℝ (gU p)).coprod (toSpanSingleton ℝ (gV p)))
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) p := by
  let L : E → (ℝ →L[ℝ] E) := toSpanSingleton ℝ
  have cL : Continuous L := (toSpanSingletonCLE : E ≃L[ℝ] (ℝ →L[ℝ] E)).continuous
  let A (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] E := (L (gU p)).coprod (L (gV p))
  have cA : ContinuousOn A (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) :=
    (cL.comp_continuousOn cU).continuousLinearMapCoprod (cL.comp_continuousOn cV)
  have hIntU : ∀ p ∈ interior (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}),
      HasDerivAt (fun x => f (x, p.2)) (gU p) p.1 := by
    intro p hp
    apply (hU p (interior_subset hp)).hasDerivAt
    have ht := (show Continuous (fun x : ℝ => (x, p.2)) from
      continuous_id.prodMk continuous_const).continuousAt (x := p.1)
    exact Filter.mem_of_superset (ht.preimage_mem_nhds
      (mem_interior_iff_mem_nhds.mp hp)) (fun _ hx => ⟨hx.1.1, le_min hx.2 hx.1.2.1⟩)
  have hIntV : ∀ p ∈ interior (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}),
      HasDerivAt (fun x => f (p.1, x)) (gV p) p.2 := by
    intro p hp
    apply (hV p (interior_subset hp)).hasDerivAt
    have ht := (show Continuous (fun x : ℝ => (p.1, x)) from
      continuous_const.prodMk continuous_id).continuousAt (x := p.2)
    exact Filter.mem_of_superset (ht.preimage_mem_nhds
      (mem_interior_iff_mem_nhds.mp hp)) (fun _ hx => ⟨hx.1.2.1, hx.1.2.2⟩)
  have hInt : ∀ p ∈ interior (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}), HasFDerivAt f (A p) p := by
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
  have cf := continuousOn_wedge_of_sectional_derivatives hU hV cU cV
  have hAll : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      HasFDerivWithinAt f (A p) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) p := by
    intro p hp
    rw [← closure_interior_wedge hac hcb]
    apply hasFDerivWithinAt_closure_of_tendsto_fderiv
      (fun q hq => (hInt q hq).differentiableAt.differentiableWithinAt)
      (convex_wedge a b c).interior isOpen_interior
    · intro q hq
      rw [closure_interior_wedge hac hcb] at hq
      exact (cf q hq).mono interior_subset
    · apply Filter.Tendsto.congr' _ ((cA p hp).mono interior_subset)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hInt q hq).fderiv.symm
  exact hAll p hp

/-- Continuous sectional partials imply C¹ regularity of the uncurried function
on a nondegenerate closed construction wedge, including all edges and corners. -/
theorem contDiffOn_wedge_of_sectional_derivatives (hac : a < c) (hcb : c ≤ b)
    (hU : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      HasDerivWithinAt (fun x => f (x, p.2)) (gU p) (Icc a (min c p.2)) p.1)
    (hV : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      HasDerivWithinAt (fun x => f (p.1, x)) (gV p) (Icc p.1 b) p.2)
    (cU : ContinuousOn gU (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cV : ContinuousOn gV (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c})) :
    ContDiffOn ℝ 1 f (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) := by
  let L : E → (ℝ →L[ℝ] E) := toSpanSingleton ℝ
  have cL : Continuous L := (toSpanSingletonCLE : E ≃L[ℝ] (ℝ →L[ℝ] E)).continuous
  let A (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] E := (L (gU p)).coprod (L (gV p))
  have cA : ContinuousOn A (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) :=
    (cL.comp_continuousOn cU).continuousLinearMapCoprod (cL.comp_continuousOn cV)
  apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
    (n := 0) (uniqueDiffOn_triangle_inter_fst_le hac hcb)).mpr
  exact ⟨by simp, A, contDiffOn_zero.mpr cA,
    hasFDerivWithinAt_wedge_of_sectional_derivatives hac hcb hU hV cU cV⟩

/-- Continuous first jets computed only in the ambient interior extend to
joint C¹ on the closed wedge. This form is useful for quotients whose
boundary values and limiting jets are obtained from radial primitives. -/
theorem contDiffOn_wedge_of_interior_sectional_derivatives (hac : a < c) (hcb : c ≤ b)
    (cf : ContinuousOn f (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cU : ContinuousOn gU (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cV : ContinuousOn gV (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hU : ∀ p ∈ interior (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}),
      HasDerivAt (fun x => f (x, p.2)) (gU p) p.1)
    (hV : ∀ p ∈ interior (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}),
      HasDerivAt (fun x => f (p.1, x)) (gV p) p.2) :
    ContDiffOn ℝ 1 f (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) := by
  let L : E → (ℝ →L[ℝ] E) := toSpanSingleton ℝ
  have cL : Continuous L := (toSpanSingletonCLE : E ≃L[ℝ] (ℝ →L[ℝ] E)).continuous
  let A (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] E := (L (gU p)).coprod (L (gV p))
  have cA : ContinuousOn A (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) :=
    (cL.comp_continuousOn cU).continuousLinearMapCoprod (cL.comp_continuousOn cV)
  have hInt : ∀ p ∈ interior (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}),
      HasFDerivAt f (A p) p := by
    intro p hp
    apply HasStrictFDerivAt.hasFDerivAt
    apply hasStrictFDerivAt_uncurry_coprod
      (f := fun x y => f (x, y)) (f₁ := fun x y => L (gU (x, y)))
      (f₂ := fun x y => L (gV (x, y)))
    · filter_upwards [isOpen_interior.eventually_mem hp] with q hq
      exact (hU q hq).hasFDerivAt
    · filter_upwards [isOpen_interior.eventually_mem hp] with q hq
      exact (hV q hq).hasFDerivAt
    · exact ((cL.comp_continuousOn cU) p (interior_subset hp)).continuousAt
        (mem_interior_iff_mem_nhds.mp hp)
    · exact ((cL.comp_continuousOn cV) p (interior_subset hp)).continuousAt
        (mem_interior_iff_mem_nhds.mp hp)
  have hAll : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      HasFDerivWithinAt f (A p) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) p := by
    intro p hp
    rw [← closure_interior_wedge hac hcb]
    apply hasFDerivWithinAt_closure_of_tendsto_fderiv
      (fun q hq => (hInt q hq).differentiableAt.differentiableWithinAt)
      (convex_wedge a b c).interior isOpen_interior
    · intro q hq
      rw [closure_interior_wedge hac hcb] at hq
      exact (cf q hq).mono interior_subset
    · apply Filter.Tendsto.congr' _ ((cA p hp).mono interior_subset)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hInt q hq).fderiv.symm
  apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
    (n := 0) (uniqueDiffOn_triangle_inter_fst_le hac hcb)).mpr
  exact ⟨by simp, A, contDiffOn_zero.mpr cA, hAll⟩

/-- Equality of continuous fields on the ambient interior extends to the
whole nondegenerate closed wedge. This retains both cutoff corners. -/
theorem eqOn_wedge_of_interior {X : Type*} [TopologicalSpace X] [T2Space X]
    {F G : (ℝ × ℝ) → X} (hac : a < c) (hcb : c ≤ b)
    (cF : ContinuousOn F (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cG : ContinuousOn G (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (heq : EqOn F G (interior (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))) :
    EqOn F G (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) := by
  apply heq.of_subset_closure cF cG interior_subset
  rw [closure_interior_wedge hac hcb]


end EmcsfAcExtension.Local.Null
