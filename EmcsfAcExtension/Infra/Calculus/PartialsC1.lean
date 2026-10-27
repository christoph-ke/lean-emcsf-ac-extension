/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Sectional derivatives of functions that are C¹ within a domain

internal project record infrastructure, with no dependency-graph node claim. The generic
section lemmas apply to triangles, trapezoids and rectangles using
`TriangleDiff` for uniqueness. For curried fields take `f := Function.uncurry g`.
-/

public section

namespace EmcsfAcExtension

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {D : Set (ℝ × ℝ)} {f : ℝ × ℝ → E} {u v : ℝ}

/-- Extract the incoming section derivative on any section contained in `D`.
The value is exactly the `pdU` expression of the architecture. -/
theorem hasDerivWithinAt_section_u (hf : ContDiffOn ℝ 1 f D)
    (hp : (u, v) ∈ D) {s : Set ℝ} (hs : MapsTo (fun x => (x, v)) s D) :
    HasDerivWithinAt (fun x => f (x, v)) (fderivWithin ℝ f D (u, v) (1, 0)) s u :=
  ((hf.differentiableOn (by norm_num) _ hp).hasFDerivWithinAt).comp_hasDerivWithinAt u
    (((hasDerivAt_id u).prodMk (hasDerivAt_const u v)).hasDerivWithinAt) hs

/-- Extract the outgoing section derivative on any section contained in `D`.
The value is exactly the `pdV` expression of the architecture. -/
theorem hasDerivWithinAt_section_v (hf : ContDiffOn ℝ 1 f D)
    (hp : (u, v) ∈ D) {s : Set ℝ} (hs : MapsTo (fun x => (u, x)) s D) :
    HasDerivWithinAt (fun x => f (u, x)) (fderivWithin ℝ f D (u, v) (0, 1)) s v :=
  ((hf.differentiableOn (by norm_num) _ hp).hasFDerivWithinAt).comp_hasDerivWithinAt v
    (((hasDerivAt_const v u).prodMk (hasDerivAt_id v)).hasDerivWithinAt) hs

/-- The incoming partial of a C¹ function is continuous on a unique-differentiation domain. -/
theorem continuousOn_partial_u (hf : ContDiffOn ℝ 1 f D) (hD : UniqueDiffOn ℝ D) :
    ContinuousOn (fun p => fderivWithin ℝ f D p (1, 0)) D :=
  (hf.continuousOn_fderivWithin hD le_rfl).clm_apply continuousOn_const

/-- The outgoing partial of a C¹ function is continuous on a unique-differentiation domain. -/
theorem continuousOn_partial_v (hf : ContDiffOn ℝ 1 f D) (hD : UniqueDiffOn ℝ D) :
    ContinuousOn (fun p => fderivWithin ℝ f D p (0, 1)) D :=
  (hf.continuousOn_fderivWithin hD le_rfl).clm_apply continuousOn_const

/-- The incoming derivative on the entire closed incoming triangle section. -/
theorem hasDerivWithinAt_triangle_u {a b : ℝ} (hf : ContDiffOn ℝ 1 f (triangle a b))
    (hp : (u, v) ∈ triangle a b) :
    HasDerivWithinAt (fun x => f (x, v))
      (fderivWithin ℝ f (triangle a b) (u, v) (1, 0)) (Icc a v) u :=
  hasDerivWithinAt_section_u hf hp (fun _ hx => ⟨hx.1, hx.2, hp.2.2⟩)

/-- The outgoing derivative on the entire closed outgoing triangle section. -/
theorem hasDerivWithinAt_triangle_v {a b : ℝ} (hf : ContDiffOn ℝ 1 f (triangle a b))
    (hp : (u, v) ∈ triangle a b) :
    HasDerivWithinAt (fun x => f (u, x))
      (fderivWithin ℝ f (triangle a b) (u, v) (0, 1)) (Icc u b) v :=
  hasDerivWithinAt_section_v hf hp (fun _ hx => ⟨hp.1, hx.1, hx.2⟩)

/-- In the interior of a section, the incoming ordinary derivative is the domain partial. -/
theorem deriv_section_u (hf : ContDiffOn ℝ 1 f D) (hp : (u, v) ∈ D)
    {s : Set ℝ} (hs : MapsTo (fun x => (x, v)) s D) (hu : s ∈ 𝓝 u) :
    deriv (fun x => f (x, v)) u = fderivWithin ℝ f D (u, v) (1, 0) :=
  ((hasDerivWithinAt_section_u hf hp hs).hasDerivAt hu).deriv

/-- In the interior of a section, the outgoing ordinary derivative is the domain partial. -/
theorem deriv_section_v (hf : ContDiffOn ℝ 1 f D) (hp : (u, v) ∈ D)
    {s : Set ℝ} (hs : MapsTo (fun x => (u, x)) s D) (hv : s ∈ 𝓝 v) :
    deriv (fun x => f (u, x)) v = fderivWithin ℝ f D (u, v) (0, 1) :=
  ((hasDerivWithinAt_section_v hf hp hs).hasDerivAt hv).deriv

/-- Restriction of a C¹ function preserves its domain derivative if the smaller
domain has unique derivatives. This applies to all nondegenerate subdomains. -/
theorem fderivWithin_eq_of_subset {D' : Set (ℝ × ℝ)} (hf : ContDiffOn ℝ 1 f D)
    (hsub : D' ⊆ D) (hD' : UniqueDiffOn ℝ D') {p : ℝ × ℝ} (hp : p ∈ D') :
    fderivWithin ℝ f D' p = fderivWithin ℝ f D p :=
  fderivWithin_subset hsub (hD' _ hp) (hf.differentiableOn (by norm_num) _ (hsub hp))

/-- Domain derivatives depend only on the function values on the domain. -/
theorem fderivWithin_eq_of_eqOn {g : ℝ × ℝ → E} (hfg : EqOn f g D)
    {p : ℝ × ℝ} (hp : p ∈ D) : fderivWithin ℝ f D p = fderivWithin ℝ g D p :=
  fderivWithin_congr hfg (hfg hp)

/-- Curried incoming sectional derivative, using exactly `Function.uncurry`. -/
theorem hasDerivWithinAt_uncurry_triangle_u {a b : ℝ} {F : ℝ → ℝ → E}
    (hf : ContDiffOn ℝ 1 (Function.uncurry F) (triangle a b))
    (hp : (u, v) ∈ triangle a b) :
    HasDerivWithinAt (fun x => F x v)
      (fderivWithin ℝ (Function.uncurry F) (triangle a b) (u, v) (1, 0)) (Icc a v) u :=
  hasDerivWithinAt_triangle_u hf hp

/-- Curried outgoing sectional derivative, using exactly `Function.uncurry`. -/
theorem hasDerivWithinAt_uncurry_triangle_v {a b : ℝ} {F : ℝ → ℝ → E}
    (hf : ContDiffOn ℝ 1 (Function.uncurry F) (triangle a b))
    (hp : (u, v) ∈ triangle a b) :
    HasDerivWithinAt (F u)
      (fderivWithin ℝ (Function.uncurry F) (triangle a b) (u, v) (0, 1)) (Icc u b) v :=
  hasDerivWithinAt_triangle_v hf hp

end EmcsfAcExtension
