module

public import EmcsfAcExtension.Local.Construction.FullSystemDomain
public import EmcsfAcExtension.Local.Defs.Partial
import EmcsfAcExtension.Infra.Calculus.WithinIntegral

/-! # Parameter integrals on the closed construction wedge

Closed-domain versions of the primitive calculus in internal project record (21).
Compactness supplies domination; no exterior differentiability is assumed.
-/

public section

open Set MeasureTheory Filter ContinuousLinearMap
open scoped Topology

namespace EmcsfAcExtension.Local.Null

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Continuous compactly parametrized integrands have continuous integrals.
This statement is local to the displayed compact parameter domain. -/
theorem continuousOn_integral_compact {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] {D : Set X} (hD : IsCompact D)
    {F : X → ℝ → E} {l r : ℝ}
    (hF : ContinuousOn (Function.uncurry F) (D ×ˢ uIcc l r)) :
    ContinuousOn (fun p => ∫ t in l..r, F p t) D := by
  obtain ⟨C, hC⟩ := (hD.prod isCompact_uIcc).exists_bound_of_continuousOn hF
  have hs (p : X) (hp : p ∈ D) : ContinuousOn (F p) (uIcc l r) :=
    hF.comp (continuousOn_const.prodMk continuousOn_id) (fun _ ht => ⟨hp, ht⟩)
  intro p hp
  apply intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun _ => C)
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact ((hs q hq).aestronglyMeasurable measurableSet_uIcc).mono_set uIoc_subset_uIcc
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact Filter.Eventually.of_forall (fun t ht => hC (q, t) ⟨hq, uIoc_subset_uIcc ht⟩)
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall (fun t ht =>
      (hF.comp (continuousOn_id.prodMk continuousOn_const)
        (fun _ hq => ⟨hq, uIoc_subset_uIcc ht⟩)) p hp)

/-- Integration of continuous first sectional jets preserves joint C¹ on
an entire nondegenerate closed construction wedge. The two jet formulas
are retained explicitly, including at collapsed endpoint sections. -/
theorem contDiffOn_integral_wedge_of_sectional_derivatives
    {a b c l r : ℝ} (hac : a < c) (hcb : c ≤ b)
    {F U V : (ℝ × ℝ) → ℝ → E}
    (cF : ContinuousOn (Function.uncurry F)
      ((triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) ×ˢ uIcc l r))
    (cU : ContinuousOn (Function.uncurry U)
      ((triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) ×ˢ uIcc l r))
    (cV : ContinuousOn (Function.uncurry V)
      ((triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) ×ˢ uIcc l r))
    (dU : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, ∀ t ∈ uIcc l r,
      HasDerivWithinAt (fun x => F (x, p.2) t) (U p t) (Icc a (min c p.2)) p.1)
    (dV : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, ∀ t ∈ uIcc l r,
      HasDerivWithinAt (fun x => F (p.1, x) t) (V p t) (Icc p.1 b) p.2) :
    ContDiffOn ℝ 1 (fun p => ∫ t in l..r, F p t)
        (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) ∧
      (∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
        HasDerivWithinAt (fun x => ∫ t in l..r, F (x, p.2) t)
          (∫ t in l..r, U p t) (Icc a (min c p.2)) p.1 ∧
        HasDerivWithinAt (fun x => ∫ t in l..r, F (p.1, x) t)
          (∫ t in l..r, V p t) (Icc p.1 b) p.2) := by
  have hU (p : ℝ × ℝ) (hp : p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) :
      HasDerivWithinAt (fun x => ∫ t in l..r, F (x, p.2) t)
        (∫ t in l..r, U p t) (Icc a (min c p.2)) p.1 := by
    have ha : a ≤ min c p.2 := le_min (hp.1.1.trans hp.2)
      (hp.1.1.trans hp.1.2.1)
    rcases ha.eq_or_lt with he | ha
    · exact HasFDerivWithinAt.of_subsingleton (by rw [← he, Icc_self]; exact subsingleton_singleton)
    have hs : MapsTo (fun q : ℝ × ℝ => ((q.1, p.2), q.2))
        (Icc a (min c p.2) ×ˢ uIcc l r)
        ((triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) ×ˢ uIcc l r) := by
      intro q hq
      exact ⟨⟨⟨hq.1.1, (le_min_iff.mp hq.1.2).2, hp.1.2.2⟩,
        (le_min_iff.mp hq.1.2).1⟩, hq.2⟩
    have hc : ContinuousOn (fun q : ℝ × ℝ => ((q.1, p.2), q.2))
        (Icc a (min c p.2) ×ˢ uIcc l r) := by fun_prop
    exact hasDerivWithinAt_integral_rectangle (F := fun x t => F (x, p.2) t)
      (F' := fun x t => U (x, p.2) t) ha
      (by simpa only [Function.comp_apply, Function.uncurry] using! cF.comp hc hs)
      (by simpa only [Function.comp_apply, Function.uncurry] using! cU.comp hc hs)
      (fun x hx t ht => dU (x, p.2)
        ⟨⟨hx.1, (le_min_iff.mp hx.2).2, hp.1.2.2⟩, (le_min_iff.mp hx.2).1⟩ t ht)
      ⟨hp.1.1, le_min hp.2 hp.1.2.1⟩
  have hV (p : ℝ × ℝ) (hp : p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) :
      HasDerivWithinAt (fun x => ∫ t in l..r, F (p.1, x) t)
        (∫ t in l..r, V p t) (Icc p.1 b) p.2 := by
    rcases (hp.1.2.1.trans hp.1.2.2).eq_or_lt with he | ha
    · exact HasFDerivWithinAt.of_subsingleton (by rw [← he, Icc_self]; exact subsingleton_singleton)
    have hs : MapsTo (fun q : ℝ × ℝ => ((p.1, q.1), q.2))
        (Icc p.1 b ×ˢ uIcc l r)
        ((triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) ×ˢ uIcc l r) := by
      intro q hq
      exact ⟨⟨⟨hp.1.1, hq.1.1, hq.1.2⟩, hp.2⟩, hq.2⟩
    have hc : ContinuousOn (fun q : ℝ × ℝ => ((p.1, q.1), q.2))
        (Icc p.1 b ×ˢ uIcc l r) := by fun_prop
    exact hasDerivWithinAt_integral_rectangle (F := fun x t => F (p.1, x) t)
      (F' := fun x t => V (p.1, x) t) ha
      (by simpa only [Function.comp_apply, Function.uncurry] using! cF.comp hc hs)
      (by simpa only [Function.comp_apply, Function.uncurry] using! cV.comp hc hs)
      (fun x hx t ht => dV (p.1, x) ⟨⟨hp.1.1, hx.1, hx.2⟩, hp.2⟩ t ht) ⟨hp.1.2.1, hp.1.2.2⟩
  exact ⟨contDiffOn_wedge_of_sectional_derivatives hac hcb hU hV
    (continuousOn_integral_compact (isCompact_wedge a b c) cU)
    (continuousOn_integral_compact (isCompact_wedge a b c) cV), fun p hp => ⟨hU p hp, hV p hp⟩⟩

/-- A jointly C¹ compact parameter integrand may be integrated on `[0,1]`
while preserving C¹ on the original closed wedge. The parameter derivative
is not needed; the product domain ensures its continuous first jets. -/
theorem contDiffOn_integral_wedge {a b c : ℝ} (hac : a < c) (hcb : c ≤ b)
    {F : (ℝ × ℝ) → ℝ → E}
    (cF : ContDiffOn ℝ 1 (Function.uncurry F)
      ((triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) ×ˢ Icc (0 : ℝ) 1)) :
    ContDiffOn ℝ 1 (fun p => ∫ t in (0 : ℝ)..1, F p t)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) := by
  let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
  let J := D ×ˢ Icc (0 : ℝ) 1
  have hJ : UniqueDiffOn ℝ J := (uniqueDiffOn_triangle_inter_fst_le hac hcb).prod
    (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
  have cd := cF.continuousOn_fderivWithin hJ le_rfl
  apply (contDiffOn_integral_wedge_of_sectional_derivatives hac hcb
    (U := fun p t => fderivWithin ℝ (Function.uncurry F) J (p, t) ((1, 0), 0))
    (V := fun p t => fderivWithin ℝ (Function.uncurry F) J (p, t) ((0, 1), 0))
    (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using! cF.continuousOn)
    (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using!
      cd.clm_apply (continuousOn_const (c := (((1, 0), 0) : (ℝ × ℝ) × ℝ))))
    (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using!
      cd.clm_apply (continuousOn_const (c := (((0, 1), 0) : (ℝ × ℝ) × ℝ)))) ?_ ?_).1
  · intro p hp t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
    have hf := (cF.differentiableOn (by norm_num) (p, t) ⟨hp, ht'⟩).hasFDerivWithinAt
    have hd := hf.comp_hasDerivWithinAt
      (f := fun x : ℝ => ((x, p.2), t))
      (s := Icc a (min c p.2)) p.1
      ((((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)).prodMk
        (hasDerivAt_const p.1 t)).hasDerivWithinAt)
      (fun x hx => ⟨⟨⟨hx.1, (le_min_iff.mp hx.2).2, hp.1.2.2⟩,
        (le_min_iff.mp hx.2).1⟩, ht'⟩)
    exact hd
  · intro p hp t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
    have hf := (cF.differentiableOn (by norm_num) (p, t) ⟨hp, ht'⟩).hasFDerivWithinAt
    exact hf.comp_hasDerivWithinAt
      (f := fun x : ℝ => ((p.1, x), t))
      (s := Icc p.1 b) p.2
      ((((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)).prodMk
        (hasDerivAt_const p.2 t)).hasDerivWithinAt)
      (fun x hx => ⟨⟨⟨hp.1.1, hx.1, hx.2⟩, hp.2⟩, ht'⟩)

/-- Every affine radial resampling stays inside the actual construction wedge. -/
theorem radialPoint_mem_wedge {a b c : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) {t : ℝ} (ht : t ∈ Icc 0 1) :
    (p.1, p.1 + (p.2 - p.1) * t) ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c} := by
  refine ⟨⟨hp.1.1, ?_, ?_⟩, hp.2⟩
  · exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hp.1.2.1) ht.1)
  · have := mul_le_mul_of_nonneg_left ht.2 (sub_nonneg.mpr hp.1.2.1)
    linarith [hp.1.2.2]

/-- Averaging along radial segments preserves joint continuity on the full
closed wedge, including the axis and the top vertex. -/
theorem continuousOn_radial_average {a b c : ℝ} {f : ℝ × ℝ → E}
    (hf : ContinuousOn f (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c})) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ t in (0 : ℝ)..1,
      f (p.1, p.1 + (p.2 - p.1) * t))
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) := by
  apply continuousOn_integral_compact (isCompact_wedge a b c)
  apply hf.comp (by fun_prop)
  intro q hq
  exact radialPoint_mem_wedge hq.1 (by simpa using hq.2)

/-- A radial average of a jointly C¹ integrand is jointly C¹ without any
second derivative. The affine resampling includes all wedge boundaries. -/
theorem contDiffOn_radial_average {a b c : ℝ} (hac : a < c) (hcb : c ≤ b)
    {f : ℝ × ℝ → E}
    (hf : ContDiffOn ℝ 1 f (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c})) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => ∫ t in (0 : ℝ)..1,
      f (p.1, p.1 + (p.2 - p.1) * t))
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) := by
  apply contDiffOn_integral_wedge hac hcb
  apply hf.comp (by fun_prop)
  intro q hq
  exact radialPoint_mem_wedge hq.1 hq.2

/-- A radial moment with any fixed nonnegative integral power preserves
joint C¹. The power is fixed before the source and no estimate constant
is introduced. This covers all weighted normalized profiles in (6). -/
theorem contDiffOn_radial_moment {a b c : ℝ} (hac : a < c) (hcb : c ≤ b)
    (n : ℕ) {f : ℝ × ℝ → E}
    (hf : ContDiffOn ℝ 1 f (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c})) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => ∫ t in (0 : ℝ)..1,
      t ^ n • f (p.1, p.1 + (p.2 - p.1) * t))
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) := by
  apply contDiffOn_integral_wedge hac hcb
  apply (contDiffOn_snd.pow n).smul
  apply hf.comp (by fun_prop)
  intro q hq
  exact radialPoint_mem_wedge hq.1 hq.2

/-- The radial substitution formula is exact also on the diagonal; no
nonzero-width cancellation is used. -/
theorem integral_eq_width_smul_radial_average (f : ℝ → ℝ → E) (u v : ℝ) :
    (∫ s in u..v, f u s) =
      (v - u) • ∫ t in (0 : ℝ)..1, f u (u + (v - u) * t) := by
  simp [intervalIntegral.smul_integral_comp_add_mul]

/-- The moving-lower-endpoint primitive of a jointly C¹ source is jointly
C¹ on its original closed wedge. This proof resamples to `[0,1]` and uses
only first jets of the source. -/
theorem contDiffOn_radial_primitive {a b c : ℝ} (hac : a < c) (hcb : c ≤ b)
    {f : ℝ → ℝ → E}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c})) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => ∫ s in p.1..p.2, f p.1 s)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) := by
  simp_rw [integral_eq_width_smul_radial_average]
  exact (contDiffOn_snd.sub contDiffOn_fst).smul (contDiffOn_radial_average hac hcb hf)

/-- Identify an actual continuous field with its outgoing primitive, even
when a raw totalized source has a different value at the axis endpoint.
The continuous source agrees with the raw one only off axis; the single
endpoint does not change the interval integral. -/
theorem eq_radial_primitive_of_off_axis_derivative [CompleteSpace E]
    {a b c : ℝ} {F G H : ℝ → ℝ → E}
    (cF : ContinuousOn (Function.uncurry F) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cG : ContinuousOn (Function.uncurry G) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hF0 : ∀ t ∈ Icc a c, F t t = 0)
    (hd : ∀ u ∈ Icc a c, ∀ v ∈ Ioo u b, HasDerivAt (F u) (G u v) v)
    (heq : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, p.1 < p.2 →
      G p.1 p.2 = H p.1 p.2) :
    ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, F p.1 p.2 = ∫ s in p.1..p.2, H p.1 s := by
  intro p hp
  have hu : p.1 ∈ Icc a c := ⟨hp.1.1, hp.2⟩
  have hs : MapsTo (fun s => (p.1, s)) (Icc p.1 p.2)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) :=
    fun s hs => ⟨⟨hp.1.1, hs.1, hs.2.trans hp.1.2.2⟩, hp.2⟩
  have cg := cG.comp (continuousOn_const.prodMk continuousOn_id) hs
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hp.1.2.1
    (cF.comp (continuousOn_const.prodMk continuousOn_id) hs)
    (fun s hs' => hd p.1 hu s ⟨hs'.1, hs'.2.trans_le hp.1.2.2⟩)
    (cg.intervalIntegrable_of_Icc hp.1.2.1)
  change (∫ s in p.1..p.2, G p.1 s) = F p.1 p.2 - F p.1 p.1 at hi
  rw [hF0 p.1 hu, sub_zero] at hi
  rw [← hi]
  apply intervalIntegral.integral_congr_ae
  exact Filter.Eventually.of_forall (fun s hs' => by
    rw [uIoc_of_le hp.1.2.1] at hs'
    exact heq (p.1, s) (hs ⟨hs'.1.le, hs'.2⟩) hs'.1)


end EmcsfAcExtension.Local.Null
