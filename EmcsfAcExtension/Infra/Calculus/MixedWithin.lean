/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Infra.Calculus.WithinIntegral

/-! # Mixed derivatives within a closed characteristic rectangle

internal project record infrastructure. Both derivatives are taken within their nondegenerate
closed section intervals. Only continuous source functions and their one
prescribed sectional partial are used, with no exterior regularity premise.
-/

public section

namespace EmcsfAcExtension

open Set Filter MeasureTheory
open scoped Topology Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Recover both within-domain mixed derivatives from the transport primitive.
The first coordinate of the source `F y t` is the transverse parameter;
the integral runs over the second coordinate. The conclusions include all
four corners. No mixed derivative of the primitive is assumed. -/
theorem hasDerivWithinAt_mixed_integral_primitive_rectangle
    {F F' : ℝ → ℝ → E} {B : ℝ → E} {B' : E} {a b c d u v : ℝ}
    (hab : a < b) (hcd : c < d)
    (hF : ContinuousOn (Function.uncurry F) (Icc c d ×ˢ Icc a b))
    (hF' : ContinuousOn (Function.uncurry F') (Icc c d ×ˢ Icc a b))
    (hd : ∀ y ∈ Icc c d, ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun z => F z t) (F' y t) (Icc c d) y)
    (hu : u ∈ Icc a b) (hv : v ∈ Icc c d)
    (hB : HasDerivWithinAt B B' (Icc c d) v) :
    HasDerivWithinAt
      (fun x => derivWithin (fun y => B y + ∫ t in a..x, F y t) (Icc c d) v)
      (F' v u) (Icc a b) u ∧
    HasDerivWithinAt
      (fun y => derivWithin (fun x => B y + ∫ t in a..x, F y t) (Icc a b) u)
      (F' v u) (Icc c d) v := by
  let : Fact (u ∈ Icc a b) := ⟨hu⟩
  have hsub {x : ℝ} (hx : x ∈ Icc a b) : uIcc a x ⊆ Icc a b := by
    rw [uIcc_of_le hx.1]
    exact Icc_subset_Icc le_rfl hx.2
  have cF (y : ℝ) (hy : y ∈ Icc c d) : ContinuousOn (F y) (Icc a b) :=
    hF.comp (continuousOn_const.prodMk continuousOn_id) (fun _ ht => ⟨hy, ht⟩)
  have cF' (y : ℝ) (hy : y ∈ Icc c d) : ContinuousOn (F' y) (Icc a b) :=
    hF'.comp (continuousOn_const.prodMk continuousOn_id) (fun _ ht => ⟨hy, ht⟩)
  have hV (x : ℝ) (hx : x ∈ Icc a b) :
      derivWithin (fun y => B y + ∫ t in a..x, F y t) (Icc c d) v =
        B' + ∫ t in a..x, F' v t := by
    have hrect : Icc c d ×ˢ uIcc a x ⊆ Icc c d ×ˢ Icc a b :=
      fun _ hp => ⟨hp.1, hsub hx hp.2⟩
    exact (hB.add (hasDerivWithinAt_integral_rectangle hcd (hF.mono hrect)
      (hF'.mono hrect) (fun y hy t ht => hd y hy t (hsub hx ht)) hv)).derivWithin
      (uniqueDiffOn_Icc hcd v hv)
  have hU (y : ℝ) (hy : y ∈ Icc c d) :
      derivWithin (fun x => B y + ∫ t in a..x, F y t) (Icc a b) u = F y u := by
    have h : HasDerivWithinAt (fun x => B y + ∫ t in a..x, F y t)
        (0 + F y u) (Icc a b) u :=
      (hasDerivWithinAt_const u (Icc a b) (B y)).add
        (intervalIntegral.integral_hasDerivWithinAt_right
          ((cF y hy).mono (hsub hu)).intervalIntegrable
          ((cF y hy).stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc u)
          (cF y hy u hu))
    simpa only [zero_add] using h.derivWithin (uniqueDiffOn_Icc hab u hu)
  constructor
  · have h : HasDerivWithinAt (fun x => B' + ∫ t in a..x, F' v t)
        (0 + F' v u) (Icc a b) u :=
      (hasDerivWithinAt_const u (Icc a b) B').add
        (intervalIntegral.integral_hasDerivWithinAt_right
          ((cF' v hv).mono (hsub hu)).intervalIntegrable
          ((cF' v hv).stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc u)
          (cF' v hv u hu))
    simpa only [zero_add] using h.congr hV (hV u hu)
  · exact (hd v hv u hu).congr hU (hU v hv)

end EmcsfAcExtension
