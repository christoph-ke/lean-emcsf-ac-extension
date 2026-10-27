module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Characteristic first derivatives on closed rectangles

The literal two Goursat integral equations give their characteristic
derivatives by FTC, including every side and corner. These elementary
helpers require only continuity and are independent of the joint C¹
upgrade and transverse Volterra equations.
-/

public section

open Set MeasureTheory Filter
open scoped Topology

namespace EmcsfAcExtension.Local

section Primitive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a b : ℝ} {q f : ℝ → E} {f₀ : E}

/-- A continuous characteristic density differentiates its integral
representation, including both endpoints of the closed interval. -/
theorem characteristic_hasDerivWithinAt
    (hq : ContinuousOn q (Icc a b))
    (heq : ∀ t ∈ Icc a b, f t = f₀ + ∫ s in a..t, q s)
    {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt f (q t) (Icc a b) t := by
  have : Fact (t ∈ Icc a b) := ⟨ht⟩
  have hi : HasDerivWithinAt (fun x => ∫ s in a..x, q s) (q t) (Icc a b) t :=
    intervalIntegral.integral_hasDerivWithinAt_right (s := Icc a b) (t := Icc a b)
      ((hq.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1)
      (hq.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hq t ht)
  apply (hi.const_add f₀).congr_of_mem _ ht
  intro s hs
  exact heq s hs

end Primitive

section Goursat

variable {I O : Type*} [NormedAddCommGroup I] [NormedSpace ℝ I] [CompleteSpace I]
  [NormedAddCommGroup O] [NormedSpace ℝ O] [CompleteSpace O]
  {a b c d : ℝ} {F : ℝ × ℝ → I × O}
  {fi : I × O → I} {fo : I × O → O} {yi : ℝ → I} {xb : ℝ → O}

omit [NormedSpace ℝ I] [CompleteSpace I] [NormedSpace ℝ O] [CompleteSpace O] in
/-- A continuous Goursat state and continuous sources have jointly
continuous characteristic slopes. Continuity is needed only on the
actual compact state range, so rational sources need no global extension. -/
theorem goursat_characteristic_slopes_continuousOn
    (hF : ContinuousOn F (Icc a b ×ˢ Icc c d))
    (hi : ContinuousOn fi (F '' (Icc a b ×ˢ Icc c d)))
    (ho : ContinuousOn fo (F '' (Icc a b ×ˢ Icc c d))) :
    ContinuousOn (fun p => fi (F p)) (Icc a b ×ˢ Icc c d) ∧
      ContinuousOn (fun p => fo (F p)) (Icc a b ×ˢ Icc c d) := by
  exact ⟨hi.comp hF (fun p hp => mem_image_of_mem F hp),
    ho.comp hF (fun p hp => mem_image_of_mem F hp)⟩

/-- The two actual integral equations on a closed rectangle give their
characteristic equations, with continuous joint right sides. This uses
only continuity of the state and sources, and includes every side and
corner of the rectangle. -/
theorem goursat_characteristic_hasDerivWithinAt
    (hF : ContinuousOn F (Icc a b ×ˢ Icc c d))
    (hi : ContinuousOn fi (F '' (Icc a b ×ˢ Icc c d)))
    (ho : ContinuousOn fo (F '' (Icc a b ×ˢ Icc c d)))
    (hYi : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      (F (u, v)).1 = yi v + ∫ s in a..u, fi (F (s, v)))
    (hXb : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      (F (u, v)).2 = xb u + ∫ t in c..v, fo (F (u, t)))
    {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc c d) :
    HasDerivWithinAt (fun s => (F (s, v)).1) (fi (F (u, v))) (Icc a b) u ∧
      HasDerivWithinAt (fun t => (F (u, t)).2) (fo (F (u, v))) (Icc c d) v := by
  obtain ⟨hci, hco⟩ := goursat_characteristic_slopes_continuousOn hF hi ho
  have hqi : ContinuousOn (fun s => fi (F (s, v))) (Icc a b) :=
    hci.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, hv⟩)
  have hqo : ContinuousOn (fun t => fo (F (u, t))) (Icc c d) :=
    hco.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨hu, ht⟩)
  exact ⟨characteristic_hasDerivWithinAt hqi (fun s hs => hYi s hs v hv) hu,
    characteristic_hasDerivWithinAt hqo (fun t ht => hXb u hu t ht) hv⟩

end Goursat

end EmcsfAcExtension.Local
