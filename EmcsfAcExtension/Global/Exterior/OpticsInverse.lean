module

public import EmcsfAcExtension.Global.Exterior.ScalarEnergy

/-! # Inverse control of the adaptive frontier

A positive almost-everywhere speed, together with the already proved
Lipschitz graph, gives a quantitative inverse bound on every proper
frontier segment. The constants are chosen for each proper interval
before quantifying over its labels.
-/

public section

open Set Filter Topology MeasureTheory
open scoped NNReal

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
A Lipschitz monotone real function whose derivative is bounded below
almost everywhere has an inverse distance bound. The numerical factor
`m` is fixed before both labels are quantified. -/
theorem inverse_distance_le_of_ae_deriv {V : ℝ → ℝ} {a b m : ℝ} {L : ℝ≥0}
    (hab : a ≤ b) (hLip : LipschitzOnWith L V (Icc a b))
    (hmono : MonotoneOn V (Icc a b))
    (hderiv : ∀ᵐ x ∂volume.restrict (Icc a b), m ≤ deriv V x) :
    ∀ u ∈ Icc a b, ∀ w ∈ Icc a b, m * dist u w ≤ dist (V u) (V w) := by
  have hAC : AbsolutelyContinuousOnInterval V a b :=
    (show LipschitzOnWith L V (uIcc a b) from by
      simpa only [uIcc_of_le hab] using hLip).absolutelyContinuousOnInterval
  have hinc (u : ℝ) (hu : u ∈ Icc a b) (w : ℝ) (hw : w ∈ Icc a b) (huw : u ≤ w) :
      m * (w - u) ≤ V w - V u := by
    have hsub : uIcc u w ⊆ uIcc a b := by
      rw [uIcc_of_le huw, uIcc_of_le hab]
      exact Icc_subset_Icc hu.1 hw.2
    have hACuw := hAC.mono hsub
    have hd : ∀ᵐ x ∂volume.restrict (Icc u w), m ≤ deriv V x :=
      hderiv.filter_mono (ae_mono (Measure.restrict_mono
        (Icc_subset_Icc hu.1 hw.2) le_rfl))
    have hi := intervalIntegral.integral_mono_ae_restrict huw
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => m) volume u w)
      hACuw.intervalIntegrable_deriv_finiteDimensional hd
    rw [intervalIntegral.integral_const, smul_eq_mul,
      hACuw.integral_deriv_eq_sub_finiteDimensional] at hi
    nlinarith only [hi]
  intro u hu w hw
  rcases le_total u w with huw | hwu
  · have hvw := hmono hu hw huw
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr huw), Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr hvw)]
    simpa only [neg_sub] using hinc u hu w hw huw
  · have hvu := hmono hw hu hwu
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hwu), Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr hvu)]
    exact hinc w hw u hu hwu

end EmcsfAcExtension.Global.Exterior
