module

public import EmcsfAcExtension.Local.Defs.Bounds
public import EmcsfAcExtension.Local.Defs.C1Class
import EmcsfAcExtension.Local.Api.Finite
import EmcsfAcExtension.Local.Limit.UIAux

/-! # Finite envelope intervals in the smooth approximation

Subinterval masses are controlled by the actual full envelope mass, without
discarding finiteness in an ENNReal-to-real conversion.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

private theorem real_interval_le_mass {F : ℝ → ℝ≥0∞} {T a b B : ℝ} (hB : 0 ≤ B)
    (hF : AEMeasurable F (volume.restrict (Icc 0 T)))
    (hbound : (∫⁻ x in Icc 0 T, F x) ≤ ENNReal.ofReal B)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    (∫ x in a..b, (F x).toReal) ≤ B := by
  have hsub : Icc a b ⊆ Icc 0 T := Icc_subset_Icc ha hb
  have hlocal : (∫⁻ x in Icc a b, F x) ≤ ENNReal.ofReal B :=
    (lintegral_mono_set hsub).trans hbound
  have hm := hF.mono_set hsub
  have hfin : (∫⁻ x in Icc a b, F x) < ⊤ := hlocal.trans_lt ENNReal.ofReal_lt_top
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    integral_toReal hm (ae_lt_top' hm hfin.ne)]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hlocal).trans_eq (ENNReal.toReal_ofReal hB)

/-- Every subinterval of either smooth envelope has real mass at most `C*d`.
The constant is exactly the supplied smooth constant, uniformly in the data
and in the independently chosen endpoints. Finiteness is proved before using
`toReal`, and no derivative supremum enters the estimate. -/
theorem envelope_intervals_le_of_bounds {C e T d M : ℝ} {S : Fields}
    (hT : 0 < T) (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hs : IsC1Solution e S (triangle 0 T)) (hb : SmoothBounds C e T d M S) :
    ∀ a b, 0 ≤ a → a ≤ b → b ≤ T →
      (∫ x in a..b, (outEnv 0 (jC1 (triangle 0 T) S) x).toReal) ≤ C * d ∧
      (∫ x in a..b, (inEnv T (kC1 e (triangle 0 T) S) x).toReal) ≤ C * d := by
  intro a b ha hab hbT
  exact ⟨real_interval_le_mass (mul_nonneg hC hd)
      (aemeasurable_outEnv (hs.continuousOn_jC1 hT)) (le_self_add.trans hb.env) ha hab hbT,
    real_interval_le_mass (mul_nonneg hC hd)
      (aemeasurable_inEnv (hs.continuousOn_kC1 hT)) (le_add_self.trans hb.env) ha hab hbT⟩

/-- The supplied localized TV bounds imply full scalar variation budgets
with the explicit coefficient `C²`. The smooth constant is fixed before
coupling, time, sizes and datum; the bound is uniform over both families. -/
theorem scalar_variations_le_of_bounds {C e T d M : ℝ} {S : Fields}
    (hT : 0 < T) (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hs : IsC1Solution e S (triangle 0 T)) (hb : SmoothBounds C e T d M S) :
    (∀ u ∈ Icc 0 T, eVariationOn (S.a u) (Icc u T) ≤ ENNReal.ofReal (C ^ 2 * d)) ∧
    (∀ v ∈ Icc 0 T, covVarIn e S.A S.b 0 v v ≤ ENNReal.ofReal (C ^ 2 * d)) := by
  have henv := envelope_intervals_le_of_bounds hT hC hd hs hb
  constructor
  · intro u hu
    apply (hb.tvj u T hu.1 hu.2 le_rfl).trans
    apply ENNReal.ofReal_le_ofReal
    simpa only [pow_two, mul_assoc] using mul_le_mul_of_nonneg_left
      (henv u T hu.1 hu.2 le_rfl).1 hC
  · intro v hv
    apply (hb.tvk 0 v le_rfl hv.1 hv.2).trans
    apply ENNReal.ofReal_le_ofReal
    simpa only [pow_two, mul_assoc] using mul_le_mul_of_nonneg_left
      (henv 0 v le_rfl hv.1 hv.2).2 hC

end EmcsfAcExtension.Local
