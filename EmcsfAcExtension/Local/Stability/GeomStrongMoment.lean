module

public import EmcsfAcExtension.Local.Stability.OrderedKernelPower

/-! # Ordered moments with a variable coefficient

This version admits the universal difference-moment constant, alongside
the individual moment coefficient, before either kernel is integrated.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- A moment majorant retains its ordered kernel after multiplication by
the primitive radius and a second label function. The exact coefficient
is `C * B`, with no dependence on the functions, sets, or interval lengths.
This is an internal analytic helper, not a graph-node theorem. -/
theorem stab_integral_moment_product_le_of_variable_bound
    {I : Set ℝ} {E : ℝ → Set ℝ} {R : ℝ → ℝ} {q P : ℝ → ℝ → ℝ}
    {y : ℝ → ℂ} {K J : ℝ → ℝ≥0∞} {B C : ℝ}
    (hI : MeasurableSet I) (hE : ∀ w ∈ I, MeasurableSet (E w)) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hR : ∀ w ∈ I, 0 ≤ R w)
    (_hq : ∀ w ∈ I, ∀ s ∈ E w, 0 ≤ q w s)
    (_hP : ∀ w ∈ I, ∀ s ∈ E w, 0 ≤ P w s)
    (hk : ∀ w ∈ I, AEMeasurable (fun s => ENNReal.ofReal (q w s) * K s)
      (volume.restrict (E w)))
    (hmoment : ∀ w ∈ I, ENNReal.ofReal ‖y w‖ ≤
      ENNReal.ofReal C * ∫⁻ s in E w, ENNReal.ofReal (q w s) * K s)
    (hpower : ∀ w ∈ I, ∀ s ∈ E w, R w * q w s ≤ B * P w s) :
    (∫⁻ w in I, ENNReal.ofReal (R w) * ENNReal.ofReal ‖y w‖ * J w) ≤
      ENNReal.ofReal (C * B) * ∫⁻ w in I, ∫⁻ s in E w,
        ENNReal.ofReal (P w s) * K s * J w := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' hI
  intro w hw
  have hcm : (∫⁻ s in E w,
      (ENNReal.ofReal (R w) * ENNReal.ofReal C) *
        (ENNReal.ofReal (q w s) * K s) * J w) =
      (ENNReal.ofReal (R w) * ENNReal.ofReal C) *
        (∫⁻ s in E w, ENNReal.ofReal (q w s) * K s) * J w := by
    have hmeas : AEMeasurable (fun s => (ENNReal.ofReal (R w) * ENNReal.ofReal C) *
        (ENNReal.ofReal (q w s) * K s)) (volume.restrict (E w)) := by
      simpa only [Pi.mul_apply] using! aemeasurable_const.mul (hk w hw)
    rw [lintegral_mul_const'' _ hmeas,
      lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  calc
    _ ≤ ENNReal.ofReal (R w) *
        (ENNReal.ofReal C * ∫⁻ s in E w, ENNReal.ofReal (q w s) * K s) * J w :=
      mul_le_mul' (mul_le_mul' le_rfl (hmoment w hw)) le_rfl
    _ = ∫⁻ s in E w, (ENNReal.ofReal (R w) * ENNReal.ofReal C) *
        (ENNReal.ofReal (q w s) * K s) * J w := by rw [hcm]; ac_rfl
    _ ≤ ∫⁻ s in E w, ENNReal.ofReal (C * B) *
        (ENNReal.ofReal (P w s) * K s * J w) := by
      apply setLIntegral_mono' (hE w hw)
      intro s hs
      have hpow := ENNReal.ofReal_le_ofReal (hpower w hw s hs)
      rw [ENNReal.ofReal_mul (hR w hw), ENNReal.ofReal_mul hB] at hpow
      calc
        _ = ENNReal.ofReal C * (ENNReal.ofReal (R w) * ENNReal.ofReal (q w s)) *
            K s * J w := by ac_rfl
        _ ≤ ENNReal.ofReal C * (ENNReal.ofReal B * ENNReal.ofReal (P w s)) * K s * J w :=
          mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hpow) le_rfl) le_rfl
        _ = _ := by rw [ENNReal.ofReal_mul hC]; ac_rfl
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end EmcsfAcExtension.Local
