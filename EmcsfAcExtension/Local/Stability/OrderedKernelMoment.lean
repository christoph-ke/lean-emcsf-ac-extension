module

public import EmcsfAcExtension.Local.Stability.OrderedKernelPower

/-! # Multiplying a radial moment by its primitive radius

This nonnegative integral argument works for either orientation of the
inner sections. In applications the scalar weight inequality comes from
`stab_radius_power_product_le`. Infinite label values are permitted.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- A moment majorant retains its ordered kernel after multiplication by
the primitive radius and a second label function. The exact coefficient
is `4 * B`, with no dependence on the functions, sets, or interval lengths.
This is an internal analytic helper, not a graph-node theorem. -/
theorem stab_integral_moment_product_le_of_bound
    {I : Set ℝ} {E : ℝ → Set ℝ} {R : ℝ → ℝ} {q P : ℝ → ℝ → ℝ}
    {y : ℝ → ℂ} {K J : ℝ → ℝ≥0∞} {B : ℝ}
    (hI : MeasurableSet I) (hE : ∀ w ∈ I, MeasurableSet (E w)) (hB : 0 ≤ B)
    (hR : ∀ w ∈ I, 0 ≤ R w)
    (_hq : ∀ w ∈ I, ∀ s ∈ E w, 0 ≤ q w s)
    (_hP : ∀ w ∈ I, ∀ s ∈ E w, 0 ≤ P w s)
    (hk : ∀ w ∈ I, AEMeasurable (fun s => ENNReal.ofReal (q w s) * K s)
      (volume.restrict (E w)))
    (hmoment : ∀ w ∈ I, ENNReal.ofReal ‖y w‖ ≤
      ENNReal.ofReal 4 * ∫⁻ s in E w, ENNReal.ofReal (q w s) * K s)
    (hpower : ∀ w ∈ I, ∀ s ∈ E w, R w * q w s ≤ B * P w s) :
    (∫⁻ w in I, ENNReal.ofReal (R w) * ENNReal.ofReal ‖y w‖ * J w) ≤
      ENNReal.ofReal (4 * B) * ∫⁻ w in I, ∫⁻ s in E w,
        ENNReal.ofReal (P w s) * K s * J w := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' hI
  intro w hw
  have hcm : (∫⁻ s in E w,
      (ENNReal.ofReal (R w) * ENNReal.ofReal 4) *
        (ENNReal.ofReal (q w s) * K s) * J w) =
      (ENNReal.ofReal (R w) * ENNReal.ofReal 4) *
        (∫⁻ s in E w, ENNReal.ofReal (q w s) * K s) * J w := by
    have hmeas : AEMeasurable (fun s => (ENNReal.ofReal (R w) * ENNReal.ofReal 4) *
        (ENNReal.ofReal (q w s) * K s)) (volume.restrict (E w)) := by
      simpa only [Pi.mul_apply] using! aemeasurable_const.mul (hk w hw)
    rw [lintegral_mul_const'' _ hmeas,
      lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  calc
    _ ≤ ENNReal.ofReal (R w) *
        (ENNReal.ofReal 4 * ∫⁻ s in E w, ENNReal.ofReal (q w s) * K s) * J w :=
      mul_le_mul' (mul_le_mul' le_rfl (hmoment w hw)) le_rfl
    _ = ∫⁻ s in E w, (ENNReal.ofReal (R w) * ENNReal.ofReal 4) *
        (ENNReal.ofReal (q w s) * K s) * J w := by rw [hcm]; ac_rfl
    _ ≤ ∫⁻ s in E w, ENNReal.ofReal (4 * B) *
        (ENNReal.ofReal (P w s) * K s * J w) := by
      apply setLIntegral_mono' (hE w hw)
      intro s hs
      have hpow := ENNReal.ofReal_le_ofReal (hpower w hw s hs)
      rw [ENNReal.ofReal_mul (hR w hw), ENNReal.ofReal_mul hB] at hpow
      calc
        _ = ENNReal.ofReal 4 * (ENNReal.ofReal (R w) * ENNReal.ofReal (q w s)) *
            K s * J w := by ac_rfl
        _ ≤ ENNReal.ofReal 4 * (ENNReal.ofReal B * ENNReal.ofReal (P w s)) * K s * J w :=
          mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hpow) le_rfl) le_rfl
        _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]; ac_rfl
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end EmcsfAcExtension.Local
