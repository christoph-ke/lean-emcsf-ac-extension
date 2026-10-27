module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Optical exponent differences from absolute flux budgets

Both orientations use this direct integral inequality on their
ordered label interval. It covers zero-length intervals as well.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- An absolute flux budget bounds the difference of its real
integrals, with universal coefficient `1`. The only constant is the
displayed nonnegative budget `L`, uniformly in the curves and interval. -/
theorem stab_optical_integral_sub_le_of_flux_bound
    {f g : ℝ → ℝ} {a b L : ℝ} (hab : a ≤ b) (hL : 0 ≤ L)
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b)
    (hbound : (∫⁻ s in Icc a b, ENNReal.ofReal |f s - g s|) ≤ ENNReal.ofReal L) :
    |(∫ s in a..b, f s) - ∫ s in a..b, g s| ≤ L := by
  have hh : ENNReal.ofReal |(∫ s in a..b, f s) - ∫ s in a..b, g s| ≤
      ∫⁻ s in Icc a b, ENNReal.ofReal |f s - g s| := by
    rw [← intervalIntegral.integral_sub hf hg, ← Real.norm_eq_abs, ofReal_norm,
      intervalIntegral.integral_of_le hab]
    apply (enorm_integral_le_lintegral_enorm (fun s => f s - g s)).trans_eq
    rw [restrict_Ioc_eq_restrict_Icc]
    apply setLIntegral_congr_fun measurableSet_Icc
    intro s hs
    change ‖f s - g s‖ₑ = ENNReal.ofReal |f s - g s|
    rw [← ofReal_norm, Real.norm_eq_abs]
  have he := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hh.trans hbound)
  simpa only [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal hL] using he

end EmcsfAcExtension.Local
