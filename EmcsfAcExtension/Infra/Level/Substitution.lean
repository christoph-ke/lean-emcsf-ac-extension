module

public import EmcsfAcExtension.Infra.Level.OrderIso
public import EmcsfAcExtension.Infra.AC.Intervals
public import EmcsfAcExtension.Infra.AC.Relabel
public import EmcsfAcExtension.Infra.RadialKernel
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Monotone radius substitution

The set formulas apply directly to open-ended intervals and to measurable,
possibly disconnected histories. Nonnegative integrals take values in `ℝ≥0∞`;
no finiteness assumption or conversion to real numbers is needed. The AC
formulas below use an almost everywhere density and the AC fundamental theorem.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace EmcsfAcExtension.Global.Level

/-- [internal] Increasing differentiable substitution on an arbitrary measurable
history, including improper intervals. The integrand need not be integrable. -/
theorem lintegral_image_mono {f f' : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hd : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hm : MonotoneOn f s)
    (g : ℝ → ℝ≥0∞) :
    (∫⁻ y in f '' s, g y) = ∫⁻ x in s, ENNReal.ofReal (f' x) * g (f x) :=
  lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn hs hd hm g

/-- [internal] Decreasing terminal-radius substitution on an arbitrary measurable
history. The Jacobian is the negative derivative, and may have infinite integral. -/
theorem lintegral_image_anti {f f' : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hd : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hm : AntitoneOn f s)
    (g : ℝ → ℝ≥0∞) :
    (∫⁻ y in f '' s, g y) = ∫⁻ x in s, ENNReal.ofReal (-f' x) * g (f x) :=
  lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn hs hd hm g

end EmcsfAcExtension.Global.Level
