module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! # Nonnegative integration of the mass forcing

The algebraic source comparison is integrated before any real value
of an extended distance is used. The five terms retain their order.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- Integrating the five nonnegative mass forcing terms has literal
constant `1`. Only the displayed coefficients and source budgets enter;
there is no integrability premise on the left side. -/
theorem stab_mass_lintegral_le_of_forcing
    {μ : Measure ℝ} {F d c x e m : ℝ → ℝ≥0∞} {a b : ℝ≥0∞}
    (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (hd : AEMeasurable d μ) (hc : AEMeasurable c μ)
    (hx : AEMeasurable x μ) (he : AEMeasurable e μ)
    (hpoint : ∀ᵐ t ∂μ, F t ≤ a * d t + c t + b * (x t + e t + m t)) :
    (∫⁻ t, F t ∂μ) ≤ a * (∫⁻ t, d t ∂μ) + (∫⁻ t, c t ∂μ) +
      b * ((∫⁻ t, x t ∂μ) + (∫⁻ t, e t ∂μ) + ∫⁻ t, m t ∂μ) := by
  apply (lintegral_mono_ae hpoint).trans_eq
  have had : AEMeasurable (fun t => a * d t) μ := hd.const_mul a
  have hsum : AEMeasurable (fun t => a * d t + c t) μ := by
    simpa only [Pi.add_apply] using! had.add hc
  have hxe : AEMeasurable (fun t => x t + e t) μ := by
    simpa only [Pi.add_apply] using! hx.add he
  rw [lintegral_add_left' (f := fun t => a * d t + c t)
      (g := fun t => b * (x t + e t + m t)) hsum,
    lintegral_add_left' (f := fun t => a * d t) (g := c) had,
    lintegral_const_mul' _ _ ha, lintegral_const_mul' _ _ hb,
    lintegral_add_left' (f := fun t => x t + e t) (g := m) hxe,
    lintegral_add_left' (f := x) (g := e) hx]

end EmcsfAcExtension.Local
