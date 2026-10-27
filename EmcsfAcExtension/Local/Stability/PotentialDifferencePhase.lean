module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Ring

/-! # Difference of the incoming parallel factors

The phase error is bounded by the integral of the difference of the
connections, with literal coefficient `1`. This is the unitary part of
the incoming difference moment in internal project record, before estimating the potential.
-/

public section

open MeasureTheory Set Complex

namespace EmcsfAcExtension.Local

/-- The real phase exponential is `1`-Lipschitz, uniformly over both
phases. No bound on either individual phase is required. -/
theorem stab_unit_phase_sub_le (x y : ℝ) :
    ‖Complex.exp (I * x) - Complex.exp (I * y)‖ ≤ |x - y| := by
  have heq : Complex.exp (I * x) - Complex.exp (I * y) =
      Complex.exp (I * y) * (Complex.exp (I * (x - y : ℝ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [heq, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

/-- Two incoming parallel factors at common labels differ by at most
`|e|` times the integral of the potential difference. The constant is
exactly `1`, uniformly in the coupling, endpoints and both potentials. -/
theorem stab_parallel_factor_sub_le {A₁ A₂ : ℝ → ℝ} {u s : ℝ}
    (hus : u ≤ s) (h₁ : IntervalIntegrable A₁ volume u s)
    (h₂ : IntervalIntegrable A₂ volume u s) (e : ℝ) :
    ‖Complex.exp (I * e * (∫ t in u..s, A₁ t : ℝ)) -
      Complex.exp (I * e * (∫ t in u..s, A₂ t : ℝ))‖ ≤
        |e| * ∫ t in u..s, |A₁ t - A₂ t| := by
  have hphase := stab_unit_phase_sub_le (e * ∫ t in u..s, A₁ t)
    (e * ∫ t in u..s, A₂ t)
  have hi := intervalIntegral.norm_integral_le_integral_norm
    (μ := volume) (f := fun t => A₁ t - A₂ t) hus
  have heq : |e * (∫ t in u..s, A₁ t) - e * (∫ t in u..s, A₂ t)| =
      |e| * |∫ t in u..s, A₁ t - A₂ t| := by
    rw [← mul_sub, ← intervalIntegral.integral_sub h₁ h₂, abs_mul]
  have hphase' : ‖Complex.exp (I * e * (∫ t in u..s, A₁ t : ℝ)) -
      Complex.exp (I * e * (∫ t in u..s, A₂ t : ℝ))‖ ≤
        |e| * |∫ t in u..s, A₁ t - A₂ t| := by
    simpa only [Complex.ofReal_mul, ← mul_assoc, heq] using hphase
  exact hphase'.trans (mul_le_mul_of_nonneg_left
    (by simpa only [Real.norm_eq_abs] using hi) (abs_nonneg e))

end EmcsfAcExtension.Local
