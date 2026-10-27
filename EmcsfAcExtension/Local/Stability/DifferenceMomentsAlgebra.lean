module

public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Algebra for the two radial difference moments

The cubic map has Lipschitz coefficient `3 * ε²` on the `ε` ball.
Consequently the real damping map `z ↦ z - ‖z‖² • z` is strongly monotone
with coefficient `1 - 3 * ε²`, as in the approved internal project record difference argument.
These auxiliary estimates have literal universal coefficients.
-/

public section

open scoped RealInnerProductSpace

namespace EmcsfAcExtension.Local

/-- The squared norms on an `ε` ball differ by at most `2ε` times the
distance. The numerical coefficient is uniform in the radius and points. -/
theorem stab_norm_sq_sub_le {ε : ℝ} {z w : ℂ}
    (hz : ‖z‖ ≤ ε) (hw : ‖w‖ ≤ ε) :
    |‖z‖ ^ 2 - ‖w‖ ^ 2| ≤ 2 * ε * ‖z - w‖ := by
  have he : 0 ≤ ε := (norm_nonneg z).trans hz
  calc
    |‖z‖ ^ 2 - ‖w‖ ^ 2| = |‖z‖ - ‖w‖| * (‖z‖ + ‖w‖) := by
      rw [show ‖z‖ ^ 2 - ‖w‖ ^ 2 = (‖z‖ - ‖w‖) * (‖z‖ + ‖w‖) by ring,
        abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    _ ≤ ‖z - w‖ * (2 * ε) :=
      mul_le_mul (abs_norm_sub_norm_le z w) (by linarith only [hz, hw])
        (by positivity) (by positivity)
    _ = _ := by ring

/-- The cubic scalar map on the `ε` ball is Lipschitz with the exact
coefficient `3ε²`, independently of every field or geometric parameter. -/
theorem stab_cubic_sub_le {ε : ℝ} {z w : ℂ}
    (hz : ‖z‖ ≤ ε) (hw : ‖w‖ ≤ ε) :
    ‖‖z‖ ^ 2 • z - ‖w‖ ^ 2 • w‖ ≤ 3 * ε ^ 2 * ‖z - w‖ := by
  have he : 0 ≤ ε := (norm_nonneg z).trans hz
  have hz2 : ‖z‖ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
  have hsplit : ‖z‖ ^ 2 • z - ‖w‖ ^ 2 • w =
      ‖z‖ ^ 2 • (z - w) + (‖z‖ ^ 2 - ‖w‖ ^ 2) • w := by
    rw [smul_sub, sub_smul]
    abel
  calc
    _ ≤ ‖z‖ ^ 2 * ‖z - w‖ + |‖z‖ ^ 2 - ‖w‖ ^ 2| * ‖w‖ := by
      rw [hsplit]
      have hh := norm_add_le (‖z‖ ^ 2 • (z - w)) ((‖z‖ ^ 2 - ‖w‖ ^ 2) • w)
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs] at hh
      rw [abs_of_nonneg (sq_nonneg ‖z‖)] at hh
      exact hh
    _ ≤ ε ^ 2 * ‖z - w‖ + (2 * ε * ‖z - w‖) * ε := by
      exact add_le_add (mul_le_mul_of_nonneg_right hz2 (norm_nonneg _))
        (mul_le_mul (stab_norm_sq_sub_le hz hw) hw (norm_nonneg _) (by positivity))
    _ = _ := by ring

/-- Strong monotonicity of the damped radial nonlinearity. The constant
is exactly `1 - 3ε²`; this estimate makes no positivity assumption on it. -/
theorem stab_radial_strong_monotone {ε : ℝ} {z w : ℂ}
    (hz : ‖z‖ ≤ ε) (hw : ‖w‖ ≤ ε) :
    (1 - 3 * ε ^ 2) * ‖z - w‖ ^ 2 ≤
      inner ℝ (z - w) ((z - ‖z‖ ^ 2 • z) - (w - ‖w‖ ^ 2 • w)) := by
  have hc := stab_cubic_sub_le hz hw
  have hi := real_inner_le_norm (z - w) (‖z‖ ^ 2 • z - ‖w‖ ^ 2 • w)
  have hb := hi.trans (mul_le_mul_of_nonneg_left hc (norm_nonneg (z - w)))
  have hid : (z - ‖z‖ ^ 2 • z) - (w - ‖w‖ ^ 2 • w) =
      (z - w) - (‖z‖ ^ 2 • z - ‖w‖ ^ 2 • w) := by abel
  rw [hid, inner_sub_right, real_inner_self_eq_norm_sq]
  nlinarith only [hb]

/-- The norm derivative of a radial difference retains the monotonicity
coefficient. A real connection contributes zero, uniformly in its size.
This is a local auxiliary inequality at an ordinary differentiability point. -/
theorem stab_norm_deriv_radial_difference_le
    {f g : ℝ → ℂ} {q : ℂ} {ε a α t : ℝ}
    (ha : 0 ≤ a) (hf : ‖f t‖ ≤ ε) (hg : ‖g t‖ ≤ ε)
    (hd : HasDerivAt (fun s => f s - g s)
      (q - a • ((f t - ‖f t‖ ^ 2 • f t) - (g t - ‖g t‖ ^ 2 • g t)) -
        α • (Complex.I * (f t - g t))) t)
    (hy : DifferentiableAt ℝ (fun s => ‖f s - g s‖) t) :
    deriv (fun s => ‖f s - g s‖) t +
      a * (1 - 3 * ε ^ 2) * ‖f t - g t‖ ≤ ‖q‖ := by
  by_cases hz : f t - g t = 0
  · have hmin : IsLocalMin (fun s => ‖f s - g s‖) t :=
      Filter.Eventually.of_forall (fun s => by
        simp only [hz, norm_zero]
        exact norm_nonneg _)
    rw [hmin.deriv_eq_zero, hz, norm_zero, mul_zero, add_zero]
    exact norm_nonneg _
  · have hi := stab_radial_strong_monotone hf hg
    have hiq := real_inner_le_norm (f t - g t) q
    have hia := mul_le_mul_of_nonneg_left hi ha
    have heq := hd.norm_sq.deriv
    have heq' : deriv (fun s => ‖f s - g s‖ ^ 2) t =
        2 * ‖f t - g t‖ * deriv (fun s => ‖f s - g s‖) t := by
      have hd' := (hy.hasDerivAt.pow 2).deriv
      have hfun : ((fun s => ‖f s - g s‖) ^ 2) = (fun s => ‖f s - g s‖ ^ 2) :=
        funext (fun s => Pi.pow_apply _ _ _)
      rw [hfun] at hd'
      simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using hd'
    have hconn : inner ℝ (f t - g t) (Complex.I * (f t - g t)) = 0 :=
      real_inner_I_smul_self (𝕜 := ℂ) (f t - g t)
    have hinner : inner ℝ (f t - g t)
        (q - a • ((f t - ‖f t‖ ^ 2 • f t) - (g t - ‖g t‖ ^ 2 • g t)) -
          α • (Complex.I * (f t - g t))) = inner ℝ (f t - g t) q -
        a * inner ℝ (f t - g t)
          ((f t - ‖f t‖ ^ 2 • f t) - (g t - ‖g t‖ ^ 2 • g t)) := by
      rw [inner_sub_right, real_inner_smul_right, hconn, mul_zero, sub_zero,
        inner_sub_right, real_inner_smul_right]
    rw [hinner] at heq
    have hp : 0 < ‖f t - g t‖ := norm_pos_iff.mpr hz
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith only [heq, heq', hiq, hia]

end EmcsfAcExtension.Local
