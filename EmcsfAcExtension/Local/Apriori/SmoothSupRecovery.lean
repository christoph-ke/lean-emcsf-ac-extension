module

public import EmcsfAcExtension.Local.Apriori.SmoothSupScalar
import EmcsfAcExtension.Local.Calculus.AxisContinuity
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity
import EmcsfAcExtension.Local.Api.Finite

/-! # Scalar recovery with a supplied uniform sup budget

These conditional lemmas isolate the use of the J/K closures. They preserve
the exact universal constants of internal project record (N1–N2); the bounds on the
renormalized fields remain explicit hypotheses and no node is tagged here.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- Scalar recovery from bounds on the two renormalized fields. The numerical
coefficients `4` and `16` are universal in the standing box, independent of
`T,e,M,h,S,A,B`. If `A,B` are uniform over a family of constructed triangles,
the displayed derivative and decay bounds are uniform over that family too.
This is a conditional helper, not the datum-dependent scalar C¹ node. -/
theorem smooth_scalar_recovery_of_bound {e T ε M A B : ℝ}
    {S : Fields} {h : ℝ → ℂ} (hset : AprioriSetting e T ε M S h)
    (hε : ε ≤ 1 / 16) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hJ : ∀ p ∈ triangle 0 T, ‖jC1 (triangle 0 T) S p.1 p.2‖ ≤ A)
    (hK : ∀ p ∈ triangle 0 T, ‖kC1 e (triangle 0 T) S p.1 p.2‖ ≤ B) :
    ∀ p ∈ triangle 0 T,
      ‖pdV (triangle 0 T) S.a p.1 p.2‖ ≤ 4 * A ∧
      ‖pdU (triangle 0 T) S.b p.1 p.2 + I * e * S.A p.1 p.2 * S.b p.1 p.2‖ ≤
        4 * B ∧
      ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ 16 * S.r p.1 p.2 * A ∧
      ‖S.xi p.1 p.2 / S.nu p.1 p.2‖ ≤ 16 * S.r p.1 p.2 * B := by
  have hj : (⨆ p ∈ triangle 0 T, ‖jC1 (triangle 0 T) S p.1 p.2‖ₑ) ≤
      ENNReal.ofReal A := by
    apply iSup₂_le
    intro p hp
    simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal (hJ p hp)
  have hk : (⨆ p ∈ triangle 0 T, ‖kC1 e (triangle 0 T) S p.1 p.2‖ₑ) ≤
      ENNReal.ofReal B := by
    apply iSup₂_le
    intro p hp
    simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal (hK p hp)
  have hr := smooth_scalar_derivative_recovery_aux hset hε
  have convert_bound {z : ℂ} {C : ℝ} (hC : 0 ≤ C) (hb : ‖z‖ₑ ≤ ENNReal.ofReal C) :
      ‖z‖ ≤ C := by
    have hi := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    simpa only [toReal_enorm, ENNReal.toReal_ofReal hC] using hi
  intro p hp
  have hr0 : 0 ≤ S.r p.1 p.2 :=
    (div_nonneg (sub_nonneg.mpr hp.2.1) (by norm_num)).trans
      (smooth_radius_bounds_aux hset hp).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply convert_bound (by positivity : 0 ≤ 4 * A)
    apply (le_iSup₂_of_le p hp le_rfl).trans (hr.1.trans ?_)
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
      ENNReal.ofReal_ofNat] using mul_le_mul' (le_refl 4) hj
  · apply convert_bound (by positivity : 0 ≤ 4 * B)
    apply (le_iSup₂_of_le p hp le_rfl).trans (hr.2.1.trans ?_)
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
      ENNReal.ofReal_ofNat] using mul_le_mul' (le_refl 4) hk
  · apply convert_bound (by positivity : 0 ≤ 16 * S.r p.1 p.2 * A)
    apply ((hr.2.2 p hp).1).trans
    simpa only [ENNReal.ofReal_mul (by positivity : 0 ≤ 16 * S.r p.1 p.2)] using
      mul_le_mul' (le_refl (ENNReal.ofReal (16 * S.r p.1 p.2))) hj
  · apply convert_bound (by positivity : 0 ≤ 16 * S.r p.1 p.2 * B)
    apply ((hr.2.2 p hp).2).trans
    simpa only [ENNReal.ofReal_mul (by positivity : 0 ≤ 16 * S.r p.1 p.2)] using
      mul_le_mul' (le_refl (ENNReal.ofReal (16 * S.r p.1 p.2))) hk

end EmcsfAcExtension.Local
