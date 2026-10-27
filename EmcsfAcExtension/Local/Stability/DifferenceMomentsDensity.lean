module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Assembly of an unabsorbed moment density

This nonnegative integral calculation combines the forcing coefficients,
the individual `3/4` moment, and the separated-kernel cost. It is shared
by field estimates without requiring integrability of their forcings.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The literal forcing costs `4,16,20`, individual moment cost `64`,
and convolution cost `4` give the uniform density coefficient `8192`.
This conditional algebraic helper closes no field graph node. All
quantities are nonnegative; their integrals may be infinite. -/
theorem stab_difference_density_of_moment_bounds
    {K D J B X Z F : ℝ → ℝ≥0∞} {a b : ℝ} {G U : ℝ≥0∞}
    (hG : G ≠ ⊤) (hU : U ≠ ⊤)
    (hKD : AEMeasurable (fun t => K t * D t) (volume.restrict (Icc a b)))
    (hKJ : AEMeasurable (fun t => K t * J t) (volume.restrict (Icc a b)))
    (hforce : ∀ᵐ t ∂volume.restrict (Icc a b),
      F t ≤ 4 * D t + 16 * U * J t + 20 * G * B t * X t)
    (hind : ∀ᵐ t ∂volume.restrict (Icc a b), X t ≤ 64 * Z t)
    (hconv : (∫⁻ t in Icc a b, K t * B t * Z t) ≤
      4 * ∫⁻ t in Icc a b, K t * J t) :
    (∫⁻ t in Icc a b, K t * F t) ≤
      8192 * ∫⁻ t in Icc a b, K t * (D t + (G + U) * J t) := by
  have hpoint : ∀ᵐ t ∂volume.restrict (Icc a b),
      K t * F t ≤ (4 * (K t * D t) + (16 * U) * (K t * J t)) +
        (1280 * G) * (K t * B t * Z t) := by
    filter_upwards [hforce, hind] with t ht hi
    calc
      _ ≤ K t * (4 * D t + 16 * U * J t + 20 * G * B t * X t) :=
        mul_le_mul' le_rfl ht
      _ ≤ K t * (4 * D t + 16 * U * J t + 20 * G * B t * (64 * Z t)) :=
        mul_le_mul' le_rfl (add_le_add le_rfl (mul_le_mul' le_rfl hi))
      _ = _ := by ring
  have h16U : (16 : ℝ≥0∞) * U ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hU
  have h1280G : (1280 : ℝ≥0∞) * G ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hG
  have hsum : AEMeasurable (fun t => 4 * (K t * D t) + (16 * U) * (K t * J t))
      (volume.restrict (Icc a b)) := (hKD.const_mul 4).add (hKJ.const_mul (16 * U))
  have hlin : (∫⁻ t in Icc a b, K t * F t) ≤
      4 * (∫⁻ t in Icc a b, K t * D t) +
      (16 * U) * (∫⁻ t in Icc a b, K t * J t) +
      (1280 * G) * (∫⁻ t in Icc a b, K t * B t * Z t) := by
    apply (lintegral_mono_ae hpoint).trans_eq
    rw [lintegral_add_left' hsum, lintegral_add_left' (hKD.const_mul 4),
      lintegral_const_mul' 4 _ (by norm_num), lintegral_const_mul' (16 * U) _ h16U,
      lintegral_const_mul' (1280 * G) _ h1280G]
  have hGU : G + U ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hG, hU⟩
  have hright : (∫⁻ t in Icc a b, K t * (D t + (G + U) * J t)) =
      (∫⁻ t in Icc a b, K t * D t) +
        (G + U) * (∫⁻ t in Icc a b, K t * J t) := by
    have heq : (fun t => K t * (D t + (G + U) * J t)) =
        (fun t => K t * D t + (G + U) * (K t * J t)) := by
      funext t
      ring
    rw [heq, lintegral_add_left' hKD, lintegral_const_mul' _ _ hGU]
  rw [hright]
  apply hlin.trans
  calc
    _ ≤ 4 * (∫⁻ t in Icc a b, K t * D t) +
        (16 * U) * (∫⁻ t in Icc a b, K t * J t) +
        (1280 * G) * (4 * ∫⁻ t in Icc a b, K t * J t) :=
      add_le_add le_rfl (mul_le_mul' le_rfl hconv)
    _ = 4 * (∫⁻ t in Icc a b, K t * D t) +
        16 * (U * ∫⁻ t in Icc a b, K t * J t) +
        5120 * (G * ∫⁻ t in Icc a b, K t * J t) := by ring
    _ ≤ 8192 * (∫⁻ t in Icc a b, K t * D t) +
        8192 * (U * ∫⁻ t in Icc a b, K t * J t) +
        8192 * (G * ∫⁻ t in Icc a b, K t * J t) := by
      apply add_le_add
      · exact add_le_add (mul_le_mul' (by norm_num) le_rfl)
          (mul_le_mul' (by norm_num) le_rfl)
      · exact mul_le_mul' (by norm_num) le_rfl
    _ = _ := by ring

end EmcsfAcExtension.Local
