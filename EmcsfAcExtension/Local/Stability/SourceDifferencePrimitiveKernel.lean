module

public import Mathlib
import EmcsfAcExtension.Local.Stability.SourceDifferenceAlgebra
import EmcsfAcExtension.Local.Stability.SourceDifferencePrimitive

/-! # Primitive difference bounded by four positive kernels

The outer coefficient, inner ratio, inner derivative and inner radius are
subtracted separately. No derivative of a datum or endpoint map occurs.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- A scalar source difference is controlled by four inverse-cube primitive
kernels. The exact coefficient is `3 B`, with every bound and constant
explicit. This analytic helper permits infinite nonnegative label envelopes. -/
theorem scalar_primitive_difference_kernel_le
    {u v B E ε G : ℝ} {ρ r₁ r₂ : ℝ → ℝ} {y₁ y₂ j₁ j₂ : ℝ → ℂ}
    {J₁ J₂ Dj : ℝ → ℝ≥0∞} {c₁ c₂ : ℂ}
    (_huv : u < v) (hB : 0 ≤ B) (hE : 0 ≤ E) (hε : 0 ≤ ε) (hG : 0 ≤ G)
    (hρ : AEMeasurable ρ (volume.restrict (Icc u v)))
    (hy₁ : AEStronglyMeasurable y₁ (volume.restrict (Icc u v)))
    (hy₂ : AEStronglyMeasurable y₂ (volume.restrict (Icc u v)))
    (hJ₁ : Measurable J₁) (_hJ₂ : Measurable J₂) (hDj : Measurable Dj)
    (hf₁ : IntegrableOn (fun w => (r₁ w : ℂ) * starRingEnd ℂ (y₁ w) * j₁ w) (Icc u v))
    (hf₂ : IntegrableOn (fun w => (r₂ w : ℂ) * starRingEnd ℂ (y₂ w) * j₂ w) (Icc u v))
    (hr : ∀ w ∈ Icc u v, 0 ≤ r₁ w ∧ r₁ w ≤ ρ w)
    (hδr : ∀ w ∈ Icc u v, |r₁ w - r₂ w| ≤ G * (ρ w))
    (hj₁ : ∀ w ∈ Icc u v, ‖j₁ w‖ₑ ≤ J₁ w)
    (hj₂ : ∀ w ∈ Icc u v, ‖j₂ w‖ₑ ≤ J₂ w)
    (hδj : ∀ w ∈ Icc u v, ‖j₁ w - j₂ w‖ₑ ≤ Dj w)
    (hc : ‖c₁ - c₂‖ₑ ≤ ENNReal.ofReal (B * E / (v - u) ^ 3))
    (hc₂ : ‖c₂‖ₑ ≤ ENNReal.ofReal (B * ε / (v - u) ^ 3)) :
    let z₁ := ∫ w in Icc u v, (r₁ w : ℂ) * starRingEnd ℂ (y₁ w) * j₁ w
    let z₂ := ∫ w in Icc u v, (r₂ w : ℂ) * starRingEnd ℂ (y₂ w) * j₂ w
    let P₁ := ∫⁻ w in Icc u v, ENNReal.ofReal (ρ w) * ‖y₁ w‖ₑ * J₁ w
    let Pδ := ∫⁻ w in Icc u v, ENNReal.ofReal (ρ w) * ‖y₁ w - y₂ w‖ₑ * J₁ w
    let PD := ∫⁻ w in Icc u v, ENNReal.ofReal (ρ w) * ‖y₂ w‖ₑ * Dj w
    let P₂ := ∫⁻ w in Icc u v, ENNReal.ofReal (ρ w) * ‖y₂ w‖ₑ * J₂ w
    let W := ENNReal.ofReal (1 / (v - u) ^ 3)
    ‖c₁ * (z₁ + 2 * starRingEnd ℂ z₁) - c₂ * (z₂ + 2 * starRingEnd ℂ z₂)‖ₑ ≤
      ENNReal.ofReal (3 * B) * (ENNReal.ofReal E * (W * P₁) +
        ENNReal.ofReal ε * (W * Pδ) + ENNReal.ofReal ε * (W * PD) +
        ENNReal.ofReal (ε * G) * (W * P₂)) := by
  dsimp only
  let f₁ := fun w => (r₁ w : ℂ) * starRingEnd ℂ (y₁ w) * j₁ w
  let f₂ := fun w => (r₂ w : ℂ) * starRingEnd ℂ (y₂ w) * j₂ w
  let p₁ := fun w => ENNReal.ofReal (ρ w) * ‖y₁ w‖ₑ * J₁ w
  let pδ := fun w => ENNReal.ofReal (ρ w) * ‖y₁ w - y₂ w‖ₑ * J₁ w
  let pD := fun w => ENNReal.ofReal (ρ w) * ‖y₂ w‖ₑ * Dj w
  let p₂ := fun w => ENNReal.ofReal (ρ w) * ‖y₂ w‖ₑ * J₂ w
  have hrnorm (w : ℝ) (hw : w ∈ Icc u v) :
      ‖(r₁ w : ℂ)‖ₑ ≤ ENNReal.ofReal (ρ w) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr w hw).1]
    exact ENNReal.ofReal_le_ofReal (hr w hw).2
  have hδrnorm (w : ℝ) (hw : w ∈ Icc u v) :
      ‖((r₁ w - r₂ w : ℝ) : ℂ)‖ₑ ≤ ENNReal.ofReal G * ENNReal.ofReal (ρ w) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, ← ENNReal.ofReal_mul hG]
    exact ENNReal.ofReal_le_ofReal (hδr w hw)
  have hraw₁ : (∫⁻ w in Icc u v, ‖f₁ w‖ₑ) ≤ ∫⁻ w in Icc u v, p₁ w := by
    apply setLIntegral_mono' measurableSet_Icc
    intro w hw
    simp only [f₁, p₁, enorm_mul, RCLike.enorm_conj]
    exact mul_le_mul' (mul_le_mul' (hrnorm w hw) le_rfl) (hj₁ w hw)
  have hrawδ : (∫⁻ w in Icc u v, ‖f₁ w - f₂ w‖ₑ) ≤
      (∫⁻ w in Icc u v, pδ w) + (∫⁻ w in Icc u v, pD w) +
        ENNReal.ofReal G * ∫⁻ w in Icc u v, p₂ w := by
    have hwmeas : AEMeasurable (fun w => ENNReal.ofReal (ρ w))
        (volume.restrict (Icc u v)) := ENNReal.measurable_ofReal.comp_aemeasurable hρ
    have hmδ : AEMeasurable pδ (volume.restrict (Icc u v)) :=
      (hwmeas.mul (hy₁.sub hy₂).enorm).mul hJ₁.aemeasurable.restrict
    have hmD : AEMeasurable pD (volume.restrict (Icc u v)) :=
      (hwmeas.mul hy₂.enorm).mul hDj.aemeasurable.restrict
    have hmδD : AEMeasurable (fun w => pδ w + pD w) (volume.restrict (Icc u v)) :=
      hmδ.fun_add hmD
    calc
      _ ≤ ∫⁻ w in Icc u v, pδ w + pD w + ENNReal.ofReal G * p₂ w := by
        apply setLIntegral_mono' measurableSet_Icc
        intro w hw
        apply (enorm_primitive_integrand_sub_le (r₁ w) (r₂ w)
          (y₁ w) (y₂ w) (j₁ w) (j₂ w)).trans
        calc
          _ ≤ (pδ w + pD w) +
              (ENNReal.ofReal G * ENNReal.ofReal (ρ w)) * ‖y₂ w‖ₑ * J₂ w := by
            exact add_le_add (add_le_add
              (mul_le_mul' (mul_le_mul' (hrnorm w hw) le_rfl) (hj₁ w hw))
              (mul_le_mul' (mul_le_mul' (hrnorm w hw) le_rfl) (hδj w hw)))
              (mul_le_mul' (mul_le_mul' (hδrnorm w hw) le_rfl) (hj₂ w hw))
          _ = _ := by dsimp only [p₂]; ring
      _ = _ := by
        rw [lintegral_add_left' hmδD, lintegral_add_left' hmδ,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hsrc := scalar_primitive_source_difference_enorm_le
    (hf₁.mono_set Ioc_subset_Icc_self) (hf₂.mono_set Ioc_subset_Icc_self) c₁ c₂
  simp only [restrict_Ioc_eq_restrict_Icc] at hsrc
  apply hsrc.trans
  apply (mul_le_mul' le_rfl (add_le_add (mul_le_mul' hc hraw₁) (mul_le_mul' hc₂ hrawδ))).trans_eq
  rw [div_eq_mul_one_div (B * E), div_eq_mul_one_div (B * ε),
    ENNReal.ofReal_mul (mul_nonneg hB hE), ENNReal.ofReal_mul hB,
    ENNReal.ofReal_mul (mul_nonneg hB hε), ENNReal.ofReal_mul hB,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_mul hε]
  dsimp only [p₁, pδ, pD, p₂]
  ring

end EmcsfAcExtension.Local.Stab
