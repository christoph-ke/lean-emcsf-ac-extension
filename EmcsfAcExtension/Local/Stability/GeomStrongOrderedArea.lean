module

public import EmcsfAcExtension.Local.Stability.GeomStrongKernelMeas

/-! # Area integration of four geometric telescope terms

Every ordered majorant is measurable before it is summed. Thus its
finite area cost follows from the positive kernel theorem, independently
of any prior integrability of the source being estimated.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- Four ordered kernel majorants can be integrated separately.
The exact area factor is `2`, for exponent `1/2`, universally before
all time, input functions and finite nonnegative coefficients.
-/
theorem stab_four_ordered_area_of_bound {T : ℝ}
    {K₁ K₂ KF J₂ DJ : ℝ → ℝ≥0∞} {F : ℝ × ℝ → ℝ≥0∞} {a b c d : ℝ≥0∞}
    (mK₁ : Measurable K₁) (mK₂ : Measurable K₂) (mKF : Measurable KF)
    (mJ₂ : Measurable J₂) (mDJ : Measurable DJ)
    (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hc : c ≠ ⊤) (hd : d ≠ ⊤)
    (hF : ∀ q ∈ triangle 0 T, F q ≤
      a * stabOrderedKernel (1 / 2) K₂ J₂ q.1 q.2 +
      b * stabOrderedKernel (1 / 2) K₂ J₂ q.1 q.2 +
      c * stabOrderedKernel (1 / 2) KF J₂ q.1 q.2 +
      d * stabOrderedKernel (1 / 2) K₁ DJ q.1 q.2) :
    (∫⁻ q in triangle 0 T, F q) ≤
      a * (2 * (∫⁻ s in Icc 0 T, K₂ s) * (∫⁻ s in Icc 0 T, J₂ s)) +
      b * (2 * (∫⁻ s in Icc 0 T, K₂ s) * (∫⁻ s in Icc 0 T, J₂ s)) +
      c * (2 * (∫⁻ s in Icc 0 T, KF s) * (∫⁻ s in Icc 0 T, J₂ s)) +
      d * (2 * (∫⁻ s in Icc 0 T, K₁ s) * (∫⁻ s in Icc 0 T, DJ s)) := by
  let f := fun q : ℝ × ℝ => a * stabOrderedKernel (1 / 2) K₂ J₂ q.1 q.2
  let g := fun q : ℝ × ℝ => b * stabOrderedKernel (1 / 2) K₂ J₂ q.1 q.2
  let h := fun q : ℝ × ℝ => c * stabOrderedKernel (1 / 2) KF J₂ q.1 q.2
  let k := fun q : ℝ × ℝ => d * stabOrderedKernel (1 / 2) K₁ DJ q.1 q.2
  have mf : Measurable f := measurable_const.mul (stab_ordered_kernel_measurable mK₂ mJ₂)
  have mg : Measurable g := measurable_const.mul (stab_ordered_kernel_measurable mK₂ mJ₂)
  have mh : Measurable h := measurable_const.mul (stab_ordered_kernel_measurable mKF mJ₂)
  have mfg : Measurable (fun q => f q + g q) := mf.add mg
  have mfgh : Measurable (fun q => f q + g q + h q) := mfg.add mh
  have hbound := setLIntegral_mono' (μ := (volume : Measure (ℝ × ℝ)))
    (measurableSet_triangle 0 T) hF
  change (∫⁻ q in triangle 0 T, F q) ≤
    ∫⁻ q in triangle 0 T, f q + g q + h q + k q at hbound
  apply hbound.trans
  rw [lintegral_add_left' (f := fun q => f q + g q + h q) (g := k) mfgh.aemeasurable,
    lintegral_add_left' (f := fun q => f q + g q) (g := h) mfg.aemeasurable,
    lintegral_add_left' (f := f) (g := g) mf.aemeasurable]
  dsimp only [f, g, h, k]
  rw [lintegral_const_mul' a _ ha, lintegral_const_mul' b _ hb,
    lintegral_const_mul' c _ hc, lintegral_const_mul' d _ hd]
  have h₂ := stab_ordered_kernel_triangle_area (T := T) (p := (1 / 2 : ℝ))
    (by norm_num) mK₂ mJ₂
  have hF₂ := stab_ordered_kernel_triangle_area (T := T) (p := (1 / 2 : ℝ))
    (by norm_num) mKF mJ₂
  have h₁ := stab_ordered_kernel_triangle_area (T := T) (p := (1 / 2 : ℝ))
    (by norm_num) mK₁ mDJ
  norm_num only [one_div, inv_div, div_one, ENNReal.ofReal_ofNat] at h₂ hF₂ h₁
  exact add_le_add (add_le_add (add_le_add (mul_le_mul' le_rfl h₂)
    (mul_le_mul' le_rfl h₂)) (mul_le_mul' le_rfl hF₂)) (mul_le_mul' le_rfl h₁)

end EmcsfAcExtension.Local
