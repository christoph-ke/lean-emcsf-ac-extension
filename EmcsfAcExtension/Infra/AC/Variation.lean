module

public import EmcsfAcExtension.Infra.AC.Primitive

/-!
# Total variation of absolutely continuous curves

For finite dimensional real normed targets, variation on an ordered closed interval
equals the integral of the derivative norm. This includes real and complex curves.
No constants or bounds on the curve enter the identity.

This supplies the variation identities used at `charged_SF_new_version.tex:L4620–L4631`.
-/

public section

open Set Filter MeasureTheory
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E]

namespace AbsolutelyContinuousOnInterval

/-- Absolute continuity implies bounded variation on an ordered closed interval. -/
theorem boundedVariationOn_Icc {f : ℝ → E} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hab : a ≤ b) :
    BoundedVariationOn f (Icc a b) := by
  simpa only [uIcc_of_le hab] using hf.boundedVariationOn

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The variation of an AC curve is bounded above by the integral of its speed. -/
theorem eVariationOn_le_integral_norm_deriv {f : ℝ → E} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hab : a ≤ b) :
    eVariationOn f (Icc a b) ≤ ENNReal.ofReal (∫ x in a..b, ‖deriv f x‖) := by
  have hg := hf.intervalIntegrable_deriv_finiteDimensional
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  have hus' (i : ℕ) : u i ∈ uIcc a b := by
    simpa only [uIcc_of_le hab] using hus i
  have hi (i : ℕ) : IntervalIntegrable (deriv f) volume (u i) (u (i + 1)) :=
    hg.mono_set (uIcc_subset_uIcc (hus' i) (hus' (i + 1)))
  calc
    _ ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal (∫ x in u i..u (i + 1), ‖deriv f x‖) := by
      apply Finset.sum_le_sum
      intro i hi'
      have hFTC := (hf.mono (uIcc_subset_uIcc (hus' i)
        (hus' (i + 1)))).integral_deriv_eq_sub_finiteDimensional
      rw [edist_eq_enorm_sub, ← ofReal_norm, ← hFTC]
      exact ENNReal.ofReal_le_ofReal
        (intervalIntegral.norm_integral_le_integral_norm (hu (Nat.le_succ i)))
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n, ∫ x in u i..u (i + 1), ‖deriv f x‖) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro i hi'
      exact intervalIntegral.integral_nonneg (hu (Nat.le_succ i)) (fun _ _ => norm_nonneg _)
    _ = ENNReal.ofReal (∫ x in u 0..u n, ‖deriv f x‖) := by
      rw [intervalIntegral.sum_integral_adjacent_intervals (fun i _ => (hi i).norm)]
    _ ≤ ENNReal.ofReal (∫ x in a..b, ‖deriv f x‖) := by
      apply ENNReal.ofReal_le_ofReal
      exact intervalIntegral.integral_mono_interval (hus 0).1 (hu (Nat.zero_le n))
        (hus n).2 (ae_of_all _ (fun _ => norm_nonneg _)) hg.norm

/-- Total variation of an AC curve equals the integral of its derivative norm. -/
theorem eVariationOn_eq_integral_norm_deriv {f : ℝ → E} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hab : a ≤ b) :
    eVariationOn f (Icc a b) = ENNReal.ofReal (∫ x in a..b, ‖deriv f x‖) := by
  apply le_antisymm (hf.eVariationOn_le_integral_norm_deriv hab)
  have hBV := hf.boundedVariationOn_Icc hab
  rw [← ENNReal.ofReal_toReal hBV]
  exact ENNReal.ofReal_le_ofReal (hBV.integral_norm_deriv_le hab)

/-- Real valued total variation of an AC curve is the integral of its speed. -/
theorem toReal_eVariationOn_eq_integral_norm_deriv {f : ℝ → E} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hab : a ≤ b) :
    (eVariationOn f (Icc a b)).toReal = ∫ x in a..b, ‖deriv f x‖ := by
  rw [hf.eVariationOn_eq_integral_norm_deriv hab,
    ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg hab (fun _ _ => norm_nonneg _))]

end AbsolutelyContinuousOnInterval

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- An integral representation gives variation equal to the integral of the density norm. -/
theorem IntervalIntegrable.eVariationOn_eq_integral_norm_of_eq_integral
    {f g : ℝ → E} {a b : ℝ} (hg : IntervalIntegrable g volume a b) (hab : a ≤ b)
    (hfg : ∀ x ∈ Icc a b, f x = f a + ∫ t in a..x, g t) :
    eVariationOn f (Icc a b) = ENNReal.ofReal (∫ x in a..b, ‖g x‖) := by
  have hp := hg.absolutelyContinuousOnInterval_intervalIntegral_normed left_mem_uIcc
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => f a) a b :=
    (LipschitzWith.const (f a)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hf : AbsolutelyContinuousOnInterval f a b := (hconst.fun_add hp).congr
    (fun x hx => (hfg x (by simpa only [uIcc_of_le hab] using hx)).symm)
  rw [hf.eVariationOn_eq_integral_norm_deriv hab]
  congr 1
  apply intervalIntegral.integral_congr_ae
  have hne_a : ∀ᵐ x : ℝ, x ≠ a := by simp [ae_iff, measure_singleton]
  have hne_b : ∀ᵐ x : ℝ, x ≠ b := by simp [ae_iff, measure_singleton]
  filter_upwards [hg.ae_hasDerivAt_integral, hne_a, hne_b] with x hx hxa hxb hmem
  have hmem' : x ∈ Icc a b := by
    simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hmem
  have hdx := (hx (uIoc_subset_uIcc hmem) a left_mem_uIcc).const_add (f a)
  have hdf : HasDerivAt f (g x) x :=
    (hdx.hasDerivWithinAt.congr_of_mem hfg hmem').hasDerivAt
      (Icc_mem_nhds (lt_of_le_of_ne hmem'.1 hxa.symm) (lt_of_le_of_ne hmem'.2 hxb))
  rw [hdf.deriv]

/-- Exact variation formula for an integral primitive with any additive constant. -/
theorem IntervalIntegrable.eVariationOn_const_add_intervalIntegral
    {g : ℝ → E} {a b : ℝ} (hg : IntervalIntegrable g volume a b) (hab : a ≤ b) (z : E) :
    eVariationOn (fun x => z + ∫ t in a..x, g t) (Icc a b) =
      ENNReal.ofReal (∫ x in a..b, ‖g x‖) := by
  apply hg.eVariationOn_eq_integral_norm_of_eq_integral hab
  intro x hx
  rw [intervalIntegral.integral_same, add_zero]

