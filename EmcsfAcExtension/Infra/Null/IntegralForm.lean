/- Copyright (c) 2026. All rights reserved. -/

module

public import EmcsfAcExtension.Frozen.IntegralForm
public import EmcsfAcExtension.Infra.AC.Primitive

/-! # Integral equations on characteristic sections

The frozen `IntegralForm` records one endpoint identity. Absolute continuity
requires that identity on every anchored subinterval. No named hypothesis
package or new predicate is introduced.
-/

public section

open Set MeasureTheory Filter

namespace EmcsfAcExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f g g' : ℝ → E} {s t r : ℝ}

/-- Evaluation of one integral-form identity. -/
theorem IntegralForm.eq_add_integral (h : IntegralForm f g s t) :
    f t = f s + ∫ x in s..t, g x := by
  rw [← h.2]
  abel

/-- A degenerate segment satisfies integral form for arbitrary functions. -/
@[simp] theorem integralForm_self (f g : ℝ → E) (s : ℝ) : IntegralForm f g s s := by
  exact ⟨IntervalIntegrable.refl, by rw [sub_self, intervalIntegral.integral_same]⟩

/-- Integral form is independent of the orientation of a segment. -/
theorem IntegralForm.symm (h : IntegralForm f g s t) : IntegralForm f g t s := by
  refine ⟨h.1.symm, ?_⟩
  rw [intervalIntegral.integral_symm, ← h.2, neg_sub]

/-- Endpoint identities concatenate; the middle point need not lie between the others. -/
theorem IntegralForm.trans (h₁ : IntegralForm f g s r) (h₂ : IntegralForm f g r t) :
    IntegralForm f g s t := by
  refine ⟨h₁.1.trans h₂.1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals h₁.1 h₂.1, ← h₁.2, ← h₂.2]
  abel

/-- Changing the density on a null set preserves the integral equation. -/
theorem IntegralForm.congr_ae (h : IntegralForm f g s t)
    (heq : g =ᵐ[volume.restrict (uIcc s t)] g') : IntegralForm f g' s t := by
  have heq' : ∀ᵐ x, x ∈ uIoc s t → g x = g' x := by
    filter_upwards [(ae_restrict_iff' measurableSet_uIcc).mp heq] with x hx hmem
    exact hx (uIoc_subset_uIcc hmem)
  exact ⟨h.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr heq'),
    h.2.trans (intervalIntegral.integral_congr_ae heq')⟩

/-- Anchored integral equations imply absolute continuity on the entire interval. -/
theorem absolutelyContinuousOnInterval_of_integralForm_on {a b : ℝ} (hab : a ≤ b)
    (h : ∀ x ∈ Icc a b, IntegralForm f g a x) :
    AbsolutelyContinuousOnInterval f a b := by
  have hg := (h b ⟨hab, le_rfl⟩).1
  have hp := ((LipschitzWith.const (f a)).lipschitzOnWith.absolutelyContinuousOnInterval
    (a := a) (b := b)).add
    (hg.absolutelyContinuousOnInterval_intervalIntegral_normed left_mem_uIcc)
  apply hp.congr
  intro x hx
  rw [uIcc_of_le hab] at hx
  exact (h x hx).eq_add_integral.symm

/-- AC and a specified integrable almost everywhere derivative imply integral form. -/
theorem integralForm_of_ac_of_ae_hasDerivAt [CompleteSpace E]
    (hf : AbsolutelyContinuousOnInterval f s t) (hg : IntervalIntegrable g volume s t)
    (hfg : ∀ᵐ x, x ∈ uIcc s t → HasDerivAt f (g x) x) : IntegralForm f g s t :=
  ⟨hg, (hf.integral_eq_sub_of_ae_hasDerivAt_normed hg hfg).symm⟩

/-- In finite dimension the derivative of an AC section always gives integral form. -/
theorem integralForm_deriv_of_ac [FiniteDimensional ℝ E]
    (hf : AbsolutelyContinuousOnInterval f s t) : IntegralForm f (deriv f) s t :=
  ⟨hf.intervalIntegrable_deriv_finiteDimensional,
    hf.integral_deriv_eq_sub_finiteDimensional.symm⟩

/-- In finite dimension an a.e. derivative equality needs no separate integrability premise. -/
theorem integralForm_of_ac_of_ae_deriv_eq [FiniteDimensional ℝ E]
    (hf : AbsolutelyContinuousOnInterval f s t)
    (hfg : deriv f =ᵐ[volume.restrict (uIcc s t)] g) : IntegralForm f g s t :=
  (integralForm_deriv_of_ac hf).congr_ae hfg

end EmcsfAcExtension
