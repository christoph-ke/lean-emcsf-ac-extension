/- Copyright (c) 2026. All rights reserved. -/
module

public import Mathlib

/-! # Nonnegative proper integrals and half-open exhaustion

Conversion to extended integrals requires proper interval integrability.
Exhaustion takes place entirely in `ℝ≥0∞`, without a finiteness assumption
and without taking `toReal` of an infinite integral.
-/

public section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace EmcsfAcExtension.Global

/-- [internal] Closed and half-open label integrals have the same endpoint convention. -/
theorem lintegral_Ico_eq_Icc (f : ℝ → ℝ≥0∞) (a b : ℝ) :
    (∫⁻ x in Ico a b, f x) = ∫⁻ x in Icc a b, f x := by
  rw [restrict_Ico_eq_restrict_Icc]

/-- [internal] Open and closed label integrals agree, including degenerate intervals. -/
theorem lintegral_Ioo_eq_Icc (f : ℝ → ℝ≥0∞) (a b : ℝ) :
    (∫⁻ x in Ioo a b, f x) = ∫⁻ x in Icc a b, f x := by
  rw [restrict_Ioo_eq_restrict_Icc]

/-- [internal] A nonnegative integrable proper section converts exactly to a lintegral. -/
theorem ofReal_intervalIntegral_eq_lintegral {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (hn : ∀ᵐ x ∂volume.restrict (Icc a b), 0 ≤ f x) :
    ENNReal.ofReal (∫ x in a..b, f x) = ∫⁻ x in Ico a b, ENNReal.ofReal (f x) := by
  rw [intervalIntegral.integral_of_le hab, restrict_Ico_eq_restrict_Icc,
    restrict_Ioc_eq_restrict_Icc]
  exact ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).1 hf) hn

/-- [internal] Continuity and nonnegativity justify conversion on a proper closed section. -/
theorem ofReal_intervalIntegral_eq_lintegral_of_continuousOn {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (hn : ∀ x ∈ Icc a b, 0 ≤ f x) :
    ENNReal.ofReal (∫ x in a..b, f x) = ∫⁻ x in Ico a b, ENNReal.ofReal (f x) := by
  apply ofReal_intervalIntegral_eq_lintegral hab
    (hf.intervalIntegrable_of_Icc hab)
  exact (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hn)

/-- [internal] Proper half-open truncations exhaust the half-open interval.
The sequence may start below the left endpoint. -/
theorem iUnion_Ico_of_tendsto {a b : ℝ} {v : ℕ → ℝ}
    (hv : ∀ n, v n ≤ b) (ht : Tendsto v atTop (𝓝 b)) :
    (⋃ n, Ico a (v n)) = Ico a b := by
  ext x
  simp only [mem_iUnion, mem_Ico]
  constructor
  · rintro ⟨n, ha, hx⟩
    exact ⟨ha, hx.trans_le (hv n)⟩
  · rintro ⟨ha, hx⟩
    obtain ⟨n, hn⟩ := (ht.eventually (Ioi_mem_nhds hx)).exists
    exact ⟨n, ha, hn⟩

/-- [internal] Monotone convergence on proper truncations, including infinite limits.
No measurability of the integrand is needed for continuity in the restricted measure. -/
theorem lintegral_Ico_eq_iSup {f : ℝ → ℝ≥0∞} {a b : ℝ} {v : ℕ → ℝ}
    (hm : Monotone v) (hv : ∀ n, v n ≤ b) (ht : Tendsto v atTop (𝓝 b)) :
    (∫⁻ x in Ico a b, f x) = ⨆ n, ∫⁻ x in Ico a (v n), f x := by
  rw [← iUnion_Ico_of_tendsto hv ht]
  apply setLIntegral_iUnion_of_directed f
  intro i j
  exact ⟨max i j, Ico_subset_Ico_right (hm (le_max_left _ _)),
    Ico_subset_Ico_right (hm (le_max_right _ _))⟩

/-- [internal] Proper real nonnegative integrals recover the full extended integral;
only the proper truncations need be finite. -/
theorem lintegral_ofReal_Ico_eq_iSup_intervalIntegral {f : ℝ → ℝ} {a b : ℝ} {v : ℕ → ℝ}
    (hm : Monotone v) (hv : ∀ n, v n ≤ b) (ht : Tendsto v atTop (𝓝 b))
    (ha : ∀ n, a ≤ v n) (hi : ∀ n, IntervalIntegrable f volume a (v n))
    (hn : ∀ x ∈ Ico a b, 0 ≤ f x) :
    (∫⁻ x in Ico a b, ENNReal.ofReal (f x)) =
      ⨆ n, ENNReal.ofReal (∫ x in a..v n, f x) := by
  rw [lintegral_Ico_eq_iSup hm hv ht]
  congr 1
  funext n
  apply (ofReal_intervalIntegral_eq_lintegral (ha n) (hi n) ?_).symm
  rw [← restrict_Ico_eq_restrict_Icc]
  exact (ae_restrict_iff' measurableSet_Ico).2
    (Eventually.of_forall fun x hx => hn x ⟨hx.1, hx.2.trans_le (hv n)⟩)

end EmcsfAcExtension.Global
