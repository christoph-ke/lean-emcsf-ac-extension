/- Copyright (c) 2026. All rights reserved. -/
module

public import Mathlib

/-! # Averaging and the cooling clock

The integral of squared normalized energy selects a time in the latter
half of the interval. Square-root propagation transfers that estimate to
the endpoint. The constants have the exact values in
`charged_SF_new_version.tex:L2990–L3021`, with no smallness relation between variation
and the initial energy envelope.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Global.Cooling

/-- [internal] Continuous squared energy attains a value at most its
average on every nondegenerate compact interval. There are no constants. -/
theorem averaged_small_energy_time {q : ℝ → ℝ} {s t : ℝ}
    (hst : s < t) (hq : ContinuousOn q (Icc s t)) :
    ∃ x ∈ Icc s t, q x ^ 2 ≤ (∫ y in s..t, q y ^ 2) / (t - s) := by
  obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr hst.le) (hq.pow 2)
  refine ⟨x, hx, ?_⟩
  apply (le_div_iff₀ (sub_pos.mpr hst)).2
  have hi := intervalIntegral.integral_mono_on (μ := volume) hst.le intervalIntegrable_const
    ((hq.pow 2).intervalIntegrable_of_Icc hst.le) hmin
  rw [intervalIntegral.integral_const, smul_eq_mul] at hi
  simpa only [mul_comm, Pi.pow_apply] using hi

/-- [node eq:charged-cool-constants]
The exact cooling constants, fixed before all energy, variation, duration,
and physical-radius data. They depend only on `d` and the budget constant `C`. -/
theorem _root_.EmcsfAcExtension.Global.charged_cool_constants (C d : ℝ) (hC : 0 < C) (hd : 0 < d) :
    0 < 18 * C / d ^ 2 ∧ 0 < 1 + d / 3 ∧
      Real.sqrt (2 * C / (18 * C / d ^ 2)) = d / 3 := by
  refine ⟨by positivity, by positivity, ?_⟩
  have heq : 2 * C / (18 * C / d ^ 2) = (d / 3) ^ 2 := by field_simp; ring
  rw [heq, Real.sqrt_sq (by positivity)]

/-- [internal] The envelope decrease from its integrated budget and the
square-root propagation bound. The constants `18*C/d²` and `1+d/3` are
fixed before every cylinder scale and every energy or variation datum. -/
theorem _root_.EmcsfAcExtension.Global.charged_cool_decrease_of_budgets
    (C d : ℝ) (hC : 0 < C) (hd : 0 < d) :
    ∀ (q : ℝ → ℝ) (b ε T σ : ℝ), 0 < b → 0 < ε → 0 ≤ σ →
      T = (18 * C / d ^ 2) * b / ε →
      ContinuousOn q (Icc 0 T) → (∀ x ∈ Icc 0 T, 0 ≤ q x) →
      (∫ x in 0..T, q x ^ 2 / b) ≤ C * (ε + σ ^ 2) →
      (∀ x ∈ Icc (T / 2) T, q T ≤ 2 * q x + σ ^ 2) →
      q T ≤ d * ε + (1 + d / 3) * σ ^ 2 := by
  intro q b ε T σ hb hε hσ hT hq hqn hbudget hprop
  have hTp : 0 < T := by rw [hT]; positivity
  have hsub : Icc (T / 2) T ⊆ Icc 0 T := Icc_subset_Icc (by linarith) le_rfl
  obtain ⟨x, hx, hmean⟩ := averaged_small_energy_time (by linarith : T / 2 < T) (hq.mono hsub)
  have hpart : (∫ y in T / 2..T, q y ^ 2) ≤ ∫ y in 0..T, q y ^ 2 := by
    apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) le_rfl
      (ae_of_all _ (fun _ => sq_nonneg _))
      ((hq.pow 2).intervalIntegrable_of_Icc hTp.le)
  have hwhole : (∫ y in 0..T, q y ^ 2) ≤ b * C * (ε + σ ^ 2) := by
    rw [intervalIntegral.integral_div] at hbudget
    have hi := (div_le_iff₀ hb).1 hbudget
    nlinarith only [hi]
  have hsmall : q x ^ 2 ≤ (d ^ 2 / 9) * ε * (ε + σ ^ 2) := by
    have hm := (le_div_iff₀ (by linarith : 0 < T - T / 2)).1 hmean
    have hc : T * ((d ^ 2 / 9) * ε * (ε + σ ^ 2)) =
        2 * (b * C * (ε + σ ^ 2)) := by
      rw [hT]
      field_simp; ring
    have ht : T * q x ^ 2 ≤ T * ((d ^ 2 / 9) * ε * (ε + σ ^ 2)) := by
      nlinarith only [hm, hpart, hwhole, hc]
    exact (mul_le_mul_iff_right₀ hTp).1 ht
  have hxp := hqn x (hsub hx)
  have hbound : q x ≤ d / 3 * ε + d / 6 * σ ^ 2 := by
    apply (sq_le_sq₀ hxp (by positivity : 0 ≤ d / 3 * ε + d / 6 * σ ^ 2)).1
    nlinarith only [hsmall, sq_nonneg (d * σ ^ 2)]
  have hp := hprop x hx
  have hde : 0 ≤ d * ε := mul_nonneg hd.le hε.le
  nlinarith only [hp, hbound, hde]

/-- [internal] The literal averaged energy estimate at an arbitrary
positive cooling duration factor `H`. The sole budget premise is discharged
by the actual-field observation consumer. Constants: the given `C,H` are
fixed before `b,ε,T,σ` and the energy curve (L2697–L2708). -/
theorem averaged_energy_envelope_of_budget (C H : ℝ) (hC : 0 < C) (hH : 0 < H)
    (q : ℝ → ℝ) (b ε T σ : ℝ) (hb : 0 < b) (hε : 0 < ε) (hσ : 0 ≤ σ)
    (hT : T = H * b / ε) (hq : ContinuousOn q (Icc 0 T))
    (_hqn : ∀ x ∈ Icc 0 T, 0 ≤ q x)
    (hbudget : (∫ x in 0..T, q x ^ 2 / b) ≤ C * (ε + σ ^ 2)) :
    ∃ x ∈ Icc (T / 2) T,
      q x ≤ Real.sqrt ((2 * C * ε / H) * (ε + σ ^ 2)) ∧
      Real.sqrt ((2 * C * ε / H) * (ε + σ ^ 2)) ≤
        Real.sqrt (2 * C / H) * (ε + Real.sqrt ε * σ) := by
  have hTp : 0 < T := by rw [hT]; positivity
  have hsub : Icc (T / 2) T ⊆ Icc 0 T := Icc_subset_Icc (by linarith) le_rfl
  obtain ⟨x, hx, hmean⟩ := averaged_small_energy_time (by linarith : T / 2 < T) (hq.mono hsub)
  have hpart : (∫ y in T / 2..T, q y ^ 2) ≤ ∫ y in 0..T, q y ^ 2 := by
    apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) le_rfl
      (ae_of_all _ (fun _ => sq_nonneg _)) ((hq.pow 2).intervalIntegrable_of_Icc hTp.le)
  have hwhole : (∫ y in 0..T, q y ^ 2) ≤ b * C * (ε + σ ^ 2) := by
    rw [intervalIntegral.integral_div] at hbudget
    have hi := (div_le_iff₀ hb).mp hbudget
    nlinarith only [hi]
  have hsmall : q x ^ 2 ≤ (2 * C * ε / H) * (ε + σ ^ 2) := by
    have hm := (le_div_iff₀ (by linarith : 0 < T - T / 2)).mp hmean
    have he : T * ((2 * C * ε / H) * (ε + σ ^ 2)) = 2 * (b * C * (ε + σ ^ 2)) := by
      rw [hT]
      field_simp
    have ht : T * q x ^ 2 ≤ T * ((2 * C * ε / H) * (ε + σ ^ 2)) := by
      nlinarith only [hm, hpart, hwhole, he]
    exact (mul_le_mul_iff_right₀ hTp).mp ht
  refine ⟨x, hx, Real.le_sqrt_of_sq_le hsmall, ?_⟩
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have he := Real.sq_sqrt hε.le
    have hc := Real.sq_sqrt (show 0 ≤ 2 * C / H by positivity)
    rw [mul_pow, hc]
    have hcross : 0 ≤ 2 * ε * Real.sqrt ε * σ := by positivity
    have halg : (2 * C * ε / H) * (ε + σ ^ 2) ≤
        (2 * C / H) * (ε + Real.sqrt ε * σ) ^ 2 := by
      have hi : ε * (ε + σ ^ 2) ≤ (ε + Real.sqrt ε * σ) ^ 2 := by
        rw [add_sq, mul_pow, he]
        nlinarith only [hcross]
      have hm := mul_le_mul_of_nonneg_left hi (show 0 ≤ 2 * C / H by positivity)
      convert hm using 1; ring
    exact halg

end EmcsfAcExtension.Global.Cooling
